use base64::{self, DecodeError};
use rand::Rng;
use sha3::{Digest, Sha3_256};
use std::error;
use std::fmt;

// Flag the encoding. The default encoding is:
// * base64URL-unpadded (signified with u)
// * SHA-256 (0x16: "F" in base64URL)
const RATCHET_SIGNIFIER: &str = "uF";
// number of iterations a previous search can use before
// ratchets are considered unrelated
const DEFAULT_PREV_BUDGET: isize = 1_000_000;

#[derive(Debug)]
pub enum RatchetErr {
    BadLen(usize),
    BadEncoding(String),
    UnknownRelation,
    Decode(DecodeError),
}

impl fmt::Display for RatchetErr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &*self {
            RatchetErr::BadLen(i) => write!(f, "invalid ratchet length {}", i),
            RatchetErr::BadEncoding(s) => write!(
                f,
                "unsupported ratched encoding: '{}'. only '{}' is supported",
                s, RATCHET_SIGNIFIER
            ),
            RatchetErr::UnknownRelation => write!(f, "cannot relate ratchets"),
            RatchetErr::Decode(e) => write!(f, "{:?}", e),
        }
    }
}

impl error::Error for RatchetErr {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match *self {
            RatchetErr::Decode(ref e) => Some(e),
            _ => None,
        }
    }
}

impl From<DecodeError> for RatchetErr {
    fn from(err: DecodeError) -> RatchetErr {
        RatchetErr::Decode(err)
    }
}

#[derive(Debug)]
pub enum PreviousErr {
    ExhaustedBudget,
    EqualRatchets,
    OlderRatchet,
}

impl fmt::Display for PreviousErr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            PreviousErr::ExhaustedBudget => write!(f, "exhausted ratchet discrepency budget"),
            PreviousErr::EqualRatchets => write!(f, "ratchets are equal"),
            PreviousErr::OlderRatchet => write!(f, "self ratchet is older than given ratchet"),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Spiral {
    large: [u8; 32],
    medium: [u8; 32],
    medium_counter: u8,
    small: [u8; 32],
    small_counter: u8,
}

impl Spiral {
    pub fn new() -> Self {
        // 32 bytes for the seed, plus two extra bytes to randomize small & medium starts
        let seed: [u8; 32] = rand::thread_rng().gen::<[u8; 32]>();
        let inc_med = rand::thread_rng().gen::<u8>();
        let inc_small = rand::thread_rng().gen::<u8>();
        let med_seed = hash_32(compliment(seed));
        let small_seed = hash_32(compliment(med_seed));

        Spiral {
            large: hash_32(seed),
            medium: hash_32_n(med_seed, inc_med),
            medium_counter: inc_med,
            small: hash_32_n(small_seed, inc_small),
            small_counter: inc_small,
        }
    }

    fn zero(seed: [u8; 32]) -> Self {
        let med = hash_32(compliment(seed));
        Spiral {
            large: hash_32(seed),
            medium: med,
            medium_counter: 0,
            small: hash_32(compliment(med)),
            small_counter: 0,
        }
    }

    pub fn key(self) -> [u8; 32] {
        let v = xor(self.large, xor(self.medium, self.small));
        hash_32(v)
    }

    pub fn summary(self) -> String {
        format!(
            "{:?}-{:?}:{:?}-{:?}:{:?}",
            &self.large[0..3],
            self.medium_counter,
            &self.medium[0..3],
            self.small_counter,
            &self.small[0..3]
        )
    }

    pub fn encode(self) -> String {
        let mut b: [u8; 98] = [0; 98];
        for (i, byte) in self.small.iter().enumerate() {
            b[i] = *byte;
        }
        b[32] = self.small_counter;
        for (i, byte) in self.medium.iter().enumerate() {
            b[i + 33] = *byte;
        }
        b[65] = self.medium_counter;
        for (i, byte) in self.large.iter().enumerate() {
            b[i + 66] = *byte;
        }
        for (i, byte) in b.iter().enumerate() {
            println!("b[{}]: {}", i, byte);
        }

        RATCHET_SIGNIFIER.to_owned() + &base64::encode_config(b, base64::URL_SAFE).to_owned()
    }

    pub fn inc(&mut self) {
        if self.small_counter >= 255 {
            let (r, _) = next_medium_epoch(*self);
            *self = r;
            return;
        }
        self.small = hash_32(self.small);
        self.small_counter += 1;
    }

    pub fn inc_by(&mut self, n: usize) {
        let (jumped, _) = inc_by(*self, n as isize);
        *self = jumped;
    }

    pub fn compare(self, other: &Spiral, max_steps: usize) -> Result<isize, RatchetErr> {
        let self_counter = self.combined_counter() as isize;
        let other_counter = other.combined_counter() as isize;
        if self.large == other.large {
            if self_counter == other_counter {
                return Ok(0);
            }
            return Ok(self_counter - other_counter);
        }

        // here, the large digit always differs, so one of the ratchets will always be bigger,
        // they cannot be equal.
        // We can find out which one is bigger by hashing both at the same time and looking at
        // when one created the same digit as the other, essentially racing the large digit's
        // recursive hashes.
        let mut self_large = self.large.clone();
        let mut other_large = other.large.clone();
        let mut steps = 0;
        let mut steps_left = max_steps;

        // Since the two ratches might just be generated from a totally different setup, we
        // can never _really_ know which one is the bigger one. They might be unrelated.
        while steps_left > 0 {
            self_large = hash_32(self_large);
            other_large = hash_32(other_large);
            steps += 1;

            if other_large == self.large {
                // other_large_counter * 256 * 256 is the count of increments applied via
                // advancing the large digit continually
                // -other_large_counter is the difference between 'other' and its next large epoch.
                // self_counter is just what's self to add because of the count at which 'self' is
                return Ok((steps * 256 * 256) - (other_counter + self_counter));
            }

            if self_large == other.large {
                // in this case, we compute the same difference, but return the negative to
                // indicate that 'other' is bigger that 'self' rather than the other way
                // around.
                return Ok(-(steps * 256 * 256) - (self_counter + other_counter));
            }
            steps_left -= 1;
        }
        return Err(RatchetErr::UnknownRelation);
    }

    pub fn equal(&self, right: &Spiral) -> bool {
        self.small == right.small
            && self.small_counter == right.small_counter
            && self.medium == right.medium
            && self.medium_counter == right.medium_counter
            && self.large == right.large
    }

    // known_after is probabilistic. Returns true if self is known to be after b, and false
    // if large counters are inequal (meaning r is before, equal, unrelated, or after)
    pub fn known_after(self, other: Spiral) -> bool {
        self.large == other.large
            && self.medium_counter > other.medium_counter
            && self.small_counter > other.small_counter
    }

    // This is adapted from the go impl, but doesn't seem to work as intended
    // examining the typescript impl, looks like a single ratchet should be returned
    // not a vector (or in go's case, a slice)
    pub fn previous(self, old: &Spiral, limit: usize) -> Result<Vec<Spiral>, PreviousErr> {
        return self.previous_budget(old, DEFAULT_PREV_BUDGET, limit);
    }

    fn previous_budget(
        self,
        old: &Spiral,
        discrepency_budget: isize,
        limit: usize,
    ) -> Result<Vec<Spiral>, PreviousErr> {
        if self.equal(old) {
            Err(PreviousErr::EqualRatchets)?;
        } else if self.known_after(*old) {
            Err(PreviousErr::OlderRatchet)?;
        }
        return previous_helper(&self.clone(), old, discrepency_budget, limit);
    }

    fn combined_counter(self) -> usize {
        (256 * self.medium_counter as usize) + self.small_counter as usize
    }
}

// TODO: this won't work for histories that span the small ratchet
pub fn previous_helper(
    recent: &Spiral,
    old: &Spiral,
    discrepency_budget: isize,
    limit: usize,
) -> Result<Vec<Spiral>, PreviousErr> {
    if discrepency_budget < 0 {
        return Err(PreviousErr::ExhaustedBudget);
    }

    let (old_next_large, old_next_large_steps_done) = next_large_epoch(*old);

    if recent.large == old.large || recent.large == old_next_large.large {
        let (old_next_medium, old_next_medium_steps_done) = next_medium_epoch(*old);

        if recent.medium == old.medium || recent.medium == old_next_medium.medium {
            // break out of the recursive pattern at this point because discrepency is
            // within the small ratchet. working sequentially if faster
            let mut revision = old.clone();
            let mut next = old.clone();
            let mut revisions = vec![*old];
            next.inc();
            while !next.equal(recent) {
                revision.inc();
                next.inc();

                // duplicate code, also is it nonsense?
                if revisions.len() == limit && limit > 0 {
                    // shift all elements by one, keeping slice the same length
                    let mut r = vec![revision.clone()];
                    r.extend(&revisions[0..revisions.len() - 1]);
                    revisions = r;
                } else {
                    // push to front
                    let mut r = vec![revision.clone()];
                    r.extend(&revisions[1..revisions.len()]);
                    revisions = r;
                };
            }
            return Ok(revisions);
        }

        return previous_helper(
            recent,
            &old_next_medium,
            discrepency_budget - old_next_medium_steps_done as isize,
            limit,
        );
    }

    return previous_helper(
        recent,
        &old_next_large,
        discrepency_budget - old_next_large_steps_done as isize,
        limit,
    );
}

fn inc_by(mut r: Spiral, n: isize) -> (Spiral, isize) {
    if n <= 0 {
        return (r, 0);
    } else if n >= 256 * 256 - r.combined_counter() as isize {
        // n is larger than at least one large epoch jump
        let (jumped, jump_count) = next_large_epoch(r);
        return inc_by(jumped, n - jump_count);
    } else if n >= 256 - r.small_counter as isize {
        // n is larger than at lest one medium epoch jump
        let (jumped, jump_count) = next_medium_epoch(r);
        return inc_by(jumped, n - jump_count);
    }
    r.small = hash_32_n(r.small, n as u8);
    r.small_counter += n as u8;
    (r, n)
}

fn next_large_epoch(r: Spiral) -> (Spiral, isize) {
    (
        Spiral::zero(r.large),
        256 * 256 - r.combined_counter() as isize,
    )
}

fn next_medium_epoch(r: Spiral) -> (Spiral, isize) {
    if r.medium_counter >= 255 {
        return next_large_epoch(r);
    }

    let jumped = Spiral {
        large: r.large,
        medium: hash_32(r.medium),
        medium_counter: r.medium_counter + 1,
        small: hash_32(compliment(r.medium)),
        small_counter: 0,
    };
    let jump_count = jumped.combined_counter() - r.combined_counter();
    (jumped, jump_count as isize)
}

pub fn decode_spiral(s: String) -> Result<Spiral, RatchetErr> {
    if s.len() != 133 {
        return Err(RatchetErr::BadLen(s.len()));
    }
    if &s[0..2] != RATCHET_SIGNIFIER {
        return Err(RatchetErr::BadEncoding(s[0..2].to_string()));
    }
    let d = base64::decode_config(s, base64::URL_SAFE)?;

    let mut s = Spiral {
        small: [0; 32],
        small_counter: 0,
        medium: [0; 32],
        medium_counter: 0,
        large: [0; 32],
    };

    for (i, byte) in d.iter().enumerate() {
        match i {
            0..=31 => s.small[i] = *byte,
            32 => s.small_counter = *byte,
            33..=64 => s.medium[i - 33] = *byte,
            65 => s.medium_counter = *byte,
            66..=97 => s.large[i - 66] = *byte,
            _ => (),
        }
    }
    Ok(s)
}

fn hash_32(d: [u8; 32]) -> [u8; 32] {
    let mut hasher = Sha3_256::new();
    hasher.update(d);
    let result_vec = hasher.finalize().to_vec();
    let mut arr = [0; 32];
    for (i, byte) in result_vec.iter().enumerate() {
        arr[i] = *byte;
    }
    arr
}

fn hash_32_n(mut d: [u8; 32], n: u8) -> [u8; 32] {
    for _ in 0..n {
        d = hash_32(d);
    }
    d
}

fn xor(a: [u8; 32], b: [u8; 32]) -> [u8; 32] {
    let mut c: [u8; 32] = [0; 32];
    for (i, (a_byte, b_byte)) in a.iter().zip(b.iter()).enumerate() {
        c[i] = a_byte ^ b_byte;
    }
    c
}

fn compliment(d: [u8; 32]) -> [u8; 32] {
    let mut e: [u8; 32] = [0; 32];
    for (i, d_byte) in d.iter().enumerate() {
        e[i] = !d_byte;
    }
    e
}

#[cfg(test)]
mod tests {
    use super::*;
    use hex::FromHex;

    fn shasum_from_hex(s: &str) -> Result<[u8; 32], hex::FromHexError> {
        <[u8; 32]>::from_hex(s)
    }

    #[test]
    fn test_ratchet() {
        // seed pulled from https://whitepaper.fission.codes/file-system/partitions/private-directories/concepts/spiral-ratchet
        let seed =
            shasum_from_hex("600b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33")
                .unwrap();

        let mut a = Spiral::zero(seed);
        let expect = Spiral {
            large: shasum_from_hex(
                "5aa00b14dd50887cdc0b0b55aa2da1eb5cc3a79cdbe893b2319da378a83ad0c5",
            )
            .unwrap(),
            medium: shasum_from_hex(
                "5a86c2477e2ae4ffcf6373cce82259eb542b72a72db9cf9cddfe06bcc20623b6",
            )
            .unwrap(),
            medium_counter: 0,
            small: shasum_from_hex(
                "962b7f9ac204ffd0fa398e9c875c90806c0cd6646655f7a5994b7a828b70c0da",
            )
            .unwrap(),
            small_counter: 0,
        };
        assert_ratchet_equal(expect, a);

        a.inc();
        let mut b = Spiral::zero(seed);
        b.inc();
        assert_ratchet_equal(a, b);

        let a_key = a.key();
        let b_key = b.key();
        assert_eq!(a_key, b_key);
    }

    #[test]
    fn test_ratchet_add_256() {
        let seed =
            shasum_from_hex("600b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33")
                .unwrap();
        // manually advance ratchet 256 (2 ^ 8) times
        let mut slow = Spiral::zero(seed);
        for _ in 0..256 {
            slow.inc();
        }

        // fast jump 256 values in one shot
        let (fast, _) = next_medium_epoch(Spiral::zero(seed));
        assert_ratchet_equal(slow, fast);
    }

    // #[test]
    // fn test_fuzz_ratchet {
    //     // TODO: research rust fuzz impl
    // }

    #[test]
    fn test_ratchet_add_65536() {
        let seed =
            shasum_from_hex("600b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33")
                .unwrap();
        // manually advance ratchet (2 ^ 16) times
        let mut slow = Spiral::zero(seed);
        for _ in 0..65536 {
            slow.inc();
        }

        // fast jump (2 ^ 16) values in one shot
        let (fast, _) = next_large_epoch(Spiral::zero(seed));
        assert_ratchet_equal(slow, fast);
    }

    // TODO broken
    #[test]
    fn test_ratchet_coding() {
        let seed =
            shasum_from_hex("600b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33")
                .unwrap();
        let a = Spiral::zero(seed);
        let encoded = a.encode();

        let b = decode_spiral(encoded).unwrap();
        assert_ratchet_equal(a, b);
    }

    #[test]
    fn test_ratchet_compare() {
        let one = Spiral::zero(
            shasum_from_hex("600b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33")
                .unwrap(),
        );
        let mut two = one.clone();
        two.inc();
        let mut twenty_five_thousand = one.clone();
        twenty_five_thousand.inc_by(25000);

        let mut one_hundred_thousand = one.clone();
        one_hundred_thousand.inc_by(100_000);

        let mut temp = one.clone();
        temp.inc_by(65_536);

        struct Cases<'a> {
            description: &'a str,
            a: Spiral,
            b: Spiral,
            max_steps: usize,
            expect: isize,
        }
        let mut cases = vec![
            Cases {
                description: "comparing same ratchet",
                a: one,
                b: one,
                max_steps: 0,
                expect: 0,
            },
            Cases {
                description: "ratchet a is one step behind",
                a: one,
                b: two,
                max_steps: 1,
                expect: -1,
            },
            Cases {
                description: "ratchet a is one step ahead",
                a: two,
                b: one,
                max_steps: 1,
                expect: 1,
            },
            Cases {
                description: "ratchet a is 25000 steps ahead",
                a: twenty_five_thousand,
                b: one,
                max_steps: 10,
                expect: 25000,
            },
            // 65_533 works, 65_536 does not
            // 256*256 = 65_536... there is something here
            //
            Cases {
                description: "ratchet a is 65_536 steps behind",
                a: one,
                b: temp,
                max_steps: 10,
                expect: -65_536,
            },
            Cases {
                description: "ratchet a is 100_000 steps behind",
                a: one,
                b: one_hundred_thousand,
                max_steps: 10,
                expect: -100_000,
            },
        ];
        for c in cases.iter_mut() {
            let got =
                c.a.compare(&c.b, c.max_steps)
                    .unwrap_or_else(|e| panic!("error in case '{}': {:?}", c.description, e));
            assert_eq!(c.expect, got);
        }

        let unrelated = Spiral::zero(
            shasum_from_hex("500b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33")
                .unwrap(),
        );
        // panic if this does not error
        one.compare(&unrelated, 100_000).unwrap_err();
    }

    #[test]
    fn test_ratchet_equal() {
        let a = Spiral::zero(
            shasum_from_hex("600b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33")
                .unwrap(),
        );
        let b = Spiral::zero(
            shasum_from_hex("600b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33")
                .unwrap(),
        );
        let c = Spiral::zero(
            shasum_from_hex("0000000000000000000000000000000000000000000000000000000000000000")
                .unwrap(),
        );

        if !a.equal(&b) {
            panic!("Spiral::equal method incorrectly asserts two equal ratchets are unequal");
        }

        if b.equal(&c) {
            panic!("Spiral::equal method incorrectly asserts two unequal ratchets are equal")
        }
    }

    #[test]
    fn test_ratchet_previous() {
        let increments: [usize; 5] = [1, 2, 2000, 20_000, 300_000];
        for inc in increments.into_iter() {
            // TODO refactor so we compute this once & copy for each test
            let old = Spiral::zero(
                shasum_from_hex("600b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33")
                    .unwrap(),
            );

            let mut recent = old.clone();
            recent.inc_by(inc);

            let mut limit = 5;
            if inc < limit {
                limit = inc;
            }

            let mut expect: Vec<Spiral> = vec![];
            let mut rev = old.clone();
            let act_inc = (inc as isize - limit as isize - 1) as usize;
            print!(
                "inc {}\nlimit {}\nactual inc {}\n",
                inc as isize, limit as isize, act_inc
            );
            rev.inc_by(act_inc); // fast forward past any elided history

            let mut i = 0;
            // handle case where history will include original "old" ratchet
            if limit < 255 && inc < 255 {
                expect.push(rev.clone());
                i += 1;
            }
            for _ in i..limit {
                rev.inc();
                expect.insert(0, rev.clone());
            }

            let got = match recent.previous(&old, 5) {
                Ok(g) => g,
                Err(e) => panic!("error for previous with inc {}: {:?}", inc, e),
            };

            for (x, g) in expect.into_iter().zip(got.into_iter()).into_iter() {
                assert_ratchet_equal(x, g);
            }
        }
    }

    #[test]
    fn test_xor() {
        let a = [0; 32];
        let b = [0; 32];
        let c = [0; 32];
        assert_eq!(c, xor(a, b));

        let a = [0xFF; 32];
        let b = [0xFF; 32];
        let c = [0; 32];
        assert_eq!(c, xor(a, b));

        let a = [0xFF; 32];
        let b = [0; 32];
        let c = [0xFF; 32];
        assert_eq!(c, xor(a, b));
    }

    #[test]
    fn test_compliment() {
        let d = [0; 32];
        let e = [0xFF; 32];
        assert_eq!(e, compliment(d));

        let d = [0; 32];
        let e = [0xFF; 32];
        assert_eq!(e, compliment(d));
    }

    fn assert_ratchet_equal(expect: Spiral, got: Spiral) {
        assert_eq!(hex::encode(expect.large), hex::encode(got.large));
        assert_eq!(hex::encode(expect.medium), hex::encode(got.medium));
        assert_eq!(expect.medium_counter, got.medium_counter);
        assert_eq!(hex::encode(expect.small), hex::encode(got.small));
        assert_eq!(expect.small_counter, got.small_counter);
    }
}
