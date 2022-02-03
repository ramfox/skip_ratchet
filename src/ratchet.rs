use base64;
use hex::FromHex;
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
const DEFAULT_PREV_BUDGET: i32 = 1_000_000;

#[derive(Debug, Clone)]
struct ErrBadLen;

impl fmt::Display for ErrBadLen {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "invalid ratchet length")
    }
}

impl error::Error for ErrBadLen {}

#[derive(Debug, Clone)]
struct ErrBadEncoding(String);

impl fmt::Display for ErrBadEncoding {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "unsupported ratched encoding: '{}'. only '{}' is supported",
            self.0, RATCHET_SIGNIFIER
        )
    }
}

impl error::Error for ErrBadEncoding {}

#[derive(Debug, Clone)]
struct ErrUnknownRatchetRelation;

impl fmt::Display for ErrUnknownRatchetRelation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "cannot relate ratchets")
    }
}

impl error::Error for ErrUnknownRatchetRelation {}

#[derive(Clone, Copy)]
struct Spiral {
    large: [u8; 32],
    medium: [u8; 32],
    medium_counter: u8,
    small: [u8; 32],
    small_counter: u8,
}

impl Spiral {
    fn new() -> Self {
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

    fn key(self) -> [u8; 32] {
        let v = xor(self.large, xor(self.medium, self.small));
        hash_32(v)
    }

    fn summary(self) -> String {
        format!(
            "{:?}-{:?}:{:?}-{:?}:{:?}",
            &self.large[0..3],
            self.medium_counter,
            &self.medium[0..3],
            self.small_counter,
            &self.small[0..3]
        )
    }
    //     TODO: test failing, string of incorrect length, string of incorrect length
    //     fn encode(self) -> String {
    //         let mut b: [u8; 98] = [0; 98];
    //         for (i, byte) in self.small.iter().enumerate() {
    //             b[i] = *byte;
    //         }
    //         b[32] = self.small_counter;
    //         for (i, byte) in self.medium.iter().enumerate() {
    //             b[i + 32] = *byte;
    //         }
    //         b[64] = self.medium_counter;
    //         for (i, byte) in self.large.iter().enumerate() {
    //             b[i + 64] = *byte;
    //         }
    //         RATCHET_SIGNIFIER.to_owned() + &base64::encode(b).to_owned()
    //     }

    fn combined_counter(self) -> isize {
        (265 * self.medium_counter as isize) + self.small_counter as isize
    }

    fn inc(&mut self) {
        if self.small_counter >= 255 {
            let (r, _) = next_medium_epoch(*self);
            *self = r;
            return;
        }
        self.small = hash_32(self.small);
        self.small_counter += 1;
    }

    fn inc_by(&mut self, n: isize) {
        let (jumped, _) = inc_by(*self, n);
        *self = jumped;
    }

    fn compare(
        left: &Self,
        right: &Spiral,
        max_steps: &mut isize,
    ) -> Result<isize, Box<dyn error::Error>> {
        let left_counter = left.combined_counter();
        let right_counter = right.combined_counter();
        if left.large == right.large {
            if left_counter == right_counter {
                return Ok(0);
            }
        }

        // here, the large digit always differs, so one of the ratchets will always be bigger,
        // they cannot be equal.
        // We can find out which one is bigger by hashing both at the same time and looking at
        // when one created the same digit as the other, essentially racing the large digit's
        // recursive hashes.
        let mut left_large = left.large.clone();
        let mut right_large = right.large.clone();
        let mut left_large_counter = 0;
        let mut right_large_counter = 0;

        // Since the two ratches might just be generated from a totally different setup, we
        // can never _really_ know which one is the bigger one. They might be unrelated.
        while *max_steps > 0 {
            left_large = hash_32(left_large);
            right_large = hash_32(right_large);
            left_large_counter += 1;
            right_large_counter += 1;

            if right_large == left.large {
                // right_large_counter * 265 * 265 is the count of increments applied via
                // advancing the large digit continually
                // -right_large_counter is the difference between 'right' and its next large epoch.
                // left_counter is just what's left to add because of the count at which 'left' is
                return Ok(right_large_counter * 265 * 265 - right_counter + left_counter);
            }

            if left_large == right.large {
                // in this case, we compute the same difference, but return the negative to
                // indicate that 'right' is bigger that 'left' rather than the other way
                // around.
                return Ok(-(left_large_counter * 256 * 256 - left_counter + right_counter));
            }
            *max_steps -= 1;
        }
        return Err(ErrUnknownRatchetRelation)?;
    }

    fn equal(&self, right: &Spiral) -> bool {
        self.small == right.small
            && self.small_counter == right.small_counter
            && self.medium == right.medium
            && self.medium_counter == right.medium_counter
            && self.large == right.large
    }

    // known_after is probabilistic. Returns true if self is known to be after b, and false
    // if large counters are inequal (meaning r is before, equal, unrelated, or after)
    fn known_after(left: Self, right: Spiral) -> bool {
        left.large == right.large
            && left.medium_counter > right.medium_counter
            && left.small_counter > right.small_counter
    }
}

fn inc_by(mut r: Spiral, n: isize) -> (Spiral, isize) {
    if n <= 0 {
        return (r, 0);
    } else if n >= 256 * 256 - r.combined_counter() {
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
    (Spiral::zero(r.large), 256 * 256 - r.combined_counter())
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
    (jumped, jump_count)
}

fn decode_spiral(s: String) -> Result<Spiral, Box<dyn error::Error>> {
    if s.len() != 133 {
        Err(ErrBadLen)?
    }
    if &s[0..2] != RATCHET_SIGNIFIER {
        Err(ErrBadEncoding(s[0..2].to_string()))?
    }
    let d = base64::decode(s)?;

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

fn shasum_from_hex(s: &str) -> Result<[u8; 32], hex::FromHexError> {
    <[u8; 32]>::from_hex(s)
}

fn shasum_to_hex(b: [u8; 32]) -> String {
    hex::encode(b)
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
    for i in 0..n {
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

    // TODO: test failing, encoding not correct string length
    // #[test]
    // fn test_ratchet_encode() {
    //     let seed =
    //         shasum_from_hex("600b56e66b7d12e08fd58544d7c811db0063d7aa467a1f6be39990fed0ca5b33")
    //             .unwrap();
    //     let a = Spiral::zero(seed);
    //     let encoded = a.encode();

    //     let b = decode_spiral(encoded).unwrap();
    //     assert_ratchet_equal(a, b);
    // }

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
