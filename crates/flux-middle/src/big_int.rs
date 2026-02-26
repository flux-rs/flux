use std::{cmp::Ordering, fmt};

use rustc_macros::{Decodable, Encodable};

/// A signed integer in the range [-2^128, 2^128], represented by a `u128` and an explicit sign.
///
/// In the logic, we work mathematical integers so we could represent them with arbitrary precision
/// integers. We instead take the simpler approach of using a fixed size representation that allows
/// us to store any Rust literal, i.e., we can represent both `i128::MIN` and `u128::MAX`. This works
/// because we never do arithmetic. We can change the representation in the future (and use arbitrary
/// precision integers) if this ever becomes a problem, e.g., if we want to do (precise) arithmetic
/// during constant folding.
#[derive(Clone, Debug, Copy, PartialEq, Eq, Hash, Encodable, Decodable)]
pub struct BigInt {
    sign: Sign,
    val: u128,
}

impl PartialOrd for BigInt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BigInt {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.sign, other.sign) {
            (Sign::Negative, Sign::NonNegative) => Ordering::Less,
            (Sign::NonNegative, Sign::Negative) => Ordering::Greater,
            (Sign::NonNegative, Sign::NonNegative) => self.val.cmp(&other.val),
            (Sign::Negative, Sign::Negative) => other.val.cmp(&self.val),
        }
    }
}

/// This are in order so negative is less than non-negative.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Encodable, Decodable, PartialOrd, Ord)]
enum Sign {
    Negative,
    NonNegative,
}

impl BigInt {
    pub const ZERO: BigInt = BigInt { sign: Sign::NonNegative, val: 0 };
    pub const ONE: BigInt = BigInt { sign: Sign::NonNegative, val: 1 };

    pub fn is_negative(&self) -> bool {
        matches!(self.sign, Sign::Negative)
    }

    pub fn abs(&self) -> u128 {
        self.val
    }

    /// Given the bit width of a signed integer type, produces the minimum integer for
    /// that type, i.e., -2^(bit_width - 1).
    pub fn int_min(bit_width: u32) -> BigInt {
        BigInt { sign: Sign::Negative, val: 1u128 << (bit_width - 1) }
    }

    /// Given the bit width of a signed integer type, produces the maximum integer for
    /// that type, i.e., 2^(bit_width - 1) - 1.
    pub fn int_max(bit_width: u32) -> BigInt {
        (i128::MAX >> (128 - bit_width)).into()
    }

    /// Given the bit width of an unsigned integer type, produces the maximum
    /// unsigned integer for that type, i.e., 2^bit_width - 1.
    pub fn uint_max(bit_width: u32) -> BigInt {
        (u128::MAX >> (128 - bit_width)).into()
    }
}

impl From<usize> for BigInt {
    fn from(val: usize) -> Self {
        BigInt { sign: Sign::NonNegative, val: val as u128 }
    }
}

impl From<u128> for BigInt {
    fn from(val: u128) -> Self {
        BigInt { sign: Sign::NonNegative, val }
    }
}

impl From<i128> for BigInt {
    fn from(val: i128) -> Self {
        let sign = if val < 0 { Sign::Negative } else { Sign::NonNegative };
        BigInt { sign, val: val.unsigned_abs() }
    }
}

impl From<i32> for BigInt {
    fn from(val: i32) -> Self {
        // TODO(nilehmann) use Flux to prove this doesn't overflow
        if val < 0 {
            BigInt { sign: Sign::Negative, val: -(val as i64) as u128 }
        } else {
            BigInt { sign: Sign::NonNegative, val: val as u128 }
        }
    }
}

impl From<u32> for BigInt {
    fn from(val: u32) -> Self {
        BigInt { sign: Sign::NonNegative, val: val as u128 }
    }
}

impl From<u64> for BigInt {
    fn from(val: u64) -> Self {
        BigInt { sign: Sign::NonNegative, val: val as u128 }
    }
}

impl fmt::Display for BigInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.sign {
            Sign::NonNegative => write!(f, "{}", self.val),
            Sign::Negative => write!(f, "-{}", self.val),
        }
    }
}
