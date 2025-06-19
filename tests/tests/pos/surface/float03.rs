#![feature(core_float_math)]

use core::f32::math::trunc;

pub fn div_euclid(x: f32, rhs: f32) -> f32 {
    let q = trunc(x / rhs);
    if x % rhs < 0.0 {
        return if rhs > 0.0 { q - 1.0 } else { q + 1.0 };
    }
    q
}
