// arith-utils-verify/src/lib.rs
//
// Pure u32 arithmetic utilities analogous to functions in std::u32 and
// the num-integer crate.  All functions are safe, branch-based (no casts),
// and operate only on u32 values so that Charon can extract concrete LLBC.
//
// These are the same operations exposed by std::u32 since Rust 1.73:
//   div_ceil    — ceiling division  (std::u32::div_ceil)
//   abs_diff    — unsigned absolute difference  (std::u32::abs_diff)
//   midpoint    — overflow-safe midpoint  (std::u32::midpoint)
//   is_pow2     — power-of-two test  (std::u32::is_power_of_two)

#![allow(unused)]

/// Ceiling division: smallest integer ≥ a/b.
/// Equivalent to (a + b - 1) / b but avoids overflow for large a.
pub fn div_ceil(a: u32, b: u32) -> u32 {
    if a % b == 0 { a / b } else { a / b + 1 }
}

/// Unsigned absolute difference: |a - b| without overflow.
pub fn abs_diff(a: u32, b: u32) -> u32 {
    if a >= b { a - b } else { b - a }
}

/// Overflow-safe midpoint: floor((a + b) / 2).
/// Uses the identity: floor((a+b)/2) = a/2 + b/2 + (a & b & 1).
pub fn midpoint(a: u32, b: u32) -> u32 {
    a / 2 + b / 2 + (a & b & 1)
}

/// Returns true iff n is a power of two (n = 2^k for some k ≥ 0).
/// Uses the bit trick: n > 0 and (n & (n-1)) == 0.
pub fn is_pow2(n: u32) -> bool {
    if n == 0 { false } else { n & (n - 1) == 0 }
}
