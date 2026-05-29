// numint-ext/src/lib.rs
//
// Concrete u32 wrappers around additional num-integer v0.1.45 functions.
// Uses explicit turbofish <u32 as Integer>::method to force monomorphisation
// so that Charon can extract concrete LLBC bodies.
//
// For unsigned integers (u32), these have particularly clean semantics:
//   div_floor(a, b) = a / b          (truncated div = floor div for unsigned)
//   div_ceil(a, b)  = a / b + (a % b != 0 ? 1 : 0)
//   is_multiple_of(a, b) = (b == 0 && a == 0) || (b != 0 && a % b == 0)

#![allow(unused)]

use num_integer::Integer;

/// Integer division rounding toward −∞ (= truncated div for u32).
/// Equivalent to `a / b`.
pub fn div_floor_u32(a: u32, b: u32) -> u32 {
    <u32 as Integer>::div_floor(&a, &b)
}

/// Integer division rounding toward +∞.
/// Equivalent to `a / b + (a % b != 0) as u32`.
pub fn div_ceil_u32(a: u32, b: u32) -> u32 {
    <u32 as Integer>::div_ceil(&a, &b)
}

/// Returns true if `a` is a multiple of `b`.
/// By convention, every integer is a multiple of 0 iff it is 0.
pub fn is_multiple_of_u32(a: u32, b: u32) -> bool {
    <u32 as Integer>::is_multiple_of(&a, &b)
}
