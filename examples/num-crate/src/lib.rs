// examples/num-crate/src/lib.rs
//
// Concrete wrappers around num-integer functions.
// Using explicit turbofish <i64 as Integer>::method to force monomorphisation.

use num_integer::Integer;

/// n % 2 == 0  — from <i64 as Integer>::is_even
pub fn is_even_i64(n: i64) -> bool {
    <i64 as Integer>::is_even(&n)
}

/// n % 2 != 0  — from <i64 as Integer>::is_odd
pub fn is_odd_i64(n: i64) -> bool {
    <i64 as Integer>::is_odd(&n)
}

/// Integer division rounding toward negative infinity
/// — from <i64 as Integer>::div_floor
pub fn div_floor_i64(a: i64, b: i64) -> i64 {
    <i64 as Integer>::div_floor(&a, &b)
}
