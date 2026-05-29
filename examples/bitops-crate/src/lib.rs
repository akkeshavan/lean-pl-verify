// bitops-verify/src/lib.rs
//
// Bitflags-style set operations over u32 values.
// These are the core operations that the `bitflags` crate generates for
// each flags type.  Implemented here as plain functions so that Charon
// can extract them directly.
//
// All functions are pure, safe, and operate on the underlying u32 representation.

#![allow(unused)]

/// Returns true if no bits are set.
pub fn bf_is_empty(flags: u32) -> bool {
    flags == 0
}

/// Returns true if all bits in `other` are set in `flags`.
pub fn bf_contains(flags: u32, other: u32) -> bool {
    flags & other == other
}

/// Returns true if at least one bit in `other` is set in `flags`.
pub fn bf_intersects(flags: u32, other: u32) -> bool {
    flags & other != 0
}

/// Returns the union (bitwise OR) of two flag sets.
pub fn bf_union(a: u32, b: u32) -> u32 {
    a | b
}

/// Returns the intersection (bitwise AND) of two flag sets.
pub fn bf_intersection(a: u32, b: u32) -> u32 {
    a & b
}

/// Returns the symmetric difference (bitwise XOR) of two flag sets.
pub fn bf_symmetric_diff(a: u32, b: u32) -> u32 {
    a ^ b
}
