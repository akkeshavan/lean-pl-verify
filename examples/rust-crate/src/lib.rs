// examples/verified_fns.rs
//
// Rust source for the functions verified in LeanPlVerify.
// These functions were processed through Charon (https://github.com/AeneasVerif/charon)
// to produce LLBC ASTs; the ASTs are encoded verbatim as `LLBCFunDef` terms
// in Translation/ElabSpec.lean.
//
// Charon command:
//   charon --input examples/verified_fns.rs --output examples/verified_fns.llbc
//
// LLBC memory layout (Charon convention):
//   locals[0]   = return slot (_0 in MIR)
//   locals[1..] = parameters left-to-right, then temporaries

#![allow(unused)]

// F1 ── return42 ─────────────────────────────────────────────────────────
// Lean: def return42Fun : LLBCFunDef := { body := .assign (.var 0) (.use (.const (.int 42 .I32))) .return_ }
pub fn return42() -> i32 { 42 }

// F2 ── id ────────────────────────────────────────────────────────────────
// Lean: body := .assign (.var 0) (.use (.copy (.var 1))) .return_
pub fn id(x: i32) -> i32 { x }

// F3 ── neg ───────────────────────────────────────────────────────────────
// Lean: body := .assign (.var 0) (.unOp .neg (.copy (.var 1))) .return_
pub fn neg(x: i32) -> i32 { -x }

// F4 ── add ───────────────────────────────────────────────────────────────
// Lean: body := .assign (.var 3) (.binOp .add (.copy (.var 1)) (.copy (.var 2)))
//              (.assign (.var 0) (.use (.copy (.var 3))) .return_)
// Panics on overflow — modelled as .arithmeticOverflow in our interpreter.
pub fn add(x: i32, y: i32) -> i32 { x + y }

// F5 ── sub ───────────────────────────────────────────────────────────────
pub fn sub(x: i32, y: i32) -> i32 { x - y }

// F6 ── max ───────────────────────────────────────────────────────────────
// Lean: .assign (.var 3) (.binOp .ge ...) (.ite (.copy (.var 3)) ...)
pub fn max(a: i32, b: i32) -> i32 { if a >= b { a } else { b } }

// F7 ── abs ───────────────────────────────────────────────────────────────
pub fn abs(x: i32) -> i32 { if x >= 0 { x } else { -x } }

// F8 ── is_zero ───────────────────────────────────────────────────────────
pub fn is_zero(x: i32) -> bool { x == 0 }

// F9 ── not_gate ──────────────────────────────────────────────────────────
pub fn not_gate(b: bool) -> bool { !b }

// F10 ── clamp ────────────────────────────────────────────────────────────
pub fn clamp(x: i32, lo: i32, hi: i32) -> i32 {
    if x < lo { lo } else if x > hi { hi } else { x }
}

// F11 ── sum_to ───────────────────────────────────────────────────────────
// Loop body stored in LoopInvariant.lean as `sumToBody`.
// Proven: sum_to(n) = n*(n-1)/2  for all safe n.
//
// Charon LLBC (abridged, 6 locals: ret, n, s, i, cond, tmp):
//   s = 0; i = 0;
//   loop {
//     cond = i < n;
//     if cond { tmp = s + i; s = tmp; tmp = i + 1; i = tmp } else { break }
//   }
//   ret = s; return
pub fn sum_to(n: i32) -> i32 {
    let mut s = 0i32;
    let mut i = 0i32;
    while i < n {
        s += i;
        i += 1;
    }
    s
}

// F12 ── fact ─────────────────────────────────────────────────────────────
// Loop body stored in FactInvariant.lean as `factBody`.
// Proven: fact(n) = n!  for 0 ≤ n ≤ 12.
//
// Charon LLBC (6 locals: ret, n, acc, i, cond, tmp):
//   acc = 1; i = 1;
//   loop {
//     cond = i <= n;
//     if cond { tmp = acc * i; acc = tmp; tmp = i + 1; i = tmp } else { break }
//   }
//   ret = acc; return
pub fn fact(n: i32) -> i32 {
    let mut acc = 1i32;
    let mut i = 1i32;
    while i <= n {
        acc *= i;
        i += 1;
    }
    acc
}

// F13 ── mul ──────────────────────────────────────────────────────────────
pub fn mul(x: i32, y: i32) -> i32 { x * y }

// F14 ── min ──────────────────────────────────────────────────────────────
pub fn min(a: i32, b: i32) -> i32 { if a <= b { a } else { b } }

// F15 ── square (cross-call) ───────────────────────────────────────────────
// Calls mul — demonstrates cross-function verification.
pub fn square(x: i32) -> i32 { mul(x, x) }

// F16 ── fib ──────────────────────────────────────────────────────────────
pub fn fib(n: i32) -> i32 {
    let mut a = 0i32;
    let mut b = 1i32;
    let mut i = 0i32;
    while i < n {
        let tmp = a + b;
        a = b;
        b = tmp;
        i += 1;
    }
    a
}

// F17 ── pow ──────────────────────────────────────────────────────────────
// Computes x^n for n >= 0.
// Invariant: result * x^remaining = x^n_original
pub fn pow(x: i32, n: i32) -> i32 {
    let mut result = 1i32;
    let mut i = 0i32;
    while i < n {
        result *= x;
        i += 1;
    }
    result
}

// F18 ── gcd ──────────────────────────────────────────────────────────────
// Euclidean GCD for non-negative inputs.
// Invariant: gcd(x, y) = gcd(a_0, b_0)
pub fn gcd(a: i32, b: i32) -> i32 {
    let mut x = a;
    let mut y = b;
    while y != 0 {
        let t = x % y;
        x = y;
        y = t;
    }
    x
}
