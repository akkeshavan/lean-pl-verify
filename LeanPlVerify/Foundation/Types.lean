/-
  Foundation/Types.lean

  Models Rust primitive types in Lean 4.

  Design principle: safe Rust programs are functionally pure — ownership and
  borrow-checking eliminate aliasing, so values are mathematical objects.
  We model types as plain Lean types; overflow and bounds are captured as
  proof obligations on theorems, not runtime checks.
-/

namespace LeanPlVerify

-- ── Integer types ──────────────────────────────────────────────────────────
-- Signed integers as Int (unbounded). Overflow properties are stated
-- explicitly in specs when needed (e.g., `v ≥ Int.minI32`).

abbrev I8    := Int
abbrev I16   := Int
abbrev I32   := Int
abbrev I64   := Int
abbrev I128  := Int
abbrev Isize := Int

-- Unsigned integers as Nat (unbounded).
-- Wrapping/saturating behaviour captured as separate lemmas.

abbrev U8    := Nat
abbrev U16   := Nat
abbrev U32   := Nat
abbrev U64   := Nat
abbrev U128  := Nat
abbrev Usize := Nat

-- ── Integer bounds ─────────────────────────────────────────────────────────

namespace IntBounds

def minI8   : I8  := -128
def maxI8   : I8  :=  127
def minI16  : I16 := -32768
def maxI16  : I16 :=  32767
def minI32  : I32 := -2147483648
def maxI32  : I32 :=  2147483647
def minI64  : I64 := -9223372036854775808
def maxI64  : I64 :=  9223372036854775807

def maxU8   : U8  := 255
def maxU16  : U16 := 65535
def maxU32  : U32 := 4294967295
def maxU64  : U64 := 18446744073709551615

/-- Predicate: value is within i32 range -/
def inRangeI32 (v : I32) : Prop := minI32 ≤ v ∧ v ≤ maxI32

/-- Predicate: value is within i64 range -/
def inRangeI64 (v : I64) : Prop := minI64 ≤ v ∧ v ≤ maxI64

end IntBounds

-- ── Panic model ────────────────────────────────────────────────────────────

/-- Every way a safe Rust program can panic at runtime. -/
inductive PanicReason : Type where
  | divisionByZero                       : PanicReason
  | indexOutOfBounds (idx len : Nat)     : PanicReason
  | arithmeticOverflow                   : PanicReason
  | stackOverflow                        : PanicReason
  | explicit (msg : String)              : PanicReason
  | unreachable                          : PanicReason
  deriving Repr, DecidableEq

-- ── Rust sum types ─────────────────────────────────────────────────────────
-- Rust's Option<T> and Result<T,E> map directly to Lean's Option and Except.

abbrev ROption  := @Option          -- Option<T>      ↔  Option T
abbrev RResult  := @Except          -- Result<T,E>    ↔  Except E T

-- ── Boolean ────────────────────────────────────────────────────────────────

abbrev RBool := Bool

-- ── Unit ───────────────────────────────────────────────────────────────────

abbrev RUnit := Unit

end LeanPlVerify
