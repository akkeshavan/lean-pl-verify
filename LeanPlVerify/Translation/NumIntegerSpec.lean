/-
  Translation/NumIntegerSpec.lean

  Verification of a function extracted from the `num-integer` v0.1.45 crate
  (https://crates.io/crates/num-integer, ~45M downloads).

  Extraction procedure:
    1. Copied num-integer source from the cargo registry.
    2. Ran `charon cargo --dest-file num_integer.llbc` directly on the source
       (Charon v0.1.197). This produced 359 functions with concrete bodies.
    3. Located `num_integer::{Integer for u32}::is_even` (Trait impl 14, 11 stmts).
    4. Translated the body using charon2lean.py logic; corrected local type
       annotations (the translator defaults to `.int .I32` for deduplicated types
       not yet in its hash-cons table; the body constants are correctly typed).

  What Charon produces for `fn is_even(&self) -> bool { *self % 2 == 0 }`:
    - var1: &u32 (self, deref'd to var3)
    - var4: bool  = (2 == 0)   -- RemainderByZero UB check, always false, dead
    - var2: u32   = var3 % 2
    - var0: bool  = (var2 == 0)

  The RemainderByZero Assert (dropped by translator) and the UB-check assignment
  (var4 = 2 == 0, kept as a dead assignment) are standard Charon outputs for
  signed/unsigned remainder on known-nonzero divisors.

  Theorem count: 5, sorry count: 0.
-/

import LeanPlVerify.Translation.Elaborator
import LeanPlVerify.Spec.Satisfies

namespace LeanPlVerify.LLBC.NumIntegerSpec

open LeanPlVerify LeanPlVerify.LLBC

/-!
## Extracted definition

`Integer::is_even` for `u32` from `num-integer` v0.1.45.
-/

/--
  `num_integer::{Integer for u32}::is_even`.
  Source: num-integer/src/lib.rs, `impl_integer_for_usize!` macro, `is_even` arm.

  Body: `*self % 2 == 0`

  Charon adds a `RemainderByZero` UB check (var4 = `2 == 0`, always false).
  The Assert is dropped; the dead assignment is kept to match the Charon output.
-/
def NumIsEvenU32Fun : LLBCFunDef := {
  name   := "num_integer::is_even<u32>"
  params := [⟨1, .uint .U32, some "self"⟩]
  locals := [
    ⟨0, .bool_,    none⟩,          -- return slot
    ⟨1, .uint .U32, some "self"⟩,  -- self (deref'd by Projection+Deref → var1)
    ⟨2, .uint .U32, none⟩,         -- var2 = *self % 2
    ⟨3, .uint .U32, none⟩,         -- var3 = copy of *self
    ⟨4, .bool_,    none⟩]          -- var4 = UB check: 2 == 0 (dead, always false)
  retTy  := .bool_
  body   :=
    -- var3 = Copy(*self)   [Projection+Deref dropped to identity by translator]
    (.assign (.var 3) (.use (.copy (.var 1)))
    -- var4 = (Const<U32>(2) == Const<U32>(0))   [UB check: divisor 2 ≠ 0]
    (.assign (.var 4) (.binOp .eq (.const (.uint 2 .U32)) (.const (.uint 0 .U32)))
    -- var2 = var3 % 2
    (.assign (.var 2) (.binOp .rem (.move_ (.var 3)) (.const (.uint 2 .U32)))
    -- var0 = (var2 == 0)
    (.assign (.var 0) (.binOp .eq (.move_ (.var 2)) (.const (.uint 0 .U32)))
    .return_))))
}

/-!
## Correctness theorems

All proofs are by `rfl`: the Lean kernel reduces the evaluator call to a
closed term matching the specification.
-/

/-- NI1 (symbolic): `is_even(n) = (n % 2 == 0)` for all `n : Nat`. -/
theorem num_is_even_symbolic (n : Nat) :
    evalFun [] NumIsEvenU32Fun 10 [.uint n] at () |=
      .pureOutput (· = .bool_ (n % 2 == 0)) :=
  ⟨.bool_ (n % 2 == 0), (), rfl, rfl⟩

/-- NI2: `is_even(0) = true`. -/
theorem num_is_even_zero :
    evalFun [] NumIsEvenU32Fun 10 [.uint 0] at () |= .pureOutput (· = .bool_ true) :=
  ⟨.bool_ true, (), rfl, rfl⟩

/-- NI3: `is_even(4) = true`. -/
theorem num_is_even_four :
    evalFun [] NumIsEvenU32Fun 10 [.uint 4] at () |= .pureOutput (· = .bool_ true) :=
  ⟨.bool_ true, (), rfl, rfl⟩

/-- NI4: `is_even(7) = false`. -/
theorem num_is_even_seven :
    evalFun [] NumIsEvenU32Fun 10 [.uint 7] at () |= .pureOutput (· = .bool_ false) :=
  ⟨.bool_ false, (), rfl, rfl⟩

/-- NI5: `is_even` never crashes (no panics for any `u32` input). -/
theorem num_is_even_nocrash (n : Nat) :
    evalFun [] NumIsEvenU32Fun 10 [.uint n] at () |= .nocrash :=
  sat_pureOutput_nocrash (num_is_even_symbolic n)

end LeanPlVerify.LLBC.NumIntegerSpec
