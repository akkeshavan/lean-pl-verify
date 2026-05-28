/-
  Spec/ProgramSpec.lean

  A declarative specification language for Rust (and TypeScript) programs.

  Analogous to `CircuitSpec n` in lean-qverify, `ProgramSpec σ α` is an
  inductive type whose constructors name the properties we can assert:

    · pureOutput P   — return value satisfies P (and no panic occurred)
    · nocrash        — computation does not panic
    · terminates     — computation terminates (always true for Lean defs)
    · withFuel n s   — spec s holds when the loop fuel parameter is n
    · both s1 s2     — conjunction of two specs
    · postcond P     — post-condition over (return_value, final_state)
    · precond P s    — spec s holds whenever precondition P holds on init state

  The |= notation: `m , init |= spec`
  reads "the computation m from initial state init satisfies spec".
-/

import LeanPlVerify.Foundation.Monad

namespace LeanPlVerify

-- ── Specification language ──────────────────────────────────────────────────

inductive ProgramSpec (σ α : Type) : Type where
  /-- Return value satisfies predicate P; implicitly: no panic. -/
  | pureOutput : (α → Prop) → ProgramSpec σ α

  /-- Computation never panics (for any reachable execution). -/
  | nocrash    : ProgramSpec σ α

  /-- Computation terminates (trivially true in Lean's total setting). -/
  | terminates : ProgramSpec σ α

  /-- Spec holds when loop fuel is exactly n (used for fuel-parameterised loops). -/
  | withFuel   : Nat → ProgramSpec σ α → ProgramSpec σ α

  /-- Both sub-specs hold simultaneously. -/
  | both       : ProgramSpec σ α → ProgramSpec σ α → ProgramSpec σ α

  /-- Post-condition over (return value, final state). -/
  | postcond   : (α → σ → Prop) → ProgramSpec σ α

  /-- Conditionally: if init state satisfies P, then sub-spec holds. -/
  | precond    : (σ → Prop) → ProgramSpec σ α → ProgramSpec σ α

-- ── Satisfaction relation ───────────────────────────────────────────────────

/--
  `ProgramSpec.satisfies m init s`:
  the RustM computation `m`, run from initial state `init`, satisfies spec `s`.
-/
def ProgramSpec.satisfies {σ α : Type}
    (m : RustM σ α) (init : σ) : ProgramSpec σ α → Prop
  | .pureOutput P =>
      ∃ v s', m init = Except.ok (v, s') ∧ P v

  | .nocrash =>
      ∃ v s', m init = Except.ok (v, s')

  | .terminates =>
      True   -- Lean functions always terminate

  | .withFuel _ s' =>
      ProgramSpec.satisfies m init s'

  | .both s1 s2 =>
      ProgramSpec.satisfies m init s1 ∧
      ProgramSpec.satisfies m init s2

  | .postcond P =>
      ∃ v s', m init = Except.ok (v, s') ∧ P v s'

  | .precond P s' =>
      P init → ProgramSpec.satisfies m init s'

-- ── Notation ────────────────────────────────────────────────────────────────

/-- `m at init |= spec`  reads as: m run from state init satisfies spec. -/
notation:50 m " at " init " |= " spec => ProgramSpec.satisfies m init spec

-- ── Derived spec combinators ────────────────────────────────────────────────

/-- Spec for a function that returns exactly a given value. -/
def ProgramSpec.returnsExact {σ α : Type} [DecidableEq α] (expected : α) :
    ProgramSpec σ α :=
  .pureOutput (· = expected)

/-- Spec asserting the final state satisfies a predicate. -/
def ProgramSpec.finalState {σ α : Type} (P : σ → Prop) : ProgramSpec σ α :=
  .postcond (fun _ s' => P s')

/-- Conjunction of a list of specs. -/
def ProgramSpec.all {σ α : Type} : List (ProgramSpec σ α) → ProgramSpec σ α
  | []      => .terminates
  | [s]     => s
  | s :: ss => .both s (.all ss)

end LeanPlVerify
