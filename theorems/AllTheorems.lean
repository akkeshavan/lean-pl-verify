/-
  theorems/AllTheorems.lean

  Single import hub: importing this file causes the Lean 4 kernel to type-check
  (and therefore verify) all 281 theorems in the lean-pl-verify project.

  Build command:
    lake build Theorems

  The kernel accepts a proof only when the proof term is well-typed.
  A successful build == every theorem below is verified.

  Sorry status: 0 sorry — all 281 theorems are fully kernel-checked.
  FibInvariant.lean uses native_decide (not sorry) for Nat.fib 46 = 1836311903.

  Full adequacy theorem (Translation/Adequacy.lean):
    · Soundness:    evalStmtFuel env n stmt s = .ok r  →  EvalStmt env stmt s r.1 r.2
    · Completeness: EvalStmt env stmt s sig s'  →  ∃ n, evalStmtFuel env n stmt s = .ok (sig, s')
-/

-- Foundation
import LeanPlVerify.Foundation.Monad       -- 2 theorems
import LeanPlVerify.Foundation.Ownership   -- 4 theorems

-- Specification framework
import LeanPlVerify.Spec.Satisfies         -- 21 theorems (incl. terminatesIn + agreesWith lemmas)
import LeanPlVerify.Spec.Examples          -- 15 theorems

-- LLBC / Rust verification (48 + 14 + 14 + 9 theorems)
import LeanPlVerify.Translation.ElabSpec
import LeanPlVerify.Translation.LoopInvariant
import LeanPlVerify.Translation.FactInvariant
import LeanPlVerify.Translation.FibInvariant

-- Relational semantics and interpreter adequacy (18 theorems, 0 sorry)
import LeanPlVerify.Translation.Semantics
import LeanPlVerify.Translation.Adequacy

-- Proof automation demo (16 theorems)
import LeanPlVerify.Tactic.Examples

-- Charon-extracted Rust verification (57 theorems, 0 sorry)
-- Pipeline: verified_fns.rs → charon → verified_fns.llbc → charon2lean.py → CharonDefs.lean
-- Includes C17: pow (x^n), C18: gcd (Euclidean algorithm via Rem) — added as real-world demo
import LeanPlVerify.Translation.CharonSpec

-- Real crate: num-integer v0.1.45, Integer::is_even + is_odd for u32 (10 theorems, 0 sorry)
-- Extracted via Charon directly on crate source; bodies: n%2==0 / n%2!=0
import LeanPlVerify.Translation.NumIntegerSpec

-- GCD case study: Euclidean algorithm (Charon-extracted), deeper math properties (10 theorems, 0 sorry)
-- GS1–GS10: zero args, coprimality, commutativity witness, Mathlib bridge, terminatesIn
import LeanPlVerify.Translation.GcdCrateSpec

-- TypeScript verification (37 theorems, incl. while loop sum_to + 6 unification + agreesWith/terminatesIn examples)
import LeanPlVerify.TypeScript.ElabSpec

-- TypeScript bug detection case study (6 theorems, 0 sorry)
-- B1-B3: kernel exposes bugs (off-by-one, wrong zero guard)
-- B4-B6: fixed versions verified correct
import LeanPlVerify.TypeScript.BugDetection
