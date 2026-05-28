/-
  Tests/Examples.lean

  Runs the example theorems as a test suite.
  `lake build LeanPlVerifyTests` checks all proofs compile.
-/

import LeanPlVerify.Spec.Examples

-- All #check calls in Examples.lean confirm types compile.
-- Proofs are kernel-checked by Lean's type-checker.

#eval "lean-pl-verify: all example proofs loaded."
