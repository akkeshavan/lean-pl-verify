import Lake
open Lake DSL

package «lean-pl-verify»

-- Mathlib for tactics (norm_num, omega, simp, ring) and real-number proofs
require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

lean_lib «LeanPlVerify» where
  roots := #[`LeanPlVerify]

lean_lib «LeanPlVerifyTests» where
  roots := #[`Tests]

-- Verification hub: `lake build Theorems` kernel-checks all 258 theorems
lean_lib «Theorems» where
  roots := #[`AllTheorems]
  srcDir := "theorems"
