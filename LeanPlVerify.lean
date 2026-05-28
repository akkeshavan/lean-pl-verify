/-
  lean-pl-verify
  Formal verification of programming languages (Rust, TypeScript) via Lean 4.

  Architecture mirrors lean-qverify (quantum circuits → Lean 4) but targets
  imperative systems languages via functional translation.

  Pipeline:
    Source (Rust / TypeScript)
      → IR (LLBC via Charon  |  TypeScript AST via tsc)
      → Lean 4 monadic term  (Foundation.Monad)
      → Specification        (Spec.ProgramSpec)
      → Kernel-checked proof

  Module layout:
    Foundation/  — primitive types, execution monad, ownership/borrow model
    Translation/ — LLBC AST, parser stubs, elaborator
    Spec/        — specification language, satisfaction proofs, examples
    TypeScript/  — TypeScript AST and elaborator (parallel to Translation/)
-/

import LeanPlVerify.Foundation.Types
import LeanPlVerify.Foundation.Monad
import LeanPlVerify.Foundation.Ownership
import LeanPlVerify.Translation.LLBC
import LeanPlVerify.Translation.Elaborator
import LeanPlVerify.Translation.ElabSpec
import LeanPlVerify.Translation.Semantics
import LeanPlVerify.Translation.Adequacy
import LeanPlVerify.Spec.ProgramSpec
import LeanPlVerify.Spec.Satisfies
import LeanPlVerify.Spec.Examples
import LeanPlVerify.TypeScript.Elaborator
import LeanPlVerify.TypeScript.ElabSpec
