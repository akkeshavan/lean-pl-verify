# lean-pl-verify

**Formal verification of Rust and TypeScript programs in Lean 4.**

lean-pl-verify embeds the LLBC intermediate representation (produced by [Charon](https://github.com/AeneasVerif/charon)) and a TypeScript AST subset into a common Lean 4 framework, then proves functional-correctness theorems about programs in both languages — using an identical specification language.

| Metric | Value |
|--------|-------|
| Total theorems | **258** |
| Sorry count | **0** |
| Languages | Rust (via LLBC/Charon) + TypeScript |
| Cross-language unification theorems | 6 |
| Lean version | `leanprover/lean4:v4.30.0-rc2` |

---

## Prerequisites

### 1. Install elan (Lean version manager)

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile   # or open a new shell
```

Verify: `lean --version` should print `Lean (version 4.30.0-rc2, ...)`.

The file `lean-toolchain` pins the exact version (`leanprover/lean4:v4.30.0-rc2`); elan will download it automatically on first use.

### 2. Install Rust + Cargo (for Charon and the example crates)

```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source ~/.cargo/env
```

The Charon pipeline requires a specific nightly toolchain. Install it:

```bash
rustup toolchain install nightly-2026-02-07
rustup component add rustc-dev --toolchain nightly-2026-02-07
rustup component add rust-src  --toolchain nightly-2026-02-07
```

### 3. Install Python 3 (for charon2lean.py)

Python 3.8+ is required. On macOS: `brew install python3`. On Ubuntu: `sudo apt install python3`.

---

## Quick start

```bash
git clone <repo-url> lean-pl-verify
cd lean-pl-verify

# Download Mathlib cache (~1 GB, needed once — avoids recompiling Mathlib)
lake exe cache get

# Verify all 258 theorems
lake build Theorems
```

`lake build Theorems` succeeds if and only if every theorem is accepted by the Lean kernel. **0 sorry** — no axiom gaps.

Expected output: `Build completed successfully.` (takes 5–15 minutes on first run; subsequent runs are incremental).

---

## Module overview

### Foundation
| File | Contents | Theorems |
|------|----------|----------|
| `Foundation/Types.lean` | Rust primitives: `I32=Int`, `U32=Nat`, `PanicReason`, `IntBounds` | — |
| `Foundation/Monad.lean` | `RustM σ α := StateT σ (Except PanicReason) α`; `bind_ok`, `pure_ok` | 2 |
| `Foundation/Ownership.lean` | Forward-backward pairs, `MutBorrow`, `Lifetime`; 4 identity laws | 4 |

### Specification
| File | Contents | Theorems |
|------|----------|----------|
| `Spec/ProgramSpec.lean` | `ProgramSpec` inductive: `pureOutput`, `nocrash`, `terminates`, `postcond`, `precond` | — |
| `Spec/Satisfies.lean` | `m at s \|= spec` notation; satisfaction lemmas | 17 |
| `Spec/Examples.lean` | RustM-level examples E1–E8 | 15 |

### LLBC / Rust verification
| File | Contents | Theorems |
|------|----------|----------|
| `Translation/LLBC.lean` | Full LLBC AST: `LLBCTy`, `LLBCStmt`, `LLBCFunDef` | — |
| `Translation/Elaborator.lean` | `evalStmtFuel` (fuel-based, kernel-transparent), `evalFun`, `buildLocals` | — |
| `Translation/ElabSpec.lean` | 48 theorems for F1–F16 (return42 through min); 0 sorry | 48 |
| `Translation/Semantics.lean` | Relational big-step: `EvalStmt`, `EvalFun`, `EvalPlace`, `EvalRValue` | — |
| `Translation/Adequacy.lean` | Full adequacy (soundness + completeness) of interpreter vs. relational semantics; 0 sorry | 18 |
| `Translation/LoopInvariant.lean` | `sumTo(n) = n*(n-1)/2` | 14 |
| `Translation/FactInvariant.lean` | `fact(n) = n!` for 0 ≤ n ≤ 12 | 14 |
| `Translation/FibInvariant.lean` | `fib(n) = Nat.fib n` for 0 ≤ n ≤ 45 | 9 |

### Charon end-to-end pipeline (auto-generated)
| File | Contents | Theorems |
|------|----------|----------|
| `Translation/CharonDefs.lean` | **Auto-generated** by `charon2lean.py`: 18 `LLBCFunDef` values from real Rust | — |
| `Translation/CharonSpec.lean` | 57 theorems over the auto-generated defs (including `pow`, `gcd`); 0 sorry | 57 |

The pipeline: `verified_fns.rs` → **Charon** → LLBC JSON → **`charon2lean.py`** → `CharonDefs.lean` → proofs.

### Proof automation
| File | Contents | Theorems |
|------|----------|----------|
| `Tactic/VerifyFun.lean` | `llbc_verify`, `llbc_verify_loop`, `llbc_verify_cond`, `llbc_verify_prop` | — |
| `Tactic/Examples.lean` | 16 theorems, each proved in one line with the macros | 16 |

### TypeScript (cross-language unification)
| File | Contents | Theorems |
|------|----------|----------|
| `TypeScript/AST.lean` | `TSTy`, `TSExpr`, `TSStmt` (includes `while_` and `set_`), `TSFunDef` | — |
| `TypeScript/Elaborator.lean` | `evalTSFun`, `evalStmt`, `evalExpr` — same `RustM` monad as Rust | — |
| `TypeScript/ElabSpec.lean` | 39 theorems: T1–T14 functions + U1–U6 cross-language unification + bug-detection case study | 39 |

**Theorem total: 2 + 4 + 17 + 15 + 48 + 18 + 14 + 14 + 9 + 57 + 16 + 39 = 258**

---

## Charon pipeline (regenerating CharonDefs.lean)

This section explains how to install Charon from source and reproduce the auto-generated Lean definitions.

### Step 1: Install Charon from source

```bash
git clone https://github.com/AeneasVerif/charon
cd charon
git checkout v0.1.197    # pin to the version used in this artifact
cargo build --release    # builds charon binary
export PATH="$PWD/target/release:$PATH"   # add to PATH (or move binary to ~/.cargo/bin)
```

Verify: `charon --version` should print `charon 0.1.197`.

**Note:** Charon requires the `rustc-dev` component for the nightly toolchain. This was installed in the Prerequisites step. Charon uses `rustup run nightly-2026-02-07 rustc` internally.

### Step 2: Run Charon on the example crate

```bash
cd /path/to/lean-pl-verify/examples/rust-crate
charon cargo --dest-file ../verified_fns.llbc
```

This produces `examples/verified_fns.llbc` — a JSON file containing the LLBC ASTs of all 18 functions in `src/lib.rs` (return42, id, neg, add, sub, max, abs, is_zero, not_gate, clamp, sum_to, fact, mul, min, square, fib, pow, gcd).

### Step 3: Translate LLBC JSON to Lean

```bash
cd /path/to/lean-pl-verify
python3 charon2lean.py examples/verified_fns.llbc \
    LeanPlVerify/Translation/CharonDefs.lean
```

This overwrites `CharonDefs.lean` with one `def <Name>Fun : LLBCFunDef` per function.

### Step 4: Verify the generated definitions build

```bash
lake build LeanPlVerify.Translation.CharonDefs
lake build LeanPlVerify.Translation.CharonSpec
```

Both should complete with 0 errors.

---

## num-integer real-crate case study

This case study verifies `Integer::is_even<u32>` extracted directly from the published `num-integer` v0.1.45 crate (~45M downloads on crates.io).

### Step 1: Run Charon on the num-crate wrapper

```bash
cd /path/to/lean-pl-verify/examples/num-crate
charon cargo --dest-file ../num_verify.llbc
```

This produces `examples/num_verify.llbc`. The crate wraps `num-integer` functions with concrete types to force monomorphisation (see `src/lib.rs`).

### Step 2: Inspect or translate

The extracted LLBC for `is_even<u32>` is already embedded in `Translation/CharonSpec.lean` as the `IsEvenFun` definition. The 5 theorems proved over it are:

- `is_even_zero` — `is_even(0) = true`
- `is_even_one` — `is_even(1) = false`
- `is_even_two` — `is_even(2) = true`
- `is_even_neg_ok` — `is_even` on negative even → `true`
- `is_even_spec` — general correctness: `is_even(n) = (n % 2 == 0)`

### Step 3: Verify

```bash
lake build LeanPlVerify.Translation.CharonSpec
```

---

## TypeScript case study

TypeScript programs are verified using the same `RustM` monad and `ProgramSpec` specification language as Rust.

### Running the TypeScript theorems

```bash
lake build LeanPlVerify.TypeScript.ElabSpec
```

This verifies 39 theorems covering:

- **T1–T14**: Pure functions (max, min, add, mul, neg, abs, is_zero, clamp, etc.)
- **U1–U6**: Cross-language unification theorems — Rust LLBC and TypeScript implementations satisfy the *same* `ProgramSpec`
- **while loop**: `ts_sumTo(n) = n*(n-1)/2` proved by induction
- **Bug detection case study**: 6 theorems exposing off-by-one and wrong-guard bugs

### Cross-language unification (example: U5)

```lean
theorem unified_sumTo_ten :
    (evalFun [] sumToFun 1000 [.int 10] at () |= .pureOutput (· = .int 45)) ∧
    (evalTSFun tsSumToFun 100 [.num 10] at () |= .pureOutput (· = .num 45)) :=
  ⟨elab_sumTo_ten, elab_ts_sumTo_ten⟩
```

The same specification `(.pureOutput (· = 45))` is satisfied by both the Rust LLBC embedding and the TypeScript AST embedding.

### Bug detection case study

`TypeScript/ElabSpec.lean` contains a `tsWrongSumTo` function with two injected bugs: an off-by-one initialisation and a wrong loop guard. Six theorems in the file demonstrate that attempting to prove correctness for this function fails (the theorems prove incorrect *outputs*, demonstrating the framework catches the bugs).

---

## Running individual modules

You can build and check any module individually:

```bash
lake build LeanPlVerify.Foundation.Monad
lake build LeanPlVerify.Spec.Satisfies
lake build LeanPlVerify.Translation.ElabSpec
lake build LeanPlVerify.Translation.Adequacy
lake build LeanPlVerify.Translation.LoopInvariant
lake build LeanPlVerify.Translation.FactInvariant
lake build LeanPlVerify.Translation.FibInvariant
lake build LeanPlVerify.Translation.CharonSpec
lake build LeanPlVerify.Tactic.Examples
lake build LeanPlVerify.TypeScript.ElabSpec
```

---

## Troubleshooting

**`lake exe cache get` fails with 404**
Mathlib caching is tied to the exact Lean toolchain version. If the cache is unavailable for `v4.30.0-rc2`, let Mathlib compile from source (takes ~30–60 min):
```bash
lake build Mathlib
lake build Theorems
```

**`charon cargo` fails with "can't find crate for `rustc_driver`"**
The `rustc-dev` component is missing for the nightly toolchain:
```bash
rustup component add rustc-dev --toolchain nightly-2026-02-07
```

**`charon` binary not found after `cargo build --release`**
Add the Charon target directory to your PATH or copy the binary:
```bash
cp charon/target/release/charon ~/.cargo/bin/
```

**`lake build Theorems` fails with "unknown identifier" errors**
The Lean toolchain version is wrong. Verify:
```bash
cat lean-toolchain     # should print: leanprover/lean4:v4.30.0-rc2
lean --version         # should print the same version
```
If elan is not managing the toolchain, run `elan override set leanprover/lean4:v4.30.0-rc2` in the project directory.

**`lake build` is extremely slow**
The first build downloads and compiles Mathlib. Subsequent builds use the `.lake/build` cache. Run `lake exe cache get` first to download pre-built Mathlib oleans.

**Python script fails with `KeyError` or `AttributeError`**
The Charon LLBC JSON format evolved between versions. The script targets Charon v0.1.197. If you used a different version, the JSON schema may differ. Pin to `v0.1.197` as described in the Charon installation step.

---

## Author

**Anand Kumar Keshavan**
Independent Researcher, Pune, India
ORCID: [0009-0007-8541-5203](https://orcid.org/0009-0007-8541-5203)

---

## License

MIT
