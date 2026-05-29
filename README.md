# lean-pl-verify

**Formal verification of Rust and TypeScript programs in Lean 4.**

lean-pl-verify embeds the LLBC intermediate representation (produced by [Charon](https://github.com/AeneasVerif/charon)) and a TypeScript AST subset into a common Lean 4 framework, then proves functional-correctness theorems about programs in both languages — using an identical specification language.

| Metric | Value |
|--------|-------|
| Total theorems | **281** |
| Sorry count | **0** |
| Languages | Rust (via LLBC/Charon) + TypeScript |
| Rust crates verified | 3 (hand-crafted suite, num-integer v0.1.45, GCD case study) |
| Cross-language unification theorems | 6 (U1–U6) + 2 relational (A7–A8 via `agreesWith`) |
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

# Verify all 281 theorems (0 sorry)
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
| `Spec/ProgramSpec.lean` | `ProgramSpec` inductive: `pureOutput`, `nocrash`, `terminates`, `postcond`, `precond`, `terminatesIn`; plus `agreesWith` standalone def | — |
| `Spec/Satisfies.lean` | `m at s \|= spec` notation; 21 satisfaction lemmas incl. `terminatesIn` + `agreesWith` | 21 |
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
| `Translation/CharonDefs.lean` | **Auto-generated** by `charon2lean.py`: 18 `LLBCFunDef` values extracted from real Rust | — |
| `Translation/CharonSpec.lean` | 57 theorems over auto-generated defs (including `pow`, `gcd`); 0 sorry | 57 |
| `Translation/NumIntegerSpec.lean` | 10 theorems for `is_even` + `is_odd` for `u32` from `num-integer` v0.1.45; 0 sorry | 10 |
| `Translation/GcdCrateSpec.lean` | 10 theorems: GCD case study — zero args, coprimality, Mathlib bridge, `terminatesIn`; 0 sorry | 10 |

### Proof automation
| File | Contents | Theorems |
|------|----------|----------|
| `Tactic/VerifyFun.lean` | `llbc_verify`, `llbc_verify_loop`, `llbc_verify_cond`, `llbc_verify_prop` | — |
| `Tactic/Examples.lean` | 16 theorems, each proved in one line with the macros | 16 |

### TypeScript (cross-language unification + bug detection)
| File | Contents | Theorems |
|------|----------|----------|
| `TypeScript/AST.lean` | `TSTy`, `TSExpr`, `TSStmt` (includes `while_` and `set_`), `TSFunDef` | — |
| `TypeScript/Elaborator.lean` | `evalTSFun`, `evalStmt`, `evalExpr` — same `RustM` monad as Rust | — |
| `TypeScript/ElabSpec.lean` | T1–T14 functions + U1–U6 cross-language unification + A7–A10 (`agreesWith` + `terminatesIn` demos) | 37 |
| `TypeScript/BugDetection.lean` | B1–B6: bug detection case study (off-by-one, wrong zero guard) | 6 |

**Theorem total: 2 + 4 + 21 + 15 + 48 + 18 + 14 + 14 + 9 + 57 + 10 + 10 + 16 + 37 + 6 = 281**

---

## Running individual modules

You can build and verify any module independently:

```bash
# Foundation
lake build LeanPlVerify.Foundation.Monad
lake build LeanPlVerify.Foundation.Ownership

# Specification framework
lake build LeanPlVerify.Spec.Satisfies
lake build LeanPlVerify.Spec.Examples

# LLBC / Rust verification
lake build LeanPlVerify.Translation.ElabSpec
lake build LeanPlVerify.Translation.Semantics
lake build LeanPlVerify.Translation.Adequacy
lake build LeanPlVerify.Translation.LoopInvariant
lake build LeanPlVerify.Translation.FactInvariant
lake build LeanPlVerify.Translation.FibInvariant

# Charon pipeline (auto-generated + verified)
lake build LeanPlVerify.Translation.CharonDefs
lake build LeanPlVerify.Translation.CharonSpec
lake build LeanPlVerify.Translation.NumIntegerSpec
lake build LeanPlVerify.Translation.GcdCrateSpec

# Proof automation
lake build LeanPlVerify.Tactic.Examples

# TypeScript
lake build LeanPlVerify.TypeScript.ElabSpec
lake build LeanPlVerify.TypeScript.BugDetection
```

---

## Case study: Charon end-to-end pipeline

This pipeline extracts Lean definitions automatically from real Rust source and verifies them.

### Step 1: Install Charon from source

```bash
git clone https://github.com/AeneasVerif/charon
cd charon
git checkout v0.1.197    # pin to the version used in this artifact
cargo build --release
cp target/release/charon ~/.cargo/bin/
cp target/release/charon-driver ~/.cargo/bin/
```

Verify: `charon --version` should print `charon 0.1.197`.

**Note:** Charon requires the `rustc-dev` component for the nightly toolchain, installed in the Prerequisites step.

### Step 2: Run Charon on the example crate

```bash
cd examples/rust-crate
charon cargo --dest-file ../verified_fns.llbc
```

This produces `examples/verified_fns.llbc` — LLBC ASTs for all 18 functions in `src/lib.rs` (return42, id, neg, add, sub, max, abs, is_zero, not_gate, clamp, sum_to, fact, mul, min, square, fib, pow, gcd).

### Step 3: Translate LLBC JSON to Lean

```bash
python3 charon2lean.py examples/verified_fns.llbc \
    LeanPlVerify/Translation/CharonDefs.lean
```

This overwrites `CharonDefs.lean` with one `def <Name>Fun : LLBCFunDef` per function. The existing file is already committed and builds correctly; this step only needs to be run if you modify `verified_fns.rs`.

### Step 4: Verify the generated definitions

```bash
lake build LeanPlVerify.Translation.CharonSpec
```

---

## Case study: num-integer real-crate verification

This case study verifies `Integer::is_even<u32>` and `Integer::is_odd<u32>` extracted directly from the published `num-integer` v0.1.45 crate (~45M downloads on crates.io).

```bash
lake build LeanPlVerify.Translation.NumIntegerSpec
```

10 theorems (NI1–NI10):
- `num_is_even_symbolic` — `is_even(n) = (n % 2 == 0)` for all `n : Nat` (symbolic)
- `num_is_even_zero/four/seven` — ground instances; `num_is_even_nocrash` — no panics
- `num_is_odd_symbolic` — `is_odd(n) = (n % 2 != 0)` for all `n : Nat` (symbolic)
- `num_is_odd_zero/one/seven` — ground instances; `num_is_odd_nocrash` — no panics

To regenerate the LLBC from the original crate (optional):

```bash
cd examples/num-crate
charon cargo --dest-file ../num_verify.llbc
python3 charon2lean.py examples/num_verify.llbc \
    LeanPlVerify/Translation/NumIntegerDefs.lean
```

---

## Case study: GCD algorithm (mathematical properties)

This case study proves richer mathematical properties of the Euclidean GCD algorithm beyond ground instances, including connection to Mathlib's `Nat.gcd`.

```bash
lake build LeanPlVerify.Translation.GcdCrateSpec
```

10 theorems (GS1–GS10):
- `gcd_zero_right (a)` — `gcd(a, 0) = a` (symbolic)
- `gcd_zero_left_5/7` — `gcd(0, 5) = 5`, `gcd(0, 7) = 7`
- `gcd_coprime_7_3` — `gcd(7, 3) = 1` (coprimality)
- `gcd_48_36` — `gcd(48, 36) = 12`
- `gcd_comm_8_12` — `gcd(8, 12) = 4` (commutativity instance, cf. CharonSpec `gcd_12_8`)
- `gcd_mathlib_48_36/100_75` — `Nat.gcd 48 36 = 12`, `Nat.gcd 100 75 = 25` (Mathlib bridge)
- `gcd_both_spec_48_36` — `.both (.pureOutput (·= .int 12)) (.terminatesIn 200)`
- `gcd_nocrash_7_3` — no panics

---

## Case study: TypeScript cross-language unification

TypeScript programs are verified using the same `RustM` monad and `ProgramSpec` specification language as Rust.

```bash
lake build LeanPlVerify.TypeScript.ElabSpec
```

This verifies 37 theorems covering:

- **T1–T14**: Pure TypeScript functions (max, min, add, mul, neg, abs, is_zero, clamp, etc.)
- **U1–U6**: Cross-language unification — Rust LLBC and TypeScript implementations satisfy the *same* `ProgramSpec`
- **while loop**: `ts_sumTo(n) = n*(n-1)/2` proved by induction
- **A7–A8**: `agreesWith` relational theorems — Rust `Value` and TypeScript `TSValue` agree on the underlying integer
- **A9–A10**: Combined `pureOutput + terminatesIn` specs for Rust and TypeScript `neg`

### Cross-language unification (example: U6)

```lean
theorem unified_neg (x : Int) :
    (evalFun [] negFun 10 [.int x] at () |= .pureOutput (· = .int (-x))) ∧
    (evalTSFun tsNegFun 10 [TSValue.num x] at () |= .pureOutput (· = TSValue.num (-x))) :=
  ⟨elab_neg x, elab_ts_neg x⟩
```

The same spec `(.pureOutput (· = -x))` is satisfied by both the Rust LLBC embedding and the TypeScript AST embedding.

### Relational agreement (example: A7)

```lean
theorem unified_neg_agreesWith (x : Int) :
    ProgramSpec.agreesWith
      (evalFun [] negFun 10 [.int x])
      (evalTSFun tsNegFun 10 [TSValue.num x])
      (fun v1 v2 => ∃ r : Int, v1 = .int r ∧ v2 = TSValue.num r)
      ()
```

`agreesWith` is a single relational `Prop` that simultaneously witnesses both executions and the correspondence between their return values.

---

## Case study: TypeScript bug detection

The Lean kernel acts as a bug oracle: if a program definition contains an error, a correctness proof attempt immediately reveals the wrong computed value.

```bash
lake build LeanPlVerify.TypeScript.BugDetection
```

6 theorems in two categories:

| Bug | Description | Kernel outcome |
|-----|-------------|----------------|
| B1 | `sum_to_buggy(5)`: loop uses `<=` instead of `<` | Kernel evaluates to 15 (should be 10) |
| B2 | `sum_to_buggy(10)`: same off-by-one | Kernel evaluates to 55 (should be 45) |
| B3 | `safeDivBuggy(10, -2)`: guard `b > 0` misses negatives | Kernel evaluates to 0 (should be -5) |
| B4 | Fixed `safeDiv(10, -2)` | Kernel confirms -5 ✓ |
| B5 | Fixed `safeDiv(10, 3)` | Kernel confirms 3 ✓ |
| B6 | Fixed `safeDiv(10, 0)` | Kernel confirms 0 (no panic) ✓ |

All 6 theorems are proved by `rfl` — no tactic machinery required.

---

## Troubleshooting

**`lake exe cache get` fails with 404**
Mathlib caching is tied to the exact Lean toolchain version. If the cache is unavailable for `v4.30.0-rc2`, let Mathlib compile from source (takes 30–60 min):
```bash
lake build Mathlib
lake build Theorems
```

**`charon cargo` fails with "can't find crate for `rustc_driver`"**
The `rustc-dev` component is missing:
```bash
rustup component add rustc-dev --toolchain nightly-2026-02-07
```

**`charon` binary not found**
```bash
cp charon/target/release/charon ~/.cargo/bin/
cp charon/target/release/charon-driver ~/.cargo/bin/
```

**`lake build Theorems` fails with "unknown identifier" errors**
The Lean toolchain version is wrong. Verify:
```bash
cat lean-toolchain     # should print: leanprover/lean4:v4.30.0-rc2
lean --version         # should match
```
If elan is not managing the toolchain: `elan override set leanprover/lean4:v4.30.0-rc2`

**`lake build` is extremely slow**
The first build downloads and compiles Mathlib. Run `lake exe cache get` first to download pre-built Mathlib oleans (~1 GB, one-time download).

**Python script fails with `KeyError` or `AttributeError`**
The Charon LLBC JSON format is version-specific. The script targets Charon v0.1.197. Pin to that version as described above.

**`charon cargo` fails with "Override `nightly-2026-02-07` is not installed"**
```bash
rustup toolchain install nightly-2026-02-07
rustup component add rustc-dev rust-src --toolchain nightly-2026-02-07
```

---

## Repository structure

```
lean-pl-verify/
├── LeanPlVerify/
│   ├── Foundation/         # RustM monad, ownership model
│   ├── Spec/               # ProgramSpec language and combinators
│   ├── Translation/        # LLBC AST, interpreter, semantics, adequacy,
│   │                       # loop invariants, Charon pipeline, NumInteger
│   ├── Tactic/             # Proof automation macros
│   └── TypeScript/         # TypeScript AST, evaluator, specs, bug detection
├── theorems/
│   └── AllTheorems.lean    # Single import hub: `lake build Theorems`
├── examples/
│   ├── rust-crate/         # Rust source for Charon extraction (verified_fns.rs)
│   └── num-crate/          # Wrapper crate for num-integer extraction
├── charon2lean.py          # LLBC JSON → LLBCFunDef translator
├── lakefile.lean
└── lean-toolchain          # leanprover/lean4:v4.30.0-rc2
```

---

## Author

**Anand Kumar Keshavan**
Independent Researcher, Pune, India
ORCID: [0009-0007-8541-5203](https://orcid.org/0009-0007-8541-5203)

---

## License

MIT
