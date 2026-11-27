# Lean Pool Feasibility Study

**Target platform:** [`LeanPool/lean-pool`](https://github.com/LeanPool/lean-pool)  
**Assessment basis:** Direct inspection of `lean-pool` (`README.md`, `CONTRIBUTING.md`, `.github/CODE_QUALITY.md`, `lakefile.toml`, `lean-toolchain`, `.github/REVIEW_RULES.md`, `candidates/CRITERIA.txt`) and automated source audit of `D:\work\sharp-L1-interpolation\Lean`.

---

## 1. Executive Summary

- **Verdict: Feasible with targeted cleanup, best pursued right after Palomar Registry acceptance.**
- Per `LeanPool/lean-pool/README.md`: *"Projects accepted to the Palomar Registry may be submitted to Lean Pool, and priority will be given to them."*
- **Important scope note:** `lean-pool` is an AI-maintained archive of **complete formalization projects** (412 projects, ~15M LOC) pinned to a shared monorepo toolchain, **not** a granular single-lemma submission pool. Individual reusable lemmas belong in future Mathlib PRs, while `sharp-L1-interpolation` as a self-contained project fits `LeanPool/SharpL1/` directly.

---

## 2. Compatibility & Gate Audit

### What Already Passes Cleanly
1. **Core closure isolation:** `SharpL1.Analysis.MainTheorem` has a clean **40-module** transitive import closure inside `SharpL1/`. The **14 excluded files** under `SharpL1/` (`SharpL1/Certificate/*` [10 files], `SharpL1/RootBrackets.lean`, and `SharpL1/Analysis/{CenterCriterion,FiniteCenter,FourierScalars}.lean`) plus all 18 files of `SharpL1Data/` and `Audit.lean` are strictly superseded v0.2 CSV/bracket/audit artifacts not needed by `MainTheorem`.
2. **Forbidden constructs (`sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `partial`, `opaque`, `set_option`):**
   - **Zero** occurrences in code across all **40 core modules**! (Note: the only `set_option` in the older repo lived in the excluded `SharpL1/Certificate/CSV.lean`, and `partial` appears only inside documentation comments in `ChordIntegral.lean` and `NodeWeights.lean`.)
   - All audited theorems depend solely on `[propext, Classical.choice, Quot.sound]`, and `n3_block0_certified`..`n3_block4_certified` use kernel `decide` (not `native_decide`).
3. **File size ceiling (10,000 non-blank, non-comment code lines):** Easily satisfied (largest file in the repo is `LowOrderMono.lean` at 2,062 physical lines).
4. **Module system (`requiresModuleSystem = true`):** Once Palomar migration adds `module`, `public import`, `public section`, and `@[expose]` across the codebase, this gate aligns automatically with `lean-pool`.

### Required Gaps to Close Before a Lean Pool PR
1. **Toolchain alignment (`leanprover/lean4:v4.36.0` + `TauCeti`):** Upgrading `D:\work\sharp-L1-palomar\Lean` to `v4.36.0` matches `lean-pool`'s pinned `lean-toolchain` and `mathlib` revision cleanly.
2. **Permissive license (`Apache-2.0` or `MIT`):** `lean-pool` strictly requires `Apache-2.0` or `MIT` (maintainer decision pending).
3. **Drop obsolete v0.2 artifacts:** Submit only the 40-module core `SharpL1` proof chain (plus clean entry `SharpL1.lean`), excluding `Certificate/*`, `SharpL1Data/*`, `RootBrackets`, `FiniteCenter`, `CenterCriterion`, `FourierScalars`, and `Audit` (`#print axioms` diagnostic commands are forbidden by `lean_pool/quality.py`!).
4. **200-line proof cap (`LeanPoolLinters`):** `LeanPoolLinters` treats any tactic/term proof body exceeding 200 lines as a build error (`warningAsError = true`). Automated span analysis across all 40 core modules identified **exactly 6 declarations** above 200 physical lines (declaration header included), plus 3 borderline declarations in the 180–195 line range:
   - `455` lines — `SharpL1/Analysis/LowOrderMono.lean:1352-1806` (`theorem rem3Upper_box_le`)
   - `332` lines — `SharpL1/Analysis/SharpSobolev.lean:1044-1375` (`theorem sharp_secondConstant_unit_le`)
   - `279` lines — `SharpL1/Analysis/FirstTermPos.lean:689-967` (`theorem firstTerm_lawSignMean_pos`)
   - `235` lines — `SharpL1/Analysis/LowOrderMono.lean:1808-2042` (`theorem chordDelta_three_pos_of_check`)
   - `233` lines — `SharpL1/Analysis/ChebyshevFirstConstant.lean:783-1015` (`theorem polynomial_L1_deriv_eq_iff`)
   - `227` lines — `SharpL1/Analysis/SharpSobolev.lean:692-918` (`theorem extremalTruncDiff_L1_identity`)
   - *(Borderline, likely safe once headers/comments excluded, worth checking with `LeanPoolLinters`: `ChordIntegral.lean:barycentricDelta_eq_chordDelta` [192 lines], `MovingOperator.lean:integral_abs_indicator_sub_movingOperator_eq_explicitError` [185 lines], `SharpSobolev.lean:sharp_sobolev_unit_eq_iff_of_continuous_top` [182 lines].)*
   Splitting those 6 proofs into helper lemmas resolves this gate completely.
5. **Compiler hygiene & resource budgets:**
   - Enable and clear `weak.linter.mathlibStandardSet = true` with `warningAsError = true` (zero `Try this` messages from `simp?`/`exact?` or fallback `ring_nf`, zero unused variables, clean 4-line Lean Pool headers, exact module compile logs).
   - Remove `import Mathlib` monolith imports (if any) in favor of specific Mathlib submodules (`python/lean_pool/quality.py` forbids broad `import Mathlib`).
   - Confirm each file builds within CI's `600s` wall-clock and `3 GiB` `RssAnon` budgets.
   - Add `LeanPool/SharpL1/Imports.lean` (via `lake exe mk_all --module`) and `LeanPool/projects/sharp-l1-interpolation.yaml` (`provenance: mix`, `status: verified`, `msc: ["26D10", "41A17", "41A44", "41A50"]`, citing the Palomar entry and English paper).

---

## 3. Recommended Submission Strategy & Reusable Submodules

1. **Primary recommendation:** Wait for **Palomar Registry acceptance** first (using the `palomar/submission-prep` worktree), then submit the trimmed 40-module core `SharpL1` project via `LeanPool/lean-pool`'s **Palomar priority track** (either proposing the repository URL via an issue or opening a clean content PR after extracting the 6 over-200-line proofs and checking `mathlibStandardSet`).
2. **Standalone reusable modules (for future Mathlib / standalone extraction):**
   - `SharpL1/Analysis/ChebyshevFirstConstant.lean` — `sgn U_n` orthogonality to polynomials of degree $< n$, exact $L^1$ norm of monic $2^{-n}U_n$, and the sharp $L^1$ Markov–Nikolskii constant $2^n n!$.
   - `SharpL1/JacobiSpectrum.lean` & `SharpL1/JacobiSymmetry.lean` — simple spectrum, 1D eigenspaces, and centrosymmetry of symmetric tridiagonal Jacobi matrices.
   - `SharpL1/Probability/` (`NoAtom`, `ScaledExponential`, `DifferenceLaw`, `ExponentialRecurrence`, `ExponentialMix`, `WeightedExponential`, `SignMean`, `CDFOrder`) — signed exponential-difference mixture laws and weighted-exponential CDF recurrences.
   - `SharpL1/Analysis/DividedDifference.lean` & `SharpL1/Analysis/TruncatedPowerDeriv.lean` — Finset barycentric divided differences, node-deletion identity, and $C^1$ regularity of $(y - t)_+^n$.
   - `SobolevW1` & integral Taylor remainder in `SharpL1/Analysis/MovingOperator.lean` — 1D iterated-FTC characterization of $W^{m,1}([a,b])$.
   - Half-Beta / Wallis rational step-ratio recurrences currently inside `SharpL1/Analysis/ChordBoundsN4.lean` (worth extracting if upstreamed separately).
