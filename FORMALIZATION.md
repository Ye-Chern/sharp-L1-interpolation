# Lean Formalization Status

The complete all-$n$ proof in [`chebyshev_L1_complete.tex`](chebyshev_L1_complete.tex) (Theorem 1 `thm:full`) is formalized unconditionally in Lean 4.32.2 / Mathlib inside [`Lean/`](Lean/).

## Verification & Axiom Policy

- Run from `Lean/`:
  ```sh
  LEAN_NUM_THREADS=1 lake build
  LEAN_NUM_THREADS=1 lake env lean Audit.lean
  ```
- Zero `sorry`, zero `admit`, zero `native_decide`, zero custom axioms.
- Every theorem in [`Lean/Audit.lean`](Lean/Audit.lean) depends only on the standard Lean axioms: `propext`, `Classical.choice`, `Quot.sound` (and pure kernel `decide` certificates depend only on `propext`).

## Complete All-$n$ Module Map (`Lean/SharpL1/Analysis/`)

1. **`ChebyshevFirstConstant.lean`** (Section 2, Claim 1 `clm:An`):
   - `chebyshevMonicU`, `chebyshevSign`, `firstBestConstant` ($A_n = 2^n n!$).
   - Moment orthogonality (`intervalIntegral_chebyshevSign_mul_pow_eq_zero`), exact $L^1$ norm (`intervalIntegral_abs_chebyshevMonicU`), sharp polynomial $L^1$ inequality (`polynomial_L1_deriv_le`, `firstBestConstant_le_of_poly_bound`), and polynomial extremizer uniqueness (`polynomial_L1_deriv_eq_iff`).
2. **`GlobalNodes.lean`** (Section 3):
   - Full-interval `orderedNode` theory on $[-1, 1]$: `continuous_orderedNode`, `orderedNode_neg`, `hasDerivAt_orderedNode_neg`, exact endpoint/center values (`orderedNode_neg_one`, `orderedNode_one`, `orderedNode_zero`, `chebyshevGrid`), `orderedNode_strictMonoOn_Icc`, `orderedNode_bijOn_Icc`, `orderedNode_last_gt_half`.
3. **`DividedCDFBridge.lean`**:
   - Bridges `weightedExpSum` / `weightedCdfZero` / `lawSignMean` to `barycentricDividedDifferenceOn` of `truncatedPower`, culminating in `lawSignMean_Hcomp_of_nodes` (eq. (9)).
4. **`FirstTermPos.lean`** (Section 5, Claim 4 `clm:first-term`):
   - `firstTerm_lawSignMean_pos` and `firstTerm_weightedCdfZero_pos` for all $n \ge 1, t > 0$, proved via real-pair Gaussian quadratic forms (`pairQuadForm_pencil_law`), alternating-sign orthogonal invariance (`altSignEquiv`), and explicit witness `((x0, 0), 1/2)`.
5. **`ChordIntegral.lean`** (Section 5, Claim 5 `clm:chord`):
   - `blaschke`, `chordDelta`, `barycentricDelta_eq_chordDelta`, `lawSignMean_diff_eq_chordDelta` for all $n \ge 1, t \in (0, 1)$, proved via Lagrange partial fractions, the Joukowsky vertical-chord loop, and elementary `Complex.log`/FTC single-pole integrals.
6. **`ExplicitError.lean`** (Sections 4–5):
   - `explicitErrorAt`, `explicitErrorCurve`, `HCurve`, continuity, evenness (`explicitErrorCurve_neg`), boundary values, exact center cosine sum (`explicitErrorCurve_zero`), `HasDerivAt` on $(-1, 1)$, unconditional exterior monotonicity on $[1/2, 1)$ (`explicitErrorDerivCurve_neg_of_Ico_half_one`), eq. (9) decomposition (`deriv_HCurve_eq_lawSignMean`), and conditional `chordDelta > 0` monotonicity (`explicitErrorCurve_strictAntiOn_of_chordDelta_pos`).
7. **`ChordBoundsN4.lean`** (Section 6 & Appendix B.1):
   - `chordDelta_pos_of_ge_four`: $0 < \mathrm{chordDelta}\; n\; t$ for all $n \ge 4$ and $t \in (0, 1/2]$ via polar bounds, Cauchy-Schwarz main-term lower bound, Wallis/half-Beta recurrences, and step ratios $< 1/2$.
8. **`LowOrderMono.lean`** (Section 7 & Appendix B.2):
   - Elementary strict monotonicity for $n = 1, 2$ (`hasDerivAt_explicitError_orderedNode_one`, `hasDerivAt_explicitError_orderedNode_two`), explicit $n = 3$ center bound (`explicitError_orderedNode_three_lt_center`), and kernel-certified 5-block integer fixed-point quadrature (`n3_block0_certified`..`n3_block4_certified` via `decide`) yielding `chordDelta_three_pos` ($0 < \mathrm{chordDelta}\; 3\; t$ on $(0, 1/2]$).
9. **`MovingOperator.lean`** (Sections 3–4):
   - `movingOperator` ($T_n$), `SobolevW1`, `movingOperator_eq_factorial_mul_barycentric`, `movingOperator_poly`, `movingOperator_L1_le`, `SobolevW1.taylor_formula`, `SobolevW1.deriv_sub_movingOperator_eq`, `SobolevW1.L1_deriv_sub_movingOperator_le`, `integral_abs_indicator_sub_movingOperator_eq_explicitError`, `explicitError_center_eq`.
10. **`SharpSobolev.lean`** (Sections 4 & 7, Claim 2 `clm:sharp`):
    - `SobolevW1.ofContDiff`, `SobolevW1.ofContDiffOn`, `SobolevW1.rescaleToUnit`, `sharp_sobolev_unit_le`, `sharp_sobolev_Icc_le`, `sharp_sobolev_contDiffOn_Icc_le`, `sharp_firstConstant_Icc_le`, `sharp_secondConstant_Icc_le`, `sharp_sobolev_contDiffOn_Icc_eq_iff`.
11. **`MainTheorem.lean`** (Theorem 1 `thm:full`):
    - Unconditional all-order monotonicity (`explicitErrorDerivCurve_neg_all_orders`, `explicitErrorCurve_strictAntiOn_Icc_zero_one`), unique center maximum (`explicitErrorCurve_unique_global_max_zero`), and the bundled master theorem `theorem_sharp_L1_interpolation_full` (`sharp_L1_interpolation_W1`, `sharp_L1_interpolation_contDiffOn`, `sharp_L1_interpolation_constants_optimal`, `sharp_L1_interpolation_contDiffOn_eq_iff`).

## Historical Artifacts

The earlier v0.2 finite-certificate infrastructure (`Chebyshev.lean`, `RootBrackets.lean`, `Certificate/*`, `Jacobi*`, `Probability/*`, `certificates/`, `notes/`, `paper.tex`) is preserved in the repository.
