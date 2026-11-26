import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar inequalities for the Section 6 Fourier estimate

This file formalizes the two pure real-algebraic inequalities from Section 6 of
`paper.tex` (`\label{sec:analytic}`):

1. `traceRatio_scalar_ineq`: with `x = 1 / n` (`0 ≤ x ≤ 1 / 20`) and `y = r^2`
   (`0 ≤ y ≤ 1`), the fourth-order trace bound is strictly below `(31 / 20) * v^2`,
   corresponding to `\eqref{traceRatio}`.
2. `gbound_scalar_ineq`: with `x = 1 / n` (`0 ≤ x ≤ 1 / 20`), the Gaussian scale
   comparison `(24 / 25)^2 * (1 + 6 * x + 3 * x^2) < (1 + 2 * x)^2` used in
   `\eqref{Gbound}`.
-/

namespace SharpL1.Analysis

/-- Fourth-order trace ratio scalar inequality from `paper.tex` Section 6
(`traceRatio`), corresponding to `x = 1 / n` and `y = r^2`. -/
theorem traceRatio_scalar_ineq {x y : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ 1 / 20) (hy0 : 0 ≤ y) (hy : y ≤ 1) :
    3 / 8 + (7 / 4) * x + 6 * y * x * (1 / 2 + 2 * x) +
        y ^ 2 * x ^ 2 * (1 + (9 / 8) * x) <
      (31 / 20) * (1 / 2 + 2 * x + y * x + (3 / 2) * y * x ^ 2) ^ 2 := by
  have hdiff :
      (31 / 20) * (1 / 2 + 2 * x + y * x + (3 / 2) * y * x ^ 2) ^ 2 -
        (3 / 8 + (7 / 4) * x + 6 * y * x * (1 / 2 + 2 * x) +
          y ^ 2 * x ^ 2 * (1 + (9 / 8) * x)) =
        (1 / 80 - (1 / 10) * x) + (109 / 40) * x ^ 2 +
          (1 - y) * ((139 / 40) * x ^ 2 + (29 / 20) * x) +
          y * ((93 / 10) * x ^ 3) +
          y ^ 2 * ((279 / 80) * x ^ 4 + (141 / 40) * x ^ 3 + (11 / 20) * x ^ 2) := by
    ring
  have h1 : 0 < 1 / 80 - (1 / 10) * x := by linarith
  have h2 : 0 ≤ (109 / 40 : ℝ) * x ^ 2 := by positivity
  have h3 : 0 ≤ (1 - y) * ((139 / 40) * x ^ 2 + (29 / 20) * x) := by
    apply mul_nonneg <;> linarith [sq_nonneg x]
  have h4 : 0 ≤ y * ((93 / 10) * x ^ 3) := by positivity
  have h5 : 0 ≤ y ^ 2 * ((279 / 80) * x ^ 4 + (141 / 40) * x ^ 3 + (11 / 20) * x ^ 2) := by
    positivity
  linarith

/-- Specialization of `traceRatio_scalar_ineq` to `x = 1 / n` (`n ≥ 20`) and
`y = r ^ 2` (`|r| ≤ 1`). -/
theorem traceRatio_nat_ineq {n : ℕ} (hn : 20 ≤ n) {r : ℝ} (hr : |r| ≤ 1) :
    3 / 8 + 7 / (4 * (n : ℝ)) + 6 * r ^ 2 / (n : ℝ) * (1 / 2 + 2 / (n : ℝ)) +
        r ^ 4 / (n : ℝ) ^ 2 * (1 + 9 / (8 * (n : ℝ))) <
      (31 / 20) *
        (1 / 2 + 2 / (n : ℝ) + r ^ 2 * ((n : ℝ) + 3 / 2) / (n : ℝ) ^ 2) ^ 2 := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn20 : (20 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hn_pos.le
  have hx : (n : ℝ)⁻¹ ≤ 1 / 20 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) hn20
  have hy0 : 0 ≤ r ^ 2 := sq_nonneg r
  have hy : r ^ 2 ≤ 1 := by nlinarith [abs_le.mp hr]
  have hmain := traceRatio_scalar_ineq hx0 hx hy0 hy
  have heq1 :
      3 / 8 + 7 / (4 * (n : ℝ)) + 6 * r ^ 2 / (n : ℝ) * (1 / 2 + 2 / (n : ℝ)) +
          r ^ 4 / (n : ℝ) ^ 2 * (1 + 9 / (8 * (n : ℝ))) =
        3 / 8 + (7 / 4) * (n : ℝ)⁻¹ + 6 * r ^ 2 * (n : ℝ)⁻¹ * (1 / 2 + 2 * (n : ℝ)⁻¹) +
          (r ^ 2) ^ 2 * (n : ℝ)⁻¹ ^ 2 * (1 + (9 / 8) * (n : ℝ)⁻¹) := by
    field_simp
  have heq2 :
      1 / 2 + 2 / (n : ℝ) + r ^ 2 * ((n : ℝ) + 3 / 2) / (n : ℝ) ^ 2 =
        1 / 2 + 2 * (n : ℝ)⁻¹ + r ^ 2 * (n : ℝ)⁻¹ + (3 / 2) * r ^ 2 * (n : ℝ)⁻¹ ^ 2 := by
    field_simp
    ring
  rw [heq1, heq2]
  exact hmain

/-- Gaussian scale comparison from `paper.tex` Section 6 (`Gbound`),
corresponding to `x = 1 / n`. -/
theorem gbound_scalar_ineq {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 20) :
    (24 / 25 : ℝ) ^ 2 * (1 + 6 * x + 3 * x ^ 2) < (1 + 2 * x) ^ 2 := by
  have hdiff :
      (1 + 2 * x) ^ 2 - (24 / 25 : ℝ) ^ 2 * (1 + 6 * x + 3 * x ^ 2) =
        (49 / 625 - (956 / 625) * x) + (772 / 625) * x ^ 2 := by
    ring
  have h1 : 0 < 49 / 625 - (956 / 625 : ℝ) * x := by linarith
  have h2 : 0 ≤ (772 / 625 : ℝ) * x ^ 2 := by
    rw [sq]
    exact mul_nonneg (by norm_num) (mul_nonneg hx0 hx0)
  linarith

/-- Square-root form of `gbound_scalar_ineq` used directly in `Gbound` to bound
`μ / √(2 * v) ≥ (24 / 25) * r`. -/
theorem gbound_sqrt_lt {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 20) :
    (24 / 25 : ℝ) * Real.sqrt (1 + 6 * x + 3 * x ^ 2) < 1 + 2 * x := by
  have hsq :
      ((24 / 25 : ℝ) * Real.sqrt (1 + 6 * x + 3 * x ^ 2)) ^ 2 < (1 + 2 * x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    exact gbound_scalar_ineq hx0 hx
  nlinarith [Real.sqrt_nonneg (1 + 6 * x + 3 * x ^ 2)]

end SharpL1.Analysis
