module

public import SharpL1.Analysis.DividedCDF
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Slope

public section

/-! ## Differentiation of a truncated power through its knot -/

namespace SharpL1.Analysis

open Filter Set Topology

/-- If the lower exponent is positive, the derivative formula also holds at
zero. The two one-sided slopes then tend to zero. -/
theorem hasDerivAt_truncatedPower_zero (n : ℕ) (hn : 0 < n) (x : ℝ) :
    HasDerivAt (truncatedPower (n + 1) 0)
      ((n + 1 : ℕ) * truncatedPower n 0 x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have he : truncatedPower (n + 1) 0 =ᶠ[𝓝 x] (fun _ : ℝ => 0) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp [truncatedPower, (show y < 0 from hy).not_ge]
    simpa [truncatedPower, hx.not_ge] using (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he
  · have hn' : n ≠ 0 := Nat.ne_of_gt hn
    have H : HasDerivAt (fun y : ℝ => y ^ (n + 1)) 0 0 := by
      simpa [zero_pow hn'] using hasDerivAt_pow (n + 1) (0 : ℝ)
    simp only [truncatedPower, le_refl, if_true, sub_self, zero_pow hn', mul_zero]
    rw [hasDerivAt_iff_tendsto_slope_left_right] at H ⊢
    constructor
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin (s := Iio (0 : ℝ))] with y hy
      rw [slope_def_field]
      simp [truncatedPower, (show y < 0 from hy).not_ge]
    · refine H.2.congr' ?_
      filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with y hy
      simp [slope_def_field, truncatedPower, (show 0 < y from hy).le]
  · have he : truncatedPower (n + 1) 0 =ᶠ[𝓝 x] (fun y : ℝ => y ^ (n + 1)) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      simp [truncatedPower, (show 0 < y from hy).le]
    simpa [truncatedPower, hx.le] using (hasDerivAt_pow (n + 1) x).congr_of_eventuallyEq he

end SharpL1.Analysis
