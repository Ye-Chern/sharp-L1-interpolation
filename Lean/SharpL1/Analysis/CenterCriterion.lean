module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic.NormNum

public section

/-! ## One-dimensional criterion for the center maximum -/

namespace SharpL1.Analysis

open Set

/-- In the paper H=1−E. Positive H′ in the central interval, evenness, and
outer monotonicity imply that 0 is its unique minimum on [-1,1]. -/
theorem center_min_of_deriv_and_outer (H : ℝ → ℝ) (heven : Function.Even H)
    (hcont : ContinuousOn H (Icc 0 (1 / 2)))
    (hderiv : ∀ x ∈ Ioo 0 (1 / 2), 0 < deriv H x)
    (houter : MonotoneOn H (Icc (1 / 2) 1)) :
    ∀ x ∈ Icc (-1 : ℝ) 1, x ≠ 0 → H 0 < H x := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hmono : StrictMonoOn H (Icc 0 (1 / 2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 _) hcont
    intro x hx
    exact hderiv x (by simpa [interior_Icc] using hx)
  have hpos (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) : H 0 < H x := by
    by_cases h : x ≤ 1 / 2
    · exact hmono ⟨le_rfl, hhalf.le⟩ ⟨hx.le, h⟩ hx
    · have hh : (1 / 2 : ℝ) ≤ 1 := by norm_num
      have hc := hmono ⟨le_rfl, hhalf.le⟩ ⟨hhalf.le, le_rfl⟩ hhalf
      exact hc.trans_le (houter ⟨le_rfl, hh⟩ ⟨le_of_not_ge h, hx1⟩ (le_of_not_ge h))
  intro x hx hx0
  have h := hpos |x| (abs_pos.mpr hx0) (abs_le.mpr hx)
  by_cases hneg : x < 0
  · rwa [abs_of_neg hneg, heven x] at h
  · rwa [abs_of_nonneg (le_of_not_gt hneg)] at h

end SharpL1.Analysis
