module

public import SharpL1.Analysis.CenterCriterion
public import SharpL1.Certificate.DerivativeBridge

public section

/-! ## The finite certificate implies center minimality given its analytic inputs -/

namespace SharpL1.Analysis

open Set
open SharpL1.Certificate

/-- This is the assembly step for the finite orders of the paper. The
hypotheses identify the interval margins with the real sign expectations,
supply the formula for H′ and its variation near zero, and supply outer
monotonicity. The internal interval and origin comparisons use the checked
integers. -/
theorem center_min_of_checked_order (n : ℕ) (rows : List Row) (hcheck : checkOrder n rows = true)
    (H : ℝ → ℝ) (signs : ℝ → Signs ℝ)
    (heven : Function.Even H) (hcont : ContinuousOn H (Icc 0 (1 / 2)))
    (houter : MonotoneOn H (Icc (1 / 2) 1))
    (hplus : Monotone (fun x => (signs x).plus))
    (hminus : Monotone (fun x => (signs x).minus))
    (hboth : Monotone (fun x => (signs x).both))
    (hcore : Monotone (fun x => (signs x).core))
    (hlower : ∀ row ∈ rows,
      ((evaluate row).lower.plus : ℝ) ≤ (gridScale : ℝ) * (signs (parameter row.t)).plus ∧
      ((evaluate row).lower.minus : ℝ) ≤ (gridScale : ℝ) * (signs (parameter row.t)).minus ∧
      ((evaluate row).lower.both : ℝ) ≤ (gridScale : ℝ) * (signs (parameter row.t)).both)
    (hupper : ∀ row ∈ rows,
      (gridScale : ℝ) * (signs (parameter row.t)).core ≤ ((evaluate row).upper.core : ℝ))
    (hformula : ∀ x ∈ Icc (parameter originGrid) (1 / 2),
      2 * deriv H x = (signs x).plus + (signs x).minus + n * ((signs x).both - (signs x).core))
    (hzero : deriv H 0 = 0)
    (hD : ContinuousOn (deriv H) (Icc 0 (parameter originGrid)))
    (hd : DifferentiableOn ℝ (deriv H) (Ioo 0 (parameter originGrid)))
    (horigin : ∀ x y, x ∈ Ioo 0 (parameter originGrid) → y ∈ Ioo 0 (parameter originGrid) →
      |deriv (deriv H) x - deriv (deriv H) y| ≤ (originBound n : ℝ) * |x - y|) :
    ∀ x ∈ Icc (-1 : ℝ) 1, x ≠ 0 → H 0 < H x := by
  have hs : 0 < gridScale := by decide
  have haInt : 0 < originGrid := by decide
  have ha : 0 < parameter originGrid :=
    div_pos (by exact_mod_cast haInt) (by exact_mod_cast hs)
  have haHalf : parameter originGrid ≤ 1 / 2 := by
    norm_num [parameter, originGrid, gridScale]
  have houterGrid : parameter outerGrid = 1 / 2 := by
    norm_num [parameter, outerGrid, gridScale]
  have hM : (0 : ℝ) ≤ originBound n := by
    push_cast [originBound]
    positivity
  obtain ⟨_, _, first, rest, hrows, ht, _, hcert, _⟩ := checkOrder_sound n rows hcheck
  have hmem : first ∈ rows.map evaluate := by simp [hrows]
  obtain ⟨firstRow, hfirstRow, rfl⟩ := List.mem_map.mp hmem
  have ht' : firstRow.t = originGrid := ht
  have hform : 2 * deriv H (parameter firstRow.t) =
      (signs (parameter firstRow.t)).plus + (signs (parameter firstRow.t)).minus +
        n * ((signs (parameter firstRow.t)).both - (signs (parameter firstRow.t)).core) := by
    rw [ht']
    exact hformula _ ⟨le_rfl, haHalf⟩
  obtain ⟨hplus0, hminus0, hboth0⟩ := hlower firstRow hfirstRow
  have hm := intervalMargin_le n gridScale (evaluate firstRow).lower (evaluate firstRow).upper
    (signs (parameter firstRow.t)) (deriv H (parameter firstRow.t))
    hplus0 hminus0 hboth0 (hupper firstRow hfirstRow) hform
  have hslope : 2 * (originBound n : ℝ) * parameter originGrid <
      deriv H (parameter originGrid) / parameter originGrid := by
    have h := origin_slope n gridScale firstRow.t hs (ht'.symm ▸ haInt)
      (evaluate firstRow).lower (evaluate firstRow).upper
      (deriv H (parameter firstRow.t)) hcert hm
    simpa only [ht', parameter] using h
  apply center_min_of_deriv_and_outer H heven hcont _ houter
  intro x hx
  by_cases h : x ≤ parameter originGrid
  · exact origin_derivative_pos (deriv H) (parameter originGrid) (originBound n) ha hM
      hzero hD hd horigin hslope x ⟨hx.1, h⟩
  · exact checkOrder_derivative_pos n rows hcheck signs (deriv H)
      hplus hminus hboth hcore hlower hupper x (lt_of_not_ge h)
      (houterGrid.symm ▸ hx.2.le) (hformula x ⟨le_of_lt (lt_of_not_ge h), hx.2.le⟩)

end SharpL1.Analysis
