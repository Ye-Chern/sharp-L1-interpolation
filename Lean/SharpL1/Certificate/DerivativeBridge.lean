import SharpL1.Certificate.Checker
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.NormNum

/-!
# From a checked partition to continuous derivative positivity

The step from endpoint signs to every intervening real parameter is formalized
here with the probability comparison and the derivative identity as hypotheses.
-/

namespace SharpL1.Certificate

open Set

noncomputable def parameter (t : ℤ) : ℝ := (t : ℝ) / gridScale

theorem checkOrder_derivative_pos (n : ℕ) (rows : List Row) (h : checkOrder n rows = true)
    (signs : ℝ → Signs ℝ) (D : ℝ → ℝ)
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
    (x : ℝ) (hax : parameter originGrid < x) (hxb : x ≤ parameter outerGrid)
    (hformula : 2 * D x =
      (signs x).plus + (signs x).minus + n * ((signs x).both - (signs x).core)) :
    0 < D x := by
  have hs : 0 < gridScale := by decide
  have hs' : (0 : ℝ) < gridScale := by exact_mod_cast hs
  obtain ⟨_, _, first, rest, hrows, hfirst, _, _, htail⟩ := checkOrder_sound n rows h
  have hxfirst : (first.row.t : ℝ) < x * gridScale := by
    rw [hfirst]
    exact (div_lt_iff₀ hs').1 hax
  have hxlast : x * (gridScale : ℝ) ≤ (outerGrid : ℝ) :=
    (le_div_iff₀ hs').1 hxb
  obtain ⟨p, hp, q, hq, hpz, hzq, hm⟩ := htail.covers (x * gridScale) hxfirst hxlast
  have hp' : p ∈ rows.map evaluate := hrows ▸ hp
  have hq' : q ∈ rows.map evaluate := hrows ▸ List.mem_cons_of_mem first hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp'
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq'
  exact derivative_pos_of_margin n gridScale hs _ _ (D x) hm
    (intervalMargin_le_on n gridScale hs _ _ signs (parameter a.t) (parameter b.t) x
      ((div_le_iff₀ hs').2 hpz) ((le_div_iff₀ hs').2 hzq)
      hplus hminus hboth hcore (hlower a ha) (hupper b hb) (D x) hformula)

/-- The mean-value step used to control the part of the origin neighborhood
between zero and the first certified parameter. Here D is H′. -/
theorem origin_derivative_pos (D : ℝ → ℝ) (a M : ℝ) (ha : 0 < a) (hM : 0 ≤ M)
    (hzero : D 0 = 0) (hD : ContinuousOn D (Icc 0 a))
    (hd : DifferentiableOn ℝ D (Ioo 0 a))
    (hbound : ∀ x y, x ∈ Ioo 0 a → y ∈ Ioo 0 a → |deriv D x - deriv D y| ≤ M * |x - y|)
    (hslope : 2 * M * a < D a / a) :
    ∀ x ∈ Ioc 0 a, 0 < D x := by
  obtain ⟨c, hc, hcs⟩ := exists_deriv_eq_slope D ha hD hd
  simp only [hzero, sub_zero] at hcs
  have hdpos (x : ℝ) (hx : x ∈ Ioo 0 a) : 0 < deriv D x := by
    have hdist : |x - c| ≤ a := abs_le.mpr
      ⟨by linarith [hx.1, hc.2], by linarith [hx.2, hc.1]⟩
    have habs := (hbound x c hx hc).trans (mul_le_mul_of_nonneg_left hdist hM)
    have hdiff := (abs_le.mp habs).1
    linarith [mul_nonneg hM ha.le]
  have hstrict : StrictMonoOn D (Icc 0 a) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 a) hD
    intro x hx
    exact hdpos x (by simpa [interior_Icc] using hx)
  intro x hx
  simpa only [hzero] using hstrict ⟨le_rfl, ha.le⟩ ⟨hx.1.le, hx.2⟩ hx.1

end SharpL1.Certificate
