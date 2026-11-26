module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.RingTheory.Polynomial.Chebyshev
import SharpL1.Analysis.MainTheorem

public section

/-!
# Proved Solution for Palomar Comparator

Discharges `SharpL1.theorem_sharp_L1_interpolation_full` from `Challenge.lean`
via `SharpL1.Analysis.MainTheorem` using only the standard Lean axioms
`[propext, Quot.sound, Classical.choice]`.
-/

open scoped ContDiff

theorem SharpL1.theorem_sharp_L1_interpolation_full (k : ℕ) {a b : ℝ} (hab : a < b) :
    let B : ℝ :=
      1 - (2 : ℝ) ^ (k + 1) / ((k + 1 : ℕ) + 1) +
        (2 : ℝ) ^ (k + 2) / ((k + 1 : ℕ) + 1) *
          ∑ m ∈ Finset.Icc 1 ((k + 2) / 2),
            (-1 : ℝ) ^ (m - 1) * (Real.cos ((m : ℝ) * Real.pi / ((k + 1 : ℕ) + 2))) ^ (k + 2)
    let A : ℝ := (4 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * (b - a) ^ (-((k + 1 : ℕ) : ℤ))
    let nodePoly : ℝ → Polynomial ℝ := fun t =>
      Polynomial.Chebyshev.U ℝ ((k : ℤ) + 2) -
        Polynomial.C (2 * t) * Polynomial.Chebyshev.U ℝ ((k : ℤ) + 1) +
        Polynomial.C (t ^ 2) * Polynomial.Chebyshev.U ℝ (k : ℤ)
    (∃! u : ℝ → Fin (k + 2) → ℝ,
      (∀ t, StrictMono (u t)) ∧ ∀ t j, (nodePoly t).eval (u t j) = 0) ∧
    (∀ u : ℝ → Fin (k + 2) → ℝ,
      (∀ t, StrictMono (u t)) → (∀ t j, (nodePoly t).eval (u t j) = 0) →
      let E : ℝ → ℝ := fun t =>
        1 - t - (2 : ℝ) ^ (k + 1) / ((k + 1 : ℕ) + 1) * (1 - t) ^ (k + 2) +
          (2 : ℝ) ^ (k + 2) / ((k + 1 : ℕ) + 1) *
            ∑ j : Fin (k + 2), (-1 : ℝ) ^ (k + 1 - j.val) * (max (u t j - t) 0) ^ (k + 2)
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt E (deriv E t) t ∧ deriv E t < 0) ∧
        StrictAntiOn E (Set.Icc (0 : ℝ) 1) ∧
        E 0 = B ∧
        (∀ t ∈ Set.Icc (-1 : ℝ) 1, t ≠ 0 → E t < B)) ∧
    (∀ (f : ℝ → ℝ) (d : ℕ → ℝ → ℝ),
      (∀ x ∈ Set.Icc a b, d 0 x = f x) →
      (∀ j < k + 2, ContinuousOn (d j) (Set.Icc a b)) →
      MeasureTheory.IntegrableOn (d (k + 2)) (Set.Icc a b) MeasureTheory.volume →
      (∀ j < k + 2, ∀ x ∈ Set.Icc a b, d j x - d j a = ∫ t in a..x, d (j + 1) t) →
      ∫ x in a..b, |d (k + 1) x| ≤
        A * (∫ y in a..b, |f y|) + ((b - a) / 2) * B * (∫ t in a..b, |d (k + 2) t|)) ∧
    ((∀ A' B' : ℝ,
      (∀ f : ℝ → ℝ, ContDiff ℝ ∞ f →
        ∫ x in a..b, |iteratedDeriv (k + 1) f x| ≤
          A' * (∫ y in a..b, |f y|) + B' * (∫ t in a..b, |iteratedDeriv (k + 2) f t|)) →
      A ≤ A') ∧
     (∀ B' : ℝ,
      (∀ f : ℝ → ℝ, ContDiff ℝ ∞ f →
        ∫ x in a..b, |iteratedDeriv (k + 1) f x| ≤
          A * (∫ y in a..b, |f y|) + B' * (∫ t in a..b, |iteratedDeriv (k + 2) f t|)) →
      ((b - a) / 2) * B ≤ B')) ∧
    (∀ f : ℝ → ℝ, ContDiffOn ℝ (k + 2) f (Set.Icc a b) →
      ((∫ x in a..b, |iteratedDerivWithin (k + 1) f (Set.Icc a b) x| =
        A * (∫ y in a..b, |f y|) +
          ((b - a) / 2) * B * (∫ t in a..b, |iteratedDerivWithin (k + 2) f (Set.Icc a b) t|)) ↔
      ∃ c : ℝ, ∀ x ∈ Set.Icc a b,
        f x = c * (Polynomial.Chebyshev.U ℝ ((k + 1 : ℕ) : ℤ)).eval
          ((2 * x - a - b) / (b - a)))) := by
  intro B A nodePoly
  obtain ⟨⟨hderiv, hanti, hzero, hmax⟩, hW1, hopt, heq⟩ :=
    SharpL1.Analysis.theorem_sharp_L1_interpolation_full k hab
  have hu_unique : ∀ u : ℝ → Fin (k + 2) → ℝ,
      (∀ t, StrictMono (u t)) → (∀ t j, (nodePoly t).eval (u t j) = 0) →
      u = SharpL1.orderedNode k := by
    intro u hmono hroot
    funext t
    have hS : ∀ x ∈ Finset.univ.image (u t), (SharpL1.nodePolynomial k t).eval x = 0 := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨j, -, rfl⟩
      exact hroot t j
    have hcard : (SharpL1.nodePolynomial k t).natDegree ≤ (Finset.univ.image (u t)).card := by
      rw [SharpL1.natDegree_nodePolynomial,
        Finset.card_image_of_injective Finset.univ (hmono t).injective]
      simp
    have hroots : (SharpL1.nodePolynomial k t).roots = (Finset.univ.image (u t)).val :=
      Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero hS hcard
        (SharpL1.nodePolynomial_ne_zero k t)
    exact SharpL1.orderedNode_eq_of_strictMono_of_roots k t (u t) (hmono t) hroots
  refine ⟨⟨SharpL1.orderedNode k,
      ⟨fun t => SharpL1.orderedNode_strictMono k t,
       fun t j => SharpL1.orderedNode_eval_eq_zero k t j⟩,
      fun u ⟨hmono, hroot⟩ => hu_unique u hmono hroot⟩,
    ?_, ?_, hopt, fun f hf => heq hf⟩
  · intro u hmono hroot
    subst (hu_unique u hmono hroot)
    intro E
    have hE_eq : E = SharpL1.Analysis.explicitErrorCurve (k + 1) := by
      funext t
      rw [SharpL1.Analysis.explicitErrorCurve_succ]
      rfl
    rw [hE_eq]
    refine ⟨fun t ht => ?_, hanti, hzero, hmax⟩
    have ht_abs : |t| < 1 := abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
    have hd := SharpL1.Analysis.hasDerivAt_explicitErrorCurve (Nat.succ_pos k) ht_abs
    exact ⟨hd.deriv ▸ hd, hd.deriv ▸ hderiv t ht⟩
  · intro f d hd0 hcont hint hftc
    exact hW1 ⟨d, hd0, hcont, hint, hftc⟩
