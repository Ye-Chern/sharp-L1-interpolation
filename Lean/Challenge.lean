module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.RingTheory.Polynomial.Chebyshev

public section

/-!
# Sharp Second Constants in $L^1$ Landau–Kolmogorov Inequalities on a Finite Interval

This file states Theorem 1 of *Sharp Second Constants in $L^1$ Landau--Kolmogorov Inequalities
on a Finite Interval* using only Lean core and Mathlib definitions.

For every order `n = k + 1 ≥ 1` and every compact interval `[a, b]` (`a < b`, length `L = b - a`):
1. The Jacobi node polynomial `U_{n+1}(y) - 2t U_n(y) + t^2 U_{n-1}(y)` admits a unique strictly
   increasing root family `u : ℝ → Fin (n + 1) → ℝ`, whose moving-node error profile `E_n(t)` is
   differentiable with `E_n'(t) < 0` on `(0, 1)`, strictly decreasing on `[0, 1]`, and uniquely
   maximized on `[-1, 1]` at `t = 0` with closed-form value `B_n`.
2. Every function `f` in the one-dimensional Sobolev space `W^{n+1,1}([a, b])` (iterated
   absolutely continuous functions represented via continuous derivatives `d 0, ..., d n`,
   integrable `d (n + 1)`, and the Fundamental Theorem of Calculus) satisfies
   `‖f^(n)‖_{L¹[a,b]} ≤ 4^n n! L^(-n) ‖f‖_{L¹[a,b]} + (L/2) B_n ‖f^(n+1)‖_{L¹[a,b]}`.
3. Both constants are optimal even when restricted to `C^∞` functions.
4. For `f ∈ C^{n+1}([a, b])`, equality holds if and only if
   `f(x) = c * U_n((2x - a - b) / (b - a))` for some `c : ℝ`.
-/

open scoped ContDiff

/-- **Theorem 1** (Sharp all-`L¹` Landau–Kolmogorov inequality and center maximum on `[a, b]`).
All four parts hold unconditionally for every order `n = k + 1 ≥ 1` and every `a < b`. -/
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
  sorry
