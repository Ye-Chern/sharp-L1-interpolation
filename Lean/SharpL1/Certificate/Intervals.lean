import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Continuous interval bounds from integer certificates

The four sign expectations are stored in units of 1/S. The interval arithmetic
in this file is independent of the probabilistic formulas that provide them.
-/

namespace SharpL1.Certificate

/-- Signs of the core quadratic form and the three augmentations in paper.tex. -/
structure Signs (α : Type) where
  core : α
  plus : α
  minus : α
  both : α
  deriving Repr

/-- The integer lower bound for 2 S H′ on an interval. -/
def intervalMargin (n : ℕ) (lower upper : Signs ℤ) : ℤ :=
  lower.plus + lower.minus + n * (lower.both - upper.core)

/-- The third-derivative bound from the origin-neighborhood argument. -/
def originBound (n : ℕ) : ℤ :=
  6 * ((n : ℤ) + 1) * ((n : ℤ) + 3) * ((n : ℤ) + 4)

def checkOrigin (n : ℕ) (s t : ℤ) (lower upper : Signs ℤ) : Bool :=
  decide (4 * originBound n * t ^ 2 < intervalMargin n lower upper * s)

/-- Given componentwise bounds at one parameter, the signed combination uses
the upper bound on the core term, which occurs with a negative coefficient. -/
theorem intervalMargin_le (n : ℕ) (s : ℤ) (lower upper : Signs ℤ)
    (signs : Signs ℝ) (derivative : ℝ)
    (hplus : (lower.plus : ℝ) ≤ (s : ℝ) * signs.plus)
    (hminus : (lower.minus : ℝ) ≤ (s : ℝ) * signs.minus)
    (hboth : (lower.both : ℝ) ≤ (s : ℝ) * signs.both)
    (hcore : (s : ℝ) * signs.core ≤ (upper.core : ℝ))
    (hderivative :
      2 * derivative = signs.plus + signs.minus + n * (signs.both - signs.core)) :
    (intervalMargin n lower upper : ℝ) ≤ 2 * s * derivative := by
  have hdiff := sub_le_sub hboth hcore
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hscaled := mul_le_mul_of_nonneg_left hdiff hn
  push_cast [intervalMargin]
  nlinarith [congrArg ((s : ℝ) * ·) hderivative]

/-- The componentwise monotonicity transports the endpoint constraints to
each point of the interval. -/
theorem intervalMargin_le_on (n : ℕ) (s : ℤ) (hs : 0 < s)
    (lower upper : Signs ℤ) (signs : ℝ → Signs ℝ) (a b x : ℝ)
    (hax : a ≤ x) (hxb : x ≤ b)
    (hplus : Monotone (fun y => (signs y).plus))
    (hminus : Monotone (fun y => (signs y).minus))
    (hboth : Monotone (fun y => (signs y).both))
    (hcore : Monotone (fun y => (signs y).core))
    (hla : (lower.plus : ℝ) ≤ (s : ℝ) * (signs a).plus ∧
      (lower.minus : ℝ) ≤ (s : ℝ) * (signs a).minus ∧
      (lower.both : ℝ) ≤ (s : ℝ) * (signs a).both)
    (hub : (s : ℝ) * (signs b).core ≤ (upper.core : ℝ))
    (derivative : ℝ)
    (hderivative : 2 * derivative =
      (signs x).plus + (signs x).minus + n * ((signs x).both - (signs x).core)) :
    (intervalMargin n lower upper : ℝ) ≤ 2 * s * derivative := by
  have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
  exact intervalMargin_le n s lower upper (signs x) derivative
    (hla.1.trans (mul_le_mul_of_nonneg_left (hplus hax) hs'))
    (hla.2.1.trans (mul_le_mul_of_nonneg_left (hminus hax) hs'))
    (hla.2.2.trans (mul_le_mul_of_nonneg_left (hboth hax) hs'))
    ((mul_le_mul_of_nonneg_left (hcore hxb) hs').trans hub) hderivative

theorem derivative_pos_of_margin (n : ℕ) (s : ℤ) (hs : 0 < s)
    (lower upper : Signs ℤ) (derivative : ℝ)
    (hmargin : 0 < intervalMargin n lower upper)
    (h : (intervalMargin n lower upper : ℝ) ≤ 2 * s * derivative) :
    0 < derivative := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hpos : (0 : ℝ) < (intervalMargin n lower upper : ℝ) := by exact_mod_cast hmargin
  exact pos_of_mul_pos_right (hpos.trans_le h) (by positivity : 0 ≤ 2 * (s : ℝ))

/-- Rescale the integer test to H′(a)/a > 2 M a with a = T/S. -/
theorem origin_slope (n : ℕ) (s t : ℤ) (hs : 0 < s) (ht : 0 < t)
    (lower upper : Signs ℤ) (derivative : ℝ)
    (hcheck : checkOrigin n s t lower upper = true)
    (h : (intervalMargin n lower upper : ℝ) ≤ 2 * s * derivative) :
    2 * (originBound n : ℝ) * ((t : ℝ) / s) < derivative / ((t : ℝ) / s) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have htest : 4 * (originBound n : ℝ) * (t : ℝ) ^ 2 <
      (intervalMargin n lower upper : ℝ) * s := by
    exact_mod_cast of_decide_eq_true hcheck
  apply (lt_div_iff₀ (div_pos ht' hs')).2
  have hrewrite : 2 * (originBound n : ℝ) * ((t : ℝ) / s) * ((t : ℝ) / s) =
      (2 * (originBound n : ℝ) * (t : ℝ) ^ 2) / (s : ℝ) ^ 2 := by
    field_simp
  rw [hrewrite]
  apply (div_lt_iff₀ (show (0 : ℝ) < (s : ℝ) ^ 2 by positivity)).2
  nlinarith [mul_le_mul_of_nonneg_right h hs'.le]

end SharpL1.Certificate
