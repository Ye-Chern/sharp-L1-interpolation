module

public import SharpL1.Chebyshev
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

public section

/-!
# Implicit differentiation and node speed for the Jacobi pencil

For order `n = k + 1`, `SharpL1.nodePolynomial k t` is the unnormalized characteristic
polynomial from `paper.tex`, equation `char`:
`p(t, y) = U_{n+1}(y) - 2 t U_n(y) + t^2 U_{n-1}(y)` (with `n = k + 1`).

This file proves:
1. The polynomial Chebyshev derivative identity
   `2 * (1 - X^2) * derivative (U R m) = -m * U R (m + 1) + (m + 2) * U R (m - 1)`
   and the resulting characteristic-polynomial identity at any root `p(t, y) = 0`:
   `2 * (1 - y^2) * ∂_y p(t, y) + L(k + 1, t, y) * ∂_t p(t, y) = 0`,
   where `L(n, t, y) = (n + 2) - 2 * (n + 1) * t * y + n * t^2`.
2. Positivity of `L(n, t, y)` via the sum-of-squares decomposition from Section 3 of `paper.tex`.
3. Automatic simplicity of roots (`∂_t p ≠ 0` and `∂_y p ≠ 0`) when `|t| < 1` and `|y| ≤ 1`.
4. The formal node speed formula `u'(t) = 2 * (1 - u(t)^2) / L(k + 1, t, u(t))` via `HasDerivAt`
   and implicit differentiation along any differentiable branch `u` satisfying `p(s, u(s)) = 0`
   near `t`.
-/

namespace SharpL1

open Polynomial
open Polynomial.Chebyshev (U)

/-- The `t`-partial derivative of `nodePolynomial k t` as a polynomial in `y`:
`∂_t p(t, y) = -2 U_{k+1}(y) + 2 t U_k(y)`. -/
@[expose] noncomputable def nodePolynomialDerivTPoly (k : ℕ) (t : ℝ) : ℝ[X] :=
  -C 2 * U ℝ ((k : ℤ) + 1) + C (2 * t) * U ℝ k

/-- The `t`-partial derivative `∂_t p(t, y) = -2 U_{k+1}(y) + 2 t U_k(y)` evaluated at `y`. -/
@[expose] noncomputable def nodePolynomialDerivT (k : ℕ) (t y : ℝ) : ℝ :=
  -2 * (U ℝ ((k : ℤ) + 1)).eval y + 2 * t * (U ℝ k).eval y

@[simp]
theorem nodePolynomialDerivTPoly_eval (k : ℕ) (t y : ℝ) :
    (nodePolynomialDerivTPoly k t).eval y = nodePolynomialDerivT k t y := by
  simp [nodePolynomialDerivTPoly, nodePolynomialDerivT]

/-- The node speed denominator `L_t(y) = (n + 2) - 2 (n + 1) t y + n t^2` from `paper.tex`,
equation `speed`. For `nodePolynomial k t`, the order is `n = k + 1`. -/
@[expose] def speedDenominator (n : ℕ) (t y : ℝ) : ℝ :=
  (n + 2 : ℝ) - 2 * (n + 1 : ℝ) * t * y + (n : ℝ) * t ^ 2

/-! ### Algebraic identity (Priority 1) -/

/-- Pure polynomial derivative identity for Chebyshev polynomials of the second kind:
`2 (1 - X^2) U_m'(X) = -m U_{m+1}(X) + (m + 2) U_{m-1}(X)`. -/
theorem two_mul_one_sub_X_sq_mul_derivative_U {R : Type*} [CommRing R] (m : ℤ) :
    2 * (1 - X ^ 2) * derivative (U R m) =
      -((m : R[X])) * U R (m + 1) + ((m : R[X]) + 2) * U R (m - 1) := by
  have h1 := Polynomial.Chebyshev.add_one_mul_T_eq_poly_in_U (R := R) m
  have h2 := Polynomial.Chebyshev.two_mul_T_eq_U_sub_U R (m - 1)
  have h3 := Polynomial.Chebyshev.U_add_one R m
  rw [show m - 1 + 2 = m + 1 by ring] at h2
  linear_combination (norm := (push_cast; ring_nf))
    2 * h1 - ((m : R[X]) + 1) * h2 - h3

/-- Polynomial-level identity relating `∂_y p(t, ·)` and `∂_t p(t, ·)` modulo `nodePolynomial k t`. -/
theorem nodePolynomial_speed_poly_identity (k : ℕ) (t : ℝ) :
    2 * (1 - X ^ 2) * derivative (nodePolynomial k t) +
        (C (((k + 1 : ℕ) + 2 : ℝ) + ((k + 1 : ℕ) : ℝ) * t ^ 2) -
          C (2 * ((k + 1 : ℕ) + 1 : ℝ) * t) * X) *
        nodePolynomialDerivTPoly k t =
      (C (2 * ((k + 1 : ℕ) : ℝ) * t) - C (2 * ((k + 1 : ℕ) + 1 : ℝ)) * X) *
        nodePolynomial k t := by
  have d2 := two_mul_one_sub_X_sq_mul_derivative_U (R := ℝ) ((k : ℤ) + 2)
  have d1 := two_mul_one_sub_X_sq_mul_derivative_U (R := ℝ) ((k : ℤ) + 1)
  have d0 := two_mul_one_sub_X_sq_mul_derivative_U (R := ℝ) (k : ℤ)
  have r3 := Polynomial.Chebyshev.U_add_two ℝ ((k : ℤ) + 1)
  have r1 := Polynomial.Chebyshev.U_add_two ℝ ((k : ℤ) - 1)
  rw [show (k : ℤ) + 2 + 1 = (k : ℤ) + 3 by ring,
    show (k : ℤ) + 2 - 1 = (k : ℤ) + 1 by ring] at d2
  rw [show (k : ℤ) + 1 + 1 = (k : ℤ) + 2 by ring,
    show (k : ℤ) + 1 - 1 = (k : ℤ) by ring] at d1
  rw [show (k : ℤ) + 1 + 2 = (k : ℤ) + 3 by ring,
    show (k : ℤ) + 1 + 1 = (k : ℤ) + 2 by ring] at r3
  rw [show (k : ℤ) - 1 + 2 = (k : ℤ) + 1 by ring,
    show (k : ℤ) - 1 + 1 = (k : ℤ) by ring] at r1
  unfold nodePolynomial nodePolynomialDerivTPoly
  simp only [derivative_add, derivative_sub, derivative_C_mul]
  simp only [map_add, map_mul, map_pow, map_ofNat, map_one, map_natCast,
    Int.cast_add, Int.cast_natCast, Int.cast_ofNat] at d2 d1 d0 ⊢
  linear_combination (norm := (push_cast; ring_nf))
    d2 - 2 * C t * d1 + C t ^ 2 * d0 -
      ((k : ℝ[X]) + 2) * r3 + C t ^ 2 * ((k : ℝ[X]) + 2) * r1

/-- Pointwise identity valid for all `k : ℕ`, `t y : ℝ`:
`2 (1 - y^2) ∂_y p(t, y) + L_{k+1}(t, y) ∂_t p(t, y) = (2 (k + 1) t - 2 (k + 2) y) p(t, y)`. -/
theorem nodePolynomial_speed_identity_eval (k : ℕ) (t y : ℝ) :
    2 * (1 - y ^ 2) * (derivative (nodePolynomial k t)).eval y +
        speedDenominator (k + 1) t y * nodePolynomialDerivT k t y =
      (2 * ((k + 1 : ℕ) : ℝ) * t - 2 * ((k + 1 : ℕ) + 1 : ℝ) * y) *
        (nodePolynomial k t).eval y := by
  have h := congr_arg (fun P : ℝ[X] => P.eval y) (nodePolynomial_speed_poly_identity k t)
  simp only [eval_add, eval_sub, eval_mul, eval_one, eval_pow, eval_ofNat, eval_X, eval_C,
    nodePolynomialDerivTPoly_eval] at h
  unfold speedDenominator
  linear_combination h

/-- Key algebraic identity at any root `(nodePolynomial k t).eval y = 0`:
`2 * (1 - y^2) * ∂_y p(t, y) + L(k + 1, t, y) * ∂_t p(t, y) = 0`. -/
theorem nodePolynomial_speed_identity (k : ℕ) (t y : ℝ)
    (hroot : (nodePolynomial k t).eval y = 0) :
    2 * (1 - y ^ 2) * (derivative (nodePolynomial k t)).eval y +
      speedDenominator (k + 1) t y * nodePolynomialDerivT k t y = 0 := by
  rw [nodePolynomial_speed_identity_eval, hroot, mul_zero]

/-! ### Positivity of the denominator `L` (Priority 2) -/

/-- Sum-of-squares decomposition from Section 3 of `paper.tex`:
`L_t(y) = (n + 1)(1 - y^2) + (n + 1)(y - t)^2 + (1 - t^2)`. -/
theorem speedDenominator_eq_sos (n : ℕ) (t y : ℝ) :
    speedDenominator n t y =
      ((n : ℝ) + 1) * (1 - y ^ 2) + ((n : ℝ) + 1) * (y - t) ^ 2 + (1 - t ^ 2) := by
  unfold speedDenominator
  ring

/-- Sharp positivity of `L`: holds whenever `|t| < 1` and `|y| ≤ 1`. -/
theorem speedDenominator_pos_of_abs_lt_one_left (n : ℕ) {t y : ℝ}
    (ht : |t| < 1) (hy : |y| ≤ 1) :
    0 < speedDenominator n t y := by
  rw [speedDenominator_eq_sos]
  have ht2 : t ^ 2 < 1 := by nlinarith [abs_lt.mp ht]
  have hy2 : y ^ 2 ≤ 1 := by nlinarith [abs_le.mp hy]
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  nlinarith [sq_nonneg (y - t)]

/-- Positivity of `L` whenever `|t| ≤ 1` and `|y| < 1`. -/
theorem speedDenominator_pos_of_abs_lt_one_right (n : ℕ) {t y : ℝ}
    (ht : |t| ≤ 1) (hy : |y| < 1) :
    0 < speedDenominator n t y := by
  rw [speedDenominator_eq_sos]
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [abs_le.mp ht]
  have hy2 : y ^ 2 < 1 := by nlinarith [abs_lt.mp hy]
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : 0 < ((n : ℝ) + 1) * (1 - y ^ 2) := mul_pos hn (sub_pos.mpr hy2)
  nlinarith [sq_nonneg (y - t)]

/-- Positivity of `L(n, t, y)` for `|t| < 1` and `|y| < 1`. -/
theorem speedDenominator_pos (n : ℕ) {t y : ℝ} (ht : |t| < 1) (hy : |y| < 1) :
    0 < speedDenominator n t y :=
  speedDenominator_pos_of_abs_lt_one_left n ht hy.le

/-! ### Non-vanishing of partials / automatic root simplicity -/

/-- Two consecutive second-kind Chebyshev polynomials cannot vanish at the same point. -/
theorem chebyshev_U_adjacent_ne_zero (k : ℕ) (y : ℝ) :
    (U ℝ k).eval y ≠ 0 ∨ (U ℝ ((k : ℤ) + 1)).eval y ≠ 0 := by
  induction k with
  | zero =>
    left
    simp [Polynomial.Chebyshev.U_zero]
  | succ k ih =>
    by_contra h
    push Not at h
    rcases h with ⟨hk1, hk2⟩
    have hrec := congr_arg (fun P : ℝ[X] => P.eval y)
      (Polynomial.Chebyshev.U_add_two ℝ (k : ℤ))
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X] at hrec
    have hk1' : (U ℝ ((k : ℤ) + 1)).eval y = 0 := by
      simpa [Nat.cast_succ] using hk1
    have hk2' : (U ℝ ((k : ℤ) + 2)).eval y = 0 := by
      simpa [Nat.cast_succ, add_assoc] using hk2
    rw [hk1', hk2'] at hrec
    have hk0 : (U ℝ k).eval y = 0 := by linarith
    rcases ih with hne | hne
    · exact hne hk0
    · exact hne hk1'

/-- At any root of `nodePolynomial k t` with `|t| < 1` and `|y| ≤ 1`, the `t`-partial
`∂_t p(t, y)` is nonzero. -/
theorem nodePolynomialDerivT_ne_zero_of_root (k : ℕ) {t y : ℝ}
    (ht : |t| < 1) (hy : |y| ≤ 1) (hroot : (nodePolynomial k t).eval y = 0) :
    nodePolynomialDerivT k t y ≠ 0 := by
  intro hdt
  have hrec := congr_arg (fun P : ℝ[X] => P.eval y)
    (Polynomial.Chebyshev.U_add_two ℝ (k : ℤ))
  simp only [eval_sub, eval_mul, eval_ofNat, eval_X] at hrec
  have hp : (U ℝ ((k : ℤ) + 2)).eval y - 2 * t * (U ℝ ((k : ℤ) + 1)).eval y +
      t ^ 2 * (U ℝ k).eval y = 0 := by
    simpa [nodePolynomial] using hroot
  have hdt' : (U ℝ ((k : ℤ) + 1)).eval y = t * (U ℝ k).eval y := by
    unfold nodePolynomialDerivT at hdt
    linarith
  have hquad : (t ^ 2 - 2 * t * y + 1) * (U ℝ k).eval y = 0 := by
    rw [hdt'] at hp hrec
    linear_combination -hp + hrec
  have hty : |t * y| < 1 := by
    calc |t * y| = |t| * |y| := abs_mul t y
      _ ≤ |t| := mul_le_of_le_one_right (abs_nonneg t) hy
      _ < 1 := ht
  have h1ty : 0 < 1 - t * y := by linarith [(abs_lt.mp hty).2]
  have hy2 : 0 ≤ 1 - y ^ 2 := by nlinarith [abs_le.mp hy]
  have hpos : 0 < t ^ 2 - 2 * t * y + 1 := by
    have heq : t ^ 2 - 2 * t * y + 1 = (1 - t * y) ^ 2 + t ^ 2 * (1 - y ^ 2) := by ring
    rw [heq]
    nlinarith [sq_pos_of_pos h1ty, sq_nonneg t]
  have hk0 : (U ℝ k).eval y = 0 := (mul_eq_zero.mp hquad).resolve_left hpos.ne'
  have hk1 : (U ℝ ((k : ℤ) + 1)).eval y = 0 := by rw [hdt', hk0, mul_zero]
  rcases chebyshev_U_adjacent_ne_zero k y with hne | hne
  · exact hne hk0
  · exact hne hk1

/-- Every root `y` of `nodePolynomial k t` with `|t| < 1` and `|y| ≤ 1` is simple:
`(derivative (nodePolynomial k t)).eval y ≠ 0`. -/
theorem derivative_nodePolynomial_ne_zero_of_root (k : ℕ) {t y : ℝ}
    (ht : |t| < 1) (hy : |y| ≤ 1) (hroot : (nodePolynomial k t).eval y = 0) :
    (derivative (nodePolynomial k t)).eval y ≠ 0 := by
  intro hdy
  have hid := nodePolynomial_speed_identity k t y hroot
  rw [hdy, mul_zero, zero_add] at hid
  have hL := speedDenominator_pos_of_abs_lt_one_left (k + 1) ht hy
  have hdt := nodePolynomialDerivT_ne_zero_of_root k ht hy hroot
  exact (mul_ne_zero hL.ne' hdt) hid

/-! ### Implicit differentiation and formal node speed (Priority 3) -/

/-- Derivative of `s ↦ (nodePolynomial k s).eval (u s)` along a differentiable branch `u`. -/
theorem hasDerivAt_nodePolynomial_eval (k : ℕ) (u : ℝ → ℝ) (t u' : ℝ)
    (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => (nodePolynomial k s).eval (u s))
      ((derivative (nodePolynomial k t)).eval (u t) * u' +
        nodePolynomialDerivT k t (u t)) t := by
  have h2 : HasDerivAt (fun s => (U ℝ ((k : ℤ) + 2)).eval (u s))
      ((derivative (U ℝ ((k : ℤ) + 2))).eval (u t) * u') t :=
    HasDerivAt.comp t (Polynomial.hasDerivAt _ (u t)) hu
  have h1 : HasDerivAt (fun s => (U ℝ ((k : ℤ) + 1)).eval (u s))
      ((derivative (U ℝ ((k : ℤ) + 1))).eval (u t) * u') t :=
    HasDerivAt.comp t (Polynomial.hasDerivAt _ (u t)) hu
  have h0 : HasDerivAt (fun s => (U ℝ k).eval (u s))
      ((derivative (U ℝ k)).eval (u t) * u') t :=
    HasDerivAt.comp t (Polynomial.hasDerivAt _ (u t)) hu
  have h2t : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
    simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
  have ht2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have hcomb := (h2.sub (h2t.mul h1)).add (ht2.mul h0)
  have hfun : (fun s => (nodePolynomial k s).eval (u s)) =
      ((fun s => (U ℝ ((k : ℤ) + 2)).eval (u s)) -
        (fun s => 2 * s) * (fun s => (U ℝ ((k : ℤ) + 1)).eval (u s)) +
        (fun s => s ^ 2) * (fun s => (U ℝ k).eval (u s))) := by
    funext s
    simp [nodePolynomial]
  have heq : (derivative (nodePolynomial k t)).eval (u t) * u' +
        nodePolynomialDerivT k t (u t) =
      (derivative (U ℝ ((k : ℤ) + 2))).eval (u t) * u' -
        (2 * (U ℝ ((k : ℤ) + 1)).eval (u t) +
          2 * t * ((derivative (U ℝ ((k : ℤ) + 1))).eval (u t) * u')) +
        (2 * t * (U ℝ k).eval (u t) +
          t ^ 2 * ((derivative (U ℝ k)).eval (u t) * u')) := by
    simp only [nodePolynomial, derivative_add, derivative_sub, derivative_C_mul,
      eval_add, eval_sub, eval_mul, eval_C, nodePolynomialDerivT]
    ring
  rw [hfun, heq]
  exact hcomb

/-- Implicit differentiation identity for any branch `u` satisfying `p(s, u(s)) = 0` near `t`. -/
theorem implicit_deriv_nodePolynomial_eq_zero (k : ℕ) (u : ℝ → ℝ) (t u' : ℝ)
    (hu : HasDerivAt u u' t)
    (hroot : ∀ᶠ s in nhds t, (nodePolynomial k s).eval (u s) = 0) :
    (derivative (nodePolynomial k t)).eval (u t) * u' +
      nodePolynomialDerivT k t (u t) = 0 := by
  have hderiv := hasDerivAt_nodePolynomial_eval k u t u' hu
  have hzero : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t := hasDerivAt_const t 0
  have hzero' : HasDerivAt (fun s => (nodePolynomial k s).eval (u s)) 0 t :=
    hzero.congr_of_eventuallyEq hroot
  exact hderiv.unique hzero'

/-- General node speed formula assuming a simple root (`∂_y p ≠ 0`) and nonzero denominator `L ≠ 0`. -/
theorem node_speed_eq_of_derivY_ne_zero (k : ℕ) (u : ℝ → ℝ) (t u' : ℝ)
    (hu : HasDerivAt u u' t)
    (hroot : ∀ᶠ s in nhds t, (nodePolynomial k s).eval (u s) = 0)
    (hdy : (derivative (nodePolynomial k t)).eval (u t) ≠ 0)
    (hL : speedDenominator (k + 1) t (u t) ≠ 0) :
    u' = 2 * (1 - u t ^ 2) / speedDenominator (k + 1) t (u t) := by
  have hrt : (nodePolynomial k t).eval (u t) = 0 := hroot.self_of_nhds
  have himp := implicit_deriv_nodePolynomial_eq_zero k u t u' hu hroot
  have hid := nodePolynomial_speed_identity k t (u t) hrt
  have hmul : (derivative (nodePolynomial k t)).eval (u t) *
      (speedDenominator (k + 1) t (u t) * u' - 2 * (1 - u t ^ 2)) = 0 := by
    linear_combination -hid + speedDenominator (k + 1) t (u t) * himp
  have heq : speedDenominator (k + 1) t (u t) * u' = 2 * (1 - u t ^ 2) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hdy)
  exact eq_div_of_mul_eq hL (by linarith)

/-- Formal node speed formula `u'(t) = 2 * (1 - u(t)^2) / L(k + 1, t, u(t))` on `|t| < 1`,
`|u t| < 1` (without requiring a separate simple-root assumption). -/
theorem node_speed_eq (k : ℕ) (u : ℝ → ℝ) (t u' : ℝ)
    (ht : |t| < 1) (hu_lt : |u t| < 1)
    (hu : HasDerivAt u u' t)
    (hroot : ∀ᶠ s in nhds t, (nodePolynomial k s).eval (u s) = 0) :
    u' = 2 * (1 - u t ^ 2) / speedDenominator (k + 1) t (u t) := by
  have hrt : (nodePolynomial k t).eval (u t) = 0 := hroot.self_of_nhds
  exact node_speed_eq_of_derivY_ne_zero k u t u' hu hroot
    (derivative_nodePolynomial_ne_zero_of_root k ht hu_lt.le hrt)
    (speedDenominator_pos (k + 1) ht hu_lt).ne'

/-- `HasDerivAt` form of the node speed formula assuming `DifferentiableAt ℝ u t`. -/
theorem hasDerivAt_node_speed (k : ℕ) (u : ℝ → ℝ) (t : ℝ)
    (ht : |t| < 1) (hu_lt : |u t| < 1)
    (hu : DifferentiableAt ℝ u t)
    (hroot : ∀ᶠ s in nhds t, (nodePolynomial k s).eval (u s) = 0) :
    HasDerivAt u (2 * (1 - u t ^ 2) / speedDenominator (k + 1) t (u t)) t := by
  rw [← node_speed_eq k u t (deriv u t) ht hu_lt hu.hasDerivAt hroot]
  exact hu.hasDerivAt

/-- Positivity and upper bound `0 < u'(t) ≤ 2 / (n + 1)` (with `n = k + 1`) from Section 3
of `paper.tex`. -/
theorem node_speed_bounds (k : ℕ) (u : ℝ → ℝ) (t u' : ℝ)
    (ht : |t| < 1) (hu_lt : |u t| < 1)
    (hu : HasDerivAt u u' t)
    (hroot : ∀ᶠ s in nhds t, (nodePolynomial k s).eval (u s) = 0) :
    0 < u' ∧ u' ≤ 2 / (((k + 1 : ℕ) : ℝ) + 1) := by
  rw [node_speed_eq k u t u' ht hu_lt hu hroot]
  have hy2 : u t ^ 2 < 1 := by nlinarith [abs_lt.mp hu_lt]
  have hnum : 0 < 2 * (1 - u t ^ 2) := by linarith
  have hL : 0 < speedDenominator (k + 1) t (u t) := speedDenominator_pos (k + 1) ht hu_lt
  refine ⟨div_pos hnum hL, ?_⟩
  have hL_ge : (((k + 1 : ℕ) : ℝ) + 1) * (1 - u t ^ 2) ≤ speedDenominator (k + 1) t (u t) := by
    rw [speedDenominator_eq_sos]
    have ht2 : t ^ 2 < 1 := by nlinarith [abs_lt.mp ht]
    have hk : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 1 := by positivity
    nlinarith [sq_nonneg (u t - t)]
  rw [div_le_div_iff₀ hL (by positivity)]
  nlinarith

end SharpL1
