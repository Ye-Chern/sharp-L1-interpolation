import SharpL1.Analysis.NodeSpeed

/-!
# Chebyshev Cassini identity and the divided-difference denominator of the nodes

For order `n = k + 1`, this file proves the local algebraic identity behind the `ode`
equation of `paper.tex` (the relation between node speed and the divided-difference
denominator `|p_t'(u)|`).

1. `cassini_U` : the Cassini identity `U (m+2) * U m = U (m+1) ^ 2 - 1` for Chebyshev
   polynomials of the second kind (Mathlib has no Cassini form, so we induct with
   `U_add_two`).
2. `sq_eval_sub_mul_nodePolynomial_eq_one_of_root` : at any root `(nodePolynomial k t).eval y = 0`
   one has `(U (k+1)(y) - t * U k(y))^2 = 1`.  This is obtained by eliminating `U (k+2)`
   between the root equation `U (k+2)(y) = 2 t U (k+1)(y) - t^2 U k(y)` and Cassini at
   index `k+1`.  No root ordering, interval assumption, or division is used.
3. `abs_nodePolynomialDerivT_eq_two_of_root` : consequently `|∂_t p(t, y)| = 2` at any root
   (since `∂_t p(t, y) = -2 (U (k+1)(y) - t U k(y))`).
4. `abs_deriv_nodePolynomial_mul_u'_eq_two` : along a differentiable interior branch of
   roots `u(t)`, implicit differentiation (`implicit_deriv_nodePolynomial_eq_zero`) plus
   `u' > 0` (`node_speed_bounds`) give `|∂_y p(t, u(t))| * u' = 2`.
5. `abs_deriv_monicNodePolynomial_mul_u'_eq` : dividing by the leading coefficient
   `2 ^ (k + 2)` of `nodePolynomial k t` (`leadingCoeff_nodePolynomial`), for the monic
   pencil polynomial `p_t = monicNodePolynomial k t` one gets
   `|p_t'(u(t))| * u' = 2 ^ (-(k+1))`, i.e. `2 / 2 ^ n` with `n = k + 1`.
   Since for a monic polynomial `|p_t'(x_i)|` is (up to sign) the product of the distances
   from a node `x_i` to the other nodes, this is exactly the divided-difference denominator
   of the node weights.
-/

namespace SharpL1

open Polynomial
open Polynomial.Chebyshev (U)

/-! ### Cassini identity for the second-kind Chebyshev polynomials -/

/-- Cassini's identity for Chebyshev polynomials of the second kind, in the form used by
the node pencil: for every `m : ℕ`,
`U (m+2) * U m = U (m+1) ^ 2 - 1` (equivalently `U_{m+1} U_{m-1} = U_m^2 - 1` at index
`m+1`).  Proved by induction from the recurrence `U_add_two`; Mathlib does not ship a
Cassini form for `U`. -/
theorem cassini_U (R : Type*) [CommRing R] :
    ∀ m : ℕ,
      U R ((m : ℤ) + 2) * U R (m : ℤ) =
        U R ((m : ℤ) + 1) * U R ((m : ℤ) + 1) - 1 := by
  intro m
  induction m with
  | zero =>
    simp only [Nat.cast_zero, zero_add, Polynomial.Chebyshev.U_zero,
      Polynomial.Chebyshev.U_one, Polynomial.Chebyshev.U_two]
    ring
  | succ m ih =>
    rw [show (((m + 1 : ℕ) : ℤ)) = (m : ℤ) + 1 by push_cast; ring,
      show ((m : ℤ) + 1) + 2 = (m : ℤ) + 3 by ring,
      show ((m : ℤ) + 1) + 1 = (m : ℤ) + 2 by ring]
    have ha := Polynomial.Chebyshev.U_add_two R ((m : ℤ) + 1)
    rw [show ((m : ℤ) + 1) + 2 = (m : ℤ) + 3 by ring,
      show ((m : ℤ) + 1) + 1 = (m : ℤ) + 2 by ring] at ha
    have hb := Polynomial.Chebyshev.U_add_two R (m : ℤ)
    linear_combination (norm := ring)
      ha * U R ((m : ℤ) + 1) - hb * U R ((m : ℤ) + 2) + ih

/-- The key local algebraic identity at a root of the node polynomial: if
`(nodePolynomial k t).eval y = 0`, then `(U (k+1)(y) - t * U k(y))^2 = 1`.  Obtained by
eliminating `U (k+2)(y)` between the root equation and Cassini at index `k`; no ordering
of the roots, no interval assumption, and no division are involved. -/
theorem sq_eval_sub_mul_nodePolynomial_eq_one_of_root (k : ℕ) {t y : ℝ}
    (hroot : (nodePolynomial k t).eval y = 0) :
    ((U ℝ ((k : ℤ) + 1)).eval y - t * (U ℝ k).eval y) ^ 2 = 1 := by
  -- Root equation: `U (k+2)(y) = 2 t U (k+1)(y) - t^2 U k(y)`.
  have hp : (U ℝ ((k : ℤ) + 2)).eval y - 2 * t * (U ℝ ((k : ℤ) + 1)).eval y +
      t ^ 2 * (U ℝ k).eval y = 0 := by
    simpa [nodePolynomial] using hroot
  -- Cassini at index `k`, evaluated at `y`.
  have hc := congr_arg (fun P : ℝ[X] => P.eval y) (cassini_U ℝ k)
  simp only [eval_mul, eval_sub, eval_one] at hc
  -- `(U k)(y) * [root eq]` minus Cassini gives exactly `(U (k+1)(y) - t U k(y))^2 - 1`.
  linear_combination (norm := ring) (U ℝ k).eval y * hp - hc

/-! ### Absolute value of the `t`-partial at a root -/

/-- At any root of `nodePolynomial k t` the `t`-partial derivative has absolute value
exactly `2`: `|∂_t p(t, y)| = 2`.  This is the Chebyshev form of the statement that the
adjugate/numerator of the implicit-derivative formula is constant along the pencil. -/
theorem abs_nodePolynomialDerivT_eq_two_of_root (k : ℕ) {t y : ℝ}
    (hroot : (nodePolynomial k t).eval y = 0) :
    |nodePolynomialDerivT k t y| = 2 := by
  set x := (U ℝ ((k : ℤ) + 1)).eval y - t * (U ℝ k).eval y with hxdef
  have hsq : x ^ 2 = 1 := sq_eval_sub_mul_nodePolynomial_eq_one_of_root k hroot
  have hx : |x| = 1 := by
    have h2 : x = 1 ∨ x = -1 :=
      eq_or_eq_neg_of_sq_eq_sq x 1
        (hsq.trans (show ((1 : ℝ) ^ 2 = 1) by norm_num).symm)
    rcases h2 with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
  unfold nodePolynomialDerivT
  have hrew : -2 * (U ℝ ((k : ℤ) + 1)).eval y + 2 * t * (U ℝ k).eval y = -2 * x := by
    rw [hxdef]
    ring
  rw [hrew, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2), hx, mul_one]

/-! ### The divided-difference denominator along a differentiable root branch -/

/-- For a differentiable branch of interior roots `u(t)` of `nodePolynomial k t`
(`|t| < 1`, `|u t| < 1`), the *unnormalized* divided-difference denominator times the
speed satisfies `|∂_y p(t, u(t))| * u' = 2`.  Indeed implicit differentiation gives
`∂_y p · u' = -∂_t p`, whose absolute value is `2` by
`abs_nodePolynomialDerivT_eq_two_of_root`, and `u' > 0` by `node_speed_bounds`. -/
theorem abs_deriv_nodePolynomial_mul_u'_eq_two (k : ℕ) (u : ℝ → ℝ) (t u' : ℝ)
    (ht : |t| < 1) (hu_lt : |u t| < 1)
    (hu : HasDerivAt u u' t)
    (hroot : ∀ᶠ s in nhds t, (nodePolynomial k s).eval (u s) = 0) :
    |(derivative (nodePolynomial k t)).eval (u t)| * u' = 2 := by
  have hrt : (nodePolynomial k t).eval (u t) = 0 := hroot.self_of_nhds
  have hpos : 0 < u' := (node_speed_bounds k u t u' ht hu_lt hu hroot).1
  have himp := implicit_deriv_nodePolynomial_eq_zero k u t u' hu hroot
  have hdyu : (derivative (nodePolynomial k t)).eval (u t) * u' =
      -nodePolynomialDerivT k t (u t) := by linarith [himp]
  rw [← abs_of_nonneg hpos.le, ← abs_mul, hdyu, abs_neg,
    abs_nodePolynomialDerivT_eq_two_of_root k hrt]

/-- The leading coefficient of the unnormalized node polynomial is `2 ^ (k + 2)`, so
`2 ^ (-(k+2)) • nodePolynomial k t` is monic. -/
theorem leadingCoeff_nodePolynomial (k : ℕ) (t : ℝ) :
    (nodePolynomial k t).leadingCoeff = (2 : ℝ) ^ (k + 2) := by
  have hu₂ : (U ℝ ((k : ℤ) + 2)).natDegree = k + 2 := by
    simpa using Polynomial.Chebyshev.natDegree_U_natCast ℝ (k + 2)
  have hu₁ : (U ℝ ((k : ℤ) + 1)).natDegree = k + 1 := by
    simpa using Polynomial.Chebyshev.natDegree_U_natCast ℝ (k + 1)
  have hu₀ : (U ℝ k).natDegree = k :=
    Polynomial.Chebyshev.natDegree_U_natCast ℝ k
  have hBlt : (C (2 * t) * U ℝ ((k : ℤ) + 1)).natDegree < k + 2 := by
    calc (C (2 * t) * U ℝ ((k : ℤ) + 1)).natDegree ≤ (U ℝ ((k : ℤ) + 1)).natDegree :=
        natDegree_C_mul_le _ _
      _ = k + 1 := hu₁
      _ < k + 2 := by omega
  have hClt : (C (t ^ 2) * U ℝ k).natDegree < k + 2 := by
    calc (C (t ^ 2) * U ℝ k).natDegree ≤ (U ℝ k).natDegree := natDegree_C_mul_le _ _
      _ = k := hu₀
      _ < k + 2 := by omega
  have hlc : (U ℝ ((k : ℤ) + 2)).leadingCoeff = (2 : ℝ) ^ (k + 2) := by
    rw [show ((k : ℤ) + 2) = ((k + 2 : ℕ) : ℤ) by push_cast; ring]
    exact Polynomial.Chebyshev.leadingCoeff_U_natCast ℝ (k + 2)
  rw [← coeff_natDegree, hu₂] at hlc
  rw [leadingCoeff, natDegree_nodePolynomial, nodePolynomial,
    coeff_add, coeff_sub, coeff_eq_zero_of_natDegree_lt hBlt,
    coeff_eq_zero_of_natDegree_lt hClt, sub_zero, add_zero]
  exact hlc

/-- The monic node polynomial `p_t` of `paper.tex`:
`p_t = 2 ^ (-(k+2)) · nodePolynomial k t`, matching `jacobiMatrix_charpoly`
(`charpoly (jacobiMatrix k t) = C ((1/2)^(k+2)) * nodePolynomial k t`). -/
noncomputable def monicNodePolynomial (k : ℕ) (t : ℝ) : ℝ[X] :=
  C ((1 / 2 : ℝ) ^ (k + 2)) * nodePolynomial k t

@[simp]
theorem leadingCoeff_monicNodePolynomial (k : ℕ) (t : ℝ) :
    (monicNodePolynomial k t).leadingCoeff = 1 := by
  have hr : (1 / 2 : ℝ) ^ (k + 2) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hn : (monicNodePolynomial k t).natDegree = k + 2 := by
    rw [monicNodePolynomial, natDegree_C_mul hr, natDegree_nodePolynomial]
  rw [leadingCoeff, hn, monicNodePolynomial, coeff_C_mul]
  have hlc1 : (nodePolynomial k t).coeff (k + 2) = (nodePolynomial k t).leadingCoeff := by
    rw [← natDegree_nodePolynomial k t, coeff_natDegree]
  rw [hlc1, leadingCoeff_nodePolynomial, ← mul_pow,
    show ((1 / 2 : ℝ) * 2) = (1 : ℝ) by norm_num, one_pow]

theorem monicNodePolynomial_monic (k : ℕ) (t : ℝ) :
    (monicNodePolynomial k t).Monic :=
  leadingCoeff_monicNodePolynomial k t

/-- The divided-difference denominator of the *monic* node polynomial along a
differentiable interior root branch:
`|p_t'(u(t))| * u' = 2 ^ (-(k+1))`, i.e. `2 / 2 ^ n` with `n = k + 1`.
Since `p_t` is monic, `|p_t'(u(t))| = ∏_{j ≠ i} |u(t) - x_j|` over the other nodes `x_j`,
so this is exactly the identity needed for the node weights in the `ode` equation of
`paper.tex`.  It is `abs_deriv_nodePolynomial_mul_u'_eq_two` divided by the leading
coefficient `2 ^ (k + 2)`. -/
theorem abs_deriv_monicNodePolynomial_mul_u'_eq (k : ℕ) (u : ℝ → ℝ) (t u' : ℝ)
    (ht : |t| < 1) (hu_lt : |u t| < 1)
    (hu : HasDerivAt u u' t)
    (hroot : ∀ᶠ s in nhds t, (nodePolynomial k s).eval (u s) = 0) :
    |((derivative (monicNodePolynomial k t))).eval (u t)| * u' =
      (1 / 2 : ℝ) ^ (k + 1) := by
  have hc : (0 : ℝ) < (1 / 2 : ℝ) ^ (k + 2) := pow_pos (by norm_num) _
  have hder : (derivative (monicNodePolynomial k t)).eval (u t) =
      (1 / 2 : ℝ) ^ (k + 2) * (derivative (nodePolynomial k t)).eval (u t) := by
    rw [monicNodePolynomial, derivative_C_mul, eval_mul, eval_C]
  rw [hder, abs_mul, abs_of_nonneg hc.le, mul_assoc,
    abs_deriv_nodePolynomial_mul_u'_eq_two k u t u' ht hu_lt hu hroot]
  rw [show (k + 2 : ℕ) = (k + 1) + 1 by omega, pow_add, pow_one, mul_assoc]
  rw [show ((1 / 2 : ℝ) * 2) = 1 by norm_num, mul_one]

end SharpL1
