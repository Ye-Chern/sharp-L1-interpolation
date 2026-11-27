module

public import SharpL1.Analysis.ChebyshevFirstConstant
public import SharpL1.Analysis.GlobalNodes
public import SharpL1.Analysis.DividedCDF
public import SharpL1.Analysis.ErrorValue
public import SharpL1.Analysis.NodeWeights
public import SharpL1.Analysis.TruncatedPowerDeriv
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Moving-node operator `T_n`, Taylor kernel representation, and explicit error `E_n`

This module formalizes Sections 3 and 4 of `chebyshev_L1_complete.tex` for order `n = k + 1 ≥ 1`:

1. `movingOperator k F x = 2^(k+1) * (k+1)! * ∑ j, ε_j * u_j'(x) * F (u_j(x))`
   with `u_j(x) = orderedNode k x j`, `ε_j = (-1)^(k + 1 - j)`.
2. `movingOperator_eq_factorial_mul_barycentric`: on `(-1, 1)`,
   `T_n F x = n! * barycentricDividedDifference (u x) (F ∘ u x)`.
3. `movingOperator_L1_le`: `L¹` contraction bound
   `∫ x in (-1)..1, |T_n F x| ≤ 2^n * n! * ∫ y in (-1)..1, |F y|`
   for every `L¹` function `F` on `[-1, 1]`.
4. `movingOperator_poly`: polynomial exactness `T_n P x = P^(n)(x)` for `deg P ≤ n`.
5. `movingOperator_normTruncatedPower_mem_Icc`: `0 ≤ T_n h_t(x) ≤ 1` for `h_t(y) = (1/n!)(y - t)_+^n`,
   and `barycentric_truncatedPower_higher_nonneg`: nonnegativity of the `(n+1)`-th divided
   difference of `h_t` (used in `SharpSobolev.lean`).
6. `SobolevW1`: 1D Sobolev class `W^{m, 1}([a, b])` of iterated absolutely continuous functions,
   its integral Taylor remainder, and the exact kernel representation
   `F^(n)(x) - T_n F(x) = ∫ t in (-1)..1, (1_{x > t} - T_n h_t(x)) * F^(n+1)(t) dt`.
7. `integral_abs_indicator_sub_movingOperator_eq_explicitError`:
   `∫ x in (-1)..1, |1_{x > t} - T_n h_t(x)| dx = explicitError (k + 1) (orderedNode k t) t`,
   and `explicitError_center_eq`: exact center formula eq. (6) of `chebyshev_L1_complete.tex`.
-/

namespace SharpL1.Analysis

open Polynomial MeasureTheory Set Filter Topology

/-! ### Core definitions -/

/-- Node speed `u_j'(x) = 2 (1 - u_j(x)^2) / L_{k+1}(x, u_j(x))` for order `n = k + 1`. -/
noncomputable def orderedNodeSpeed (k : ℕ) (x : ℝ) (j : Fin (k + 2)) : ℝ :=
  2 * (1 - orderedNode k x j ^ 2) / speedDenominator (k + 1) x (orderedNode k x j)

/-- Alternating sign `ε_j = (-1)^(n - j)` for `j : Fin (n + 1)`. -/
def altSign (n : ℕ) (j : Fin (n + 1)) : ℝ :=
  (-1 : ℝ) ^ (n - j.val)

/-- The moving-node operator `T_{k+1} F x = 2^(k+1) * (k+1)! * ∑ j, ε_j * u_j'(x) * F (u_j(x))`. -/
noncomputable def movingOperator (k : ℕ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  firstBestConstant (k + 1) *
    ∑ j : Fin (k + 2), altSign (k + 1) j * orderedNodeSpeed k x j * F (orderedNode k x j)

/-- Normalized truncated power `h_t(y) = (1 / n!) * (y - t)_+^n`. -/
noncomputable def normTruncatedPower (n : ℕ) (t y : ℝ) : ℝ :=
  truncatedPower n t y / (n.factorial : ℝ)

/-- Closed-form center constant `b_n = E_n(0)` from eq. (6) of `chebyshev_L1_complete.tex`. -/
noncomputable def centerBestConstant (n : ℕ) : ℝ :=
  1 - (2 : ℝ) ^ n / ((n : ℝ) + 1) +
    (2 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) *
      ∑ m ∈ Finset.Icc 1 ((n + 1) / 2),
        (-1 : ℝ) ^ (m - 1) * (Real.cos ((m : ℝ) * Real.pi / ((n : ℝ) + 2))) ^ (n + 1)

/-! ### Elementary properties of `orderedNodeSpeed` and `altSign` -/

theorem abs_altSign (n : ℕ) (j : Fin (n + 1)) : |altSign n j| = 1 := by
  simp [altSign]

theorem altSign_sq (n : ℕ) (j : Fin (n + 1)) : altSign n j * altSign n j = 1 := by
  simp [altSign, ← mul_pow]

theorem orderedNodeSpeed_pos (k : ℕ) {x : ℝ} (hx : |x| < 1) (j : Fin (k + 2)) :
    0 < orderedNodeSpeed k x j := by
  have hd := hasDerivAt_orderedNode k hx j
  have h := (orderedNode_deriv_bounds k hx j).1
  rwa [hd.deriv] at h

theorem orderedNodeSpeed_le (k : ℕ) {x : ℝ} (hx : |x| < 1) (j : Fin (k + 2)) :
    orderedNodeSpeed k x j ≤ 2 / (((k + 1 : ℕ) : ℝ) + 1) := by
  have hd := hasDerivAt_orderedNode k hx j
  have h := (orderedNode_deriv_bounds k hx j).2
  rwa [hd.deriv] at h

theorem continuousOn_orderedNodeSpeed (k : ℕ) (j : Fin (k + 2)) :
    ContinuousOn (fun x => orderedNodeSpeed k x j) (Ioo (-1 : ℝ) 1) := by
  have hc : Continuous (fun x => orderedNode k x j) := continuous_orderedNode k j
  have hnum : ContinuousOn (fun x => 2 * (1 - orderedNode k x j ^ 2)) (Ioo (-1 : ℝ) 1) :=
    (by fun_prop : Continuous fun x => 2 * (1 - orderedNode k x j ^ 2)).continuousOn
  have hden : ContinuousOn (fun x => speedDenominator (k + 1) x (orderedNode k x j))
      (Ioo (-1 : ℝ) 1) := by
    unfold speedDenominator
    exact (by fun_prop : Continuous fun x =>
      ((k + 1 : ℕ) + 2 : ℝ) - 2 * ((k + 1 : ℕ) + 1 : ℝ) * x * orderedNode k x j +
        ((k + 1 : ℕ) : ℝ) * x ^ 2).continuousOn
  refine hnum.div hden fun x hx => ?_
  have hx' : |x| < 1 := abs_lt.mpr hx
  have hy' : |orderedNode k x j| < 1 :=
    abs_lt.mpr (nodePolynomial_root_mem_Ioo k hx' (orderedNode_eval_eq_zero k x j))
  exact (speedDenominator_pos (k + 1) hx' hy').ne'

theorem truncatedPower_eq_max_pow' {m : ℕ} (hm : 0 < m) (t y : ℝ) :
    truncatedPower m t y = (max (y - t) 0) ^ m := by
  by_cases h : t ≤ y
  · simp [truncatedPower, h]
  · have hsub : y - t ≤ 0 := sub_nonpos.mpr (le_of_not_ge h)
    simp [truncatedPower, h, max_eq_right hsub, zero_pow (Nat.ne_of_gt hm)]

theorem continuous_truncatedPower {m : ℕ} (hm : 0 < m) :
    Continuous (fun p : ℝ × ℝ => truncatedPower m p.1 p.2) := by
  have heq : (fun p : ℝ × ℝ => truncatedPower m p.1 p.2) =
      fun p => (max (p.2 - p.1) 0) ^ m := by
    ext ⟨t, y⟩
    exact truncatedPower_eq_max_pow' hm t y
  rw [heq]
  fun_prop

theorem continuous_normTruncatedPower {m : ℕ} (hm : 0 < m) :
    Continuous (fun p : ℝ × ℝ => normTruncatedPower m p.1 p.2) :=
  (continuous_truncatedPower hm).div_const _

/-! ### Barycentric divided-difference identity `T_n F = n! * F[u_0, ..., u_n]` -/

theorem monicNodePolynomial_eq_prod (k : ℕ) (x : ℝ) :
    monicNodePolynomial k x = ∏ i : Fin (k + 2), (X - C (orderedNode k x i)) := by
  have hroots : (nodePolynomial k x).roots = Finset.univ.val.map (orderedNode k x) := by
    have h1 : (List.ofFn (orderedNode k x) : Multiset ℝ) = (nodePolynomial k x).roots := by
      rw [orderedNode_ofFn]
      simp [Multiset.sort_eq]
    rw [← h1, ← Fin.univ_val_map]
  apply Polynomial.funext
  intro y
  rw [monicNodePolynomial, eval_mul, eval_C, (nodePolynomial_splits k x).eval_eq_prod_roots,
    hroots, Multiset.map_map, leadingCoeff_nodePolynomial]
  have hprod : (Multiset.map ((fun a => y - a) ∘ orderedNode k x) Finset.univ.val).prod =
      ∏ i : Fin (k + 2), (y - orderedNode k x i) := rfl
  rw [hprod, ← mul_assoc, ← mul_pow, show ((1 / 2 : ℝ) * 2) = 1 by norm_num, one_pow, one_mul]
  rw [eval_prod]
  refine Finset.prod_congr rfl fun i _ => by simp

theorem eval_derivative_monicNodePolynomial (k : ℕ) (x : ℝ) (j : Fin (k + 2)) :
    (derivative (monicNodePolynomial k x)).eval (orderedNode k x j) =
      ∏ i ∈ Finset.univ.erase j, (orderedNode k x j - orderedNode k x i) := by
  rw [monicNodePolynomial_eq_prod, Polynomial.derivative_prod_finset, eval_finsetSum]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  have hzero : ∑ i ∈ Finset.univ.erase j,
      ((∏ l ∈ Finset.univ.erase i, (X - C (orderedNode k x l))) *
        derivative (X - C (orderedNode k x i))).eval (orderedNode k x j) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hij : j ≠ i := (Finset.mem_erase.mp hi).1.symm
    have hj_mem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩
    rw [eval_mul, eval_prod, Finset.prod_eq_zero hj_mem (by simp), zero_mul]
  rw [hzero, add_zero, eval_mul, derivative_sub, derivative_X, derivative_C, sub_zero, eval_one,
    mul_one, eval_prod]
  refine Finset.prod_congr rfl fun i _ => by simp

private theorem prod_sub_eq_altSign_mul_abs {n : ℕ} {u : Fin (n + 1) → ℝ}
    (hu : StrictMono u) (j : Fin (n + 1)) :
    ∏ i ∈ Finset.univ.erase j, (u j - u i) =
      altSign n j * |∏ i ∈ Finset.univ.erase j, (u j - u i)| := by
  rw [Finset.abs_prod]
  let S_lt := (Finset.univ.erase j).filter (fun i => i < j)
  let S_gt := (Finset.univ.erase j).filter (fun i => j < i)
  have hdisj : Disjoint S_lt S_gt := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    have hlt := (Finset.mem_filter.mp h1).2
    have hgt := (Finset.mem_filter.mp h2).2
    exact lt_asymm hlt hgt
  have hunion : Finset.univ.erase j = S_lt ∪ S_gt := by
    ext i
    simp only [S_lt, S_gt, Finset.mem_union, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true]
    constructor
    · intro hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨hne, h⟩
      · exact Or.inr ⟨hne, h⟩
    · rintro (⟨hne, _⟩ | ⟨hne, _⟩) <;> exact hne
  have hlt_eq : ∏ i ∈ S_lt, (u j - u i) = ∏ i ∈ S_lt, |u j - u i| := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hlt := (Finset.mem_filter.mp hi).2
    exact (abs_of_pos (sub_pos.mpr (hu hlt))).symm
  have hgt_eq : ∏ i ∈ S_gt, (u j - u i) = (-1 : ℝ) ^ S_gt.card * ∏ i ∈ S_gt, |u j - u i| := by
    have hterm : ∀ i ∈ S_gt, u j - u i = (-1 : ℝ) * |u j - u i| := by
      intro i hi
      have hgt := (Finset.mem_filter.mp hi).2
      rw [abs_of_neg (sub_neg.mpr (hu hgt))]
      ring
    rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_const]
  have hcard : S_gt.card = n - j.val := by
    have hbij : S_gt.card = (Finset.Ico (j.val + 1) (n + 1)).card := by
      refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
      · intro i hi
        have hgt := (Finset.mem_filter.mp hi).2
        rw [Finset.mem_Ico]
        exact ⟨Nat.succ_le_of_lt hgt, i.isLt⟩
      · intro a _ b _ hab
        exact Fin.ext hab
      · intro m hm
        rw [Finset.mem_Ico] at hm
        refine ⟨⟨m, hm.2⟩, ?_, rfl⟩
        rw [Finset.mem_filter, Finset.mem_erase]
        refine ⟨⟨?_, Finset.mem_univ _⟩, Nat.lt_of_succ_le hm.1⟩
        intro h
        have hv : m = j.val := congrArg Fin.val h
        omega
    rw [hbij, Nat.card_Ico]
    omega
  rw [hunion, Finset.prod_union hdisj, Finset.prod_union hdisj, hlt_eq, hgt_eq, hcard]
  dsimp [altSign]
  ring

theorem two_pow_mul_altSign_mul_orderedNodeSpeed (k : ℕ) {x : ℝ} (hx : |x| < 1)
    (j : Fin (k + 2)) :
    (2 : ℝ) ^ (k + 1) * altSign (k + 1) j * orderedNodeSpeed k x j =
      (∏ i ∈ Finset.univ.erase j, (orderedNode k x j - orderedNode k x i))⁻¹ := by
  have hy : |orderedNode k x j| < 1 :=
    abs_lt.mpr (nodePolynomial_root_mem_Ioo k hx (orderedNode_eval_eq_zero k x j))
  have hweight := abs_deriv_monicNodePolynomial_mul_u'_eq k (fun s => orderedNode k s j) x
    (orderedNodeSpeed k x j) hx hy (hasDerivAt_orderedNode k hx j)
    (.of_forall fun s => orderedNode_eval_eq_zero k s j)
  rw [eval_derivative_monicNodePolynomial] at hweight
  have hsign := prod_sub_eq_altSign_mul_abs (orderedNode_strictMono k x) j
  apply eq_inv_of_mul_eq_one_left
  calc (2 : ℝ) ^ (k + 1) * altSign (k + 1) j * orderedNodeSpeed k x j *
        ∏ i ∈ Finset.univ.erase j, (orderedNode k x j - orderedNode k x i)
      = (2 : ℝ) ^ (k + 1) * (altSign (k + 1) j * altSign (k + 1) j) *
          (|∏ i ∈ Finset.univ.erase j, (orderedNode k x j - orderedNode k x i)| *
            orderedNodeSpeed k x j) := by
        conv_lhs => rw [hsign]
        ring
    _ = (2 : ℝ) ^ (k + 1) * 1 * (1 / 2 : ℝ) ^ (k + 1) := by
        rw [altSign_sq, hweight]
    _ = 1 := by
        rw [mul_one, ← mul_pow]
        norm_num

/-- **Barycentric divided-difference identity** (eq. (4) of `chebyshev_L1_complete.tex`):
for `|x| < 1`, `T_{k+1} F x = (k + 1)! * F[u_0(x), ..., u_{k+1}(x)]`. -/
theorem movingOperator_eq_factorial_mul_barycentric (k : ℕ) (F : ℝ → ℝ) {x : ℝ} (hx : |x| < 1) :
    movingOperator k F x =
      ((k + 1).factorial : ℝ) *
        barycentricDividedDifference (orderedNode k x) (fun j => F (orderedNode k x j)) := by
  unfold movingOperator firstBestConstant barycentricDividedDifference barycentricDividedDifferenceOn
  rw [mul_comm ((2 : ℝ) ^ (k + 1)), mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← two_pow_mul_altSign_mul_orderedNodeSpeed k hx j]
  ring

/-! ### Polynomial exactness of `T_n` -/

/-- **Polynomial exactness**: for `deg P ≤ k + 1` and `|x| < 1`, `T_{k+1} P x = P^(k+1)(x)`. -/
theorem movingOperator_poly (k : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ k + 1)
    {x : ℝ} (hx : |x| < 1) :
    movingOperator k (fun y => P.eval y) x =
      iteratedDeriv (k + 1) (fun y => P.eval y) x := by
  rw [movingOperator_eq_factorial_mul_barycentric k _ hx,
    iteratedDeriv_polynomial_eval_of_natDegree_le P (k + 1) hP x]
  congr 1
  have hdeg : P.degree < ((k + 1 + 1 : ℕ) : WithBot ℕ) :=
    lt_of_le_of_lt Polynomial.degree_le_natDegree (Nat.cast_lt.mpr (Nat.lt_succ_of_le hP))
  exact barycentricDividedDifference_eval_eq_coeff (orderedNode_strictMono k x).injective P hdeg

/-! ### Divided-difference bounds for truncated powers (no probability required) -/

/-- For any nonempty finite set of distinct real nodes, the `(s.card - 1)`-th divided difference
of `truncatedPower (s.card - 1) t` lies in `[0, 1]`. -/
theorem barycentric_truncatedPower_mem_Icc {ι : Type*} [DecidableEq ι]
    (s : Finset ι) {a : ι → ℝ} (ha : Set.InjOn a s) (hs : s.Nonempty) (t : ℝ) :
    0 ≤ barycentricDividedDifferenceOn s a (fun i => truncatedPower (s.card - 1) t (a i)) ∧
    barycentricDividedDifferenceOn s a (fun i => truncatedPower (s.card - 1) t (a i)) ≤ 1 := by
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | ind m ih =>
    rcases m with _ | _ | m
    · exact absurd hn (Finset.card_pos.mpr hs).ne'
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hn
      simp only [barycentricDividedDifferenceOn, Finset.sum_singleton, Finset.erase_singleton,
        Finset.prod_empty, inv_one, mul_one, Nat.sub_self, truncatedPower, pow_zero]
      split_ifs <;> norm_num
    · by_cases hall_ge : ∀ i ∈ s, t ≤ a i
      · rw [← hn, barycentric_truncatedPower_nonneg_side ha hs t hall_ge]
        norm_num
      by_cases hall_le : ∀ i ∈ s, a i ≤ t
      · rw [← hn, barycentric_truncatedPower_nonpos_side s a (by omega) t hall_le]
        norm_num
      push Not at hall_ge hall_le
      obtain ⟨l, hl, hlt⟩ := hall_ge
      obtain ⟨h, hh, hgt⟩ := hall_le
      have horder : a l < a h := lt_trans hlt hgt
      have hsub : m + 1 + 1 - 1 = m + 1 := by omega
      rw [hsub, barycentric_truncatedPower_erase_pair ha hl hh horder m t]
      have hcard_l : (s.erase l).card = m + 1 := by rw [Finset.card_erase_of_mem hl, hn]; omega
      have hcard_h : (s.erase h).card = m + 1 := by rw [Finset.card_erase_of_mem hh, hn]; omega
      have hne_l : (s.erase l).Nonempty := Finset.card_pos.mp (by omega)
      have hne_h : (s.erase h).Nonempty := Finset.card_pos.mp (by omega)
      have ihl := ih (m + 1) (by omega) (s.erase l) (ha.mono (Finset.erase_subset _ _)) hne_l hcard_l
      have ihh := ih (m + 1) (by omega) (s.erase h) (ha.mono (Finset.erase_subset _ _)) hne_h hcard_h
      have hcm : m + 1 - 1 = m := by omega
      rw [hcm] at ihl ihh
      have hden : 0 < a h - a l := sub_pos.mpr horder
      have hw1 : 0 < a h - t := sub_pos.mpr hgt
      have hw2 : 0 < t - a l := sub_pos.mpr hlt
      constructor
      · apply div_nonneg _ hden.le
        exact add_nonneg (mul_nonneg hw1.le ihl.1) (mul_nonneg hw2.le ihh.1)
      · rw [div_le_one hden]
        nlinarith [ihl.2, ihh.2]

/-- For any finite set of at least `2` distinct real nodes, the `(s.card - 1)`-th divided
difference of `truncatedPower (s.card - 2) t` is nonnegative.
(This is `h_t[u_0, ..., u_n, y] ≥ 0` used in the sharpness sign structure in `SharpSobolev.lean`.) -/
theorem barycentric_truncatedPower_higher_nonneg {ι : Type*} [DecidableEq ι]
    (s : Finset ι) {a : ι → ℝ} (ha : Set.InjOn a s) (hs : 2 ≤ s.card) (t : ℝ) :
    0 ≤ barycentricDividedDifferenceOn s a (fun i => truncatedPower (s.card - 2) t (a i)) := by
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | ind m ih =>
    rcases m with _ | _ | _ | m
    · omega
    · omega
    · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hn
      have hne : a x ≠ a y := fun h => hxy (ha (Finset.mem_insert_self _ _)
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) h)
      have hcalc : barycentricDividedDifferenceOn ({x, y} : Finset ι) a
            (fun i => truncatedPower 0 t (a i)) =
          (truncatedPower 0 t (a x) - truncatedPower 0 t (a y)) / (a x - a y) := by
        unfold barycentricDividedDifferenceOn
        rw [Finset.sum_pair hxy]
        have hx_erase : ({x, y} : Finset ι).erase x = {y} := by
          ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨hz, rfl | rfl⟩; exact absurd rfl hz; exact rfl
          · rintro rfl; exact ⟨hxy.symm, Or.inr rfl⟩
        have hy_erase : ({x, y} : Finset ι).erase y = {x} := by
          ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨hz, rfl | rfl⟩; exact rfl; exact absurd rfl hz
          · rintro rfl; exact ⟨hxy, Or.inl rfl⟩
        rw [hx_erase, hy_erase, Finset.prod_singleton, Finset.prod_singleton]
        have hsub : a y - a x = -(a x - a y) := by ring
        rw [hsub]
        field_simp [sub_ne_zero.mpr hne]
        ring
      have hzero : 0 + 1 + 1 - 2 = 0 := rfl
      rw [hzero, hcalc]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · apply div_nonneg_of_nonpos _ (sub_nonpos.mpr hlt.le)
        by_cases hx : t ≤ a x
        · simp [truncatedPower, hx, le_trans hx hlt.le]
        · by_cases hy : t ≤ a y <;> simp [truncatedPower, hx, hy]
      · apply div_nonneg _ (sub_nonneg.mpr hgt.le)
        by_cases hy : t ≤ a y
        · simp [truncatedPower, hy, le_trans hy hgt.le]
        · by_cases hx : t ≤ a x <;> simp [truncatedPower, hx, hy]
    · have hsub : m + 1 + 1 + 1 - 2 = m + 1 := by omega
      rw [hsub]
      by_cases hall_ge : ∀ i ∈ s, t ≤ a i
      · let p : ℝ[X] := (X - C t) ^ (m + 1)
        have heq : barycentricDividedDifferenceOn s a (fun i => truncatedPower (m + 1) t (a i)) =
            barycentricDividedDifferenceOn s a (fun i => p.eval (a i)) := by
          unfold barycentricDividedDifferenceOn
          refine Finset.sum_congr rfl fun i hi => ?_
          simp [truncatedPower, hall_ge i hi, p]
        rw [heq]
        have hp_deg : p.degree < s.card := by
          have hmon : p.Monic := (monic_X_sub_C t).pow _
          rw [degree_eq_natDegree hmon.ne_zero]
          have hnat : p.natDegree = m + 1 := by simp [p]
          rw [hnat, hn]
          exact_mod_cast (by omega : m + 1 < m + 3)
        rw [barycentricDividedDifferenceOn_eval_eq_coeff ha p hp_deg]
        have hcoeff0 : p.coeff (s.card - 1) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          have hnat : p.natDegree = m + 1 := by simp [p]
          rw [hnat, hn]; omega
        rw [hcoeff0]
      by_cases hall_le : ∀ i ∈ s, a i ≤ t
      · rw [barycentric_truncatedPower_nonpos_side s a (Nat.succ_pos m) t hall_le]
      push Not at hall_ge hall_le
      obtain ⟨l, hl, hlt⟩ := hall_ge
      obtain ⟨h, hh, hgt⟩ := hall_le
      have horder : a l < a h := lt_trans hlt hgt
      rw [barycentric_truncatedPower_erase_pair ha hl hh horder m t]
      have hcard_l : (s.erase l).card = m + 2 := by rw [Finset.card_erase_of_mem hl, hn]; omega
      have hcard_h : (s.erase h).card = m + 2 := by rw [Finset.card_erase_of_mem hh, hn]; omega
      have ihl := ih (m + 2) (by omega) (s.erase l) (ha.mono (Finset.erase_subset _ _)) (by omega) hcard_l
      have ihh := ih (m + 2) (by omega) (s.erase h) (ha.mono (Finset.erase_subset _ _)) (by omega) hcard_h
      have hcm : m + 2 - 2 = m := by omega
      rw [hcm] at ihl ihh
      apply div_nonneg _ (sub_nonneg.mpr horder.le)
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr hgt.le) ihl)
        (mul_nonneg (sub_nonneg.mpr hlt.le) ihh)

/-- For `|x| < 1` and any `t : ℝ`, `0 ≤ T_{k+1} h_t(x) ≤ 1`. -/
theorem movingOperator_normTruncatedPower_mem_Icc (k : ℕ) (t : ℝ) {x : ℝ} (hx : |x| < 1) :
    0 ≤ movingOperator k (normTruncatedPower (k + 1) t) x ∧
    movingOperator k (normTruncatedPower (k + 1) t) x ≤ 1 := by
  rw [movingOperator_eq_factorial_mul_barycentric k _ hx]
  have hfac : ((k + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hsimp : ((k + 1).factorial : ℝ) *
        barycentricDividedDifference (orderedNode k x)
          (fun j => normTruncatedPower (k + 1) t (orderedNode k x j)) =
      barycentricDividedDifferenceOn Finset.univ (orderedNode k x)
        (fun j => truncatedPower ((Finset.univ : Finset (Fin (k + 2))).card - 1) t
          (orderedNode k x j)) := by
    unfold barycentricDividedDifference barycentricDividedDifferenceOn normTruncatedPower
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hcard : (Finset.univ : Finset (Fin (k + 2))).card - 1 = k + 1 := by simp
    rw [hcard]
    field_simp [hfac]
  rw [hsimp]
  exact barycentric_truncatedPower_mem_Icc Finset.univ (orderedNode_strictMono k x).injective.injOn
    Finset.univ_nonempty t

/-! ### Exact 1D change of variables along `u_j : [a, b] → [u_j(a), u_j(b)]` -/

theorem orderedNode_image_Ioo (k : ℕ) (j : Fin (k + 2)) {a b : ℝ}
    (ha : a ∈ Icc (-1 : ℝ) 1) (hb : b ∈ Icc (-1 : ℝ) 1) (hab : a ≤ b) :
    (fun x => orderedNode k x j) '' Ioo a b =
      Ioo (orderedNode k a j) (orderedNode k b j) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx_Icc : x ∈ Icc (-1 : ℝ) 1 := ⟨le_trans ha.1 hx.1.le, le_trans hx.2.le hb.2⟩
    exact ⟨orderedNode_strictMonoOn_Icc k j ha hx_Icc hx.1,
      orderedNode_strictMonoOn_Icc k j hx_Icc hb hx.2⟩
  · intro hy
    have hsub : Icc a b ⊆ Icc (-1 : ℝ) 1 := Icc_subset_Icc ha.1 hb.2
    exact intermediate_value_Ioo hab ((continuousOn_orderedNode k j).mono hsub) hy

theorem integrableOn_comp_orderedNode_iff (k : ℕ) (j : Fin (k + 2)) {a b : ℝ}
    (ha : a ∈ Icc (-1 : ℝ) 1) (hb : b ∈ Icc (-1 : ℝ) 1) (hab : a ≤ b) (F : ℝ → ℝ) :
    IntegrableOn F (Ioo (orderedNode k a j) (orderedNode k b j)) volume ↔
      IntegrableOn (fun x => orderedNodeSpeed k x j * F (orderedNode k x j)) (Ioo a b) volume := by
  rw [← orderedNode_image_Ioo k j ha hb hab]
  have hderiv : ∀ x ∈ Ioo a b,
      HasDerivWithinAt (fun s => orderedNode k s j) (orderedNodeSpeed k x j) (Ioo a b) x := by
    intro x hx
    have hx' : |x| < 1 := abs_lt.mpr ⟨lt_of_le_of_lt ha.1 hx.1, lt_of_lt_of_le hx.2 hb.2⟩
    exact (hasDerivAt_orderedNode k hx' j).hasDerivWithinAt
  have hsub : Ioo a b ⊆ Icc (-1 : ℝ) 1 :=
    fun x hx => ⟨le_trans ha.1 hx.1.le, le_trans hx.2.le hb.2⟩
  have hinj : InjOn (fun s => orderedNode k s j) (Ioo a b) :=
    (orderedNode_strictMonoOn_Icc k j).injOn.mono hsub
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hderiv hinj F]
  refine integrableOn_congr_fun (fun x hx => ?_) measurableSet_Ioo
  have hx' : |x| < 1 := abs_lt.mpr ⟨lt_of_le_of_lt ha.1 hx.1, lt_of_lt_of_le hx.2 hb.2⟩
  simp only [smul_eq_mul, abs_of_pos (orderedNodeSpeed_pos k hx' j)]

theorem intervalIntegral_comp_orderedNode (k : ℕ) (j : Fin (k + 2)) {a b : ℝ}
    (ha : a ∈ Icc (-1 : ℝ) 1) (hb : b ∈ Icc (-1 : ℝ) 1) (hab : a ≤ b) (F : ℝ → ℝ) :
    ∫ y in orderedNode k a j..orderedNode k b j, F y =
      ∫ x in a..b, orderedNodeSpeed k x j * F (orderedNode k x j) := by
  have hub : orderedNode k a j ≤ orderedNode k b j :=
    (orderedNode_strictMonoOn_Icc k j).monotoneOn ha hb hab
  rw [intervalIntegral.integral_of_le hub, intervalIntegral.integral_of_le hab,
    MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← orderedNode_image_Ioo k j ha hb hab]
  have hderiv : ∀ x ∈ Ioo a b,
      HasDerivWithinAt (fun s => orderedNode k s j) (orderedNodeSpeed k x j) (Ioo a b) x := by
    intro x hx
    have hx' : |x| < 1 := abs_lt.mpr ⟨lt_of_le_of_lt ha.1 hx.1, lt_of_lt_of_le hx.2 hb.2⟩
    exact (hasDerivAt_orderedNode k hx' j).hasDerivWithinAt
  have hsub : Ioo a b ⊆ Icc (-1 : ℝ) 1 :=
    fun x hx => ⟨le_trans ha.1 hx.1.le, le_trans hx.2.le hb.2⟩
  have hinj : InjOn (fun s => orderedNode k s j) (Ioo a b) :=
    (orderedNode_strictMonoOn_Icc k j).injOn.mono hsub
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj F]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have hx' : |x| < 1 := abs_lt.mpr ⟨lt_of_le_of_lt ha.1 hx.1, lt_of_lt_of_le hx.2 hb.2⟩
  simp only [smul_eq_mul, abs_of_pos (orderedNodeSpeed_pos k hx' j)]

/-! ### `L¹` contraction bound of `T_n` -/

theorem intervalIntegrable_movingOperator (k : ℕ) {F : ℝ → ℝ}
    (hF : IntegrableOn F (Icc (-1 : ℝ) 1) volume) :
    IntervalIntegrable (movingOperator k F) volume (-1) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  unfold movingOperator
  apply Integrable.const_mul
  refine integrable_finsetSum Finset.univ fun j _ => ?_
  have h1 : IntegrableOn (fun x => orderedNodeSpeed k x j * F (orderedNode k x j))
      (Ioo (-1 : ℝ) 1) volume := by
    rw [← integrableOn_comp_orderedNode_iff k j ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩
      (by norm_num) F]
    refine hF.mono_set ?_
    rw [orderedNode_neg_one, orderedNode_one]
    exact Ioo_subset_Icc_self.trans
      (Icc_subset_Icc (chebyshevGrid_mem_Icc k j.val (by omega)).1
        (chebyshevGrid_mem_Icc k (j.val + 1) (by omega)).2)
  have h2 : (fun x => altSign (k + 1) j * orderedNodeSpeed k x j * F (orderedNode k x j)) =
      fun x => altSign (k + 1) j * (orderedNodeSpeed k x j * F (orderedNode k x j)) := by
    ext x; ring
  rw [h2]
  exact h1.const_mul _

/-- **`L¹` contraction bound** (eq. (3)–(4) of `chebyshev_L1_complete.tex`):
for any `F ∈ L¹([-1, 1])`, `‖T_{k+1} F‖_{L¹[-1,1]} ≤ 2^(k+1) * (k+1)! * ‖F‖_{L¹[-1,1]}`. -/
theorem movingOperator_L1_le (k : ℕ) {F : ℝ → ℝ}
    (hF : IntegrableOn F (Icc (-1 : ℝ) 1) volume) :
    ∫ x in (-1 : ℝ)..1, |movingOperator k F x| ≤
      firstBestConstant (k + 1) * ∫ y in (-1 : ℝ)..1, |F y| := by
  have hF_abs : IntegrableOn (fun y => |F y|) (Icc (-1 : ℝ) 1) volume := hF.abs
  have hterm_int : ∀ j : Fin (k + 2),
      IntervalIntegrable (fun x => orderedNodeSpeed k x j * |F (orderedNode k x j)|)
        volume (-1) 1 := by
    intro j
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    rw [← integrableOn_comp_orderedNode_iff k j ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩
      (by norm_num) (fun y => |F y|)]
    refine hF_abs.mono_set ?_
    rw [orderedNode_neg_one, orderedNode_one]
    exact Ioo_subset_Icc_self.trans
      (Icc_subset_Icc (chebyshevGrid_mem_Icc k j.val (by omega)).1
        (chebyshevGrid_mem_Icc k (j.val + 1) (by omega)).2)
  have hT_abs_int : IntervalIntegrable (fun x => |movingOperator k F x|) volume (-1) 1 :=
    (intervalIntegrable_movingOperator k hF).abs
  have hrhs_int : IntervalIntegrable
      (fun x => firstBestConstant (k + 1) *
        ∑ j : Fin (k + 2), orderedNodeSpeed k x j * |F (orderedNode k x j)|) volume (-1) 1 := by
    have hsum : IntervalIntegrable
        (fun x => ∑ j : Fin (k + 2), orderedNodeSpeed k x j * |F (orderedNode k x j)|)
        volume (-1) 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
      exact integrable_finsetSum Finset.univ fun j _ =>
        (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp (hterm_int j)
    exact hsum.const_mul _
  have hmono : ∫ x in (-1 : ℝ)..1, |movingOperator k F x| ≤
      ∫ x in (-1 : ℝ)..1, firstBestConstant (k + 1) *
        ∑ j : Fin (k + 2), orderedNodeSpeed k x j * |F (orderedNode k x j)| := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    apply MeasureTheory.setIntegral_mono_on
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp hT_abs_int)
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp hrhs_int)
      measurableSet_Ioo
    intro x hx
    have hx' : |x| < 1 := abs_lt.mpr hx
    unfold movingOperator
    rw [abs_mul, abs_of_nonneg (by unfold firstBestConstant; positivity)]
    apply mul_le_mul_of_nonneg_left _ (by unfold firstBestConstant; positivity)
    calc |∑ j : Fin (k + 2), altSign (k + 1) j * orderedNodeSpeed k x j * F (orderedNode k x j)|
        ≤ ∑ j : Fin (k + 2), |altSign (k + 1) j * orderedNodeSpeed k x j * F (orderedNode k x j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin (k + 2), orderedNodeSpeed k x j * |F (orderedNode k x j)| := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [abs_mul, abs_mul, abs_altSign, one_mul,
            abs_of_pos (orderedNodeSpeed_pos k hx' j)]
  refine hmono.trans_eq ?_
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun j _ => hterm_int j)]
  congr 1
  have hsubst : ∀ j : Fin (k + 2),
      ∫ x in (-1 : ℝ)..1, orderedNodeSpeed k x j * |F (orderedNode k x j)| =
        ∫ y in chebyshevGrid k j.val..chebyshevGrid k (j.val + 1), |F y| := by
    intro j
    rw [← orderedNode_neg_one k j, ← orderedNode_one k j]
    exact (intervalIntegral_comp_orderedNode k j ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩
      (by norm_num) (fun y => |F y|)).symm
  simp_rw [hsubst]
  rw [Fin.sum_univ_eq_sum_range (fun j => ∫ y in chebyshevGrid k j..chebyshevGrid k (j + 1), |F y|)
    (k + 2)]
  have hadj := intervalIntegral.sum_integral_adjacent_intervals (a := chebyshevGrid k)
    (μ := volume) (f := fun y => |F y|) (n := k + 2) fun j hj => by
      have hlo := chebyshevGrid_mem_Icc k j (by omega)
      have hhi := chebyshevGrid_mem_Icc k (j + 1) (by omega)
      have hle : chebyshevGrid k j ≤ chebyshevGrid k (j + 1) :=
        (chebyshevGrid_strictMono k (show (⟨j, by omega⟩ : Fin (k + 3)) < ⟨j + 1, by omega⟩ by
          simp [Fin.lt_def])).le
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
      exact hF_abs.mono_set (Icc_subset_Icc hlo.1 hhi.2)
  rw [hadj, chebyshevGrid_zero, chebyshevGrid_last]

/-! ### Exact integral-to-explicit error identity (eq. (5) & eq. (6)) -/

private theorem hasDerivAt_truncatedPower_shifted (n : ℕ) (hn : 0 < n) (t y : ℝ) :
    HasDerivAt (fun z => truncatedPower (n + 1) t z / ((n : ℝ) + 1)) (truncatedPower n t y) y := by
  have hcomp : HasDerivAt (fun z => truncatedPower (n + 1) 0 (z - t))
      (((n + 1 : ℕ) : ℝ) * truncatedPower n 0 (y - t)) y := by
    have h1 := hasDerivAt_truncatedPower_zero n hn (y - t)
    have h2 : HasDerivAt (fun z : ℝ => z - t) 1 y := (hasDerivAt_id y).sub_const t
    simpa [Function.comp_def] using h1.comp y h2
  have hfun : (fun z => truncatedPower (n + 1) t z / ((n : ℝ) + 1)) =
      fun z => truncatedPower (n + 1) 0 (z - t) / ((n : ℝ) + 1) := by
    ext z; simp [truncatedPower, sub_nonneg]
  have hval : truncatedPower n t y = truncatedPower n 0 (y - t) := by
    simp [truncatedPower, sub_nonneg]
  rw [hfun, hval]
  have hdiv := hcomp.div_const ((n : ℝ) + 1)
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hsimp : (((n + 1 : ℕ) : ℝ) * truncatedPower n 0 (y - t)) / ((n : ℝ) + 1) =
      truncatedPower n 0 (y - t) := by
    push_cast; field_simp
  rwa [hsimp] at hdiv

/-- **Exact integral-to-explicit error identity** (eq. (5) of `chebyshev_L1_complete.tex`):
for every `t ∈ [-1, 1]` and `n = k + 1`,
`∫_{-1}^1 |1_{x > t} - T_n h_t(x)| dx = explicitError (k + 1) (orderedNode k t) t`. -/
theorem integral_abs_indicator_sub_movingOperator_eq_explicitError (k : ℕ) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    ∫ x in (-1 : ℝ)..1,
      |(if t < x then (1 : ℝ) else 0) - movingOperator k (normTruncatedPower (k + 1) t) x| =
      explicitError (k + 1) (orderedNode k t) t := by
  have hht_cont : Continuous (normTruncatedPower (k + 1) t) :=
    (continuous_normTruncatedPower (Nat.succ_pos k)).comp (continuous_const.prodMk continuous_id)
  have hT_int_Icc : IntegrableOn (movingOperator k (normTruncatedPower (k + 1) t))
      (Icc (-1 : ℝ) 1) volume := by
    have h := intervalIntegrable_movingOperator k hht_cont.integrableOn_Icc
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp h
  have hT_int_left : IntervalIntegrable (movingOperator k (normTruncatedPower (k + 1) t))
      volume (-1) t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr
      (hT_int_Icc.mono_set (Icc_subset_Icc le_rfl ht.2))
  have hT_int_right : IntervalIntegrable (movingOperator k (normTruncatedPower (k + 1) t))
      volume t 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.2).mpr
      (hT_int_Icc.mono_set (Icc_subset_Icc ht.1 le_rfl))
  have hleft_eq :
      ∫ x in (-1 : ℝ)..t,
        |(if t < x then (1 : ℝ) else 0) - movingOperator k (normTruncatedPower (k + 1) t) x| =
      ∫ x in (-1 : ℝ)..t, movingOperator k (normTruncatedPower (k + 1) t) x := by
    rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1,
      MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    have hx' : |x| < 1 := abs_lt.mpr ⟨hx.1, lt_of_lt_of_le hx.2 ht.2⟩
    have hmem := movingOperator_normTruncatedPower_mem_Icc k t hx'
    rw [if_neg (not_lt_of_gt hx.2), zero_sub, abs_neg, abs_of_nonneg hmem.1]
  have hright_eq :
      ∫ x in t..1,
        |(if t < x then (1 : ℝ) else 0) - movingOperator k (normTruncatedPower (k + 1) t) x| =
      (1 - t) - ∫ x in t..1, movingOperator k (normTruncatedPower (k + 1) t) x := by
    have h1 : ∫ x in t..1,
        |(if t < x then (1 : ℝ) else 0) - movingOperator k (normTruncatedPower (k + 1) t) x| =
        ∫ x in t..1, (1 - movingOperator k (normTruncatedPower (k + 1) t) x) := by
      rw [intervalIntegral.integral_of_le ht.2, intervalIntegral.integral_of_le ht.2,
        MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      have hx' : |x| < 1 := abs_lt.mpr ⟨lt_of_le_of_lt ht.1 hx.1, hx.2⟩
      have hmem := movingOperator_normTruncatedPower_mem_Icc k t hx'
      rw [if_pos hx.1, abs_of_nonneg (sub_nonneg.mpr hmem.2)]
    rw [h1, intervalIntegral.integral_sub (intervalIntegrable_const (c := (1 : ℝ))) hT_int_right,
      intervalIntegral.integral_const, smul_eq_mul, mul_one]
  have hint_left : IntervalIntegrable
      (fun x => |(if t < x then (1 : ℝ) else 0) - movingOperator k (normTruncatedPower (k + 1) t) x|)
      volume (-1) t := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1]
    refine ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp hT_int_left).congr_fun
      (fun x hx => ?_) measurableSet_Ioo
    have hx' : |x| < 1 := abs_lt.mpr ⟨hx.1, lt_of_lt_of_le hx.2 ht.2⟩
    have hmem := movingOperator_normTruncatedPower_mem_Icc k t hx'
    rw [if_neg (not_lt_of_gt hx.2), zero_sub, abs_neg, abs_of_nonneg hmem.1]
  have hint_right : IntervalIntegrable
      (fun x => |(if t < x then (1 : ℝ) else 0) - movingOperator k (normTruncatedPower (k + 1) t) x|)
      volume t 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.2]
    refine ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.2).mp
      ((intervalIntegrable_const (c := (1 : ℝ))).sub hT_int_right)).congr_fun
      (fun x hx => ?_) measurableSet_Ioo
    have hx' : |x| < 1 := abs_lt.mpr ⟨lt_of_le_of_lt ht.1 hx.1, hx.2⟩
    have hmem := movingOperator_normTruncatedPower_mem_Icc k t hx'
    rw [if_pos hx.1, abs_of_nonneg (sub_nonneg.mpr hmem.2)]
  rw [← intervalIntegral.integral_add_adjacent_intervals hint_left hint_right, hleft_eq, hright_eq]
  have hpiece : ∀ {a b : ℝ}, a ∈ Icc (-1 : ℝ) 1 → b ∈ Icc (-1 : ℝ) 1 → a ≤ b →
      ∫ x in a..b, movingOperator k (normTruncatedPower (k + 1) t) x =
        (2 : ℝ) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) + 1) *
          ∑ j : Fin (k + 2), altSign (k + 1) j *
            (truncatedPower (k + 2) t (orderedNode k b j) -
              truncatedPower (k + 2) t (orderedNode k a j)) := by
    intro a b ha hb hab
    have hfac : ((k + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hfun : (fun x => movingOperator k (normTruncatedPower (k + 1) t) x) =
        fun x => (2 : ℝ) ^ (k + 1) * ∑ j : Fin (k + 2),
          altSign (k + 1) j * (orderedNodeSpeed k x j *
            truncatedPower (k + 1) t (orderedNode k x j)) := by
      ext x
      unfold movingOperator firstBestConstant normTruncatedPower
      rw [mul_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp [hfac]
    rw [hfun, intervalIntegral.integral_const_mul]
    have hterm_int : ∀ j : Fin (k + 2),
        IntervalIntegrable (fun x => altSign (k + 1) j *
          (orderedNodeSpeed k x j * truncatedPower (k + 1) t (orderedNode k x j))) volume a b := by
      intro j
      apply IntervalIntegrable.const_mul
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab,
        ← integrableOn_comp_orderedNode_iff k j ha hb hab (truncatedPower (k + 1) t)]
      exact ((continuous_truncatedPower (Nat.succ_pos k)).comp
        (continuous_const.prodMk continuous_id)).integrableOn_Icc.mono_set Ioo_subset_Icc_self
    rw [intervalIntegral.integral_finsetSum (fun j _ => hterm_int j)]
    have hsubst_j : ∀ j : Fin (k + 2),
        ∫ x in a..b, altSign (k + 1) j *
          (orderedNodeSpeed k x j * truncatedPower (k + 1) t (orderedNode k x j)) =
        altSign (k + 1) j *
          ((truncatedPower (k + 2) t (orderedNode k b j) -
            truncatedPower (k + 2) t (orderedNode k a j)) / (((k + 1 : ℕ) : ℝ) + 1)) := by
      intro j
      rw [intervalIntegral.integral_const_mul, ← intervalIntegral_comp_orderedNode k j ha hb hab]
      congr 1
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun z => truncatedPower (k + 2) t z / (((k + 1 : ℕ) : ℝ) + 1))
        (a := orderedNode k a j) (b := orderedNode k b j)
        (fun y _ => hasDerivAt_truncatedPower_shifted (k + 1) (Nat.succ_pos k) t y)
        (((continuous_truncatedPower (Nat.succ_pos k)).comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
      rw [hFTC, sub_div]
    simp_rw [hsubst_j]
    rw [div_mul_eq_mul_div, Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hpiece ⟨le_rfl, by norm_num⟩ ht ht.1, hpiece ht ⟨by norm_num, le_rfl⟩ ht.2]
  have hcomb :
      (2 : ℝ) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) + 1) *
        ∑ j : Fin (k + 2), altSign (k + 1) j *
          (truncatedPower (k + 2) t (orderedNode k t j) -
            truncatedPower (k + 2) t (orderedNode k (-1) j)) +
      ((1 - t) -
        (2 : ℝ) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) + 1) *
          ∑ j : Fin (k + 2), altSign (k + 1) j *
            (truncatedPower (k + 2) t (orderedNode k 1 j) -
              truncatedPower (k + 2) t (orderedNode k t j))) =
      1 - t - (2 : ℝ) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) + 1) *
        ∑ j : Fin (k + 2), altSign (k + 1) j *
          (truncatedPower (k + 2) t (chebyshevGrid k j.val) +
            truncatedPower (k + 2) t (chebyshevGrid k (j.val + 1))) +
      (2 : ℝ) ^ (k + 2) / (((k + 1 : ℕ) : ℝ) + 1) *
        ∑ j : Fin (k + 2), altSign (k + 1) j * truncatedPower (k + 2) t (orderedNode k t j) := by
    simp_rw [orderedNode_neg_one, orderedNode_one]
    have hsum_split :
        ∑ j : Fin (k + 2), altSign (k + 1) j *
          (truncatedPower (k + 2) t (orderedNode k t j) -
            truncatedPower (k + 2) t (chebyshevGrid k j.val)) -
        ∑ j : Fin (k + 2), altSign (k + 1) j *
          (truncatedPower (k + 2) t (chebyshevGrid k (j.val + 1)) -
            truncatedPower (k + 2) t (orderedNode k t j)) =
        2 * ∑ j : Fin (k + 2), altSign (k + 1) j *
          truncatedPower (k + 2) t (orderedNode k t j) -
        ∑ j : Fin (k + 2), altSign (k + 1) j *
          (truncatedPower (k + 2) t (chebyshevGrid k j.val) +
            truncatedPower (k + 2) t (chebyshevGrid k (j.val + 1))) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
    have hpow2 : (2 : ℝ) ^ (k + 2) = 2 * (2 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
    rw [hpow2]
    linear_combination (norm := ring)
      (2 : ℝ) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) + 1) * hsum_split
  rw [hcomb]
  have htele :
      ∑ j : Fin (k + 2), altSign (k + 1) j *
        (truncatedPower (k + 2) t (chebyshevGrid k j.val) +
          truncatedPower (k + 2) t (chebyshevGrid k (j.val + 1))) =
      (1 - t) ^ (k + 2) := by
    let g : ℕ → ℝ := fun j =>
      (-1 : ℝ) ^ (k + 2 - j) * truncatedPower (k + 2) t (chebyshevGrid k j)
    have hterm : ∀ j : Fin (k + 2),
        altSign (k + 1) j *
          (truncatedPower (k + 2) t (chebyshevGrid k j.val) +
            truncatedPower (k + 2) t (chebyshevGrid k (j.val + 1))) =
        g (j.val + 1) - g j.val := by
      intro j
      dsimp [altSign, g]
      have h1 : k + 2 - (j.val + 1) = k + 1 - j.val := by omega
      have h2 : k + 2 - j.val = (k + 1 - j.val) + 1 := by omega
      rw [h1, h2, pow_succ]
      ring
    simp_rw [hterm]
    rw [Fin.sum_univ_eq_sum_range (fun j => g (j + 1) - g j) (k + 2),
      Finset.sum_range_sub g (k + 2)]
    dsimp [g]
    rw [Nat.sub_self, pow_zero, one_mul, chebyshevGrid_last, chebyshevGrid_zero]
    have h1 : truncatedPower (k + 2) t 1 = (1 - t) ^ (k + 2) := by
      simp [truncatedPower, ht.2]
    have h0 : truncatedPower (k + 2) t (-1) = 0 := by
      rw [truncatedPower_eq_max_pow' (Nat.succ_pos _)]
      have hle : (-1 : ℝ) - t ≤ 0 := by linarith [ht.1]
      rw [max_eq_right hle, zero_pow (Nat.succ_ne_zero _)]
    rw [h1, h0, mul_zero, sub_zero]
  rw [htele]
  unfold explicitError altSign
  simp_rw [truncatedPower_eq_max_pow' (Nat.succ_pos (k + 1))]

/-- **Exact center formula** (eq. (6) of `chebyshev_L1_complete.tex`):
`explicitError (k + 1) (orderedNode k 0) 0 = centerBestConstant (k + 1)`. -/
theorem explicitError_center_eq (k : ℕ) :
    explicitError (k + 1) (orderedNode k 0) 0 = centerBestConstant (k + 1) := by
  unfold explicitError centerBestConstant
  simp only [sub_zero, one_pow, mul_one]
  congr 2
  have hrew_node : ∀ j : Fin (k + 2),
      orderedNode k 0 j = Real.cos (((k + 2 - j.val : ℕ) : ℝ) * Real.pi / ((k : ℝ) + 3)) := by
    intro j
    rw [orderedNode_zero]
    have hk3 : (k : ℝ) + 3 ≠ 0 := by positivity
    have harg : ((k + 2 - j.val : ℕ) : ℝ) * Real.pi / ((k : ℝ) + 3) =
        Real.pi - ((j.val : ℝ) + 1) * Real.pi / ((k : ℝ) + 3) := by
      rw [Nat.cast_sub (by omega : j.val ≤ k + 2)]
      push_cast
      field_simp
      ring
    rw [harg, Real.cos_pi_sub]
  simp_rw [hrew_node]
  have hsplit_sum :
      ∑ j : Fin (k + 2), (-1 : ℝ) ^ (k + 1 - j.val) *
        (max (Real.cos (((k + 2 - j.val : ℕ) : ℝ) * Real.pi / ((k : ℝ) + 3))) 0) ^ (k + 2) =
      ∑ m ∈ Finset.Icc 1 (k + 2), (-1 : ℝ) ^ (m - 1) *
        (max (Real.cos ((m : ℝ) * Real.pi / ((k : ℝ) + 3))) 0) ^ (k + 2) := by
    refine Finset.sum_bij (fun j _ => k + 2 - j.val) ?_ ?_ ?_ ?_
    · intro j _
      rw [Finset.mem_Icc]
      omega
    · intro a _ b _ hab
      ext; omega
    · intro m hm
      rw [Finset.mem_Icc] at hm
      exact ⟨⟨k + 2 - m, by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
    · intro j _
      have hexp : k + 1 - j.val = k + 2 - j.val - 1 := by omega
      rw [hexp]
  rw [hsplit_sum]
  have hsub : Finset.Icc 1 ((k + 2) / 2) ⊆ Finset.Icc 1 (k + 2) :=
    Finset.Icc_subset_Icc_right (Nat.div_le_self _ _)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    have hcos_nonneg : 0 ≤ Real.cos ((m : ℝ) * Real.pi / ((k : ℝ) + 3)) := by
      apply Real.cos_nonneg_of_mem_Icc
      have hk3 : (0 : ℝ) < (k : ℝ) + 3 := by positivity
      constructor
      · linarith [Real.pi_pos, show (0 : ℝ) ≤ (m : ℝ) * Real.pi / ((k : ℝ) + 3) by positivity]
      · rw [div_le_iff₀ hk3]
        have hm2 : (2 * m : ℝ) ≤ (k : ℝ) + 2 := by exact_mod_cast (by omega : 2 * m ≤ k + 2)
        nlinarith [Real.pi_pos]
    rw [max_eq_left hcos_nonneg]
    have hden : ((k + 1 : ℕ) : ℝ) + 2 = (k : ℝ) + 3 := by push_cast; ring
    rw [hden]
  · intro m hm hm_not
    rw [Finset.mem_Icc] at hm hm_not
    have hm_gt : (k + 2) / 2 < m := by omega
    have hcos_nonpos : Real.cos ((m : ℝ) * Real.pi / ((k : ℝ) + 3)) ≤ 0 := by
      apply Real.cos_nonpos_of_pi_div_two_le_of_le
      · have hk3 : (0 : ℝ) < (k : ℝ) + 3 := by positivity
        rw [le_div_iff₀ hk3]
        have hm2 : (k : ℝ) + 3 ≤ 2 * (m : ℝ) := by exact_mod_cast (by omega : k + 3 ≤ 2 * m)
        nlinarith [Real.pi_pos]
      · have hk3 : (0 : ℝ) < (k : ℝ) + 3 := by positivity
        rw [div_le_iff₀ hk3]
        have hmk : (m : ℝ) ≤ (k : ℝ) + 3 := by exact_mod_cast (by omega : m ≤ k + 3)
        nlinarith [Real.pi_pos]
    rw [max_eq_right hcos_nonpos, zero_pow (Nat.succ_ne_zero _), mul_zero]

/-! ### 1D Sobolev class `W^{m, 1}([a, b])` and integral Taylor representation -/

/-- The 1D Sobolev class `W^{m, 1}([a, b])` (continuous representatives):
functions with a chain of weak derivatives `d 0, ..., d m` where `d 0 = f` on `[a, b]`,
`d m ∈ L¹([a, b])`, and for every `j < m`, `d j` is continuous on `[a, b]` and satisfies the
Fundamental Theorem of Calculus `d j x - d j a = ∫ t in a..x, d (j + 1) t`. -/
structure SobolevW1 (m : ℕ) (a b : ℝ) (f : ℝ → ℝ) where
  d : ℕ → ℝ → ℝ
  d_zero : ∀ x ∈ Icc a b, d 0 x = f x
  continuousOn_d : ∀ j < m, ContinuousOn (d j) (Icc a b)
  integrable_top : IntegrableOn (d m) (Icc a b) volume
  ftc : ∀ j < m, ∀ x ∈ Icc a b, d j x - d j a = ∫ t in a..x, d (j + 1) t

/-- Shifting a `SobolevW1 (m + 1)` function drops the order by 1. -/
def SobolevW1.shift {m : ℕ} {a b : ℝ} {f : ℝ → ℝ} (F : SobolevW1 (m + 1) a b f) :
    SobolevW1 m a b (F.d 1) where
  d j := F.d (j + 1)
  d_zero _ _ := rfl
  continuousOn_d j hj := F.continuousOn_d (j + 1) (Nat.succ_lt_succ hj)
  integrable_top := F.integrable_top
  ftc j hj := F.ftc (j + 1) (Nat.succ_lt_succ hj)

/-- Fubini integration of the truncated-power Taylor kernel. -/
private theorem integral_taylor_kernel_step {a y : ℝ} (hay : a ≤ y) (m : ℕ) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Icc a y) volume) :
    ∫ s in a..y, (∫ t in a..s, (s - t) ^ m / (m.factorial : ℝ) * g t) =
      ∫ t in a..y, (y - t) ^ (m + 1) / ((m + 1).factorial : ℝ) * g t := by
  let K : ℝ → ℝ → ℝ := fun s t =>
    if t ≤ s then (s - t) ^ m / (m.factorial : ℝ) * g t else 0
  have hK_int : Integrable (Function.uncurry K)
      ((volume.restrict (Ioc a y)).prod (volume.restrict (Ioc a y))) := by
    have hmeas : AEStronglyMeasurable (Function.uncurry K)
        ((volume.restrict (Ioc a y)).prod (volume.restrict (Ioc a y))) := by
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 - p.2) ^ m / (m.factorial : ℝ))
          ((volume.restrict (Ioc a y)).prod (volume.restrict (Ioc a y))) :=
        (Continuous.aestronglyMeasurable (by fun_prop))
      have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.2)
          ((volume.restrict (Ioc a y)).prod (volume.restrict (Ioc a y))) :=
        (hg.mono_set Ioc_subset_Icc_self).aestronglyMeasurable.comp_snd
      exact (h1.mul h2).indicator (isClosed_le continuous_snd continuous_fst).measurableSet
    let C : ℝ := (y - a) ^ m / (m.factorial : ℝ)
    have hdom : Integrable (fun p : ℝ × ℝ => C * |g p.2|)
        ((volume.restrict (Ioc a y)).prod (volume.restrict (Ioc a y))) :=
      (integrable_const C).mul_prod (hg.mono_set Ioc_subset_Icc_self).abs
    refine hdom.mono' hmeas ?_
    have hae_prod : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ioc a y)).prod (volume.restrict (Ioc a y))),
        p ∈ Ioc a y ×ˢ Ioc a y := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
    filter_upwards [hae_prod] with ⟨s, t⟩ ⟨hs, ht⟩
    dsimp [Function.uncurry, K]
    split_ifs with hts
    · rw [abs_mul, abs_div, abs_of_nonneg (pow_nonneg (sub_nonneg.mpr hts) m),
        abs_of_nonneg (Nat.cast_nonneg _)]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact pow_le_pow_left₀ (sub_nonneg.mpr hts) (by linarith [hs.2, ht.1]) m
    · rw [abs_zero]
      exact mul_nonneg (div_nonneg (pow_nonneg (sub_nonneg.mpr hay) m) (Nat.cast_nonneg _))
        (abs_nonneg _)
  have hswap := MeasureTheory.integral_integral_swap hK_int
  have hLHS : ∫ s in a..y, (∫ t in a..s, (s - t) ^ m / (m.factorial : ℝ) * g t) =
      ∫ s in Ioc a y, ∫ t in Ioc a y, K s t := by
    rw [intervalIntegral.integral_of_le hay]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    rw [intervalIntegral.integral_of_le hs.1.le, ← MeasureTheory.integral_indicator measurableSet_Ioc,
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
    congr 1
    ext t
    dsimp [K, Set.indicator]
    by_cases ht1 : t ∈ Ioc a s <;> by_cases ht2 : t ∈ Ioc a y
    · simp [ht1, ht2, ht1.2]
    · exact absurd ⟨ht1.1, le_trans ht1.2 hs.2⟩ ht2
    · simp only [ht1, ht2, ite_true, ite_false]
      have hnot : ¬(t ≤ s) := fun hle => ht1 ⟨ht2.1, hle⟩
      simp [hnot]
    · simp [ht1, ht2]
  have hRHS : ∫ t in Ioc a y, ∫ s in Ioc a y, K s t =
      ∫ t in a..y, (y - t) ^ (m + 1) / ((m + 1).factorial : ℝ) * g t := by
    rw [intervalIntegral.integral_of_le hay]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have hinner : ∫ s in Ioc a y, K s t =
        (∫ s in t..y, (s - t) ^ m / (m.factorial : ℝ)) * g t := by
      have hrew : ∫ s in Ioc a y, K s t =
          ∫ s in Ioc t y, (s - t) ^ m / (m.factorial : ℝ) * g t := by
        rw [← MeasureTheory.integral_indicator measurableSet_Ioc,
          ← MeasureTheory.integral_indicator measurableSet_Ioc]
        have hae : (Ioc a y).indicator (fun s => K s t) =ᵐ[volume]
            (Ioc t y).indicator (fun s => (s - t) ^ m / (m.factorial : ℝ) * g t) := by
          have hsing : ∀ᵐ s ∂volume, s ≠ t := ae_iff.mpr (by simp [measure_singleton])
          filter_upwards [hsing] with s hne
          dsimp [K, Set.indicator]
          by_cases h1 : s ∈ Ioc a y <;> by_cases h2 : s ∈ Ioc t y
          · simp [h1, h2, h2.1.le]
          · simp only [h1, h2, ite_true, ite_false]
            have hnot : ¬(t ≤ s) := fun hle => h2 ⟨lt_of_le_of_ne hle hne.symm, h1.2⟩
            simp [hnot]
          · exact absurd ⟨lt_trans ht.1 h2.1, h2.2⟩ h1
          · simp [h1, h2]
        exact integral_congr_ae hae
      rw [hrew, ← intervalIntegral.integral_of_le ht.2, intervalIntegral.integral_mul_const]
    rw [hinner]
    congr 1
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s => (s - t) ^ (m + 1) / ((m + 1).factorial : ℝ))
      (a := t) (b := y)
      (fun s _ => by
        have h1 : HasDerivAt (fun z : ℝ => (z - t) ^ (m + 1))
            (((m + 1 : ℕ) : ℝ) * (s - t) ^ m) s := by
          simpa [Function.comp_def] using
            (hasDerivAt_pow (m + 1) (s - t)).comp s ((hasDerivAt_id s).sub_const t)
        have h2 := h1.div_const ((m + 1).factorial : ℝ)
        have hsimp : (((m + 1 : ℕ) : ℝ) * (s - t) ^ m) / ((m + 1).factorial : ℝ) =
            (s - t) ^ m / (m.factorial : ℝ) := by
          rw [Nat.factorial_succ]
          have hne1 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          have hne2 : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
          push_cast at hne1 ⊢
          field_simp
        rwa [hsimp] at h2)
      ((by fun_prop : Continuous fun s : ℝ => (s - t) ^ m / (m.factorial : ℝ)).intervalIntegrable _ _)
    rw [hFTC, sub_self, zero_pow (Nat.succ_ne_zero m), zero_div, sub_zero]
  rw [hLHS, hswap, hRHS]

/-- **Integral Taylor remainder for `SobolevW1 (m + 1) a b f`**:
for all `y ∈ [a, b]`,
`f y = ∑ r ∈ Finset.range (m + 1), F.d r a / r! * (y - a)^r + ∫ t in a..b, h_t(y) * F.d (m + 1) t`. -/
theorem SobolevW1.taylor_formula {m : ℕ} {a b : ℝ} (_hab : a ≤ b) {f : ℝ → ℝ}
    (F : SobolevW1 (m + 1) a b f) {y : ℝ} (hy : y ∈ Icc a b) :
    f y = (∑ r ∈ Finset.range (m + 1), F.d r a / (r.factorial : ℝ) * (y - a) ^ r) +
      ∫ t in a..b, normTruncatedPower m t y * F.d (m + 1) t := by
  have hmain : ∀ m : ℕ, ∀ {f : ℝ → ℝ} (F : SobolevW1 (m + 1) a b f), ∀ y ∈ Icc a b,
      F.d 0 y = (∑ r ∈ Finset.range (m + 1), F.d r a / (r.factorial : ℝ) * (y - a) ^ r) +
        ∫ t in a..y, (y - t) ^ m / (m.factorial : ℝ) * F.d (m + 1) t := by
    intro m
    induction m with
    | zero =>
      intro f F y hy
      have hftc := F.ftc 0 (Nat.zero_lt_succ 0) y hy
      rw [Finset.sum_range_one]
      simp only [Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, mul_one, one_mul]
      linarith
    | succ m ih =>
      intro f F y hy
      have hftc0 := F.ftc 0 (Nat.zero_lt_succ _) y hy
      have hshift : ∀ s ∈ Icc a b,
          F.d 1 s = (∑ r ∈ Finset.range (m + 1), F.d (r + 1) a / (r.factorial : ℝ) * (s - a) ^ r) +
            ∫ t in a..s, (s - t) ^ m / (m.factorial : ℝ) * F.d (m + 2) t :=
        fun s hs => ih F.shift s hs
      have hsub_int : ∫ s in a..y, F.d 1 s =
          ∫ s in a..y,
            ((∑ r ∈ Finset.range (m + 1), F.d (r + 1) a / (r.factorial : ℝ) * (s - a) ^ r) +
              ∫ t in a..s, (s - t) ^ m / (m.factorial : ℝ) * F.d (m + 2) t) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hy.1] at hs
        exact hshift s ⟨hs.1, le_trans hs.2 hy.2⟩
      have hpoly_int : IntervalIntegrable
          (fun s => ∑ r ∈ Finset.range (m + 1), F.d (r + 1) a / (r.factorial : ℝ) * (s - a) ^ r)
          volume a y :=
        (by fun_prop : Continuous fun s =>
          ∑ r ∈ Finset.range (m + 1), F.d (r + 1) a / (r.factorial : ℝ) * (s - a) ^ r).intervalIntegrable _ _
      have hrem_int : IntervalIntegrable
          (fun s => ∫ t in a..s, (s - t) ^ m / (m.factorial : ℝ) * F.d (m + 2) t) volume a y := by
        have heq_rem : ∀ s ∈ uIcc a y,
            ∫ t in a..s, (s - t) ^ m / (m.factorial : ℝ) * F.d (m + 2) t =
            F.d 1 s - ∑ r ∈ Finset.range (m + 1), F.d (r + 1) a / (r.factorial : ℝ) * (s - a) ^ r := by
          intro s hs
          rw [uIcc_of_le hy.1] at hs
          linarith [hshift s ⟨hs.1, le_trans hs.2 hy.2⟩]
        have hd1_int : IntervalIntegrable (F.d 1) volume a y :=
          ((F.continuousOn_d 1 (by omega)).mono (Icc_subset_Icc le_rfl hy.2)).intervalIntegrable_of_Icc hy.1
        exact (hd1_int.sub hpoly_int).congr (fun s hs => (heq_rem s (uIoc_subset_uIcc hs)).symm)
      rw [hsub_int, intervalIntegral.integral_add hpoly_int hrem_int] at hftc0
      have hpoly_eval :
          ∫ s in a..y, (∑ r ∈ Finset.range (m + 1), F.d (r + 1) a / (r.factorial : ℝ) * (s - a) ^ r) =
          ∑ r ∈ Finset.range (m + 1), F.d (r + 1) a / ((r + 1).factorial : ℝ) * (y - a) ^ (r + 1) := by
        rw [intervalIntegral.integral_finsetSum (fun r _ =>
          (by fun_prop : Continuous fun s : ℝ =>
            F.d (r + 1) a / (r.factorial : ℝ) * (s - a) ^ r).intervalIntegrable _ _)]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [intervalIntegral.integral_const_mul]
        have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun s => (s - a) ^ (r + 1) / ((r : ℝ) + 1)) (a := a) (b := y)
          (fun s _ => by
            have h1 : HasDerivAt (fun z : ℝ => (z - a) ^ (r + 1))
                (((r + 1 : ℕ) : ℝ) * (s - a) ^ r) s := by
              simpa [Function.comp_def] using
                (hasDerivAt_pow (r + 1) (s - a)).comp s ((hasDerivAt_id s).sub_const a)
            have h2 := h1.div_const ((r : ℝ) + 1)
            have hne : ((r : ℝ) + 1) ≠ 0 := by positivity
            have hsimp : (((r + 1 : ℕ) : ℝ) * (s - a) ^ r) / ((r : ℝ) + 1) = (s - a) ^ r := by
              push_cast; field_simp
            rwa [hsimp] at h2)
          ((by fun_prop : Continuous fun s : ℝ => (s - a) ^ r).intervalIntegrable _ _)
        rw [hFTC, sub_self, zero_pow (Nat.succ_ne_zero r), zero_div, sub_zero, Nat.factorial_succ]
        have hne1 : ((r : ℝ) + 1) ≠ 0 := by positivity
        have hne2 : (r.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        push_cast
        field_simp
      have hrem_eval := integral_taylor_kernel_step hy.1 m
        (F.integrable_top.mono_set (Icc_subset_Icc le_rfl hy.2))
      rw [hpoly_eval, hrem_eval] at hftc0
      rw [Finset.sum_range_succ']
      simp only [Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, mul_one]
      linarith
  rw [← F.d_zero y hy, hmain m F y hy]
  congr 1
  have h1 : ∫ t in a..y, (y - t) ^ m / (m.factorial : ℝ) * F.d (m + 1) t =
      ∫ t in a..y, normTruncatedPower m t y * F.d (m + 1) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hy.1] at ht
    simp [normTruncatedPower, truncatedPower, ht.2]
  have h2 : ∫ t in y..b, normTruncatedPower m t y * F.d (m + 1) t = 0 := by
    rw [intervalIntegral.integral_of_le hy.2]
    refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
    simp [normTruncatedPower, truncatedPower, not_le_of_gt ht.1]
  have hint_left : IntervalIntegrable (fun t => normTruncatedPower m t y * F.d (m + 1) t)
      volume a y := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hy.1]
    have hcont : ContinuousOn (fun t => (y - t) ^ m / (m.factorial : ℝ)) (Icc a y) := by fun_prop
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    have hdom : IntegrableOn (fun t => C * |F.d (m + 1) t|) (Icc a y) volume :=
      ((F.integrable_top.mono_set (Icc_subset_Icc le_rfl hy.2)).abs).const_mul C
    have hmeas : AEStronglyMeasurable (fun t => (y - t) ^ m / (m.factorial : ℝ) * F.d (m + 1) t)
        (volume.restrict (Icc a y)) :=
      (hcont.aestronglyMeasurable measurableSet_Icc).mul
        (F.integrable_top.mono_set (Icc_subset_Icc le_rfl hy.2)).aestronglyMeasurable
    have hint_poly : IntegrableOn (fun t => (y - t) ^ m / (m.factorial : ℝ) * F.d (m + 1) t)
        (Icc a y) volume := by
      refine hdom.mono' hmeas ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hC t ht) (abs_nonneg _)
    exact hint_poly.congr_fun
      (fun t ht => by simp [normTruncatedPower, truncatedPower, ht.2]) measurableSet_Icc
  have hint_right : IntervalIntegrable (fun t => normTruncatedPower m t y * F.d (m + 1) t)
      volume y b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hy.2]
    exact (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioc y b) volume).congr_fun
      (fun t ht => by simp [normTruncatedPower, truncatedPower, not_le_of_gt ht.1]) measurableSet_Ioc
  rw [← intervalIntegral.integral_add_adjacent_intervals hint_left hint_right, h2, add_zero, h1]

/-- **Exact kernel representation for `F^(n) - T_n F`** (Section 4 of `chebyshev_L1_complete.tex`):
for `n = k + 1`, `F : SobolevW1 (k + 2) (-1) 1 f`, and `x ∈ (-1, 1)`,
`F.d (k + 1) x - T_{k+1} f x = ∫ t in (-1)..1, (1_{x > t} - T_{k+1} h_t(x)) * F.d (k + 2) t`. -/
theorem SobolevW1.deriv_sub_movingOperator_eq (k : ℕ) {f : ℝ → ℝ}
    (F : SobolevW1 (k + 2) (-1) 1 f) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    F.d (k + 1) x - movingOperator k f x =
      ∫ t in (-1 : ℝ)..1,
        ((if t < x then (1 : ℝ) else 0) - movingOperator k (normTruncatedPower (k + 1) t) x) *
          F.d (k + 2) t := by
  have hx_abs : |x| < 1 := abs_lt.mpr hx
  have hx_Icc : x ∈ Icc (-1 : ℝ) 1 := Ioo_subset_Icc_self hx
  let P : ℝ[X] := ∑ r ∈ Finset.range (k + 2),
    C (F.d r (-1) / (r.factorial : ℝ)) * (X - C (-1 : ℝ)) ^ r
  have hP_eval : ∀ y : ℝ, P.eval y =
      ∑ r ∈ Finset.range (k + 2), F.d r (-1) / (r.factorial : ℝ) * (y - (-1)) ^ r := by
    intro y
    simp [P, eval_finsetSum]
  have hdeg_X1 : (X - C (-1 : ℝ)).natDegree = 1 := by
    have hrew : X - C (-1 : ℝ) = X + C (1 : ℝ) := by simp [sub_eq_add_neg]
    rw [hrew, Polynomial.natDegree_X_add_C]
  have hdeg_pow : ∀ r : ℕ, ((X - C (-1 : ℝ)) ^ r).natDegree = r := by
    intro r
    rw [Polynomial.natDegree_pow, hdeg_X1, mul_one]
  have hP_deg : P.natDegree ≤ k + 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun r hr => ?_
    have hr' : r ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    calc (C (F.d r (-1) / (r.factorial : ℝ)) * (X - C (-1 : ℝ)) ^ r).natDegree
        ≤ ((X - C (-1 : ℝ)) ^ r).natDegree := natDegree_C_mul_le _ _
      _ = r := hdeg_pow r
      _ ≤ k + 1 := hr'
  have hP_coeff : P.coeff (k + 1) = F.d (k + 1) (-1) / ((k + 1).factorial : ℝ) := by
    simp only [P, finsetSum_coeff]
    rw [Finset.sum_eq_single (k + 1)]
    · rw [coeff_C_mul]
      have hmon : ((X - C (-1 : ℝ)) ^ (k + 1)).Monic := (monic_X_sub_C (-1 : ℝ)).pow _
      have h1 : ((X - C (-1 : ℝ)) ^ (k + 1)).coeff (k + 1) = 1 := by
        rwa [Polynomial.Monic, leadingCoeff, hdeg_pow (k + 1)] at hmon
      rw [h1, mul_one]
    · intro r hr hne
      have hlt : r < k + 1 := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)) hne
      rw [coeff_C_mul, Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg_pow r]; exact hlt),
        mul_zero]
    · intro hnot
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self (k + 1))) hnot
  have hTP : movingOperator k (fun y => P.eval y) x = F.d (k + 1) (-1) := by
    rw [movingOperator_poly k P hP_deg hx_abs,
      iteratedDeriv_polynomial_eval_of_natDegree_le P (k + 1) hP_deg x, hP_coeff]
    have hfac : ((k + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp [hfac]
  have hrem_int : ∀ j : Fin (k + 2),
      IntervalIntegrable
        (fun t => normTruncatedPower (k + 1) t (orderedNode k x j) * F.d (k + 2) t)
        volume (-1) 1 := by
    intro j
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    have hcont : ContinuousOn (fun t => normTruncatedPower (k + 1) t (orderedNode k x j))
        (Icc (-1 : ℝ) 1) :=
      ((continuous_normTruncatedPower (Nat.succ_pos k)).comp
        (continuous_id.prodMk continuous_const)).continuousOn
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    refine (F.integrable_top.abs.const_mul C).mono'
      ((hcont.aestronglyMeasurable measurableSet_Icc).mul F.integrable_top.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hC t ht) (abs_nonneg _)
  have hTf : movingOperator k f x =
      F.d (k + 1) (-1) +
        ∫ t in (-1 : ℝ)..1,
          movingOperator k (normTruncatedPower (k + 1) t) x * F.d (k + 2) t := by
    have h1 : movingOperator k f x =
        movingOperator k (fun y => P.eval y) x +
          firstBestConstant (k + 1) * ∑ j : Fin (k + 2),
            altSign (k + 1) j * orderedNodeSpeed k x j *
              ∫ t in (-1 : ℝ)..1, normTruncatedPower (k + 1) t (orderedNode k x j) * F.d (k + 2) t := by
      unfold movingOperator
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      have huj : orderedNode k x j ∈ Icc (-1 : ℝ) 1 := orderedNode_mem_Icc_unit k hx_Icc j
      dsimp only
      rw [F.taylor_formula (by norm_num : (-1 : ℝ) ≤ 1) huj, hP_eval]
      ring
    rw [h1, hTP]
    congr 1
    simp_rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_finsetSum (fun j _ => (hrem_int j).const_mul _),
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    unfold movingOperator
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => by ring
  have hftc_ind : F.d (k + 1) x - F.d (k + 1) (-1) =
      ∫ t in (-1 : ℝ)..1, (if t < x then (1 : ℝ) else 0) * F.d (k + 2) t := by
    rw [F.ftc (k + 1) (Nat.lt_succ_self _) x hx_Icc]
    have hleft : ∫ t in (-1 : ℝ)..x, (if t < x then (1 : ℝ) else 0) * F.d (k + 2) t =
        ∫ t in (-1 : ℝ)..x, F.d (k + 2) t := by
      rw [intervalIntegral.integral_of_le hx_Icc.1, intervalIntegral.integral_of_le hx_Icc.1,
        MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      exact setIntegral_congr_fun measurableSet_Ioo fun t ht => by simp [ht.2]
    have hright : ∫ t in x..1, (if t < x then (1 : ℝ) else 0) * F.d (k + 2) t = 0 := by
      rw [intervalIntegral.integral_of_le hx_Icc.2]
      exact setIntegral_eq_zero_of_forall_eq_zero fun t ht => by simp [not_lt_of_gt ht.1]
    have hint1 : IntervalIntegrable (fun t => (if t < x then (1 : ℝ) else 0) * F.d (k + 2) t)
        volume (-1) x := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hx_Icc.1]
      exact (F.integrable_top.mono_set (Ioo_subset_Icc_self.trans (Icc_subset_Icc le_rfl hx_Icc.2))).congr_fun
        (fun t ht => by simp [ht.2]) measurableSet_Ioo
    have hint2 : IntervalIntegrable (fun t => (if t < x then (1 : ℝ) else 0) * F.d (k + 2) t)
        volume x 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx_Icc.2]
      exact (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioc x 1) volume).congr_fun
        (fun t ht => by simp [not_lt_of_gt ht.1]) measurableSet_Ioc
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2, hleft, hright, add_zero]
  have hint_ind : IntervalIntegrable (fun t => (if t < x then (1 : ℝ) else 0) * F.d (k + 2) t)
      volume (-1) 1 := by
    have h1 : IntervalIntegrable (fun t => (if t < x then (1 : ℝ) else 0) * F.d (k + 2) t)
        volume (-1) x := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hx_Icc.1]
      exact (F.integrable_top.mono_set (Ioo_subset_Icc_self.trans (Icc_subset_Icc le_rfl hx_Icc.2))).congr_fun
        (fun t ht => by simp [ht.2]) measurableSet_Ioo
    have h2 : IntervalIntegrable (fun t => (if t < x then (1 : ℝ) else 0) * F.d (k + 2) t)
        volume x 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx_Icc.2]
      exact (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioc x 1) volume).congr_fun
        (fun t ht => by simp [not_lt_of_gt ht.1]) measurableSet_Ioc
    exact h1.trans h2
  have hint_T : IntervalIntegrable
      (fun t => movingOperator k (normTruncatedPower (k + 1) t) x * F.d (k + 2) t) volume (-1) 1 := by
    have heq : (fun t => movingOperator k (normTruncatedPower (k + 1) t) x * F.d (k + 2) t) =
        fun t => firstBestConstant (k + 1) * ∑ j : Fin (k + 2),
          (altSign (k + 1) j * orderedNodeSpeed k x j) *
            (normTruncatedPower (k + 1) t (orderedNode k x j) * F.d (k + 2) t) := by
      ext t; unfold movingOperator
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [heq]
    have hsum : IntervalIntegrable
        (fun t => ∑ j : Fin (k + 2), (altSign (k + 1) j * orderedNodeSpeed k x j) *
          (normTruncatedPower (k + 1) t (orderedNode k x j) * F.d (k + 2) t)) volume (-1) 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
      exact integrable_finsetSum Finset.univ fun j _ =>
        (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp
          ((hrem_int j).const_mul (altSign (k + 1) j * orderedNodeSpeed k x j))
    exact hsum.const_mul _
  have hsub_eq : F.d (k + 1) x - movingOperator k f x =
      (F.d (k + 1) x - F.d (k + 1) (-1)) -
        ∫ t in (-1 : ℝ)..1,
          movingOperator k (normTruncatedPower (k + 1) t) x * F.d (k + 2) t := by
    linarith [hTf]
  rw [hsub_eq, hftc_ind, ← intervalIntegral.integral_sub hint_ind hint_T]
  refine intervalIntegral.integral_congr fun t _ => by ring

/-- **Fubini error bound for `F^(n) - T_n F`**:
for `n = k + 1` and `F : SobolevW1 (k + 2) (-1) 1 f`,
`‖F^(n) - T_n F‖_{L¹[-1,1]} ≤ ∫_{-1}^1 E_n(t) * |F^(n+1)(t)| dt`. -/
theorem SobolevW1.L1_deriv_sub_movingOperator_le (k : ℕ) {f : ℝ → ℝ}
    (F : SobolevW1 (k + 2) (-1) 1 f) :
    ∫ x in (-1 : ℝ)..1, |F.d (k + 1) x - movingOperator k f x| ≤
      ∫ t in (-1 : ℝ)..1, explicitError (k + 1) (orderedNode k t) t * |F.d (k + 2) t| := by
  let K : ℝ → ℝ → ℝ := fun x t =>
    |(if t < x then (1 : ℝ) else 0) - movingOperator k (normTruncatedPower (k + 1) t) x| *
      |F.d (k + 2) t|
  have hK_meas : AEStronglyMeasurable (Function.uncurry K)
      ((volume.restrict (Ioo (-1 : ℝ) 1)).prod (volume.restrict (Ioo (-1 : ℝ) 1))) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => if p.2 < p.1 then (1 : ℝ) else 0)
        ((volume.restrict (Ioo (-1 : ℝ) 1)).prod (volume.restrict (Ioo (-1 : ℝ) 1))) :=
      (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ × ℝ => (1 : ℝ)) _).indicator
        (isOpen_lt continuous_snd continuous_fst).measurableSet
    have h2 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => movingOperator k (normTruncatedPower (k + 1) p.2) p.1)
        ((volume.restrict (Ioo (-1 : ℝ) 1)).prod (volume.restrict (Ioo (-1 : ℝ) 1))) := by
      have hcont : ContinuousOn
          (fun p : ℝ × ℝ => movingOperator k (normTruncatedPower (k + 1) p.2) p.1)
          (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) := by
        unfold movingOperator
        refine continuousOn_const.mul (continuousOn_finsetSum Finset.univ fun j _ => ?_)
        have hsp : ContinuousOn (fun p : ℝ × ℝ => orderedNodeSpeed k p.1 j)
            (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) :=
          (continuousOn_orderedNodeSpeed k j).comp continuous_fst.continuousOn (fun _ hp => hp.1)
        have htp : ContinuousOn
            (fun p : ℝ × ℝ => normTruncatedPower (k + 1) p.2 (orderedNode k p.1 j))
            (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) :=
          (continuous_normTruncatedPower (Nat.succ_pos k)).continuousOn.comp
            (continuous_snd.prodMk ((continuous_orderedNode k j).comp continuous_fst)).continuousOn
            (fun _ _ => Set.mem_univ _)
        exact (continuousOn_const.mul hsp).mul htp
      rw [Measure.prod_restrict]
      exact hcont.aestronglyMeasurable (measurableSet_Ioo.prod measurableSet_Ioo)
    have h3 : AEStronglyMeasurable (fun p : ℝ × ℝ => |F.d (k + 2) p.2|)
        ((volume.restrict (Ioo (-1 : ℝ) 1)).prod (volume.restrict (Ioo (-1 : ℝ) 1))) :=
      (F.integrable_top.mono_set Ioo_subset_Icc_self).abs.aestronglyMeasurable.comp_snd
    exact (continuous_abs.comp_aestronglyMeasurable (h1.sub h2)).mul h3
  have hK_int : Integrable (Function.uncurry K)
      ((volume.restrict (Ioo (-1 : ℝ) 1)).prod (volume.restrict (Ioo (-1 : ℝ) 1))) := by
    have hdom : Integrable (fun p : ℝ × ℝ => (1 : ℝ) * |F.d (k + 2) p.2|)
        ((volume.restrict (Ioo (-1 : ℝ) 1)).prod (volume.restrict (Ioo (-1 : ℝ) 1))) :=
      (integrable_const (1 : ℝ)).mul_prod (F.integrable_top.mono_set Ioo_subset_Icc_self).abs
    refine hdom.mono' hK_meas ?_
    have hae : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (-1 : ℝ) 1))), p ∈ Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1 := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
    filter_upwards [hae] with ⟨x, t⟩ ⟨hx, _⟩
    have hmem := movingOperator_normTruncatedPower_mem_Icc k t (abs_lt.mpr hx)
    have habs_le : |(if t < x then (1 : ℝ) else 0) -
        movingOperator k (normTruncatedPower (k + 1) t) x| ≤ 1 := by
      split_ifs
      · rw [abs_of_nonneg (sub_nonneg.mpr hmem.2)]; linarith [hmem.1]
      · rw [zero_sub, abs_neg, abs_of_nonneg hmem.1]; exact hmem.2
    dsimp [Function.uncurry, K]
    rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
    exact mul_le_mul_of_nonneg_right habs_le (abs_nonneg _)
  have hLHS_int : IntegrableOn (fun x => |F.d (k + 1) x - movingOperator k f x|)
      (Ioo (-1 : ℝ) 1) volume := by
    have hf_int : IntegrableOn f (Icc (-1 : ℝ) 1) volume :=
      ((F.continuousOn_d 0 (Nat.zero_lt_succ _)).integrableOn_Icc).congr_fun
        (fun x hx => F.d_zero x hx) measurableSet_Icc
    have hd_int : IntegrableOn (F.d (k + 1)) (Ioo (-1 : ℝ) 1) volume :=
      (F.continuousOn_d (k + 1) (Nat.lt_succ_self _)).integrableOn_Icc.mono_set Ioo_subset_Icc_self
    have hT_int : IntegrableOn (movingOperator k f) (Ioo (-1 : ℝ) 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp
        (intervalIntegrable_movingOperator k hf_int)
    exact (hd_int.sub hT_int).abs
  have hRHS_int : IntegrableOn (fun x => ∫ t in Ioo (-1 : ℝ) 1, K x t)
      (Ioo (-1 : ℝ) 1) volume := hK_int.integral_prod_left
  calc ∫ x in (-1 : ℝ)..1, |F.d (k + 1) x - movingOperator k f x|
      = ∫ x in Ioo (-1 : ℝ) 1, |F.d (k + 1) x - movingOperator k f x| := by
        rw [intervalIntegral.integral_of_le (by norm_num), MeasureTheory.integral_Ioc_eq_integral_Ioo]
    _ ≤ ∫ x in Ioo (-1 : ℝ) 1, ∫ t in Ioo (-1 : ℝ) 1, K x t := by
        apply MeasureTheory.setIntegral_mono_on hLHS_int hRHS_int measurableSet_Ioo
        intro x hx
        rw [F.deriv_sub_movingOperator_eq k hx]
        calc |∫ t in (-1 : ℝ)..1,
                ((if t < x then (1 : ℝ) else 0) -
                  movingOperator k (normTruncatedPower (k + 1) t) x) * F.d (k + 2) t|
            ≤ ∫ t in (-1 : ℝ)..1,
                |((if t < x then (1 : ℝ) else 0) -
                  movingOperator k (normTruncatedPower (k + 1) t) x) * F.d (k + 2) t| :=
              intervalIntegral.abs_integral_le_integral_abs (by norm_num)
          _ = ∫ t in Ioo (-1 : ℝ) 1, K x t := by
              rw [intervalIntegral.integral_of_le (by norm_num),
                MeasureTheory.integral_Ioc_eq_integral_Ioo]
              refine setIntegral_congr_fun measurableSet_Ioo fun t _ => abs_mul _ _
    _ = ∫ t in Ioo (-1 : ℝ) 1, ∫ x in Ioo (-1 : ℝ) 1, K x t :=
        MeasureTheory.integral_integral_swap hK_int
    _ = ∫ t in (-1 : ℝ)..1, explicitError (k + 1) (orderedNode k t) t * |F.d (k + 2) t| := by
        rw [intervalIntegral.integral_of_le (by norm_num), MeasureTheory.integral_Ioc_eq_integral_Ioo]
        refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
        dsimp [K]
        rw [MeasureTheory.integral_mul_const,
          ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
          integral_abs_indicator_sub_movingOperator_eq_explicitError k (Ioo_subset_Icc_self ht)]

end SharpL1.Analysis
