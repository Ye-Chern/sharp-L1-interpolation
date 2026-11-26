module

public import SharpL1.Analysis.TruncatedPowerDeriv
public import SharpL1.Analysis.ErrorValue
public import SharpL1.Analysis.Exterior
public import SharpL1.Analysis.GlobalNodes
public import SharpL1.Analysis.DividedCDFBridge
public import SharpL1.Analysis.LowOrderNodes
public import SharpL1.Analysis.FirstTermPos
public import SharpL1.Analysis.ChordIntegral
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# The explicit interpolation error, its derivative, exterior monotonicity, and Hcomp

This module completes the explicit error-curve analysis for all orders `n = k + 1 ≥ 1`:
1. `explicitErrorAt k t` / `explicitErrorCurve n t` and `HAt` / `HCurve`.
2. Continuity on `ℝ` (and `[-1, 1]`), boundary values `E_n(±1) = 0`, evenness `E_n(-t) = E_n(t)`,
   and the exact center value `E_n(0)` (eq. (6)).
3. Total derivative `HasDerivAt` on `(-1, 1)` (`hasDerivAt_explicitErrorAt`, `hasDerivAt_HCurve`).
4. Exterior strict monotonicity `E_n'(t) < 0` on `[1/2, 1)` (`clm:outer`).
5. The barycentric / weighted-exponential `Hcomp` decomposition (eq. (9)) on `(-1, 1)`.
-/

namespace SharpL1.Analysis

open SharpL1
open SharpL1.Probability
open Polynomial Filter Set Topology
open Polynomial.Chebyshev (U)

private theorem truncatedPower_eq_max_pow {m : ℕ} (hm : m ≠ 0) (x : ℝ) :
    truncatedPower m 0 x = (max x 0) ^ m := by
  by_cases hx : 0 ≤ x
  · simp [truncatedPower, hx]
  · simp [truncatedPower, hx, max_eq_right (le_of_not_ge hx), zero_pow hm]

private theorem truncatedPower_sub_eq (m : ℕ) (t y : ℝ) :
    truncatedPower m 0 (y - t) = truncatedPower m t y := by
  by_cases h : t ≤ y
  · have h' : 0 ≤ y - t := sub_nonneg.mpr h
    simp [truncatedPower, h, h']
  · have h' : ¬ (0 ≤ y - t) := fun hh => h (sub_nonneg.mp hh)
    simp [truncatedPower, h, h']

/-- Differentiate the explicit error, including a parameter at which a node
crosses the diagonal. -/
theorem hasDerivAt_explicitError (n : ℕ) (hn : 0 < n) (u : Fin (n + 1) → ℝ → ℝ)
    (v : Fin (n + 1) → ℝ) (t : ℝ) (hu : ∀ j, HasDerivAt (u j) (v j) t) :
    HasDerivAt (fun x => explicitError n (fun j => u j x) x)
      (-1 + (2 : ℝ) ^ n * (1 - t) ^ n + (2 : ℝ) ^ (n + 1) *
        ∑ j, (-1 : ℝ) ^ (n - j.val) * truncatedPower n 0 (u j t - t) * (v j - 1)) t := by
  have hbase := (hasDerivAt_id t).const_sub 1
  have hpow : HasDerivAt (fun x : ℝ => (1 - x) ^ (n + 1))
      (-((n : ℝ) + 1) * (1 - t) ^ n) t := by
    simpa only [Function.comp_def, id_eq, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel,
      mul_neg, mul_one, neg_mul] using (hasDerivAt_pow (n + 1) (1 - t)).comp t hbase
  have hsum : HasDerivAt (fun x : ℝ => ∑ j : Fin (n + 1),
      (-1 : ℝ) ^ (n - j.val) * truncatedPower (n + 1) 0 (u j x - x))
      (((n : ℝ) + 1) * ∑ j : Fin (n + 1),
        (-1 : ℝ) ^ (n - j.val) * truncatedPower n 0 (u j t - t) * (v j - 1)) t := by
    rw [Finset.mul_sum]
    apply HasDerivAt.fun_sum
    intro j _
    have hinner : HasDerivAt (fun x => u j x - x) (v j - 1) t :=
      (hu j).sub (hasDerivAt_id t)
    have hj := (hasDerivAt_truncatedPower_zero n hn (u j t - t)).comp
      (h := fun x : ℝ => u j x - x) t hinner
    simpa [Function.comp_def, mul_assoc, mul_left_comm, mul_comm] using
      hj.const_mul ((-1 : ℝ) ^ (n - j.val))
  have hd : HasDerivAt (fun x => explicitError n (fun j => u j x) x)
      (0 - 1 - (2 : ℝ) ^ n / ((n : ℝ) + 1) * (-((n : ℝ) + 1) * (1 - t) ^ n) +
        (2 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) * (((n : ℝ) + 1) * ∑ j : Fin (n + 1),
          (-1 : ℝ) ^ (n - j.val) * truncatedPower n 0 (u j t - t) * (v j - 1))) t := by
    simp only [explicitError, ← truncatedPower_eq_max_pow (Nat.succ_ne_zero n)]
    change HasDerivAt (((fun x : ℝ => 1 - id x) - (fun y : ℝ =>
        (2 : ℝ) ^ n / ((n : ℝ) + 1) * (1 - y) ^ (n + 1))) + (fun y : ℝ =>
        (2 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) * ∑ j,
          (-1 : ℝ) ^ (n - j.val) * truncatedPower (n + 1) 0 (u j y - y))) _ t
    simpa only [zero_sub] using
      (hbase.sub (hpow.const_mul ((2 : ℝ) ^ n / ((n : ℝ) + 1)))).add
        (hsum.const_mul ((2 : ℝ) ^ (n + 1) / ((n : ℝ) + 1)))
  convert hd using 1
  have hn' : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  field_simp [hn'.ne']
  ring

/-! ### Explicit error and H curves evaluated on global ordered nodes -/

/-- Explicit error `E_{k+1}(t)` evaluated on the canonical `orderedNode k t`. -/
noncomputable def explicitErrorAt (k : ℕ) (t : ℝ) : ℝ :=
  explicitError (k + 1) (orderedNode k t) t

/-- Complement `H_{k+1}(t) = 1 - E_{k+1}(t)`. -/
noncomputable def HAt (k : ℕ) (t : ℝ) : ℝ :=
  1 - explicitErrorAt k t

/-- Explicit error `E_n(t)` indexed by order `n ≥ 1`. -/
noncomputable def explicitErrorCurve (n : ℕ) (t : ℝ) : ℝ :=
  if hn : 1 ≤ n then
    explicitError n (fun j => orderedNode (n - 1) t (Fin.cast (by omega) j)) t
  else 0

/-- Complement `H_n(t) = 1 - E_n(t)` indexed by order `n ≥ 1`. -/
noncomputable def HCurve (n : ℕ) (t : ℝ) : ℝ :=
  1 - explicitErrorCurve n t

@[simp]
theorem explicitErrorCurve_succ (k : ℕ) (t : ℝ) :
    explicitErrorCurve (k + 1) t = explicitErrorAt k t := by
  simp [explicitErrorCurve, explicitErrorAt]

@[simp]
theorem HCurve_succ (k : ℕ) (t : ℝ) :
    HCurve (k + 1) t = HAt k t := by
  simp [HCurve, HAt]

/-- Explicit derivative formula for `E_{k+1}(t)` at `|t| < 1`. -/
noncomputable def explicitErrorDerivAt (k : ℕ) (t : ℝ) : ℝ :=
  -1 + (2 : ℝ) ^ (k + 1) * (1 - t) ^ (k + 1) + (2 : ℝ) ^ (k + 2) *
    ∑ j : Fin (k + 2), (-1 : ℝ) ^ (k + 1 - j.val) *
      truncatedPower (k + 1) 0 (orderedNode k t j - t) *
      (2 * (1 - orderedNode k t j ^ 2) /
        SharpL1.speedDenominator (k + 1) t (orderedNode k t j) - 1)

/-- Explicit derivative formula for `E_n(t)` indexed by order `n ≥ 1`. -/
noncomputable def explicitErrorDerivCurve (n : ℕ) (t : ℝ) : ℝ :=
  if 1 ≤ n then explicitErrorDerivAt (n - 1) t else 0

@[simp]
theorem explicitErrorDerivCurve_succ (k : ℕ) (t : ℝ) :
    explicitErrorDerivCurve (k + 1) t = explicitErrorDerivAt k t := by
  simp [explicitErrorDerivCurve]

theorem hasDerivAt_explicitErrorAt (k : ℕ) {t : ℝ} (ht : |t| < 1) :
    HasDerivAt (explicitErrorAt k) (explicitErrorDerivAt k t) t := by
  have hfun : explicitErrorAt k = fun x => explicitError (k + 1) (fun j => orderedNode k x j) x := rfl
  rw [hfun]
  exact hasDerivAt_explicitError (k + 1) (Nat.succ_pos k) (fun j s => orderedNode k s j)
    (fun j => 2 * (1 - orderedNode k t j ^ 2) /
      SharpL1.speedDenominator (k + 1) t (orderedNode k t j))
    t (fun j => hasDerivAt_orderedNode k ht j)

theorem hasDerivAt_HAt (k : ℕ) {t : ℝ} (ht : |t| < 1) :
    HasDerivAt (HAt k) (-explicitErrorDerivAt k t) t := by
  have hfun : HAt k = fun x => 1 - explicitErrorAt k x := rfl
  rw [hfun]
  exact (hasDerivAt_explicitErrorAt k ht).const_sub 1

theorem hasDerivAt_explicitErrorCurve {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : |t| < 1) :
    HasDerivAt (explicitErrorCurve n) (explicitErrorDerivCurve n t) t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hfun : explicitErrorCurve (k + 1) = explicitErrorAt k :=
    funext (explicitErrorCurve_succ k)
  rw [hfun, explicitErrorDerivCurve_succ]
  exact hasDerivAt_explicitErrorAt k ht

theorem hasDerivAt_HCurve {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : |t| < 1) :
    HasDerivAt (HCurve n) (-explicitErrorDerivCurve n t) t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hfun : HCurve (k + 1) = HAt k := funext (HCurve_succ k)
  rw [hfun, explicitErrorDerivCurve_succ]
  exact hasDerivAt_HAt k ht

theorem continuous_explicitErrorAt (k : ℕ) : Continuous (explicitErrorAt k) := by
  have hfun : explicitErrorAt k = fun t =>
      1 - t - (2 : ℝ) ^ (k + 1) / ((k + 1 : ℕ) + 1 : ℝ) * (1 - t) ^ (k + 2) +
        (2 : ℝ) ^ (k + 2) / ((k + 1 : ℕ) + 1 : ℝ) *
          ∑ j : Fin (k + 2), (-1 : ℝ) ^ (k + 1 - j.val) *
            (max (orderedNode k t j - t) 0) ^ (k + 2) := by
    funext t
    simp [explicitErrorAt, explicitError]
  rw [hfun]
  have hc : ∀ j : Fin (k + 2), Continuous (fun t => orderedNode k t j) :=
    continuous_orderedNode k
  fun_prop

theorem continuous_HAt (k : ℕ) : Continuous (HAt k) :=
  continuous_const.sub (continuous_explicitErrorAt k)

theorem continuous_explicitErrorCurve (n : ℕ) : Continuous (explicitErrorCurve n) := by
  by_cases hn : 1 ≤ n
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    have hfun : explicitErrorCurve (k + 1) = explicitErrorAt k :=
      funext (explicitErrorCurve_succ k)
    rw [hfun]
    exact continuous_explicitErrorAt k
  · have h0 : n = 0 := by omega
    subst h0
    have hfun : explicitErrorCurve 0 = fun _ => 0 := by
      funext t
      simp [explicitErrorCurve]
    rw [hfun]
    exact continuous_const

theorem continuous_HCurve (n : ℕ) : Continuous (HCurve n) :=
  continuous_const.sub (continuous_explicitErrorCurve n)

theorem explicitErrorAt_one (k : ℕ) : explicitErrorAt k 1 = 0 := by
  simp only [explicitErrorAt, explicitError, sub_self]
  have hzero : ∀ j : Fin (k + 2), max (orderedNode k 1 j - 1) 0 = 0 := by
    intro j
    apply max_eq_right
    have hmem := orderedNode_mem_Icc_unit k ⟨by norm_num, le_rfl⟩ j
    linarith [hmem.2]
  simp [hzero, zero_pow (Nat.succ_ne_zero (k + 1))]

/-! ### Structural identity `dS` on the augmented node polynomial -/

private theorem monicNodePolynomial_splits (k : ℕ) (t : ℝ) :
    (monicNodePolynomial k t).Splits := by
  rw [monicNodePolynomial]
  exact (Polynomial.Splits.C _).mul (nodePolynomial_splits k t)

private theorem monicNodePolynomial_roots (k : ℕ) (t : ℝ) :
    (monicNodePolynomial k t).roots = Finset.univ.val.map (orderedNode k t) := by
  rw [monicNodePolynomial, Polynomial.roots_C_mul _ (by positivity)]
  have h1 : (List.ofFn (orderedNode k t) : Multiset ℝ) = (nodePolynomial k t).roots := by
    rw [orderedNode_ofFn]
    simp [Multiset.sort_eq]
  rw [← h1, ← Fin.univ_val_map]

private theorem monicNodePolynomial_eq_prod_aux (k : ℕ) (t : ℝ) :
    monicNodePolynomial k t = ∏ j : Fin (k + 2), (X - C (orderedNode k t j)) := by
  rw [(monicNodePolynomial_splits k t).eq_prod_roots_of_monic (monicNodePolynomial_monic k t),
    monicNodePolynomial_roots, Multiset.map_map]
  exact (Finset.prod_eq_multiset_prod Finset.univ (fun j => X - C (orderedNode k t j))).symm

private theorem card_fin_Ioi (k : ℕ) (j : Fin (k + 2)) :
    (Finset.univ.filter (fun i : Fin (k + 2) => j < i)).card = k + 1 - j.val := by
  rw [← Finset.card_range (k + 1 - j.val)]
  refine Finset.card_bij (fun (i : Fin (k + 2)) _ => i.val - j.val - 1) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [Finset.mem_range]
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    ext
    omega
  · intro m hm
    rw [Finset.mem_range] at hm
    refine ⟨⟨j.val + 1 + m, by omega⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [Fin.lt_def]
      dsimp
      omega
    · dsimp
      omega

private theorem derivative_monicNodePolynomial_eval_sign (k : ℕ) (t : ℝ) (j : Fin (k + 2)) :
    (derivative (monicNodePolynomial k t)).eval (orderedNode k t j) =
      (-1 : ℝ) ^ (k + 1 - j.val) *
        |(derivative (monicNodePolynomial k t)).eval (orderedNode k t j)| := by
  let u := orderedNode k t
  have hder : derivative (monicNodePolynomial k t) =
      ∑ i : Fin (k + 2), ∏ l ∈ Finset.univ.erase i, (X - C (u l)) := by
    rw [monicNodePolynomial_eq_prod_aux, Polynomial.derivative_prod_finset]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [u, derivative_sub, derivative_X, derivative_C]
  have heval : (derivative (monicNodePolynomial k t)).eval (u j) =
      ∏ l ∈ Finset.univ.erase j, (u j - u l) := by
    rw [hder, eval_finsetSum]
    rw [Finset.sum_eq_single j]
    · simp [eval_prod]
    · intro i _ hij
      have hjmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩
      rw [eval_prod, Finset.prod_eq_zero hjmem (by simp)]
    · intro hj
      exact (hj (Finset.mem_univ _)).elim
  have hsplit : (∏ l ∈ Finset.univ.erase j, (u j - u l)) =
      (∏ l ∈ (Finset.univ.erase j).filter (fun l => l < j), (u j - u l)) *
        (∏ l ∈ (Finset.univ.erase j).filter (fun l => ¬ l < j), (u j - u l)) :=
    (Finset.prod_filter_mul_prod_filter_not (Finset.univ.erase j) (fun l => l < j)
      (fun l => u j - u l)).symm
  have hfilt_gt : (Finset.univ.erase j).filter (fun l => ¬ l < j) =
      Finset.univ.filter (fun l : Fin (k + 2) => j < l) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
    rcases lt_trichotomy l j with h1 | rfl | h1
    · simp [h1, h1.ne, h1.asymm]
    · simp
    · simp [h1, h1.ne.symm, h1.asymm]
  have hleft_pos : 0 < ∏ l ∈ (Finset.univ.erase j).filter (fun l => l < j), (u j - u l) := by
    apply Finset.prod_pos
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_erase] at hl
    exact sub_pos.mpr (orderedNode_strictMono k t hl.2)
  have hright_neg : ∏ l ∈ Finset.univ.filter (fun l : Fin (k + 2) => j < l), (u j - u l) =
      (-1 : ℝ) ^ (k + 1 - j.val) *
        ∏ l ∈ Finset.univ.filter (fun l : Fin (k + 2) => j < l), (u l - u j) := by
    have hneg : ∏ l ∈ Finset.univ.filter (fun l : Fin (k + 2) => j < l), (u j - u l) =
        ∏ l ∈ Finset.univ.filter (fun l : Fin (k + 2) => j < l), (-(u l - u j)) :=
      Finset.prod_congr rfl fun l _ => by ring
    rw [hneg, Finset.prod_neg, card_fin_Ioi]
  have hright_pos : 0 < ∏ l ∈ Finset.univ.filter (fun l : Fin (k + 2) => j < l), (u l - u j) := by
    apply Finset.prod_pos
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    exact sub_pos.mpr (orderedNode_strictMono k t hl)
  let A : ℝ := (∏ l ∈ (Finset.univ.erase j).filter (fun l => l < j), (u j - u l)) *
    (∏ l ∈ Finset.univ.filter (fun l : Fin (k + 2) => j < l), (u l - u j))
  have hA_pos : 0 < A := mul_pos hleft_pos hright_pos
  have heqA : (derivative (monicNodePolynomial k t)).eval (u j) = (-1 : ℝ) ^ (k + 1 - j.val) * A := by
    rw [heval, hsplit, hfilt_gt, hright_neg]
    dsimp [A]
    ring
  rw [heqA, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hA_pos]

private theorem nodePolynomial_eval_one (k : ℕ) (t : ℝ) :
    (nodePolynomial k t).eval 1 = SharpL1.speedDenominator (k + 1) t 1 := by
  simp only [nodePolynomial, eval_add, eval_sub, eval_mul, eval_C,
    Polynomial.Chebyshev.U_eval_one, Int.cast_add, Int.cast_natCast, Int.cast_ofNat, Int.cast_one,
    SharpL1.speedDenominator]
  push_cast
  ring

private theorem U_eval_neg_one_nat (m : ℕ) :
    (U ℝ (m : ℤ)).eval (-1) = (-1 : ℝ) ^ m * ((m : ℝ) + 1) := by
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one => simp; norm_num
  | more m ih0 ih1 =>
    rw [show ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 by omega,
      Polynomial.Chebyshev.U_add_two]
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X, mul_neg, mul_one, ih0,
      show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by omega, ih1]
    push_cast
    simp only [pow_succ]
    ring

private theorem nodePolynomial_eval_neg_one (k : ℕ) (t : ℝ) :
    (nodePolynomial k t).eval (-1) = (-1 : ℝ) ^ k * SharpL1.speedDenominator (k + 1) t (-1) := by
  unfold nodePolynomial
  rw [show (k : ℤ) + 2 = ((k + 2 : ℕ) : ℤ) by omega,
    show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by omega]
  simp only [eval_add, eval_sub, eval_mul, eval_C, U_eval_neg_one_nat, SharpL1.speedDenominator]
  push_cast
  simp only [pow_succ]
  ring

private noncomputable def augmentedNodes (k : ℕ) (t : ℝ) : Finset ℝ :=
  insert (-1 : ℝ) (insert (1 : ℝ) (Finset.univ.image (orderedNode k t)))

private theorem augmentedNodes_card (k : ℕ) {t : ℝ} (ht : |t| < 1) :
    (augmentedNodes k t).card = k + 4 := by
  let u := orderedNode k t
  have hbd : ∀ j : Fin (k + 2), u j ∈ Set.Ioo (-1 : ℝ) 1 := fun j =>
    nodePolynomial_root_mem_Ioo k ht (orderedNode_eval_eq_zero k t j)
  have hpos1 : (1 : ℝ) ∉ Finset.univ.image u := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro j hj
    linarith [(hbd j).2]
  have hneg1 : (-1 : ℝ) ∉ insert (1 : ℝ) (Finset.univ.image u) := by
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, not_or, not_exists]
    refine ⟨by norm_num, fun j hj => ?_⟩
    linarith [(hbd j).1]
  rw [augmentedNodes, Finset.card_insert_of_notMem hneg1,
    Finset.card_insert_of_notMem hpos1,
    Finset.card_image_of_injective Finset.univ (orderedNode_strictMono k t).injective,
    Finset.card_fin]

private noncomputable def augmentedNodePoly (k : ℕ) (t : ℝ) : ℝ[X] :=
  (X ^ 2 - 1) * monicNodePolynomial k t

private theorem augmentedNodePoly_eq_prod (k : ℕ) {t : ℝ} (ht : |t| < 1) :
    augmentedNodePoly k t = ∏ w ∈ augmentedNodes k t, (X - C w) := by
  let u := orderedNode k t
  have hbd : ∀ j : Fin (k + 2), u j ∈ Set.Ioo (-1 : ℝ) 1 := fun j =>
    nodePolynomial_root_mem_Ioo k ht (orderedNode_eval_eq_zero k t j)
  have hpos1 : (1 : ℝ) ∉ Finset.univ.image u := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro j hj
    linarith [(hbd j).2]
  have hneg1 : (-1 : ℝ) ∉ insert (1 : ℝ) (Finset.univ.image u) := by
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, not_or, not_exists]
    refine ⟨by norm_num, fun j hj => ?_⟩
    linarith [(hbd j).1]
  rw [augmentedNodes, Finset.prod_insert hneg1, Finset.prod_insert hpos1,
    Finset.prod_image (fun a _ b _ hab => (orderedNode_strictMono k t).injective hab),
    ← monicNodePolynomial_eq_prod_aux, augmentedNodePoly]
  simp only [map_neg, map_one]
  ring

private theorem prod_augmentedNodes_erase (k : ℕ) {t : ℝ} (ht : |t| < 1)
    {z : ℝ} (hz : z ∈ augmentedNodes k t) :
    (∏ w ∈ (augmentedNodes k t).erase z, (z - w)) =
      (derivative (augmentedNodePoly k t)).eval z := by
  rw [augmentedNodePoly_eq_prod k ht, Polynomial.derivative_prod_finset, eval_finsetSum]
  rw [Finset.sum_eq_single z _ (fun h => (h hz).elim)]
  · simp [eval_prod]
  · intro y hy hyz
    have hzmem : z ∈ (augmentedNodes k t).erase y := Finset.mem_erase.mpr ⟨hyz.symm, hz⟩
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero, mul_one, eval_prod]
    exact Finset.prod_eq_zero hzmem (by simp)

private theorem derivative_augmentedNodePoly_eval_one (k : ℕ) (t : ℝ) :
    (derivative (augmentedNodePoly k t)).eval 1 =
      (1 / 2 : ℝ) ^ (k + 1) * SharpL1.speedDenominator (k + 1) t 1 := by
  rw [augmentedNodePoly, derivative_mul, eval_add, eval_mul, eval_mul]
  have hx : (X ^ 2 - 1 : ℝ[X]).eval 1 = 0 := by simp
  have hdx : (derivative (X ^ 2 - 1 : ℝ[X])).eval 1 = 2 := by
    simp [derivative_sub]
    norm_num
  rw [hx, hdx, zero_mul, add_zero, monicNodePolynomial, eval_mul, eval_C,
    nodePolynomial_eval_one]
  rw [show k + 2 = (k + 1) + 1 by omega, pow_add, pow_one]
  ring

private theorem derivative_augmentedNodePoly_eval_neg_one (k : ℕ) (t : ℝ) :
    (derivative (augmentedNodePoly k t)).eval (-1) =
      (-1 : ℝ) ^ (k + 1) * (1 / 2 : ℝ) ^ (k + 1) * SharpL1.speedDenominator (k + 1) t (-1) := by
  rw [augmentedNodePoly, derivative_mul, eval_add, eval_mul, eval_mul]
  have hx : (X ^ 2 - 1 : ℝ[X]).eval (-1) = 0 := by simp
  have hdx : (derivative (X ^ 2 - 1 : ℝ[X])).eval (-1) = -2 := by
    simp [derivative_sub]
    norm_num
  rw [hx, hdx, zero_mul, add_zero, monicNodePolynomial, eval_mul, eval_C,
    nodePolynomial_eval_neg_one]
  rw [show k + 2 = (k + 1) + 1 by omega, pow_add, pow_one, pow_add, pow_one]
  ring

private theorem derivative_augmentedNodePoly_eval_node (k : ℕ) {t : ℝ} (ht : |t| < 1)
    (j : Fin (k + 2)) :
    (derivative (augmentedNodePoly k t)).eval (orderedNode k t j) =
      -((-1 : ℝ) ^ (k + 1 - j.val) * (1 / 2 : ℝ) ^ (k + 2) *
        SharpL1.speedDenominator (k + 1) t (orderedNode k t j)) := by
  let u := orderedNode k t
  have hu_lt : |u j| < 1 := abs_lt.mpr (nodePolynomial_root_mem_Ioo k ht (orderedNode_eval_eq_zero k t j))
  have hroot : (monicNodePolynomial k t).eval (u j) = 0 := by
    dsimp [u]
    rw [monicNodePolynomial, eval_mul, eval_C, orderedNode_eval_eq_zero, mul_zero]
  have hderiv := hasDerivAt_orderedNode k ht j
  have hspeed := abs_deriv_monicNodePolynomial_mul_u'_eq k (fun s => orderedNode k s j) t _
    ht hu_lt hderiv (.of_forall fun s => orderedNode_eval_eq_zero k s j)
  have hL : 0 < SharpL1.speedDenominator (k + 1) t (u j) :=
    SharpL1.speedDenominator_pos (k + 1) ht hu_lt
  have h1u : 1 - u j ^ 2 ≠ 0 := by nlinarith [abs_lt.mp hu_lt]
  have hder_abs : |(derivative (monicNodePolynomial k t)).eval (u j)| =
      (1 / 2 : ℝ) ^ (k + 1) * SharpL1.speedDenominator (k + 1) t (u j) / (2 * (1 - u j ^ 2)) := by
    have hmul : |(derivative (monicNodePolynomial k t)).eval (u j)| *
        (2 * (1 - u j ^ 2) / SharpL1.speedDenominator (k + 1) t (u j)) = (1 / 2 : ℝ) ^ (k + 1) := hspeed
    field_simp [hL.ne', h1u] at hmul ⊢
    linarith
  rw [augmentedNodePoly, derivative_mul, eval_add, eval_mul, eval_mul, hroot, mul_zero, zero_add]
  have hx : (X ^ 2 - 1 : ℝ[X]).eval (u j) = -(1 - u j ^ 2) := by
    simp only [eval_sub, eval_pow, eval_X, eval_one]
    ring
  rw [hx, derivative_monicNodePolynomial_eval_sign, hder_abs,
    show (1 / 2 : ℝ) ^ (k + 2) = (1 / 2 : ℝ) ^ (k + 1) * (1 / 2 : ℝ) by rw [pow_succ]]
  field_simp [h1u]
  ring

/-- The structural identity `dS` for `speedDenominator (k + 1) t y * g y` on the augmented
nodes `{-1, u_0(t), ..., u_{k+1}(t), 1}`. -/
theorem barycentric_speedDenominator_mul (k : ℕ) {t : ℝ} (ht : |t| < 1) (g : ℝ → ℝ) :
    barycentricDividedDifferenceOn (augmentedNodes k t) id
        (fun y => SharpL1.speedDenominator (k + 1) t y * g y) =
      (2 : ℝ) ^ (k + 1) * g 1 - (-1 : ℝ) ^ (k + 2) * (2 : ℝ) ^ (k + 1) * g (-1) -
        (2 : ℝ) ^ (k + 2) * ∑ j : Fin (k + 2), (-1 : ℝ) ^ (k + 1 - j.val) * g (orderedNode k t j) := by
  let u := orderedNode k t
  have hbd : ∀ j : Fin (k + 2), u j ∈ Set.Ioo (-1 : ℝ) 1 := fun j =>
    nodePolynomial_root_mem_Ioo k ht (orderedNode_eval_eq_zero k t j)
  have hpos1 : (1 : ℝ) ∉ Finset.univ.image u := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro j hj
    linarith [(hbd j).2]
  have hneg1 : (-1 : ℝ) ∉ insert (1 : ℝ) (Finset.univ.image u) := by
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, not_or, not_exists]
    refine ⟨by norm_num, fun j hj => ?_⟩
    linarith [(hbd j).1]
  unfold barycentricDividedDifferenceOn
  simp only [id_eq]
  have hsplit1 :
      ∑ i ∈ augmentedNodes k t,
          (SharpL1.speedDenominator (k + 1) t i * g i) *
            (∏ j ∈ (augmentedNodes k t).erase i, (i - j))⁻¹ =
        (SharpL1.speedDenominator (k + 1) t (-1) * g (-1)) *
            (∏ j ∈ (augmentedNodes k t).erase (-1), (-1 - j))⁻¹ +
          (SharpL1.speedDenominator (k + 1) t 1 * g 1) *
            (∏ j ∈ (augmentedNodes k t).erase 1, (1 - j))⁻¹ +
          ∑ j : Fin (k + 2),
            (SharpL1.speedDenominator (k + 1) t (u j) * g (u j)) *
              (∏ l ∈ (augmentedNodes k t).erase (u j), (u j - l))⁻¹ := by
    rw [augmentedNodes, Finset.sum_insert hneg1, Finset.sum_insert hpos1,
      Finset.sum_image (fun a _ b _ hab => (orderedNode_strictMono k t).injective hab)]
    ring
  rw [hsplit1]
  have hmem_neg1 : (-1 : ℝ) ∈ augmentedNodes k t := by simp [augmentedNodes]
  have hmem_pos1 : (1 : ℝ) ∈ augmentedNodes k t := by simp [augmentedNodes]
  have hmem_u (j : Fin (k + 2)) : u j ∈ augmentedNodes k t := by
    simp only [augmentedNodes, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr (Or.inr ⟨j, rfl⟩)
  rw [prod_augmentedNodes_erase k ht hmem_neg1,
    prod_augmentedNodes_erase k ht hmem_pos1,
    derivative_augmentedNodePoly_eval_neg_one,
    derivative_augmentedNodePoly_eval_one]
  have hsum_eq :
      ∑ j : Fin (k + 2),
          (SharpL1.speedDenominator (k + 1) t (u j) * g (u j)) *
            (∏ l ∈ (augmentedNodes k t).erase (u j), (u j - l))⁻¹ =
        - ((2 : ℝ) ^ (k + 2) * ∑ j : Fin (k + 2), (-1 : ℝ) ^ (k + 1 - j.val) * g (u j)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [prod_augmentedNodes_erase k ht (hmem_u j), derivative_augmentedNodePoly_eval_node k ht j]
    have hL : SharpL1.speedDenominator (k + 1) t (u j) ≠ 0 :=
      (SharpL1.speedDenominator_pos (k + 1) ht (abs_lt.mpr (hbd j))).ne'
    have hpow : (1 / 2 : ℝ) ^ (k + 2) * (2 : ℝ) ^ (k + 2) = 1 := by
      rw [← mul_pow]; norm_num
    have hinv_sgn : ((-1 : ℝ) ^ (k + 1 - j.val))⁻¹ = (-1 : ℝ) ^ (k + 1 - j.val) := by
      rw [← inv_pow, inv_neg, inv_one]
    have hinv_pow : ((1 / 2 : ℝ) ^ (k + 2))⁻¹ = (2 : ℝ) ^ (k + 2) := by
      rw [← inv_pow, one_div, inv_inv]
    rw [inv_neg, mul_inv, mul_inv, hinv_sgn, hinv_pow]
    change SharpL1.speedDenominator (k + 1) t (u j) * g (u j) *
        -(((-1 : ℝ) ^ (k + 1 - j.val) * (2 : ℝ) ^ (k + 2)) *
          (SharpL1.speedDenominator (k + 1) t (u j))⁻¹) =
      -((2 : ℝ) ^ (k + 2) * ((-1 : ℝ) ^ (k + 1 - j.val) * g (u j)))
    calc
      SharpL1.speedDenominator (k + 1) t (u j) * g (u j) *
          -(((-1 : ℝ) ^ (k + 1 - j.val) * (2 : ℝ) ^ (k + 2)) *
            (SharpL1.speedDenominator (k + 1) t (u j))⁻¹)
        = -(SharpL1.speedDenominator (k + 1) t (u j) *
            (SharpL1.speedDenominator (k + 1) t (u j))⁻¹) *
            ((2 : ℝ) ^ (k + 2) * ((-1 : ℝ) ^ (k + 1 - j.val) * g (u j))) := by ring
      _ = -((2 : ℝ) ^ (k + 2) * ((-1 : ℝ) ^ (k + 1 - j.val) * g (u j))) := by
            rw [mul_inv_cancel₀ hL, neg_mul, one_mul]
  rw [hsum_eq]
  have hL1 : SharpL1.speedDenominator (k + 1) t 1 ≠ 0 :=
    (SharpL1.speedDenominator_pos_of_abs_lt_one_left (k + 1) ht (by norm_num)).ne'
  have hLm1 : SharpL1.speedDenominator (k + 1) t (-1) ≠ 0 :=
    (SharpL1.speedDenominator_pos_of_abs_lt_one_left (k + 1) ht (by norm_num)).ne'
  have hinv_pow1 : ((1 / 2 : ℝ) ^ (k + 1))⁻¹ = (2 : ℝ) ^ (k + 1) := by
    rw [← inv_pow, one_div, inv_inv]
  have hinv_sgn1 : ((-1 : ℝ) ^ (k + 1))⁻¹ = (-1 : ℝ) ^ (k + 1) := by
    rw [← inv_pow, inv_neg, inv_one]
  have hterm1 : (SharpL1.speedDenominator (k + 1) t 1 * g 1) *
      ((1 / 2 : ℝ) ^ (k + 1) * SharpL1.speedDenominator (k + 1) t 1)⁻¹ =
      (2 : ℝ) ^ (k + 1) * g 1 := by
    rw [mul_inv, hinv_pow1]
    field_simp [hL1]
  have hterm_m1 : (SharpL1.speedDenominator (k + 1) t (-1) * g (-1)) *
      ((-1 : ℝ) ^ (k + 1) * (1 / 2 : ℝ) ^ (k + 1) *
        SharpL1.speedDenominator (k + 1) t (-1))⁻¹ =
      -((-1 : ℝ) ^ (k + 2) * (2 : ℝ) ^ (k + 1) * g (-1)) := by
    rw [mul_inv, mul_inv, hinv_sgn1, hinv_pow1, show k + 2 = (k + 1) + 1 by omega, pow_succ]
    calc
      SharpL1.speedDenominator (k + 1) t (-1) * g (-1) *
          ((-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (k + 1) * (SharpL1.speedDenominator (k + 1) t (-1))⁻¹)
        = (SharpL1.speedDenominator (k + 1) t (-1) * (SharpL1.speedDenominator (k + 1) t (-1))⁻¹) *
            ((-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (k + 1) * g (-1)) := by ring
      _ = -((-1 : ℝ) ^ (k + 1) * (-1 : ℝ) * (2 : ℝ) ^ (k + 1) * g (-1)) := by
            rw [mul_inv_cancel₀ hLm1, one_mul]; ring
  rw [hterm1, hterm_m1]
  ring

/-- The barycentric identity for `2 * (1 - y ^ 2) * g y` on the augmented nodes. -/
theorem barycentric_two_mul_one_sub_sq_mul (k : ℕ) {t : ℝ} (ht : |t| < 1) (g : ℝ → ℝ) :
    barycentricDividedDifferenceOn (augmentedNodes k t) id
        (fun y => 2 * (1 - y ^ 2) * g y) =
      -(2 : ℝ) ^ (k + 2) * ∑ j : Fin (k + 2), (-1 : ℝ) ^ (k + 1 - j.val) *
        (2 * (1 - orderedNode k t j ^ 2) /
          SharpL1.speedDenominator (k + 1) t (orderedNode k t j)) * g (orderedNode k t j) := by
  let u := orderedNode k t
  have hbd : ∀ j : Fin (k + 2), u j ∈ Set.Ioo (-1 : ℝ) 1 := fun j =>
    nodePolynomial_root_mem_Ioo k ht (orderedNode_eval_eq_zero k t j)
  have hpos1 : (1 : ℝ) ∉ Finset.univ.image u := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro j hj
    linarith [(hbd j).2]
  have hneg1 : (-1 : ℝ) ∉ insert (1 : ℝ) (Finset.univ.image u) := by
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, not_or, not_exists]
    refine ⟨by norm_num, fun j hj => ?_⟩
    linarith [(hbd j).1]
  unfold barycentricDividedDifferenceOn
  simp only [id_eq]
  rw [augmentedNodes, Finset.sum_insert hneg1, Finset.sum_insert hpos1,
    Finset.sum_image (fun a _ b _ hab => (orderedNode_strictMono k t).injective hab),
    ← augmentedNodes]
  norm_num
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hmem_u : u j ∈ augmentedNodes k t := by
    simp only [augmentedNodes, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr (Or.inr ⟨j, rfl⟩)
  rw [prod_augmentedNodes_erase k ht hmem_u, derivative_augmentedNodePoly_eval_node k ht j]
  have hL : SharpL1.speedDenominator (k + 1) t (u j) ≠ 0 :=
    (SharpL1.speedDenominator_pos (k + 1) ht (abs_lt.mpr (hbd j))).ne'
  have hinv_sgn : ((-1 : ℝ) ^ (k + 1 - j.val))⁻¹ = (-1 : ℝ) ^ (k + 1 - j.val) := by
    rw [← inv_pow, inv_neg, inv_one]
  have hinv_pow : ((1 / 2 : ℝ) ^ (k + 2))⁻¹ = (2 : ℝ) ^ (k + 2) := by
    rw [← inv_pow, one_div, inv_inv]
  rw [inv_neg, mul_inv, mul_inv, hinv_sgn, hinv_pow]
  rw [div_eq_mul_inv]
  ring

/-! ### Evenness, left endpoint, and center value (eq. (6)) -/

private theorem max_neg_pow_add (m : ℕ) (hm : m ≠ 0) (x : ℝ) :
    (max (-x) 0) ^ m + (-1 : ℝ) ^ m * (max x 0) ^ m = (-1 : ℝ) ^ m * x ^ m := by
  rcases le_or_gt 0 x with hx | hx
  · have hnx : -x ≤ 0 := by linarith
    simp [max_eq_right hnx, max_eq_left hx, zero_pow hm]
  · have hnx : 0 ≤ -x := by linarith
    have hneg : -x = (-1 : ℝ) * x := by ring
    rw [max_eq_left hnx, max_eq_right hx.le, zero_pow hm, hneg, mul_pow]
    ring

private theorem explicitError_full_poly_sum (k : ℕ) {t : ℝ} (ht : |t| < 1) :
    (2 : ℝ) ^ (k + 2) / ((k + 1 : ℕ) + 1 : ℝ) *
        ∑ j : Fin (k + 2), (-1 : ℝ) ^ (k + 1 - j.val) * (orderedNode k t j - t) ^ (k + 2) =
      2 * t + (2 : ℝ) ^ (k + 1) / ((k + 1 : ℕ) + 1 : ℝ) *
        ((1 - t) ^ (k + 2) - (1 + t) ^ (k + 2)) := by
  let P : ℝ[X] :=
    (C ((k + 3 : ℝ) + (k + 1 : ℝ) * t ^ 2) - C (2 * (k + 2 : ℝ) * t) * X) *
      (X - C t) ^ (k + 2)
  have hdeg : P.degree < ((augmentedNodes k t).card : WithBot ℕ) := by
    rw [augmentedNodes_card k ht]
    have h1 : (C ((k + 3 : ℝ) + (k + 1 : ℝ) * t ^ 2) - C (2 * (k + 2 : ℝ) * t) * X).degree ≤ 1 := by
      refine (degree_sub_le _ _).trans (max_le (degree_C_le.trans (by norm_num)) ?_)
      exact (degree_C_mul_X_le _).trans (by norm_num)
    have h2 : ((X - C t) ^ (k + 2)).degree ≤ ((k + 2 : ℕ) : WithBot ℕ) := by
      have hnat : ((X - C t) ^ (k + 2)).natDegree = k + 2 := by simp
      calc
        ((X - C t) ^ (k + 2)).degree ≤ (((X - C t) ^ (k + 2)).natDegree : WithBot ℕ) :=
          degree_le_natDegree
        _ = ((k + 2 : ℕ) : WithBot ℕ) := by rw [hnat]
    calc
      P.degree ≤ (C ((k + 3 : ℝ) + (k + 1 : ℝ) * t ^ 2) - C (2 * (k + 2 : ℝ) * t) * X).degree +
          ((X - C t) ^ (k + 2)).degree := degree_mul_le _ _
      _ ≤ 1 + ((k + 2 : ℕ) : WithBot ℕ) := add_le_add h1 h2
      _ < ((k + 4 : ℕ) : WithBot ℕ) := by norm_cast; omega
  have hcoeff : P.coeff ((augmentedNodes k t).card - 1) = -2 * (k + 2 : ℝ) * t := by
    rw [augmentedNodes_card k ht, show k + 4 - 1 = k + 3 by omega]
    have hmonic : ((X - C t) ^ (k + 2)).Monic := (monic_X_sub_C t).pow (k + 2)
    have hnat : ((X - C t) ^ (k + 2)).natDegree = k + 2 := by simp
    have hsub : (C ((k + 3 : ℝ) + (k + 1 : ℝ) * t ^ 2) * (X - C t) ^ (k + 2)).coeff (k + 3) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      calc
        (C ((k + 3 : ℝ) + (k + 1 : ℝ) * t ^ 2) * (X - C t) ^ (k + 2)).natDegree ≤
            ((X - C t) ^ (k + 2)).natDegree := natDegree_C_mul_le _ _
        _ = k + 2 := hnat
        _ < k + 3 := by omega
    have hexp : P = C ((k + 3 : ℝ) + (k + 1 : ℝ) * t ^ 2) * (X - C t) ^ (k + 2) -
        C (2 * (k + 2 : ℝ) * t) * (X * (X - C t) ^ (k + 2)) := by
      dsimp [P]; ring
    have hcoeff_pow : ((X - C t) ^ (k + 2)).coeff (k + 2) = 1 := by
      nth_rw 2 [← hnat]
      exact hmonic.coeff_natDegree
    rw [hexp, coeff_sub, hsub, zero_sub, coeff_C_mul, coeff_X_mul, hcoeff_pow]
    ring
  have heval (y : ℝ) : P.eval y = SharpL1.speedDenominator (k + 1) t y * (y - t) ^ (k + 2) := by
    simp only [P, eval_mul, eval_sub, eval_C, eval_X, eval_pow, SharpL1.speedDenominator]
    push_cast
    ring
  have hinj : Set.InjOn id (augmentedNodes k t : Set ℝ) := fun _ _ _ _ h => h
  have hdd := barycentricDividedDifferenceOn_eval_eq_coeff hinj P hdeg
  rw [hcoeff] at hdd
  have hdd' : barycentricDividedDifferenceOn (augmentedNodes k t) id
      (fun y => SharpL1.speedDenominator (k + 1) t y * (y - t) ^ (k + 2)) =
      -2 * (k + 2 : ℝ) * t := by
    simpa only [id_eq, heval] using hdd
  rw [barycentric_speedDenominator_mul k ht (fun y => (y - t) ^ (k + 2))] at hdd'
  have hm1 : (-1 : ℝ) ^ (k + 2) * (2 : ℝ) ^ (k + 1) * (-1 - t) ^ (k + 2) =
      (2 : ℝ) ^ (k + 1) * (1 + t) ^ (k + 2) := by
    rw [mul_right_comm, ← mul_pow]
    ring_nf
  rw [hm1] at hdd'
  have hk2 : ((k + 1 : ℕ) + 1 : ℝ) = (k : ℝ) + 2 := by push_cast; ring
  have hk2_ne : (k : ℝ) + 2 ≠ 0 := by positivity
  rw [hk2]
  have heq : (2 : ℝ) ^ (k + 2) * ∑ j : Fin (k + 2), (-1 : ℝ) ^ (k + 1 - j.val) * (orderedNode k t j - t) ^ (k + 2) =
      2 * ((k : ℝ) + 2) * t + (2 : ℝ) ^ (k + 1) * ((1 - t) ^ (k + 2) - (1 + t) ^ (k + 2)) := by
    linear_combination -hdd'
  rw [div_mul_eq_mul_div, heq]
  field_simp [hk2_ne]

theorem explicitErrorAt_neg_of_Ioo (k : ℕ) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    explicitErrorAt k (-t) = explicitErrorAt k t := by
  have ht_abs : |t| < 1 := abs_lt.mpr ht
  have hfull := explicitError_full_poly_sum k ht_abs
  have hsum_neg :
      ∑ j : Fin (k + 2), (-1 : ℝ) ^ (k + 1 - j.val) * (max (orderedNode k (-t) j - (-t)) 0) ^ (k + 2) =
        ∑ j : Fin (k + 2), (-1 : ℝ) ^ (k + 1 - j.val) * (max (orderedNode k t j - t) 0) ^ (k + 2) -
          ∑ j : Fin (k + 2), (-1 : ℝ) ^ (k + 1 - j.val) * (orderedNode k t j - t) ^ (k + 2) := by
    rw [← Equiv.sum_comp Fin.revPerm]
    simp only [Fin.revPerm_apply, orderedNode_neg, Fin.rev_rev]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hexp : k + 1 - (j.rev).val = j.val := by simp [Fin.val_rev]; omega
    rw [hexp, show -orderedNode k t j - -t = -(orderedNode k t j - t) by ring]
    have hmax := max_neg_pow_add (k + 2) (Nat.succ_ne_zero (k + 1)) (orderedNode k t j - t)
    have hpow : (-1 : ℝ) ^ j.val * (-1 : ℝ) ^ (k + 2) = -((-1 : ℝ) ^ (k + 1 - j.val)) := by
      have hjle : j.val ≤ k + 1 := by omega
      calc
        (-1 : ℝ) ^ j.val * (-1 : ℝ) ^ (k + 2)
          = (-1 : ℝ) ^ (j.val + (k + 2)) := (pow_add _ _ _).symm
        _ = (-1 : ℝ) ^ (2 * j.val + 1 + (k + 1 - j.val)) := by
              congr 1
              omega
        _ = ((-1 : ℝ) ^ 2) ^ j.val * (-1 : ℝ) * (-1 : ℝ) ^ (k + 1 - j.val) := by
              rw [pow_add, pow_add, pow_mul, pow_one]
        _ = -((-1 : ℝ) ^ (k + 1 - j.val)) := by norm_num
    calc
      (-1 : ℝ) ^ j.val * (max (-(orderedNode k t j - t)) 0) ^ (k + 2)
        = (-1 : ℝ) ^ j.val * ((-1 : ℝ) ^ (k + 2) * (orderedNode k t j - t) ^ (k + 2) -
            (-1 : ℝ) ^ (k + 2) * (max (orderedNode k t j - t) 0) ^ (k + 2)) := by
          congr 1; linarith
      _ = (-1 : ℝ) ^ j.val * (-1 : ℝ) ^ (k + 2) *
            ((orderedNode k t j - t) ^ (k + 2) - (max (orderedNode k t j - t) 0) ^ (k + 2)) := by
          ring
      _ = -((-1 : ℝ) ^ (k + 1 - j.val)) *
            ((orderedNode k t j - t) ^ (k + 2) - (max (orderedNode k t j - t) 0) ^ (k + 2)) := by
          rw [hpow]
      _ = (-1 : ℝ) ^ (k + 1 - j.val) * (max (orderedNode k t j - t) 0) ^ (k + 2) -
            (-1 : ℝ) ^ (k + 1 - j.val) * (orderedNode k t j - t) ^ (k + 2) := by ring
  unfold explicitErrorAt explicitError
  rw [hsum_neg, mul_sub, sub_neg_eq_add]
  have hpow2 : (2 : ℝ) ^ (k + 1 + 1) = (2 : ℝ) ^ (k + 2) := rfl
  have hsum_cast :
      (∑ j : Fin (k + 2), (-1 : ℝ) ^ (k + 1 - j.val) * (max (orderedNode k t j - t) 0) ^ (k + 1 + 1)) =
        ∑ j : Fin (k + 2), (-1 : ℝ) ^ (k + 1 - j.val) * (max (orderedNode k t j - t) 0) ^ (k + 2) := rfl
  have h1p : (1 + t) ^ (k + 1 + 1) = (1 + t) ^ (k + 2) := rfl
  have h1m : (1 - t) ^ (k + 1 + 1) = (1 - t) ^ (k + 2) := rfl
  rw [hpow2, hsum_cast, h1p, h1m]
  linarith

/-- Evenness of `explicitErrorAt k` on `[-1, 1]` (extended from `(-1, 1)` by continuity). -/
theorem explicitErrorAt_neg (k : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    explicitErrorAt k (-t) = explicitErrorAt k t := by
  have heq : Set.EqOn (fun s => explicitErrorAt k (-s)) (explicitErrorAt k) (Set.Ioo (-1 : ℝ) 1) :=
    fun s hs => explicitErrorAt_neg_of_Ioo k hs
  have hcl := heq.closure ((continuous_explicitErrorAt k).comp continuous_neg)
    (continuous_explicitErrorAt k)
  rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)] at hcl
  exact hcl ht

theorem explicitErrorAt_neg_one (k : ℕ) : explicitErrorAt k (-1) = 0 := by
  have h := explicitErrorAt_neg k ⟨by norm_num, le_rfl⟩
  simpa [explicitErrorAt_one] using h

theorem explicitErrorCurve_neg {n : ℕ} {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    explicitErrorCurve n (-t) = explicitErrorCurve n t := by
  by_cases hn : 1 ≤ n
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    simpa [explicitErrorCurve_succ] using explicitErrorAt_neg k ht
  · have h0 : n = 0 := by omega
    subst h0
    simp [explicitErrorCurve]

theorem HCurve_neg {n : ℕ} {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    HCurve n (-t) = HCurve n t := by
  simp [HCurve, explicitErrorCurve_neg ht]

theorem explicitErrorCurve_one {n : ℕ} : explicitErrorCurve n 1 = 0 := by
  by_cases hn : 1 ≤ n
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    simpa [explicitErrorCurve_succ] using explicitErrorAt_one k
  · have h0 : n = 0 := by omega
    subst h0
    simp [explicitErrorCurve]

theorem explicitErrorCurve_neg_one {n : ℕ} : explicitErrorCurve n (-1) = 0 := by
  rw [explicitErrorCurve_neg ⟨by norm_num, le_rfl⟩, explicitErrorCurve_one]

/-- Exact center value `E_{k+1}(0)` matching eq. (6) of `chebyshev_L1_complete.tex`. -/
theorem explicitErrorAt_zero (k : ℕ) :
    explicitErrorAt k 0 =
      1 - (2 : ℝ) ^ (k + 1) / ((k : ℝ) + 2) +
        (2 : ℝ) ^ (k + 2) / ((k : ℝ) + 2) *
          ∑ m ∈ Finset.Icc 1 ((k + 2) / 2),
            (-1 : ℝ) ^ (m - 1) * (Real.cos ((m : ℝ) * Real.pi / ((k : ℝ) + 3))) ^ (k + 2) := by
  unfold explicitErrorAt explicitError
  simp only [sub_zero, one_pow, mul_one]
  rw [show ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 by push_cast; ring]
  congr 2
  rw [← Equiv.sum_comp Fin.revPerm]
  have hsum1 :
      ∑ j : Fin (k + 2), (-1 : ℝ) ^ (k + 1 - (Fin.revPerm j).val) *
          (max (orderedNode k 0 (Fin.revPerm j)) 0) ^ (k + 2) =
        ∑ m ∈ Finset.Icc 1 (k + 2), (-1 : ℝ) ^ (m - 1) *
          (max (Real.cos ((m : ℝ) * Real.pi / ((k : ℝ) + 3))) 0) ^ (k + 2) := by
    refine Finset.sum_bij (fun j _ => j.val + 1) ?_ ?_ ?_ ?_
    · intro j _
      rw [Finset.mem_Icc]
      omega
    · intro a _ b _ hab
      ext
      omega
    · intro m hm
      rw [Finset.mem_Icc] at hm
      refine ⟨⟨m - 1, by omega⟩, Finset.mem_univ _, ?_⟩
      dsimp
      omega
    · intro j _
      simp only [Fin.revPerm_apply, orderedNode_zero]
      have hrev : (j.rev).val = k + 1 - j.val := by rw [Fin.val_rev]; omega
      have hexp : k + 1 - (j.rev).val = j.val := by omega
      have hcast : (((j.rev).val : ℝ) + 1) = (k : ℝ) + 3 - ((j.val : ℝ) + 1) := by
        rw [hrev, Nat.cast_sub (by omega : j.val ≤ k + 1)]
        push_cast
        ring
      have hk3 : (k : ℝ) + 3 ≠ 0 := by positivity
      rw [hexp, Nat.add_sub_cancel, hcast, sub_mul, sub_div, mul_div_cancel_left₀ _ hk3,
        Real.cos_pi_sub, neg_neg]
      push_cast
      rfl
  rw [hsum1]
  have hsub : Finset.Icc 1 ((k + 2) / 2) ⊆ Finset.Icc 1 (k + 2) := by
    intro m hm
    rw [Finset.mem_Icc] at hm ⊢
    omega
  rw [← Finset.sum_sdiff hsub]
  have hzero : ∑ m ∈ Finset.Icc 1 (k + 2) \ Finset.Icc 1 ((k + 2) / 2),
      (-1 : ℝ) ^ (m - 1) * (max (Real.cos ((m : ℝ) * Real.pi / ((k : ℝ) + 3))) 0) ^ (k + 2) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    simp only [Finset.mem_sdiff, Finset.mem_Icc, not_and, not_le] at hm
    have hm1 : (k + 2) / 2 < m := hm.2 hm.1.1
    have hpi2 : Real.pi / 2 ≤ (m : ℝ) * Real.pi / ((k : ℝ) + 3) := by
      have hk3 : (0 : ℝ) < (k : ℝ) + 3 := by positivity
      rw [div_le_div_iff₀ (by norm_num) hk3]
      have hm2 : k + 3 ≤ 2 * m := by omega
      have hm2' : (k : ℝ) + 3 ≤ 2 * (m : ℝ) := by exact_mod_cast hm2
      nlinarith [Real.pi_pos]
    have hpi : (m : ℝ) * Real.pi / ((k : ℝ) + 3) ≤ Real.pi := by
      have hk3 : (0 : ℝ) < (k : ℝ) + 3 := by positivity
      rw [div_le_iff₀ hk3]
      have hm_le : (m : ℝ) ≤ (k : ℝ) + 3 := by exact_mod_cast (by omega : m ≤ k + 3)
      nlinarith [Real.pi_pos]
    have hcos_le : Real.cos ((m : ℝ) * Real.pi / ((k : ℝ) + 3)) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hpi2 (hpi.trans (by linarith [Real.pi_pos]))
    rw [max_eq_right hcos_le, zero_pow (Nat.succ_ne_zero (k + 1)), mul_zero]
  rw [hzero, zero_add]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_Icc] at hm
  have hnonneg : 0 ≤ (m : ℝ) * Real.pi / ((k : ℝ) + 3) := by positivity
  have hpi2 : (m : ℝ) * Real.pi / ((k : ℝ) + 3) ≤ Real.pi / 2 := by
    have hk3 : (0 : ℝ) < (k : ℝ) + 3 := by positivity
    rw [div_le_div_iff₀ hk3 (by norm_num)]
    have hm2 : 2 * m ≤ k + 2 := by omega
    have hm2' : 2 * (m : ℝ) ≤ (k : ℝ) + 2 := by exact_mod_cast hm2
    nlinarith [Real.pi_pos]
  have hcos_nn : 0 ≤ Real.cos ((m : ℝ) * Real.pi / ((k : ℝ) + 3)) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hpi2⟩
  rw [max_eq_left hcos_nn]

theorem explicitErrorCurve_zero {n : ℕ} (hn : 1 ≤ n) :
    explicitErrorCurve n 0 =
      1 - (2 : ℝ) ^ n / ((n : ℝ) + 1) +
        (2 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) *
          ∑ m ∈ Finset.Icc 1 ((n + 1) / 2),
            (-1 : ℝ) ^ (m - 1) * (Real.cos ((m : ℝ) * Real.pi / ((n : ℝ) + 2))) ^ (n + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [show k.succ = k + 1 from rfl, explicitErrorCurve_succ, explicitErrorAt_zero k]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring,
    show (k : ℝ) + 1 + 2 = (k : ℝ) + 3 by ring,
    show k + 1 + 1 = k + 2 by rfl]

/-! ### Exterior monotonicity `E_n'(t) < 0` on `[1/2, 1)` (Claim 3) -/

private theorem foldl_sub_eq_sum (m : ℕ) (w : Fin m → ℝ) :
    (List.ofFn w).foldl (fun acc x => x - acc) 0 =
      ∑ j : Fin m, (-1 : ℝ) ^ (m - 1 - j.val) * w j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih (fun j : Fin m => w j.castSucc)]
    rw [Fin.sum_univ_castSucc]
    have hlast : (-1 : ℝ) ^ (m + 1 - 1 - (Fin.last m).val) * w (Fin.last m) = w (Fin.last m) := by
      simp only [Fin.val_last, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    rw [hlast, sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fin.val_castSucc]
    have hj : j.val ≤ m - 1 := by omega
    have hexp : m + 1 - 1 - j.val = (m - 1 - j.val) + 1 := by omega
    rw [hexp, pow_succ]
    ring

private theorem explicitErrorDerivAt_eq_exterior (k : ℕ) {t : ℝ} (_ht0 : 0 ≤ t) (_ht1 : t < 1) :
    explicitErrorDerivAt k t =
      -1 + (2 * (1 - t)) ^ (k + 1) -
        (2 : ℝ) ^ (k + 2) *
          ((List.ofFn (fun j : Fin (k + 2) =>
            exteriorWeight (k + 1) t (orderedNode k t j))).foldl
              (fun acc x => x - acc) 0) := by
  rw [foldl_sub_eq_sum]
  unfold explicitErrorDerivAt
  rw [mul_pow]
  have hsum :
      ∑ j : Fin (k + 2), (-1 : ℝ) ^ (k + 1 - j.val) *
          truncatedPower (k + 1) 0 (orderedNode k t j - t) *
          (2 * (1 - orderedNode k t j ^ 2) /
            SharpL1.speedDenominator (k + 1) t (orderedNode k t j) - 1) =
        - ∑ j : Fin (k + 2), (-1 : ℝ) ^ (k + 1 - j.val) *
            exteriorWeight (k + 1) t (orderedNode k t j) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [truncatedPower_sub_eq]
    by_cases hlt : orderedNode k t j < t
    · simp [truncatedPower, hlt.not_ge, exteriorWeight, hlt]
    · have hle : t ≤ orderedNode k t j := le_of_not_gt hlt
      simp only [truncatedPower, hle, ↓reduceIte, exteriorWeight, hlt]
      change (-1 : ℝ) ^ (k + 1 - j.val) * (orderedNode k t j - t) ^ (k + 1) *
          (speedFactor (k + 1) t (orderedNode k t j) - 1) = _
      ring
  rw [hsum]
  simp only [show k + 1 + 1 - 1 = k + 1 by omega]
  ring

theorem explicitErrorDerivAt_neg_of_Ico_half_one (k : ℕ) {t : ℝ}
    (ht0 : 1 / 2 ≤ t) (ht1 : t < 1) :
    explicitErrorDerivAt k t < 0 := by
  have ht_pos : 0 < t := by linarith
  have ht_abs : |t| < 1 := abs_lt.mpr ⟨by linarith, ht1⟩
  rw [explicitErrorDerivAt_eq_exterior k ht_pos.le ht1]
  have hord : (List.ofFn (orderedNode k t)).Pairwise (· ≤ ·) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_ofFn]
    exact (orderedNode_strictMono k t (Fin.mk_lt_mk.mpr hij)).le
  have hbd : ∀ y ∈ List.ofFn (orderedNode k t), y ∈ Set.Icc (-1 : ℝ) 1 := by
    intro y hy
    rcases List.mem_ofFn.mp hy with ⟨j, rfl⟩
    exact orderedNode_mem_Icc_unit k ⟨by linarith, ht1.le⟩ j
  have halt := exteriorWeight_alternating_nonneg (k + 1) (Nat.succ_pos k) ht_pos ht1
    (List.ofFn (orderedNode k t)) hord hbd
  rw [List.map_ofFn] at halt
  rcases lt_or_eq_of_le ht0 with hgt | rfl
  · exact exterior_derivative_neg (Nat.succ_ne_zero k) hgt ht1 halt
  · -- Boundary `t = 1/2`: `-1 + (2 * (1 - 1/2))^(k+1) = 0`, so we need `0 < alt`
    have hpow : -1 + (2 * (1 - (1 / 2 : ℝ))) ^ (k + 1) = 0 := by norm_num
    rw [hpow, zero_sub]
    suffices hpos : 0 < (List.ofFn (fun j : Fin (k + 2) =>
        exteriorWeight (k + 1) (1 / 2) (orderedNode k (1 / 2) j))).foldl
        (fun acc x => x - acc) 0 by
      have h2 : (0 : ℝ) < (2 : ℝ) ^ (k + 2) := by positivity
      linarith [mul_pos h2 hpos]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · -- `k = 0` (`n = 1`): direct computation using `nodes₁ (1/2)`
      have hnodes := orderedNode_eq_of_strictMono_of_roots 0 (1 / 2) (nodes₁ (1 / 2))
        (nodes₁_strictMono (1 / 2)) (nodePolynomial_zero_roots (1 / 2))
      rw [hnodes]
      norm_num [List.ofFn_succ, nodes₁, exteriorWeight, speedFactor, speedDenominator]
    · -- `1 ≤ k` (`n ≥ 2`): split off the top pair `u_k(1/2), u_{k+1}(1/2)`
      let w : Fin (k + 2) → ℝ := fun j => exteriorWeight (k + 1) (1 / 2) (orderedNode k (1 / 2) j)
      let prefixList : List ℝ := List.ofFn (fun j : Fin k => w ⟨j.val, by omega⟩)
      let u_pen := orderedNode k (1 / 2) ⟨k, by omega⟩
      let u_last := orderedNode k (1 / 2) (Fin.last (k + 1))
      have hlist : List.ofFn w = prefixList ++ [w ⟨k, by omega⟩, w (Fin.last (k + 1))] := by
        have h1 := List.ofFn_succ' w
        have h2 := List.ofFn_succ' (fun j : Fin (k + 1) => w j.castSucc)
        simp only [List.concat_eq_append] at h1 h2
        rw [h1, h2, List.append_assoc]
        rfl
      rw [hlist, List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_nil]
      have hprefix_nonneg : 0 ≤ prefixList.foldl (fun acc x => x - acc) 0 := by
        have hpref_eq : prefixList = (List.ofFn (fun j : Fin k => orderedNode k (1 / 2) ⟨j.val, by omega⟩)).map
            (exteriorWeight (k + 1) (1 / 2)) := by
          rw [List.map_ofFn]
          rfl
        rw [hpref_eq]
        apply exteriorWeight_alternating_nonneg (k + 1) (Nat.succ_pos k) (by norm_num) (by norm_num)
        · rw [List.pairwise_iff_getElem]
          intro i j hi hj hij
          simp only [List.getElem_ofFn]
          exact (orderedNode_strictMono k (1 / 2) (Fin.mk_lt_mk.mpr hij)).le
        · intro y hy
          rcases List.mem_ofFn.mp hy with ⟨j, rfl⟩
          exact orderedNode_mem_Icc_unit k ⟨by norm_num, by norm_num⟩ _
      have hlast_gt : (1 / 2 : ℝ) < u_last := orderedNode_last_gt_half hk
      have hlast_le : u_last ≤ 1 := (orderedNode_mem_Icc_unit k ⟨by norm_num, by norm_num⟩ _).2
      have hpen_lt : u_pen < u_last :=
        orderedNode_strictMono k (1 / 2) (by simp [Fin.lt_def])
      have hpen_bd : u_pen ∈ Set.Icc (-1 : ℝ) 1 :=
        orderedNode_mem_Icc_unit k ⟨by norm_num, by norm_num⟩ _
      have hw_lt : w ⟨k, by omega⟩ < w (Fin.last (k + 1)) := by
        dsimp [w]
        change exteriorWeight (k + 1) (1 / 2) u_pen < exteriorWeight (k + 1) (1 / 2) u_last
        have hlast_pos : 0 < exteriorWeight (k + 1) (1 / 2) u_last := by
          rw [exteriorWeight, if_neg (not_lt_of_ge hlast_gt.le)]
          have hsf : speedFactor (k + 1) (1 / 2) u_last < 1 :=
            speedFactor_lt_one (k + 1) (Nat.succ_pos k) ht_abs (abs_le.mpr ⟨by linarith, hlast_le⟩)
          exact mul_pos (pow_pos (sub_pos.mpr hlast_gt) _) (sub_pos.mpr hsf)
        by_cases hpen_half : u_pen < 1 / 2
        · rw [exteriorWeight, if_pos hpen_half]
          exact hlast_pos
        · have hpen_ge : 1 / 2 ≤ u_pen := le_of_not_gt hpen_half
          rw [exteriorWeight, if_neg hpen_half, exteriorWeight, if_neg (not_lt_of_ge hlast_gt.le)]
          have hpow_lt : (u_pen - 1 / 2) ^ (k + 1) < (u_last - 1 / 2) ^ (k + 1) := by
            gcongr
          have hsf_lt : speedFactor (k + 1) (1 / 2) u_last < speedFactor (k + 1) (1 / 2) u_pen :=
            speedFactor_strictAntiOn (k + 1) (by norm_num) (by norm_num)
              ⟨hpen_ge, hpen_bd.2⟩ ⟨hlast_gt.le, hlast_le⟩ hpen_lt
          have h1sf_pos : 0 < 1 - speedFactor (k + 1) (1 / 2) u_pen :=
            sub_pos.mpr (speedFactor_lt_one (k + 1) (Nat.succ_pos k) ht_abs (abs_le.mpr hpen_bd))
          nlinarith [pow_nonneg (sub_nonneg.mpr hpen_ge) (k + 1)]
      linarith

theorem explicitErrorDerivCurve_neg_of_Ico_half_one {n : ℕ} (hn : 1 ≤ n) {t : ℝ}
    (ht0 : 1 / 2 ≤ t) (ht1 : t < 1) :
    explicitErrorDerivCurve n t < 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simpa [explicitErrorDerivCurve_succ] using explicitErrorDerivAt_neg_of_Ico_half_one k ht0 ht1

theorem explicitErrorCurve_strictAntiOn_Icc_half_one {n : ℕ} (hn : 1 ≤ n) :
    StrictAntiOn (explicitErrorCurve n) (Set.Icc (1 / 2 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact (continuous_explicitErrorCurve n).continuousOn
  · intro t ht
    rw [interior_Icc] at ht
    have ht_abs : |t| < 1 := abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
    rw [(hasDerivAt_explicitErrorCurve hn ht_abs).deriv]
    exact explicitErrorDerivCurve_neg_of_Ico_half_one hn ht.1.le ht.2

theorem HCurve_strictMonoOn_Icc_half_one {n : ℕ} (hn : 1 ≤ n) :
    StrictMonoOn (HCurve n) (Set.Icc (1 / 2 : ℝ) 1) := by
  intro a ha b hb hab
  have h := explicitErrorCurve_strictAntiOn_Icc_half_one hn ha hb hab
  simp only [HCurve]
  linarith

theorem HCurve_monotoneOn_Icc_half_one {n : ℕ} (hn : 1 ≤ n) :
    MonotoneOn (HCurve n) (Set.Icc (1 / 2 : ℝ) 1) :=
  (HCurve_strictMonoOn_Icc_half_one hn).monotoneOn

/-! ### Eq. (9) decomposition (`Hcomp`) via `DividedCDFBridge` -/

theorem neg_explicitErrorDerivAt_eq_barycentric (k : ℕ) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    -explicitErrorDerivAt k t =
      1 - barycentricDividedDifferenceOn (augmentedNodes k t) id (fun y =>
        (((k + 1 : ℕ) : ℝ) * (1 - t ^ 2) - 2 * (((k + 1 : ℕ) : ℝ) - 1) * t * (y - t) +
          2 * (y - t) ^ 2) * truncatedPower (k + 1) t y) := by
  have ht_abs : |t| < 1 := abs_lt.mpr ht
  have hquad (y : ℝ) :
      ((k + 1 : ℕ) : ℝ) * (1 - t ^ 2) - 2 * (((k + 1 : ℕ) : ℝ) - 1) * t * (y - t) +
          2 * (y - t) ^ 2 =
        SharpL1.speedDenominator (k + 1) t y - 2 * (1 - y ^ 2) := by
    simp only [SharpL1.speedDenominator]
    push_cast
    ring
  have hdiff :
      barycentricDividedDifferenceOn (augmentedNodes k t) id (fun y =>
          (SharpL1.speedDenominator (k + 1) t y - 2 * (1 - y ^ 2)) * truncatedPower (k + 1) t y) =
        barycentricDividedDifferenceOn (augmentedNodes k t) id
            (fun y => SharpL1.speedDenominator (k + 1) t y * truncatedPower (k + 1) t y) -
          barycentricDividedDifferenceOn (augmentedNodes k t) id
            (fun y => 2 * (1 - y ^ 2) * truncatedPower (k + 1) t y) := by
    unfold barycentricDividedDifferenceOn
    simp only [id_eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  have h1 := barycentric_speedDenominator_mul k ht_abs (truncatedPower (k + 1) t)
  have h2 := barycentric_two_mul_one_sub_sq_mul k ht_abs (truncatedPower (k + 1) t)
  have hm1 : truncatedPower (k + 1) t (-1) = 0 := by
    simp [truncatedPower, (show ¬ (t ≤ -1) by linarith [ht.1])]
  have hp1 : truncatedPower (k + 1) t 1 = (1 - t) ^ (k + 1) := by
    simp [truncatedPower, ht.2.le]
  rw [hm1, hp1] at h1
  simp_rw [hquad]
  rw [hdiff, h1, h2]
  have hcombine :
      (2 : ℝ) ^ (k + 1) * (1 - t) ^ (k + 1) - (-1 : ℝ) ^ (k + 2) * (2 : ℝ) ^ (k + 1) * 0 -
          (2 : ℝ) ^ (k + 2) *
            ∑ j : Fin (k + 2), (-1 : ℝ) ^ (k + 1 - j.val) * truncatedPower (k + 1) t (orderedNode k t j) -
        -(2 : ℝ) ^ (k + 2) *
          ∑ j : Fin (k + 2), (-1 : ℝ) ^ (k + 1 - j.val) *
            (2 * (1 - orderedNode k t j ^ 2) /
              SharpL1.speedDenominator (k + 1) t (orderedNode k t j)) *
            truncatedPower (k + 1) t (orderedNode k t j) =
      (2 : ℝ) ^ (k + 1) * (1 - t) ^ (k + 1) +
        (2 : ℝ) ^ (k + 2) *
          ∑ j : Fin (k + 2), (-1 : ℝ) ^ (k + 1 - j.val) *
            truncatedPower (k + 1) t (orderedNode k t j) *
            (2 * (1 - orderedNode k t j ^ 2) /
              SharpL1.speedDenominator (k + 1) t (orderedNode k t j) - 1) := by
    have hsum_comb :
        (2 : ℝ) ^ (k + 2) *
            ∑ j : Fin (k + 2), (-1 : ℝ) ^ (k + 1 - j.val) *
              truncatedPower (k + 1) t (orderedNode k t j) *
              (2 * (1 - orderedNode k t j ^ 2) /
                SharpL1.speedDenominator (k + 1) t (orderedNode k t j) - 1) =
          (2 : ℝ) ^ (k + 2) *
              ∑ j : Fin (k + 2), (-1 : ℝ) ^ (k + 1 - j.val) *
                (2 * (1 - orderedNode k t j ^ 2) /
                  SharpL1.speedDenominator (k + 1) t (orderedNode k t j)) *
                truncatedPower (k + 1) t (orderedNode k t j) -
            (2 : ℝ) ^ (k + 2) *
              ∑ j : Fin (k + 2), (-1 : ℝ) ^ (k + 1 - j.val) *
                truncatedPower (k + 1) t (orderedNode k t j) := by
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    linarith
  rw [hcombine]
  unfold explicitErrorDerivAt
  simp_rw [truncatedPower_sub_eq]
  ring

/-- Exact eq. (9) decomposition of `H'_{k+1}(t)` into the four weighted-exponential
sign expectations `G(Q_t^0 + (t+1)e_+)`, `G(Q_t^0 + (t-1)e_-)`, `G(Q_t)`, and `G(Q_t^0)`. -/
theorem neg_explicitErrorDerivAt_eq_lawSignMean (k : ℕ) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    let coreList : List ℝ := List.ofFn (orderedNode k t);
    let plusList : List ℝ := (-1 : ℝ) :: coreList;
    let minusList : List ℝ := (1 : ℝ) :: coreList;
    let fullList : List ℝ := (-1 : ℝ) :: (1 : ℝ) :: coreList;
    -explicitErrorDerivAt k t =
      (lawSignMean (weightedExpSum (plusList.map fun z => t - z)) +
        lawSignMean (weightedExpSum (minusList.map fun z => t - z))) / 2 +
      ((k + 1 : ℕ) : ℝ) / 2 *
        (lawSignMean (weightedExpSum (fullList.map fun z => t - z)) -
          lawSignMean (weightedExpSum (coreList.map fun z => t - z))) := by
  have ht_abs : |t| < 1 := abs_lt.mpr ht
  have hbd : ∀ j : Fin (k + 2), orderedNode k t j ∈ Set.Ioo (-1 : ℝ) 1 := fun j =>
    nodePolynomial_root_mem_Ioo k ht_abs (orderedNode_eval_eq_zero k t j)
  have hs_eq : (augmentedNodes k t) =
      ((-1 : ℝ) :: (1 : ℝ) :: List.ofFn (orderedNode k t)).toFinset := by
    ext x
    simp only [augmentedNodes, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and,
      List.toFinset_cons, List.mem_toFinset, List.mem_ofFn]
  rw [neg_explicitErrorDerivAt_eq_barycentric k ht, hs_eq]
  exact lawSignMean_Hcomp_of_nodes (Nat.succ_pos k) (orderedNode k t)
    (orderedNode_strictMono k t) hbd ht

theorem deriv_HCurve_eq_lawSignMean {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    let k := n - 1;
    let coreList : List ℝ := List.ofFn (orderedNode k t);
    let plusList : List ℝ := (-1 : ℝ) :: coreList;
    let minusList : List ℝ := (1 : ℝ) :: coreList;
    let fullList : List ℝ := (-1 : ℝ) :: (1 : ℝ) :: coreList;
    deriv (HCurve n) t =
      (lawSignMean (weightedExpSum (plusList.map fun z => t - z)) +
        lawSignMean (weightedExpSum (minusList.map fun z => t - z))) / 2 +
      (n : ℝ) / 2 *
        (lawSignMean (weightedExpSum (fullList.map fun z => t - z)) -
          lawSignMean (weightedExpSum (coreList.map fun z => t - z))) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have ht_abs : |t| < 1 := abs_lt.mpr ht
  rw [(hasDerivAt_HCurve hn ht_abs).deriv]
  simpa [explicitErrorDerivCurve_succ] using neg_explicitErrorDerivAt_eq_lawSignMean k ht

/-! ### Conditional full-interval monotonicity and unique center maximum from `chordDelta > 0` -/

theorem explicitErrorDerivAt_neg_of_chordDelta_pos (k : ℕ) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hchord : 0 < chordDelta (k + 1) t) :
    explicitErrorDerivAt k t < 0 := by
  have ht : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, ht1⟩
  have hdecomp := neg_explicitErrorDerivAt_eq_lawSignMean k ht
  dsimp only at hdecomp
  simp only [List.map_cons, List.map_ofFn, Function.comp_def, sub_neg_eq_add] at hdecomp
  have hfirst : 0 < (lawSignMean (weightedExpSum ((t + 1) :: List.ofFn fun x => t - orderedNode k t x)) +
      lawSignMean (weightedExpSum ((t - 1) :: List.ofFn fun x => t - orderedNode k t x))) / 2 :=
    firstTerm_lawSignMean_pos k ht0
  have hsecond : lawSignMean (weightedExpSum ((t + 1) :: (t - 1) :: List.ofFn fun x => t - orderedNode k t x)) -
      lawSignMean (weightedExpSum (List.ofFn fun x => t - orderedNode k t x)) =
      chordDelta (k + 1) t := by
    simpa [fullCoeffs, coreCoeffs] using lawSignMean_diff_eq_chordDelta k ht0 ht1
  have hk_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) / 2 := by positivity
  rw [hsecond] at hdecomp
  have hpos : 0 < -explicitErrorDerivAt k t := by
    rw [hdecomp]
    exact add_pos hfirst (mul_pos hk_pos hchord)
  linarith

theorem explicitErrorDerivCurve_neg_of_chordDelta_pos {n : ℕ} (hn : 1 ≤ n) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hchord : 0 < chordDelta n t) :
    explicitErrorDerivCurve n t < 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simpa [explicitErrorDerivCurve_succ] using
    explicitErrorDerivAt_neg_of_chordDelta_pos k ht0 ht1 hchord

theorem explicitErrorCurve_strictAntiOn_of_chordDelta_pos {n : ℕ} (hn : 1 ≤ n)
    (hchord : ∀ t ∈ Set.Ioc (0 : ℝ) (1 / 2), 0 < chordDelta n t) :
    StrictAntiOn (explicitErrorCurve n) (Set.Icc (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1) (continuous_explicitErrorCurve n).continuousOn
  intro t ht
  rw [interior_Icc] at ht
  have ht_abs : |t| < 1 := abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
  rw [(hasDerivAt_explicitErrorCurve hn ht_abs).deriv]
  by_cases hle : t ≤ 1 / 2
  · exact explicitErrorDerivCurve_neg_of_chordDelta_pos hn ht.1 ht.2 (hchord t ⟨ht.1, hle⟩)
  · exact explicitErrorDerivCurve_neg_of_Ico_half_one hn (le_of_not_ge hle) ht.2

theorem explicitErrorCurve_unique_max_of_chordDelta_pos {n : ℕ} (hn : 1 ≤ n)
    (hchord : ∀ t ∈ Set.Ioc (0 : ℝ) (1 / 2), 0 < chordDelta n t) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, t ≠ 0 → explicitErrorCurve n t < explicitErrorCurve n 0 := by
  have hanti := explicitErrorCurve_strictAntiOn_of_chordDelta_pos hn hchord
  intro t ht ht0
  rcases lt_or_gt_of_ne ht0 with hneg | hpos
  · rw [← explicitErrorCurve_neg ht]
    exact hanti ⟨le_rfl, zero_le_one⟩ ⟨by linarith, by linarith [ht.1]⟩ (neg_pos.mpr hneg)
  · exact hanti ⟨le_rfl, zero_le_one⟩ ⟨hpos.le, ht.2⟩ hpos

theorem HCurve_strictMonoOn_of_chordDelta_pos {n : ℕ} (hn : 1 ≤ n)
    (hchord : ∀ t ∈ Set.Ioc (0 : ℝ) (1 / 2), 0 < chordDelta n t) :
    StrictMonoOn (HCurve n) (Set.Icc (0 : ℝ) 1) := by
  have hanti := explicitErrorCurve_strictAntiOn_of_chordDelta_pos hn hchord
  intro a ha b hb hab
  simp only [HCurve]
  linarith [hanti ha hb hab]

theorem HCurve_unique_min_of_chordDelta_pos {n : ℕ} (hn : 1 ≤ n)
    (hchord : ∀ t ∈ Set.Ioc (0 : ℝ) (1 / 2), 0 < chordDelta n t) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, t ≠ 0 → HCurve n 0 < HCurve n t := by
  have hmax := explicitErrorCurve_unique_max_of_chordDelta_pos hn hchord
  intro t ht ht0
  simp only [HCurve]
  linarith [hmax t ht ht0]

end SharpL1.Analysis
