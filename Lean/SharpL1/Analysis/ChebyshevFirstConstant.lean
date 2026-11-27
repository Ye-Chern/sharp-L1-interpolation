module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Data.Real.Sign
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

/-!
# First sharp constant via second-kind Chebyshev polynomials

This module formalizes Section 2 (Claim 1, `clm:An`) of `chebyshev_L1_complete.tex`:

- `chebyshevMonicU n = 2^(-n) * U_n` is the monic second-kind Chebyshev polynomial `Q_n`.
- `chebyshevSign n y = sign (Q_n(y))` is its sign function `s_n`.
- Orthogonality: `∫ y in (-1)..1, s_n(y) * y^k = 0` for all `k < n`.
- Exact `L¹` norm: `∫ y in (-1)..1, |Q_n(y)| = 2^(1 - n)`.
- Derivatives: `D^n Q_n = n!` and `D^(n+1) Q_n = 0`.
- Sharp polynomial Markov-type `L¹` inequality: for every polynomial `P` of degree `≤ n`,
  `∫_{-1}^1 |P^(n)| ≤ 2^n * n! * ∫_{-1}^1 |P|`,
  with equality if and only if `P = C c * U_n` for some `c : ℝ`.
-/

namespace SharpL1.Analysis

open Polynomial MeasureTheory Set
open Polynomial.Chebyshev (U)

/-! ### Small helper lemmas for `Real.sign` and adjacent interval integrability -/

private theorem real_sign_mul_pos_left {c x : ℝ} (hc : 0 < c) :
    Real.sign (c * x) = Real.sign x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg hc hx), Real.sign_of_neg hx]
  · simp
  · rw [Real.sign_of_pos (mul_pos hc hx), Real.sign_of_pos hx]

private theorem real_sign_mul_pos_right {x c : ℝ} (hc : 0 < c) :
    Real.sign (x * c) = Real.sign x := by
  rw [mul_comm, real_sign_mul_pos_left hc]

private theorem real_sign_mul_self (x : ℝ) : Real.sign x * x = |x| := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [Real.sign_of_neg hx, abs_of_neg hx]; ring
  · simp
  · rw [Real.sign_of_pos hx, abs_of_pos hx, one_mul]

private theorem intervalIntegrable_adjacent {f : ℝ → ℝ} {a : ℕ → ℝ} :
    ∀ m : ℕ, (∀ i < m, IntervalIntegrable f volume (a i) (a (i + 1))) →
      IntervalIntegrable f volume (a 0) (a m)
  | 0, _ => IntervalIntegrable.refl
  | m + 1, h =>
    (intervalIntegrable_adjacent m (fun i hi => h i (Nat.lt_succ_of_lt hi))).trans
      (h m (Nat.lt_succ_self m))

/-! ### Definitions -/

/-- The monic second-kind Chebyshev polynomial `Q_n = 2^(-n) * U_n`. -/
noncomputable def chebyshevMonicU (n : ℕ) : ℝ[X] :=
  C ((1 / 2 : ℝ) ^ n) * U ℝ n

/-- The sign function `s_n(y) = sign(Q_n(y))` of the second-kind Chebyshev polynomial. -/
noncomputable def chebyshevSign (n : ℕ) (y : ℝ) : ℝ :=
  Real.sign ((chebyshevMonicU n).eval y)

/-- The descending Chebyshev partition `c_m = cos (m * π / (n + 1))` for `m = 0, ..., n + 1`. -/
noncomputable def chebyshevCosNode (n m : ℕ) : ℝ :=
  Real.cos ((m : ℝ) * Real.pi / ((n : ℝ) + 1))

/-- The ascending Chebyshev partition `r_j = -cos (j * π / (n + 1))` for `j = 0, ..., n + 1`. -/
noncomputable def chebyshevPartition (n j : ℕ) : ℝ :=
  -Real.cos ((j : ℝ) * Real.pi / ((n : ℝ) + 1))

/-- The sharp first constant `A_n = 2^n * n!` on `[-1, 1]`. -/
def firstBestConstant (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * (n.factorial : ℝ)

/-! ### Algebraic and trigonometric properties of `Q_n` -/

theorem natDegree_chebyshevMonicU (n : ℕ) : (chebyshevMonicU n).natDegree = n := by
  have hc : (1 / 2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [chebyshevMonicU, natDegree_C_mul hc, Polynomial.Chebyshev.natDegree_U_natCast]

theorem monic_chebyshevMonicU (n : ℕ) : (chebyshevMonicU n).Monic := by
  rw [Polynomial.Monic, leadingCoeff, natDegree_chebyshevMonicU, chebyshevMonicU, coeff_C_mul]
  have hlc : (U ℝ n).coeff n = (2 : ℝ) ^ n := by
    have h1 := Polynomial.Chebyshev.leadingCoeff_U_natCast ℝ n
    rwa [leadingCoeff, Polynomial.Chebyshev.natDegree_U_natCast] at h1
  rw [hlc, ← mul_pow]
  norm_num

theorem coeff_chebyshevMonicU_self (n : ℕ) : (chebyshevMonicU n).coeff n = 1 := by
  have h := monic_chebyshevMonicU n
  rwa [Polynomial.Monic, leadingCoeff, natDegree_chebyshevMonicU] at h

theorem chebyshevMonicU_ne_zero (n : ℕ) : chebyshevMonicU n ≠ 0 :=
  (monic_chebyshevMonicU n).ne_zero

theorem chebyshevMonicU_eval_cos_mul_sin (n : ℕ) (θ : ℝ) :
    (chebyshevMonicU n).eval (Real.cos θ) * Real.sin θ =
      (1 / 2 : ℝ) ^ n * Real.sin (((n : ℝ) + 1) * θ) := by
  rw [chebyshevMonicU, eval_mul, eval_C, mul_assoc]
  have hU := Polynomial.Chebyshev.U_real_cos (n := (n : ℤ)) (θ := θ)
  have hcast : (((n : ℤ) : ℝ) + 1) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hU
  rw [hU]

theorem chebyshevSign_eq_sign_U (n : ℕ) (y : ℝ) :
    chebyshevSign n y = Real.sign ((U ℝ n).eval y) := by
  rw [chebyshevSign, chebyshevMonicU, eval_mul, eval_C]
  exact real_sign_mul_pos_left (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)

theorem chebyshevSign_mul_self_eval (n : ℕ) (y : ℝ) :
    chebyshevSign n y * (chebyshevMonicU n).eval y = |(chebyshevMonicU n).eval y| :=
  real_sign_mul_self ((chebyshevMonicU n).eval y)

theorem abs_chebyshevSign_le_one (n : ℕ) (y : ℝ) : |chebyshevSign n y| ≤ 1 := by
  rcases lt_trichotomy ((chebyshevMonicU n).eval y) 0 with h | h | h
  · rw [chebyshevSign, Real.sign_of_neg h]; norm_num
  · rw [chebyshevSign, h, Real.sign_zero]; norm_num
  · rw [chebyshevSign, Real.sign_of_pos h]; norm_num

/-! ### Polynomial iterated derivatives -/

theorem iteratedDeriv_polynomial_eval (P : ℝ[X]) (k : ℕ) :
    iteratedDeriv k (fun y : ℝ => P.eval y) = fun y => (Polynomial.derivative^[k] P).eval y := by
  induction k generalizing P with
  | zero =>
    ext y
    simp
  | succ k ih =>
    rw [iteratedDeriv_succ']
    have hderiv : deriv (fun y : ℝ => P.eval y) = fun y => (Polynomial.derivative P).eval y := by
      ext y
      exact (Polynomial.hasDerivAt P y).deriv
    rw [hderiv, ih (Polynomial.derivative P), Function.iterate_succ_apply]

theorem polynomial_iterate_derivative_of_natDegree_le (P : ℝ[X]) (n : ℕ) (hP : P.natDegree ≤ n) :
    Polynomial.derivative^[n] P = C ((n.factorial : ℝ) * P.coeff n) := by
  induction n generalizing P with
  | zero =>
    have h0 : P.natDegree = 0 := Nat.eq_zero_of_le_zero hP
    rw [Function.iterate_zero_apply, Nat.factorial_zero, Nat.cast_one, one_mul]
    exact Polynomial.eq_C_of_natDegree_eq_zero h0
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have hdeg' : (Polynomial.derivative P).natDegree ≤ n := by
      have := Polynomial.natDegree_derivative_le P
      omega
    rw [ih (Polynomial.derivative P) hdeg', Polynomial.coeff_derivative]
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    ring

theorem iteratedDeriv_polynomial_eval_of_natDegree_le (P : ℝ[X]) (n : ℕ) (hP : P.natDegree ≤ n)
    (x : ℝ) :
    iteratedDeriv n (fun y : ℝ => P.eval y) x = (n.factorial : ℝ) * P.coeff n := by
  simp [iteratedDeriv_polynomial_eval, polynomial_iterate_derivative_of_natDegree_le P n hP]

theorem iteratedDeriv_chebyshevMonicU (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ => (chebyshevMonicU n).eval y) x = (n.factorial : ℝ) := by
  rw [iteratedDeriv_polynomial_eval_of_natDegree_le _ n (natDegree_chebyshevMonicU n).le,
    coeff_chebyshevMonicU_self, mul_one]

theorem iteratedDeriv_succ_chebyshevMonicU (n : ℕ) (x : ℝ) :
    iteratedDeriv (n + 1) (fun y : ℝ => (chebyshevMonicU n).eval y) x = 0 := by
  have hle : (chebyshevMonicU n).natDegree ≤ n + 1 := by
    rw [natDegree_chebyshevMonicU]; omega
  rw [iteratedDeriv_polynomial_eval_of_natDegree_le _ (n + 1) hle]
  have hzero : (chebyshevMonicU n).coeff (n + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [natDegree_chebyshevMonicU]; omega)
  rw [hzero, mul_zero]

/-! ### Partition points and piecewise sign of `Q_n` -/

theorem chebyshevCosNode_zero (n : ℕ) : chebyshevCosNode n 0 = 1 := by
  simp [chebyshevCosNode]

theorem chebyshevCosNode_last (n : ℕ) : chebyshevCosNode n (n + 1) = -1 := by
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  simp only [chebyshevCosNode, Nat.cast_add, Nat.cast_one]
  rw [mul_div_cancel_left₀ _ hne, Real.cos_pi]

theorem chebyshevPartition_eq_cosNode (n j : ℕ) (hj : j ≤ n + 1) :
    chebyshevPartition n j = chebyshevCosNode n (n + 1 - j) := by
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  simp only [chebyshevPartition, chebyshevCosNode]
  have hsub : ((n + 1 - j : ℕ) : ℝ) * Real.pi / ((n : ℝ) + 1) =
      Real.pi - (j : ℝ) * Real.pi / ((n : ℝ) + 1) := by
    rw [Nat.cast_sub hj]
    push_cast
    field_simp
  rw [hsub, Real.cos_pi_sub]

theorem chebyshevPartition_zero (n : ℕ) : chebyshevPartition n 0 = -1 := by
  simp [chebyshevPartition]

theorem chebyshevPartition_last (n : ℕ) : chebyshevPartition n (n + 1) = 1 := by
  rw [chebyshevPartition_eq_cosNode n (n + 1) le_rfl, Nat.sub_self, chebyshevCosNode_zero]

theorem chebyshevCosNode_strictAnti (n : ℕ) {i j : ℕ} (hj : j ≤ n + 1) (hij : i < j) :
    chebyshevCosNode n j < chebyshevCosNode n i := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  apply Real.strictAntiOn_cos
  · constructor
    · positivity
    · rw [div_le_iff₀ hpos]
      have : (i : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (hij.le.trans hj)
      nlinarith [Real.pi_pos]
  · constructor
    · positivity
    · rw [div_le_iff₀ hpos]
      have : (j : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hj
      nlinarith [Real.pi_pos]
  · exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right (by exact_mod_cast hij) Real.pi_pos) hpos

theorem chebyshevCosNode_mem_Icc (n m : ℕ) :
    chebyshevCosNode n m ∈ Icc (-1 : ℝ) 1 :=
  ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

theorem chebyshevMonicU_eval_cosNode (n m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    (chebyshevMonicU n).eval (chebyshevCosNode n m) = 0 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set θ := (m : ℝ) * Real.pi / ((n : ℝ) + 1)
  have hθ_pos : 0 < θ := by
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm1
    positivity
  have hθ_lt_pi : θ < Real.pi := by
    rw [div_lt_iff₀ hpos]
    have hm' : (m : ℝ) < (n : ℝ) + 1 := by exact_mod_cast (Nat.lt_succ_of_le hmn)
    nlinarith [Real.pi_pos]
  have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
  have hmul := chebyshevMonicU_eval_cos_mul_sin n θ
  have harg : ((n : ℝ) + 1) * θ = (m : ℝ) * Real.pi := by
    dsimp [θ]; field_simp
  rw [harg, Real.sin_nat_mul_pi, mul_zero] at hmul
  exact (mul_eq_zero.mp hmul).resolve_right hsin_pos.ne'

private theorem sign_sin_on_pi_interval (m : ℕ) {φ : ℝ}
    (hlo : (m : ℝ) * Real.pi < φ) (hhi : φ < ((m + 1 : ℕ) : ℝ) * Real.pi) :
    Real.sign (Real.sin φ) = (-1 : ℝ) ^ m := by
  have hsub : Real.sin φ = (-1 : ℝ) ^ m * Real.sin (φ - (m : ℝ) * Real.pi) := by
    have h1 := Real.sin_add_nat_mul_pi (φ - (m : ℝ) * Real.pi) m
    rw [sub_add_cancel] at h1
    rw [h1, mul_comm]
  have hpos : 0 < Real.sin (φ - (m : ℝ) * Real.pi) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · push_cast at hhi
      linarith
  rw [hsub, real_sign_mul_pos_right hpos]
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h1 : (-1 : ℝ) ^ (k + k) = 1 := by
      rw [← two_mul, pow_mul]; norm_num
    rw [h1, Real.sign_one]
  · have h1 : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
      rw [pow_succ, pow_mul]; norm_num
    rw [h1, Real.sign_of_neg (by norm_num)]

theorem chebyshevSign_on_cosInterval (n m : ℕ) (hm : m ≤ n) {y : ℝ}
    (hy : y ∈ Ioo (chebyshevCosNode n (m + 1)) (chebyshevCosNode n m)) :
    chebyshevSign n y = (-1 : ℝ) ^ m := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hy_Icc : y ∈ Icc (-1 : ℝ) 1 :=
    ⟨le_trans (Real.neg_one_le_cos _) hy.1.le, le_trans hy.2.le (Real.cos_le_one _)⟩
  set θ := Real.arccos y
  have hcosθ : Real.cos θ = y := Real.cos_arccos hy_Icc.1 hy_Icc.2
  have hθ_lo : (m : ℝ) * Real.pi / ((n : ℝ) + 1) < θ := by
    have hlt : Real.cos θ < Real.cos ((m : ℝ) * Real.pi / ((n : ℝ) + 1)) := by
      rw [hcosθ]; exact hy.2
    have hθ_mem : θ ∈ Icc 0 Real.pi := ⟨Real.arccos_nonneg y, Real.arccos_le_pi y⟩
    have hm_mem : (m : ℝ) * Real.pi / ((n : ℝ) + 1) ∈ Icc 0 Real.pi := by
      constructor
      · positivity
      · rw [div_le_iff₀ hpos]
        have : (m : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (Nat.le_succ_of_le hm)
        nlinarith [Real.pi_pos]
    by_contra hle
    push Not at hle
    have := Real.strictAntiOn_cos.antitoneOn hθ_mem hm_mem hle
    linarith
  have hθ_hi : θ < ((m + 1 : ℕ) : ℝ) * Real.pi / ((n : ℝ) + 1) := by
    have hlt : Real.cos (((m + 1 : ℕ) : ℝ) * Real.pi / ((n : ℝ) + 1)) < Real.cos θ := by
      rw [hcosθ]; exact hy.1
    have hθ_mem : θ ∈ Icc 0 Real.pi := ⟨Real.arccos_nonneg y, Real.arccos_le_pi y⟩
    have hm_mem : ((m + 1 : ℕ) : ℝ) * Real.pi / ((n : ℝ) + 1) ∈ Icc 0 Real.pi := by
      constructor
      · positivity
      · rw [div_le_iff₀ hpos]
        have : ((m + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (Nat.succ_le_succ hm)
        nlinarith [Real.pi_pos]
    by_contra hle
    push Not at hle
    have := Real.strictAntiOn_cos.antitoneOn hm_mem hθ_mem hle
    linarith
  have hθ_pos : 0 < θ := lt_of_le_of_lt (by positivity) hθ_lo
  have hθ_lt_pi : θ < Real.pi := by
    refine lt_of_lt_of_le hθ_hi ?_
    rw [div_le_iff₀ hpos]
    have : ((m + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (Nat.succ_le_succ hm)
    nlinarith [Real.pi_pos]
  have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
  have hmul := chebyshevMonicU_eval_cos_mul_sin n θ
  rw [hcosθ] at hmul
  have hsign_eq : chebyshevSign n y = Real.sign (Real.sin (((n : ℝ) + 1) * θ)) := by
    have h1 : Real.sign ((chebyshevMonicU n).eval y * Real.sin θ) =
        Real.sign ((1 / 2 : ℝ) ^ n * Real.sin (((n : ℝ) + 1) * θ)) := by
      rw [hmul]
    rw [real_sign_mul_pos_right hsin_pos,
      real_sign_mul_pos_left (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)] at h1
    exact h1
  rw [hsign_eq]
  apply sign_sin_on_pi_interval m
  · have h1 := (div_lt_iff₀ hpos).mp hθ_lo
    linarith
  · have h1 := (lt_div_iff₀ hpos).mp hθ_hi
    linarith

/-! ### Piecewise `y = cos θ` integration formula -/

private theorem intervalIntegrable_chebyshevSign_mul (n : ℕ) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    IntervalIntegrable (fun y => chebyshevSign n y * f y) volume (-1) 1 := by
  have hsub : ∀ m < n + 1,
      IntervalIntegrable (fun y => chebyshevSign n y * f y) volume
        (chebyshevCosNode n m) (chebyshevCosNode n (m + 1)) := by
    intro m hm
    have hm' : m ≤ n := Nat.lt_succ_iff.mp hm
    have hlt := chebyshevCosNode_strictAnti n (Nat.succ_le_succ hm') (Nat.lt_succ_self m)
    have hcont : ContinuousOn (fun y => (-1 : ℝ) ^ m * f y)
        (uIcc (chebyshevCosNode n m) (chebyshevCosNode n (m + 1))) := by
      refine continuousOn_const.mul (hf.mono ?_)
      rw [uIcc_of_ge hlt.le]
      exact Icc_subset_Icc (Real.neg_one_le_cos _) (Real.cos_le_one _)
    refine hcont.intervalIntegrable.congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    have hsing : ∀ᵐ y ∂volume, y ≠ chebyshevCosNode n m :=
      ae_iff.mpr (by simp [measure_singleton])
    filter_upwards [hsing] with y hne hy
    rw [uIoc_of_ge hlt.le] at hy
    rw [chebyshevSign_on_cosInterval n m hm' ⟨hy.1, lt_of_le_of_ne hy.2 hne⟩]
  have htrans := intervalIntegrable_adjacent (n + 1) hsub
  rw [chebyshevCosNode_zero, chebyshevCosNode_last] at htrans
  exact htrans.symm

theorem intervalIntegral_chebyshevSign_mul_piecewise (n : ℕ) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    ∫ y in (-1 : ℝ)..1, chebyshevSign n y * f y =
      ∑ m ∈ Finset.range (n + 1), (-1 : ℝ) ^ m *
        ∫ y in chebyshevCosNode n (m + 1)..chebyshevCosNode n m, f y := by
  have hint_sub : ∀ m ∈ Finset.range (n + 1),
      IntervalIntegrable (fun y => chebyshevSign n y * f y) volume
        (chebyshevCosNode n m) (chebyshevCosNode n (m + 1)) := by
    intro m hm
    have hm' : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hlt := chebyshevCosNode_strictAnti n (Nat.succ_le_succ hm') (Nat.lt_succ_self m)
    have hcont : ContinuousOn (fun y => (-1 : ℝ) ^ m * f y)
        (uIcc (chebyshevCosNode n m) (chebyshevCosNode n (m + 1))) := by
      refine continuousOn_const.mul (hf.mono ?_)
      rw [uIcc_of_ge hlt.le]
      exact Icc_subset_Icc (Real.neg_one_le_cos _) (Real.cos_le_one _)
    refine hcont.intervalIntegrable.congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    have hsing : ∀ᵐ y ∂volume, y ≠ chebyshevCosNode n m :=
      ae_iff.mpr (by simp [measure_singleton])
    filter_upwards [hsing] with y hne hy
    rw [uIoc_of_ge hlt.le] at hy
    rw [chebyshevSign_on_cosInterval n m hm' ⟨hy.1, lt_of_le_of_ne hy.2 hne⟩]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := chebyshevCosNode n)
    (μ := volume) (f := fun y => chebyshevSign n y * f y) (n := n + 1)
    (fun m hm => hint_sub m (Finset.mem_range.mpr hm))
  rw [chebyshevCosNode_zero, chebyshevCosNode_last] at hsum
  rw [← neg_neg (∫ y in (-1 : ℝ)..1, chebyshevSign n y * f y),
    ← intervalIntegral.integral_symm, ← hsum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hlt := chebyshevCosNode_strictAnti n (Nat.succ_le_succ hm') (Nat.lt_succ_self m)
  rw [intervalIntegral.integral_symm, neg_neg, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  have hsing : ∀ᵐ y ∂volume, y ≠ chebyshevCosNode n m :=
    ae_iff.mpr (by simp [measure_singleton])
  filter_upwards [hsing] with y hne hy
  rw [uIoc_of_le hlt.le] at hy
  rw [chebyshevSign_on_cosInterval n m hm' ⟨hy.1, lt_of_le_of_ne hy.2 hne⟩]

theorem intervalIntegral_cos_subst {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    ∫ y in Real.cos b..Real.cos a, f y =
      ∫ θ in a..b, f (Real.cos θ) * Real.sin θ := by
  have hderiv : ∀ θ ∈ uIcc a b, HasDerivAt Real.cos (-Real.sin θ) θ :=
    fun θ _ => Real.hasDerivAt_cos θ
  have hcont_deriv : ContinuousOn (fun θ => -Real.sin θ) (uIcc a b) :=
    Real.continuous_sin.neg.continuousOn
  have hcont_f : ContinuousOn f (Real.cos '' uIcc a b) := by
    refine hf.mono ?_
    rintro y ⟨θ, -, rfl⟩
    exact ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have h := intervalIntegral.integral_comp_mul_deriv' hderiv hcont_deriv hcont_f
  dsimp [Function.comp_def] at h
  have hneg : ∫ θ in a..b, f (Real.cos θ) * -Real.sin θ =
      -(∫ θ in a..b, f (Real.cos θ) * Real.sin θ) := by
    simp_rw [mul_neg]
    exact intervalIntegral.integral_neg
  rw [hneg] at h
  rw [intervalIntegral.integral_symm]
  linarith

theorem intervalIntegral_chebyshevSign_mul (n : ℕ) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    ∫ y in (-1 : ℝ)..1, chebyshevSign n y * f y =
      ∑ m ∈ Finset.range (n + 1), (-1 : ℝ) ^ m *
        ∫ θ in ((m : ℝ) * Real.pi / ((n : ℝ) + 1))..(((m + 1 : ℕ) : ℝ) * Real.pi / ((n : ℝ) + 1)),
          f (Real.cos θ) * Real.sin θ := by
  rw [intervalIntegral_chebyshevSign_mul_piecewise n hf]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  exact intervalIntegral_cos_subst hf

/-! ### Exact `L¹` norm of `Q_n` and `U_n` -/

theorem intervalIntegral_abs_chebyshevMonicU (n : ℕ) :
    ∫ y in (-1 : ℝ)..1, |(chebyshevMonicU n).eval y| = 2 * (1 / 2 : ℝ) ^ n := by
  have hrew : (fun y => |(chebyshevMonicU n).eval y|) =
      fun y => chebyshevSign n y * (chebyshevMonicU n).eval y := by
    ext y
    exact (chebyshevSign_mul_self_eval n y).symm
  rw [hrew, intervalIntegral_chebyshevSign_mul n (chebyshevMonicU n).continuous.continuousOn]
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hterm : ∀ m ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ m *
        ∫ θ in ((m : ℝ) * Real.pi / ((n : ℝ) + 1))..(((m + 1 : ℕ) : ℝ) * Real.pi / ((n : ℝ) + 1)),
          (chebyshevMonicU n).eval (Real.cos θ) * Real.sin θ =
        2 * (1 / 2 : ℝ) ^ n / ((n : ℝ) + 1) := by
    intro m _
    simp_rw [chebyshevMonicU_eval_cos_mul_sin]
    rw [intervalIntegral.integral_const_mul]
    set a := (m : ℝ) * Real.pi / ((n : ℝ) + 1)
    set b := ((m + 1 : ℕ) : ℝ) * Real.pi / ((n : ℝ) + 1)
    have hFTC : ∫ θ in a..b, Real.sin (((n : ℝ) + 1) * θ) =
        (-Real.cos (((n : ℝ) + 1) * b) / ((n : ℝ) + 1)) -
        (-Real.cos (((n : ℝ) + 1) * a) / ((n : ℝ) + 1)) := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun θ => -Real.cos (((n : ℝ) + 1) * θ) / ((n : ℝ) + 1))
        (fun θ _ => by
          have h1 : HasDerivAt (fun t : ℝ => ((n : ℝ) + 1) * t) ((n : ℝ) + 1) θ := by
            simpa using (hasDerivAt_id θ).const_mul ((n : ℝ) + 1)
          have h2 := (Real.hasDerivAt_cos (((n : ℝ) + 1) * θ)).comp θ h1
          have h3 := (h2.neg).div_const ((n : ℝ) + 1)
          have hsimp : -(-Real.sin (((n : ℝ) + 1) * θ) * ((n : ℝ) + 1)) / ((n : ℝ) + 1) =
              Real.sin (((n : ℝ) + 1) * θ) := by
            field_simp
          rwa [hsimp] at h3)
        ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
    rw [hFTC]
    have ha : ((n : ℝ) + 1) * a = (m : ℝ) * Real.pi := by dsimp [a]; field_simp
    have hb : ((n : ℝ) + 1) * b = ((m + 1 : ℕ) : ℝ) * Real.pi := by dsimp [b]; field_simp
    rw [ha, hb, Real.cos_nat_mul_pi, Real.cos_nat_mul_pi]
    have hpow : (-1 : ℝ) ^ m * ((-1 : ℝ) ^ m) = 1 := by
      rw [← mul_pow]; norm_num
    have hpow1 : (-1 : ℝ) ^ (m + 1) = -((-1 : ℝ) ^ m) := by rw [pow_succ]; ring
    rw [hpow1]
    calc (-1 : ℝ) ^ m *
          ((1 / 2 : ℝ) ^ n * (- -(-1 : ℝ) ^ m / ((n : ℝ) + 1) - -(-1 : ℝ) ^ m / ((n : ℝ) + 1)))
        = 2 * (1 / 2 : ℝ) ^ n * ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m) / ((n : ℝ) + 1) := by ring
      _ = 2 * (1 / 2 : ℝ) ^ n / ((n : ℝ) + 1) := by rw [hpow, mul_one]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  field_simp

theorem intervalIntegral_abs_chebyshevMonicU_zpow (n : ℕ) :
    ∫ y in (-1 : ℝ)..1, |(chebyshevMonicU n).eval y| = (2 : ℝ) ^ (1 - (n : ℤ)) := by
  rw [intervalIntegral_abs_chebyshevMonicU]
  rw [sub_eq_add_neg, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, zpow_neg, zpow_natCast,
    one_div, inv_pow]

theorem intervalIntegral_abs_U (n : ℕ) :
    ∫ y in (-1 : ℝ)..1, |(U ℝ n).eval y| = 2 := by
  have h := intervalIntegral_abs_chebyshevMonicU n
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  have heq : (fun y => |(chebyshevMonicU n).eval y|) =
      fun y => (1 / 2 : ℝ) ^ n * |(U ℝ n).eval y| := by
    ext y
    rw [chebyshevMonicU, eval_mul, eval_C, abs_mul, abs_of_pos hpos]
  rw [heq, intervalIntegral.integral_const_mul] at h
  exact mul_left_cancel₀ hpos.ne' (by linarith)

/-! ### Moment orthogonality of `s_n` -/

private theorem chebyshevSign_integral_sin_mul (n r : ℕ) (hr : r ≤ n) :
    ∑ m ∈ Finset.range (n + 1), (-1 : ℝ) ^ m *
      ∫ θ in ((m : ℝ) * Real.pi / ((n : ℝ) + 1))..(((m + 1 : ℕ) : ℝ) * Real.pi / ((n : ℝ) + 1)),
        Real.sin ((r : ℝ) * θ) = 0 := by
  by_cases hr0 : r = 0
  · subst hr0
    simp
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hr0)
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set φ := (r : ℝ) * Real.pi / ((n : ℝ) + 1)
  have hcos_pos : 0 < Real.cos (φ / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    have hφ_pos : 0 < φ := by dsimp [φ]; positivity
    have hφ_lt : φ < Real.pi := by
      dsimp [φ]
      rw [div_lt_iff₀ hpos]
      have : (r : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.lt_succ_of_le hr
      nlinarith [Real.pi_pos]
    constructor <;> linarith [Real.pi_pos]
  have hstep : ∀ m : ℕ,
      ∫ θ in ((m : ℝ) * Real.pi / ((n : ℝ) + 1))..(((m + 1 : ℕ) : ℝ) * Real.pi / ((n : ℝ) + 1)),
        Real.sin ((r : ℝ) * θ) =
      (Real.cos ((m : ℝ) * φ) - Real.cos (((m + 1 : ℕ) : ℝ) * φ)) / (r : ℝ) := by
    intro m
    set a := (m : ℝ) * Real.pi / ((n : ℝ) + 1)
    set b := ((m + 1 : ℕ) : ℝ) * Real.pi / ((n : ℝ) + 1)
    have hFTC : ∫ θ in a..b, Real.sin ((r : ℝ) * θ) =
        (-Real.cos ((r : ℝ) * b) / (r : ℝ)) - (-Real.cos ((r : ℝ) * a) / (r : ℝ)) := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun θ => -Real.cos ((r : ℝ) * θ) / (r : ℝ))
        (fun θ _ => by
          have h1 : HasDerivAt (fun t : ℝ => (r : ℝ) * t) (r : ℝ) θ := by
            simpa using (hasDerivAt_id θ).const_mul (r : ℝ)
          have h2 := (Real.hasDerivAt_cos ((r : ℝ) * θ)).comp θ h1
          have h3 := (h2.neg).div_const (r : ℝ)
          have hsimp : -(-Real.sin ((r : ℝ) * θ) * (r : ℝ)) / (r : ℝ) = Real.sin ((r : ℝ) * θ) := by
            field_simp
          rwa [hsimp] at h3)
        ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
    rw [hFTC]
    have ha : (r : ℝ) * a = (m : ℝ) * φ := by dsimp [a, φ]; ring
    have hb : (r : ℝ) * b = ((m + 1 : ℕ) : ℝ) * φ := by dsimp [b, φ]; ring
    rw [ha, hb]
    ring
  simp_rw [hstep, mul_div_assoc', ← Finset.sum_div]
  rw [div_eq_zero_iff]
  left
  suffices hmul :
      Real.cos (φ / 2) * ∑ m ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ m * (Real.cos ((m : ℝ) * φ) - Real.cos (((m + 1 : ℕ) : ℝ) * φ)) = 0 by
    exact (mul_eq_zero.mp hmul).resolve_left hcos_pos.ne'
  rw [Finset.mul_sum]
  have htrig : ∀ m : ℕ,
      Real.cos (φ / 2) * ((-1 : ℝ) ^ m * (Real.cos ((m : ℝ) * φ) - Real.cos (((m + 1 : ℕ) : ℝ) * φ))) =
      Real.sin (φ / 2) * (((-1 : ℝ) ^ m * Real.sin ((m : ℝ) * φ)) -
        ((-1 : ℝ) ^ (m + 1) * Real.sin (((m + 1 : ℕ) : ℝ) * φ))) := by
    intro m
    have hcos := Real.cos_sub_cos ((m : ℝ) * φ) (((m + 1 : ℕ) : ℝ) * φ)
    have hsin := Real.sin_add_sin ((m : ℝ) * φ) (((m + 1 : ℕ) : ℝ) * φ)
    have hdiff : ((m : ℝ) * φ - ((m + 1 : ℕ) : ℝ) * φ) / 2 = -(φ / 2) := by
      push_cast; ring
    rw [hdiff, Real.sin_neg] at hcos
    rw [hdiff, Real.cos_neg] at hsin
    have hpow : (-1 : ℝ) ^ (m + 1) = -((-1 : ℝ) ^ m) := by rw [pow_succ]; ring
    rw [hpow, hcos]
    linear_combination (norm := ring) -Real.sin (φ / 2) * (-1 : ℝ) ^ m * hsin
  simp_rw [htrig, ← Finset.mul_sum]
  have htele := Finset.sum_range_sub' (fun m => (-1 : ℝ) ^ m * Real.sin ((m : ℝ) * φ)) (n + 1)
  rw [htele]
  have harg : ((n + 1 : ℕ) : ℝ) * φ = (r : ℝ) * Real.pi := by
    dsimp [φ]
    push_cast
    field_simp
  rw [harg, Real.sin_nat_mul_pi]
  simp

private theorem chebyshevSign_integral_cos_pow_mul_sin (n k r : ℕ) (hkr : k + r ≤ n) :
    ∑ m ∈ Finset.range (n + 1), (-1 : ℝ) ^ m *
      ∫ θ in ((m : ℝ) * Real.pi / ((n : ℝ) + 1))..(((m + 1 : ℕ) : ℝ) * Real.pi / ((n : ℝ) + 1)),
        Real.cos θ ^ k * Real.sin ((r : ℝ) * θ) = 0 := by
  induction k generalizing r with
  | zero =>
    simpa using chebyshevSign_integral_sin_mul n r (by omega)
  | succ k ih =>
    cases r with
    | zero =>
      simp
    | succ r =>
      have hident : ∀ θ : ℝ,
          Real.cos θ ^ (k + 1) * Real.sin (((r + 1 : ℕ) : ℝ) * θ) =
          (1 / 2 : ℝ) * (Real.cos θ ^ k * Real.sin (((r + 2 : ℕ) : ℝ) * θ) +
            Real.cos θ ^ k * Real.sin ((r : ℝ) * θ)) := by
        intro θ
        have h := Real.sin_add_sin (((r + 2 : ℕ) : ℝ) * θ) ((r : ℝ) * θ)
        have h1 : (((r + 2 : ℕ) : ℝ) * θ + (r : ℝ) * θ) / 2 = ((r + 1 : ℕ) : ℝ) * θ := by
          push_cast; ring
        have h2 : (((r + 2 : ℕ) : ℝ) * θ - (r : ℝ) * θ) / 2 = θ := by
          push_cast; ring
        rw [h1, h2] at h
        rw [pow_succ]
        linear_combination (norm := ring) -(1 / 2 : ℝ) * Real.cos θ ^ k * h
      simp_rw [hident, intervalIntegral.integral_const_mul]
      have hint : ∀ m : ℕ,
          ∫ θ in ((m : ℝ) * Real.pi / ((n : ℝ) + 1))..(((m + 1 : ℕ) : ℝ) * Real.pi / ((n : ℝ) + 1)),
            (Real.cos θ ^ k * Real.sin (((r + 2 : ℕ) : ℝ) * θ) +
              Real.cos θ ^ k * Real.sin ((r : ℝ) * θ)) =
          (∫ θ in ((m : ℝ) * Real.pi / ((n : ℝ) + 1))..(((m + 1 : ℕ) : ℝ) * Real.pi / ((n : ℝ) + 1)),
            Real.cos θ ^ k * Real.sin (((r + 2 : ℕ) : ℝ) * θ)) +
          (∫ θ in ((m : ℝ) * Real.pi / ((n : ℝ) + 1))..(((m + 1 : ℕ) : ℝ) * Real.pi / ((n : ℝ) + 1)),
            Real.cos θ ^ k * Real.sin ((r : ℝ) * θ)) := by
        intro m
        exact intervalIntegral.integral_add
          (((Real.continuous_cos.pow k).mul
            (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _)
          (((Real.continuous_cos.pow k).mul
            (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _)
      simp_rw [hint]
      have hsplit :
          ∑ m ∈ Finset.range (n + 1), (-1 : ℝ) ^ m *
            ((1 / 2 : ℝ) *
              ((∫ θ in ((m : ℝ) * Real.pi / ((n : ℝ) + 1))..(((m + 1 : ℕ) : ℝ) * Real.pi / ((n : ℝ) + 1)),
                Real.cos θ ^ k * Real.sin (((r + 2 : ℕ) : ℝ) * θ)) +
              (∫ θ in ((m : ℝ) * Real.pi / ((n : ℝ) + 1))..(((m + 1 : ℕ) : ℝ) * Real.pi / ((n : ℝ) + 1)),
                Real.cos θ ^ k * Real.sin ((r : ℝ) * θ)))) =
          (1 / 2 : ℝ) *
            ((∑ m ∈ Finset.range (n + 1), (-1 : ℝ) ^ m *
              ∫ θ in ((m : ℝ) * Real.pi / ((n : ℝ) + 1))..(((m + 1 : ℕ) : ℝ) * Real.pi / ((n : ℝ) + 1)),
                Real.cos θ ^ k * Real.sin (((r + 2 : ℕ) : ℝ) * θ)) +
            (∑ m ∈ Finset.range (n + 1), (-1 : ℝ) ^ m *
              ∫ θ in ((m : ℝ) * Real.pi / ((n : ℝ) + 1))..(((m + 1 : ℕ) : ℝ) * Real.pi / ((n : ℝ) + 1)),
                Real.cos θ ^ k * Real.sin ((r : ℝ) * θ))) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => by ring
      rw [hsplit, ih (r + 2) (by omega), ih r (by omega)]
      ring

/-- Moment orthogonality of `s_n`: `∫_{-1}^1 s_n(y) * y^k dy = 0` for all `0 ≤ k < n`. -/
theorem intervalIntegral_chebyshevSign_mul_pow_eq_zero (n k : ℕ) (hk : k < n) :
    ∫ y in (-1 : ℝ)..1, chebyshevSign n y * y ^ k = 0 := by
  rw [intervalIntegral_chebyshevSign_mul n (continuous_pow k).continuousOn]
  simpa using chebyshevSign_integral_cos_pow_mul_sin n k 1 (by omega)

/-- Any polynomial of degree strictly less than `n` is orthogonal to `s_n` on `[-1, 1]`. -/
theorem intervalIntegral_chebyshevSign_mul_poly_eq_zero (n : ℕ) (R : ℝ[X])
    (hR : ∀ k, n ≤ k → R.coeff k = 0) :
    ∫ y in (-1 : ℝ)..1, chebyshevSign n y * R.eval y = 0 := by
  by_cases hR0 : R = 0
  · subst hR0; simp
  have hdeg_lt : R.natDegree < n := by
    by_contra hge
    push Not at hge
    exact (Polynomial.leadingCoeff_ne_zero.mpr hR0) (hR R.natDegree hge)
  have hsum_eval : ∀ y : ℝ, R.eval y = ∑ k ∈ Finset.range n, R.coeff k * y ^ k :=
    fun y => Polynomial.eval_eq_sum_range' hdeg_lt y
  have hint_term : ∀ k ∈ Finset.range n,
      IntervalIntegrable (fun y : ℝ => chebyshevSign n y * (R.coeff k * y ^ k)) volume (-1) 1 :=
    fun k _ => intervalIntegrable_chebyshevSign_mul n
      (continuous_const.mul (continuous_pow k)).continuousOn
  have hfun : (fun y : ℝ => chebyshevSign n y * R.eval y) =
      fun y => ∑ k ∈ Finset.range n, chebyshevSign n y * (R.coeff k * y ^ k) := by
    ext y
    rw [hsum_eval, Finset.mul_sum]
  rw [hfun, intervalIntegral.integral_finsetSum hint_term]
  apply Finset.sum_eq_zero
  intro k hk
  have h1 : (fun y : ℝ => chebyshevSign n y * (R.coeff k * y ^ k)) =
      fun y => R.coeff k * (chebyshevSign n y * y ^ k) := by
    ext y; ring
  rw [h1, intervalIntegral.integral_const_mul,
    intervalIntegral_chebyshevSign_mul_pow_eq_zero n k (Finset.mem_range.mp hk), mul_zero]

/-- Exact formula for `∫_{-1}^1 s_n(y) * P(y) dy` when `deg P ≤ n`. -/
theorem intervalIntegral_chebyshevSign_mul_poly (n : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ n) :
    ∫ y in (-1 : ℝ)..1, chebyshevSign n y * P.eval y =
      2 * (1 / 2 : ℝ) ^ n * P.coeff n := by
  let R : ℝ[X] := P - C (P.coeff n) * chebyshevMonicU n
  have hR_coeff : ∀ k, n ≤ k → R.coeff k = 0 := by
    intro k hk
    simp only [R, coeff_sub, coeff_C_mul]
    rcases hk.eq_or_lt with rfl | hlt
    · rw [coeff_chebyshevMonicU_self, mul_one, sub_self]
    · have hP0 : P.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP hlt)
      have hQ0 : (chebyshevMonicU n).coeff k = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [natDegree_chebyshevMonicU]; exact hlt)
      rw [hP0, hQ0, mul_zero, sub_zero]
  have hsplit : (fun y : ℝ => chebyshevSign n y * P.eval y) =
      fun y => P.coeff n * (chebyshevSign n y * (chebyshevMonicU n).eval y) +
        chebyshevSign n y * R.eval y := by
    ext y
    simp only [R, eval_sub, eval_mul, eval_C]
    ring
  have hint_Q : IntervalIntegrable
      (fun y : ℝ => P.coeff n * (chebyshevSign n y * (chebyshevMonicU n).eval y)) volume (-1) 1 := by
    have heq : (fun y : ℝ => P.coeff n * (chebyshevSign n y * (chebyshevMonicU n).eval y)) =
        fun y => P.coeff n * |(chebyshevMonicU n).eval y| := by
      ext y; rw [chebyshevSign_mul_self_eval]
    rw [heq]
    exact (continuous_const.mul (chebyshevMonicU n).continuous.abs).intervalIntegrable _ _
  have hint_R : IntervalIntegrable (fun y : ℝ => chebyshevSign n y * R.eval y) volume (-1) 1 :=
    intervalIntegrable_chebyshevSign_mul n R.continuous.continuousOn
  rw [hsplit, intervalIntegral.integral_add hint_Q hint_R,
    intervalIntegral_chebyshevSign_mul_poly_eq_zero n R hR_coeff, add_zero,
    intervalIntegral.integral_const_mul]
  have heq : (fun y => chebyshevSign n y * (chebyshevMonicU n).eval y) =
      fun y => |(chebyshevMonicU n).eval y| := by
    ext y; exact chebyshevSign_mul_self_eval n y
  rw [heq, intervalIntegral_abs_chebyshevMonicU]
  ring

/-! ### Sharp polynomial inequality and extremizer uniqueness (Claim 1) -/

/-- The `L¹` norm of the `n`-th derivative of a polynomial of degree `≤ n` on `[-1, 1]`. -/
theorem intervalIntegral_abs_iteratedDeriv_poly (n : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ n) :
    ∫ y in (-1 : ℝ)..1, |iteratedDeriv n (fun x => P.eval x) y| =
      2 * (n.factorial : ℝ) * |P.coeff n| := by
  simp_rw [iteratedDeriv_polynomial_eval_of_natDegree_le P n hP]
  rw [intervalIntegral.integral_const, smul_eq_mul, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg _)]
  ring

/-- **Sharp polynomial `L¹` inequality** (Section 2, Claim 1):
for every polynomial `P` of degree at most `n`,
`‖P^(n)‖_{L¹[-1,1]} ≤ 2^n * n! * ‖P‖_{L¹[-1,1]}`. -/
theorem polynomial_L1_deriv_le (n : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ n) :
    ∫ y in (-1 : ℝ)..1, |iteratedDeriv n (fun x => P.eval x) y| ≤
      firstBestConstant n * ∫ y in (-1 : ℝ)..1, |P.eval y| := by
  rw [intervalIntegral_abs_iteratedDeriv_poly n P hP, firstBestConstant]
  have hsign := intervalIntegral_chebyshevSign_mul_poly n P hP
  have hint_abs : IntervalIntegrable (fun y : ℝ => |chebyshevSign n y * P.eval y|) volume (-1) 1 := by
    have hsub : ∀ m < n + 1,
        IntervalIntegrable (fun y : ℝ => |chebyshevSign n y * P.eval y|) volume
          (chebyshevCosNode n m) (chebyshevCosNode n (m + 1)) := by
      intro m hm
      have hm' : m ≤ n := Nat.lt_succ_iff.mp hm
      have hlt := chebyshevCosNode_strictAnti n (Nat.succ_le_succ hm') (Nat.lt_succ_self m)
      refine (P.continuous.abs.intervalIntegrable _ _).congr_ae ?_
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
      have hsing : ∀ᵐ y ∂volume, y ≠ chebyshevCosNode n m :=
        ae_iff.mpr (by simp [measure_singleton])
      filter_upwards [hsing] with y hne hy
      rw [uIoc_of_ge hlt.le] at hy
      rw [chebyshevSign_on_cosInterval n m hm' ⟨hy.1, lt_of_le_of_ne hy.2 hne⟩,
        abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have htrans := intervalIntegrable_adjacent (n + 1) hsub
    rw [chebyshevCosNode_zero, chebyshevCosNode_last] at htrans
    exact htrans.symm
  have habs_int : |∫ y in (-1 : ℝ)..1, chebyshevSign n y * P.eval y| ≤
      ∫ y in (-1 : ℝ)..1, |P.eval y| := by
    calc |∫ y in (-1 : ℝ)..1, chebyshevSign n y * P.eval y|
        ≤ ∫ y in (-1 : ℝ)..1, |chebyshevSign n y * P.eval y| :=
          intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ ≤ ∫ y in (-1 : ℝ)..1, |P.eval y| := by
          apply intervalIntegral.integral_mono_on (by norm_num) hint_abs
            (P.continuous.abs.intervalIntegrable _ _)
          intro y _
          rw [abs_mul]
          calc |chebyshevSign n y| * |P.eval y|
              ≤ 1 * |P.eval y| :=
                mul_le_mul_of_nonneg_right (abs_chebyshevSign_le_one n y) (abs_nonneg _)
            _ = |P.eval y| := one_mul _
  rw [hsign, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * (1 / 2 : ℝ) ^ n)] at habs_int
  have hmul := mul_le_mul_of_nonneg_left habs_int
    (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n * (n.factorial : ℝ))
  have hcancel : (2 : ℝ) ^ n * (n.factorial : ℝ) * (2 * (1 / 2 : ℝ) ^ n * |P.coeff n|) =
      2 * (n.factorial : ℝ) * |P.coeff n| := by
    have : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
    linear_combination (norm := ring) 2 * (n.factorial : ℝ) * |P.coeff n| * this
  linarith

/-- Any constant `A` valid on polynomials of degree `≤ n` satisfies `A ≥ 2^n * n!`. -/
theorem firstBestConstant_le_of_poly_bound (n : ℕ) (A : ℝ)
    (hA : ∀ P : ℝ[X], P.natDegree ≤ n →
      ∫ y in (-1 : ℝ)..1, |iteratedDeriv n (fun x => P.eval x) y| ≤
        A * ∫ y in (-1 : ℝ)..1, |P.eval y|) :
    firstBestConstant n ≤ A := by
  have h := hA (chebyshevMonicU n) (natDegree_chebyshevMonicU n).le
  simp_rw [iteratedDeriv_chebyshevMonicU] at h
  rw [intervalIntegral.integral_const, smul_eq_mul, abs_of_nonneg (Nat.cast_nonneg _),
    intervalIntegral_abs_chebyshevMonicU] at h
  have hpos : (0 : ℝ) < 2 * (1 / 2 : ℝ) ^ n := by positivity
  rw [firstBestConstant]
  have hcancel : (2 : ℝ) ^ n * (n.factorial : ℝ) * (2 * (1 / 2 : ℝ) ^ n) =
      (1 - (-1 : ℝ)) * (n.factorial : ℝ) := by
    have : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
    linear_combination (norm := ring) 2 * (n.factorial : ℝ) * this
  nlinarith

/-- **Polynomial extremizer uniqueness** (Section 2, Claim 1):
for `deg P ≤ n`, equality `‖P^(n)‖_1 = 2^n * n! * ‖P‖_1` holds on `[-1, 1]`
if and only if `P = C c * U_n` for some `c : ℝ`. -/
theorem polynomial_L1_deriv_eq_iff (n : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ n) :
    (∫ y in (-1 : ℝ)..1, |iteratedDeriv n (fun x => P.eval x) y| =
      firstBestConstant n * ∫ y in (-1 : ℝ)..1, |P.eval y|) ↔
    ∃ c : ℝ, P = C c * U ℝ n := by
  constructor
  · intro heq
    by_cases hn0 : n = 0
    · subst hn0
      refine ⟨P.coeff 0, ?_⟩
      rw [Nat.cast_zero, Polynomial.Chebyshev.U_zero, mul_one]
      exact Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hP)
    rw [intervalIntegral_abs_iteratedDeriv_poly n P hP, firstBestConstant] at heq
    have hsign := intervalIntegral_chebyshevSign_mul_poly n P hP
    have hpos_coeff : (0 : ℝ) < (2 : ℝ) ^ n * (n.factorial : ℝ) := by positivity
    have habs_eq : |∫ y in (-1 : ℝ)..1, chebyshevSign n y * P.eval y| =
        ∫ y in (-1 : ℝ)..1, |P.eval y| := by
      rw [hsign, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * (1 / 2 : ℝ) ^ n)]
      have hcancel : (2 : ℝ) ^ n * (n.factorial : ℝ) * (2 * (1 / 2 : ℝ) ^ n * |P.coeff n|) =
          2 * (n.factorial : ℝ) * |P.coeff n| := by
        have : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
        linear_combination (norm := ring) 2 * (n.factorial : ℝ) * |P.coeff n| * this
      nlinarith
    -- Pick `σ ∈ {1, -1}` so that `σ * ∫ s_n * P = ∫ |P|`.
    let σ : ℝ := if 0 ≤ ∫ y in (-1 : ℝ)..1, chebyshevSign n y * P.eval y then 1 else -1
    have hσ_abs : |σ| = 1 := by
      dsimp [σ]; split_ifs <;> norm_num
    have hσ_eq : σ * ∫ y in (-1 : ℝ)..1, chebyshevSign n y * P.eval y =
        ∫ y in (-1 : ℝ)..1, |P.eval y| := by
      rw [← habs_eq]
      dsimp [σ]
      split_ifs with h
      · rw [one_mul, abs_of_nonneg h]
      · push Not at h; rw [abs_of_neg h]; ring
    -- Split `∫ |P| - σ * ∫ s_n * P = 0` into the `n + 1` subintervals `[c_{m+1}, c_m]`.
    have hsplit_abs : ∫ y in (-1 : ℝ)..1, |P.eval y| =
        ∑ m ∈ Finset.range (n + 1),
          ∫ y in chebyshevCosNode n (m + 1)..chebyshevCosNode n m, |P.eval y| := by
      have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := chebyshevCosNode n)
        (μ := volume) (f := fun y => |P.eval y|) (n := n + 1)
        (fun m _ => P.continuous.abs.intervalIntegrable _ _)
      rw [chebyshevCosNode_zero, chebyshevCosNode_last] at hsum
      rw [← neg_neg (∫ y in (-1 : ℝ)..1, |P.eval y|), ← intervalIntegral.integral_symm, ← hsum,
        ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [intervalIntegral.integral_symm, neg_neg]
    have hsplit_sign := intervalIntegral_chebyshevSign_mul_piecewise n P.continuous.continuousOn
    have hsum_zero : ∑ m ∈ Finset.range (n + 1),
        ∫ y in chebyshevCosNode n (m + 1)..chebyshevCosNode n m,
          (|P.eval y| - σ * (-1 : ℝ) ^ m * P.eval y) = 0 := by
      have hrew : ∀ m ∈ Finset.range (n + 1),
          ∫ y in chebyshevCosNode n (m + 1)..chebyshevCosNode n m,
            (|P.eval y| - σ * (-1 : ℝ) ^ m * P.eval y) =
          (∫ y in chebyshevCosNode n (m + 1)..chebyshevCosNode n m, |P.eval y|) -
            σ * ((-1 : ℝ) ^ m *
              ∫ y in chebyshevCosNode n (m + 1)..chebyshevCosNode n m, P.eval y) := by
        intro m _
        have hint2 : IntervalIntegrable (fun y => σ * (-1 : ℝ) ^ m * P.eval y) volume
            (chebyshevCosNode n (m + 1)) (chebyshevCosNode n m) :=
          (continuous_const.mul P.continuous).intervalIntegrable _ _
        rw [intervalIntegral.integral_sub (P.continuous.abs.intervalIntegrable _ _) hint2]
        simp_rw [mul_assoc]
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      rw [Finset.sum_congr rfl hrew, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← hsplit_abs, ← hsplit_sign, hσ_eq, sub_self]
    have hnonneg_integrand : ∀ m (y : ℝ), 0 ≤ |P.eval y| - σ * (-1 : ℝ) ^ m * P.eval y := by
      intro m y
      have h1 : σ * (-1 : ℝ) ^ m * P.eval y ≤ |σ * (-1 : ℝ) ^ m * P.eval y| := le_abs_self _
      rw [abs_mul, abs_mul, hσ_abs, abs_pow, abs_neg, abs_one, one_pow, one_mul, one_mul] at h1
      linarith
    have hterm_zero : ∀ m ∈ Finset.range (n + 1),
        ∫ y in chebyshevCosNode n (m + 1)..chebyshevCosNode n m,
          (|P.eval y| - σ * (-1 : ℝ) ^ m * P.eval y) = 0 := by
      have hnonneg : ∀ m ∈ Finset.range (n + 1),
          0 ≤ ∫ y in chebyshevCosNode n (m + 1)..chebyshevCosNode n m,
            (|P.eval y| - σ * (-1 : ℝ) ^ m * P.eval y) := by
        intro m hm
        have hm' : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
        have hlt := chebyshevCosNode_strictAnti n (Nat.succ_le_succ hm') (Nat.lt_succ_self m)
        exact intervalIntegral.integral_nonneg hlt.le (fun y _ => hnonneg_integrand m y)
      exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum_zero
    -- On each closed subinterval `[c_{m+1}, c_m]`, `σ * (-1)^m * P(y) = |P(y)| ≥ 0`.
    have hsign_sub : ∀ m ≤ n, ∀ y ∈ Icc (chebyshevCosNode n (m + 1)) (chebyshevCosNode n m),
        0 ≤ σ * (-1 : ℝ) ^ m * P.eval y := by
      intro m hm y hy
      have hlt := chebyshevCosNode_strictAnti n (Nat.succ_le_succ hm) (Nat.lt_succ_self m)
      have hz := hterm_zero m (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
      have hcont : ContinuousOn (fun x => |P.eval x| - σ * (-1 : ℝ) ^ m * P.eval x)
          (Icc (chebyshevCosNode n (m + 1)) (chebyshevCosNode n m)) :=
        (P.continuous.abs.sub (continuous_const.mul P.continuous)).continuousOn
      have hzero_on : ∀ x ∈ Icc (chebyshevCosNode n (m + 1)) (chebyshevCosNode n m),
          |P.eval x| - σ * (-1 : ℝ) ^ m * P.eval x = 0 := by
        rw [intervalIntegral.integral_of_le hlt.le] at hz
        have hEqOn := (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
          (Filter.Eventually.of_forall fun x => hnonneg_integrand m x)
          (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)).mp hz
        have hIoo : ∀ x ∈ Ioo (chebyshevCosNode n (m + 1)) (chebyshevCosNode n m),
            |P.eval x| - σ * (-1 : ℝ) ^ m * P.eval x = 0 := by
          intro x hx
          by_contra hne
          have hpos_val : 0 < |P.eval x| - σ * (-1 : ℝ) ^ m * P.eval x :=
            lt_of_le_of_ne (hnonneg_integrand m x) (Ne.symm hne)
          have hopen : IsOpen {z | 0 < |P.eval z| - σ * (-1 : ℝ) ^ m * P.eval z} :=
            isOpen_lt continuous_const (P.continuous.abs.sub (continuous_const.mul P.continuous))
          have hU : (Ioo (chebyshevCosNode n (m + 1)) (chebyshevCosNode n m) ∩
              {z | 0 < |P.eval z| - σ * (-1 : ℝ) ^ m * P.eval z}).Nonempty := ⟨x, hx, hpos_val⟩
          have hU_open : IsOpen (Ioo (chebyshevCosNode n (m + 1)) (chebyshevCosNode n m) ∩
              {z | 0 < |P.eval z| - σ * (-1 : ℝ) ^ m * P.eval z}) := isOpen_Ioo.inter hopen
          have hmeas_pos : 0 < volume (Ioo (chebyshevCosNode n (m + 1)) (chebyshevCosNode n m) ∩
              {z | 0 < |P.eval z| - σ * (-1 : ℝ) ^ m * P.eval z}) :=
            hU_open.measure_pos volume hU
          have hsub_zero : (Ioo (chebyshevCosNode n (m + 1)) (chebyshevCosNode n m) ∩
              {z | 0 < |P.eval z| - σ * (-1 : ℝ) ^ m * P.eval z}) ⊆
              {z | z ∈ Ioc (chebyshevCosNode n (m + 1)) (chebyshevCosNode n m) ∧
                |P.eval z| - σ * (-1 : ℝ) ^ m * P.eval z ≠ 0} := by
            intro z ⟨hz1, hz2⟩
            exact ⟨Ioo_subset_Ioc_self hz1, ne_of_gt hz2⟩
          have hae0 : volume {z | z ∈ Ioc (chebyshevCosNode n (m + 1)) (chebyshevCosNode n m) ∧
              |P.eval z| - σ * (-1 : ℝ) ^ m * P.eval z ≠ 0} = 0 := by
            rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at hEqOn
            have hset : {z | z ∈ Ioc (chebyshevCosNode n (m + 1)) (chebyshevCosNode n m) ∧
                |P.eval z| - σ * (-1 : ℝ) ^ m * P.eval z ≠ 0} =
                {z | ¬(z ∈ Ioc (chebyshevCosNode n (m + 1)) (chebyshevCosNode n m) →
                  |P.eval z| - σ * (-1 : ℝ) ^ m * P.eval z = 0)} := by
              ext z; simp only [Set.mem_setOf_eq, ne_eq, Classical.not_imp]
            rw [hset]
            exact ae_iff.mp hEqOn
          exact hmeas_pos.ne' (measure_mono_null hsub_zero hae0)
        have hdense : closure (Ioo (chebyshevCosNode n (m + 1)) (chebyshevCosNode n m)) =
            Icc (chebyshevCosNode n (m + 1)) (chebyshevCosNode n m) :=
          closure_Ioo hlt.ne
        have hclosed : IsClosed {x | |P.eval x| - σ * (-1 : ℝ) ^ m * P.eval x = 0} :=
          isClosed_eq (P.continuous.abs.sub (continuous_const.mul P.continuous)) continuous_const
        have hsub_cl : Icc (chebyshevCosNode n (m + 1)) (chebyshevCosNode n m) ⊆
            {x | |P.eval x| - σ * (-1 : ℝ) ^ m * P.eval x = 0} := by
          rw [← hdense]
          exact closure_minimal hIoo hclosed
        exact hsub_cl
      have hy0 := hzero_on y hy
      linarith [abs_nonneg (P.eval y)]
    -- Hence `P` vanishes at all `n` interior Chebyshev nodes `c_1, ..., c_n`.
    have hP_roots : ∀ m, 1 ≤ m → m ≤ n → P.eval (chebyshevCosNode n m) = 0 := by
      intro m hm1 hmn
      have hge1 := hsign_sub m hmn (chebyshevCosNode n m)
        ⟨(chebyshevCosNode_strictAnti n (Nat.succ_le_succ hmn) (Nat.lt_succ_self m)).le, le_rfl⟩
      have hm1' : m - 1 ≤ n := by omega
      have hsub_eq : m - 1 + 1 = m := Nat.sub_add_cancel hm1
      have hge2 := hsign_sub (m - 1) hm1' (chebyshevCosNode n m)
        ⟨by rw [hsub_eq], by
          rw [← hsub_eq]
          exact (chebyshevCosNode_strictAnti n (by omega) (Nat.lt_succ_self (m - 1))).le⟩
      have hpow : (-1 : ℝ) ^ m = -((-1 : ℝ) ^ (m - 1)) := by
        conv_lhs => rw [← hsub_eq, pow_succ]
        ring
      rw [hpow] at hge1
      have hprod0 : σ * (-1 : ℝ) ^ (m - 1) * P.eval (chebyshevCosNode n m) = 0 := by linarith
      have hσ_ne : σ ≠ 0 := by
        intro h0; rw [h0, abs_zero] at hσ_abs; norm_num at hσ_abs
      have hpow_ne : (-1 : ℝ) ^ (m - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
      exact (mul_eq_zero.mp hprod0).resolve_left (mul_ne_zero hσ_ne hpow_ne)
    -- Now `R = P - C (P.coeff n) * chebyshevMonicU n` has degree `< n` and `n` distinct roots.
    let R : ℝ[X] := P - C (P.coeff n) * chebyshevMonicU n
    have hR_deg : R = 0 ∨ R.natDegree < n := by
      by_cases hR0 : R = 0
      · exact Or.inl hR0
      · right
        by_contra hge
        push Not at hge
        have hcoeff_ne : R.coeff R.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hR0
        have hcoeff0 : R.coeff R.natDegree = 0 := by
          simp only [R, coeff_sub, coeff_C_mul]
          rcases hge.eq_or_lt with heq' | hlt'
          · rw [← heq', coeff_chebyshevMonicU_self, mul_one, sub_self]
          · have hP0 := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP hlt')
            have hQ0 := Polynomial.coeff_eq_zero_of_natDegree_lt
              (by rw [natDegree_chebyshevMonicU]; exact hlt')
            rw [hP0, hQ0, mul_zero, sub_zero]
        exact hcoeff_ne hcoeff0
    have hR_zero : R = 0 := by
      rcases hR_deg with h0 | hdeg_lt
      · exact h0
      · by_contra hR_ne
        let S : Finset ℝ := (Finset.Icc 1 n).image (chebyshevCosNode n)
        have hS_inj : Set.InjOn (chebyshevCosNode n) (Finset.Icc 1 n) := by
          intro i hi j hj hij
          simp only [Finset.coe_Icc, mem_Icc] at hi hj
          rcases lt_trichotomy i j with hlt | heq' | hgt
          · exact absurd hij (chebyshevCosNode_strictAnti n (Nat.le_succ_of_le hj.2) hlt).ne'
          · exact heq'
          · exact absurd hij.symm (chebyshevCosNode_strictAnti n (Nat.le_succ_of_le hi.2) hgt).ne'
        have hS_card : S.card = n := by
          rw [Finset.card_image_of_injOn hS_inj, Nat.card_Icc]
          omega
        have hS_sub : S ⊆ R.roots.toFinset := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨m, hm, rfl⟩
          rw [Finset.mem_Icc] at hm
          rw [Multiset.mem_toFinset, Polynomial.mem_roots hR_ne, Polynomial.IsRoot.def]
          simp only [R, eval_sub, eval_mul, eval_C]
          rw [hP_roots m hm.1 hm.2, chebyshevMonicU_eval_cosNode n m hm.1 hm.2, mul_zero, sub_zero]
        have hcard_le : n ≤ R.natDegree := by
          calc n = S.card := hS_card.symm
            _ ≤ R.roots.toFinset.card := Finset.card_le_card hS_sub
            _ ≤ R.roots.card := Multiset.toFinset_card_le _
            _ ≤ R.natDegree := Polynomial.card_roots' R
        omega
    have hP_eq : P = C (P.coeff n) * chebyshevMonicU n := sub_eq_zero.mp hR_zero
    refine ⟨P.coeff n * (1 / 2 : ℝ) ^ n, ?_⟩
    conv_lhs => rw [hP_eq, chebyshevMonicU, ← mul_assoc, ← C_mul]
  · rintro ⟨c, rfl⟩
    have hrew : C c * U ℝ n = C (c * (2 : ℝ) ^ n) * chebyshevMonicU n := by
      rw [chebyshevMonicU, ← mul_assoc, ← C_mul]
      have : c * (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = c := by
        have h1 : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
        linear_combination (norm := ring) c * h1
      rw [this]
    rw [hrew]
    have hdeg : (C (c * (2 : ℝ) ^ n) * chebyshevMonicU n).natDegree ≤ n := by
      calc (C (c * (2 : ℝ) ^ n) * chebyshevMonicU n).natDegree
          ≤ (chebyshevMonicU n).natDegree := natDegree_C_mul_le _ _
        _ = n := natDegree_chebyshevMonicU n
    rw [intervalIntegral_abs_iteratedDeriv_poly n _ hdeg, firstBestConstant]
    have hcoeff : (C (c * (2 : ℝ) ^ n) * chebyshevMonicU n).coeff n = c * (2 : ℝ) ^ n := by
      rw [coeff_C_mul, coeff_chebyshevMonicU_self, mul_one]
    rw [hcoeff]
    have heval : (fun y => |(C (c * (2 : ℝ) ^ n) * chebyshevMonicU n).eval y|) =
        fun y => |c * (2 : ℝ) ^ n| * |(chebyshevMonicU n).eval y| := by
      ext y
      simp only [eval_mul, eval_C, abs_mul]
    rw [heval, intervalIntegral.integral_const_mul, intervalIntegral_abs_chebyshevMonicU]
    have h1 : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
    linear_combination (norm := ring) -2 * (n.factorial : ℝ) * |c * (2 : ℝ) ^ n| * h1

end SharpL1.Analysis
