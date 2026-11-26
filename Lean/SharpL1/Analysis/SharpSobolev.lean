module

public import SharpL1.Analysis.MovingOperator
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

/-!
# Sharp higher-order `L¹` Sobolev interpolation inequality (Claim 2 & Theorem 1)

This module formalizes Claim 2 (`clm:sharp`) and Theorem 1 (`thm:full`) of
`chebyshev_L1_complete.tex` for every order `n = k + 1 ≥ 1`:

1. **Coercion from `C^{n+1}`**: `SobolevW1.ofContDiffOn` and `SobolevW1.ofContDiff`.
2. **Upper bound on `[-1, 1]` and `[a, b]`**: assuming `∀ t ∈ [-1, 1], E_n(t) ≤ b_n`,
   for every `F : SobolevW1 (n + 1) a b f` (`a < b`, `L = b - a`),
   `‖f^(n)‖_{L¹[a,b]} ≤ 4^n * n! * L^(-n) * ‖f‖_{L¹[a,b]} + (L/2) * b_n * ‖f^(n+1)‖_{L¹[a,b]}`.
3. **Sharpness of `A_n`** (`sharp_firstConstant_Icc_le`): even on `C^∞([a, b])`, the first
   constant cannot be reduced below `4^n * n! * L^(-n)`.
4. **Sharpness of `B_n = E_n(0)`** (Claim 2, `sharp_secondConstant_unit_le` &
   `sharp_secondConstant_Icc_le`): fixing `A_n`, even on `C^∞([a, b])`, the second constant
   cannot be reduced below `(L/2) * E_n(t)` for any `t ∈ (-1, 1)` (in particular `t = 0`).
5. **`C^{n+1}([a, b])` equality characterization** (Theorem 1,
   `sharp_sobolev_contDiffOn_Icc_eq_iff`): assuming `E_n(t) < E_n(0)` for `t ≠ 0`, equality
   holds for `f ∈ C^{n+1}([a, b])` if and only if
   `∀ x ∈ [a, b], f x = c * U_n((2x - a - b)/(b - a))` for some `c : ℝ`.
-/

namespace SharpL1.Analysis

open Polynomial MeasureTheory Set Filter Topology
open Polynomial.Chebyshev (U)
open scoped ContDiff

private lemma natCast_lt_infty (m : ℕ) : (m : WithTop ℕ∞) < ∞ :=
  WithTop.coe_lt_coe.mpr (ENat.coe_lt_top m)

private lemma natCast_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  (natCast_lt_infty m).le

/-! ### Coercions from `ContDiff` / `ContDiffOn` into `SobolevW1` -/

/-- Any globally `C^m` function belongs to `SobolevW1 m a b f` for `a ≤ b`. -/
noncomputable def SobolevW1.ofContDiff {m : ℕ} {a b : ℝ} (_hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ m f) : SobolevW1 m a b f where
  d j := iteratedDeriv j f
  d_zero _ _ := by simp
  continuousOn_d j hj :=
    (hf.continuous_iteratedDeriv j (by exact_mod_cast hj.le)).continuousOn
  integrable_top :=
    (hf.continuous_iteratedDeriv m le_rfl).integrableOn_Icc
  ftc j hj x _hx := by
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := iteratedDeriv j f) (f' := iteratedDeriv (j + 1) f) (a := a) (b := x)
      (fun y _ => by
        rw [iteratedDeriv_succ]
        exact (hf.differentiable_iteratedDeriv j (by exact_mod_cast hj) y).hasDerivAt)
      ((hf.continuous_iteratedDeriv (j + 1) (by exact_mod_cast Nat.succ_le_of_lt hj)).intervalIntegrable _ _)
    exact hFTC.symm

/-- Any `ContDiffOn ℝ m f (Icc a b)` function (`a < b`) belongs to `SobolevW1 m a b f`,
with derivatives `d j = iteratedDerivWithin j f (Icc a b)`. -/
noncomputable def SobolevW1.ofContDiffOn {m : ℕ} {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ m f (Icc a b)) : SobolevW1 m a b f where
  d j := iteratedDerivWithin j f (Icc a b)
  d_zero _ _ := by simp
  continuousOn_d j hj :=
    hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hj.le) (uniqueDiffOn_Icc hab)
  integrable_top :=
    (hf.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Icc hab)).integrableOn_Icc
  ftc j hj x hx := by
    have hcont_j : ContinuousOn (iteratedDerivWithin j f (Icc a b)) (Icc a x) :=
      (hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hj.le)
        (uniqueDiffOn_Icc hab)).mono (Icc_subset_Icc le_rfl hx.2)
    have hcont_j1 : ContinuousOn (iteratedDerivWithin (j + 1) f (Icc a b)) (Icc a x) :=
      (hf.continuousOn_iteratedDerivWithin (by exact_mod_cast Nat.succ_le_of_lt hj)
        (uniqueDiffOn_Icc hab)).mono (Icc_subset_Icc le_rfl hx.2)
    have hderiv : ∀ y ∈ Ioo a x,
        HasDerivAt (iteratedDerivWithin j f (Icc a b))
          (iteratedDerivWithin (j + 1) f (Icc a b) y) y := by
      intro y hy
      have hy_Ioo : y ∈ Ioo a b := ⟨hy.1, lt_of_lt_of_le hy.2 hx.2⟩
      have hnhds : Icc a b ∈ 𝓝 y := Icc_mem_nhds hy_Ioo.1 hy_Ioo.2
      have hdiff_w : DifferentiableWithinAt ℝ (iteratedDerivWithin j f (Icc a b)) (Icc a b) y :=
        hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hj) (uniqueDiffOn_Icc hab)
          y (Ioo_subset_Icc_self hy_Ioo)
      have hhas_w : HasDerivWithinAt (iteratedDerivWithin j f (Icc a b))
          (iteratedDerivWithin (j + 1) f (Icc a b) y) (Icc a b) y := by
        rw [iteratedDerivWithin_succ]
        exact hdiff_w.hasDerivWithinAt
      exact hhas_w.hasDerivAt hnhds
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1 hcont_j hderiv
      (hcont_j1.intervalIntegrable_of_Icc hx.1)
    exact hFTC.symm

/-! ### Affine rescaling from `[a, b]` to `[-1, 1]` -/

/-- Affine map `φ(u) = (a + b) / 2 + ((b - a) / 2) * u` sending `[-1, 1]` onto `[a, b]`. -/
noncomputable def affineToIcc (a b u : ℝ) : ℝ :=
  (a + b) / 2 + (b - a) / 2 * u

theorem affineToIcc_neg_one (a b : ℝ) : affineToIcc a b (-1) = a := by
  unfold affineToIcc; ring

theorem affineToIcc_one (a b : ℝ) : affineToIcc a b 1 = b := by
  unfold affineToIcc; ring

theorem affineToIcc_inv (a b x : ℝ) (hab : a < b) :
    affineToIcc a b ((2 * x - a - b) / (b - a)) = x := by
  have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  unfold affineToIcc
  field_simp [hne]
  ring

theorem affineToIcc_mem_Icc {a b u : ℝ} (hab : a ≤ b) (hu : u ∈ Icc (-1 : ℝ) 1) :
    affineToIcc a b u ∈ Icc a b := by
  unfold affineToIcc
  constructor <;> nlinarith [hu.1, hu.2]

theorem inv_affineToIcc_mem_Icc {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    (2 * x - a - b) / (b - a) ∈ Icc (-1 : ℝ) 1 := by
  have hpos : 0 < b - a := sub_pos.mpr hab
  constructor
  · rw [le_div_iff₀ hpos]; linarith [hx.1]
  · rw [div_le_iff₀ hpos]; linarith [hx.2]

/-- Linear change of variables `y = affineToIcc a b u` for any function `g : ℝ → ℝ`. -/
theorem intervalIntegral_comp_affineToIcc {a b u₁ u₂ : ℝ} (hab : a < b) (g : ℝ → ℝ) :
    ∫ u in u₁..u₂, g (affineToIcc a b u) =
      ((b - a) / 2)⁻¹ * ∫ y in affineToIcc a b u₁..affineToIcc a b u₂, g y := by
  have hc : (b - a) / 2 ≠ 0 := by linarith
  have h := intervalIntegral.integral_comp_mul_add (a := u₁) (b := u₂)
    (c := (b - a) / 2) (d := (a + b) / 2) g hc
  have hfun : (fun u => g (affineToIcc a b u)) = fun u => g ((b - a) / 2 * u + (a + b) / 2) := by
    ext u; unfold affineToIcc; ring_nf
  have hlo : (b - a) / 2 * u₁ + (a + b) / 2 = affineToIcc a b u₁ := by unfold affineToIcc; ring
  have hhi : (b - a) / 2 * u₂ + (a + b) / 2 = affineToIcc a b u₂ := by unfold affineToIcc; ring
  rw [hfun, h, hlo, hhi, smul_eq_mul]

/-- Rescale `F : SobolevW1 m a b f` (`a < b`) to `[-1, 1]`. -/
noncomputable def SobolevW1.rescaleToUnit {m : ℕ} {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (F : SobolevW1 m a b f) :
    SobolevW1 m (-1) 1 (fun u => f (affineToIcc a b u)) where
  d j u := ((b - a) / 2) ^ j * F.d j (affineToIcc a b u)
  d_zero u hu := by
    simp [F.d_zero (affineToIcc a b u) (affineToIcc_mem_Icc hab.le hu)]
  continuousOn_d j hj := by
    have hphi : Continuous (fun u => affineToIcc a b u) := by unfold affineToIcc; fun_prop
    exact continuousOn_const.mul ((F.continuousOn_d j hj).comp hphi.continuousOn
      (fun u hu => affineToIcc_mem_Icc hab.le hu))
  integrable_top := by
    have hL : 0 < b - a := sub_pos.mpr hab
    have hpos : 0 < (b - a) / 2 := by linarith
    have himg : (fun u => affineToIcc a b u) '' Icc (-1 : ℝ) 1 = Icc a b := by
      ext y; constructor
      · rintro ⟨u, hu, rfl⟩; exact affineToIcc_mem_Icc hab.le hu
      · intro hy
        exact ⟨(2 * y - a - b) / (b - a), inv_affineToIcc_mem_Icc hab hy, affineToIcc_inv a b y hab⟩
    have hderiv : ∀ u ∈ Icc (-1 : ℝ) 1,
        HasDerivWithinAt (fun s => affineToIcc a b s) ((b - a) / 2) (Icc (-1 : ℝ) 1) u := by
      intro u _
      have h1 : HasDerivAt (fun s => (a + b) / 2 + (b - a) / 2 * s) ((b - a) / 2) u := by
        simpa using ((hasDerivAt_id u).const_mul ((b - a) / 2)).const_add ((a + b) / 2)
      exact h1.hasDerivWithinAt
    have hinj : InjOn (fun s => affineToIcc a b s) (Icc (-1 : ℝ) 1) := by
      intro u₁ _ u₂ _ h
      unfold affineToIcc at h
      nlinarith
    have hint1 : IntegrableOn (fun u => ((b - a) / 2) * F.d m (affineToIcc a b u))
        (Icc (-1 : ℝ) 1) volume := by
      have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc hderiv hinj
        (F.d m)
      rw [himg] at hiff
      have h2 := hiff.mp F.integrable_top
      simpa [smul_eq_mul, abs_of_pos hpos] using h2
    have hrew : (fun u => ((b - a) / 2) ^ m * F.d m (affineToIcc a b u)) =
        fun u => (((b - a) / 2) ^ m / ((b - a) / 2)) *
          (((b - a) / 2) * F.d m (affineToIcc a b u)) := by
      ext u; field_simp [hpos.ne', hL.ne']
    rw [hrew]
    exact hint1.const_mul _
  ftc j hj u hu := by
    have hL : 0 < b - a := sub_pos.mpr hab
    have hpos : 0 < (b - a) / 2 := by linarith
    have h1 := F.ftc j hj (affineToIcc a b u) (affineToIcc_mem_Icc hab.le hu)
    rw [intervalIntegral.integral_const_mul, intervalIntegral_comp_affineToIcc hab (F.d (j + 1)),
      affineToIcc_neg_one, ← h1]
    rw [pow_succ]
    field_simp [hpos.ne', hL.ne']

theorem SobolevW1.rescaleToUnit_L1 {m : ℕ} {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (F : SobolevW1 m a b f) (j : ℕ) :
    ∫ u in (-1 : ℝ)..1, |(F.rescaleToUnit hab).d j u| =
      ((b - a) / 2) ^ j * ((b - a) / 2)⁻¹ * ∫ y in a..b, |F.d j y| := by
  have hpos : 0 < (b - a) / 2 := by linarith
  have hfun : (fun u => |(F.rescaleToUnit hab).d j u|) =
      fun u => ((b - a) / 2) ^ j * |F.d j (affineToIcc a b u)| := by
    ext u
    simp only [SobolevW1.rescaleToUnit, abs_mul, abs_of_pos (pow_pos hpos j)]
  rw [hfun, intervalIntegral.integral_const_mul,
    intervalIntegral_comp_affineToIcc hab (fun y => |F.d j y|),
    affineToIcc_neg_one, affineToIcc_one]
  ring

/-! ### Sharp upper bound on `[-1, 1]` and `[a, b]` -/

/-- **Sharp `L¹` Sobolev interpolation inequality on `[-1, 1]`** (conditional on the center
maximum bound `E_n(t) ≤ E_n(0)`):
`‖F^(n)‖_{L¹[-1,1]} ≤ 2^n * n! * ‖F‖_{L¹[-1,1]} + b_n * ‖F^(n+1)‖_{L¹[-1,1]}`. -/
theorem sharp_sobolev_unit_le (k : ℕ)
    (hmax : ∀ t ∈ Icc (-1 : ℝ) 1,
      explicitError (k + 1) (orderedNode k t) t ≤ centerBestConstant (k + 1))
    {f : ℝ → ℝ} (F : SobolevW1 (k + 2) (-1) 1 f) :
    ∫ x in (-1 : ℝ)..1, |F.d (k + 1) x| ≤
      firstBestConstant (k + 1) * (∫ y in (-1 : ℝ)..1, |f y|) +
        centerBestConstant (k + 1) * (∫ t in (-1 : ℝ)..1, |F.d (k + 2) t|) := by
  have hf_int : IntegrableOn f (Icc (-1 : ℝ) 1) volume :=
    (F.continuousOn_d 0 (Nat.zero_lt_succ _)).integrableOn_Icc.congr_fun
      (fun x hx => F.d_zero x hx) measurableSet_Icc
  have hT_int : IntervalIntegrable (movingOperator k f) volume (-1) 1 :=
    intervalIntegrable_movingOperator k hf_int
  have hd_int : IntervalIntegrable (F.d (k + 1)) volume (-1) 1 :=
    (F.continuousOn_d (k + 1) (Nat.lt_succ_self _)).intervalIntegrable_of_Icc (by norm_num)
  have htri : ∫ x in (-1 : ℝ)..1, |F.d (k + 1) x| ≤
      (∫ x in (-1 : ℝ)..1, |movingOperator k f x|) +
        ∫ x in (-1 : ℝ)..1, |F.d (k + 1) x - movingOperator k f x| := by
    rw [← intervalIntegral.integral_add hT_int.abs (hd_int.sub hT_int).abs]
    apply intervalIntegral.integral_mono_on (by norm_num) hd_int.abs
      (hT_int.abs.add (hd_int.sub hT_int).abs)
    intro x _
    calc |F.d (k + 1) x| = |movingOperator k f x + (F.d (k + 1) x - movingOperator k f x)| := by
            ring_nf
      _ ≤ |movingOperator k f x| + |F.d (k + 1) x - movingOperator k f x| := abs_add_le _ _
  have h1 := movingOperator_L1_le k hf_int
  have h2 := F.L1_deriv_sub_movingOperator_le k
  have h3 : ∫ t in (-1 : ℝ)..1, explicitError (k + 1) (orderedNode k t) t * |F.d (k + 2) t| ≤
      centerBestConstant (k + 1) * ∫ t in (-1 : ℝ)..1, |F.d (k + 2) t| := by
    rw [← intervalIntegral.integral_const_mul]
    have hE_cont : Continuous (fun t => explicitError (k + 1) (orderedNode k t) t) := by
      unfold explicitError
      have hc : ∀ j : Fin (k + 2), Continuous (fun t => orderedNode k t j) :=
        fun j => continuous_orderedNode k j
      fun_prop
    have hE_int : IntervalIntegrable
        (fun t => explicitError (k + 1) (orderedNode k t) t * |F.d (k + 2) t|) volume (-1) 1 := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hE_cont.continuousOn
      refine (F.integrable_top.abs.const_mul C).mono'
        ((hE_cont.continuousOn.aestronglyMeasurable measurableSet_Icc).mul
          F.integrable_top.abs.aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [Real.norm_eq_abs, abs_mul, abs_abs]
      exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hC t ht)
        (abs_nonneg _)
    have hB_int : IntervalIntegrable
        (fun t => centerBestConstant (k + 1) * |F.d (k + 2) t|) volume (-1) 1 :=
      ((intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr
        F.integrable_top.abs).const_mul _
    apply intervalIntegral.integral_mono_on (by norm_num) hE_int hB_int
    intro t ht
    exact mul_le_mul_of_nonneg_right (hmax t ht) (abs_nonneg _)
  linarith

/-- **Sharp `L¹` Sobolev interpolation inequality on any interval `[a, b]`** (`L = b - a > 0`,
order `n = k + 1`):
`‖f^(n)‖_{L¹[a,b]} ≤ 4^n * n! * L^(-n) * ‖f‖_{L¹[a,b]} + (L / 2) * b_n * ‖f^(n+1)‖_{L¹[a,b]}`. -/
theorem sharp_sobolev_Icc_le (k : ℕ) {a b : ℝ} (hab : a < b)
    (hmax : ∀ t ∈ Icc (-1 : ℝ) 1,
      explicitError (k + 1) (orderedNode k t) t ≤ centerBestConstant (k + 1))
    {f : ℝ → ℝ} (F : SobolevW1 (k + 2) a b f) :
    ∫ x in a..b, |F.d (k + 1) x| ≤
      (4 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * (b - a) ^ (-((k + 1 : ℕ) : ℤ)) *
          (∫ y in a..b, |f y|) +
        ((b - a) / 2) * centerBestConstant (k + 1) * (∫ t in a..b, |F.d (k + 2) t|) := by
  let G := F.rescaleToUnit hab
  have hunit := sharp_sobolev_unit_le k hmax G
  have h0 : ∫ u in (-1 : ℝ)..1, |f (affineToIcc a b u)| =
      ((b - a) / 2)⁻¹ * ∫ y in a..b, |f y| := by
    rw [intervalIntegral_comp_affineToIcc hab (fun y => |f y|), affineToIcc_neg_one, affineToIcc_one]
  have hn := F.rescaleToUnit_L1 hab (k + 1)
  have hn1 := F.rescaleToUnit_L1 hab (k + 2)
  rw [h0, hn, hn1] at hunit
  have hL : 0 < b - a := sub_pos.mpr hab
  have hL2 : 0 < (b - a) / 2 := by linarith
  have hpow_pos : 0 < ((b - a) / 2) ^ (k + 1) * ((b - a) / 2)⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_left hunit (le_of_lt (inv_pos.mpr hpow_pos))
  refine le_trans ?_ (hmul.trans_eq ?_)
  · rw [← mul_assoc, inv_mul_cancel₀ hpow_pos.ne', one_mul]
  · unfold firstBestConstant
    rw [zpow_neg, zpow_natCast, mul_add]
    have hterm1 :
        (((b - a) / 2) ^ (k + 1) * ((b - a) / 2)⁻¹)⁻¹ *
          ((2 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) *
            (((b - a) / 2)⁻¹ * ∫ y in a..b, |f y|)) =
        (4 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * ((b - a) ^ (k + 1))⁻¹ *
          ∫ y in a..b, |f y| := by
      have h4 : (4 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (k + 1) := by
        rw [← mul_pow]; norm_num
      rw [h4, div_pow]
      field_simp [hL.ne']
    have hterm2 :
        (((b - a) / 2) ^ (k + 1) * ((b - a) / 2)⁻¹)⁻¹ *
          (centerBestConstant (k + 1) *
            (((b - a) / 2) ^ (k + 2) * ((b - a) / 2)⁻¹ * ∫ t in a..b, |F.d (k + 2) t|)) =
        (b - a) / 2 * centerBestConstant (k + 1) * ∫ t in a..b, |F.d (k + 2) t| := by
      rw [pow_succ ((b - a) / 2) (k + 1)]
      field_simp [hL.ne']
    rw [hterm1, hterm2]

/-- Corollary for `ContDiffOn ℝ (k + 2) f (Icc a b)`. -/
theorem sharp_sobolev_contDiffOn_Icc_le (k : ℕ) {a b : ℝ} (hab : a < b)
    (hmax : ∀ t ∈ Icc (-1 : ℝ) 1,
      explicitError (k + 1) (orderedNode k t) t ≤ centerBestConstant (k + 1))
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ (k + 2) f (Icc a b)) :
    ∫ x in a..b, |iteratedDerivWithin (k + 1) f (Icc a b) x| ≤
      (4 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * (b - a) ^ (-((k + 1 : ℕ) : ℤ)) *
          (∫ y in a..b, |f y|) +
        ((b - a) / 2) * centerBestConstant (k + 1) *
          (∫ t in a..b, |iteratedDerivWithin (k + 2) f (Icc a b) t|) :=
  sharp_sobolev_Icc_le k hab hmax (SobolevW1.ofContDiffOn hab hf)

/-! ### Sharpness of the first constant `A_n` even on `C^∞([a, b])` -/

/-- Even restricted to `C^∞` functions on `[a, b]`, no constant `A < 4^n * n! * L^(-n)` can hold
for any `B : ℝ`. -/
theorem sharp_firstConstant_Icc_le (n : ℕ) {a b : ℝ} (hab : a < b) (A B : ℝ)
    (hAB : ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f →
      ∫ x in a..b, |iteratedDeriv n f x| ≤
        A * (∫ y in a..b, |f y|) + B * (∫ t in a..b, |iteratedDeriv (n + 1) f t|)) :
    (4 : ℝ) ^ n * (n.factorial : ℝ) * (b - a) ^ (-(n : ℤ)) ≤ A := by
  have hL : 0 < b - a := sub_pos.mpr hab
  have hL2 : 0 < (b - a) / 2 := by linarith
  let linP : ℝ[X] := C (2 / (b - a)) * X - C ((a + b) / (b - a))
  let P : ℝ[X] := (chebyshevMonicU n).comp linP
  have hlin_eval : ∀ x : ℝ, linP.eval x = (2 * x - a - b) / (b - a) := by
    intro x; simp only [linP, eval_sub, eval_mul, eval_C, eval_X]; ring
  have hP_eval : ∀ u : ℝ, P.eval (affineToIcc a b u) = (chebyshevMonicU n).eval u := by
    intro u
    rw [eval_comp, hlin_eval]
    have harg : (2 * affineToIcc a b u - a - b) / (b - a) = u := by
      unfold affineToIcc; field_simp [hL.ne']; ring
    rw [harg]
  have hP_deg : P.natDegree ≤ n := by
    calc P.natDegree ≤ (chebyshevMonicU n).natDegree * linP.natDegree := natDegree_comp_le
      _ ≤ n * 1 := by
        rw [natDegree_chebyshevMonicU]
        apply Nat.mul_le_mul_left
        calc linP.natDegree ≤ max (C (2 / (b - a)) * X).natDegree (C ((a + b) / (b - a))).natDegree :=
              natDegree_sub_le _ _
          _ ≤ 1 := by
            simp only [natDegree_C, max_eq_left (Nat.zero_le _)]
            exact (natDegree_C_mul_le _ _).trans (by simp)
      _ = n := mul_one n
  have hlin_lc : linP.coeff 1 = 2 / (b - a) := by
    simp [linP]
  have hlin_deg : linP.natDegree = 1 := by
    apply le_antisymm
    · calc linP.natDegree ≤ max (C (2 / (b - a)) * X).natDegree (C ((a + b) / (b - a))).natDegree :=
            natDegree_sub_le _ _
        _ ≤ 1 := by
          simp only [natDegree_C, max_eq_left (Nat.zero_le _)]
          exact (natDegree_C_mul_le _ _).trans (by simp)
    · apply Polynomial.le_natDegree_of_ne_zero
      rw [hlin_lc]; positivity
  have hP_coeff : P.coeff n = (2 / (b - a)) ^ n := by
    have hcomp_deg : P.natDegree = n := by
      rw [Polynomial.natDegree_comp, natDegree_chebyshevMonicU, hlin_deg, mul_one]
    have hcomp_lc : P.leadingCoeff = (chebyshevMonicU n).leadingCoeff * linP.leadingCoeff ^ n := by
      rw [Polynomial.leadingCoeff_comp (by rw [hlin_deg]; omega), natDegree_chebyshevMonicU]
    rw [leadingCoeff, hcomp_deg, monic_chebyshevMonicU n, one_mul, leadingCoeff, hlin_deg,
      hlin_lc] at hcomp_lc
    exact hcomp_lc
  have hP_smooth : ContDiff ℝ ∞ (fun x => P.eval x) := by
    simpa [Polynomial.aeval_def] using P.contDiff_aeval (𝕜 := ℝ) ∞
  have hbound := hAB (fun x => P.eval x) hP_smooth
  have hdn : ∀ x : ℝ, iteratedDeriv n (fun y => P.eval y) x =
      (n.factorial : ℝ) * (2 / (b - a)) ^ n := by
    intro x
    rw [iteratedDeriv_polynomial_eval_of_natDegree_le P n hP_deg x, hP_coeff]
  have hdn1 : ∀ x : ℝ, iteratedDeriv (n + 1) (fun y => P.eval y) x = 0 := by
    intro x
    rw [iteratedDeriv_polynomial_eval_of_natDegree_le P (n + 1) (Nat.le_succ_of_le hP_deg) x,
      Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hP_deg), mul_zero]
  simp_rw [hdn, hdn1, abs_zero, intervalIntegral.integral_zero, mul_zero, add_zero] at hbound
  rw [intervalIntegral.integral_const, smul_eq_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (n.factorial : ℝ) * (2 / (b - a)) ^ n)] at hbound
  have hint_P : ∫ y in a..b, |P.eval y| = (b - a) * (1 / 2 : ℝ) ^ n := by
    have hsub := intervalIntegral_comp_affineToIcc hab (fun y => |P.eval y|) (u₁ := -1) (u₂ := 1)
    rw [affineToIcc_neg_one, affineToIcc_one] at hsub
    have hleft : ∫ u in (-1 : ℝ)..1, |P.eval (affineToIcc a b u)| = 2 * (1 / 2 : ℝ) ^ n := by
      simp_rw [hP_eval]
      exact intervalIntegral_abs_chebyshevMonicU n
    rw [hleft] at hsub
    have hmul := congrArg (fun z => ((b - a) / 2) * z) hsub
    rw [← mul_assoc ((b - a) / 2) ((b - a) / 2)⁻¹, mul_inv_cancel₀ hL2.ne', one_mul] at hmul
    linarith [hmul.symm]
  rw [hint_P] at hbound
  have hpos_rhs : 0 < (b - a) * (1 / 2 : ℝ) ^ n := by positivity
  rw [zpow_neg, zpow_natCast]
  have h4 : (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by rw [← mul_pow]; norm_num
  have hident : ((4 : ℝ) ^ n * (n.factorial : ℝ) * ((b - a) ^ n)⁻¹) *
      ((b - a) * (1 / 2 : ℝ) ^ n) = (b - a) * ((n.factorial : ℝ) * (2 / (b - a)) ^ n) := by
    rw [h4, div_pow, div_pow, one_pow]
    field_simp [hL.ne']
  nlinarith

/-! ### Sharpness of the second constant `B_n = E_n(0)` (Claim 2 `clm:sharp`) -/

/-- The degree-`≤ k+1` Lagrange interpolant `P_t` of `h_t` at `orderedNode k t`. -/
noncomputable def truncLagrangePoly (k : ℕ) (t : ℝ) : ℝ[X] :=
  Lagrange.interpolate Finset.univ (orderedNode k t)
    (fun j => normTruncatedPower (k + 1) t (orderedNode k t j))

/-- The extremal test function `G_t(y) = h_t(y) - P_t(y)` (with distributional `(n+1)`-th
derivative `δ_t`). -/
noncomputable def extremalTruncDiff (k : ℕ) (t y : ℝ) : ℝ :=
  normTruncatedPower (k + 1) t y - (truncLagrangePoly k t).eval y

private theorem truncLagrangePoly_natDegree_le (k : ℕ) (t : ℝ) :
    (truncLagrangePoly k t).natDegree ≤ k + 1 := by
  have hlt := Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin (k + 2))))
    (r := fun j => normTruncatedPower (k + 1) t (orderedNode k t j))
    (orderedNode_strictMono k t).injective.injOn
  simp only [Finset.card_univ, Fintype.card_fin] at hlt
  by_cases h0 : truncLagrangePoly k t = 0
  · simp [h0]
  · unfold truncLagrangePoly at h0 ⊢
    rw [Polynomial.degree_eq_natDegree h0] at hlt
    exact Nat.lt_succ_iff.mp (by exact_mod_cast hlt)

private theorem truncLagrangePoly_eval_node (k : ℕ) (t : ℝ) (j : Fin (k + 2)) :
    (truncLagrangePoly k t).eval (orderedNode k t j) =
      normTruncatedPower (k + 1) t (orderedNode k t j) :=
  Lagrange.eval_interpolate_at_node _ (orderedNode_strictMono k t).injective.injOn
    (Finset.mem_univ j)

private theorem truncLagrangePoly_iteratedDeriv (k : ℕ) {t : ℝ} (ht : |t| < 1) (x : ℝ) :
    iteratedDeriv (k + 1) (fun y => (truncLagrangePoly k t).eval y) x =
      movingOperator k (normTruncatedPower (k + 1) t) t := by
  rw [iteratedDeriv_polynomial_eval_of_natDegree_le _ (k + 1) (truncLagrangePoly_natDegree_le k t) x,
    ← iteratedDeriv_polynomial_eval_of_natDegree_le _ (k + 1) (truncLagrangePoly_natDegree_le k t) t,
    ← movingOperator_poly k (truncLagrangePoly k t) (truncLagrangePoly_natDegree_le k t) ht]
  unfold movingOperator
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  dsimp only
  rw [truncLagrangePoly_eval_node]

/-- Lagrange interpolation remainder for `G_t(y) = h_t(y) - P_t(y)`:
for any `y` distinct from all nodes `u_j(t)`, `G_t(y)` has the same sign as
`∏ j, (y - u_j(t))` (up to a nonnegative `(n+1)`-th divided difference factor). -/
theorem extremalTruncDiff_eq_divDiff_mul_prod (k : ℕ) (t y : ℝ)
    (hy : ∀ j : Fin (k + 2), y ≠ orderedNode k t j) :
    ∃ c : ℝ, 0 ≤ c ∧
      extremalTruncDiff k t y = c * ∏ j : Fin (k + 2), (y - orderedNode k t j) := by
  let a : Fin (k + 3) → ℝ := Fin.snoc (orderedNode k t) y
  have ha_inj : Function.Injective a := by
    intro i j hij
    cases i using Fin.lastCases with
    | last =>
      cases j using Fin.lastCases with
      | last => rfl
      | cast j' =>
        simp only [a, Fin.snoc_last, Fin.snoc_castSucc] at hij
        exact absurd hij (hy j')
    | cast i' =>
      cases j using Fin.lastCases with
      | last =>
        simp only [a, Fin.snoc_last, Fin.snoc_castSucc] at hij
        exact absurd hij.symm (hy i')
      | cast j' =>
        simp only [a, Fin.snoc_castSucc] at hij
        exact congrArg Fin.castSucc ((orderedNode_strictMono k t).injective hij)
  let c : ℝ := barycentricDividedDifferenceOn Finset.univ a
    (fun i => normTruncatedPower (k + 1) t (a i))
  have hc_nonneg : 0 ≤ c := by
    have hcard : (Finset.univ : Finset (Fin (k + 3))).card = k + 3 := by simp
    have hnn := barycentric_truncatedPower_higher_nonneg (Finset.univ : Finset (Fin (k + 3)))
      ha_inj.injOn (by omega) t
    have hsub : (Finset.univ : Finset (Fin (k + 3))).card - 2 = k + 1 := by omega
    rw [hsub] at hnn
    have hrew : c = barycentricDividedDifferenceOn Finset.univ a
        (fun i => truncatedPower (k + 1) t (a i)) / ((k + 1).factorial : ℝ) := by
      unfold c barycentricDividedDifferenceOn normTruncatedPower
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hrew]
    exact div_nonneg hnn (Nat.cast_nonneg _)
  have hP_dd : barycentricDividedDifferenceOn Finset.univ a
      (fun i => (truncLagrangePoly k t).eval (a i)) = 0 := by
    have hdeg : (truncLagrangePoly k t).degree < ((Finset.univ : Finset (Fin (k + 3))).card : WithBot ℕ) := by
      simp only [Finset.card_univ, Fintype.card_fin]
      exact lt_of_le_of_lt Polynomial.degree_le_natDegree
        (Nat.cast_lt.mpr (Nat.lt_succ_of_le (Nat.le_succ_of_le (truncLagrangePoly_natDegree_le k t))))
    rw [barycentricDividedDifferenceOn_eval_eq_coeff ha_inj.injOn _ hdeg]
    simp only [Finset.card_univ, Fintype.card_fin]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (Nat.lt_succ_of_le (truncLagrangePoly_natDegree_le k t))
  have hc_eq : c = extremalTruncDiff k t y *
      (∏ j : Fin (k + 2), (y - orderedNode k t j))⁻¹ := by
    have hdiff : c = barycentricDividedDifferenceOn Finset.univ a
        (fun i => extremalTruncDiff k t (a i)) := by
      have h1 : barycentricDividedDifferenceOn Finset.univ a
          (fun i => extremalTruncDiff k t (a i)) = c -
          barycentricDividedDifferenceOn Finset.univ a
            (fun i => (truncLagrangePoly k t).eval (a i)) := by
        unfold c barycentricDividedDifferenceOn extremalTruncDiff
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [h1, hP_dd, sub_zero]
    rw [hdiff]
    unfold barycentricDividedDifferenceOn
    rw [Finset.sum_eq_single (Fin.last (k + 2))]
    · simp only [a, Fin.snoc_last]
      congr 2
      symm
      refine Finset.prod_bij (fun (j : Fin (k + 2)) _ => j.castSucc) ?_ ?_ ?_ ?_
      · intro j _
        exact Finset.mem_erase.mpr ⟨Fin.castSucc_ne_last j, Finset.mem_univ _⟩
      · intro i₁ _ i₂ _ h
        exact Fin.castSucc_inj.mp h
      · intro i hi
        have hne : i ≠ Fin.last (k + 2) := (Finset.mem_erase.mp hi).1
        exact ⟨i.castPred hne, Finset.mem_univ _, Fin.castSucc_castPred i hne⟩
      · intro j _
        simp [Fin.snoc_castSucc]
    · intro i _ hne
      have hi : ∃ j : Fin (k + 2), i = j.castSucc :=
        ⟨i.castPred hne, (Fin.castSucc_castPred i hne).symm⟩
      rcases hi with ⟨j, rfl⟩
      simp [a, Fin.snoc_castSucc, extremalTruncDiff, truncLagrangePoly_eval_node]
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot
  have hprod_ne : (∏ j : Fin (k + 2), (y - orderedNode k t j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact sub_ne_zero.mpr (hy j)
  refine ⟨c, hc_nonneg, ?_⟩
  rw [hc_eq, mul_assoc, inv_mul_cancel₀ hprod_ne, mul_one]

/-- Sign structure of `G_t(u_j(x))` for `x > t`: every `ε_j * G_t(u_j(x)) ≥ 0`. -/
theorem altSign_mul_extremalTruncDiff_nonneg (k : ℕ) {t x : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hx : x ∈ Ioo (-1 : ℝ) 1) (htx : t < x) (j : Fin (k + 2)) :
    0 ≤ altSign (k + 1) j * extremalTruncDiff k t (orderedNode k x j) := by
  have hrel_le : ∀ i : Fin (k + 2), i ≤ j → orderedNode k t i < orderedNode k x j := by
    intro i hij
    calc orderedNode k t i ≤ orderedNode k t j := (orderedNode_strictMono k t).monotone hij
      _ < orderedNode k x j := orderedNode_strictMonoOn k j ht hx htx
  have hrel_gt : ∀ i : Fin (k + 2), j < i → orderedNode k x j < orderedNode k t i := by
    intro i hij
    have h1 : orderedNode k x j < chebyshevGrid k (j.val + 1) := (orderedNode_mem_Ioo k hx j).2
    have h2 : chebyshevGrid k (j.val + 1) ≤ chebyshevGrid k i.val := by
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hij) with heq | hlt
      · rw [Nat.succ_eq_add_one] at heq; rw [heq]
      · exact (chebyshevGrid_strictMono k
          (show (⟨j.val + 1, by omega⟩ : Fin (k + 3)) < ⟨i.val, by omega⟩ by
            simp [Fin.lt_def, hlt])).le
    have h3 : chebyshevGrid k i.val < orderedNode k t i := (orderedNode_mem_Ioo k ht i).1
    linarith
  have hne : ∀ i : Fin (k + 2), orderedNode k x j ≠ orderedNode k t i := by
    intro i
    rcases le_or_gt i j with hij | hij
    · exact (hrel_le i hij).ne'
    · exact (hrel_gt i hij).ne
  obtain ⟨c, hc, heq⟩ := extremalTruncDiff_eq_divDiff_mul_prod k t (orderedNode k x j) hne
  rw [heq]
  have hprod_sign : 0 < altSign (k + 1) j *
      ∏ i : Fin (k + 2), (orderedNode k x j - orderedNode k t i) := by
    let S_le := Finset.univ.filter (fun i : Fin (k + 2) => i ≤ j)
    let S_gt := Finset.univ.filter (fun i : Fin (k + 2) => j < i)
    have hdisj : Disjoint S_le S_gt := by
      rw [Finset.disjoint_left]; intro i h1 h2
      exact not_lt_of_ge (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    have hunion : (Finset.univ : Finset (Fin (k + 2))) = S_le ∪ S_gt := by
      ext i; simp only [S_le, S_gt, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun _ => le_or_gt i j, fun _ => trivial⟩
    have hcard : S_gt.card = k + 1 - j.val := by
      have hbij : S_gt.card = (Finset.Ico (j.val + 1) (k + 2)).card := by
        refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
        · intro i hi
          rw [Finset.mem_Ico]
          exact ⟨Nat.succ_le_of_lt (Finset.mem_filter.mp hi).2, i.isLt⟩
        · intro a _ b _ h; exact Fin.ext h
        · intro m hm; rw [Finset.mem_Ico] at hm
          exact ⟨⟨m, hm.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.lt_of_succ_le hm.1⟩, rfl⟩
      rw [hbij, Nat.card_Ico]; omega
    have hpos_le : 0 < ∏ i ∈ S_le, (orderedNode k x j - orderedNode k t i) :=
      Finset.prod_pos fun i hi => sub_pos.mpr (hrel_le i (Finset.mem_filter.mp hi).2)
    have hgt_eq : ∏ i ∈ S_gt, (orderedNode k x j - orderedNode k t i) =
        (-1 : ℝ) ^ S_gt.card * ∏ i ∈ S_gt, (orderedNode k t i - orderedNode k x j) := by
      have hterm : ∀ i ∈ S_gt, orderedNode k x j - orderedNode k t i =
          (-1 : ℝ) * (orderedNode k t i - orderedNode k x j) := fun _ _ => by ring
      rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_const]
    have hpos_gt : 0 < ∏ i ∈ S_gt, (orderedNode k t i - orderedNode k x j) :=
      Finset.prod_pos fun i hi => sub_pos.mpr (hrel_gt i (Finset.mem_filter.mp hi).2)
    rw [hunion, Finset.prod_union hdisj, hgt_eq, hcard]
    have hsq : altSign (k + 1) j * (-1 : ℝ) ^ (k + 1 - j.val) = 1 := altSign_sq (k + 1) j
    calc altSign (k + 1) j *
          ((∏ i ∈ S_le, (orderedNode k x j - orderedNode k t i)) *
            ((-1 : ℝ) ^ (k + 1 - j.val) * ∏ i ∈ S_gt, (orderedNode k t i - orderedNode k x j)))
        = (altSign (k + 1) j * (-1 : ℝ) ^ (k + 1 - j.val)) *
          ((∏ i ∈ S_le, (orderedNode k x j - orderedNode k t i)) *
            (∏ i ∈ S_gt, (orderedNode k t i - orderedNode k x j))) := by ring
      _ = (∏ i ∈ S_le, (orderedNode k x j - orderedNode k t i)) *
            (∏ i ∈ S_gt, (orderedNode k t i - orderedNode k x j)) := by rw [hsq, one_mul]
      _ > 0 := mul_pos hpos_le hpos_gt
  calc 0 ≤ c * (altSign (k + 1) j * ∏ i : Fin (k + 2), (orderedNode k x j - orderedNode k t i)) :=
        mul_nonneg hc hprod_sign.le
    _ = altSign (k + 1) j * (c * ∏ i : Fin (k + 2), (orderedNode k x j - orderedNode k t i)) := by
        ring

/-- Sign structure of `G_t(u_j(x))` for `x < t`: every `ε_j * G_t(u_j(x)) ≤ 0`. -/
theorem altSign_mul_extremalTruncDiff_nonpos (k : ℕ) {t x : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hx : x ∈ Ioo (-1 : ℝ) 1) (hxt : x < t) (j : Fin (k + 2)) :
    altSign (k + 1) j * extremalTruncDiff k t (orderedNode k x j) ≤ 0 := by
  have hrel_lt : ∀ i : Fin (k + 2), i < j → orderedNode k t i < orderedNode k x j := by
    intro i hij
    have h1 : orderedNode k t i < chebyshevGrid k (i.val + 1) := (orderedNode_mem_Ioo k ht i).2
    have h2 : chebyshevGrid k (i.val + 1) ≤ chebyshevGrid k j.val := by
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hij) with heq | hlt
      · rw [Nat.succ_eq_add_one] at heq; rw [heq]
      · exact (chebyshevGrid_strictMono k
          (show (⟨i.val + 1, by omega⟩ : Fin (k + 3)) < ⟨j.val, by omega⟩ by
            simp [Fin.lt_def, hlt])).le
    have h3 : chebyshevGrid k j.val < orderedNode k x j := (orderedNode_mem_Ioo k hx j).1
    linarith
  have hrel_ge : ∀ i : Fin (k + 2), j ≤ i → orderedNode k x j < orderedNode k t i := by
    intro i hij
    calc orderedNode k x j < orderedNode k t j := orderedNode_strictMonoOn k j hx ht hxt
      _ ≤ orderedNode k t i := (orderedNode_strictMono k t).monotone hij
  have hne : ∀ i : Fin (k + 2), orderedNode k x j ≠ orderedNode k t i := by
    intro i
    rcases lt_or_ge i j with hij | hij
    · exact (hrel_lt i hij).ne'
    · exact (hrel_ge i hij).ne
  obtain ⟨c, hc, heq⟩ := extremalTruncDiff_eq_divDiff_mul_prod k t (orderedNode k x j) hne
  rw [heq]
  have hprod_sign : altSign (k + 1) j *
      ∏ i : Fin (k + 2), (orderedNode k x j - orderedNode k t i) < 0 := by
    let S_lt := Finset.univ.filter (fun i : Fin (k + 2) => i < j)
    let S_ge := Finset.univ.filter (fun i : Fin (k + 2) => j ≤ i)
    have hdisj : Disjoint S_lt S_ge := by
      rw [Finset.disjoint_left]; intro i h1 h2
      exact not_lt_of_ge (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hunion : (Finset.univ : Finset (Fin (k + 2))) = S_lt ∪ S_ge := by
      ext i; simp only [S_lt, S_ge, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun _ => lt_or_ge i j, fun _ => trivial⟩
    have hcard : S_ge.card = k + 2 - j.val := by
      have hbij : S_ge.card = (Finset.Ico j.val (k + 2)).card := by
        refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
        · intro i hi
          rw [Finset.mem_Ico]
          exact ⟨(Finset.mem_filter.mp hi).2, i.isLt⟩
        · intro a _ b _ h; exact Fin.ext h
        · intro m hm; rw [Finset.mem_Ico] at hm
          exact ⟨⟨m, hm.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm.1⟩, rfl⟩
      rw [hbij, Nat.card_Ico]
    have hpos_lt : 0 < ∏ i ∈ S_lt, (orderedNode k x j - orderedNode k t i) :=
      Finset.prod_pos fun i hi => sub_pos.mpr (hrel_lt i (Finset.mem_filter.mp hi).2)
    have hge_eq : ∏ i ∈ S_ge, (orderedNode k x j - orderedNode k t i) =
        (-1 : ℝ) ^ S_ge.card * ∏ i ∈ S_ge, (orderedNode k t i - orderedNode k x j) := by
      have hterm : ∀ i ∈ S_ge, orderedNode k x j - orderedNode k t i =
          (-1 : ℝ) * (orderedNode k t i - orderedNode k x j) := fun _ _ => by ring
      rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_const]
    have hpos_ge : 0 < ∏ i ∈ S_ge, (orderedNode k t i - orderedNode k x j) :=
      Finset.prod_pos fun i hi => sub_pos.mpr (hrel_ge i (Finset.mem_filter.mp hi).2)
    rw [hunion, Finset.prod_union hdisj, hge_eq, hcard]
    have hexp : k + 2 - j.val = (k + 1 - j.val) + 1 := by omega
    have hneg1 : altSign (k + 1) j * (-1 : ℝ) ^ (k + 2 - j.val) = -1 := by
      rw [hexp, pow_succ]
      have hsq := altSign_sq (k + 1) j
      unfold altSign at hsq ⊢
      linarith
    calc altSign (k + 1) j *
          ((∏ i ∈ S_lt, (orderedNode k x j - orderedNode k t i)) *
            ((-1 : ℝ) ^ (k + 2 - j.val) * ∏ i ∈ S_ge, (orderedNode k t i - orderedNode k x j)))
        = (altSign (k + 1) j * (-1 : ℝ) ^ (k + 2 - j.val)) *
          ((∏ i ∈ S_lt, (orderedNode k x j - orderedNode k t i)) *
            (∏ i ∈ S_ge, (orderedNode k t i - orderedNode k x j))) := by ring
      _ = -((∏ i ∈ S_lt, (orderedNode k x j - orderedNode k t i)) *
            (∏ i ∈ S_ge, (orderedNode k t i - orderedNode k x j))) := by rw [hneg1]; ring
      _ < 0 := neg_lt_zero.mpr (mul_pos hpos_lt hpos_ge)
  calc altSign (k + 1) j * (c * ∏ i : Fin (k + 2), (orderedNode k x j - orderedNode k t i))
      = c * (altSign (k + 1) j * ∏ i : Fin (k + 2), (orderedNode k x j - orderedNode k t i)) := by
        ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc hprod_sign.le

/-- Exact identity for the unsmoothed extremal `G_t = h_t - P_t`:
`‖G_t^(n)‖_1 - A_n ‖G_t‖_1 = E_n(t)`. -/
theorem extremalTruncDiff_L1_identity (k : ℕ) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    (∫ x in (-1 : ℝ)..1,
      |(if t < x then (1 : ℝ) else 0) -
        iteratedDeriv (k + 1) (fun y => (truncLagrangePoly k t).eval y) x|) -
      firstBestConstant (k + 1) * (∫ y in (-1 : ℝ)..1, |extremalTruncDiff k t y|) =
      explicitError (k + 1) (orderedNode k t) t := by
  have ht_abs : |t| < 1 := abs_lt.mpr ht
  have ht_Icc : t ∈ Icc (-1 : ℝ) 1 := Ioo_subset_Icc_self ht
  set c_t := movingOperator k (normTruncatedPower (k + 1) t) t
  have hc_mem : 0 ≤ c_t ∧ c_t ≤ 1 := movingOperator_normTruncatedPower_mem_Icc k t ht_abs
  have hGn : ∫ x in (-1 : ℝ)..1,
      |(if t < x then (1 : ℝ) else 0) -
        iteratedDeriv (k + 1) (fun y => (truncLagrangePoly k t).eval y) x| =
      (1 - t) + 2 * t * c_t := by
    simp_rw [truncLagrangePoly_iteratedDeriv k ht_abs]
    have hleft : ∫ x in (-1 : ℝ)..t, |(if t < x then (1 : ℝ) else 0) - c_t| = (t + 1) * c_t := by
      have heq : ∫ x in (-1 : ℝ)..t, |(if t < x then (1 : ℝ) else 0) - c_t| =
          ∫ _x in (-1 : ℝ)..t, c_t := by
        rw [intervalIntegral.integral_of_le ht.1.le, intervalIntegral.integral_of_le ht.1.le,
          MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
        refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
        rw [if_neg (not_lt_of_gt hx.2), zero_sub, abs_neg, abs_of_nonneg hc_mem.1]
      rw [heq, intervalIntegral.integral_const, smul_eq_mul]; ring
    have hright : ∫ x in t..1, |(if t < x then (1 : ℝ) else 0) - c_t| = (1 - t) * (1 - c_t) := by
      have heq : ∫ x in t..1, |(if t < x then (1 : ℝ) else 0) - c_t| =
          ∫ _x in t..1, (1 - c_t) := by
        rw [intervalIntegral.integral_of_le ht.2.le, intervalIntegral.integral_of_le ht.2.le,
          MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
        refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
        rw [if_pos hx.1, abs_of_nonneg (sub_nonneg.mpr hc_mem.2)]
      rw [heq, intervalIntegral.integral_const, smul_eq_mul]
    have hi1 : IntervalIntegrable (fun x => |(if t < x then (1 : ℝ) else 0) - c_t|) volume (-1) t := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1.le]
      exact (integrableOn_const (C := c_t) (hs := measure_Ioo_lt_top.ne)).congr_fun (fun x hx => by
        rw [if_neg (not_lt_of_gt hx.2), zero_sub, abs_neg, abs_of_nonneg hc_mem.1]) measurableSet_Ioo
    have hi2 : IntervalIntegrable (fun x => |(if t < x then (1 : ℝ) else 0) - c_t|) volume t 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.2.le]
      exact (integrableOn_const (C := 1 - c_t) (hs := measure_Ioo_lt_top.ne)).congr_fun (fun x hx => by
        rw [if_pos hx.1, abs_of_nonneg (sub_nonneg.mpr hc_mem.2)]) measurableSet_Ioo
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, hleft, hright]
    ring
  have hGt_cont : Continuous (extremalTruncDiff k t) :=
    ((continuous_normTruncatedPower (Nat.succ_pos k)).comp
      (continuous_const.prodMk continuous_id)).sub (truncLagrangePoly k t).continuous
  have hAG : firstBestConstant (k + 1) * ∫ y in (-1 : ℝ)..1, |extremalTruncDiff k t y| =
      -(∫ x in (-1 : ℝ)..t, movingOperator k (extremalTruncDiff k t) x) +
        (∫ x in t..1, movingOperator k (extremalTruncDiff k t) x) := by
    have hpiece : ∫ y in (-1 : ℝ)..1, |extremalTruncDiff k t y| =
        ∑ j : Fin (k + 2),
          ∫ x in (-1 : ℝ)..1, orderedNodeSpeed k x j * |extremalTruncDiff k t (orderedNode k x j)| := by
      have hsubst : ∀ j : Fin (k + 2),
          ∫ x in (-1 : ℝ)..1, orderedNodeSpeed k x j * |extremalTruncDiff k t (orderedNode k x j)| =
            ∫ y in chebyshevGrid k j.val..chebyshevGrid k (j.val + 1), |extremalTruncDiff k t y| := by
        intro j
        rw [← orderedNode_neg_one k j, ← orderedNode_one k j]
        exact (intervalIntegral_comp_orderedNode k j ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩
          (by norm_num) (fun y => |extremalTruncDiff k t y|)).symm
      simp_rw [hsubst]
      rw [Fin.sum_univ_eq_sum_range (fun j =>
        ∫ y in chebyshevGrid k j..chebyshevGrid k (j + 1), |extremalTruncDiff k t y|) (k + 2)]
      have hadj := intervalIntegral.sum_integral_adjacent_intervals (a := chebyshevGrid k)
        (μ := volume) (f := fun y => |extremalTruncDiff k t y|) (n := k + 2)
        (fun j _ => hGt_cont.abs.intervalIntegrable _ _)
      rw [hadj, chebyshevGrid_zero, chebyshevGrid_last]
    have hterm_int : ∀ j : Fin (k + 2),
        IntervalIntegrable
          (fun x => orderedNodeSpeed k x j * |extremalTruncDiff k t (orderedNode k x j)|)
          volume (-1) 1 := by
      intro j
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num),
        ← integrableOn_comp_orderedNode_iff k j ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩
          (by norm_num) (fun y => |extremalTruncDiff k t y|)]
      exact hGt_cont.abs.integrableOn_Icc.mono_set Ioo_subset_Icc_self
    rw [hpiece, ← intervalIntegral.integral_finsetSum (fun j _ => hterm_int j),
      ← intervalIntegral.integral_const_mul]
    have hsum_int : IntervalIntegrable
        (fun x => firstBestConstant (k + 1) *
          ∑ j : Fin (k + 2), orderedNodeSpeed k x j * |extremalTruncDiff k t (orderedNode k x j)|)
        volume (-1) 1 := by
      have h1 : IntervalIntegrable
          (fun x => ∑ j : Fin (k + 2), orderedNodeSpeed k x j * |extremalTruncDiff k t (orderedNode k x j)|)
          volume (-1) 1 := by
        rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
        exact integrable_finsetSum Finset.univ fun j _ =>
          (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp (hterm_int j)
      exact h1.const_mul _
    have hsum_int_Icc : IntegrableOn
        (fun x => firstBestConstant (k + 1) *
          ∑ j : Fin (k + 2), orderedNodeSpeed k x j * |extremalTruncDiff k t (orderedNode k x j)|)
        (Icc (-1 : ℝ) 1) volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp hsum_int
    rw [← intervalIntegral.integral_add_adjacent_intervals
      ((intervalIntegrable_iff_integrableOn_Icc_of_le ht.1.le).mpr
        (hsum_int_Icc.mono_set (Icc_subset_Icc le_rfl ht.2.le)))
      ((intervalIntegrable_iff_integrableOn_Icc_of_le ht.2.le).mpr
        (hsum_int_Icc.mono_set (Icc_subset_Icc ht.1.le le_rfl)))]
    congr 1
    · rw [← intervalIntegral.integral_neg, intervalIntegral.integral_of_le ht.1.le,
        intervalIntegral.integral_of_le ht.1.le,
        MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      have hx_Ioo : x ∈ Ioo (-1 : ℝ) 1 := ⟨hx.1, lt_trans hx.2 ht.2⟩
      unfold movingOperator
      rw [← mul_neg, ← Finset.sum_neg_distrib]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      have hnp := altSign_mul_extremalTruncDiff_nonpos k ht hx_Ioo hx.2 j
      have habs : |altSign (k + 1) j * extremalTruncDiff k t (orderedNode k x j)| =
          -(altSign (k + 1) j * extremalTruncDiff k t (orderedNode k x j)) := abs_of_nonpos hnp
      rw [abs_mul, abs_altSign, one_mul] at habs
      rw [habs]; ring
    · rw [intervalIntegral.integral_of_le ht.2.le, intervalIntegral.integral_of_le ht.2.le,
        MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      have hx_Ioo : x ∈ Ioo (-1 : ℝ) 1 := ⟨lt_trans ht.1 hx.1, hx.2⟩
      unfold movingOperator
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      have hnn := altSign_mul_extremalTruncDiff_nonneg k ht hx_Ioo hx.1 j
      have habs : |altSign (k + 1) j * extremalTruncDiff k t (orderedNode k x j)| =
          altSign (k + 1) j * extremalTruncDiff k t (orderedNode k x j) := abs_of_nonneg hnn
      rw [abs_mul, abs_altSign, one_mul] at habs
      rw [habs]; ring
  have hT_Gt_eq : ∀ x ∈ Ioo (-1 : ℝ) 1,
      movingOperator k (extremalTruncDiff k t) x =
        movingOperator k (normTruncatedPower (k + 1) t) x - c_t := by
    intro x hx
    have hx_abs : |x| < 1 := abs_lt.mpr hx
    have hlin : movingOperator k (extremalTruncDiff k t) x =
        movingOperator k (normTruncatedPower (k + 1) t) x -
          movingOperator k (fun y => (truncLagrangePoly k t).eval y) x := by
      unfold movingOperator extremalTruncDiff
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [hlin, movingOperator_poly k (truncLagrangePoly k t) (truncLagrangePoly_natDegree_le k t)
      hx_abs, truncLagrangePoly_iteratedDeriv k ht_abs]
  have hht_cont : Continuous (normTruncatedPower (k + 1) t) :=
    (continuous_normTruncatedPower (Nat.succ_pos k)).comp (continuous_const.prodMk continuous_id)
  have hT_ht_Icc : IntegrableOn (movingOperator k (normTruncatedPower (k + 1) t))
      (Icc (-1 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
      (intervalIntegrable_movingOperator k hht_cont.integrableOn_Icc)
  have hT_ht_left : IntervalIntegrable (movingOperator k (normTruncatedPower (k + 1) t))
      volume (-1) t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1.le).mpr
      (hT_ht_Icc.mono_set (Icc_subset_Icc le_rfl ht.2.le))
  have hT_ht_right : IntervalIntegrable (movingOperator k (normTruncatedPower (k + 1) t))
      volume t 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.2.le).mpr
      (hT_ht_Icc.mono_set (Icc_subset_Icc ht.1.le le_rfl))
  have hint_left : ∫ x in (-1 : ℝ)..t, movingOperator k (extremalTruncDiff k t) x =
      (∫ x in (-1 : ℝ)..t, movingOperator k (normTruncatedPower (k + 1) t) x) - (t + 1) * c_t := by
    have h1 : ∫ x in (-1 : ℝ)..t, movingOperator k (extremalTruncDiff k t) x =
        ∫ x in (-1 : ℝ)..t, (movingOperator k (normTruncatedPower (k + 1) t) x - c_t) := by
      rw [intervalIntegral.integral_of_le ht.1.le, intervalIntegral.integral_of_le ht.1.le,
        MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      exact setIntegral_congr_fun measurableSet_Ioo fun x hx =>
        hT_Gt_eq x ⟨hx.1, lt_trans hx.2 ht.2⟩
    rw [h1, intervalIntegral.integral_sub hT_ht_left (intervalIntegrable_const (c := c_t)),
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hint_right : ∫ x in t..1, movingOperator k (extremalTruncDiff k t) x =
      (∫ x in t..1, movingOperator k (normTruncatedPower (k + 1) t) x) - (1 - t) * c_t := by
    have h1 : ∫ x in t..1, movingOperator k (extremalTruncDiff k t) x =
        ∫ x in t..1, (movingOperator k (normTruncatedPower (k + 1) t) x - c_t) := by
      rw [intervalIntegral.integral_of_le ht.2.le, intervalIntegral.integral_of_le ht.2.le,
        MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      exact setIntegral_congr_fun measurableSet_Ioo fun x hx =>
        hT_Gt_eq x ⟨lt_trans ht.1 hx.1, hx.2⟩
    rw [h1, intervalIntegral.integral_sub hT_ht_right (intervalIntegrable_const (c := c_t)),
      intervalIntegral.integral_const, smul_eq_mul]
  have hE_split : explicitError (k + 1) (orderedNode k t) t =
      (1 - t) + (∫ x in (-1 : ℝ)..t, movingOperator k (normTruncatedPower (k + 1) t) x) -
        (∫ x in t..1, movingOperator k (normTruncatedPower (k + 1) t) x) := by
    rw [← integral_abs_indicator_sub_movingOperator_eq_explicitError k ht_Icc]
    have hl : ∫ x in (-1 : ℝ)..t,
        |(if t < x then (1 : ℝ) else 0) - movingOperator k (normTruncatedPower (k + 1) t) x| =
        ∫ x in (-1 : ℝ)..t, movingOperator k (normTruncatedPower (k + 1) t) x := by
      rw [intervalIntegral.integral_of_le ht.1.le, intervalIntegral.integral_of_le ht.1.le,
        MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      have hmem := movingOperator_normTruncatedPower_mem_Icc k t (abs_lt.mpr ⟨hx.1, lt_trans hx.2 ht.2⟩)
      rw [if_neg (not_lt_of_gt hx.2), zero_sub, abs_neg, abs_of_nonneg hmem.1]
    have hr : ∫ x in t..1,
        |(if t < x then (1 : ℝ) else 0) - movingOperator k (normTruncatedPower (k + 1) t) x| =
        (1 - t) - ∫ x in t..1, movingOperator k (normTruncatedPower (k + 1) t) x := by
      have h1 : ∫ x in t..1,
          |(if t < x then (1 : ℝ) else 0) - movingOperator k (normTruncatedPower (k + 1) t) x| =
          ∫ x in t..1, (1 - movingOperator k (normTruncatedPower (k + 1) t) x) := by
        rw [intervalIntegral.integral_of_le ht.2.le, intervalIntegral.integral_of_le ht.2.le,
          MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
        refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
        have hmem := movingOperator_normTruncatedPower_mem_Icc k t (abs_lt.mpr ⟨lt_trans ht.1 hx.1, hx.2⟩)
        rw [if_pos hx.1, abs_of_nonneg (sub_nonneg.mpr hmem.2)]
      rw [h1, intervalIntegral.integral_sub (intervalIntegrable_const (c := (1 : ℝ))) hT_ht_right,
        intervalIntegral.integral_const, smul_eq_mul, mul_one]
    have hil : IntervalIntegrable
        (fun x => |(if t < x then (1 : ℝ) else 0) - movingOperator k (normTruncatedPower (k + 1) t) x|)
        volume (-1) t := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1.le]
      exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1.le).mp hT_ht_left).congr_fun
        (fun x hx => by
          have hmem := movingOperator_normTruncatedPower_mem_Icc k t
            (abs_lt.mpr ⟨hx.1, lt_trans hx.2 ht.2⟩)
          rw [if_neg (not_lt_of_gt hx.2), zero_sub, abs_neg, abs_of_nonneg hmem.1])
        measurableSet_Ioo
    have hir : IntervalIntegrable
        (fun x => |(if t < x then (1 : ℝ) else 0) - movingOperator k (normTruncatedPower (k + 1) t) x|)
        volume t 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.2.le]
      exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.2.le).mp
        ((intervalIntegrable_const (c := (1 : ℝ))).sub hT_ht_right)).congr_fun
        (fun x hx => by
          have hmem := movingOperator_normTruncatedPower_mem_Icc k t
            (abs_lt.mpr ⟨lt_trans ht.1 hx.1, hx.2⟩)
          rw [if_pos hx.1, abs_of_nonneg (sub_nonneg.mpr hmem.2)])
        measurableSet_Ioo
    rw [← intervalIntegral.integral_add_adjacent_intervals hil hir, hl, hr]
    ring
  rw [hGn, hAG, hint_left, hint_right, hE_split]
  ring

/-! ### Smooth approximation of `h_t` via iterated indefinite integrals of a `ContDiffBump` -/

/-- `m`-fold indefinite integral starting at `-1`:
`iteratedAntideriv g 0 y = ∫_{-1}^y g`, `iteratedAntideriv g (m + 1) y = ∫_{-1}^y iteratedAntideriv g m`. -/
noncomputable def iteratedAntideriv (g : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0, y => ∫ s in (-1 : ℝ)..y, g s
  | m + 1, y => ∫ s in (-1 : ℝ)..y, iteratedAntideriv g m s

private theorem hasDerivAt_iteratedAntideriv_zero {g : ℝ → ℝ} (hg : Continuous g) (y : ℝ) :
    HasDerivAt (iteratedAntideriv g 0) (g y) y :=
  intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
    (hg.stronglyMeasurableAtFilter volume (𝓝 y)) hg.continuousAt

private theorem contDiff_iteratedAntideriv {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    ∀ m : ℕ, ContDiff ℝ ∞ (iteratedAntideriv g m)
  | 0 => by
    rw [contDiff_infty_iff_deriv]
    have hderiv : deriv (iteratedAntideriv g 0) = g := by
      ext y; exact (hasDerivAt_iteratedAntideriv_zero hg.continuous y).deriv
    exact ⟨fun y => (hasDerivAt_iteratedAntideriv_zero hg.continuous y).differentiableAt,
      by rwa [hderiv]⟩
  | m + 1 => by
    have ihm := contDiff_iteratedAntideriv hg m
    rw [contDiff_infty_iff_deriv]
    have hhas : ∀ y : ℝ, HasDerivAt (iteratedAntideriv g (m + 1)) (iteratedAntideriv g m y) y :=
      fun y => intervalIntegral.integral_hasDerivAt_right (ihm.continuous.intervalIntegrable _ _)
        (ihm.continuous.stronglyMeasurableAtFilter volume (𝓝 y)) ihm.continuous.continuousAt
    have hderiv : deriv (iteratedAntideriv g (m + 1)) = iteratedAntideriv g m := by
      ext y; exact (hhas y).deriv
    exact ⟨fun y => (hhas y).differentiableAt, by rwa [hderiv]⟩

private theorem iteratedDeriv_iteratedAntideriv {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    ∀ m : ℕ, iteratedDeriv m (iteratedAntideriv g m) = iteratedAntideriv g 0
  | 0 => rfl
  | m + 1 => by
    rw [iteratedDeriv_succ']
    have ihm := contDiff_iteratedAntideriv hg m
    have hderiv : deriv (iteratedAntideriv g (m + 1)) = iteratedAntideriv g m := by
      ext y
      exact (intervalIntegral.integral_hasDerivAt_right (ihm.continuous.intervalIntegrable _ _)
        (ihm.continuous.stronglyMeasurableAtFilter volume (𝓝 y)) ihm.continuous.continuousAt).deriv
    rw [hderiv]
    exact iteratedDeriv_iteratedAntideriv hg m

private theorem iteratedDeriv_succ_iteratedAntideriv {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (m : ℕ) :
    iteratedDeriv (m + 1) (iteratedAntideriv g m) = g := by
  rw [iteratedDeriv_succ, iteratedDeriv_iteratedAntideriv hg m]
  ext y
  exact (hasDerivAt_iteratedAntideriv_zero hg.continuous y).deriv

private theorem hasDerivAt_truncatedPower_shifted' (n : ℕ) (hn : 0 < n) (t y : ℝ) :
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

private theorem normTruncatedPower_eq_integral {t y : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hy : y ∈ Icc (-1 : ℝ) 1) (m : ℕ) :
    normTruncatedPower (m + 1) t y =
      ∫ s in (-1 : ℝ)..y, if m = 0 then (if t < s then (1 : ℝ) else 0) else normTruncatedPower m t s := by
  cases m with
  | zero =>
    simp only [ite_true]
    by_cases hty : t ≤ y
    · have h1 : ∫ s in (-1 : ℝ)..t, (if t < s then (1 : ℝ) else 0) = 0 := by
        rw [intervalIntegral.integral_of_le ht.1.le]
        exact setIntegral_eq_zero_of_forall_eq_zero fun s hs => if_neg (not_lt_of_ge hs.2)
      have h2 : ∫ s in t..y, (if t < s then (1 : ℝ) else 0) = y - t := by
        have heq : ∫ s in t..y, (if t < s then (1 : ℝ) else 0) = ∫ _s in t..y, (1 : ℝ) := by
          rw [intervalIntegral.integral_of_le hty, intervalIntegral.integral_of_le hty]
          exact setIntegral_congr_fun measurableSet_Ioc fun s hs => if_pos hs.1
        rw [heq, intervalIntegral.integral_const, smul_eq_mul, mul_one]
      have hi1 : IntervalIntegrable (fun s => if t < s then (1 : ℝ) else 0) volume (-1) t := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1.le]
        exact (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioc (-1) t) volume).congr_fun
          (fun s hs => (if_neg (not_lt_of_ge hs.2)).symm) measurableSet_Ioc
      have hi2 : IntervalIntegrable (fun s => if t < s then (1 : ℝ) else 0) volume t y := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hty]
        exact (integrableOn_const (C := (1 : ℝ)) (hs := measure_Ioc_lt_top.ne)).congr_fun
          (fun s hs => (if_pos hs.1).symm) measurableSet_Ioc
      rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, h1, h2, zero_add]
      simp [normTruncatedPower, truncatedPower, hty]
    · push Not at hty
      have h0 : ∫ s in (-1 : ℝ)..y, (if t < s then (1 : ℝ) else 0) = 0 := by
        rw [intervalIntegral.integral_of_le hy.1]
        exact setIntegral_eq_zero_of_forall_eq_zero fun s hs =>
          if_neg (not_lt_of_gt (lt_of_le_of_lt hs.2 hty))
      rw [h0]
      simp [normTruncatedPower, truncatedPower, not_le_of_gt hty]
  | succ m =>
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := normTruncatedPower (m + 2) t) (f' := normTruncatedPower (m + 1) t) (a := -1) (b := y)
      (fun s _ => by
        have h1 := hasDerivAt_truncatedPower_shifted' (m + 1) (Nat.succ_pos m) t s
        have h2 := h1.div_const ((m + 1).factorial : ℝ)
        have hfun : (fun z => truncatedPower (m + 2) t z / (((m + 1 : ℕ) : ℝ) + 1) /
            ((m + 1).factorial : ℝ)) = normTruncatedPower (m + 2) t := by
          ext z; unfold normTruncatedPower
          rw [div_div]
          congr 1
          conv_rhs => rw [show m + 2 = (m + 1) + 1 by omega, Nat.factorial_succ]
          push_cast; ring
        rwa [hfun] at h2)
      (((continuous_normTruncatedPower (Nat.succ_pos m)).comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
    rw [hFTC]
    have hneg1 : normTruncatedPower (m + 2) t (-1) = 0 := by
      simp [normTruncatedPower, truncatedPower, not_le_of_gt ht.1]
    rw [hneg1, sub_zero]

/-- **Sharpness of the second constant on `[-1, 1]`** (Claim 2 `clm:sharp`):
fixing `A_n = 2^n * n!`, for ANY `t ∈ (-1, 1)` and ANY `B : ℝ` valid on `C^∞([-1, 1])`,
`E_n(t) ≤ B` (in particular, `b_n = E_n(0) ≤ B`). -/
theorem sharp_secondConstant_unit_le (k : ℕ) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) (B : ℝ)
    (hB : ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f →
      ∫ x in (-1 : ℝ)..1, |iteratedDeriv (k + 1) f x| ≤
        firstBestConstant (k + 1) * (∫ y in (-1 : ℝ)..1, |f y|) +
          B * (∫ s in (-1 : ℝ)..1, |iteratedDeriv (k + 2) f s|)) :
    explicitError (k + 1) (orderedNode k t) t ≤ B := by
  by_contra hlt
  push Not at hlt
  set δ := explicitError (k + 1) (orderedNode k t) t - B
  have hδ : 0 < δ := sub_pos.mpr hlt
  set C_err : ℝ := 2 + firstBestConstant (k + 1) * (2 : ℝ) ^ (k + 2)
  have hC_pos : 0 < C_err := by unfold C_err firstBestConstant; positivity
  set ε : ℝ := min (min (t + 1) (1 - t) / 2) (δ / (2 * C_err))
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact lt_min (div_pos (lt_min (by linarith [ht.1]) (by linarith [ht.2])) (by norm_num))
      (div_pos hδ (by positivity))
  have hε_lo : -1 < t - ε := by
    have h1 : ε ≤ min (t + 1) (1 - t) / 2 := min_le_left _ _
    have h2 : min (t + 1) (1 - t) ≤ t + 1 := min_le_left _ _
    linarith [ht.1]
  have hε_hi : t + ε < 1 := by
    have h1 : ε ≤ min (t + 1) (1 - t) / 2 := min_le_left _ _
    have h2 : min (t + 1) (1 - t) ≤ 1 - t := min_le_right _ _
    linarith [ht.2]
  have hε_small : C_err * ε < δ := by
    have h1 : ε ≤ δ / (2 * C_err) := min_le_right _ _
    have h2 : C_err * ε ≤ δ / 2 := by
      have := mul_le_mul_of_nonneg_left h1 hC_pos.le
      have hne : C_err ≠ 0 := hC_pos.ne'
      have heq : C_err * (δ / (2 * C_err)) = δ / 2 := by field_simp [hne]
      linarith
    linarith
  let b : ContDiffBump t := ⟨ε / 2, ε, by linarith, by linarith⟩
  let φ : ℝ → ℝ := b.normed volume
  have hφ_smooth : ContDiff ℝ ∞ φ := b.contDiff.div_const _
  have hφ_nonneg : ∀ y : ℝ, 0 ≤ φ y := fun y => b.nonneg_normed y
  have hφ_zero_of_ge : ∀ y : ℝ, ε ≤ |y - t| → φ y = 0 := by
    intro y hy
    have hnot : y ∉ Function.support b := by
      rw [b.support_eq, Metric.mem_ball, Real.dist_eq]
      exact not_lt_of_ge hy
    have hb0 : b y = 0 := Function.notMem_support.mp hnot
    simp [φ, ContDiffBump.normed, hb0]
  have hφ_int_univ : ∫ y : ℝ, φ y = 1 := b.integral_normed
  have hφ_int_Icc : ∫ y in (-1 : ℝ)..1, φ y = 1 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    have hsupp : Function.support φ ⊆ Ioc (-1 : ℝ) 1 := by
      intro y hy
      by_contra hnot
      have hge : ε ≤ |y - t| := by
        by_contra hlt'
        push Not at hlt'
        have hlt_abs := abs_lt.mp hlt'
        exact hnot ⟨by linarith [hε_lo, hlt_abs.1], by linarith [hε_hi, hlt_abs.2]⟩
      exact hy (hφ_zero_of_ge y hge)
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    have heq : (Ioc (-1 : ℝ) 1).indicator φ = φ := by
      ext y
      by_cases hy : y ∈ Ioc (-1 : ℝ) 1
      · simp [Set.indicator_of_mem hy]
      · rw [Set.indicator_of_notMem hy]
        by_contra hne
        exact hy (hsupp (Function.mem_support.mpr (Ne.symm hne)))
    rw [heq, hφ_int_univ]
  have hI0_le : ∀ y ∈ Icc (-1 : ℝ) 1, 0 ≤ iteratedAntideriv φ 0 y ∧ iteratedAntideriv φ 0 y ≤ 1 := by
    intro y hy
    dsimp [iteratedAntideriv]
    constructor
    · exact intervalIntegral.integral_nonneg hy.1 (fun s _ => hφ_nonneg s)
    · have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hφ_smooth.continuous.intervalIntegrable (μ := volume) (-1) y)
        (hφ_smooth.continuous.intervalIntegrable (μ := volume) y 1)
      have hnn := intervalIntegral.integral_nonneg (μ := volume) hy.2 (fun s _ => hφ_nonneg s)
      linarith [hsplit, hφ_int_Icc, hnn]
  have hI0_left : ∀ y ∈ Icc (-1 : ℝ) (t - ε), iteratedAntideriv φ 0 y = 0 := by
    intro y hy
    dsimp [iteratedAntideriv]
    rw [intervalIntegral.integral_of_le hy.1]
    refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => hφ_zero_of_ge s ?_
    rw [abs_of_nonpos (by linarith [hs.2, hy.2])]; linarith [hs.2, hy.2]
  have hI0_right : ∀ y ∈ Icc (t + ε) 1, iteratedAntideriv φ 0 y = 1 := by
    intro y hy
    have htail : ∫ s in y..1, φ s = 0 := by
      rw [intervalIntegral.integral_of_le hy.2]
      refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => hφ_zero_of_ge s ?_
      rw [abs_of_nonneg (by linarith [hs.1, hy.1])]; linarith [hs.1, hy.1]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hφ_smooth.continuous.intervalIntegrable (μ := volume) (-1) y)
      (hφ_smooth.continuous.intervalIntegrable (μ := volume) y 1)
    dsimp [iteratedAntideriv]
    linarith [hsplit, htail, hφ_int_Icc]
  have hL1_0 : ∫ y in (-1 : ℝ)..1, |iteratedAntideriv φ 0 y - (if t < y then (1 : ℝ) else 0)| ≤
      2 * ε := by
    have hint_diff : ∀ a b : ℝ, a ∈ Icc (-1 : ℝ) 1 → b ∈ Icc (-1 : ℝ) 1 → a ≤ b →
        IntervalIntegrable (fun y => |iteratedAntideriv φ 0 y - (if t < y then (1 : ℝ) else 0)|)
          volume a b := by
      intro a b _ha _hb hab
      have h1 : IntervalIntegrable (iteratedAntideriv φ 0) volume a b :=
        (contDiff_iteratedAntideriv hφ_smooth 0).continuous.intervalIntegrable a b
      have h2 : IntervalIntegrable (fun y => if t < y then (1 : ℝ) else 0) volume a b := by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
        exact (integrableOn_const (C := (1 : ℝ)) (hs := measure_Icc_lt_top.ne)).indicator
          isOpen_Ioi.measurableSet
      exact (h1.sub h2).abs
    have hI1 : ∫ y in (-1 : ℝ)..(t - ε),
        |iteratedAntideriv φ 0 y - (if t < y then (1 : ℝ) else 0)| = 0 := by
      rw [intervalIntegral.integral_of_le hε_lo.le]
      refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
      rw [hI0_left y ⟨hy.1.le, hy.2⟩, if_neg (by linarith [hy.2, hε_pos]), sub_zero, abs_zero]
    have hI3 : ∫ y in (t + ε)..1,
        |iteratedAntideriv φ 0 y - (if t < y then (1 : ℝ) else 0)| = 0 := by
      rw [intervalIntegral.integral_of_le hε_hi.le]
      refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
      rw [hI0_right y ⟨hy.1.le, hy.2⟩, if_pos (by linarith [hy.1, hε_pos]), sub_self, abs_zero]
    have hI2 : ∫ y in (t - ε)..(t + ε),
        |iteratedAntideriv φ 0 y - (if t < y then (1 : ℝ) else 0)| ≤ 2 * ε := by
      calc ∫ y in (t - ε)..(t + ε), |iteratedAntideriv φ 0 y - (if t < y then (1 : ℝ) else 0)|
          ≤ ∫ _y in (t - ε)..(t + ε), (1 : ℝ) := by
            apply intervalIntegral.integral_mono_on (by linarith)
              (hint_diff _ _ ⟨hε_lo.le, by linarith⟩ ⟨by linarith, hε_hi.le⟩ (by linarith))
              intervalIntegrable_const
            intro y hy
            have hmem := hI0_le y ⟨by linarith [hε_lo, hy.1], by linarith [hε_hi, hy.2]⟩
            split_ifs
            · rw [abs_le]; constructor <;> linarith [hmem.1, hmem.2]
            · rw [sub_zero, abs_of_nonneg hmem.1]; exact hmem.2
        _ = 2 * ε := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
      (hint_diff (-1) (t - ε) ⟨le_rfl, by norm_num⟩ ⟨hε_lo.le, by linarith⟩ hε_lo.le)
      (hint_diff (t - ε) (t + ε) ⟨hε_lo.le, by linarith⟩ ⟨by linarith, hε_hi.le⟩ (by linarith))
    have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
      (hint_diff (-1) (t + ε) ⟨le_rfl, by norm_num⟩ ⟨by linarith, hε_hi.le⟩ (by linarith))
      (hint_diff (t + ε) 1 ⟨by linarith, hε_hi.le⟩ ⟨by norm_num, le_rfl⟩ hε_hi.le)
    linarith
  have hL1_m : ∀ m : ℕ,
      ∫ y in (-1 : ℝ)..1, |iteratedAntideriv φ (m + 1) y - normTruncatedPower (m + 1) t y| ≤
        (2 : ℝ) ^ (m + 2) * ε := by
    intro m
    induction m with
    | zero =>
      have hpt : ∀ y ∈ Icc (-1 : ℝ) 1,
          |iteratedAntideriv φ 1 y - normTruncatedPower 1 t y| ≤ 2 * ε := by
        intro y hy
        rw [normTruncatedPower_eq_integral ht hy 0]
        simp only [ite_true]
        change |(∫ s in (-1 : ℝ)..y, iteratedAntideriv φ 0 s) -
          ∫ s in (-1 : ℝ)..y, if t < s then (1 : ℝ) else 0| ≤ 2 * ε
        have hi1 : IntervalIntegrable (iteratedAntideriv φ 0) volume (-1) y :=
          (contDiff_iteratedAntideriv hφ_smooth 0).continuous.intervalIntegrable _ _
        have hi2 : IntervalIntegrable (fun s => if t < s then (1 : ℝ) else 0) volume (-1) y := by
          rw [intervalIntegrable_iff_integrableOn_Icc_of_le hy.1]
          exact (integrableOn_const (C := (1 : ℝ)) (hs := measure_Icc_lt_top.ne)).indicator
            isOpen_Ioi.measurableSet
        rw [← intervalIntegral.integral_sub hi1 hi2]
        calc |∫ s in (-1 : ℝ)..y, (iteratedAntideriv φ 0 s - (if t < s then (1 : ℝ) else 0))|
            ≤ ∫ s in (-1 : ℝ)..y, |iteratedAntideriv φ 0 s - (if t < s then (1 : ℝ) else 0)| :=
              intervalIntegral.abs_integral_le_integral_abs hy.1
          _ ≤ ∫ s in (-1 : ℝ)..1, |iteratedAntideriv φ 0 s - (if t < s then (1 : ℝ) else 0)| := by
              have hi_abs : IntervalIntegrable
                  (fun s => |iteratedAntideriv φ 0 s - (if t < s then (1 : ℝ) else 0)|)
                  volume y 1 := by
                have h1 : IntervalIntegrable (iteratedAntideriv φ 0) volume y 1 :=
                  (contDiff_iteratedAntideriv hφ_smooth 0).continuous.intervalIntegrable _ _
                have h2 : IntervalIntegrable (fun s => if t < s then (1 : ℝ) else 0) volume y 1 := by
                  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hy.2]
                  exact (integrableOn_const (C := (1 : ℝ)) (hs := measure_Icc_lt_top.ne)).indicator
                    isOpen_Ioi.measurableSet
                exact (h1.sub h2).abs
              rw [← intervalIntegral.integral_add_adjacent_intervals (hi1.sub hi2).abs hi_abs]
              have hnn := intervalIntegral.integral_nonneg (μ := volume) hy.2
                (f := fun s => |iteratedAntideriv φ 0 s - if t < s then (1 : ℝ) else 0|)
                (fun _ _ => abs_nonneg _)
              linarith
          _ ≤ 2 * ε := hL1_0
      have hint_lhs : IntervalIntegrable
          (fun y => |iteratedAntideriv φ 1 y - normTruncatedPower 1 t y|) volume (-1) 1 :=
        (((contDiff_iteratedAntideriv hφ_smooth 1).continuous.sub
          ((continuous_normTruncatedPower (Nat.succ_pos 0)).comp
            (continuous_const.prodMk continuous_id))).abs).intervalIntegrable _ _
      calc ∫ y in (-1 : ℝ)..1, |iteratedAntideriv φ 1 y - normTruncatedPower 1 t y|
          ≤ ∫ _y in (-1 : ℝ)..1, (2 * ε) :=
            intervalIntegral.integral_mono_on (by norm_num) hint_lhs intervalIntegrable_const hpt
        _ = (2 : ℝ) ^ 2 * ε := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    | succ m ih =>
      have hpt : ∀ y ∈ Icc (-1 : ℝ) 1,
          |iteratedAntideriv φ (m + 2) y - normTruncatedPower (m + 2) t y| ≤
            (2 : ℝ) ^ (m + 2) * ε := by
        intro y hy
        rw [normTruncatedPower_eq_integral ht hy (m + 1)]
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
        change |(∫ s in (-1 : ℝ)..y, iteratedAntideriv φ (m + 1) s) -
          ∫ s in (-1 : ℝ)..y, normTruncatedPower (m + 1) t s| ≤ (2 : ℝ) ^ (m + 2) * ε
        have hc1 : Continuous (iteratedAntideriv φ (m + 1)) :=
          (contDiff_iteratedAntideriv hφ_smooth (m + 1)).continuous
        have hc2 : Continuous (normTruncatedPower (m + 1) t) :=
          (continuous_normTruncatedPower (Nat.succ_pos m)).comp
            (continuous_const.prodMk continuous_id)
        rw [← intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
        calc |∫ s in (-1 : ℝ)..y, (iteratedAntideriv φ (m + 1) s - normTruncatedPower (m + 1) t s)|
            ≤ ∫ s in (-1 : ℝ)..y, |iteratedAntideriv φ (m + 1) s - normTruncatedPower (m + 1) t s| :=
              intervalIntegral.abs_integral_le_integral_abs hy.1
          _ ≤ ∫ s in (-1 : ℝ)..1, |iteratedAntideriv φ (m + 1) s - normTruncatedPower (m + 1) t s| := by
              have hcd : Continuous
                  (fun s => |iteratedAntideriv φ (m + 1) s - normTruncatedPower (m + 1) t s|) :=
                (hc1.sub hc2).abs
              have hsplit := intervalIntegral.integral_add_adjacent_intervals
                (hcd.intervalIntegrable (μ := volume) (-1) y)
                (hcd.intervalIntegrable (μ := volume) y 1)
              have hnn := intervalIntegral.integral_nonneg (μ := volume) hy.2
                (f := fun s => |iteratedAntideriv φ (m + 1) s - normTruncatedPower (m + 1) t s|)
                (fun _ _ => abs_nonneg _)
              linarith
          _ ≤ (2 : ℝ) ^ (m + 2) * ε := ih
      have hint_lhs : IntervalIntegrable
          (fun y => |iteratedAntideriv φ (m + 2) y - normTruncatedPower (m + 2) t y|) volume (-1) 1 :=
        (((contDiff_iteratedAntideriv hφ_smooth (m + 2)).continuous.sub
          ((continuous_normTruncatedPower (Nat.succ_pos (m + 1))).comp
            (continuous_const.prodMk continuous_id))).abs).intervalIntegrable _ _
      calc ∫ y in (-1 : ℝ)..1, |iteratedAntideriv φ (m + 2) y - normTruncatedPower (m + 2) t y|
          ≤ ∫ _y in (-1 : ℝ)..1, ((2 : ℝ) ^ (m + 2) * ε) :=
            intervalIntegral.integral_mono_on (by norm_num) hint_lhs intervalIntegrable_const hpt
        _ = (2 : ℝ) ^ (m + 3) * ε := by
            rw [intervalIntegral.integral_const, smul_eq_mul, pow_succ]; ring
  let fε : ℝ → ℝ := fun y => iteratedAntideriv φ (k + 1) y - (truncLagrangePoly k t).eval y
  have hP_smooth : ContDiff ℝ ∞ (fun y => (truncLagrangePoly k t).eval y) := by
    simpa [Polynomial.aeval_def] using (truncLagrangePoly k t).contDiff_aeval (𝕜 := ℝ) ∞
  have hfε_smooth : ContDiff ℝ ∞ fε :=
    (contDiff_iteratedAntideriv hφ_smooth (k + 1)).sub hP_smooth
  have hfε_dn : ∀ x : ℝ, iteratedDeriv (k + 1) fε x =
      iteratedAntideriv φ 0 x - iteratedDeriv (k + 1) (fun y => (truncLagrangePoly k t).eval y) x := by
    intro x
    have h1 := iteratedDeriv_sub (n := k + 1) (x := x)
      ((contDiff_iteratedAntideriv hφ_smooth (k + 1)).contDiffAt.of_le (by exact_mod_cast natCast_le_infty (k + 1)))
      (hP_smooth.contDiffAt.of_le (by exact_mod_cast natCast_le_infty (k + 1)))
    rw [show fε = (iteratedAntideriv φ (k + 1)) - (fun y => (truncLagrangePoly k t).eval y) from rfl,
      h1, iteratedDeriv_iteratedAntideriv hφ_smooth (k + 1)]
  have hfε_dn1 : ∀ s : ℝ, iteratedDeriv (k + 2) fε s = φ s := by
    intro s
    have h1 := iteratedDeriv_sub (n := k + 2) (x := s)
      ((contDiff_iteratedAntideriv hφ_smooth (k + 1)).contDiffAt.of_le (by exact_mod_cast natCast_le_infty (k + 2)))
      (hP_smooth.contDiffAt.of_le (by exact_mod_cast natCast_le_infty (k + 2)))
    have hP0 : iteratedDeriv (k + 2) (fun y => (truncLagrangePoly k t).eval y) s = 0 := by
      rw [iteratedDeriv_polynomial_eval_of_natDegree_le _ (k + 2)
        (Nat.le_succ_of_le (truncLagrangePoly_natDegree_le k t)) s,
        Polynomial.coeff_eq_zero_of_natDegree_lt
          (Nat.lt_succ_of_le (truncLagrangePoly_natDegree_le k t)), mul_zero]
    rw [show fε = (iteratedAntideriv φ (k + 1)) - (fun y => (truncLagrangePoly k t).eval y) from rfl,
      h1, iteratedDeriv_succ_iteratedAntideriv hφ_smooth (k + 1), hP0, sub_zero]
  have htest := hB fε hfε_smooth
  have hnorm_top : ∫ s in (-1 : ℝ)..1, |iteratedDeriv (k + 2) fε s| = 1 := by
    simp_rw [hfε_dn1]
    have heq : (fun s => |φ s|) = φ := by ext s; exact abs_of_nonneg (hφ_nonneg s)
    rw [heq, hφ_int_Icc]
  have hnorm_0 : ∫ y in (-1 : ℝ)..1, |fε y| ≤
      (∫ y in (-1 : ℝ)..1, |extremalTruncDiff k t y|) + (2 : ℝ) ^ (k + 2) * ε := by
    have hcGt : Continuous (extremalTruncDiff k t) :=
      ((continuous_normTruncatedPower (Nat.succ_pos k)).comp
        (continuous_const.prodMk continuous_id)).sub (truncLagrangePoly k t).continuous
    have hcDiff : Continuous (fun y => iteratedAntideriv φ (k + 1) y - normTruncatedPower (k + 1) t y) :=
      (contDiff_iteratedAntideriv hφ_smooth (k + 1)).continuous.sub
        ((continuous_normTruncatedPower (Nat.succ_pos k)).comp
          (continuous_const.prodMk continuous_id))
    calc ∫ y in (-1 : ℝ)..1, |fε y|
        ≤ ∫ y in (-1 : ℝ)..1,
            (|extremalTruncDiff k t y| +
              |iteratedAntideriv φ (k + 1) y - normTruncatedPower (k + 1) t y|) := by
          apply intervalIntegral.integral_mono_on (by norm_num)
            (hfε_smooth.continuous.abs.intervalIntegrable _ _)
            ((hcGt.abs.add hcDiff.abs).intervalIntegrable _ _)
          intro y _
          calc |fε y| = |extremalTruncDiff k t y +
                  (iteratedAntideriv φ (k + 1) y - normTruncatedPower (k + 1) t y)| := by
                dsimp [fε, extremalTruncDiff]; ring_nf
            _ ≤ _ := abs_add_le _ _
      _ = (∫ y in (-1 : ℝ)..1, |extremalTruncDiff k t y|) +
            ∫ y in (-1 : ℝ)..1, |iteratedAntideriv φ (k + 1) y - normTruncatedPower (k + 1) t y| :=
          intervalIntegral.integral_add (hcGt.abs.intervalIntegrable _ _)
            (hcDiff.abs.intervalIntegrable _ _)
      _ ≤ (∫ y in (-1 : ℝ)..1, |extremalTruncDiff k t y|) + (2 : ℝ) ^ (k + 2) * ε := by
          linarith [hL1_m k]
  have hnorm_n : ∫ x in (-1 : ℝ)..1,
        |(if t < x then (1 : ℝ) else 0) -
          iteratedDeriv (k + 1) (fun y => (truncLagrangePoly k t).eval y) x| ≤
      (∫ x in (-1 : ℝ)..1, |iteratedDeriv (k + 1) fε x|) + 2 * ε := by
    have hP_cont : Continuous (fun x => iteratedDeriv (k + 1) (fun y => (truncLagrangePoly k t).eval y) x) := by
      simp_rw [truncLagrangePoly_iteratedDeriv k (abs_lt.mpr ht)]
      exact continuous_const
    have hind_int : IntervalIntegrable (fun x => if t < x then (1 : ℝ) else 0) volume (-1) 1 := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
      exact (integrableOn_const (C := (1 : ℝ)) (hs := measure_Icc_lt_top.ne)).indicator
        isOpen_Ioi.measurableSet
    have h1_int : IntervalIntegrable
        (fun x => |iteratedDeriv (k + 1) fε x|) volume (-1) 1 :=
      (hfε_smooth.continuous_iteratedDeriv (k + 1) (by exact_mod_cast natCast_le_infty (k + 1))).abs.intervalIntegrable _ _
    have h2_int : IntervalIntegrable
        (fun x => |iteratedAntideriv φ 0 x - (if t < x then (1 : ℝ) else 0)|) volume (-1) 1 :=
      (((contDiff_iteratedAntideriv hφ_smooth 0).continuous.intervalIntegrable _ _).sub hind_int).abs
    calc ∫ x in (-1 : ℝ)..1,
            |(if t < x then (1 : ℝ) else 0) -
              iteratedDeriv (k + 1) (fun y => (truncLagrangePoly k t).eval y) x|
        ≤ ∫ x in (-1 : ℝ)..1,
            (|iteratedDeriv (k + 1) fε x| +
              |iteratedAntideriv φ 0 x - (if t < x then (1 : ℝ) else 0)|) := by
          apply intervalIntegral.integral_mono_on (by norm_num)
            (hind_int.sub (hP_cont.intervalIntegrable _ _)).abs (h1_int.add h2_int)
          intro x _
          rw [hfε_dn x]
          calc |(if t < x then (1 : ℝ) else 0) -
                  iteratedDeriv (k + 1) (fun y => (truncLagrangePoly k t).eval y) x|
              = |(iteratedAntideriv φ 0 x -
                    iteratedDeriv (k + 1) (fun y => (truncLagrangePoly k t).eval y) x) +
                  ((if t < x then (1 : ℝ) else 0) - iteratedAntideriv φ 0 x)| := by ring_nf
            _ ≤ |iteratedAntideriv φ 0 x -
                    iteratedDeriv (k + 1) (fun y => (truncLagrangePoly k t).eval y) x| +
                  |(if t < x then (1 : ℝ) else 0) - iteratedAntideriv φ 0 x| := abs_add_le _ _
            _ = |iteratedAntideriv φ 0 x -
                    iteratedDeriv (k + 1) (fun y => (truncLagrangePoly k t).eval y) x| +
                  |iteratedAntideriv φ 0 x - (if t < x then (1 : ℝ) else 0)| := by
                rw [abs_sub_comm (if t < x then (1 : ℝ) else 0)]
      _ = (∫ x in (-1 : ℝ)..1, |iteratedDeriv (k + 1) fε x|) +
            ∫ x in (-1 : ℝ)..1, |iteratedAntideriv φ 0 x - (if t < x then (1 : ℝ) else 0)| :=
          intervalIntegral.integral_add h1_int h2_int
      _ ≤ (∫ x in (-1 : ℝ)..1, |iteratedDeriv (k + 1) fε x|) + 2 * ε := by linarith [hL1_0]
  have hid := extremalTruncDiff_L1_identity k ht
  have hA_nonneg : 0 ≤ firstBestConstant (k + 1) := by unfold firstBestConstant; positivity
  rw [hnorm_top, mul_one] at htest
  have hmul_A := mul_le_mul_of_nonneg_left hnorm_0 hA_nonneg
  dsimp [δ, C_err] at hε_small
  linarith

/-- Center sharpness on `[-1, 1]`: `centerBestConstant (k + 1) ≤ B`. -/
theorem sharp_centerBestConstant_unit_le (k : ℕ) (B : ℝ)
    (hB : ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f →
      ∫ x in (-1 : ℝ)..1, |iteratedDeriv (k + 1) f x| ≤
        firstBestConstant (k + 1) * (∫ y in (-1 : ℝ)..1, |f y|) +
          B * (∫ s in (-1 : ℝ)..1, |iteratedDeriv (k + 2) f s|)) :
    centerBestConstant (k + 1) ≤ B := by
  rw [← explicitError_center_eq k]
  exact sharp_secondConstant_unit_le k ⟨by norm_num, by norm_num⟩ B hB

/-- Sharpness of the second constant `(L / 2) * b_n` on any interval `[a, b]` (`a < b`),
even restricted to `C^∞([a, b])`. -/
theorem sharp_secondConstant_Icc_le (k : ℕ) {a b : ℝ} (hab : a < b) (B : ℝ)
    (hB : ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f →
      ∫ x in a..b, |iteratedDeriv (k + 1) f x| ≤
        (4 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * (b - a) ^ (-((k + 1 : ℕ) : ℤ)) *
            (∫ y in a..b, |f y|) +
          B * (∫ s in a..b, |iteratedDeriv (k + 2) f s|)) :
    ((b - a) / 2) * centerBestConstant (k + 1) ≤ B := by
  have hL : 0 < b - a := sub_pos.mpr hab
  have hL2 : 0 < (b - a) / 2 := by linarith
  suffices hunit : centerBestConstant (k + 1) ≤ B / ((b - a) / 2) by
    have h1 := (le_div_iff₀ hL2).mp hunit
    linarith
  apply sharp_centerBestConstant_unit_le k (B / ((b - a) / 2))
  intro g hg
  let α : ℝ := 2 / (b - a)
  let β : ℝ := -(a + b) / (b - a)
  let f : ℝ → ℝ := fun x => g (α * x + β)
  have hf_smooth : ContDiff ℝ ∞ f :=
    hg.comp ((contDiff_const.mul contDiff_id).add contDiff_const)
  have hf_deriv : ∀ m : ℕ, ∀ x : ℝ, iteratedDeriv m f x = α ^ m * iteratedDeriv m g (α * x + β) := by
    intro m
    induction m with
    | zero => intro x; simp [f]
    | succ m ih =>
      intro x
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have hfun : iteratedDeriv m f = fun y => α ^ m * iteratedDeriv m g (α * y + β) := funext ih
      rw [hfun]
      have h1 : HasDerivAt (fun y => α * y + β) α x := by
        simpa using ((hasDerivAt_id x).const_mul α).add_const β
      have h2 : HasDerivAt (iteratedDeriv m g) (deriv (iteratedDeriv m g) (α * x + β)) (α * x + β) :=
        (hg.differentiable_iteratedDeriv m (natCast_lt_infty m) (α * x + β)).hasDerivAt
      have h3 := (h2.comp x h1).const_mul (α ^ m)
      dsimp only [Function.comp_def] at h3
      rw [h3.deriv, pow_succ]
      ring
  have hcomp_id : ∀ u : ℝ, α * affineToIcc a b u + β = u := by
    intro u; dsimp [α, β, affineToIcc]; field_simp [hL.ne']; ring
  have hL1_scale : ∀ m : ℕ,
      ∫ x in a..b, |iteratedDeriv m f x| =
        ((b - a) / 2) * α ^ m * ∫ u in (-1 : ℝ)..1, |iteratedDeriv m g u| := by
    intro m
    have hsub := intervalIntegral_comp_affineToIcc hab (fun x => |iteratedDeriv m f x|)
      (u₁ := -1) (u₂ := 1)
    rw [affineToIcc_neg_one, affineToIcc_one] at hsub
    have hleft : ∫ u in (-1 : ℝ)..1, |iteratedDeriv m f (affineToIcc a b u)| =
        α ^ m * ∫ u in (-1 : ℝ)..1, |iteratedDeriv m g u| := by
      have hα_pos : 0 < α := by dsimp [α]; positivity
      have hfun : (fun u => |iteratedDeriv m f (affineToIcc a b u)|) =
          fun u => α ^ m * |iteratedDeriv m g u| := by
        ext u; rw [hf_deriv m, hcomp_id, abs_mul, abs_of_pos (pow_pos hα_pos m)]
      rw [hfun, intervalIntegral.integral_const_mul]
    rw [hleft] at hsub
    have hmul := congrArg (fun z => ((b - a) / 2) * z) hsub
    rw [← mul_assoc ((b - a) / 2) ((b - a) / 2)⁻¹, mul_inv_cancel₀ hL2.ne', one_mul] at hmul
    linarith [hmul.symm]
  have htest := hB f hf_smooth
  rw [hL1_scale (k + 1), hL1_scale (k + 2)] at htest
  have hL1_0 : ∫ y in a..b, |f y| = ((b - a) / 2) * ∫ u in (-1 : ℝ)..1, |g u| := by
    simpa [iteratedDeriv_zero, pow_zero, mul_one] using hL1_scale 0
  rw [hL1_0] at htest
  have hα_pos : 0 < α := by dsimp [α]; positivity
  have hfac_pos : 0 < ((b - a) / 2) * α ^ (k + 1) := by positivity
  have hdiv := (mul_le_mul_iff_of_pos_left (inv_pos.mpr hfac_pos)).mpr htest
  refine le_trans ?_ (hdiv.trans_eq ?_)
  · rw [← mul_assoc, inv_mul_cancel₀ hfac_pos.ne', one_mul]
  · unfold firstBestConstant
    rw [zpow_neg, zpow_natCast, mul_add]
    have h4 : (4 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (k + 1) := by
      rw [← mul_pow]; norm_num
    have ht1 : (((b - a) / 2) * α ^ (k + 1))⁻¹ *
        ((4 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * ((b - a) ^ (k + 1))⁻¹ *
          ((b - a) / 2 * ∫ u in (-1 : ℝ)..1, |g u|)) =
        (2 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * ∫ u in (-1 : ℝ)..1, |g u| := by
      dsimp [α]; rw [h4, div_pow]; field_simp [hL.ne']
    have ht2 : (((b - a) / 2) * α ^ (k + 1))⁻¹ *
        (B * ((b - a) / 2 * α ^ (k + 2) * ∫ u in (-1 : ℝ)..1, |iteratedDeriv (k + 2) g u|)) =
        B / ((b - a) / 2) * ∫ u in (-1 : ℝ)..1, |iteratedDeriv (k + 2) g u| := by
      rw [pow_succ α (k + 1)]; dsimp [α]; field_simp [hL.ne']
    rw [ht1, ht2]

/-! ### `C^{n+1}([a, b])` equality characterization (Theorem 1 `thm:full`) -/

/-- Helper: if a continuous nonnegative function on `[a, b]` (`a < b`) has zero integral,
it vanishes identically on `[a, b]`. -/
private theorem eq_zero_on_Icc_of_integral_eq_zero {a b : ℝ} (hab : a < b) {g : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Icc a b)) (hg_nonneg : ∀ x ∈ Icc a b, 0 ≤ g x)
    (hg_int : ∫ x in a..b, g x = 0) :
    ∀ x ∈ Icc a b, g x = 0 := by
  rw [intervalIntegral.integral_of_le hab.le] at hg_int
  have hEqOn := (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hg_nonneg x (Ioc_subset_Icc_self hx))
    (hg_cont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)).mp hg_int
  have hIoo : ∀ x ∈ Ioo a b, g x = 0 := by
    intro x hx
    by_contra hne
    have hpos : 0 < g x := lt_of_le_of_ne (hg_nonneg x (Ioo_subset_Icc_self hx)) (Ne.symm hne)
    have hcont_at : ContinuousAt g x :=
      hg_cont.continuousAt (Icc_mem_nhds hx.1 hx.2)
    have hev : ∀ᶠ z in 𝓝 x, 0 < g z := hcont_at.eventually (Ioi_mem_nhds hpos)
    obtain ⟨U, hU_sub, hU_open, hxU⟩ := mem_nhds_iff.mp hev
    have hmeas_pos : 0 < volume (Ioo a b ∩ U) :=
      (isOpen_Ioo.inter hU_open).measure_pos volume ⟨x, hx, hxU⟩
    have hsub : Ioo a b ∩ U ⊆ {z | z ∈ Ioc a b ∧ g z ≠ 0} := by
      intro z ⟨hz1, hz2⟩
      exact ⟨Ioo_subset_Ioc_self hz1, ne_of_gt (hU_sub hz2)⟩
    have hae0 : volume {z | z ∈ Ioc a b ∧ g z ≠ 0} = 0 := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at hEqOn
      have hset : {z | z ∈ Ioc a b ∧ g z ≠ 0} = {z | ¬(z ∈ Ioc a b → g z = 0)} := by
        ext z; simp only [Set.mem_setOf_eq, ne_eq, Classical.not_imp]
      rw [hset]
      exact ae_iff.mp hEqOn
    exact hmeas_pos.ne' (measure_mono_null hsub hae0)
  intro x hx
  have hmem_cl : x ∈ closure (Ioo a b) := by rw [closure_Ioo hab.ne]; exact hx
  obtain ⟨u, hu_mem, hu_lim⟩ := mem_closure_iff_seq_limit.mp hmem_cl
  have hgu : Tendsto (g ∘ u) atTop (𝓝 (g x)) :=
    (hg_cont x hx).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hu_lim
        (Eventually.of_forall fun n => Ioo_subset_Icc_self (hu_mem n)))
  have hzero : (g ∘ u) = fun _ => 0 := by ext n; exact hIoo (u n) (hu_mem n)
  rw [hzero] at hgu
  exact tendsto_nhds_unique hgu tendsto_const_nhds

/-- Equality characterization on `[-1, 1]` for any `F : SobolevW1 (k + 2) (-1) 1 f` whose top
derivative `F.d (k + 2)` is continuous on `[-1, 1]`. -/
theorem sharp_sobolev_unit_eq_iff_of_continuous_top (k : ℕ)
    (hstrict : ∀ t ∈ Icc (-1 : ℝ) 1, t ≠ 0 →
      explicitError (k + 1) (orderedNode k t) t < centerBestConstant (k + 1))
    {f : ℝ → ℝ} (F : SobolevW1 (k + 2) (-1) 1 f)
    (htop_cont : ContinuousOn (F.d (k + 2)) (Icc (-1 : ℝ) 1)) :
    (∫ x in (-1 : ℝ)..1, |F.d (k + 1) x| =
      firstBestConstant (k + 1) * (∫ y in (-1 : ℝ)..1, |f y|) +
        centerBestConstant (k + 1) * (∫ t in (-1 : ℝ)..1, |F.d (k + 2) t|)) →
    ∃ c : ℝ, ∀ x ∈ Icc (-1 : ℝ) 1, f x = c * (U ℝ ((k + 1 : ℕ) : ℤ)).eval x := by
  intro heq
  have hmax : ∀ t ∈ Icc (-1 : ℝ) 1,
      explicitError (k + 1) (orderedNode k t) t ≤ centerBestConstant (k + 1) := by
    intro t ht
    by_cases ht0 : t = 0
    · subst ht0; rw [explicitError_center_eq]
    · exact (hstrict t ht ht0).le
  have hf_int : IntegrableOn f (Icc (-1 : ℝ) 1) volume :=
    (F.continuousOn_d 0 (Nat.zero_lt_succ _)).integrableOn_Icc.congr_fun
      (fun x hx => F.d_zero x hx) measurableSet_Icc
  have hT_int := intervalIntegrable_movingOperator k hf_int
  have hd_int : IntervalIntegrable (F.d (k + 1)) volume (-1) 1 :=
    (F.continuousOn_d (k + 1) (Nat.lt_succ_self _)).intervalIntegrable_of_Icc (by norm_num)
  have htri : ∫ x in (-1 : ℝ)..1, |F.d (k + 1) x| ≤
      (∫ x in (-1 : ℝ)..1, |movingOperator k f x|) +
        ∫ x in (-1 : ℝ)..1, |F.d (k + 1) x - movingOperator k f x| := by
    rw [← intervalIntegral.integral_add hT_int.abs (hd_int.sub hT_int).abs]
    apply intervalIntegral.integral_mono_on (by norm_num) hd_int.abs
      (hT_int.abs.add (hd_int.sub hT_int).abs)
    intro x _
    calc |F.d (k + 1) x| = |movingOperator k f x + (F.d (k + 1) x - movingOperator k f x)| := by
            ring_nf
      _ ≤ _ := abs_add_le _ _
  have h1 := movingOperator_L1_le k hf_int
  have h2 := F.L1_deriv_sub_movingOperator_le k
  have hE_cont : Continuous (fun t => explicitError (k + 1) (orderedNode k t) t) := by
    unfold explicitError
    have hc : ∀ j : Fin (k + 2), Continuous (fun t => orderedNode k t j) :=
      fun j => continuous_orderedNode k j
    fun_prop
  have hgap_cont : ContinuousOn
      (fun t => (centerBestConstant (k + 1) - explicitError (k + 1) (orderedNode k t) t) *
        |F.d (k + 2) t|) (Icc (-1 : ℝ) 1) :=
    (continuousOn_const.sub hE_cont.continuousOn).mul htop_cont.abs
  have hgap_nonneg : ∀ t ∈ Icc (-1 : ℝ) 1,
      0 ≤ (centerBestConstant (k + 1) - explicitError (k + 1) (orderedNode k t) t) *
        |F.d (k + 2) t| :=
    fun t ht => mul_nonneg (sub_nonneg.mpr (hmax t ht)) (abs_nonneg _)
  have hgap_int_le : ∫ t in (-1 : ℝ)..1,
      (centerBestConstant (k + 1) - explicitError (k + 1) (orderedNode k t) t) *
        |F.d (k + 2) t| ≤ 0 := by
    have hi1 : IntervalIntegrable (fun t => centerBestConstant (k + 1) * |F.d (k + 2) t|)
        volume (-1) 1 :=
      (continuousOn_const.mul htop_cont.abs).intervalIntegrable_of_Icc (by norm_num)
    have hi2 : IntervalIntegrable
        (fun t => explicitError (k + 1) (orderedNode k t) t * |F.d (k + 2) t|) volume (-1) 1 :=
      (hE_cont.continuousOn.mul htop_cont.abs).intervalIntegrable_of_Icc (by norm_num)
    have hsplit : ∫ t in (-1 : ℝ)..1,
        (centerBestConstant (k + 1) - explicitError (k + 1) (orderedNode k t) t) *
          |F.d (k + 2) t| =
        centerBestConstant (k + 1) * (∫ t in (-1 : ℝ)..1, |F.d (k + 2) t|) -
          ∫ t in (-1 : ℝ)..1, explicitError (k + 1) (orderedNode k t) t * |F.d (k + 2) t| := by
      have hfun : (fun t =>
          (centerBestConstant (k + 1) - explicitError (k + 1) (orderedNode k t) t) *
            |F.d (k + 2) t|) =
          fun t => centerBestConstant (k + 1) * |F.d (k + 2) t| -
            explicitError (k + 1) (orderedNode k t) t * |F.d (k + 2) t| := by ext t; ring
      rw [hfun, intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul]
    linarith
  have hgap_int_zero : ∫ t in (-1 : ℝ)..1,
      (centerBestConstant (k + 1) - explicitError (k + 1) (orderedNode k t) t) *
        |F.d (k + 2) t| = 0 :=
    le_antisymm hgap_int_le
      (intervalIntegral.integral_nonneg (by norm_num) hgap_nonneg)
  have hgap_zero := eq_zero_on_Icc_of_integral_eq_zero (by norm_num : (-1 : ℝ) < 1)
    hgap_cont hgap_nonneg hgap_int_zero
  have htop_zero_ne : ∀ t ∈ Icc (-1 : ℝ) 1, t ≠ 0 → F.d (k + 2) t = 0 := by
    intro t ht ht0
    have hz := hgap_zero t ht
    have hpos : 0 < centerBestConstant (k + 1) - explicitError (k + 1) (orderedNode k t) t :=
      sub_pos.mpr (hstrict t ht ht0)
    have habs0 : |F.d (k + 2) t| = 0 := (mul_eq_zero.mp hz).resolve_left hpos.ne'
    exact abs_eq_zero.mp habs0
  have htop_zero : ∀ t ∈ Icc (-1 : ℝ) 1, F.d (k + 2) t = 0 := by
    intro t ht
    by_cases ht0 : t = 0
    · subst ht0
      have hseq_eq : (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 2)) =
          (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) ∘ (fun m : ℕ => m + 1) := by
        ext m; dsimp [Function.comp_def]; push_cast; ring
      have hseq : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 2)) atTop (𝓝 0) := by
        rw [hseq_eq]
        exact tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
      have hmem : ∀ m : ℕ, (1 : ℝ) / ((m : ℝ) + 2) ∈ Icc (-1 : ℝ) 1 := by
        intro m
        have hm : (0 : ℝ) < (m : ℝ) + 2 := by positivity
        constructor
        · linarith [div_pos zero_lt_one hm]
        · rw [div_le_one hm]; linarith [Nat.cast_nonneg (α := ℝ) m]
      have hlim : Tendsto (fun m : ℕ => F.d (k + 2) (1 / ((m : ℝ) + 2))) atTop (𝓝 (F.d (k + 2) 0)) :=
        (htop_cont 0 ⟨by norm_num, by norm_num⟩).tendsto.comp
          (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hseq
            (Eventually.of_forall hmem))
      have hconst0 : (fun m : ℕ => F.d (k + 2) (1 / ((m : ℝ) + 2))) = fun _ => 0 := by
        ext m
        exact htop_zero_ne _ (hmem m) (div_ne_zero one_ne_zero (by positivity))
      rw [hconst0] at hlim
      exact tendsto_nhds_unique hlim tendsto_const_nhds
    · exact htop_zero_ne t ht ht0
  let P : ℝ[X] := ∑ r ∈ Finset.range (k + 2),
    C (F.d r (-1) / (r.factorial : ℝ)) * (X - C (-1 : ℝ)) ^ r
  have hdeg_X1 : (X - C (-1 : ℝ)).natDegree = 1 := by
    have hrew : X - C (-1 : ℝ) = X + C (1 : ℝ) := by simp [sub_eq_add_neg]
    rw [hrew, Polynomial.natDegree_X_add_C]
  have hdeg_pow : ∀ r : ℕ, ((X - C (-1 : ℝ)) ^ r).natDegree = r := by
    intro r; rw [Polynomial.natDegree_pow, hdeg_X1, mul_one]
  have hP_deg : P.natDegree ≤ k + 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun r hr => ?_
    have hr' : r ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    calc (C (F.d r (-1) / (r.factorial : ℝ)) * (X - C (-1 : ℝ)) ^ r).natDegree
        ≤ ((X - C (-1 : ℝ)) ^ r).natDegree := natDegree_C_mul_le _ _
      _ = r := hdeg_pow r
      _ ≤ k + 1 := hr'
  have hf_eq_P : ∀ y ∈ Icc (-1 : ℝ) 1, f y = P.eval y := by
    intro y hy
    rw [F.taylor_formula (by norm_num : (-1 : ℝ) ≤ 1) hy]
    have hrem0 : ∫ t in (-1 : ℝ)..1, normTruncatedPower (k + 1) t y * F.d (k + 2) t = 0 := by
      rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact setIntegral_eq_zero_of_forall_eq_zero fun t ht => by
        rw [htop_zero t (Ioc_subset_Icc_self ht), mul_zero]
    rw [hrem0, add_zero]
    simp [P, eval_finsetSum]
  have hdn_const : ∀ x ∈ Icc (-1 : ℝ) 1, F.d (k + 1) x = F.d (k + 1) (-1) := by
    intro x hx
    have hftc := F.ftc (k + 1) (Nat.lt_succ_self _) x hx
    have hz : ∫ t in (-1 : ℝ)..x, F.d (k + 2) t = 0 := by
      rw [intervalIntegral.integral_of_le hx.1]
      exact setIntegral_eq_zero_of_forall_eq_zero fun t ht =>
        htop_zero t ⟨ht.1.le, le_trans ht.2 hx.2⟩
    linarith
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
  have hdn_eq_P : ∀ x ∈ Icc (-1 : ℝ) 1,
      F.d (k + 1) x = iteratedDeriv (k + 1) (fun y => P.eval y) x := by
    intro x hx
    rw [hdn_const x hx, iteratedDeriv_polynomial_eval_of_natDegree_le P (k + 1) hP_deg x, hP_coeff]
    have hfac : ((k + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp [hfac]
  have hP_eq_L1 : ∫ x in (-1 : ℝ)..1, |iteratedDeriv (k + 1) (fun y => P.eval y) x| =
      firstBestConstant (k + 1) * ∫ y in (-1 : ℝ)..1, |P.eval y| := by
    have htop_int0 : ∫ t in (-1 : ℝ)..1, |F.d (k + 2) t| = 0 := by
      rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact setIntegral_eq_zero_of_forall_eq_zero fun t ht => by
        rw [htop_zero t (Ioc_subset_Icc_self ht), abs_zero]
    have hLHS : ∫ x in (-1 : ℝ)..1, |F.d (k + 1) x| =
        ∫ x in (-1 : ℝ)..1, |iteratedDeriv (k + 1) (fun y => P.eval y) x| := by
      apply intervalIntegral.integral_congr
      intro x hx; rw [uIcc_of_le (by norm_num)] at hx; dsimp only; rw [hdn_eq_P x hx]
    have hRHS : ∫ y in (-1 : ℝ)..1, |f y| = ∫ y in (-1 : ℝ)..1, |P.eval y| := by
      apply intervalIntegral.integral_congr
      intro y hy; rw [uIcc_of_le (by norm_num)] at hy; dsimp only; rw [hf_eq_P y hy]
    rw [hLHS, hRHS, htop_int0, mul_zero, add_zero] at heq
    exact heq
  obtain ⟨c, hc⟩ := (polynomial_L1_deriv_eq_iff (k + 1) P hP_deg).mp hP_eq_L1
  refine ⟨c, fun x hx => ?_⟩
  rw [hf_eq_P x hx, hc, eval_mul, eval_C]

/-- **`C^{n+1}([a, b])` equality characterization (Theorem 1 `thm:full`)**:
assuming `E_n(t) < E_n(0)` for all `t ∈ [-1, 1] \ {0}`, a function `f ∈ C^{n+1}([a, b])`
(`a < b`, `n = k + 1`) achieves equality in the sharp `L¹` Sobolev interpolation inequality
if and only if `∀ x ∈ [a, b], f x = c * U_n((2x - a - b)/(b - a))` for some `c : ℝ`. -/
theorem sharp_sobolev_contDiffOn_Icc_eq_iff (k : ℕ) {a b : ℝ} (hab : a < b)
    (hstrict : ∀ t ∈ Icc (-1 : ℝ) 1, t ≠ 0 →
      explicitError (k + 1) (orderedNode k t) t < centerBestConstant (k + 1))
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ (k + 2) f (Icc a b)) :
    (∫ x in a..b, |iteratedDerivWithin (k + 1) f (Icc a b) x| =
      (4 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * (b - a) ^ (-((k + 1 : ℕ) : ℤ)) *
          (∫ y in a..b, |f y|) +
        ((b - a) / 2) * centerBestConstant (k + 1) *
          (∫ t in a..b, |iteratedDerivWithin (k + 2) f (Icc a b) t|)) ↔
    ∃ c : ℝ, ∀ x ∈ Icc a b, f x = c * (U ℝ ((k + 1 : ℕ) : ℤ)).eval ((2 * x - a - b) / (b - a)) := by
  have hL : 0 < b - a := sub_pos.mpr hab
  have hL2 : 0 < (b - a) / 2 := by linarith
  constructor
  · intro heq
    let F := SobolevW1.ofContDiffOn hab hf
    let G := F.rescaleToUnit hab
    have htop_cont : ContinuousOn (G.d (k + 2)) (Icc (-1 : ℝ) 1) := by
      have hFtop : ContinuousOn (F.d (k + 2)) (Icc a b) :=
        hf.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Icc hab)
      have hphi : Continuous (fun u => affineToIcc a b u) := by unfold affineToIcc; fun_prop
      exact continuousOn_const.mul (hFtop.comp hphi.continuousOn
        (fun u hu => affineToIcc_mem_Icc hab.le hu))
    have hunit_eq : ∫ u in (-1 : ℝ)..1, |G.d (k + 1) u| =
        firstBestConstant (k + 1) * (∫ u in (-1 : ℝ)..1, |f (affineToIcc a b u)|) +
          centerBestConstant (k + 1) * (∫ u in (-1 : ℝ)..1, |G.d (k + 2) u|) := by
      have h0 : ∫ u in (-1 : ℝ)..1, |f (affineToIcc a b u)| =
          ((b - a) / 2)⁻¹ * ∫ y in a..b, |f y| := by
        rw [intervalIntegral_comp_affineToIcc hab (fun y => |f y|), affineToIcc_neg_one,
          affineToIcc_one]
      rw [h0, F.rescaleToUnit_L1 hab (k + 1), F.rescaleToUnit_L1 hab (k + 2)]
      change ((b - a) / 2) ^ (k + 1) * ((b - a) / 2)⁻¹ *
          (∫ x in a..b, |iteratedDerivWithin (k + 1) f (Icc a b) x|) =
        firstBestConstant (k + 1) * (((b - a) / 2)⁻¹ * ∫ y in a..b, |f y|) +
          centerBestConstant (k + 1) *
            (((b - a) / 2) ^ (k + 2) * ((b - a) / 2)⁻¹ *
              ∫ t in a..b, |iteratedDerivWithin (k + 2) f (Icc a b) t|)
      rw [heq, zpow_neg, zpow_natCast]
      unfold firstBestConstant
      have h4 : (4 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (k + 1) := by
        rw [← mul_pow]; norm_num
      rw [h4, pow_succ ((b - a) / 2) (k + 1), div_pow]
      field_simp [hL.ne']
    obtain ⟨c, hc⟩ := sharp_sobolev_unit_eq_iff_of_continuous_top k hstrict G htop_cont hunit_eq
    refine ⟨c, fun x hx => ?_⟩
    have hu := inv_affineToIcc_mem_Icc hab hx
    have h1 := hc ((2 * x - a - b) / (b - a)) hu
    rwa [affineToIcc_inv a b x hab] at h1
  · rintro ⟨c, hc⟩
    let linP : ℝ[X] := C (2 / (b - a)) * X - C ((a + b) / (b - a))
    let P : ℝ[X] := C c * (U ℝ ((k + 1 : ℕ) : ℤ)).comp linP
    have hlin_eval : ∀ x : ℝ, linP.eval x = (2 * x - a - b) / (b - a) := by
      intro x; simp only [linP, eval_sub, eval_mul, eval_C, eval_X]; ring
    have hf_eqOn : Set.EqOn f (fun x => P.eval x) (Icc a b) := by
      intro x hx
      rw [hc x hx]
      simp [P, eval_comp, hlin_eval]
    have hP_smooth : ContDiff ℝ ∞ (fun x => P.eval x) := by
      simpa [Polynomial.aeval_def] using P.contDiff_aeval (𝕜 := ℝ) ∞
    have hderiv_eqOn : ∀ m : ℕ, ∀ x ∈ Icc a b,
        iteratedDerivWithin m f (Icc a b) x = iteratedDeriv m (fun y => P.eval y) x := by
      intro m x hx
      rw [iteratedDerivWithin_congr hf_eqOn hx,
        iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
          (hP_smooth.contDiffAt.of_le (natCast_le_infty m)) hx]
    have hlin_deg : linP.natDegree = 1 := by
      apply le_antisymm
      · calc linP.natDegree ≤ max (C (2 / (b - a)) * X).natDegree (C ((a + b) / (b - a))).natDegree :=
              natDegree_sub_le _ _
          _ ≤ 1 := by
            simp only [natDegree_C, max_eq_left (Nat.zero_le _)]
            exact (natDegree_C_mul_le _ _).trans (by simp)
      · apply Polynomial.le_natDegree_of_ne_zero
        simp only [linP, coeff_sub, coeff_C_mul, coeff_X_one, mul_one, coeff_C_succ, sub_zero]
        positivity
    have hU_deg : (U ℝ ((k + 1 : ℕ) : ℤ)).natDegree = k + 1 :=
      Polynomial.Chebyshev.natDegree_U_natCast ℝ (k + 1)
    have hU_lc : (U ℝ ((k + 1 : ℕ) : ℤ)).leadingCoeff = (2 : ℝ) ^ (k + 1) :=
      Polynomial.Chebyshev.leadingCoeff_U_natCast ℝ (k + 1)
    have hcomp_deg : ((U ℝ ((k + 1 : ℕ) : ℤ)).comp linP).natDegree = k + 1 := by
      rw [Polynomial.natDegree_comp, hU_deg, hlin_deg, mul_one]
    have hcomp_lc : ((U ℝ ((k + 1 : ℕ) : ℤ)).comp linP).leadingCoeff =
        (2 : ℝ) ^ (k + 1) * (2 / (b - a)) ^ (k + 1) := by
      rw [Polynomial.leadingCoeff_comp (by rw [hlin_deg]; omega), hU_deg, hU_lc,
        leadingCoeff, hlin_deg]
      simp [linP]
    have hP_deg : P.natDegree ≤ k + 1 := by
      calc P.natDegree ≤ ((U ℝ ((k + 1 : ℕ) : ℤ)).comp linP).natDegree := natDegree_C_mul_le _ _
        _ = k + 1 := hcomp_deg
    have hP_coeff : P.coeff (k + 1) = c * ((2 : ℝ) ^ (k + 1) * (2 / (b - a)) ^ (k + 1)) := by
      rw [coeff_C_mul]
      have h1 : ((U ℝ ((k + 1 : ℕ) : ℤ)).comp linP).coeff (k + 1) =
          (2 : ℝ) ^ (k + 1) * (2 / (b - a)) ^ (k + 1) := by
        rwa [leadingCoeff, hcomp_deg] at hcomp_lc
      rw [h1]
    have hLHS : ∫ x in a..b, |iteratedDerivWithin (k + 1) f (Icc a b) x| =
        (b - a) * (((k + 1).factorial : ℝ) * |c| *
          ((2 : ℝ) ^ (k + 1) * (2 / (b - a)) ^ (k + 1))) := by
      have hcongr : ∫ x in a..b, |iteratedDerivWithin (k + 1) f (Icc a b) x| =
          ∫ x in a..b, |iteratedDeriv (k + 1) (fun y => P.eval y) x| := by
        apply intervalIntegral.integral_congr
        intro x hx; rw [uIcc_of_le hab.le] at hx; dsimp only; rw [hderiv_eqOn (k + 1) x hx]
      rw [hcongr]
      simp_rw [iteratedDeriv_polynomial_eval_of_natDegree_le P (k + 1) hP_deg, hP_coeff]
      rw [intervalIntegral.integral_const, smul_eq_mul, abs_mul, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (k + 1) * (2 / (b - a)) ^ (k + 1))]
      ring
    have htop0 : ∫ t in a..b, |iteratedDerivWithin (k + 2) f (Icc a b) t| = 0 := by
      have hcongr : ∫ t in a..b, |iteratedDerivWithin (k + 2) f (Icc a b) t| =
          ∫ t in a..b, |iteratedDeriv (k + 2) (fun y => P.eval y) t| := by
        apply intervalIntegral.integral_congr
        intro t ht; rw [uIcc_of_le hab.le] at ht; dsimp only; rw [hderiv_eqOn (k + 2) t ht]
      rw [hcongr]
      simp_rw [iteratedDeriv_polynomial_eval_of_natDegree_le P (k + 2) (Nat.le_succ_of_le hP_deg),
        Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hP_deg), mul_zero, abs_zero,
        intervalIntegral.integral_zero]
    have hL1f : ∫ y in a..b, |f y| = (b - a) * |c| := by
      have hsub := intervalIntegral_comp_affineToIcc hab (fun y => |f y|) (u₁ := -1) (u₂ := 1)
      rw [affineToIcc_neg_one, affineToIcc_one] at hsub
      have hleft : ∫ u in (-1 : ℝ)..1, |f (affineToIcc a b u)| = 2 * |c| := by
        have hcongr : ∫ u in (-1 : ℝ)..1, |f (affineToIcc a b u)| =
            ∫ u in (-1 : ℝ)..1, |c| * |(U ℝ ((k + 1 : ℕ) : ℤ)).eval u| := by
          apply intervalIntegral.integral_congr
          intro u hu
          rw [uIcc_of_le (by norm_num)] at hu
          dsimp only
          rw [hc (affineToIcc a b u) (affineToIcc_mem_Icc hab.le hu)]
          have harg : (2 * affineToIcc a b u - a - b) / (b - a) = u := by
            unfold affineToIcc; field_simp [hL.ne']; ring
          rw [harg, abs_mul]
        rw [hcongr, intervalIntegral.integral_const_mul, intervalIntegral_abs_U]
        ring
      rw [hleft] at hsub
      have hmul := congrArg (fun z => ((b - a) / 2) * z) hsub
      rw [← mul_assoc ((b - a) / 2) ((b - a) / 2)⁻¹, mul_inv_cancel₀ hL2.ne', one_mul] at hmul
      linarith [hmul.symm]
    rw [hLHS, hL1f, htop0, mul_zero, add_zero, zpow_neg, zpow_natCast]
    have h4 : (4 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (k + 1) := by
      rw [← mul_pow]; norm_num
    rw [h4, div_pow]
    field_simp [hL.ne']

end SharpL1.Analysis
