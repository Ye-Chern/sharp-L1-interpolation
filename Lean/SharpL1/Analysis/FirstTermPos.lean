module

public import SharpL1.JacobiOrdered
public import SharpL1.Probability.WeightedComparison
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-!
# Strict positivity of the first term in the H' decomposition (Claim 4)

This file formalizes Claim 4 (`clm:first-term`) of `chebyshev_L1_complete.tex`:
for all orders `n = k + 1 ≥ 1` and all `t > 0`,

  `(1 / 2) * (lawSignMean(Q_t^0 + (t + 1) e_+) + lawSignMean(Q_t^0 + (t - 1) e_-)) > 0`

where `Q_t^0` is the weighted exponential sum with coefficients `[t - u_0(t), ..., t - u_n(t)]`.

Proof outline (following `chebyshev_L1_complete.tex` §5):
1. Realize `Q_t^0` as the real quadratic form `((xᵀ (t I - J_n(t)) x) + (yᵀ (t I - J_n(t)) y)) / 2`
   for two independent standard real Gaussian vectors `x, y ∈ EuclideanSpace ℝ (Fin (k + 2))`.
   By orthogonal invariance of the standard Gaussian measure (`LinearIsometryEquiv.measurePreserving`)
   and the spectral theorem for the symmetric Jacobi matrix `jacobiMatrix k t`, this quadratic form
   has the exact law `weightedExpSum (List.ofFn fun i => t - orderedNode k t i)`.
2. Write `t I - J_n(t) = t D_n^0 - J_n(0)` (`jacobi_pencil_affine`).
   The alternating-sign isometry `S = diag(1, -1, 1, -1, ...)` preserves the standard Gaussian
   measure, fixes `D_n^0`, and negates `J_n(0)`.
3. Coupling with an independent `e ~ Exp(1)`, setting `X = t (A + e) > 0` a.e. and `Y = e - Z`,
   we obtain `law(Q_t^0 + (t + 1) e_+) = law(X + Y)` and `law(Q_t^0 + (t - 1) e_-) = law(X - Y)`,
   so the average sign expectation equals `P(|Y| < X)`.
4. At the explicit witness `x₀ = (1, 1, 0, ..., 0)`, `y₀ = 0`, `e₀ = 1/2`, we have
   `Z₀ = 1/2 = e₀` so `|Y₀| = 0 < t (A₀ + e₀) = X₀`. By continuity and strict positivity of
   the product Gaussian-exponential density on `ℝ^{k+2} × ℝ^{k+2} × (0, ∞)`, `P(|Y| < X) > 0`.
-/

namespace SharpL1.Analysis

open MeasureTheory Set

/-! ### Standard Gaussian measure on `EuclideanSpace ℝ (Fin m)` -/

/-- Standard Gaussian probability density on `EuclideanSpace ℝ (Fin m)`. -/
noncomputable def stdGaussDensity (m : ℕ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ ^ m * Real.exp (-‖x‖ ^ 2 / 2)

/-- Standard Gaussian measure on `EuclideanSpace ℝ (Fin m)`. -/
noncomputable def stdGaussMeasure (m : ℕ) : Measure (EuclideanSpace ℝ (Fin m)) :=
  volume.withDensity fun x => ENNReal.ofReal (stdGaussDensity m x)

private theorem stdGaussDensity_pos (m : ℕ) (x : EuclideanSpace ℝ (Fin m)) :
    0 < stdGaussDensity m x := by
  unfold stdGaussDensity
  have hpi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  positivity

private theorem stdGaussDensity_continuous (m : ℕ) : Continuous (stdGaussDensity m) := by
  unfold stdGaussDensity
  fun_prop

private theorem stdGaussDensity_eq_prod_gaussianPDFReal (m : ℕ) (x : EuclideanSpace ℝ (Fin m)) :
    stdGaussDensity m x = ∏ i : Fin m, ProbabilityTheory.gaussianPDFReal 0 1 (x i) := by
  have hnorm : ‖x‖ ^ 2 = ∑ i : Fin m, (x i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Real.norm_eq_abs, sq_abs]
  unfold stdGaussDensity
  simp only [ProbabilityTheory.gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum]
  congr 2
  rw [hnorm, ← Finset.sum_div, ← Finset.sum_neg_distrib]

private theorem withDensity_prod_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SigmaFinite μ] [SigmaFinite ν]
    {f : α → ENNReal} {g : β → ENNReal} (hf : Measurable f) (hg : Measurable g)
    [SigmaFinite (μ.withDensity f)] [SigmaFinite (ν.withDensity g)] :
    (μ.withDensity f).prod (ν.withDensity g) =
      (μ.prod ν).withDensity (fun p => f p.1 * g p.2) := by
  refine Measure.prod_eq (μ := μ.withDensity f) (ν := ν.withDensity g) fun s t hs ht => ?_
  rw [withDensity_apply _ (hs.prod ht),
    setLIntegral_prod (f := fun p : α × β => f p.1 * g p.2)
      ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).aemeasurable]
  simp_rw [lintegral_const_mul _ hg, lintegral_mul_const _ hf,
    withDensity_apply _ hs, withDensity_apply _ ht]

private theorem withDensity_pi_eq :
    ∀ (m : ℕ) {f : ℝ → ENNReal} (_hf : Measurable f) [IsProbabilityMeasure (volume.withDensity f)],
      Measure.pi (fun _ : Fin m => volume.withDensity f) =
        (volume : Measure (Fin m → ℝ)).withDensity (fun x => ∏ i : Fin m, f (x i))
  | 0, f, _, _ => by
    refine Measure.pi_eq (μ := fun _ : Fin 0 => volume.withDensity f) fun s _ => ?_
    have huniv : Set.univ.pi s = Set.univ := by ext x; simp
    rw [huniv, withDensity_apply _ MeasurableSet.univ]
    simp only [Fin.prod_univ_zero, Measure.restrict_univ, lintegral_one]
    change (Measure.pi fun _ : Fin 0 => (volume : Measure ℝ)) Set.univ = 1
    simp
  | m + 1, f, hf, hprob => by
    have ih := withDensity_pi_eq m hf
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    have hmp_prob : MeasurePreserving e
        (Measure.pi fun _ : Fin (m + 1) => volume.withDensity f)
        ((volume.withDensity f).prod (Measure.pi fun _ : Fin m => volume.withDensity f)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => volume.withDensity f) 0
    have hmp_vol : MeasurePreserving e
        (volume : Measure (Fin (m + 1) → ℝ))
        ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    have hmeas_rhs : Measurable (fun p : ℝ × (Fin m → ℝ) => f p.1 * ∏ i : Fin m, f (p.2 i)) :=
      (hf.comp measurable_fst).mul
        (Finset.measurable_prod Finset.univ fun i _ => hf.comp ((measurable_pi_apply i).comp measurable_snd))
    have hprod_eq :
        (volume.withDensity f).prod (Measure.pi fun _ : Fin m => volume.withDensity f) =
          ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).withDensity
            (fun p => f p.1 * ∏ i : Fin m, f (p.2 i)) := by
      rw [ih]
      have hmeas_m : Measurable (fun x : Fin m → ℝ => ∏ i : Fin m, f (x i)) :=
        Finset.measurable_prod Finset.univ fun i _ => hf.comp (measurable_pi_apply i)
      haveI : SigmaFinite ((volume : Measure (Fin m → ℝ)).withDensity (fun x => ∏ i : Fin m, f (x i))) := by
        rw [← ih]; infer_instance
      exact withDensity_prod_eq hf hmeas_m
    apply Measure.ext fun s hs => ?_
    have h1 : (Measure.pi fun _ : Fin (m + 1) => volume.withDensity f) s =
        ((volume.withDensity f).prod (Measure.pi fun _ : Fin m => volume.withDensity f)) (e.symm ⁻¹' s) := by
      rw [← hmp_prob.map_eq, Measure.map_apply e.measurable (e.symm.measurable hs)]
      congr 1; ext x; simp
    rw [h1, hprod_eq, withDensity_apply _ (e.symm.measurable hs), ← hmp_vol.map_eq,
      setLIntegral_map (e.symm.measurable hs) hmeas_rhs e.measurable]
    rw [withDensity_apply _ hs]
    have hpre : e ⁻¹' (e.symm ⁻¹' s) = s := by ext x; simp
    rw [hpre]
    refine setLIntegral_congr_fun hs fun x _ => ?_
    simp [e, Fin.prod_univ_succ, Fin.tail]

/-- Pushing `stdGaussMeasure m` forward along `WithLp.ofLp` yields the `m`-fold product
of standard real Gaussians `gaussianReal 0 1`. -/
theorem stdGaussMeasure_map_ofLp (m : ℕ) :
    (stdGaussMeasure m).map WithLp.ofLp =
      Measure.pi (fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1) := by
  have hpdf : ProbabilityTheory.gaussianReal 0 1 =
      volume.withDensity (ProbabilityTheory.gaussianPDF 0 1) :=
    ProbabilityTheory.gaussianReal_of_var_ne_zero 0 one_ne_zero
  haveI : IsProbabilityMeasure (volume.withDensity (ProbabilityTheory.gaussianPDF 0 1)) := by
    rw [← hpdf]; infer_instance
  have hmeas_pdf : Measurable (ProbabilityTheory.gaussianPDF 0 1) :=
    ProbabilityTheory.measurable_gaussianPDF 0 1
  rw [hpdf, withDensity_pi_eq m hmeas_pdf]
  have hmp := PiLp.volume_preserving_ofLp (Fin m)
  apply Measure.ext fun s hs => ?_
  rw [Measure.map_apply (WithLp.measurable_ofLp 2 _) hs, stdGaussMeasure,
    withDensity_apply _ (WithLp.measurable_ofLp 2 _ hs), withDensity_apply _ hs, ← hmp.map_eq]
  have hmeas_rhs : Measurable (fun x : Fin m → ℝ => ∏ i : Fin m, ProbabilityTheory.gaussianPDF 0 1 (x i)) :=
    Finset.measurable_prod Finset.univ fun i _ => hmeas_pdf.comp (measurable_pi_apply i)
  rw [setLIntegral_map hs hmeas_rhs (WithLp.measurable_ofLp 2 _)]
  refine setLIntegral_congr_fun (WithLp.measurable_ofLp 2 _ hs) fun x _ => ?_
  rw [stdGaussDensity_eq_prod_gaussianPDFReal]
  simp only [ProbabilityTheory.gaussianPDF]
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ => ProbabilityTheory.gaussianPDFReal_nonneg 0 1 _]

instance stdGaussMeasure_isProbability (m : ℕ) : IsProbabilityMeasure (stdGaussMeasure m) := by
  constructor
  have h := congrArg (fun μ : Measure (Fin m → ℝ) => μ Set.univ) (stdGaussMeasure_map_ofLp m)
  rw [Measure.map_apply (WithLp.measurable_ofLp 2 _) MeasurableSet.univ, Set.preimage_univ] at h
  exact h.trans measure_univ

/-- Any linear isometry equivalence of `EuclideanSpace ℝ (Fin m)` preserves `stdGaussMeasure m`. -/
theorem stdGaussMeasure_measurePreserving {m : ℕ}
    (T : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) :
    MeasurePreserving T (stdGaussMeasure m) (stdGaussMeasure m) := by
  refine ⟨T.continuous.measurable, ?_⟩
  have hvol := T.measurePreserving
  apply Measure.ext fun s hs => ?_
  rw [Measure.map_apply T.continuous.measurable hs, stdGaussMeasure,
    withDensity_apply _ (T.continuous.measurable hs), withDensity_apply _ hs]
  conv_rhs => rw [← hvol.map_eq]
  have hmeas_d : Measurable (fun x => ENNReal.ofReal (stdGaussDensity m x)) :=
    ENNReal.continuous_ofReal.measurable.comp (stdGaussDensity_continuous m).measurable
  rw [setLIntegral_map hs hmeas_d T.continuous.measurable]
  refine setLIntegral_congr_fun (T.continuous.measurable hs) fun x _ => ?_
  simp [stdGaussDensity, T.norm_map]

/-! ### Sum of two squared independent standard Gaussians divided by 2 is `Exp(1)` -/

private theorem gaussian_sq_half_eq_expMeasure :
    ((ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) / 2) =
      ProbabilityTheory.expMeasure 1 := by
  let g1 := ProbabilityTheory.gaussianReal 0 1
  have hmap_meas : Measurable (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) / 2) := by fun_prop
  haveI : IsProbabilityMeasure ((g1.prod g1).map (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) / 2)) :=
    ⟨by rw [Measure.map_apply hmap_meas MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    Probability.expMeasure_probability zero_lt_one
  apply Measure.ext_of_Iic
  intro s
  rw [Measure.map_apply hmap_meas measurableSet_Iic,
    ← ProbabilityTheory.ofReal_cdf (ProbabilityTheory.expMeasure 1) s,
    Probability.expMeasure_cdf_formula zero_lt_one s]
  by_cases hs : 0 ≤ s
  · rw [if_pos hs, one_mul]
    have hg1 : g1 = volume.withDensity (ProbabilityTheory.gaussianPDF 0 1) :=
      ProbabilityTheory.gaussianReal_of_var_ne_zero 0 one_ne_zero
    haveI : SigmaFinite ((volume : Measure ℝ).withDensity (ProbabilityTheory.gaussianPDF 0 1)) := by
      rw [← hg1]; infer_instance
    have hprod : g1.prod g1 =
        (volume : Measure (ℝ × ℝ)).withDensity
          (fun p => ProbabilityTheory.gaussianPDF 0 1 p.1 * ProbabilityTheory.gaussianPDF 0 1 p.2) := by
      have h1 : g1.prod g1 =
          ((volume : Measure ℝ).withDensity (ProbabilityTheory.gaussianPDF 0 1)).prod
            ((volume : Measure ℝ).withDensity (ProbabilityTheory.gaussianPDF 0 1)) := by
        rw [← hg1]
      rw [h1, withDensity_prod_eq (ProbabilityTheory.measurable_gaussianPDF 0 1)
        (ProbabilityTheory.measurable_gaussianPDF 0 1)]
      rfl
    have hS : MeasurableSet ((fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) / 2) ⁻¹' Iic s) :=
      hmap_meas measurableSet_Iic
    rw [hprod, withDensity_apply _ hS, ← lintegral_indicator hS]
    rw [← lintegral_comp_polarCoord_symm]
    -- Rewrite the integrand on `polarCoord.target = Ioi 0 ×ˢ Ioo (-π) π`
    have htarget : polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi := rfl
    rw [htarget]
    let rad : ℝ → ENNReal := fun r =>
      if r ≤ Real.sqrt (2 * s) then
        ENNReal.ofReal (r * (2 * Real.pi)⁻¹ * Real.exp (-r ^ 2 / 2))
      else 0
    have hcongr : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 •
          ((fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) / 2) ⁻¹' Iic s).indicator
            (fun p => ProbabilityTheory.gaussianPDF 0 1 p.1 * ProbabilityTheory.gaussianPDF 0 1 p.2)
            (polarCoord.symm p) = rad p.1 := by
      intro p hp
      have hr0 : 0 < p.1 := hp.1
      have hsq : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
        have hcs := Real.cos_sq_add_sin_sq p.2
        linear_combination p.1 ^ 2 * hcs
      have hiff : (p.1 ^ 2) / 2 ≤ s ↔ p.1 ≤ Real.sqrt (2 * s) := by
        rw [Real.le_sqrt hr0.le (by linarith)]
        constructor <;> intro h <;> linarith
      have hpdf_prod :
          ProbabilityTheory.gaussianPDF 0 1 (p.1 * Real.cos p.2) *
            ProbabilityTheory.gaussianPDF 0 1 (p.1 * Real.sin p.2) =
          ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.exp (-p.1 ^ 2 / 2)) := by
        simp only [ProbabilityTheory.gaussianPDF, ProbabilityTheory.gaussianPDFReal,
          NNReal.coe_one, mul_one, sub_zero]
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have hsqrt : (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹ = (2 * Real.pi)⁻¹ := by
          rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
        calc
          (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(p.1 * Real.cos p.2) ^ 2 / 2) *
              ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(p.1 * Real.sin p.2) ^ 2 / 2))
            = ((Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹) *
                (Real.exp (-(p.1 * Real.cos p.2) ^ 2 / 2) *
                  Real.exp (-(p.1 * Real.sin p.2) ^ 2 / 2)) := by ring
          _ = (2 * Real.pi)⁻¹ * Real.exp (-((p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2) / 2) := by
              rw [hsqrt, ← Real.exp_add]; congr 2; ring
          _ = (2 * Real.pi)⁻¹ * Real.exp (-p.1 ^ 2 / 2) := by rw [hsq]
      simp only [polarCoord_symm_apply, Set.indicator, Set.mem_preimage, Set.mem_Iic,
        hsq, hiff, smul_eq_mul, rad]
      split_ifs with hle
      · rw [hpdf_prod, ← ENNReal.ofReal_mul hr0.le]
        congr 1; ring
      · simp
    rw [setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hcongr]
    have hrad_meas : Measurable rad := by
      refine Measurable.ite measurableSet_Iic ?_ measurable_const
      exact ENNReal.continuous_ofReal.measurable.comp (by fun_prop)
    change ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, rad p.1 ∂(volume.prod volume) = _
    rw [setLIntegral_prod (f := fun p : ℝ × ℝ => rad p.1) (hrad_meas.comp measurable_fst).aemeasurable]
    simp_rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo,
      show Real.pi - -Real.pi = 2 * Real.pi by ring, lintegral_mul_const _ hrad_meas]
    -- Evaluate the radial integral over `Ioi 0`
    have hrad_ind : ∀ r : ℝ, rad r =
        (Set.Iic (Real.sqrt (2 * s))).indicator
          (fun r => ENNReal.ofReal (r * (2 * Real.pi)⁻¹ * Real.exp (-r ^ 2 / 2))) r := by
      intro r; simp [rad, Set.indicator]
    simp_rw [hrad_ind]
    rw [lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      Set.inter_comm, Set.Ioi_inter_Iic]
    have hcont : ContinuousOn (fun r : ℝ => r * (2 * Real.pi)⁻¹ * Real.exp (-r ^ 2 / 2))
        (Set.Icc 0 (Real.sqrt (2 * s))) := by fun_prop
    have hnonneg : ∀ r ∈ Set.Ioc (0 : ℝ) (Real.sqrt (2 * s)),
        0 ≤ r * (2 * Real.pi)⁻¹ * Real.exp (-r ^ 2 / 2) := fun r hr => by
      have : 0 < r := hr.1
      positivity
    rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hnonneg)),
      ← intervalIntegral.integral_of_le (Real.sqrt_nonneg _)]
    -- FTC for `r ↦ -(2π)⁻¹ * exp (-r^2 / 2)`
    have hderiv : ∀ r ∈ Set.uIcc (0 : ℝ) (Real.sqrt (2 * s)),
        HasDerivAt (fun x : ℝ => -(2 * Real.pi)⁻¹ * Real.exp (-x ^ 2 / 2))
          (r * (2 * Real.pi)⁻¹ * Real.exp (-r ^ 2 / 2)) r := by
      intro r _
      have hpow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
        simpa using hasDerivAt_pow 2 r
      have h1 : HasDerivAt (fun x : ℝ => -x ^ 2 / 2) (-r) r := by
        have h := hpow.neg.div_const 2
        have hval : -(2 * r) / 2 = -r := by ring
        rwa [hval] at h
      have h2 := (Real.hasDerivAt_exp (-r ^ 2 / 2)).comp r h1
      have h3 := h2.const_mul (-(2 * Real.pi)⁻¹)
      have hval2 : -(2 * Real.pi)⁻¹ * (Real.exp (-r ^ 2 / 2) * -r) =
          r * (2 * Real.pi)⁻¹ * Real.exp (-r ^ 2 / 2) := by ring
      rwa [hval2] at h3
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable_of_Icc (Real.sqrt_nonneg _))]
    rw [Real.sq_sqrt (by linarith : 0 ≤ 2 * s)]
    have hval : -(2 * Real.pi)⁻¹ * Real.exp (-(2 * s) / 2) -
        -(2 * Real.pi)⁻¹ * Real.exp (-0 ^ 2 / 2) =
        (2 * Real.pi)⁻¹ * (1 - Real.exp (-s)) := by
      have : -(2 * s) / 2 = -s := by ring
      rw [this]; simp; ring
    rw [hval, ← ENNReal.ofReal_mul (by
      have hle : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have : 0 ≤ 1 - Real.exp (-s) := by linarith
      positivity)]
    congr 1
    have hpi : 2 * Real.pi ≠ 0 := by positivity
    field_simp [hpi]
  · rw [if_neg hs, ENNReal.ofReal_zero]
    have hempty : (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) / 2) ⁻¹' Iic s = ∅ := by
      ext p
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
      have : 0 ≤ (p.1 ^ 2 + p.2 ^ 2) / 2 := by positivity
      linarith
    rw [hempty, measure_empty]

/-! ### Pushforward of diagonal quadratic form under `stdGaussMeasure × stdGaussMeasure` -/

private theorem pi_gaussian_weighted_sq_sum_eq :
    ∀ (m : ℕ) (c : Fin m → ℝ),
      ((Measure.pi fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1)).map
          (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
            ∑ i : Fin m, c i * ((p.1 i ^ 2 + p.2 i ^ 2) / 2)) =
        Probability.weightedExpSum (List.ofFn c)
  | 0, c => by
    have hconst : (fun p : (Fin 0 → ℝ) × (Fin 0 → ℝ) =>
        ∑ i : Fin 0, c i * ((p.1 i ^ 2 + p.2 i ^ 2) / 2)) = fun _ => 0 := by
      funext p; simp
    rw [hconst, Measure.map_const, measure_univ, one_smul, List.ofFn_zero,
      Probability.weightedExpSum]
  | m + 1, c => by
    let g1 := ProbabilityTheory.gaussianReal 0 1
    let μm := Measure.pi fun _ : Fin m => g1
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    have hmp : MeasurePreserving e (Measure.pi fun _ : Fin (m + 1) => g1) (g1.prod μm) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => g1) 0
    let sw : (ℝ × (Fin m → ℝ)) × (ℝ × (Fin m → ℝ)) → (ℝ × ℝ) × ((Fin m → ℝ) × (Fin m → ℝ)) :=
      fun q => ((q.1.1, q.2.1), (q.1.2, q.2.2))
    have hsw_meas : Measurable sw := by fun_prop
    have hmp_prod : MeasurePreserving (Prod.map e e)
        ((Measure.pi fun _ : Fin (m + 1) => g1).prod (Measure.pi fun _ : Fin (m + 1) => g1))
        ((g1.prod μm).prod (g1.prod μm)) := hmp.prod hmp
    have hmp_sw : MeasurePreserving sw ((g1.prod μm).prod (g1.prod μm)) ((g1.prod g1).prod (μm.prod μm)) := by
      refine ⟨hsw_meas, ?_⟩
      apply Measure.ext fun S hS => ?_
      rw [Measure.map_apply hsw_meas hS]
      have hind : Measurable (S.indicator (fun _ => (1 : ENNReal))) := measurable_const.indicator hS
      rw [← lintegral_indicator_one (hsw_meas hS), ← lintegral_indicator_one hS]
      have hpre : (sw ⁻¹' S).indicator (fun _ => (1 : ENNReal)) =
          (S.indicator (fun _ => (1 : ENNReal))) ∘ sw := by
        funext q; by_cases h : sw q ∈ S <;> simp [Set.indicator, h]
      change ∫⁻ q, (sw ⁻¹' S).indicator (fun _ => (1 : ENNReal)) q ∂((g1.prod μm).prod (g1.prod μm)) =
        ∫⁻ x, S.indicator (fun _ => (1 : ENNReal)) x ∂((g1.prod g1).prod (μm.prod μm))
      rw [hpre, lintegral_prod _ (hind.comp hsw_meas).aemeasurable, lintegral_prod _ hind.aemeasurable]
      rw [lintegral_prod _ (Measurable.lintegral_prod_right' (hind.comp hsw_meas)).aemeasurable]
      have hinner_lhs : ∀ a : ℝ, ∀ b : Fin m → ℝ,
          ∫⁻ p : ℝ × (Fin m → ℝ), S.indicator (fun _ => (1 : ENNReal)) ((a, p.1), (b, p.2)) ∂(g1.prod μm) =
          ∫⁻ c' : ℝ, ∫⁻ d : Fin m → ℝ, S.indicator (fun _ => (1 : ENNReal)) ((a, c'), (b, d)) ∂μm ∂g1 := fun a b =>
        lintegral_prod _ (hind.comp (by fun_prop : Measurable fun p : ℝ × (Fin m → ℝ) => ((a, p.1), (b, p.2)))).aemeasurable
      have houter_lhs : ∀ a : ℝ,
          ∫⁻ b : Fin m → ℝ, (∫⁻ c' : ℝ, ∫⁻ d : Fin m → ℝ, S.indicator (fun _ => (1 : ENNReal)) ((a, c'), (b, d)) ∂μm ∂g1) ∂μm =
          ∫⁻ c' : ℝ, ∫⁻ b : Fin m → ℝ, ∫⁻ d : Fin m → ℝ, S.indicator (fun _ => (1 : ENNReal)) ((a, c'), (b, d)) ∂μm ∂μm ∂g1 := fun a =>
        lintegral_lintegral_swap (by
          have hm : Measurable fun p : (Fin m → ℝ) × ℝ => ∫⁻ d : Fin m → ℝ, S.indicator (fun _ => (1 : ENNReal)) ((a, p.2), (p.1, d)) ∂μm :=
            Measurable.lintegral_prod_right (hind.comp (by fun_prop))
          exact hm.aemeasurable)
      have houter_rhs : ∀ a : ℝ, ∀ c' : ℝ,
          ∫⁻ q : (Fin m → ℝ) × (Fin m → ℝ), S.indicator (fun _ => (1 : ENNReal)) ((a, c'), q) ∂(μm.prod μm) =
          ∫⁻ b : Fin m → ℝ, ∫⁻ d : Fin m → ℝ, S.indicator (fun _ => (1 : ENNReal)) ((a, c'), (b, d)) ∂μm ∂μm := fun a c' =>
        lintegral_prod _ (hind.comp (measurable_prodMk_left (x := (a, c')))).aemeasurable
      have hrhs_outer :
          ∫⁻ r : ℝ × ℝ, (∫⁻ q : (Fin m → ℝ) × (Fin m → ℝ), S.indicator (fun _ => (1 : ENNReal)) (r, q) ∂(μm.prod μm)) ∂(g1.prod g1) =
          ∫⁻ a : ℝ, ∫⁻ c' : ℝ, ∫⁻ b : Fin m → ℝ, ∫⁻ d : Fin m → ℝ, S.indicator (fun _ => (1 : ENNReal)) ((a, c'), (b, d)) ∂μm ∂μm ∂g1 ∂g1 := by
        rw [lintegral_prod _ (Measurable.lintegral_prod_right' hind).aemeasurable]
        refine lintegral_congr fun a => lintegral_congr fun c' => houter_rhs a c'
      rw [hrhs_outer]
      refine lintegral_congr fun a => ?_
      rw [← houter_lhs a]
      refine lintegral_congr fun b => ?_
      exact hinner_lhs a b
    have hmp_all : MeasurePreserving (sw ∘ Prod.map e e)
        ((Measure.pi fun _ : Fin (m + 1) => g1).prod (Measure.pi fun _ : Fin (m + 1) => g1))
        ((g1.prod g1).prod (μm.prod μm)) := hmp_sw.comp hmp_prod
    let f1 : ℝ × ℝ → ℝ := fun r => c 0 * ((r.1 ^ 2 + r.2 ^ 2) / 2)
    let f2 : (Fin m → ℝ) × (Fin m → ℝ) → ℝ := fun q =>
      ∑ j : Fin m, c j.succ * ((q.1 j ^ 2 + q.2 j ^ 2) / 2)
    have hf1 : Measurable f1 := by fun_prop
    have hf2 : Measurable f2 := by
      refine Finset.measurable_sum Finset.univ fun j _ => ?_
      exact measurable_const.mul ((((measurable_pi_apply j).comp measurable_fst).pow_const 2 |>.add
        (((measurable_pi_apply j).comp measurable_snd).pow_const 2)).div_const 2)
    have hcomp_fun :
        (fun p : (Fin (m + 1) → ℝ) × (Fin (m + 1) → ℝ) =>
          ∑ i : Fin (m + 1), c i * ((p.1 i ^ 2 + p.2 i ^ 2) / 2)) =
        ((fun z : ℝ × ℝ => z.1 + z.2) ∘ Prod.map f1 f2) ∘ (sw ∘ Prod.map e e) := by
      funext p
      simp only [Function.comp_apply, Prod.map_apply, sw, f1, f2, e,
        MeasurableEquiv.piFinSuccAbove_apply, Fin.sum_univ_succ]
      rfl
    have hadd_meas : Measurable (fun z : ℝ × ℝ => z.1 + z.2) := measurable_fst.add measurable_snd
    rw [hcomp_fun, ← Measure.map_map (hadd_meas.comp (hf1.prodMap hf2)) hmp_all.measurable,
      hmp_all.map_eq, ← Measure.map_map hadd_meas (hf1.prodMap hf2),
      ← Measure.map_prod_map (g1.prod g1) (μm.prod μm) hf1 hf2]
    change ((g1.prod g1).map f1) ∗ ((μm.prod μm).map f2) = Probability.weightedExpSum (List.ofFn c)
    have hfirst : (g1.prod g1).map f1 = Probability.weightedExp (c 0) := by
      have hsq : f1 = (fun x : ℝ => c 0 * x) ∘ (fun r : ℝ × ℝ => (r.1 ^ 2 + r.2 ^ 2) / 2) := rfl
      have hm1 : Measurable (fun x : ℝ => c 0 * x) := measurable_const.mul measurable_id
      have hm2 : Measurable (fun r : ℝ × ℝ => (r.1 ^ 2 + r.2 ^ 2) / 2) := by fun_prop
      rw [hsq, ← Measure.map_map hm1 hm2, gaussian_sq_half_eq_expMeasure]
      rfl
    have hrest : (μm.prod μm).map f2 = Probability.weightedExpSum (List.ofFn fun j : Fin m => c j.succ) :=
      pi_gaussian_weighted_sq_sum_eq m (fun j => c j.succ)
    rw [hfirst, hrest, List.ofFn_succ, Probability.weightedExpSum]

/-! ### Alternating-sign symmetry and spectral decomposition of `t I - J_n(t)` -/

/-- The alternating-sign linear isometry `S = diag(1, -1, 1, -1, ...)` on `EuclideanSpace ℝ (Fin m)`. -/
noncomputable def altSignEquiv (m : ℕ) :
    EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m) :=
  { toFun := fun x => WithLp.toLp 2 (fun i : Fin m => (-1 : ℝ) ^ i.val * x i)
    invFun := fun x => WithLp.toLp 2 (fun i : Fin m => (-1 : ℝ) ^ i.val * x i)
    map_add' := fun x y => by ext i; simp [mul_add]
    map_smul' := fun r x => by ext i; simp; ring
    left_inv := fun x => by
      ext i; simp only [← mul_assoc, ← pow_add]
      have : Even (i.val + i.val) := ⟨i.val, rfl⟩
      simp [this.neg_one_pow]
    right_inv := fun x => by
      ext i; simp only [← mul_assoc, ← pow_add]
      have : Even (i.val + i.val) := ⟨i.val, rfl⟩
      simp [this.neg_one_pow]
    norm_map' := fun x => by
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
        EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Real.norm_eq_abs] }

/-- Real quadratic form `xᵀ M x` on `EuclideanSpace ℝ (Fin m)`. -/
noncomputable def quadForm {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  dotProduct (WithLp.ofLp x) (M.mulVec (WithLp.ofLp x))

/-- Complexified real quadratic form `(xᵀ M x + yᵀ M y) / 2` for a pair of real vectors. -/
noncomputable def pairQuadForm {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ)
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) : ℝ :=
  (quadForm M p.1 + quadForm M p.2) / 2

theorem quadForm_altSign_jacobiPencilD (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 2))) :
    quadForm (jacobiPencilD k) (altSignEquiv (k + 2) x) = quadForm (jacobiPencilD k) x := by
  simp only [quadForm, dotProduct, Matrix.mulVec, jacobiPencilD, Matrix.diagonal_apply,
    altSignEquiv, LinearIsometryEquiv.coe_mk, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, WithLp.ofLp_toLp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hev : Even (i.val + i.val) := ⟨i.val, rfl⟩
  split_ifs
  · calc (-1 : ℝ) ^ i.val * x i * ((1 / 2 : ℝ) * ((-1) ^ i.val * x i))
        = (-1 : ℝ) ^ (i.val + i.val) * (x i * ((1 / 2 : ℝ) * x i)) := by rw [pow_add]; ring
      _ = x i * ((1 / 2 : ℝ) * x i) := by rw [hev.neg_one_pow, one_mul]
  · calc (-1 : ℝ) ^ i.val * x i * (1 * ((-1) ^ i.val * x i))
        = (-1 : ℝ) ^ (i.val + i.val) * (x i * (1 * x i)) := by rw [pow_add]; ring
      _ = x i * (1 * x i) := by rw [hev.neg_one_pow, one_mul]

theorem quadForm_altSign_jacobiZero (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 2))) :
    quadForm (jacobiMatrix k 0) (altSignEquiv (k + 2) x) = -quadForm (jacobiMatrix k 0) x := by
  simp only [quadForm, dotProduct, Matrix.mulVec, altSignEquiv, LinearIsometryEquiv.coe_mk,
    LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold jacobiMatrix
  split_ifs with hij hedge hadj
  · simp
  · simp
  · rcases hadj with h1 | h2
    · have hodd : Odd (i.val + j.val) := ⟨i.val, by omega⟩
      calc (-1 : ℝ) ^ i.val * x i * (1 / 2 * ((-1) ^ j.val * x j))
          = (-1 : ℝ) ^ (i.val + j.val) * (x i * (1 / 2 * x j)) := by rw [pow_add]; ring
        _ = -(x i * (1 / 2 * x j)) := by rw [hodd.neg_one_pow]; ring
    · have hodd : Odd (i.val + j.val) := ⟨j.val, by omega⟩
      calc (-1 : ℝ) ^ i.val * x i * (1 / 2 * ((-1) ^ j.val * x j))
          = (-1 : ℝ) ^ (i.val + j.val) * (x i * (1 / 2 * x j)) := by rw [pow_add]; ring
        _ = -(x i * (1 / 2 * x j)) := by rw [hodd.neg_one_pow]; ring
  · simp

theorem quadForm_jacobiPencilD_nonneg (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 2))) :
    0 ≤ quadForm (jacobiPencilD k) x := by
  simp only [quadForm, dotProduct, Matrix.mulVec, jacobiPencilD, Matrix.diagonal_apply]
  refine Finset.sum_nonneg fun i _ => ?_
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  split_ifs <;> nlinarith [sq_nonneg (x i)]

/-- Spectral diagonalization of `quadForm (t • 1 - jacobiMatrix k t)` in the eigenbasis of `jacobiMatrix k t`. -/
theorem quadForm_pencil_eq_sum_eigenvalues (k : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin (k + 2))) :
    let hJ := jacobi_isHermitian k t
    let T := hJ.eigenvectorBasis.repr
    quadForm (t • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ) - jacobiMatrix k t) x =
      ∑ i : Fin (k + 2), (t - hJ.eigenvalues i) * (T x i) ^ 2 := by
  intro hJ T
  let b := hJ.eigenvectorBasis
  have hx : x = ∑ i : Fin (k + 2), (T x i) • b i := (b.sum_repr x).symm
  have hmul : ∀ i : Fin (k + 2),
      (t • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ) - jacobiMatrix k t).mulVec (WithLp.ofLp (b i)) =
        (t - hJ.eigenvalues i) • WithLp.ofLp (b i) := by
    intro i
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hJ.mulVec_eigenvectorBasis i,
      sub_smul]
  have hofLp_sum : ∀ (f : Fin (k + 2) → EuclideanSpace ℝ (Fin (k + 2))),
      WithLp.ofLp (∑ i : Fin (k + 2), f i) = ∑ i : Fin (k + 2), WithLp.ofLp (f i) := fun f =>
    map_sum (WithLp.linearEquiv 2 ℝ (Fin (k + 2) → ℝ)) f Finset.univ
  have hofLp_smul : ∀ (r : ℝ) (v : EuclideanSpace ℝ (Fin (k + 2))),
      WithLp.ofLp (r • v) = r • WithLp.ofLp v := fun r v =>
    map_smul (WithLp.linearEquiv 2 ℝ (Fin (k + 2) → ℝ)) r v
  have hMmul :
      (t • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ) - jacobiMatrix k t).mulVec (WithLp.ofLp x) =
        WithLp.ofLp (∑ i : Fin (k + 2), ((t - hJ.eigenvalues i) * T x i) • b i) := by
    conv_lhs => rw [hx]
    rw [hofLp_sum, hofLp_sum, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hofLp_smul, hofLp_smul, Matrix.mulVec_smul, hmul, smul_smul, mul_comm]
  have hinner : ∀ u v : EuclideanSpace ℝ (Fin (k + 2)),
      dotProduct (WithLp.ofLp u) (WithLp.ofLp v) = @inner ℝ _ _ u v := by
    intro u v
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct, mul_comm]
  rw [quadForm, hMmul, hinner]
  have hfirst := congrArg (fun u => @inner ℝ _ _ u (∑ i : Fin (k + 2), ((t - hJ.eigenvalues i) * T x i) • b i)) hx
  rw [hfirst, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, b.orthonormal.1 i]
    ring
  · intro j _ hji
    rw [real_inner_smul_left, real_inner_smul_right, b.orthonormal.2 hji.symm]
    ring
  · intro hi; exact (hi (Finset.mem_univ i)).elim

/-! ### Law identification and Claim 4 (strict positivity of the first term) -/

private theorem weightedExpSum_perm_ft {xs ys : List ℝ} (h : xs.Perm ys) :
    Probability.weightedExpSum xs = Probability.weightedExpSum ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [Probability.weightedExpSum, ih]
  | swap x y l =>
    simp only [Probability.weightedExpSum, ← Measure.conv_assoc]
    rw [Measure.conv_comm (Probability.weightedExp y) (Probability.weightedExp x)]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private theorem jacobi_eigenvalues_perm_orderedNode (k : ℕ) (t : ℝ) :
    (List.ofFn (jacobi_isHermitian k t).eigenvalues).Perm (List.ofFn (orderedNode k t)) := by
  apply Multiset.coe_eq_coe.mp
  have h1 : ((List.ofFn (jacobi_isHermitian k t).eigenvalues : List ℝ) : Multiset ℝ) =
      (jacobiMatrix k t).charpoly.roots := by
    rw [(jacobi_isHermitian k t).roots_charpoly_eq_eigenvalues]
    symm
    exact Fin.univ_val_map (jacobi_isHermitian k t).eigenvalues
  have h2 : (jacobiMatrix k t).charpoly.roots = (nodePolynomial k t).roots := by
    rw [jacobi_charpoly, Polynomial.roots_C_mul _ (pow_ne_zero _ (by norm_num))]
  have h3 : ((List.ofFn (orderedNode k t) : List ℝ) : Multiset ℝ) =
      (nodePolynomial k t).roots := by
    have hof := orderedNode_ofFn k t
    have hcoe := congrArg (fun l : List ℝ => (l : Multiset ℝ)) hof
    rwa [Multiset.sort_eq] at hcoe
  rw [h1, h2, h3]

/-- The law of the complexified Gaussian quadratic form `pairQuadForm (t • 1 - jacobiMatrix k t)`
equals `weightedExpSum [t - u_0(t), ..., t - u_n(t)]`. -/
theorem pairQuadForm_pencil_law (k : ℕ) (t : ℝ) :
    ((stdGaussMeasure (k + 2)).prod (stdGaussMeasure (k + 2))).map
        (pairQuadForm (t • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ) - jacobiMatrix k t)) =
      Probability.weightedExpSum (List.ofFn fun i : Fin (k + 2) => t - orderedNode k t i) := by
  let hJ := jacobi_isHermitian k t
  let T := hJ.eigenvectorBasis.repr
  let μ := stdGaussMeasure (k + 2)
  have hmpT : MeasurePreserving (Prod.map T T) (μ.prod μ) (μ.prod μ) :=
    (stdGaussMeasure_measurePreserving T).prod (stdGaussMeasure_measurePreserving T)
  have hmpL : MeasurePreserving (Prod.map (WithLp.ofLp (p := 2) (V := Fin (k + 2) → ℝ))
      (WithLp.ofLp (p := 2) (V := Fin (k + 2) → ℝ)))
      (μ.prod μ)
      ((Measure.pi fun _ : Fin (k + 2) => ProbabilityTheory.gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (k + 2) => ProbabilityTheory.gaussianReal 0 1)) := by
    have h1 : MeasurePreserving (WithLp.ofLp (p := 2) (V := Fin (k + 2) → ℝ)) μ
        (Measure.pi fun _ : Fin (k + 2) => ProbabilityTheory.gaussianReal 0 1) :=
      ⟨WithLp.measurable_ofLp 2 _, stdGaussMeasure_map_ofLp (k + 2)⟩
    exact h1.prod h1
  let f : (Fin (k + 2) → ℝ) × (Fin (k + 2) → ℝ) → ℝ := fun p =>
    ∑ i : Fin (k + 2), (t - hJ.eigenvalues i) * ((p.1 i ^ 2 + p.2 i ^ 2) / 2)
  have hf : Measurable f := by
    refine Finset.measurable_sum Finset.univ fun i _ => ?_
    exact measurable_const.mul ((((measurable_pi_apply i).comp measurable_fst).pow_const 2 |>.add
      (((measurable_pi_apply i).comp measurable_snd).pow_const 2)).div_const 2)
  have hcomp :
      pairQuadForm (t • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ) - jacobiMatrix k t) =
      (f ∘ Prod.map WithLp.ofLp WithLp.ofLp) ∘ Prod.map T T := by
    funext ⟨x, y⟩
    simp only [pairQuadForm, Function.comp_apply, Prod.map_apply, f,
      quadForm_pencil_eq_sum_eigenvalues, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hcomp, ← Measure.map_map (hf.comp hmpL.measurable) hmpT.measurable, hmpT.map_eq,
    ← Measure.map_map hf hmpL.measurable, hmpL.map_eq, pi_gaussian_weighted_sq_sum_eq]
  apply weightedExpSum_perm_ft
  have hperm := jacobi_eigenvalues_perm_orderedNode k t
  have hmap := hperm.map (fun x : ℝ => t - x)
  simpa only [List.map_ofFn, Function.comp_def] using hmap

private theorem continuous_quadForm {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (quadForm M) := by
  unfold quadForm dotProduct Matrix.mulVec
  refine continuous_finsetSum Finset.univ fun i _ => ?_
  refine (EuclideanSpace.proj i).continuous.mul ?_
  refine continuous_finsetSum Finset.univ fun j _ => ?_
  exact continuous_const.mul (EuclideanSpace.proj j).continuous

private theorem continuous_pairQuadForm {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (pairQuadForm M) := by
  unfold pairQuadForm
  exact (((continuous_quadForm M).comp continuous_fst).add
    ((continuous_quadForm M).comp continuous_snd)).div_const 2

private theorem witness_quadForm_jacobiZero (k : ℕ) :
    let x0 : EuclideanSpace ℝ (Fin (k + 2)) :=
      WithLp.toLp 2 (fun i : Fin (k + 2) => if i.val = 0 ∨ i.val = 1 then (1 : ℝ) else 0)
    quadForm (jacobiMatrix k 0) x0 = 1 := by
  intro x0
  have h01 : (0 : Fin (k + 2)) ≠ 1 := by simp
  have hsum_i : ∀ i : Fin (k + 2),
      (WithLp.ofLp x0 i) *
        ∑ j : Fin (k + 2), jacobiMatrix k 0 i j * (WithLp.ofLp x0 j) =
      (if i = 0 then (1 / 2 : ℝ) else 0) + (if i = 1 then (1 / 2 : ℝ) else 0) := by
    intro i
    by_cases hi0 : i = 0
    · subst hi0
      have hx0 : WithLp.ofLp x0 0 = 1 := by simp [x0]
      rw [hx0, one_mul, if_pos rfl, if_neg h01, add_zero]
      rw [Finset.sum_eq_single (1 : Fin (k + 2))]
      · have hx1 : WithLp.ofLp x0 1 = 1 := by simp [x0]
        rw [hx1, mul_one]
        simp [jacobiMatrix]
      · intro j _ hj1
        by_cases hj0 : j = 0
        · subst hj0; simp [jacobiMatrix]
        · have hjv0 : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
          have hjv1 : j.val ≠ 1 := fun h => hj1 (Fin.ext h)
          have hxj : WithLp.ofLp x0 j = 0 := by simp [x0, hjv0, hjv1]
          rw [hxj, mul_zero]
      · intro h; exact (h (Finset.mem_univ _)).elim
    · by_cases hi1 : i = 1
      · subst hi1
        have hx1 : WithLp.ofLp x0 1 = 1 := by simp [x0]
        rw [hx1, one_mul, if_neg h01.symm, if_pos rfl, zero_add]
        rw [Finset.sum_eq_single (0 : Fin (k + 2))]
        · have hx0 : WithLp.ofLp x0 0 = 1 := by simp [x0]
          rw [hx0, mul_one]
          simp [jacobiMatrix]
        · intro j _ hj0
          by_cases hj1 : j = 1
          · subst hj1; simp [jacobiMatrix]
          · have hjv0 : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
            have hjv1 : j.val ≠ 1 := fun h => hj1 (Fin.ext h)
            have hxj : WithLp.ofLp x0 j = 0 := by simp [x0, hjv0, hjv1]
            rw [hxj, mul_zero]
        · intro h; exact (h (Finset.mem_univ _)).elim
      · have hiv0 : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
        have hiv1 : i.val ≠ 1 := fun h => hi1 (Fin.ext h)
        have hxi : WithLp.ofLp x0 i = 0 := by simp [x0, hiv0, hiv1]
        rw [hxi, zero_mul, if_neg hi0, if_neg hi1, add_zero]
  change ∑ i : Fin (k + 2), WithLp.ofLp x0 i *
      ∑ j : Fin (k + 2), jacobiMatrix k 0 i j * WithLp.ofLp x0 j = 1
  simp_rw [hsum_i]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp
  norm_num

/-- Main theorem (Claim 4, `clm:first-term`): for every order `n = k + 1 ≥ 1` and every `t > 0`,
the first term in the `H_n'(t)` decomposition is strictly positive. -/
theorem firstTerm_lawSignMean_pos (k : ℕ) {t : ℝ} (ht : 0 < t) :
    let csCore : List ℝ := List.ofFn fun i : Fin (k + 2) => t - orderedNode k t i
    0 < (Probability.lawSignMean (Probability.weightedExpSum ((t + 1) :: csCore)) +
      Probability.lawSignMean (Probability.weightedExpSum ((t - 1) :: csCore))) / 2 := by
  intro csCore
  let E := EuclideanSpace ℝ (Fin (k + 2))
  let μ := stdGaussMeasure (k + 2)
  let ν := ProbabilityTheory.expMeasure (1 : ℝ)
  letI : IsProbabilityMeasure ν := Probability.expMeasure_probability zero_lt_one
  let P : Measure ((E × E) × ℝ) := (μ.prod μ).prod ν
  let A : (E × E) × ℝ → ℝ := fun ω => pairQuadForm (jacobiPencilD k) ω.1
  let Z : (E × E) × ℝ → ℝ := fun ω => pairQuadForm (jacobiMatrix k 0) ω.1
  let X : (E × E) × ℝ → ℝ := fun ω => t * (A ω + ω.2)
  let Y : (E × E) × ℝ → ℝ := fun ω => ω.2 - Z ω
  have hA_cont : Continuous A := (continuous_pairQuadForm (jacobiPencilD k)).comp continuous_fst
  have hZ_cont : Continuous Z := (continuous_pairQuadForm (jacobiMatrix k 0)).comp continuous_fst
  have hX_cont : Continuous X := continuous_const.mul (hA_cont.add continuous_snd)
  have hY_cont : Continuous Y := continuous_snd.sub hZ_cont
  have hXY_add_cont : Continuous (fun ω => X ω + Y ω) := hX_cont.add hY_cont
  have hXY_sub_cont : Continuous (fun ω => X ω - Y ω) := hX_cont.sub hY_cont
  -- Step 1: Identify `P.map (X + Y)` with `weightedExpSum ((t + 1) :: csCore)`.
  have hQ0_decomp : ∀ p : E × E,
      pairQuadForm (t • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ) - jacobiMatrix k t) p =
        t * pairQuadForm (jacobiPencilD k) p - pairQuadForm (jacobiMatrix k 0) p := by
    intro p
    rw [jacobi_pencil_affine]
    simp only [pairQuadForm, quadForm, Matrix.sub_mulVec, Matrix.smul_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul]
    ring
  have hlaw_plus : P.map (fun ω => X ω + Y ω) = Probability.weightedExpSum ((t + 1) :: csCore) := by
    have hfun : (fun ω : (E × E) × ℝ => X ω + Y ω) =
        (fun z : ℝ × ℝ => z.1 + z.2) ∘
          Prod.map (pairQuadForm (t • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ) - jacobiMatrix k t))
            (fun e : ℝ => (t + 1) * e) := by
      funext ⟨p, e⟩
      simp only [Function.comp_apply, Prod.map_apply, X, Y, A, Z, hQ0_decomp]
      ring
    have hm1 : Measurable (pairQuadForm (t • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ) - jacobiMatrix k t)) :=
      (continuous_pairQuadForm _).measurable
    have hm2 : Measurable (fun e : ℝ => (t + 1) * e) := measurable_const.mul measurable_id
    have hadd : Measurable (fun z : ℝ × ℝ => z.1 + z.2) := measurable_fst.add measurable_snd
    rw [hfun, ← Measure.map_map hadd (hm1.prodMap hm2),
      ← Measure.map_prod_map (μ.prod μ) ν hm1 hm2]
    change ((μ.prod μ).map (pairQuadForm _)) ∗ (ν.map fun e => (t + 1) * e) = _
    rw [pairQuadForm_pencil_law k t, Measure.conv_comm]
    rfl
  -- Step 2: Identify `P.map (X - Y)` with `weightedExpSum ((t - 1) :: csCore)` via `altSignEquiv`.
  let S := altSignEquiv (k + 2)
  let invol : (E × E) × ℝ → (E × E) × ℝ := Prod.map (Prod.map S S) id
  have hinvol_mp : MeasurePreserving invol P P :=
    ((stdGaussMeasure_measurePreserving S).prod (stdGaussMeasure_measurePreserving S)).prod
      (MeasurePreserving.id ν)
  have hlaw_minus : P.map (fun ω => X ω - Y ω) = Probability.weightedExpSum ((t - 1) :: csCore) := by
    let Qminus : (E × E) × ℝ → ℝ := fun ω =>
      pairQuadForm (t • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ) - jacobiMatrix k t) ω.1 +
        (t - 1) * ω.2
    have hQminus_law : P.map Qminus = Probability.weightedExpSum ((t - 1) :: csCore) := by
      have hfun : Qminus =
          (fun z : ℝ × ℝ => z.1 + z.2) ∘
            Prod.map (pairQuadForm (t • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ) - jacobiMatrix k t))
              (fun e : ℝ => (t - 1) * e) := by
        funext ω; rfl
      have hm1 : Measurable (pairQuadForm (t • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ) - jacobiMatrix k t)) :=
        (continuous_pairQuadForm _).measurable
      have hm2 : Measurable (fun e : ℝ => (t - 1) * e) := measurable_const.mul measurable_id
      have hadd : Measurable (fun z : ℝ × ℝ => z.1 + z.2) := measurable_fst.add measurable_snd
      rw [hfun, ← Measure.map_map hadd (hm1.prodMap hm2),
        ← Measure.map_prod_map (μ.prod μ) ν hm1 hm2]
      change ((μ.prod μ).map (pairQuadForm _)) ∗ (ν.map fun e => (t - 1) * e) = _
      rw [pairQuadForm_pencil_law k t, Measure.conv_comm]
      rfl
    have hcomp_minus : (fun ω => X ω - Y ω) = Qminus ∘ invol := by
      funext ⟨⟨x, y⟩, e⟩
      simp only [Function.comp_apply, Qminus, invol, Prod.map_apply, id_eq]
      rw [hQ0_decomp]
      simp only [pairQuadForm, S, quadForm_altSign_jacobiPencilD, quadForm_altSign_jacobiZero,
        X, Y, A, Z]
      ring
    have hQminus_meas : Measurable Qminus :=
      (((continuous_pairQuadForm _).comp continuous_fst).add
        (continuous_const.mul continuous_snd)).measurable
    rw [hcomp_minus, ← Measure.map_map hQminus_meas hinvol_mp.measurable,
      hinvol_mp.map_eq, hQminus_law]
  -- Step 3: Exact probability formula `(lawSignMean(X+Y) + lawSignMean(X-Y)) / 2 = P.real {|Y| < X}`.
  have hX_ae_pos : ∀ᵐ ω ∂P, 0 < X ω := by
    have he_pos : ∀ᵐ e ∂ν, 0 < e := by
      have hset : {e : ℝ | ¬ 0 < e} = Set.Iic 0 := by ext e; simp
      rw [ae_iff, hset, ← ProbabilityTheory.ofReal_cdf,
        Probability.expMeasure_cdf_formula zero_lt_one]
      simp
    have hprod_ae : ∀ᵐ ω ∂P, 0 < ω.2 := by
      rw [Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_snd)]
      exact Filter.Eventually.of_forall fun _ => he_pos
    filter_upwards [hprod_ae] with ω hω
    have hA0 : 0 ≤ A ω := by
      dsimp [A, pairQuadForm]
      exact div_nonneg (add_nonneg (quadForm_jacobiPencilD_nonneg k _) (quadForm_jacobiPencilD_nonneg k _))
        (by norm_num)
    exact mul_pos ht (by linarith)
  have hcore_nz : ∃ c ∈ csCore, c ≠ 0 := by
    by_cases h0 : t - orderedNode k t 0 = 0
    · refine ⟨t - orderedNode k t 1, List.mem_ofFn.mpr ⟨1, rfl⟩, ?_⟩
      have hlt : orderedNode k t 0 < orderedNode k t 1 := orderedNode_strictMono k t (by simp)
      linarith
    · exact ⟨t - orderedNode k t 0, List.mem_ofFn.mpr ⟨0, rfl⟩, h0⟩
  have hplus_zero : P {ω | X ω + Y ω = 0} = 0 := by
    have hnz : ∃ c ∈ (t + 1) :: csCore, c ≠ 0 := ⟨t + 1, by simp, by linarith⟩
    have h0 := Probability.weightedExpSum_singleton_eq_zero hnz 0
    rw [← hlaw_plus, Measure.map_apply hXY_add_cont.measurable (measurableSet_singleton 0)] at h0
    exact h0
  have hminus_zero : P {ω | X ω - Y ω = 0} = 0 := by
    obtain ⟨c, hc, hne⟩ := hcore_nz
    have hnz : ∃ c ∈ (t - 1) :: csCore, c ≠ 0 := ⟨c, List.mem_cons_of_mem _ hc, hne⟩
    have h0 := Probability.weightedExpSum_singleton_eq_zero hnz 0
    rw [← hlaw_minus, Measure.map_apply hXY_sub_cont.measurable (measurableSet_singleton 0)] at h0
    exact h0
  let U : Set ((E × E) × ℝ) := {ω | 0 < X ω} ∩ ({ω | X ω + Y ω ≠ 0} ∩ {ω | X ω - Y ω ≠ 0})
  have hU_meas : MeasurableSet U :=
    (measurableSet_lt measurable_const hX_cont.measurable).inter
      ((measurableSet_eq_fun hXY_add_cont.measurable measurable_const).compl.inter
        (measurableSet_eq_fun hXY_sub_cont.measurable measurable_const).compl)
  have hU_compl : P Uᶜ = 0 := by
    have hsub : Uᶜ = {ω | ¬ 0 < X ω} ∪ ({ω | X ω + Y ω = 0} ∪ {ω | X ω - Y ω = 0}) := by
      ext ω
      simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, U]
      tauto
    rw [hsub]
    apply le_antisymm _ bot_le
    calc P ({ω | ¬ 0 < X ω} ∪ ({ω | X ω + Y ω = 0} ∪ {ω | X ω - Y ω = 0}))
        ≤ P {ω | ¬ 0 < X ω} + P ({ω | X ω + Y ω = 0} ∪ {ω | X ω - Y ω = 0}) := measure_union_le _ _
      _ ≤ P {ω | ¬ 0 < X ω} + (P {ω | X ω + Y ω = 0} + P {ω | X ω - Y ω = 0}) :=
          add_le_add le_rfl (measure_union_le _ _)
      _ = 0 := by rw [ae_iff.mp hX_ae_pos, hplus_zero, hminus_zero]; simp
  have hreal_inter_U : ∀ S : Set ((E × E) × ℝ), P.real (S ∩ U) = P.real S := by
    intro S
    apply measureReal_congr
    have h1 : (S ∩ U : Set _) =ᵐ[P] S := by
      filter_upwards [compl_mem_ae_iff.mpr hU_compl] with ω hω
      have hωU : ω ∈ U := by simpa using hω
      simp [hωU]
    exact h1
  -- Set decompositions inside `U`
  have hS1 : {ω | 0 < X ω + Y ω} ∩ U = ({ω | |Y ω| < X ω} ∩ U) ∪ ({ω | X ω - Y ω < 0} ∩ U) := by
    ext ω; simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, U, abs_lt]
    constructor
    · rintro ⟨h1, hX, _, hsub_ne⟩
      rcases lt_or_gt_of_ne hsub_ne with hlt | hgt
      · exact Or.inr ⟨hlt, hX, by linarith, hsub_ne⟩
      · exact Or.inl ⟨⟨by linarith, by linarith⟩, hX, by linarith, hsub_ne⟩
    · rintro (⟨⟨h1, _⟩, hX, hadd_ne, hsub_ne⟩ | ⟨hlt, hX, hadd_ne, hsub_ne⟩)
      · exact ⟨by linarith, hX, hadd_ne, hsub_ne⟩
      · exact ⟨by linarith, hX, hadd_ne, hsub_ne⟩
  have hD1 : Disjoint ({ω | |Y ω| < X ω} ∩ U) ({ω | X ω - Y ω < 0} ∩ U) := by
    rw [Set.disjoint_left]
    rintro ω ⟨habs, _⟩ ⟨hlt, _⟩
    change |Y ω| < X ω at habs
    change X ω - Y ω < 0 at hlt
    linarith [(abs_lt.mp habs).2]
  have hS2 : {ω | 0 < X ω - Y ω} ∩ U = ({ω | |Y ω| < X ω} ∩ U) ∪ ({ω | X ω + Y ω < 0} ∩ U) := by
    ext ω; simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, U, abs_lt]
    constructor
    · rintro ⟨h1, hX, hadd_ne, _⟩
      rcases lt_or_gt_of_ne hadd_ne with hlt | hgt
      · exact Or.inr ⟨hlt, hX, hadd_ne, by linarith⟩
      · exact Or.inl ⟨⟨by linarith, by linarith⟩, hX, hadd_ne, by linarith⟩
    · rintro (⟨⟨_, h2⟩, hX, hadd_ne, hsub_ne⟩ | ⟨hlt, hX, hadd_ne, hsub_ne⟩)
      · exact ⟨by linarith, hX, hadd_ne, hsub_ne⟩
      · exact ⟨by linarith, hX, hadd_ne, hsub_ne⟩
  have hD2 : Disjoint ({ω | |Y ω| < X ω} ∩ U) ({ω | X ω + Y ω < 0} ∩ U) := by
    rw [Set.disjoint_left]
    rintro ω ⟨habs, _⟩ ⟨hlt, _⟩
    change |Y ω| < X ω at habs
    change X ω + Y ω < 0 at hlt
    linarith [(abs_lt.mp habs).1]
  have hm_sub_neg : MeasurableSet ({ω | X ω - Y ω < 0} ∩ U) :=
    (measurableSet_lt hXY_sub_cont.measurable measurable_const).inter hU_meas
  have hm_add_neg : MeasurableSet ({ω | X ω + Y ω < 0} ∩ U) :=
    (measurableSet_lt hXY_add_cont.measurable measurable_const).inter hU_meas
  have hEq1 : P.real {ω | 0 < X ω + Y ω} = P.real {ω | |Y ω| < X ω} + P.real {ω | X ω - Y ω < 0} := by
    rw [← hreal_inter_U {ω | 0 < X ω + Y ω}, hS1, measureReal_union hD1 hm_sub_neg,
      hreal_inter_U, hreal_inter_U]
  have hEq2 : P.real {ω | 0 < X ω - Y ω} = P.real {ω | |Y ω| < X ω} + P.real {ω | X ω + Y ω < 0} := by
    rw [← hreal_inter_U {ω | 0 < X ω - Y ω}, hS2, measureReal_union hD2 hm_add_neg,
      hreal_inter_U, hreal_inter_U]
  have hmean_eq :
      (Probability.lawSignMean (Probability.weightedExpSum ((t + 1) :: csCore)) +
        Probability.lawSignMean (Probability.weightedExpSum ((t - 1) :: csCore))) / 2 =
      P.real {ω | |Y ω| < X ω} := by
    rw [← hlaw_plus, ← hlaw_minus, Probability.lawSignMean, Probability.lawSignMean]
    simp only [measureReal_def, Measure.map_apply hXY_add_cont.measurable measurableSet_Ioi,
      Measure.map_apply hXY_add_cont.measurable measurableSet_Iio,
      Measure.map_apply hXY_sub_cont.measurable measurableSet_Ioi,
      Measure.map_apply hXY_sub_cont.measurable measurableSet_Iio]
    change ((P.real {ω | 0 < X ω + Y ω} - P.real {ω | X ω + Y ω < 0}) +
      (P.real {ω | 0 < X ω - Y ω} - P.real {ω | X ω - Y ω < 0})) / 2 = P.real {ω | |Y ω| < X ω}
    linarith [hEq1, hEq2]
  rw [hmean_eq]
  -- Step 4: Strict positivity via explicit witness `((x₀, 0), 1/2)` in an open set `W`.
  let W : Set ((E × E) × ℝ) := {ω | |Y ω| < X ω} ∩ {ω | 0 < ω.2}
  have hW_open : IsOpen W :=
    (isOpen_lt hY_cont.abs hX_cont).inter (isOpen_lt continuous_const continuous_snd)
  let x0 : E := WithLp.toLp 2 (fun i : Fin (k + 2) => if i.val = 0 ∨ i.val = 1 then (1 : ℝ) else 0)
  let ω0 : (E × E) × ℝ := ((x0, 0), 1 / 2)
  have hω0_mem : ω0 ∈ W := by
    refine ⟨?_, by norm_num⟩
    have hZ0 : Z ω0 = 1 / 2 := by
      dsimp [Z, ω0, pairQuadForm]
      have hq0 : quadForm (jacobiMatrix k 0) 0 = 0 := by simp [quadForm]
      rw [hq0, witness_quadForm_jacobiZero k]
      norm_num
    have hA0 : 0 ≤ A ω0 := by
      dsimp [A, pairQuadForm]
      exact div_nonneg (add_nonneg (quadForm_jacobiPencilD_nonneg k _) (quadForm_jacobiPencilD_nonneg k _))
        (by norm_num)
    have hY0 : Y ω0 = 0 := by dsimp [Y, ω0]; linarith
    change |Y ω0| < X ω0
    rw [hY0, abs_zero]
    dsimp [X, ω0]
    nlinarith
  have hW_vol_pos : 0 < (volume : Measure ((E × E) × ℝ)) W :=
    hW_open.measure_pos volume ⟨ω0, hω0_mem⟩
  -- Express `P` as `volume.withDensity ρ` where `ρ > 0` everywhere on `W`.
  let ρ : (E × E) × ℝ → ENNReal := fun ω =>
    (ENNReal.ofReal (stdGaussDensity (k + 2) ω.1.1) *
      ENNReal.ofReal (stdGaussDensity (k + 2) ω.1.2)) *
      ProbabilityTheory.exponentialPDF 1 ω.2
  have hP_dens : P = (volume : Measure ((E × E) × ℝ)).withDensity ρ := by
    have hμ_meas : Measurable (fun x : E => ENNReal.ofReal (stdGaussDensity (k + 2) x)) :=
      ENNReal.continuous_ofReal.measurable.comp (stdGaussDensity_continuous (k + 2)).measurable
    have hν_meas : Measurable (ProbabilityTheory.exponentialPDF 1) :=
      ENNReal.continuous_ofReal.measurable.comp (ProbabilityTheory.measurable_exponentialPDFReal 1)
    have hprod1 : μ.prod μ = (volume : Measure (E × E)).withDensity
        (fun p => ENNReal.ofReal (stdGaussDensity (k + 2) p.1) *
          ENNReal.ofReal (stdGaussDensity (k + 2) p.2)) :=
      withDensity_prod_eq hμ_meas hμ_meas
    have hprod1_meas : Measurable (fun p : E × E =>
        ENNReal.ofReal (stdGaussDensity (k + 2) p.1) *
          ENNReal.ofReal (stdGaussDensity (k + 2) p.2)) :=
      (hμ_meas.comp measurable_fst).mul (hμ_meas.comp measurable_snd)
    haveI : SigmaFinite ((volume : Measure (E × E)).withDensity
        (fun p => ENNReal.ofReal (stdGaussDensity (k + 2) p.1) *
          ENNReal.ofReal (stdGaussDensity (k + 2) p.2))) := by
      rw [← hprod1]; infer_instance
    have hν_eq : ν = (volume : Measure ℝ).withDensity (ProbabilityTheory.exponentialPDF 1) := rfl
    haveI : SigmaFinite ((volume : Measure ℝ).withDensity (ProbabilityTheory.exponentialPDF 1)) := by
      rw [← hν_eq]; infer_instance
    change (μ.prod μ).prod ν = _
    rw [hprod1, hν_eq, withDensity_prod_eq hprod1_meas hν_meas]
    rfl
  have hP_W_pos : 0 < P W := by
    rw [hP_dens, withDensity_apply _ hW_open.measurableSet]
    have hρ_pos : ∀ ω ∈ W, 0 < ρ ω := by
      intro ω hω
      have he : 0 < ω.2 := hω.2
      have h1 : 0 < ENNReal.ofReal (stdGaussDensity (k + 2) ω.1.1) :=
        ENNReal.ofReal_pos.mpr (stdGaussDensity_pos _ _)
      have h2 : 0 < ENNReal.ofReal (stdGaussDensity (k + 2) ω.1.2) :=
        ENNReal.ofReal_pos.mpr (stdGaussDensity_pos _ _)
      have h3 : 0 < ProbabilityTheory.exponentialPDF 1 ω.2 := by
        rw [ProbabilityTheory.exponentialPDF_of_nonneg he.le]
        exact ENNReal.ofReal_pos.mpr (by positivity)
      exact ENNReal.mul_pos (ENNReal.mul_pos h1.ne' h2.ne').ne' h3.ne'
    have hρ_meas : Measurable ρ := by
      have hμ_meas : Measurable (fun x : E => ENNReal.ofReal (stdGaussDensity (k + 2) x)) :=
        ENNReal.continuous_ofReal.measurable.comp (stdGaussDensity_continuous (k + 2)).measurable
      have hν_meas : Measurable (ProbabilityTheory.exponentialPDF 1) :=
        ENNReal.continuous_ofReal.measurable.comp (ProbabilityTheory.measurable_exponentialPDFReal 1)
      exact ((hμ_meas.comp (measurable_fst.comp measurable_fst)).mul
        (hμ_meas.comp (measurable_snd.comp measurable_fst))).mul (hν_meas.comp measurable_snd)
    rw [lintegral_pos_iff_support hρ_meas]
    have hsub : W ⊆ Function.support ρ := fun ω hω => (hρ_pos ω hω).ne'
    have hsupp_meas : MeasurableSet (Function.support ρ) :=
      (measurableSet_singleton 0).preimage hρ_meas |>.compl
    rw [Measure.restrict_apply hsupp_meas, Set.inter_eq_right.mpr hsub]
    exact hW_vol_pos
  have hP_event_pos : 0 < P {ω | |Y ω| < X ω} :=
    lt_of_lt_of_le hP_W_pos (measure_mono Set.inter_subset_left)
  exact ENNReal.toReal_pos hP_event_pos.ne' (measure_ne_top P _)

/-- Equivalent CDF form of Claim 4 (`clm:first-term`): for all `n = k + 1 ≥ 1` and `t > 0`,
`((1 - 2 * weightedCdfZero ((t + 1) :: csCore)) + (1 - 2 * weightedCdfZero ((t - 1) :: csCore))) / 2 > 0`. -/
theorem firstTerm_weightedCdfZero_pos (k : ℕ) {t : ℝ} (ht : 0 < t) :
    let csCore : List ℝ := List.ofFn fun i : Fin (k + 2) => t - orderedNode k t i
    0 < ((1 - 2 * Probability.weightedCdfZero ((t + 1) :: csCore)) +
      (1 - 2 * Probability.weightedCdfZero ((t - 1) :: csCore))) / 2 := by
  intro csCore
  have hcore_nz : ∃ c ∈ csCore, c ≠ 0 := by
    by_cases h0 : t - orderedNode k t 0 = 0
    · refine ⟨t - orderedNode k t 1, List.mem_ofFn.mpr ⟨1, rfl⟩, ?_⟩
      have hlt : orderedNode k t 0 < orderedNode k t 1 := orderedNode_strictMono k t (by simp)
      linarith
    · exact ⟨t - orderedNode k t 0, List.mem_ofFn.mpr ⟨0, rfl⟩, h0⟩
  have hplus_nz : ∃ c ∈ (t + 1) :: csCore, c ≠ 0 := ⟨t + 1, by simp, by linarith⟩
  have hminus_nz : ∃ c ∈ (t - 1) :: csCore, c ≠ 0 := by
    obtain ⟨c, hc, hne⟩ := hcore_nz
    exact ⟨c, List.mem_cons_of_mem _ hc, hne⟩
  rw [← Probability.weightedExpSum_signMean hplus_nz,
    ← Probability.weightedExpSum_signMean hminus_nz]
  exact firstTerm_lawSignMean_pos k ht

end SharpL1.Analysis
