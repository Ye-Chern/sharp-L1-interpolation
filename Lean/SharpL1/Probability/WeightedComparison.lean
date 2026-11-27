module

public import SharpL1.Probability.NoAtom
public import SharpL1.Probability.SignMean
public import SharpL1.Probability.WeightedExponential

public section

/-! ## Order and scaling for the weighted exponential laws used by the checker -/

namespace SharpL1.Probability

open MeasureTheory Set

private theorem weightedExp_conv {μ : Measure ℝ} [SFinite μ] (c : ℝ) :
    weightedExp c ∗ μ = ((ProbabilityTheory.expMeasure 1).prod μ).map
      (fun p : ℝ × ℝ => c * p.1 + p.2) := by
  let ν := ProbabilityTheory.expMeasure (1 : ℝ)
  letI : IsProbabilityMeasure ν := expMeasure_probability zero_lt_one
  have hc : Measurable (fun x : ℝ => c * x) := measurable_const.mul measurable_id
  have hadd : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
  have hprod : (ν.map (fun x : ℝ => c * x)).prod μ =
      (ν.prod μ).map (Prod.map (fun x : ℝ => c * x) id) := by
    simpa using Measure.map_prod_map ν μ hc measurable_id
  change Measure.map (fun p : ℝ × ℝ => p.1 + p.2) ((ν.map (fun x : ℝ => c * x)).prod μ) = _
  rw [hprod, Measure.map_map hadd (hc.prodMap measurable_id)]
  rfl

private theorem weightedExpSum_cons_Iic (c : ℝ) (cs : List ℝ) (t : ℝ) :
    weightedExpSum (c :: cs) (Iic t) =
      ∫⁻ x, weightedExpSum cs (Iic (t - c * x)) ∂ProbabilityTheory.expMeasure 1 := by
  rw [weightedExpSum, weightedExp_conv]
  have hm : Measurable (fun p : ℝ × ℝ => c * p.1 + p.2) :=
    (measurable_const.mul measurable_fst).add measurable_snd
  rw [Measure.map_apply hm measurableSet_Iic, Measure.prod_apply (hm measurableSet_Iic)]
  refine lintegral_congr fun x => congrArg (weightedExpSum cs) ?_
  ext y
  change c * x + y ≤ t ↔ y ≤ t - c * x
  constructor <;> intro h <;> linarith

/-- Increasing all coefficients decreases every closed sublevel probability.
Signs of the individual coefficients may be arbitrary. -/
theorem weightedExpSum_Iic_antitone {as bs : List ℝ} (hab : List.Forall₂ (· ≤ ·) as bs)
    (t : ℝ) : weightedExpSum bs (Iic t) ≤ weightedExpSum as (Iic t) := by
  induction hab generalizing t with
  | nil => exact le_rfl
  | @cons a b as bs hab _ ih =>
    rw [weightedExpSum_cons_Iic, weightedExpSum_cons_Iic]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_nonneg_expMeasure 1] with x hx
    apply (ih (t - b * x)).trans
    exact measure_mono (Iic_subset_Iic.mpr (sub_le_sub_left (mul_le_mul_of_nonneg_right hab hx) t))

theorem weightedCdfZero_antitone {as bs : List ℝ} (hab : List.Forall₂ (· ≤ ·) as bs) :
    weightedCdfZero bs ≤ weightedCdfZero as :=
  ENNReal.toReal_mono (measure_ne_top _ _) (weightedExpSum_Iic_antitone hab 0)

private theorem weightedExp_conv_singleton_eq_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {c : ℝ} (hc : c ≠ 0) (t : ℝ) : (weightedExp c ∗ μ) {t} = 0 := by
  let ν := ProbabilityTheory.expMeasure (1 : ℝ)
  letI : IsProbabilityMeasure ν := expMeasure_probability zero_lt_one
  have hm : Measurable (fun p : ℝ × ℝ => c * p.1 + p.2) :=
    (measurable_const.mul measurable_fst).add measurable_snd
  rw [weightedExp_conv, Measure.map_apply hm (measurableSet_singleton t), ← Measure.prod_swap]
  rw [Measure.map_apply measurable_swap (hm (measurableSet_singleton t))]
  change (μ.prod ν) {p : ℝ × ℝ | c * p.2 + p.1 = t} = 0
  simp only [add_comm (c * _)]
  exact prod_add_mul_exp_level_set_null μ measurable_id zero_lt_one hc t

/-- A finite weighted sum has no atoms as soon as one coefficient is nonzero. -/
theorem weightedExpSum_singleton_eq_zero {cs : List ℝ} (h : ∃ c ∈ cs, c ≠ 0) (t : ℝ) :
    weightedExpSum cs {t} = 0 := by
  obtain ⟨c, hc, hne⟩ := h
  obtain ⟨xs, ys, rfl⟩ := List.append_of_mem hc
  rw [weightedExpSum_append, weightedExpSum, ← Measure.conv_assoc,
    Measure.conv_comm (weightedExpSum xs) (weightedExp c), Measure.conv_assoc]
  exact weightedExp_conv_singleton_eq_zero _ hne t

/-- Multiplying all coefficients by a positive common scale preserves the CDF at zero. -/
theorem weightedCdfZero_map_pos (cs : List ℝ) {s : ℝ} (hs : 0 < s) :
    weightedCdfZero (cs.map fun c => s * c) = weightedCdfZero cs := by
  let L : ℝ →+ ℝ := ⟨⟨fun x => s * x, mul_zero s⟩, mul_add s⟩
  have hm : Measurable L := measurable_const.mul measurable_id
  have hsum : weightedExpSum (cs.map fun c => s * c) = (weightedExpSum cs).map L := by
    induction cs with
    | nil =>
      simp only [List.map_nil, weightedExpSum, Measure.map_dirac' hm, map_zero]
    | cons c cs ih =>
      rw [List.map_cons, weightedExpSum, weightedExpSum, Measure.map_conv_addMonoidHom L hm, ih]
      congr 1
      have hc : Measurable (fun x : ℝ => c * x) := measurable_const.mul measurable_id
      rw [weightedExp, weightedExp, Measure.map_map hm hc]
      congr 1
      funext x
      exact mul_assoc s c x
  have hset : L ⁻¹' Iic 0 = Iic 0 := by
    ext x
    change s * x ≤ 0 ↔ x ≤ 0
    exact ⟨fun hx => le_of_not_gt fun h => (mul_pos hs h).not_ge hx,
      mul_nonpos_of_nonneg_of_nonpos hs.le⟩
  simp only [weightedCdfZero, measureReal_def, hsum, Measure.map_apply hm measurableSet_Iic, hset]

/-- For a nondegenerate sum, the closed CDF controls the sign expectation. -/
theorem weightedExpSum_signMean {cs : List ℝ} (h : ∃ c ∈ cs, c ≠ 0) :
    lawSignMean (weightedExpSum cs) = 1 - 2 * weightedCdfZero cs := by
  rw [lawSignMean_eq_cdf _ (weightedExpSum_singleton_eq_zero h 0),
    ProbabilityTheory.cdf_eq_real, weightedCdfZero]

end SharpL1.Probability
