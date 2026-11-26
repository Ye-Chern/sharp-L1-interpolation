module

public import SharpL1.Probability.NoAtom

public section

/-! ## The mixture law of a difference of independent exponentials -/

namespace SharpL1.Probability

open MeasureTheory Set

private theorem expMeasure_Iic {r : ℝ} (hr : 0 < r) (x : ℝ) :
    ProbabilityTheory.expMeasure r (Iic x) =
      ENNReal.ofReal (if 0 ≤ x then 1 - Real.exp (-(r * x)) else 0) := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure r) := expMeasure_probability hr
  rw [← ProbabilityTheory.ofReal_cdf, expMeasure_cdf_formula hr]

private theorem exp_difference_measure_le_of_lt {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) :
    let μ := ProbabilityTheory.expMeasure (1 / a)
    let ν := ProbabilityTheory.expMeasure (1 / b)
    (μ.prod ν) {p : ℝ × ℝ | p.2 - p.1 ≤ x} =
      (μ.prod ν) {p : ℝ × ℝ | p.2 - p.1 < x} := by
  let μ := ProbabilityTheory.expMeasure (1 / a)
  let ν := ProbabilityTheory.expMeasure (1 / b)
  letI : IsProbabilityMeasure μ := expMeasure_probability (one_div_pos.mpr ha)
  letI : IsProbabilityMeasure ν := expMeasure_probability (one_div_pos.mpr hb)
  change (μ.prod ν) _ = _
  have hnull : (μ.prod ν) {p : ℝ × ℝ | p.2 - p.1 = x} = 0 := by
    simpa [ν, one_div, one_mul, sub_eq_add_neg, add_comm] using
      (prod_add_mul_exp_level_set_null μ (v := fun u : ℝ => -u) measurable_neg
        (one_div_pos.mpr hb) (c := 1) one_ne_zero x)
  have hsplit :
      {p : ℝ × ℝ | p.2 - p.1 ≤ x} =
        {p : ℝ × ℝ | p.2 - p.1 < x} ∪ {p : ℝ × ℝ | p.2 - p.1 = x} := by
    ext p
    simp only [mem_setOf_eq, mem_union, le_iff_lt_or_eq]
  apply le_antisymm
  · rw [hsplit]
    exact (measure_union_le _ _).trans_eq (by rw [hnull, add_zero])
  · apply measure_mono
    intro p hp
    exact le_of_lt (show p.2 - p.1 < x from hp)

/-- The exact CDF of B−A is the weighted sum of the CDFs of −A and B.
The conclusion includes x=0. -/
theorem exp_difference_cdf {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    let μ := ProbabilityTheory.expMeasure (1 / a)
    let ν := ProbabilityTheory.expMeasure (1 / b)
    (μ.prod ν) {p : ℝ × ℝ | p.2 - p.1 ≤ x} =
      ENNReal.ofReal (a / (a + b)) * μ {y : ℝ | -y ≤ x} +
        ENNReal.ofReal (b / (a + b)) * ν (Iic x) := by
  let μ := ProbabilityTheory.expMeasure (1 / a)
  let ν := ProbabilityTheory.expMeasure (1 / b)
  have ha' := one_div_pos.mpr ha
  have hb' := one_div_pos.mpr hb
  letI : IsProbabilityMeasure μ := expMeasure_probability ha'
  letI : IsProbabilityMeasure ν := expMeasure_probability hb'
  change (μ.prod ν) _ = _
  have negSet : {y : ℝ | -y ≤ x} = Ici (-x) := by
    ext y
    simp only [mem_setOf_eq, mem_Ici]
    constructor <;> intro h <;> linarith
  by_cases hx : 0 ≤ x
  · have hE : MeasurableSet {p : ℝ × ℝ | p.2 - p.1 > x} :=
      measurableSet_lt measurable_const (measurable_snd.sub measurable_fst)
    have hcomp : {p : ℝ × ℝ | p.2 - p.1 ≤ x} = {p : ℝ × ℝ | p.2 - p.1 > x}ᶜ := by
      ext p
      simp
    have hμ0 : μ (Iic 0) = 0 := by simpa [μ] using expMeasure_Iic ha' 0
    have hμneg : μ (Ici (-x)) = 1 := by
      have hsmall : μ (Iio (-x)) = 0 :=
        le_antisymm ((measure_mono fun (y : ℝ) (hy : y ∈ Iio (-x)) =>
          show y ∈ Iic (0 : ℝ) from le_of_lt (hy.trans_le (neg_nonpos.mpr hx))).trans_eq hμ0)
          bot_le
      rw [← compl_Iio, measure_compl measurableSet_Iio (measure_ne_top _ _), measure_univ, hsmall,
        tsub_zero]
    have hνcdf : ν (Iic x) = ENNReal.ofReal (1 - Real.exp (-x / b)) := by
      rw [expMeasure_Iic hb', if_pos hx, show -(1 / b * x) = -x / b by ring]
    have hExp : Real.exp (-x / b) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx) hb.le
    have hab : 0 < a + b := add_pos ha hb
    have hweight : a / (a + b) + b / (a + b) = 1 := by rw [← add_div, div_self hab.ne']
    have hα := div_nonneg ha.le hab.le
    have hβ := div_nonneg hb.le hab.le
    rw [hcomp, measure_compl hE (measure_ne_top _ _), measure_univ, exp_difference_product_tail ha hb hx,
      negSet, hμneg, hνcdf, mul_one, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ (mul_nonneg hβ (Real.exp_nonneg _)),
      ← ENNReal.ofReal_mul hβ, ← ENNReal.ofReal_add hα (mul_nonneg hβ (sub_nonneg.mpr hExp))]
    congr 1
    linarith [hweight]
  · have hx' : x < 0 := lt_of_not_ge hx
    have hνcdf : ν (Iic x) = 0 := by rw [expMeasure_Iic hb', if_neg hx, ENNReal.ofReal_zero]
    letI : NullSingletonClass μ := by
      dsimp [μ]
      rw [expMeasure_eq_withDensity]
      infer_instance
    have hμneg : μ (Ici (-x)) = ENNReal.ofReal (Real.exp (x / a)) := by
      rw [← measure_congr (Ioi_ae_eq_Ici (μ := μ) (a := -x))]
      rw [expMeasure_Ioi ha' (neg_nonneg.mpr hx'.le), show -(1 / a * -x) = x / a by ring]
    have hswapSet : Prod.swap ⁻¹' {p : ℝ × ℝ | p.2 - p.1 > -x} =
        {p : ℝ × ℝ | p.2 - p.1 < x} := by
      ext p
      change p.1 - p.2 > -x ↔ p.2 - p.1 < x
      constructor <;> intro h <;> linarith
    have hswap : (μ.prod ν) {p : ℝ × ℝ | p.2 - p.1 < x} =
        (ν.prod μ) {p : ℝ × ℝ | p.2 - p.1 > -x} := by
      rw [← hswapSet]
      have hmeas : MeasurableSet {p : ℝ × ℝ | p.2 - p.1 > -x} :=
        measurableSet_lt measurable_const (measurable_snd.sub measurable_fst)
      exact (Measure.measurePreserving_swap (μ := μ) (ν := ν)).measure_preimage
        hmeas.nullMeasurableSet
    rw [exp_difference_measure_le_of_lt ha hb, hswap,
      exp_difference_product_tail hb ha (neg_nonneg.mpr hx'.le),
      negSet, hμneg, hνcdf, mul_zero, add_zero,
      ← ENNReal.ofReal_mul (div_nonneg ha.le (add_nonneg ha.le hb.le)), add_comm a b, neg_neg]

/-- A difference of independent exponentials is a mixture of a negative
exponential of mean magnitude a and a positive exponential of mean b. -/
theorem exp_difference_law {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    let μ := ProbabilityTheory.expMeasure (1 / a)
    let ν := ProbabilityTheory.expMeasure (1 / b)
    (μ.prod ν).map (fun p : ℝ × ℝ => p.2 - p.1) =
      ENNReal.ofReal (a / (a + b)) • μ.map (fun y : ℝ => -y) +
        ENNReal.ofReal (b / (a + b)) • ν := by
  let μ := ProbabilityTheory.expMeasure (1 / a)
  let ν := ProbabilityTheory.expMeasure (1 / b)
  letI : IsProbabilityMeasure μ := expMeasure_probability (one_div_pos.mpr ha)
  letI : IsProbabilityMeasure ν := expMeasure_probability (one_div_pos.mpr hb)
  have hmeas : Measurable (fun p : ℝ × ℝ => p.2 - p.1) := measurable_snd.sub measurable_fst
  letI : IsProbabilityMeasure ((μ.prod ν).map (fun p : ℝ × ℝ => p.2 - p.1)) :=
    isProbabilityMeasure_map hmeas.aemeasurable
  apply Measure.ext_of_Iic
  intro x
  simp only [Measure.map_apply hmeas measurableSet_Iic, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul, Measure.map_apply measurable_neg measurableSet_Iic]
  exact exp_difference_cdf ha hb x

end SharpL1.Probability
