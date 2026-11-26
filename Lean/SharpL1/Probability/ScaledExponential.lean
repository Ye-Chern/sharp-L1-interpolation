module

public import SharpL1.Probability.ExponentialMix

public section

/-! ## Rescaling the unit exponential measure -/

namespace SharpL1.Probability

open MeasureTheory Set

/-- Multiplication by a positive scale sends a rate-one exponential to rate
1/a. Equality is proved on the closed CDF half-lines. -/
theorem expMeasure_one_map_mul {a : ℝ} (ha : 0 < a) :
    (ProbabilityTheory.expMeasure 1).map (fun x : ℝ => a * x) =
      ProbabilityTheory.expMeasure (1 / a) := by
  let μ := ProbabilityTheory.expMeasure 1
  let ν := ProbabilityTheory.expMeasure (1 / a)
  have hmeas : Measurable (fun x : ℝ => a * x) := measurable_const.mul measurable_id
  letI : IsProbabilityMeasure μ := expMeasure_probability zero_lt_one
  letI : IsProbabilityMeasure ν := expMeasure_probability (one_div_pos.mpr ha)
  letI : IsProbabilityMeasure (μ.map (fun x : ℝ => a * x)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  change μ.map (fun x : ℝ => a * x) = ν
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply hmeas measurableSet_Iic]
  have hpre : (fun x : ℝ => a * x) ⁻¹' Iic t = Iic (t / a) := by
    ext x
    simp only [mem_preimage, mem_Iic, le_div_iff₀ ha, mul_comm a x]
  rw [hpre, ← ProbabilityTheory.ofReal_cdf μ, ← ProbabilityTheory.ofReal_cdf ν]
  rw [expMeasure_cdf_formula zero_lt_one, expMeasure_cdf_formula (one_div_pos.mpr ha)]
  by_cases ht : 0 ≤ t
  · rw [if_pos (div_nonneg ht ha.le), if_pos ht, one_mul]
    rw [show -(t / a) = -(1 / a * t) by ring]
  · rw [if_neg (not_le_of_gt (div_neg_of_neg_of_pos (lt_of_not_ge ht) ha)), if_neg ht]

end SharpL1.Probability
