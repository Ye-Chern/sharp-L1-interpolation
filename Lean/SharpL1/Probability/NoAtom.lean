import SharpL1.Probability.ExponentialMix
import Mathlib.Tactic.Linarith

/-! ## No atoms for a sum with a nonzero independent exponential term -/

namespace SharpL1.Probability

open MeasureTheory

/-- A nonzero weighted exponential term makes the sum atomless, even when the
remaining terms have atoms. Independence is represented by the product measure. -/
theorem prod_add_mul_exp_level_set_null {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {v : Ω → ℝ} (hv : Measurable v)
    {r c : ℝ} (hr : 0 < r) (hc : c ≠ 0) (q : ℝ) :
    (μ.prod (ProbabilityTheory.expMeasure r)) {p : Ω × ℝ | v p.1 + c * p.2 = q} = 0 := by
  let ν := ProbabilityTheory.expMeasure r
  letI : IsProbabilityMeasure ν := expMeasure_probability hr
  letI : NullSingletonClass ν := by
    dsimp [ν]
    rw [expMeasure_eq_withDensity]
    infer_instance
  change (μ.prod ν) {p : Ω × ℝ | v p.1 + c * p.2 = q} = 0
  have hE : MeasurableSet {p : Ω × ℝ | v p.1 + c * p.2 = q} :=
    measurableSet_eq_fun ((hv.comp measurable_fst).add (measurable_const.mul measurable_snd))
      measurable_const
  have hsection (x : Ω) : Prod.mk x ⁻¹' {p : Ω × ℝ | v p.1 + c * p.2 = q} =
      {(q - v x) / c} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff, eq_div_iff_mul_eq hc]
    constructor <;> intro h <;> linarith [mul_comm c y]
  rw [Measure.prod_apply hE]
  simp_rw [hsection, measure_singleton, lintegral_zero]

end SharpL1.Probability
