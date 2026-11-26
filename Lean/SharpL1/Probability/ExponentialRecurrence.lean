import SharpL1.Probability.DifferenceLaw
import Mathlib.MeasureTheory.Group.Convolution

/-! ## Adding independent interior terms in the mixed-sign recursion -/

namespace SharpL1.Probability

open MeasureTheory Set

/-- The two-exponential mixture persists after adding an independent term
with law κ. This is the mixed-sign step of the CDF recursion as a measure identity. -/
theorem exp_difference_conv {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (κ : Measure ℝ) [SFinite κ] :
    let μ := ProbabilityTheory.expMeasure (1 / a)
    let ν := ProbabilityTheory.expMeasure (1 / b)
    ((μ.prod ν).map (fun p : ℝ × ℝ => p.2 - p.1)) ∗ κ =
      ENNReal.ofReal (a / (a + b)) • (μ.map (fun y : ℝ => -y) ∗ κ) +
        ENNReal.ofReal (b / (a + b)) • (ν ∗ κ) := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure (1 / a)) :=
    expMeasure_probability (one_div_pos.mpr ha)
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure (1 / b)) :=
    expMeasure_probability (one_div_pos.mpr hb)
  letI : IsProbabilityMeasure ((ProbabilityTheory.expMeasure (1 / a)).map (fun y : ℝ => -y)) :=
    Measure.isProbabilityMeasure_map measurable_neg.aemeasurable
  dsimp only
  rw [exp_difference_law ha hb, Measure.add_conv, Measure.conv_smul_left, Measure.conv_smul_left]

/-- Taking the closed sublevel set at zero of the mixed-sign step. -/
theorem exp_difference_conv_cdf_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (κ : Measure ℝ) [SFinite κ] :
    let μ := ProbabilityTheory.expMeasure (1 / a)
    let ν := ProbabilityTheory.expMeasure (1 / b)
    (((μ.prod ν).map (fun p : ℝ × ℝ => p.2 - p.1)) ∗ κ) (Iic 0) =
      ENNReal.ofReal (a / (a + b)) * ((μ.map (fun y : ℝ => -y)) ∗ κ) (Iic 0) +
        ENNReal.ofReal (b / (a + b)) * (ν ∗ κ) (Iic 0) := by
  dsimp only
  rw [exp_difference_conv ha hb κ]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]

end SharpL1.Probability
