module

public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic.Ring

public section

/-! ## Sign expectation of a law with zero mass at zero -/

namespace SharpL1.Probability

open MeasureTheory Set

/-- Difference of the positive and negative masses of a probability law. -/
@[expose] noncomputable def lawSignMean (μ : Measure ℝ) : ℝ :=
  μ.real (Ioi 0) - μ.real (Iio 0)

/-- For a law with no atom at zero, the difference of positive and negative
masses is 1 minus twice its closed CDF at zero. -/
theorem lawSignMean_eq_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hzero : μ {0} = 0) :
    lawSignMean μ = 1 - 2 * ProbabilityTheory.cdf μ 0 := by
  rw [lawSignMean, measureReal_congr (Iio_ae_eq_Iic' hzero),
    ← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ, ProbabilityTheory.cdf_eq_real]
  ring

end SharpL1.Probability
