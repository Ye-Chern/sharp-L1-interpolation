module

public import Mathlib.Probability.Distributions.Exponential

public section

/-! ## Coefficient monotonicity for CDFs of nonnegative random variables -/

namespace SharpL1.Probability

open MeasureTheory
open scoped BigOperators

/-- Pointwise comparison of linear combinations of nonnegative variables. -/
theorem sum_mul_le_sum_mul {m : ℕ} {a b z : Fin m → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hab : ∀ i, a i ≤ b i) :
    ∑ i, a i * z i ≤ ∑ i, b i * z i :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hab i) (hz i)

/-- With the same nonnegative variables on both sides, increasing the
coefficients decreases the probability of a lower sublevel set. -/
theorem measure_sum_mul_le_antitone {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {m : ℕ} {a b : Fin m → ℝ} {Z : Fin m → Ω → ℝ} (t : ℝ)
    (hZ : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ Z i ω) (hab : ∀ i, a i ≤ b i) :
    μ {ω | ∑ i, b i * Z i ω ≤ t} ≤ μ {ω | ∑ i, a i * Z i ω ≤ t} := by
  refine measure_mono_ae ?_
  filter_upwards [ae_all_iff.mpr hZ] with ω hω hb
  exact (sum_mul_le_sum_mul hω hab).trans hb

/-- The rate-parameterized exponential is almost everywhere nonnegative. -/
theorem ae_nonneg_expMeasure (r : ℝ) :
    ∀ᵐ x ∂(ProbabilityTheory.expMeasure r), 0 ≤ x := by
  rw [ae_iff]
  have hset : {x : ℝ | ¬ 0 ≤ x} = Set.Iio 0 := by
    ext x
    simp [not_le]
  change (volume.withDensity (ProbabilityTheory.exponentialPDF r)) _ = _
  rw [hset, withDensity_apply _ measurableSet_Iio]
  calc
    ∫⁻ x in Set.Iio 0, ProbabilityTheory.exponentialPDF r x ∂volume =
        ∫⁻ _ in Set.Iio 0, (0 : ENNReal) ∂volume :=
      setLIntegral_congr_fun measurableSet_Iio fun _ hx => ProbabilityTheory.exponentialPDF_of_neg hx
    _ = 0 := by simp

/-- Specialization to shared variables with exponential marginals. -/
theorem measure_sum_mul_le_antitone_of_expMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {m : ℕ} {a b r : Fin m → ℝ} {Z : Fin m → Ω → ℝ} (t : ℝ)
    (hZm : ∀ i, AEMeasurable (Z i) μ)
    (hZ : ∀ i, μ.map (Z i) = ProbabilityTheory.expMeasure (r i))
    (hab : ∀ i, a i ≤ b i) :
    μ {ω | ∑ i, b i * Z i ω ≤ t} ≤ μ {ω | ∑ i, a i * Z i ω ≤ t} := by
  apply measure_sum_mul_le_antitone μ t _ hab
  intro i
  exact ae_of_ae_map (hZm i) (hZ i ▸ ae_nonneg_expMeasure (r i))

end SharpL1.Probability
