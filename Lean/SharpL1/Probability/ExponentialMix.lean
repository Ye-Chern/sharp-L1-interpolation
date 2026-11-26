import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Exponential mixture tail integral

This module connects the positive tail of a difference of independent
exponentials to a closed-form real integral.
-/

namespace SharpL1.Probability

open MeasureTheory

/-- The rate-parameterized exponential measure is a probability measure. -/
theorem expMeasure_probability {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (ProbabilityTheory.expMeasure r) :=
  ProbabilityTheory.isProbabilityMeasure_expMeasure hr

/-- Mathlib's exponential law is its real density with respect to volume. -/
theorem expMeasure_eq_withDensity {r : ℝ} :
    ProbabilityTheory.expMeasure r =
      volume.withDensity (ProbabilityTheory.exponentialPDF r) := by
  rfl

/-- Mathlib's exact CDF formula for its normalized exponential measure. -/
theorem expMeasure_cdf_formula {r : ℝ} (hr : 0 < r) (x : ℝ) :
    ProbabilityTheory.cdf (ProbabilityTheory.expMeasure r) x =
      if 0 ≤ x then 1 - Real.exp (-(r * x)) else 0 :=
  ProbabilityTheory.cdf_expMeasure_eq hr x

/-- The strict upper tail of an exponential measure, obtained from its CDF. -/
theorem expMeasure_Ioi {r x : ℝ} (hr : 0 < r) (hx : 0 ≤ x) :
    ProbabilityTheory.expMeasure r (Set.Ioi x) = ENNReal.ofReal (Real.exp (-(r * x))) := by
  let μ := ProbabilityTheory.expMeasure r
  letI : IsProbabilityMeasure μ := expMeasure_probability hr
  have hcompl : Set.Ioi x = (Set.Iic x)ᶜ := by
    ext y
    simp
  rw [hcompl, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ]
  rw [← ProbabilityTheory.ofReal_cdf μ x, ProbabilityTheory.cdf_expMeasure_eq hr x]
  rw [if_pos hx]
  have hE0 : 0 ≤ Real.exp (-(r * x)) := (Real.exp_pos _).le
  have hE1 : Real.exp (-(r * x)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith
  rw [← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub (1 : ℝ) (sub_nonneg.mpr hE1)]
  congr 1
  ring

/-- Product-measure slicing for the difference event.  The probability is the
integral, over the first exponential, of the second exponential's strict tail. -/
theorem exp_difference_product_tail_sections {a b u : ℝ} (_ha : 0 < a) (_hb : 0 < b)
    (_hu : 0 ≤ u) :
    let μ := ProbabilityTheory.expMeasure (1 / a)
    let ν := ProbabilityTheory.expMeasure (1 / b)
    μ.prod ν {p : ℝ × ℝ | p.2 - p.1 > u} =
      ∫⁻ x, ν (Set.Ioi (x + u)) ∂μ := by
  let μ := ProbabilityTheory.expMeasure (1 / a)
  let ν := ProbabilityTheory.expMeasure (1 / b)
  letI : IsProbabilityMeasure μ := expMeasure_probability (one_div_pos.mpr _ha)
  letI : IsProbabilityMeasure ν := expMeasure_probability (one_div_pos.mpr _hb)
  change (μ.prod ν) {p : ℝ × ℝ | p.2 - p.1 > u} = _
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.2 - p.1 > u} := by
    exact measurableSet_lt measurable_const (measurable_snd.sub measurable_fst)
  rw [Measure.prod_apply hmeas]
  apply lintegral_congr
  intro x
  congr 1
  ext y
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ioi]
  constructor <;> intro h <;> linarith

/-- Rewriting the first exponential law by its density turns the section formula
into a single nonnegative Lebesgue integral. -/
theorem exp_difference_product_density_integral {a b u : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hu : 0 ≤ u) :
    let μ := ProbabilityTheory.expMeasure (1 / a)
    let ν := ProbabilityTheory.expMeasure (1 / b)
    μ.prod ν {p : ℝ × ℝ | p.2 - p.1 > u} =
      ∫⁻ x, ProbabilityTheory.exponentialPDF (1 / a) x *
        ν (Set.Ioi (x + u)) ∂volume := by
  let μ := ProbabilityTheory.expMeasure (1 / a)
  let ν := ProbabilityTheory.expMeasure (1 / b)
  letI : IsProbabilityMeasure μ := expMeasure_probability (one_div_pos.mpr ha)
  letI : IsProbabilityMeasure ν := expMeasure_probability (one_div_pos.mpr hb)
  change (μ.prod ν) {p : ℝ × ℝ | p.2 - p.1 > u} = _
  rw [exp_difference_product_tail_sections ha hb hu]
  rw [expMeasure_eq_withDensity]
  have hE : MeasurableSet {p : ℝ × ℝ | p.2 - p.1 > u} := by
    exact measurableSet_lt measurable_const (measurable_snd.sub measurable_fst)
  have hsec (x : ℝ) : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.2 - p.1 > u} =
      Set.Ioi (x + u) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ioi]
    constructor <;> intro h <;> linarith
  have htail : Measurable (fun x : ℝ => ν (Set.Ioi (x + u))) := by
    convert (measurable_measure_prodMk_left (ν := ν) hE) using 1
    funext x
    exact congrArg ν (hsec x).symm
  have hpdf : Measurable (ProbabilityTheory.exponentialPDF (1 / a)) := by
    exact ENNReal.continuous_ofReal.measurable.comp
      (ProbabilityTheory.measurable_exponentialPDFReal (1 / a))
  change (∫⁻ x, ν (Set.Ioi (x + u)) ∂
      volume.withDensity (ProbabilityTheory.exponentialPDF (1 / a))) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume hpdf htail]
  rfl

/-- On nonnegative first coordinates, the density-times-tail integrand is the
real exponential integrand; negative coordinates contribute zero. -/
theorem exp_difference_density_integrand {a b u x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hu : 0 ≤ u) :
    ProbabilityTheory.exponentialPDF (1 / a) x *
        ProbabilityTheory.expMeasure (1 / b) (Set.Ioi (x + u)) =
      ENNReal.ofReal (if 0 ≤ x then
        (1 / a) * Real.exp (-x / a) * Real.exp (-(x + u) / b) else 0) := by
  by_cases hx : 0 ≤ x
  · rw [ProbabilityTheory.exponentialPDF_of_nonneg hx,
      expMeasure_Ioi (one_div_pos.mpr hb) (by linarith)]
    rw [if_pos hx]
    rw [show -(1 / a * x) = -x / a by ring,
      show -(1 / b * (x + u)) = -(x + u) / b by ring]
    rw [← ENNReal.ofReal_mul (show 0 ≤ (1 / a) * Real.exp (-x / a) by positivity)]
  · rw [ProbabilityTheory.exponentialPDF_of_neg (lt_of_not_ge hx)]
    simp [hx]

private theorem exponential_integrand_factor (a b u x : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    (1 / a) * Real.exp (-x / a) * Real.exp (-(x + u) / b) =
      (Real.exp (-u / b) / a) * Real.exp (-( (a + b) / (a * b)) * x) := by
  let c : ℝ := (a + b) / (a * b)
  have hexp (x : ℝ) :
      (1 / a) * Real.exp (-x / a) * Real.exp (-(x + u) / b) =
        (Real.exp (-u / b) / a) * Real.exp (-c * x) := by
    have hsplit : Real.exp (-(x + u) / b) =
        Real.exp (-x / b) * Real.exp (-u / b) := by
      rw [show -(x + u) / b = -x / b + -u / b by ring, Real.exp_add]
    have hrate : Real.exp (-x / a) * Real.exp (-x / b) = Real.exp (-c * x) := by
      rw [← Real.exp_add]
      apply Real.exp_injective
      dsimp [c]
      field_simp
      ring_nf
    rw [hsplit, ← mul_assoc]
    calc
      (1 / a) * Real.exp (-x / a) * Real.exp (-x / b) * Real.exp (-u / b) =
          (1 / a) * (Real.exp (-x / a) * Real.exp (-x / b)) * Real.exp (-u / b) := by ring
      _ = (Real.exp (-u / b) / a) * Real.exp (-c * x) := by rw [hrate]; ring
  exact hexp x

/-- Integrating the product of two exponential tails gives the upper tail of
the positive component in the difference of independent exponentials. -/
theorem exp_mixture_tail_integral {a b u : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Set.Ioi (0 : ℝ),
      (1 / a) * Real.exp (-x / a) * Real.exp (-(x + u) / b)) =
      b / (a + b) * Real.exp (-u / b) := by
  let c : ℝ := (a + b) / (a * b)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  rw [show (fun x : ℝ => (1 / a) * Real.exp (-x / a) * Real.exp (-(x + u) / b)) =
      (fun x => (Real.exp (-u / b) / a) * Real.exp (-c * x)) from funext fun x => exponential_integrand_factor a b u x ha hb]
  rw [integral_const_mul]
  rw [integral_exp_mul_Ioi (by linarith : -c < 0) 0]
  dsimp [c]
  field_simp
  simp [Real.exp_zero]

/-- The exact strict upper tail of B−A for independent exponentials of
means a and b. The lower tail follows by swapping the two coordinates. -/
theorem exp_difference_product_tail {a b u : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hu : 0 ≤ u) :
    (ProbabilityTheory.expMeasure (1 / a)).prod (ProbabilityTheory.expMeasure (1 / b))
        {p : ℝ × ℝ | p.2 - p.1 > u} =
      ENNReal.ofReal (b / (a + b) * Real.exp (-u / b)) := by
  let f : ℝ → ℝ := fun x => (1 / a) * Real.exp (-x / a) * Real.exp (-(x + u) / b)
  have hf : IntegrableOn f (Set.Ioi 0) := by
    have hc : 0 < (a + b) / (a * b) := by positivity
    simp only [f, exponential_integrand_factor a b u _ ha hb]
    exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hc) 0).const_mul _
  rw [exp_difference_product_density_integral ha hb hu]
  calc
    _ = ∫⁻ x, (Set.Ici (0 : ℝ)).indicator (fun y => ENNReal.ofReal (f y)) x := by
      apply lintegral_congr
      intro x
      rw [exp_difference_density_integrand ha hb hu]
      by_cases hx : 0 ≤ x <;> simp [Set.indicator, hx, f]
    _ = ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (f x) := by
      rw [lintegral_indicator measurableSet_Ici, restrict_Ioi_eq_restrict_Ici]
    _ = ENNReal.ofReal (∫ x in Set.Ioi (0 : ℝ), f x) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal hf
        (Filter.Eventually.of_forall fun x => by dsimp [f]; positivity)
    _ = _ := congrArg ENNReal.ofReal (exp_mixture_tail_integral ha hb)

end SharpL1.Probability
