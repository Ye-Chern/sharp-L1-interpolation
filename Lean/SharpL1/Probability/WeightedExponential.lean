import SharpL1.Probability.ExponentialRecurrence
import SharpL1.Probability.CDFOrder
import SharpL1.Probability.ScaledExponential

/-! ## Laws of finite weighted sums of unit exponential variables -/

namespace SharpL1.Probability

open MeasureTheory

/-- The law of c times a rate-one exponential. -/
noncomputable def weightedExp (c : ℝ) : Measure ℝ :=
  (ProbabilityTheory.expMeasure 1).map (fun x : ℝ => c * x)

instance (c : ℝ) : IsProbabilityMeasure (weightedExp c) := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) := expMeasure_probability zero_lt_one
  exact Measure.isProbabilityMeasure_map (measurable_const.mul measurable_id).aemeasurable

/-- The law of the sum of independent rate-one exponentials with the listed
coefficients. The empty sum is a point mass at zero. -/
noncomputable def weightedExpSum : List ℝ → Measure ℝ
  | [] => Measure.dirac 0
  | c :: cs => weightedExp c ∗ weightedExpSum cs

instance (cs : List ℝ) : IsProbabilityMeasure (weightedExpSum cs) := by
  induction cs with
  | nil =>
    change IsProbabilityMeasure (Measure.dirac (0 : ℝ))
    infer_instance
  | cons c cs ih =>
    letI := ih
    change IsProbabilityMeasure (weightedExp c ∗ weightedExpSum cs)
    infer_instance

@[simp] theorem weightedExpSum_singleton (c : ℝ) : weightedExpSum [c] = weightedExp c := by
  simpa only [weightedExpSum] using Measure.conv_dirac_zero (weightedExp c)

theorem weightedExpSum_append (xs ys : List ℝ) :
    weightedExpSum (xs ++ ys) = weightedExpSum xs ∗ weightedExpSum ys := by
  induction xs with
  | nil => simp [weightedExpSum, Measure.dirac_zero_conv]
  | cons c cs ih =>
    change weightedExp c ∗ weightedExpSum (cs ++ ys) =
      (weightedExp c ∗ weightedExpSum cs) ∗ weightedExpSum ys
    rw [ih, Measure.conv_assoc]

theorem weightedExp_pos {a : ℝ} (ha : 0 < a) :
    weightedExp a = ProbabilityTheory.expMeasure (1 / a) :=
  expMeasure_one_map_mul ha

theorem weightedExp_neg {a : ℝ} (ha : 0 < a) :
    weightedExp (-a) = (ProbabilityTheory.expMeasure (1 / a)).map (fun y : ℝ => -y) := by
  have hscale : Measurable (fun x : ℝ => a * x) := measurable_const.mul measurable_id
  rw [← weightedExp_pos ha, weightedExp, weightedExp, Measure.map_map measurable_neg hscale]
  congr 1
  funext x
  simp

private theorem weightedExp_mixed_pair {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    weightedExp (-a) ∗ weightedExp b =
      ((ProbabilityTheory.expMeasure (1 / a)).prod (ProbabilityTheory.expMeasure (1 / b))).map
        (fun p : ℝ × ℝ => p.2 - p.1) := by
  let μ := ProbabilityTheory.expMeasure (1 / a)
  let ν := ProbabilityTheory.expMeasure (1 / b)
  letI : IsProbabilityMeasure μ := expMeasure_probability (one_div_pos.mpr ha)
  letI : IsProbabilityMeasure ν := expMeasure_probability (one_div_pos.mpr hb)
  have hprod : (μ.map (fun y : ℝ => -y)).prod ν =
      (μ.prod ν).map (Prod.map (fun y : ℝ => -y) id) := by
    simpa using Measure.map_prod_map μ ν measurable_neg measurable_id
  change weightedExp (-a) ∗ weightedExp b = (μ.prod ν).map _
  rw [weightedExp_neg ha, weightedExp_pos hb]
  change Measure.map (fun p : ℝ × ℝ => p.1 + p.2) ((μ.map (fun y : ℝ => -y)).prod ν) = _
  have hadd : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
  rw [hprod, Measure.map_map hadd (measurable_neg.prodMap measurable_id)]
  congr 1
  funext p
  simp [sub_eq_add_neg, add_comm]

/-- The law of the full weighted sum has the mixed-sign recurrence from the
paper. The weights on the two terms delete the opposite endpoint. -/
theorem weightedExpSum_mixed {l h : ℝ} (hl : l < 0) (hh : 0 < h) (middle : List ℝ) :
    weightedExpSum (l :: (middle ++ [h])) =
      ENNReal.ofReal (-l / (h - l)) • weightedExpSum (l :: middle) +
        ENNReal.ofReal (h / (h - l)) • weightedExpSum (middle ++ [h]) := by
  have hsplit : weightedExpSum (l :: (middle ++ [h])) =
      (weightedExp l ∗ weightedExp h) ∗ weightedExpSum middle := by
    change weightedExp l ∗ weightedExpSum (middle ++ [h]) = _
    rw [weightedExpSum_append, weightedExpSum_singleton,
      Measure.conv_comm (weightedExpSum middle) (weightedExp h), Measure.conv_assoc]
  have hpair := weightedExp_mixed_pair (neg_pos.mpr hl) hh
  rw [neg_neg] at hpair
  have hlaw := exp_difference_conv (neg_pos.mpr hl) hh (weightedExpSum middle)
  dsimp only at hlaw
  rw [← weightedExp_neg (neg_pos.mpr hl), neg_neg, ← weightedExp_pos hh,
    Measure.conv_comm (weightedExp h) (weightedExpSum middle)] at hlaw
  rw [hsplit, hpair, ← weightedExp_pos hh, hlaw, weightedExpSum_append, weightedExpSum_singleton]
  change ENNReal.ofReal (-l / (-l + h)) • (weightedExp l ∗ weightedExpSum middle) +
      ENNReal.ofReal (h / (-l + h)) • (weightedExpSum middle ∗ weightedExp h) =
    ENNReal.ofReal (-l / (h - l)) • (weightedExp l ∗ weightedExpSum middle) +
      ENNReal.ofReal (h / (h - l)) • (weightedExpSum middle ∗ weightedExp h)
  rw [sub_eq_add_neg, add_comm h (-l)]

/-- The real-valued closed CDF at zero of a finite weighted exponential sum. -/
noncomputable def weightedCdfZero (cs : List ℝ) : ℝ :=
  (weightedExpSum cs).real (Set.Iic 0)

/-- The mixed branch agrees with the normalized real CDF recursion. -/
theorem weightedCdfZero_mixed {l h : ℝ} (hl : l < 0) (hh : 0 < h) (middle : List ℝ) :
    weightedCdfZero (l :: (middle ++ [h])) =
      (-l * weightedCdfZero (l :: middle) + h * weightedCdfZero (middle ++ [h])) / (h - l) := by
  have hd : 0 ≤ h - l := sub_nonneg.mpr (hl.le.trans hh.le)
  have hα : 0 ≤ -l / (h - l) := div_nonneg (neg_nonneg.mpr hl.le) hd
  have hβ : 0 ≤ h / (h - l) := div_nonneg hh.le hd
  simp only [weightedCdfZero, measureReal_def]
  rw [weightedExpSum_mixed hl hh, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hα, ENNReal.toReal_ofReal hβ]
  ring

private theorem ae_conv_of_add {μ ν : Measure ℝ} [SFinite ν] {P Q R : ℝ → Prop}
    (hR : MeasurableSet {x | R x}) (hμ : ∀ᵐ x ∂μ, P x) (hν : ∀ᵐ y ∂ν, Q y)
    (hadd : ∀ x y, P x → Q y → R (x + y)) : ∀ᵐ z ∂(μ ∗ ν), R z := by
  have hm : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
  rw [Measure.conv, ae_map_iff hm.aemeasurable hR]
  rw [Measure.ae_prod_iff_ae_ae (μ := μ) (ν := ν) (p := fun z => R (z.1 + z.2)) (hm hR)]
  filter_upwards [hμ] with x hx
  filter_upwards [hν] with y hy
  exact hadd x y hx hy

private theorem weightedExp_ae_nonpos {c : ℝ} (hc : c ≤ 0) :
    ∀ᵐ x ∂(weightedExp c), x ≤ 0 := by
  have hm : Measurable (fun x : ℝ => c * x) := measurable_const.mul measurable_id
  rw [weightedExp, ae_map_iff hm.aemeasurable measurableSet_Iic]
  filter_upwards [ae_nonneg_expMeasure 1] with x hx
  exact mul_nonpos_of_nonpos_of_nonneg hc hx

private theorem weightedExp_ae_nonneg {c : ℝ} (hc : 0 ≤ c) :
    ∀ᵐ x ∂(weightedExp c), 0 ≤ x := by
  have hm : Measurable (fun x : ℝ => c * x) := measurable_const.mul measurable_id
  rw [weightedExp, ae_map_iff hm.aemeasurable measurableSet_Ici]
  filter_upwards [ae_nonneg_expMeasure 1] with x hx
  exact mul_nonneg hc hx

private theorem weightedExp_ae_pos {c : ℝ} (hc : 0 < c) :
    ∀ᵐ x ∂(weightedExp c), 0 < x := by
  have hbase : ∀ᵐ x ∂(ProbabilityTheory.expMeasure 1), 0 < x := by
    letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
      expMeasure_probability zero_lt_one
    have hset : {x : ℝ | ¬ 0 < x} = Set.Iic 0 := by ext x; simp
    rw [ae_iff, hset, ← ProbabilityTheory.ofReal_cdf,
      expMeasure_cdf_formula (show (0 : ℝ) < 1 by norm_num)]
    simp
  have hm : Measurable (fun x : ℝ => c * x) := measurable_const.mul measurable_id
  rw [weightedExp, ae_map_iff hm.aemeasurable measurableSet_Ioi]
  filter_upwards [hbase] with x hx
  exact mul_pos hc hx

private theorem weightedExpSum_ae_nonpos (cs : List ℝ) (hc : ∀ c ∈ cs, c ≤ 0) :
    ∀ᵐ x ∂(weightedExpSum cs), x ≤ 0 := by
  induction cs with
  | nil => exact (ae_dirac_iff measurableSet_Iic).2 le_rfl
  | cons c cs ih =>
    change ∀ᵐ x ∂(weightedExp c ∗ weightedExpSum cs), x ≤ 0
    exact ae_conv_of_add measurableSet_Iic (weightedExp_ae_nonpos (hc c (by simp)))
      (ih fun d hd => hc d (List.mem_cons_of_mem _ hd)) (fun _ _ => add_nonpos)

private theorem weightedExpSum_ae_nonneg (cs : List ℝ) (hc : ∀ c ∈ cs, 0 ≤ c) :
    ∀ᵐ x ∂(weightedExpSum cs), 0 ≤ x := by
  induction cs with
  | nil => exact (ae_dirac_iff measurableSet_Ici).2 le_rfl
  | cons c cs ih =>
    change ∀ᵐ x ∂(weightedExp c ∗ weightedExpSum cs), 0 ≤ x
    exact ae_conv_of_add measurableSet_Ici (weightedExp_ae_nonneg (hc c (by simp)))
      (ih fun d hd => hc d (List.mem_cons_of_mem _ hd)) (fun _ _ => add_nonneg)

private theorem weightedExpSum_ae_pos (cs : List ℝ) (hc : ∀ c ∈ cs, 0 ≤ c)
    (hpos : ∃ c ∈ cs, 0 < c) : ∀ᵐ x ∂(weightedExpSum cs), 0 < x := by
  induction cs with
  | nil => simp at hpos
  | cons c cs ih =>
    change ∀ᵐ x ∂(weightedExp c ∗ weightedExpSum cs), 0 < x
    have hcs (d : ℝ) (hd : d ∈ cs) : 0 ≤ d := hc d (List.mem_cons_of_mem _ hd)
    obtain ⟨d, hd, hdpos⟩ := hpos
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ae_conv_of_add measurableSet_Ioi (weightedExp_ae_pos hdpos)
        (weightedExpSum_ae_nonneg cs hcs) (fun _ _ => add_pos_of_pos_of_nonneg)
    · exact ae_conv_of_add measurableSet_Ioi (weightedExp_ae_nonneg (hc c (by simp)))
        (ih hcs ⟨d, hd, hdpos⟩) (fun _ _ => add_pos_of_nonneg_of_pos)

/-- The closed zero-threshold CDF is 1 for nonpositive coefficients, including
the all-zero and empty sums. -/
theorem weightedCdfZero_nonpos (cs : List ℝ) (hc : ∀ c ∈ cs, c ≤ 0) :
    weightedCdfZero cs = 1 := by
  have hz : (weightedExpSum cs) (Set.Iic 0)ᶜ = 0 := (ae_iff.mp (weightedExpSum_ae_nonpos cs hc))
  have h := measure_add_measure_compl (μ := weightedExpSum cs) (s := Set.Iic 0) measurableSet_Iic
  rw [hz, add_zero] at h
  simp [weightedCdfZero, measureReal_def, h]

/-- The closed zero-threshold CDF is 0 when all coefficients are nonnegative
and at least one is positive. -/
theorem weightedCdfZero_nonneg_pos (cs : List ℝ) (hc : ∀ c ∈ cs, 0 ≤ c)
    (hpos : ∃ c ∈ cs, 0 < c) : weightedCdfZero cs = 0 := by
  have h := ae_iff.mp (weightedExpSum_ae_pos cs hc hpos)
  have hset : {x : ℝ | ¬ 0 < x} = Set.Iic 0 := by ext x; simp
  rw [hset] at h
  simp [weightedCdfZero, measureReal_def, h]

end SharpL1.Probability
