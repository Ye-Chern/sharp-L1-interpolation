import SharpL1.Analysis.DividedCDF
import SharpL1.Analysis.ErrorDividedDifference
import SharpL1.Probability.WeightedExponential
import SharpL1.Probability.WeightedComparison

/-! ## Bridge between barycentric divided differences and weighted exponential laws -/

namespace SharpL1.Analysis

open SharpL1.Probability
open MeasureTheory

private theorem pairwise_gt_nodup {zs : List ℝ} (h : zs.Pairwise (· > ·)) : zs.Nodup := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    rw [List.pairwise_cons] at h
    rw [List.nodup_cons]
    refine ⟨?_, ih h.2⟩
    intro hz
    exact (lt_irrefl z) (h.1 z hz)

theorem toFinset_erase_head_of_nodup {zs : List ℝ} (hn : zs.Nodup) (hne : zs ≠ []) :
    zs.toFinset.erase (zs.head hne) = zs.tail.toFinset := by
  cases zs with
  | nil => contradiction
  | cons z zs =>
    simp only [List.head_cons, List.tail_cons, List.toFinset_cons]
    apply Finset.erase_insert
    intro hz
    have hz' : z ∈ zs := List.mem_toFinset.mp hz
    exact (List.nodup_cons.mp hn).1 hz'

theorem toFinset_erase_last_of_nodup {zs : List ℝ} (hn : zs.Nodup) (hne : zs ≠ []) :
    zs.toFinset.erase (zs.getLast hne) = zs.dropLast.toFinset := by
  have hsplit := List.dropLast_append_getLast hne
  have hnd : (zs.dropLast ++ [zs.getLast hne]).Nodup := by
    rw [hsplit]
    exact hn
  have hdisj := (List.nodup_append'.mp hnd).2.2
  have hnot : zs.getLast hne ∉ zs.dropLast := by
    intro ha
    exact hdisj ha (by simp)
  have hfin : zs.toFinset = (zs.dropLast ++ [zs.getLast hne]).toFinset :=
    congrArg List.toFinset hsplit.symm
  rw [hfin, List.toFinset_append, Finset.erase_union_distrib]
  simp [List.mem_toFinset, hnot]

/-- Convolution of independent exponential laws is invariant under permutation of weights. -/
theorem weightedExpSum_perm {cs ds : List ℝ} (h : cs.Perm ds) :
    weightedExpSum cs = weightedExpSum ds := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    change weightedExp x ∗ weightedExpSum _ = weightedExp x ∗ weightedExpSum _
    rw [ih]
  | swap x y l =>
    change weightedExp y ∗ (weightedExp x ∗ weightedExpSum l) =
      weightedExp x ∗ (weightedExp y ∗ weightedExpSum l)
    rw [← Measure.conv_assoc, Measure.conv_comm (weightedExp y) (weightedExp x), Measure.conv_assoc]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The closed zero-threshold CDF is invariant under permutation of weights. -/
theorem weightedCdfZero_perm {cs ds : List ℝ} (h : cs.Perm ds) :
    weightedCdfZero cs = weightedCdfZero ds := by
  simp only [weightedCdfZero, weightedExpSum_perm h]

/-- The closed zero CDF of the weighted exponential sum is the barycentric
divided difference of the truncated power of one lower order. The node list
is written in strict descending order, so its first and last coefficients
are exactly the negative and positive endpoints in the mixed recurrence. -/
theorem weightedCdfZero_eq_barycentric_truncatedPower (zs : List ℝ)
    (hdesc : zs.Pairwise (· > ·)) (hne : zs ≠ []) (t : ℝ) :
    weightedCdfZero (zs.map fun z => t - z) =
      barycentricDividedDifferenceOn zs.toFinset id
        (fun z => truncatedPower (zs.length - 1) t z) := by
  classical
  have main : ∀ n : ℕ, ∀ zs : List ℝ, zs.length = n →
      zs.Pairwise (· > ·) → zs ≠ [] →
      weightedCdfZero (zs.map fun z => t - z) =
        barycentricDividedDifferenceOn zs.toFinset id
          (fun z => truncatedPower (zs.length - 1) t z) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro zs hlen hdesc hne
      cases zs with
      | nil => contradiction
      | cons b tail =>
        by_cases htail : tail = []
        · subst tail
          by_cases ht : t ≤ b
          · have hc : ∀ c ∈ [t - b], c ≤ 0 := by simp [ht]
            simp only [List.map_cons, List.map_nil]
            rw [weightedCdfZero_nonpos _ hc]
            simp [barycentricDividedDifferenceOn, truncatedPower, ht]
          · have hbt : b < t := lt_of_not_ge ht
            have hc : ∀ c ∈ [t - b], 0 ≤ c := by simp [le_of_lt hbt]
            have hp : ∃ c ∈ [t - b], 0 < c := ⟨t - b, by simp, by linarith⟩
            simp only [List.map_cons, List.map_nil]
            rw [weightedCdfZero_nonneg_pos _ hc hp]
            simp [barycentricDividedDifferenceOn, truncatedPower, not_le_of_gt hbt]
        · let a : ℝ := tail.getLast htail
          let middle : List ℝ := tail.dropLast
          have hsplit : middle ++ [a] = tail := List.dropLast_append_getLast htail
          have htailPair : tail.Pairwise (· > ·) := (List.pairwise_cons.mp hdesc).2
          have hhead : ∀ z ∈ tail, b > z := (List.pairwise_cons.mp hdesc).1
          have hba : b > a := hhead a (List.getLast_mem htail)
          have hsmall₁ : (b :: middle).Pairwise (· > ·) := by
            apply List.pairwise_cons.mpr
            constructor
            · intro z hz
              exact hhead z (List.dropLast_subset _ hz)
            · have hp := htailPair
              rw [← hsplit, List.pairwise_append] at hp
              simpa [middle] using hp.1
          have hsmall₂ : (middle ++ [a]).Pairwise (· > ·) := by
            rw [hsplit]
            exact htailPair
          have hfull : (b :: (middle ++ [a])).Pairwise (· > ·) := by
            rw [hsplit]
            exact hdesc
          have hnd : (b :: (middle ++ [a])).Nodup := pairwise_gt_nodup hfull
          let s : Finset ℝ := (b :: (middle ++ [a])).toFinset
          have hsEraseA : s.erase a = (b :: middle).toFinset := by
            have h := toFinset_erase_last_of_nodup hnd (by simp)
            have hd : (b :: (middle ++ [a])).dropLast = b :: middle := by
              rw [← List.cons_append, List.dropLast_concat]
            rw [hd] at h
            simpa [s] using h
          have hsEraseB : s.erase b = (middle ++ [a]).toFinset := by
            have h := toFinset_erase_head_of_nodup hnd (by simp)
            simpa [s] using h
          have hcard : s.card = (b :: (middle ++ [a])).length :=
            List.toFinset_card_of_nodup hnd
          have hnonempty : s.Nonempty := ⟨b, by simp [s]⟩
          have hinj : Set.InjOn id (s : Set ℝ) := fun _ _ _ _ hxy => hxy
          have htail_len : tail.length = middle.length + 1 := by
            simpa using congrArg List.length hsplit.symm
          by_cases hleft : t ≤ a
          · have hnodes : ∀ z ∈ b :: (middle ++ [a]), t ≤ z := by
              intro z hz
              rcases List.mem_cons.mp hz with rfl | hz
              · exact hleft.trans hba.le
              · rcases List.mem_append.mp hz with hm | ha
                · have hza : z > a := by
                    have h := hsmall₂.rel_dropLast_getLast (by simpa [middle] using hm)
                    simpa [a] using h
                  exact hleft.trans hza.le
                · simp only [List.mem_singleton] at ha
                  subst z
                  exact hleft
            have hc : ∀ c ∈ (b :: (middle ++ [a])).map (fun z => t - z), c ≤ 0 := by
              intro c hc
              rcases List.mem_map.mp hc with ⟨z, hz, rfl⟩
              linarith [hnodes z hz]
            have hcdf := weightedCdfZero_nonpos _ hc
            have hdd := barycentric_truncatedPower_nonneg_side
              (s := s) (a := id) hinj hnonempty t (fun z hz => hnodes z (List.mem_toFinset.mp hz))
            rw [← hsplit]
            change weightedCdfZero ((b :: (middle ++ [a])).map (fun z => t - z)) =
              barycentricDividedDifferenceOn s id
                (fun z => truncatedPower ((b :: (middle ++ [a])).length - 1) t z)
            rw [hcdf, ← hcard]
            exact hdd.symm
          · by_cases hright : b ≤ t
            · have hnodes : ∀ z ∈ b :: (middle ++ [a]), z ≤ t := by
                intro z hz
                rcases List.mem_cons.mp hz with rfl | hz
                · exact hright
                · rcases List.mem_append.mp hz with hm | ha
                  · have hzb : b > z := hhead z (by rw [← hsplit]; exact List.mem_append_left [a] hm)
                    exact hzb.le.trans hright
                  · simp only [List.mem_singleton] at ha
                    subst z
                    exact hba.le.trans hright
              have hc : ∀ c ∈ (b :: (middle ++ [a])).map (fun z => t - z), 0 ≤ c := by
                intro c hc
                rcases List.mem_map.mp hc with ⟨z, hz, rfl⟩
                linarith [hnodes z hz]
              have hp : ∃ c ∈ (b :: (middle ++ [a])).map (fun z => t - z), 0 < c := by
                refine ⟨t - a, ?_, ?_⟩
                · simp
                · have : a < t := lt_of_lt_of_le hba hright
                  linarith
              have hcdf := weightedCdfZero_nonneg_pos _ hc hp
              have hlenfull : (b :: (middle ++ [a])).length = middle.length + 2 := by simp
              have hm : 0 < s.card - 1 := by rw [hcard, hlenfull]; omega
              have hdd := barycentric_truncatedPower_nonpos_side
                s id hm t (fun z hz => hnodes z (List.mem_toFinset.mp hz))
              rw [← hsplit]
              change weightedCdfZero ((b :: (middle ++ [a])).map (fun z => t - z)) =
                barycentricDividedDifferenceOn s id
                  (fun z => truncatedPower ((b :: (middle ++ [a])).length - 1) t z)
              rw [hcdf, ← hcard]
              exact hdd.symm
            · have hmix₁ : t - b < 0 := by linarith
              have hmix₂ : 0 < t - a := by linarith [lt_of_not_ge hleft]
              have hcdf := weightedCdfZero_mixed hmix₁ hmix₂ (middle.map fun z => t - z)
              have hdd := barycentric_truncatedPower_erase_pair
                (s := s) (a := id) hinj (l := a) (h := b) (by simp [s]) (by simp [s]) hba middle.length t
              have hrec₁ := ih (b :: middle).length (by simp [← hlen, htail_len])
                (b :: middle) rfl hsmall₁ (by simp)
              have hrec₂ := ih (middle ++ [a]).length (by simp [← hlen, htail_len])
                (middle ++ [a]) rfl hsmall₂ (by simp)
              rw [← hsplit]
              change weightedCdfZero ((b :: (middle ++ [a])).map (fun z => t - z)) =
                barycentricDividedDifferenceOn s id
                  (fun z => truncatedPower ((b :: (middle ++ [a])).length - 1) t z)
              simp only [List.map_cons, List.map_append, List.map_nil] at hrec₁ hrec₂ ⊢
              rw [hcdf]
              rw [hsEraseA, hsEraseB] at hdd
              have hlen₁ : (b :: middle).length - 1 = middle.length := by simp
              have hlen₂ : (middle ++ [a]).length - 1 = middle.length := by simp
              have hlen₃ : (b :: (middle ++ [a])).length - 1 = middle.length + 1 := by simp
              rw [hlen₁] at hrec₁
              rw [hlen₂] at hrec₂
              simp only [id_eq] at hdd
              rw [hlen₃, hdd, ← hrec₁, ← hrec₂]
              simp only [sub_eq_add_neg]
              ring
  exact main zs.length zs rfl hdesc hne

/-- Reindexing a barycentric divided difference along an injective node map. -/
theorem barycentricDividedDifferenceOn_image {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {a : ι → ℝ} (hinj : Set.InjOn a s) (f : ℝ → ℝ) :
    barycentricDividedDifferenceOn s a (fun i => f (a i)) =
      barycentricDividedDifferenceOn (s.image a) id f := by
  classical
  unfold barycentricDividedDifferenceOn
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 1
  congr 1
  have himg : (s.image a).erase (a i) = (s.erase i).image a := by
    ext y
    simp only [Finset.mem_erase, Finset.mem_image]
    constructor
    · rintro ⟨hyne, ⟨j, hj, rfl⟩⟩
      exact ⟨j, ⟨fun hji => hyne (congrArg a hji), hj⟩, rfl⟩
    · rintro ⟨j, ⟨hji, hj⟩, rfl⟩
      exact ⟨fun h => hji (hinj hj hi h), ⟨j, hj, rfl⟩⟩
  rw [himg, Finset.prod_image (hinj.mono (Finset.erase_subset i s))]
  rfl

/-- Permutation-invariant version for any nonempty `Nodup` list of real nodes. -/
theorem weightedCdfZero_eq_barycentric_truncatedPower_of_nodup (zs : List ℝ)
    (hnd : zs.Nodup) (hne : zs ≠ []) (t : ℝ) :
    weightedCdfZero (zs.map fun z => t - z) =
      barycentricDividedDifferenceOn zs.toFinset id
        (fun z => truncatedPower (zs.length - 1) t z) := by
  let desc : List ℝ := zs.toFinset.sort (· ≥ ·)
  have hperm_nodes : zs.Perm desc := by
    refine (List.perm_ext_iff_of_nodup hnd (zs.toFinset.sort_nodup _)).2 fun x => ?_
    simp [Finset.mem_sort, List.mem_toFinset]
  have hperm_map : (zs.map fun z => t - z).Perm (desc.map fun z => t - z) :=
    hperm_nodes.map _
  have hdesc_ge : desc.Pairwise (· ≥ ·) := zs.toFinset.pairwise_sort _
  have hdesc_nd : desc.Nodup := zs.toFinset.sort_nodup _
  have hdesc_gt : desc.Pairwise (· > ·) := by
    rw [List.pairwise_iff_get] at hdesc_ge ⊢
    intro i j hij
    have hge : desc.get i ≥ desc.get j := hdesc_ge i j hij
    have hne_ij : desc.get i ≠ desc.get j := hdesc_nd.get_inj_iff.ne.mpr hij.ne
    exact lt_of_le_of_ne hge hne_ij.symm
  have hdesc_ne : desc ≠ [] := by
    intro h
    rw [h] at hperm_nodes
    exact hne hperm_nodes.symm.nil_eq.symm
  have htoFinset : desc.toFinset = zs.toFinset := by
    ext x
    simp [List.mem_toFinset, hperm_nodes.mem_iff]
  have hlen : desc.length = zs.length := hperm_nodes.length_eq.symm
  rw [weightedCdfZero_perm hperm_map,
    weightedCdfZero_eq_barycentric_truncatedPower desc hdesc_gt hdesc_ne t,
    htoFinset, hlen]

/-- Sign expectation of the weighted exponential sum on any nonempty `Nodup` node list
having at least one node different from `t`. -/
theorem lawSignMean_weightedExpSum_eq_barycentric_truncatedPower (zs : List ℝ)
    (hnd : zs.Nodup) (hne : zs ≠ []) (t : ℝ) (hnz : ∃ z ∈ zs, z ≠ t) :
    lawSignMean (weightedExpSum (zs.map fun z => t - z)) =
      1 - 2 * barycentricDividedDifferenceOn zs.toFinset id
        (fun z => truncatedPower (zs.length - 1) t z) := by
  have hnz' : ∃ c ∈ zs.map (fun z => t - z), c ≠ 0 := by
    rcases hnz with ⟨z, hz, hzt⟩
    exact ⟨t - z, List.mem_map.mpr ⟨z, hz, rfl⟩, sub_ne_zero.mpr hzt.symm⟩
  rw [weightedExpSum_signMean hnz',
    weightedCdfZero_eq_barycentric_truncatedPower_of_nodup zs hnd hne t]

/-- `Hcomp` identity bridging `barycentricDividedDifferenceOn` of the augmented nodal
weight polynomial to the four weighted-exponential sign expectations `G(Q_t^0 + (t+1)e_+)`,
`G(Q_t^0 + (t-1)e_-)`, `G(Q_t)`, and `G(Q_t^0)`. -/
theorem lawSignMean_Hcomp_of_nodes {n : ℕ} (hn : 1 ≤ n)
    (u : Fin (n + 1) → ℝ) (hu_mono : StrictMono u) (hu_bd : ∀ j, u j ∈ Set.Ioo (-1 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    let coreList : List ℝ := List.ofFn u
    let plusList : List ℝ := (-1 : ℝ) :: coreList
    let minusList : List ℝ := (1 : ℝ) :: coreList
    let fullList : List ℝ := (-1 : ℝ) :: (1 : ℝ) :: coreList
    let s : Finset ℝ := fullList.toFinset
    1 - barycentricDividedDifferenceOn s id (fun y =>
        ((n : ℝ) * (1 - t ^ 2) - 2 * ((n : ℝ) - 1) * t * (y - t) + 2 * (y - t) ^ 2) *
          truncatedPower n t y) =
      (lawSignMean (weightedExpSum (plusList.map fun z => t - z)) +
        lawSignMean (weightedExpSum (minusList.map fun z => t - z))) / 2 +
      (n : ℝ) / 2 *
        (lawSignMean (weightedExpSum (fullList.map fun z => t - z)) -
          lawSignMean (weightedExpSum (coreList.map fun z => t - z))) := by
  classical
  intro coreList plusList minusList fullList s
  have hcore_nd : coreList.Nodup := by
    rw [List.nodup_ofFn]
    exact hu_mono.injective
  have hneg1_not : (-1 : ℝ) ∉ coreList := by
    simp only [coreList, List.mem_ofFn, not_exists]
    intro j hj
    have := (hu_bd j).1
    linarith
  have hpos1_not : (1 : ℝ) ∉ coreList := by
    simp only [coreList, List.mem_ofFn, not_exists]
    intro j hj
    have := (hu_bd j).2
    linarith
  have hplus_nd : plusList.Nodup := List.nodup_cons.mpr ⟨hneg1_not, hcore_nd⟩
  have hminus_nd : minusList.Nodup := List.nodup_cons.mpr ⟨hpos1_not, hcore_nd⟩
  have hfull_nd : fullList.Nodup := by
    refine List.nodup_cons.mpr ⟨?_, hminus_nd⟩
    simp only [List.mem_cons]
    rintro (h | h)
    · norm_num at h
    · exact hneg1_not h
  have hcore_ne : coreList ≠ [] := by
    simp [coreList]
  have hcore_nz : ∃ z ∈ coreList, z ≠ t := by
    have h01 : u 0 < u ⟨1, by omega⟩ := hu_mono (by simp [Fin.lt_def])
    by_cases h0 : u 0 = t
    · exact ⟨u ⟨1, by omega⟩, List.mem_ofFn.mpr ⟨⟨1, by omega⟩, rfl⟩, by linarith⟩
    · exact ⟨u 0, List.mem_ofFn.mpr ⟨0, rfl⟩, h0⟩
  have hplus_nz : ∃ z ∈ plusList, z ≠ t :=
    ⟨-1, by simp [plusList], by linarith [ht.1]⟩
  have hminus_nz : ∃ z ∈ minusList, z ≠ t :=
    ⟨1, by simp [minusList], by linarith [ht.2]⟩
  have hfull_nz : ∃ z ∈ fullList, z ≠ t :=
    ⟨-1, by simp [fullList], by linarith [ht.1]⟩
  have hGcore := lawSignMean_weightedExpSum_eq_barycentric_truncatedPower coreList hcore_nd hcore_ne t hcore_nz
  have hGplus := lawSignMean_weightedExpSum_eq_barycentric_truncatedPower plusList hplus_nd (by simp [plusList]) t hplus_nz
  have hGminus := lawSignMean_weightedExpSum_eq_barycentric_truncatedPower minusList hminus_nd (by simp [minusList]) t hminus_nz
  have hGfull := lawSignMean_weightedExpSum_eq_barycentric_truncatedPower fullList hfull_nd (by simp [fullList]) t hfull_nz
  have hlen_core : coreList.length - 1 = n := by simp [coreList]
  have hlen_plus : plusList.length - 1 = n + 1 := by simp [plusList, coreList]
  have hlen_minus : minusList.length - 1 = n + 1 := by simp [minusList, coreList]
  have hlen_full : fullList.length - 1 = n + 2 := by simp [fullList, coreList]
  have hs_erase_pos : s.erase (1 : ℝ) = plusList.toFinset := by
    ext x
    simp only [s, fullList, plusList, List.toFinset_cons, Finset.mem_erase, Finset.mem_insert,
      List.mem_toFinset]
    constructor
    · rintro ⟨hx1, rfl | rfl | hx⟩
      · left; rfl
      · exact (hx1 rfl).elim
      · right; exact hx
    · rintro (rfl | hx)
      · exact ⟨by norm_num, Or.inl rfl⟩
      · exact ⟨fun h => hpos1_not (h ▸ hx), Or.inr (Or.inr hx)⟩
  have hs_erase_neg : s.erase (-1 : ℝ) = minusList.toFinset := by
    ext x
    simp only [s, fullList, minusList, List.toFinset_cons, Finset.mem_erase, Finset.mem_insert,
      List.mem_toFinset]
    constructor
    · rintro ⟨hx1, rfl | rfl | hx⟩
      · exact (hx1 rfl).elim
      · left; rfl
      · right; exact hx
    · rintro (rfl | hx)
      · exact ⟨by norm_num, Or.inr (Or.inl rfl)⟩
      · exact ⟨fun h => hneg1_not (h ▸ hx), Or.inr (Or.inr hx)⟩
  have hs_erase_both : (s.erase (-1 : ℝ)).erase (1 : ℝ) = coreList.toFinset := by
    rw [hs_erase_neg]
    exact toFinset_erase_head_of_nodup hminus_nd (by simp [minusList])
  rw [hGplus, hGminus, hGfull, hGcore, hlen_plus, hlen_minus, hlen_full, hlen_core,
    ← hs_erase_pos, ← hs_erase_neg, ← hs_erase_both]
  have hinj : Set.InjOn (id : ℝ → ℝ) s := fun _ _ _ _ h => h
  have h_l : (-1 : ℝ) ∈ s := by simp [s, fullList]
  have h_h : (1 : ℝ) ∈ s := by simp [s, fullList]
  simpa using barycentric_Hcomp hinj h_l h_h rfl rfl n t

end SharpL1.Analysis
