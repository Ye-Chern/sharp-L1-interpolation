module

public import SharpL1.Chebyshev
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Polynomial

public section

namespace SharpL1

open Polynomial

/-- Ordered, pairwise separated open brackets with a strict sign change
contain the complete real-root multiset of a polynomial of matching degree. -/
theorem roots_of_ordered_sign_change (p : ℝ[X]) (d : ℕ)
    (lo hi : Fin d → ℝ)
    (hdegree : p.natDegree = d) (hp : p ≠ 0)
    (hwidth : ∀ i, lo i < hi i)
    (hseparated : ∀ i j, i < j → hi j < lo i)
    (hsign : ∀ i, p.eval (lo i) * p.eval (hi i) < 0) :
    ∃ r : Fin d → ℝ,
      (∀ i, lo i < r i ∧ r i < hi i ∧ p.eval (r i) = 0) ∧
      StrictAnti r ∧
      p.roots = (Finset.univ.image r).val := by
  have hex : ∀ i : Fin d, ∃ x, lo i < x ∧ x < hi i ∧ p.eval x = 0 := by
    intro i
    have hcont : ContinuousOn (fun x : ℝ => p.eval x) (Set.Icc (lo i) (hi i)) :=
      p.continuous.continuousOn
    have hsign' := hsign i
    rcases mul_neg_iff.mp hsign' with ⟨hl, hu⟩ | ⟨hl, hu⟩
    · have hz : (0 : ℝ) ∈ Set.Ioo (p.eval (hi i)) (p.eval (lo i)) := ⟨hu, hl⟩
      rcases intermediate_value_Ioo' (hwidth i).le hcont hz with ⟨x, hx, hfx⟩
      exact ⟨x, hx.1, hx.2, hfx⟩
    · have hz : (0 : ℝ) ∈ Set.Ioo (p.eval (lo i)) (p.eval (hi i)) := ⟨hl, hu⟩
      rcases intermediate_value_Ioo (hwidth i).le hcont hz with ⟨x, hx, hfx⟩
      exact ⟨x, hx.1, hx.2, hfx⟩
  let r : Fin d → ℝ := fun i => Classical.choose (hex i)
  have hr (i : Fin d) : lo i < r i ∧ r i < hi i ∧ p.eval (r i) = 0 :=
    Classical.choose_spec (hex i)
  have hanti : StrictAnti r := by
    intro i j hij
    calc
      r j < hi j := (hr j).2.1
      _ < lo i := hseparated i j hij
      _ < r i := (hr i).1
  let S : Finset ℝ := Finset.univ.image r
  have hS : ∀ x ∈ S, p.eval x = 0 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
    exact (hr i).2.2
  have hcard : p.natDegree ≤ S.card := by
    rw [hdegree]
    dsimp [S]
    rw [Finset.card_image_of_injective Finset.univ hanti.injective]
    simp
  have roots_eq := roots_eq_of_natDegree_le_card_of_ne_zero hS hcard hp
  exact ⟨r, hr, hanti, roots_eq⟩

/-- A family of integer certificate brackets, at positive common scale, gives
the full root multiset of the corresponding node polynomial. -/
theorem certified_node_roots (s t : ℤ) (hs : 0 < s) (k : ℕ)
    (lo hi : Fin (k + 2) → ℤ)
    (hwidth : ∀ i, lo i < hi i)
    (hseparated : ∀ i j, i < j → hi j < lo i)
    (hsign : ∀ i,
      scaledNodeEval s t (lo i) k * scaledNodeEval s t (hi i) k < 0) :
    ∃ roots : Fin (k + 2) → ℝ,
      (∀ i, (lo i : ℝ) / s < roots i ∧ roots i < (hi i : ℝ) / s ∧
        (nodePolynomial k ((t : ℝ) / s)).eval (roots i) = 0) ∧
      StrictAnti roots ∧
      (nodePolynomial k ((t : ℝ) / s)).roots = (Finset.univ.image roots).val := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hwR : ∀ i, (lo i : ℝ) / s < (hi i : ℝ) / s := by
    intro i
    rw [div_lt_div_iff_of_pos_right hsR]
    exact_mod_cast hwidth i
  have hsRsep : ∀ i j, i < j → (hi j : ℝ) / s < (lo i : ℝ) / s := by
    intro i j hij
    rw [div_lt_div_iff_of_pos_right hsR]
    exact_mod_cast hseparated i j hij
  have hsignR : ∀ i,
      (nodePolynomial k ((t : ℝ) / s)).eval ((lo i : ℝ) / s) *
        (nodePolynomial k ((t : ℝ) / s)).eval ((hi i : ℝ) / s) < 0 := by
    intro i
    exact scaledNodeEval_sign_change s t (lo i) (hi i) hs k (hsign i)
  obtain ⟨roots, hroots, hanti, hmultiset⟩ :=
    roots_of_ordered_sign_change (nodePolynomial k ((t : ℝ) / s)) (k + 2)
      (fun i => (lo i : ℝ) / s) (fun i => (hi i : ℝ) / s)
      (natDegree_nodePolynomial k _) (nodePolynomial_ne_zero k _)
      hwR hsRsep hsignR
  exact ⟨roots, hroots, hanti, hmultiset⟩

end SharpL1
