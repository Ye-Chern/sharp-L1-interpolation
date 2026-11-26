module

public import SharpL1.JacobiSpectrum
public import Mathlib.Data.Multiset.Sort

public section

/-!
# Ordered Jacobi nodes

The characteristic polynomial of the Jacobi pencil has a finite multiset of
real roots.  This module selects their globally ascending enumeration by sorting
that multiset, without choosing eigenvalue branches or assuming continuity in
the pencil parameter.
-/

namespace SharpL1

theorem sortedNodeRoots_length (k : ℕ) (t : ℝ) :
    ((nodePolynomial k t).roots.sort).length = k + 2 := by
  simp [nodePolynomial_card_roots]

/-- The roots of the node polynomial in globally ascending order. -/
@[expose] noncomputable def orderedNode (k : ℕ) (t : ℝ) (i : Fin (k + 2)) : ℝ :=
  let roots := (nodePolynomial k t).roots.sort
  roots.get (Fin.cast (sortedNodeRoots_length k t).symm i)

/-- The `Fin` enumeration lists exactly the sorted root list. -/
theorem orderedNode_ofFn (k : ℕ) (t : ℝ) :
    List.ofFn (orderedNode k t) = (nodePolynomial k t).roots.sort := by
  let roots := (nodePolynomial k t).roots.sort
  have hlen : roots.length = k + 2 := sortedNodeRoots_length k t
  change List.ofFn (fun i : Fin (k + 2) =>
    roots.get (Fin.cast hlen.symm i)) = roots
  calc
    List.ofFn (fun i : Fin (k + 2) => roots.get (Fin.cast hlen.symm i)) =
        List.ofFn (List.get roots) := (List.ofFn_congr hlen (List.get roots)).symm
    _ = roots := List.ofFn_get roots

/-- The ascending enumeration is strictly increasing, since the Jacobi
characteristic polynomial has simple roots. -/
theorem orderedNode_strictMono (k : ℕ) (t : ℝ) :
    StrictMono (orderedNode k t) := by
  let roots := (nodePolynomial k t).roots.sort
  have hlen : roots.length = k + 2 := sortedNodeRoots_length k t
  have hroots_nodup : (nodePolynomial k t).roots.Nodup := nodePolynomial_roots_nodup k t
  have hnodup : roots.Nodup := by
    have hcoe : Multiset.Nodup (↑roots : Multiset ℝ) := by
      simpa only [roots, Multiset.sort_eq] using hroots_nodup
    exact Multiset.coe_nodup.mp hcoe
  have hsortedLE : roots.SortedLE := by
    rw [List.sortedLE_iff_pairwise]
    simpa only [roots] using
      (Multiset.pairwise_sort (s := (nodePolynomial k t).roots) (r := (· ≤ ·)))
  have hsortedLT : roots.SortedLT := hsortedLE.sortedLT_of_nodup hnodup
  have hget : StrictMono (List.get roots) := hsortedLT.strictMono_get
  intro i j hij
  change roots.get (Fin.cast hlen.symm i) < roots.get (Fin.cast hlen.symm j)
  exact hget ((Fin.cast_lt_cast hlen.symm).2 hij)

/-- Every selected node is a root of the corresponding node polynomial. -/
theorem orderedNode_eval_eq_zero (k : ℕ) (t : ℝ) (i : Fin (k + 2)) :
    (nodePolynomial k t).eval (orderedNode k t i) = 0 := by
  have hmem_sort : orderedNode k t i ∈ (nodePolynomial k t).roots.sort := by
    exact List.get_mem _ _
  have hmem : orderedNode k t i ∈ (nodePolynomial k t).roots := by
    simpa only [Multiset.mem_sort] using hmem_sort
  exact (Polynomial.IsRoot.def).mp
    ((Polynomial.mem_roots (nodePolynomial_ne_zero k t)).mp hmem)

/-- Any strictly ascending enumeration with the same root multiset agrees with
the canonical sorted enumeration. -/
theorem orderedNode_eq_of_strictMono_of_roots (k : ℕ) (t : ℝ)
    (u : Fin (k + 2) → ℝ) (hu : StrictMono u)
    (hroots : (nodePolynomial k t).roots = (Finset.univ.image u).val) :
    orderedNode k t = u := by
  classical
  let roots := (nodePolynomial k t).roots.sort
  have hsortedRoots : roots.SortedLE := by
    rw [List.sortedLE_iff_pairwise]
    simpa only [roots] using
      (Multiset.pairwise_sort (s := (nodePolynomial k t).roots) (r := (· ≤ ·)))
  have hsortedU : (List.ofFn u).SortedLE := hu.sortedLT_ofFn.sortedLE
  have hnodupUniv : Multiset.Nodup (Finset.univ : Finset (Fin (k + 2))).val := by
    exact Finset.univ.2
  have hcoe : (List.ofFn u : Multiset ℝ) = (roots : Multiset ℝ) := by
    calc
      (List.ofFn u : Multiset ℝ) = (Finset.univ.image u).val := by
        rw [Finset.image_val, ← Fin.univ_val_map]
        exact (hnodupUniv.map hu.injective).dedup.symm
      _ = (nodePolynomial k t).roots := hroots.symm
      _ = (roots : Multiset ℝ) := by simp [roots, Multiset.sort_eq]
  have huPerm : List.Perm (List.ofFn u) roots := Multiset.coe_eq_coe.mp hcoe
  have hlist : List.ofFn u = roots :=
    List.Perm.eq_of_sortedLE hsortedU hsortedRoots huPerm
  apply List.ofFn_injective
  rw [orderedNode_ofFn]
  exact hlist.symm

end SharpL1
