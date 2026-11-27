module

public import SharpL1.RootBrackets
public import Lean.Elab.Tactic.Omega

public section

/-! ## Per-row root certificates -/

namespace SharpL1.Certificate

/-- Brackets are enclosed in the scaled open interval and have an integer sign change. -/
@[expose] def ValidBracket (s t : ℤ) (k : ℕ) (bracket : ℤ × ℤ) : Prop :=
  -s < bracket.1 ∧ bracket.1 < bracket.2 ∧ bracket.2 < s ∧
    scaledNodeEval s t bracket.1 k * scaledNodeEval s t bracket.2 k < 0

@[expose] instance (s t : ℤ) (k : ℕ) (bracket : ℤ × ℤ) : Decidable (ValidBracket s t k bracket) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Check one certificate row: exact cardinality, strict containment in the
scaled open interval, ordered disjoint brackets, and integer sign changes. -/
@[expose] def checkRootRow (s t : ℤ) (k : ℕ) (brackets : List (ℤ × ℤ)) : Bool :=
  decide (0 < s ∧ brackets.length = k + 2) &&
    brackets.all (fun bracket => decide (ValidBracket s t k bracket)) &&
    decide (brackets.Pairwise (fun a b => b.2 < a.1))

/-- At a valid list length this is just the indexed bracket. -/
@[expose] def rowBracket (brackets : List (ℤ × ℤ)) (i : ℕ) : ℤ × ℤ :=
  brackets.getD i (0, 0)

theorem checkRootRow_sound (s t : ℤ) (k : ℕ) (brackets : List (ℤ × ℤ))
    (hcheck : checkRootRow s t k brackets = true) :
    ∃ roots : Fin (k + 2) → ℝ,
      (∀ i, ((rowBracket brackets i.val).1 : ℝ) / s < roots i ∧
        roots i < ((rowBracket brackets i.val).2 : ℝ) / s ∧
        (nodePolynomial k ((t : ℝ) / s)).eval (roots i) = 0) ∧
      StrictAnti roots ∧
      (nodePolynomial k ((t : ℝ) / s)).roots = (Finset.univ.image roots).val := by
  simp only [checkRootRow, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hcheck
  obtain ⟨⟨⟨hs, hlen⟩, hvalid⟩, hseparated⟩ := hcheck
  have hind (i : Fin (k + 2)) : i.val < brackets.length := by rw [hlen]; exact i.isLt
  have hget (i : Fin (k + 2)) : rowBracket brackets i.val = brackets[i.val]'(hind i) := by
    simp [rowBracket, hind i]
  have hentry (i : Fin (k + 2)) : ValidBracket s t k (rowBracket brackets i.val) := by
    rw [hget i]
    exact hvalid _ (List.getElem_mem (hind i))
  have hsep (i j : Fin (k + 2)) (hij : i < j) :
      (rowBracket brackets j.val).2 < (rowBracket brackets i.val).1 := by
    rw [hget i, hget j]
    exact List.pairwise_iff_getElem.mp hseparated i.val j.val (hind i) (hind j) hij
  exact certified_node_roots s t hs k
    (fun i => (rowBracket brackets i.val).1) (fun i => (rowBracket brackets i.val).2)
    (fun i => (hentry i).2.1) hsep (fun i => (hentry i).2.2.2)

end SharpL1.Certificate
