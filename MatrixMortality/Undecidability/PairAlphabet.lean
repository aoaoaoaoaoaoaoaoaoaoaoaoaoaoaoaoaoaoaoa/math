import MatrixMortality.Undecidability.Problems

/-!
# Canonical cut and transition labels

Both return constructions enumerate the cut as zero and the transition as one.
-/

namespace MatrixMortality.Undecidability

/-- Canonical enumeration of the cut and ambient-transition generators. -/
def changedSeparatorLabelOfFin : Fin 2 → Option Unit
  | ⟨0, _⟩ => none
  | ⟨1, _⟩ => some ()

/-- Inverse of `changedSeparatorLabelOfFin`. -/
def finOfChangedSeparatorLabel : Option Unit → Fin 2
  | none => 0
  | some _ => 1

theorem changedSeparatorLabelOfFin_finOfChangedSeparatorLabel
    (label : Option Unit) :
    changedSeparatorLabelOfFin (finOfChangedSeparatorLabel label) = label := by
  cases label with
  | none => rfl
  | some value => cases value; rfl

theorem finOfChangedSeparatorLabel_changedSeparatorLabelOfFin (label : Fin 2) :
    finOfChangedSeparatorLabel (changedSeparatorLabelOfFin label) = label := by
  fin_cases label <;> rfl

/-- Fixed relabelling from the encoded binary alphabet to the semantic pair alphabet. -/
def changedSeparatorFinEquiv : Fin 2 ≃ Option Unit where
  toFun := changedSeparatorLabelOfFin
  invFun := finOfChangedSeparatorLabel
  left_inv := finOfChangedSeparatorLabel_changedSeparatorLabelOfFin
  right_inv := changedSeparatorLabelOfFin_finOfChangedSeparatorLabel

end MatrixMortality.Undecidability
