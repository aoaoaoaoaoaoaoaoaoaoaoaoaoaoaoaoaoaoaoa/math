import MatrixMortality.ChangedSeparatorEffectivity
import MatrixMortality.Undecidability.NearyProblems

/-!
# Canonical two-matrix nine-dimensional mortality instances

This file relabels the effective changed-separator pair from its semantic `Option Unit`
alphabet to `Fin 2`, the transparent carrier of the encoded `M₉(2)` decision problem.
-/

namespace MatrixMortality
namespace Undecidability

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

/-- The two effective `9 × 9` integer matrices emitted by one restricted tag source. -/
noncomputable def nearyMortality92 (β : Nat) (body : List TagLetter) : Mortality92 :=
  fun label =>
    ChangedSeparatorRealization.effectiveIntegralGenerator β body
      (changedSeparatorLabelOfFin label)

/-- Every entry of the canonical nine-dimensional pair is primitive recursive in the source
body. -/
private theorem nearyMortality92_entry_primrec (β : Nat) (label : Fin 2)
    (row column : Fin 9) :
    Primrec fun body => nearyMortality92 β body label row column := by
  fin_cases label
  · simpa [nearyMortality92, changedSeparatorLabelOfFin] using
      ChangedSeparatorRealization.effectiveIntegralGenerator_entry_primrec
        β none row column
  · simpa [nearyMortality92, changedSeparatorLabelOfFin] using
      ChangedSeparatorRealization.effectiveIntegralGenerator_entry_primrec
        β (some ()) row column

/-- The nine-dimensional pair is primitive recursive in the variable source body. -/
theorem nearyMortality92_primrec (β : Nat) :
    Primrec (nearyMortality92 β) := by
  apply MortalityProblem.primrec
  exact nearyMortality92_entry_primrec β

theorem nearyMortality92_mortal_iff_tagHaltsFrom (β : Nat)
    (body : List TagLetter) (β_large : 2 < β)
    (body_long : β - 1 ≤ body.length)
    (body_divisible : β - 1 ∣ body.length) (b_mem : .b ∈ body) :
    (nearyMortality92 β body).Mortal ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  rw [show (nearyMortality92 β body).Mortal =
      IsMortal
        (ChangedSeparatorRealization.effectiveIntegralGenerator β body ∘
          changedSeparatorLabelOfFin) by rfl]
  change IsMortal
      (ChangedSeparatorRealization.effectiveIntegralGenerator β body ∘
        changedSeparatorFinEquiv) ↔ _
  rw [isMortal_comp_equiv
    (ChangedSeparatorRealization.effectiveIntegralGenerator β body)
    changedSeparatorFinEquiv]
  exact
    ChangedSeparatorRealization.effectiveIntegralGenerator_mortal_iff_tagHaltsFrom
      β body β_large body_long body_divisible b_mem

/-- The effective nine-dimensional pair padded by an identically zero block of dimension
`extra`. -/
noncomputable def nearyMortality9Plus (extra β : Nat) (body : List TagLetter) :
    MortalityProblem (9 + extra) 2 :=
  fun label =>
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (zeroPad (κ := Fin extra) (nearyMortality92 β body label))

@[simp]
private theorem nearyMortality9Plus_inl_inl (extra β : Nat) (body : List TagLetter)
    (label : Fin 2) (row column : Fin 9) :
    nearyMortality9Plus extra β body label
        (Fin.castAdd extra row) (Fin.castAdd extra column) =
      nearyMortality92 β body label row column := by
  simp [nearyMortality9Plus, zeroPad]

@[simp]
private theorem nearyMortality9Plus_inl_inr (extra β : Nat) (body : List TagLetter)
    (label : Fin 2) (row : Fin 9) (column : Fin extra) :
    nearyMortality9Plus extra β body label
        (Fin.castAdd extra row) (Fin.natAdd 9 column) = 0 := by
  simp [nearyMortality9Plus, zeroPad]

@[simp]
private theorem nearyMortality9Plus_inr (extra β : Nat) (body : List TagLetter)
    (label : Fin 2) (row : Fin extra) (column : Fin 9 ⊕ Fin extra) :
    nearyMortality9Plus extra β body label
        (Fin.natAdd 9 row)
        (finSumFinEquiv column) = 0 := by
  cases column <;> simp [nearyMortality9Plus, zeroPad]

/-- Every fixed zero-padded nine-dimensional family remains primitive recursive in its source
body. -/
theorem nearyMortality9Plus_primrec (extra β : Nat) :
    Primrec (nearyMortality9Plus extra β) := by
  apply MortalityProblem.primrec
  intro label row column
  obtain ⟨sumRow, rfl⟩ := finSumFinEquiv.surjective row
  obtain ⟨sumColumn, rfl⟩ := finSumFinEquiv.surjective column
  cases sumRow with
  | inl sourceRow =>
      cases sumColumn with
      | inl sourceColumn =>
          simpa only [finSumFinEquiv_apply_left, nearyMortality9Plus_inl_inl] using
            nearyMortality92_entry_primrec β label sourceRow sourceColumn
      | inr _ =>
          exact (Primrec.const 0).of_eq fun body => by
            simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
              nearyMortality9Plus_inl_inr]
  | inr _ =>
      exact (Primrec.const 0).of_eq fun body => by
        simp only [finSumFinEquiv_apply_right, nearyMortality9Plus_inr]

/-- Every zero-padded nine-dimensional pair is mortal exactly when its source tag instance
halts. -/
theorem nearyMortality9Plus_mortal_iff_tagHaltsFrom (extra β : Nat)
    (body : List TagLetter) (β_large : 2 < β)
    (body_long : β - 1 ≤ body.length)
    (body_divisible : β - 1 ∣ body.length) (b_mem : .b ∈ body) :
    (nearyMortality9Plus extra β body).Mortal ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  change IsMortal
      (Matrix.reindex finSumFinEquiv finSumFinEquiv ∘
        (zeroPad (κ := Fin extra) ∘ (nearyMortality92 β body).matrix)) ↔ _
  rw [isMortal_reindex_iff, isMortal_zeroPad_iff]
  exact nearyMortality92_mortal_iff_tagHaltsFrom β body β_large body_long
    body_divisible b_mem

end Undecidability
end MatrixMortality
