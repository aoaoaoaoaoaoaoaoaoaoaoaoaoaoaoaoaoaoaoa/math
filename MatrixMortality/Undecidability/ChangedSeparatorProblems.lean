import MatrixMortality.ChangedSeparatorEffectivity
import MatrixMortality.Undecidability.NearyProblems

/-!
# Canonical two-matrix rank-nine mortality instances

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

/-- The rank-nine pair is primitive recursive in the variable source body. -/
theorem nearyMortality92_primrec (β : Nat) :
    Primrec (nearyMortality92 β) := by
  apply MortalityProblem.primrec
  intro label row column
  fin_cases label
  · simpa [nearyMortality92, changedSeparatorLabelOfFin] using
      ChangedSeparatorRealization.effectiveIntegralGenerator_entry_primrec
        β none row column
  · simpa [nearyMortality92, changedSeparatorLabelOfFin] using
      ChangedSeparatorRealization.effectiveIntegralGenerator_entry_primrec
        β (some ()) row column

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

end Undecidability
end MatrixMortality
