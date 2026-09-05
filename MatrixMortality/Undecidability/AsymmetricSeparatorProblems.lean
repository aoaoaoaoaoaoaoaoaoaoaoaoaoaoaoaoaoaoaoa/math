import MatrixMortality.AsymmetricSeparatorEffectivity
import MatrixMortality.Undecidability.PairAlphabet

/-!
# Canonical M₈(2) instances

The effective asymmetric pair is relabelled from its cut/transition alphabet to `Fin 2`.
All 128 integer entries are primitive recursive in the source body.
-/

namespace MatrixMortality.Undecidability

/-- Two labelled `8 × 8` integer matrices emitted by the asymmetric construction. -/
noncomputable def nearyMortality82 (β : Nat) (body : List TagLetter) : MortalityProblem 8 2 :=
  fun label => AsymmetricSeparatorRealization.effectiveIntegralGenerator β body
    (changedSeparatorLabelOfFin label)

theorem nearyMortality82_primrec (β : Nat) : Primrec (nearyMortality82 β) :=
  MortalityProblem.primrec _ fun label row column =>
    AsymmetricSeparatorRealization.effectiveIntegralGenerator_entry_primrec β
      (changedSeparatorLabelOfFin label) row column

/-- The encoded integer instance has exactly the source's unrestricted halting predicate. -/
theorem nearyMortality82_mortal_iff_tagHaltsFrom (β : Nat) (body : List TagLetter)
    (width : 2 < β) (body_long : β - 1 ≤ body.length)
    (body_divisible : β - 1 ∣ body.length) (starts_bcb : body.take 3 = [.b, .c, .b]) :
    (nearyMortality82 β body).Mortal ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  change IsMortal (AsymmetricSeparatorRealization.effectiveIntegralGenerator β body ∘
    changedSeparatorFinEquiv) ↔ _
  rw [isMortal_comp_equiv]
  exact AsymmetricSeparatorRealization.effectiveIntegralGenerator_mortal_iff_tagHaltsFrom
    β body width body_long body_divisible starts_bcb

end MatrixMortality.Undecidability
