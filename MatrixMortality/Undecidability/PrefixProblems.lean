import MatrixMortality.PrefixMortality
import MatrixMortality.Undecidability.Problems

/-!
# Canonical two-matrix mortality instances

This file transports the semantic binary alphabet of the ten-state prefix compiler to `Fin 2`,
the transparent carrier of the encoded `M₁₀(2)` decision problem, then pads the construction
without changing its nonempty-word zero language.
-/

namespace MatrixMortality
namespace Undecidability

/-- The two exact `10 × 10` integer matrices emitted by one restricted tag source. -/
def nearyMortality102 (β : Nat) (body : List TagLetter) : Mortality102 :=
  fun label => restrictedPrefixGenerator β body (finTwoEquiv label)

theorem nearyMortality102_mortal_iff_tagHaltsFrom (β : Nat)
    (body : List TagLetter) (β_large : 2 < β) (body_long : β - 1 ≤ body.length)
    (body_divisible : β - 1 ∣ body.length) :
    (nearyMortality102 β body).Mortal ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  rw [show (nearyMortality102 β body).Mortal =
      IsMortal (restrictedPrefixGenerator β body ∘ finTwoEquiv) by rfl]
  rw [isMortal_comp_equiv (restrictedPrefixGenerator β body) finTwoEquiv]
  exact restrictedPrefixGenerator_mortal_iff_tagHaltsFrom β body β_large body_long
    body_divisible

/-- The ten-state pair padded by an identically zero block of dimension `extra`. -/
def nearyMortality10Plus (extra β : Nat) (body : List TagLetter) :
    MortalityProblem (10 + extra) 2 :=
  fun label =>
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (zeroPad (κ := Fin extra) (nearyMortality102 β body label))

theorem nearyMortality10Plus_mortal_iff_tagHaltsFrom (extra β : Nat)
    (body : List TagLetter) (β_large : 2 < β) (body_long : β - 1 ≤ body.length)
    (body_divisible : β - 1 ∣ body.length) :
    (nearyMortality10Plus extra β body).Mortal ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  change IsMortal
      (Matrix.reindex finSumFinEquiv finSumFinEquiv ∘
        (zeroPad (κ := Fin extra) ∘ nearyMortality102 β body)) ↔ _
  rw [isMortal_reindex_iff, isMortal_zeroPad_iff]
  exact nearyMortality102_mortal_iff_tagHaltsFrom β body β_large body_long body_divisible

end Undecidability

namespace NearyArithmeticEnvelope

/-- The exact two-matrix ten-state instance emitted by an arithmetic-envelope source. -/
def mortality102 (source : NearyArithmeticEnvelope) : Undecidability.Mortality102 :=
  Undecidability.nearyMortality102 source.β source.body

theorem mortality102_iff_halts (source : NearyArithmeticEnvelope) :
    source.mortality102.Mortal ↔
      TagHaltsFrom source.β (tagOutput source.body) source.initial := by
  exact Undecidability.nearyMortality102_mortal_iff_tagHaltsFrom source.β source.body
    source.beta_large source.body_long source.body_divisible

/-- The two-matrix instance in every dimension `10 + extra`. -/
def mortality10Plus (source : NearyArithmeticEnvelope) (extra : Nat) :
    Undecidability.MortalityProblem (10 + extra) 2 :=
  Undecidability.nearyMortality10Plus extra source.β source.body

theorem mortality10Plus_iff_halts (source : NearyArithmeticEnvelope) (extra : Nat) :
    (source.mortality10Plus extra).Mortal ↔
      TagHaltsFrom source.β (tagOutput source.body) source.initial := by
  exact Undecidability.nearyMortality10Plus_mortal_iff_tagHaltsFrom extra source.β source.body
    source.beta_large source.body_long source.body_divisible

end NearyArithmeticEnvelope
end MatrixMortality
