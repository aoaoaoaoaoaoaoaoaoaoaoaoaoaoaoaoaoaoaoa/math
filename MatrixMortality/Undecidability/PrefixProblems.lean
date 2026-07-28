import MatrixMortality.PrefixMortality
import MatrixMortality.Undecidability.NearyProblems

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

private theorem prefixOutput_int_entry_primrec (β : Nat) (state : PrefixState)
    (bit : Bool) (row column : Fin 3) :
    Primrec fun body : List TagLetter => prefixOutput β body state bit row column := by
  cases state <;> cases bit
  case root.false =>
    exact
      (Primrec.const (prefixOutput β [] .root false row column)).of_eq fun _body => by
        simp [prefixOutput, prefixEmission, normalizedNearyFamily,
          nearyMortalityFamilyInt, absorbedFamily, separatedGenerator]
  case root.true | one.false | one.true =>
    exact Primrec.const _
  case ten.false =>
    have lowerWord := nearyLower_primrec β (.rule .c)
    have lowerCode := ternaryCode_int_primrec.comp lowerWord
    have lowerScale := ternaryScale_int_primrec.comp lowerWord
    fin_cases row <;> fin_cases column <;>
      simp [prefixOutput, prefixEmission, normalizedNearyFamily_some,
        sidePcpMatrix, Matrix.vecHead, Matrix.vecTail]
    all_goals first | exact Primrec.const _ | exact lowerCode | exact lowerScale
  case ten.true =>
    exact
      (Primrec.const (prefixOutput β [] .ten true row column)).of_eq fun body => by
        simp [prefixOutput, prefixEmission, normalizedNearyFamily_some,
          sidePcpMatrix, nearyLower]
  case eleven.false =>
    exact
      (Primrec.const (prefixOutput β [] .eleven false row column)).of_eq fun body => by
        simp [prefixOutput, prefixEmission, normalizedNearyFamily_some,
          sidePcpMatrix, nearyLower]
  case eleven.true =>
    exact
      (Primrec.const (prefixOutput β [] .eleven true row column)).of_eq fun body => by
        simp [prefixOutput, prefixEmission, normalizedNearyFamily_some,
          sidePcpMatrix, nearyLower]

private theorem restrictedPrefixGenerator_primrec (β : Nat) (bit : Bool)
    (row column : Fin 10) :
    Primrec fun body : List TagLetter =>
      restrictedPrefixGenerator β body bit row column := by
  let state := prefixNext (prefixRepresentative row).1 bit
  let sourceRow := (prefixRepresentative row).2
  have outputZero := prefixOutput_int_entry_primrec β
    (prefixRepresentative row).1 bit sourceRow 0
  have outputOne := prefixOutput_int_entry_primrec β
    (prefixRepresentative row).1 bit sourceRow 1
  have outputTwo := prefixOutput_int_entry_primrec β
    (prefixRepresentative row).1 bit sourceRow 2
  by_cases zero : prefixCoordinate state 0 = column
  · exact outputZero.of_eq fun body => by
      rw [restrictedPrefixGenerator_apply_sparse]
      simp [state, sourceRow, zero]
  · by_cases one : prefixCoordinate state 1 = column
    · exact outputOne.of_eq fun body => by
        rw [restrictedPrefixGenerator_apply_sparse]
        simp [state, sourceRow, zero, one]
    · by_cases two : prefixCoordinate state 2 = column
      · exact outputTwo.of_eq fun body => by
          rw [restrictedPrefixGenerator_apply_sparse]
          simp [state, sourceRow, zero, one, two]
      · exact (Primrec.const 0).of_eq fun body => by
          rw [restrictedPrefixGenerator_apply_sparse]
          simp [state, zero, one, two]

/-- The two-matrix prefix compiler is primitive recursive in its variable body. -/
theorem nearyMortality102_primrec (β : Nat) :
    Primrec (nearyMortality102 β) := by
  apply MortalityProblem.primrec
  intro label row column
  fin_cases label
  · simpa [nearyMortality102, finTwoEquiv] using
      restrictedPrefixGenerator_primrec β false row column
  · simpa [nearyMortality102, finTwoEquiv] using
      restrictedPrefixGenerator_primrec β true row column

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
