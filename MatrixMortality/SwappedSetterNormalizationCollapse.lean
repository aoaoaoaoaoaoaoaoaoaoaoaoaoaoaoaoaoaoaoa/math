import MatrixMortality.SwappedSetterEmptyFrontChamber
import MatrixMortality.SwappedSetterDeletionCContraction

set_option autoImplicit false

/-!
# Primitive-normalization collapse

The exact singleton-`D_c` contraction channel and a seed above the terminal ray do not by
themselves support a two-step Farey-height argument. This module gives a finite counterexample
through the canonical `R_c;D_b` block. The seed is an abstract local carrier; no encoded-entry
reachability, `MM-O29` seed, or pole claim is made.
-/

namespace MatrixMortality.SwappedSetterNormalizationCollapse

open SwappedSetterCarrierGap SwappedSetterMultitransfer
  SwappedSetterEmptyFrontChamber SwappedSetterDeletionCContraction

/-- Adjugate numerator of the inverse canonical width-six `R_c;D_b` transition. -/
def canonicalRcDbInverseRawNumerator
    (targetNumerator targetDenominator : ℤ) : ℤ :=
  centeredCoefficient 6 *
      swappedUpperCode 6 [.rule .c, .erase .b] * targetNumerator -
    terminalDiscrepancy 6 *
      (swappedUpperCode 6 [.rule .c, .erase .b] -
        setterMarker 6 * upperPower 6 [.rule .c, .erase .b]) * targetDenominator

/-- Adjugate denominator of the inverse canonical width-six `R_c;D_b` transition. -/
def canonicalRcDbInverseRawDenominator
    (targetNumerator targetDenominator : ℤ) : ℤ :=
  centeredCoefficient 6 *
      swappedLowerCode 6 (canonicalRcDbBody 6) [.rule .c, .erase .b] *
        targetNumerator -
    terminalDiscrepancy 6 *
      swappedLowerCode 6 (canonicalRcDbBody 6) [.rule .c, .erase .b] *
        targetDenominator

/-- The complete local hypothesis bundle defeated by the normalization-collapse witness. -/
def IsNormalizationCollapseWitness
    (seedNumerator seedDenominator numerator denominator
      postNumerator postDenominator inverseContent : Nat)
    (forwardScale : ℤ) : Prop :=
  let body := canonicalRcDbBody 6
  let block : List NearyTile := [.rule .c, .erase .b]
  swappedUpperCode 6 block = 23911928 ∧
    swappedLowerCode 6 body block = 23911568 ∧
    upperPower 6 block = 19683 ∧
    0 < seedDenominator ∧
    0 < inverseContent ∧
    forwardScale ≠ 0 ∧
    (terminalDiscrepancy 6 : ℚ) < (seedNumerator : ℚ) / seedDenominator ∧
    nextCarrierNumerator 6 body block numerator denominator =
      forwardScale * seedNumerator ∧
    nextCarrierDenominator 6 body block numerator denominator =
      forwardScale * seedDenominator ∧
    canonicalRcDbInverseRawNumerator seedNumerator seedDenominator =
      -(inverseContent : ℤ) * numerator ∧
    canonicalRcDbInverseRawDenominator seedNumerator seedDenominator =
      -(inverseContent : ℤ) * denominator ∧
    Int.gcd
        (canonicalRcDbInverseRawNumerator seedNumerator seedDenominator)
        (canonicalRcDbInverseRawDenominator seedNumerator seedDenominator) =
      inverseContent ∧
    (inverseContent : ℤ) * (-forwardScale) =
      (terminalDiscrepancy 6 : ℤ) * deletionCRadius 6 * setterMarker 6 *
        upperPower 6 block * swappedLowerCode 6 body block ∧
    numerator.Coprime denominator ∧
    denominator < numerator ∧
    deletionCHalfHead 6 ∣ numerator ∧
    (deletionCRadius 6).Coprime denominator ∧
    Nat.gcd (numerator - denominator) (3 * deletionCMarker 6) = 3 ∧
    Nat.gcd
        (deletionCRawNumerator 6 numerator denominator)
        (deletionCRawDenominator 6 numerator denominator) =
      3 * deletionCHead 6 ∧
    deletionCRawNumerator 6 numerator denominator / (3 * deletionCHead 6) =
      postNumerator ∧
    deletionCRawDenominator 6 numerator denominator / (3 * deletionCHead 6) =
      postDenominator ∧
    fareyHeight numerator denominator < fareyHeight seedNumerator seedDenominator ∧
    fareyHeight postNumerator postDenominator < fareyHeight numerator denominator ∧
    fareyHeight postNumerator postDenominator <
      fareyHeight seedNumerator seedDenominator

/-- A canonical physical pullback followed by an exact-channel `D_c` contraction can shrink
Farey height across both the first step and the complete two-step window. The witness is an
abstract local carrier, not a proved `MM-O29` seed, reachable carrier, or pole. -/
theorem exists_normalizationCollapseWitness :
    ∃ seedNumerator seedDenominator numerator denominator
        postNumerator postDenominator inverseContent : Nat,
      ∃ forwardScale : ℤ,
        IsNormalizationCollapseWitness seedNumerator seedDenominator numerator denominator
          postNumerator postDenominator inverseContent forwardScale := by
  refine ⟨1915861521737, 27626, 200420, 200417, 727, 160268,
    166177436936869872, -10932, ?_⟩
  have upper_eq :
      swappedUpperCode 6 [.rule .c, .erase .b] = 23911928 := by
    simpa [widthScale] using canonicalRcDb_upperCode 6
  have lower_eq :
      swappedLowerCode 6 (canonicalRcDbBody 6) [.rule .c, .erase .b] =
        23911568 := by
    have doubled := canonicalRcDb_lowerCode (width := 6) (by norm_num)
    norm_num [widthScale] at doubled
    omega
  have power_eq : upperPower 6 [.rule .c, .erase .b] = 19683 := by
    simp [widthScale]
  simp only [IsNormalizationCollapseWitness]
  rw [upper_eq, lower_eq, power_eq]
  norm_num [upper_eq, lower_eq, power_eq, canonicalRcDbInverseRawNumerator,
    canonicalRcDbInverseRawDenominator, nextCarrierNumerator,
    nextCarrierDenominator, upperPower, upperLength, spell, nearyUpper, tagCode,
    widthScale, setterMarker, terminalDiscrepancy, centeredCoefficient,
    deletionCRadius, deletionCMarker, deletionCHead, deletionCHalfHead,
    deletionCRawNumerator, deletionCRawDenominator, fareyHeight, Nat.dist]

end MatrixMortality.SwappedSetterNormalizationCollapse
