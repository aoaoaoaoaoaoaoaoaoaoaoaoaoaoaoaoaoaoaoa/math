import MatrixMortality.SwappedSetterThreeBlockFrontier

/-!
# Reachable counterexample to block-local cylinder extinction
-/

namespace MatrixMortality.SwappedSetterReachableCylinder

open SwappedSetterMultitransfer SwappedSetterHistory SwappedSetterThresholdCarry
  SwappedSetterCarrierGap

/-- Compiler body used by the smallest audited reachable-cylinder witness. -/
def reachableCylinderBody : List TagLetter := [.b, .b, .c, .c]

/-- The witness block is a rule `R_c` followed by its closing deletion `D_c`. -/
def reachableCylinderBlock : List NearyTile := [.rule .c, .erase .c]

/-- Two copies of `R_cD_c` from the ordinary reset reach the witness carrier. -/
def reachableCylinderOrigin : CenteredState :=
  blockStep 3 reachableCylinderBody reachableCylinderBlock
    (blockStep 3 reachableCylinderBody reachableCylinderBlock (ordinaryReset 3))

private abbrev originNumerator : ℤ := -570661367816
private abbrev originDenominator : ℤ := 106465174525
private abbrev successorNumerator : ℤ := -607561904608405895896
private abbrev successorDenominator : ℤ := 113351524805114612975

private theorem reachableCylinderOrigin_represented :
    RepresentsDefectRatio 3 reachableCylinderOrigin originNumerator originDenominator := by
  norm_num [RepresentsDefectRatio, reachableCylinderOrigin, reachableCylinderBody,
    reachableCylinderBlock, ordinaryDefect, ordinaryReset, blockStep, nextX, nextY,
    blockCoefficient, centeredCoupling, centeredCoefficient, setterMarker,
    terminalDiscrepancy, widthScale, swappedUpperCode, swappedLowerCode, upperLength,
    nearyUpper, nearyLower, nearyMarker, tagCode, tagEncode, spell, ternaryCode,
    ternaryDigit, Nat.ofDigits, List.replicate]

/-- The `MM-S71` predecessor cylinder is genuinely reachable. The theorem asserts no pole. -/
theorem reachable_nonDeletionC_predecessorCylinder :
    IsRoleBlock reachableCylinderBlock ∧
      reachableCylinderBlock ≠ [.erase .c] ∧
      RepresentsDefectRatio 3 reachableCylinderOrigin
        originNumerator originDenominator ∧
      IsCoprime originNumerator originDenominator ∧
      IsCoprime successorNumerator successorDenominator ∧
      upperLength 3 reachableCylinderBlock = 2 ∧
      nextCarrierNumerator 3 reachableCylinderBody reachableCylinderBlock
          originNumerator originDenominator =
        -3 * successorNumerator ∧
      nextCarrierDenominator 3 reachableCylinderBody reachableCylinderBlock
          originNumerator originDenominator =
        -3 * successorDenominator ∧
      successorDenominator - successorNumerator ≠ 0 ∧
      widthScale 3 ∣ successorDenominator - successorNumerator ∧
      (3 : ℤ) ^ 3 ∣
        swappedUpperCode 3 reachableCylinderBlock * originDenominator -
            swappedLowerCode 3 reachableCylinderBody reachableCylinderBlock *
              originNumerator -
          3 * terminalDiscrepancy 3 * originDenominator := by
  refine ⟨⟨[.rule .c], .c, rfl⟩, ?_, reachableCylinderOrigin_represented, ?_⟩
  · simp [reachableCylinderBlock]
  norm_num [reachableCylinderBody, reachableCylinderBlock, nextCarrierNumerator,
    nextCarrierDenominator, swappedUpperCode, swappedLowerCode, upperLength,
    centeredCoefficient, setterMarker, terminalDiscrepancy, widthScale,
    nearyUpper, nearyLower, nearyMarker, tagCode, tagEncode, spell, ternaryCode,
    ternaryDigit, Nat.ofDigits, List.replicate, Int.isCoprime_iff_gcd_eq_one]

end MatrixMortality.SwappedSetterReachableCylinder
