import MatrixMortality.SwappedSetterSequentialDoubleDeletion

/-!
# Three-block backward frontier for the swapped setter
-/

namespace MatrixMortality.SwappedSetterThreeBlockFrontier

open PadicValuation SwappedSetterMultitransfer SwappedSetterHistory
  SwappedSetterThresholdCarry SwappedSetterCarrierGap SwappedSetterPredecessorCylinder
  SwappedSetterSequentialDoubleDeletion

/-- A nonterminal full-tail pole behind two singleton `D_c` transfers either halts genuinely or
puts the block before them in its exact nonzero last-resonance predecessor cylinder. -/
theorem erasureTailPole_threeBlock_backwardFrontier
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    (body_long : width - 1 ≤ body.length)
    {precedingBlock : List NearyTile} (preceding_role : IsRoleBlock precedingBlock)
    (origin : CenteredState)
    {originNumerator originDenominator
      antecedentNumerator antecedentDenominator antecedentScale
      previousNumerator previousDenominator previousScale
      currentNumerator currentDenominator currentScale : ℤ}
    (origin_represented :
      RepresentsDefectRatio width origin originNumerator originDenominator)
    (origin_primitive : IsCoprime originNumerator originDenominator)
    (antecedent_primitive :
      IsCoprime antecedentNumerator antecedentDenominator)
    (previous_primitive : IsCoprime previousNumerator previousDenominator)
    (current_primitive : IsCoprime currentNumerator currentDenominator)
    (antecedent_scale_ne : antecedentScale ≠ 0)
    (antecedent_numerator_eq :
      nextCarrierNumerator width body precedingBlock originNumerator originDenominator =
        antecedentScale * antecedentNumerator)
    (antecedent_denominator_eq :
      nextCarrierDenominator width body precedingBlock originNumerator originDenominator =
        antecedentScale * antecedentDenominator)
    (previous_scale_ne : previousScale ≠ 0)
    (previous_numerator_eq :
      nextCarrierNumerator width body [.erase .c]
          antecedentNumerator antecedentDenominator =
        previousScale * previousNumerator)
    (previous_denominator_eq :
      nextCarrierDenominator width body [.erase .c]
          antecedentNumerator antecedentDenominator =
        previousScale * previousDenominator)
    (current_scale_ne : currentScale ≠ 0)
    (current_numerator_eq :
      nextCarrierNumerator width body [.erase .c]
          previousNumerator previousDenominator =
        currentScale * currentNumerator)
    (current_denominator_eq :
      nextCarrierDenominator width body [.erase .c]
          previousNumerator previousDenominator =
        currentScale * currentDenominator)
    {target : List NearyTile} (target_tail : HasErasureTail width target)
    (current_y_ne :
      (blockStep width body [.erase .c]
        (blockStep width body [.erase .c]
          (blockStep width body precedingBlock origin))).y ≠ 0)
    (pole :
      poleResidual width body target
        (blockStep width body [.erase .c]
          (blockStep width body [.erase .c]
            (blockStep width body precedingBlock origin))) = 0)
    (nonterminal : currentDenominator - currentNumerator ≠ 0) :
    TagHaltsFrom width (tagOutput body) (body.drop (width - 1) ++ [.b]) ∨
      ∃ scaleDepth : Nat,
        HasValue 3 (antecedentScale : ℚ) scaleDepth ∧
          upperLength width precedingBlock = scaleDepth + 1 ∧
            (3 : ℤ) ^ (scaleDepth + width - 1) ∣
              swappedUpperCode width precedingBlock * originDenominator -
                  swappedLowerCode width body precedingBlock * originNumerator -
                3 ^ scaleDepth * terminalDiscrepancy width * originDenominator := by
  have antecedent_raw_represented :=
    blockStep_represents_nextCarrier width body precedingBlock origin
      originNumerator originDenominator origin_represented
  rw [antecedent_numerator_eq, antecedent_denominator_eq] at antecedent_raw_represented
  have antecedent_represented :
      RepresentsDefectRatio width (blockStep width body precedingBlock origin)
        antecedentNumerator antecedentDenominator :=
    RepresentsDefectRatio.of_common_scale antecedent_scale_ne antecedent_raw_represented
  rcases sequentialDoubleDeletionC_erasureTailPole_forces_halt_or_nonzeroPredecessorGap
      width_two body body_long (blockStep width body precedingBlock origin)
      antecedent_represented antecedent_primitive previous_primitive current_primitive
      previous_scale_ne previous_numerator_eq previous_denominator_eq current_scale_ne
      current_numerator_eq current_denominator_eq target_tail current_y_ne pole nonterminal with
    halts | ⟨antecedent_gap_ne, antecedent_gap_divisible⟩
  · exact Or.inl halts
  · exact Or.inr <|
      primitiveDivisibleSuccessor_predecessorCylinder width_two body preceding_role
        origin_primitive antecedent_primitive antecedent_scale_ne antecedent_gap_ne
        antecedent_gap_divisible antecedent_numerator_eq antecedent_denominator_eq

end MatrixMortality.SwappedSetterThreeBlockFrontier
