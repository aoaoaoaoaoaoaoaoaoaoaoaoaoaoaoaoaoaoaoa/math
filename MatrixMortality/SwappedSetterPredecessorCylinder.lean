import Mathlib.Tactic.NormNum.IsCoprime
import MatrixMortality.SwappedSetterCarrierResonance

/-!
# The unique predecessor cylinder behind a full-tail pole
-/

namespace MatrixMortality.SwappedSetterPredecessorCylinder

open PadicValuation SwappedSetterMultitransfer SwappedSetterCarrierGap
  SwappedSetterCarrierResonance

private instance factPrimeThree : Fact (Nat.Prime 3) :=
  ⟨by norm_num⟩

private theorem setterMarker_coprime_three
    {width : Nat} (width_pos : 0 < width) :
    IsCoprime (setterMarker width) (3 : ℤ) := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
  refine ⟨-1, 2 * (3 : ℤ) ^ offset, ?_⟩
  simp [setterMarker, widthScale, pow_succ]
  ring

private theorem intPower_dvd_of_hasValue
    {value : ℤ} {depth : Nat} (shell : HasValue 3 (value : ℚ) depth) :
    (3 : ℤ) ^ depth ∣ value := by
  have valuation_eq : padicValInt 3 value = depth := by
    have rational_eq := shell.2
    rw [padicValRat.of_int] at rational_eq
    exact_mod_cast rational_eq
  exact (padicValInt_dvd_iff depth value).mpr (Or.inr valuation_eq.ge)

private theorem cancel_one_three
    {depth : Nat} {value : ℤ}
    (divides : (3 : ℤ) ^ (depth + 1) ∣ 3 * value) :
    (3 : ℤ) ^ depth ∣ value := by
  have rearranged :
      (3 : ℤ) * 3 ^ depth ∣ 3 * value := by
    simpa [pow_succ, mul_comm] using divides
  exact (mul_dvd_mul_iff_left (by norm_num : (3 : ℤ) ≠ 0)).mp rearranged

/-- Full marker congruence after a primitive role-block transition leaves only one predecessor
cylinder. Its precision is the marker width plus the discarded common depth, less one. -/
theorem primitiveDivisibleSuccessor_predecessorCylinder
    {width : Nat} (width_two : 2 ≤ width)
    (body : List TagLetter) {block : List NearyTile} (role_block : IsRoleBlock block)
    {numerator denominator nextNumerator nextDenominator scale : ℤ}
    (primitive : IsCoprime numerator denominator)
    (next_primitive : IsCoprime nextNumerator nextDenominator)
    (scale_ne : scale ≠ 0)
    (gap_ne : nextDenominator - nextNumerator ≠ 0)
    (gap_divisible : widthScale width ∣ nextDenominator - nextNumerator)
    (numerator_eq :
      nextCarrierNumerator width body block numerator denominator =
        scale * nextNumerator)
    (denominator_eq :
      nextCarrierDenominator width body block numerator denominator =
        scale * nextDenominator) :
    ∃ scaleDepth : Nat,
      HasValue 3 (scale : ℚ) scaleDepth ∧
        upperLength width block = scaleDepth + 1 ∧
          (3 : ℤ) ^ (scaleDepth + width - 1) ∣
            swappedUpperCode width block * denominator -
                swappedLowerCode width body block * numerator -
              3 ^ scaleDepth * terminalDiscrepancy width * denominator := by
  obtain ⟨scaleDepth, scale_shell, length_eq⟩ :=
    primitiveDivisibleSuccessor_forces_lastStep_resonance width_two body role_block
      primitive next_primitive scale_ne gap_ne gap_divisible numerator_eq denominator_eq
  let residual : ℤ :=
    swappedUpperCode width block * denominator -
      swappedLowerCode width body block * numerator
  let cylinder : ℤ :=
    residual - 3 ^ scaleDepth * terminalDiscrepancy width * denominator
  have scale_divisible : (3 : ℤ) ^ scaleDepth ∣ scale :=
    intPower_dvd_of_hasValue scale_shell
  have gap_power_divisible :
      (3 : ℤ) ^ width ∣ nextDenominator - nextNumerator := by
    simpa [widthScale] using gap_divisible
  have product_divisible :
      (3 : ℤ) ^ (scaleDepth + width) ∣
        scale * (nextDenominator - nextNumerator) := by
    simpa [pow_add] using mul_dvd_mul scale_divisible gap_power_divisible
  have raw_gap := nextCarrier_gap width body block numerator denominator
  rw [denominator_eq, numerator_eq] at raw_gap
  have product_eq :
      scale * (nextDenominator - nextNumerator) =
        setterMarker width *
          (terminalDiscrepancy width * 3 ^ upperLength width block * denominator -
            3 * residual) := by
    calc
      scale * (nextDenominator - nextNumerator) =
          scale * nextDenominator - scale * nextNumerator := by ring
      _ = setterMarker width *
          (terminalDiscrepancy width * 3 ^ upperLength width block * denominator -
            3 * (swappedUpperCode width block * denominator -
              swappedLowerCode width body block * numerator)) := raw_gap
      _ = setterMarker width *
          (terminalDiscrepancy width * 3 ^ upperLength width block * denominator -
            3 * residual) := by rfl
  rw [product_eq] at product_divisible
  have power_marker_coprime :
      IsCoprime ((3 : ℤ) ^ (scaleDepth + width)) (setterMarker width) :=
    (setterMarker_coprime_three (by omega)).symm.pow_left
  have obstruction_divisible :
      (3 : ℤ) ^ (scaleDepth + width) ∣
        terminalDiscrepancy width * 3 ^ upperLength width block * denominator -
          3 * residual :=
    power_marker_coprime.dvd_of_dvd_mul_left product_divisible
  have obstruction_eq :
      terminalDiscrepancy width * 3 ^ upperLength width block * denominator -
          3 * residual =
        -3 * cylinder := by
    rw [length_eq, pow_succ]
    simp [cylinder]
    ring
  rw [obstruction_eq] at obstruction_divisible
  have triple_divisible :
      (3 : ℤ) ^ (scaleDepth + width) ∣ 3 * cylinder := by
    simpa using dvd_neg.mpr obstruction_divisible
  have exponent_eq :
      scaleDepth + width = (scaleDepth + width - 1) + 1 := by omega
  rw [exponent_eq] at triple_divisible
  refine ⟨scaleDepth, scale_shell, length_eq, ?_⟩
  simpa [cylinder, residual] using cancel_one_three triple_divisible

/-- A nonterminal pole with a full erasure tail puts the preceding primitive carrier in the
unique cylinder selected by the final role block and its normalization depth. -/
theorem erasureTailPole_forces_predecessorCylinder
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    {block : List NearyTile} (role_block : IsRoleBlock block)
    (previous : SwappedSetterHistory.CenteredState)
    {numerator denominator nextNumerator nextDenominator scale : ℤ}
    (represented :
      SwappedSetterThresholdCarry.RepresentsDefectRatio width previous
        numerator denominator)
    (primitive : IsCoprime numerator denominator)
    (next_primitive : IsCoprime nextNumerator nextDenominator)
    (scale_ne : scale ≠ 0)
    (numerator_eq :
      nextCarrierNumerator width body block numerator denominator =
        scale * nextNumerator)
    (denominator_eq :
      nextCarrierDenominator width body block numerator denominator =
        scale * nextDenominator)
    {target : List NearyTile}
    (target_tail : SwappedSetterThresholdCarry.HasErasureTail width target)
    (current_y_ne :
      (SwappedSetterHistory.blockStep width body block previous).y ≠ 0)
    (pole :
      SwappedSetterHistory.poleResidual width body target
        (SwappedSetterHistory.blockStep width body block previous) = 0)
    (nonterminal : nextDenominator - nextNumerator ≠ 0) :
    ∃ scaleDepth : Nat,
      HasValue 3 (scale : ℚ) scaleDepth ∧
        upperLength width block = scaleDepth + 1 ∧
          (3 : ℤ) ^ (scaleDepth + width - 1) ∣
            swappedUpperCode width block * denominator -
                swappedLowerCode width body block * numerator -
              3 ^ scaleDepth * terminalDiscrepancy width * denominator := by
  have raw_represented := blockStep_represents_nextCarrier width body block previous
    numerator denominator represented
  rw [numerator_eq, denominator_eq] at raw_represented
  have current_represented :=
    RepresentsDefectRatio.of_common_scale scale_ne raw_represented
  have threshold :=
    SwappedSetterThresholdCarry.threshold_crossProduct_of_pole width_two body target
      (SwappedSetterHistory.blockStep width body block previous) current_y_ne
      current_represented pole
  have gap_divisible : widthScale width ∣ nextDenominator - nextNumerator := by
    simpa [widthScale] using
      SwappedSetterThresholdCarry.erasureTail_threshold_dvd_gap body target_tail threshold
  exact primitiveDivisibleSuccessor_predecessorCylinder width_two body role_block
    primitive next_primitive scale_ne nonterminal gap_divisible numerator_eq denominator_eq

private theorem literalDeletionC_numerator_of_predecessorCylinder
    {width scaleDepth : Nat} (body : List TagLetter)
    {numerator denominator : ℤ}
    (length_eq : upperLength width [.erase .c] = scaleDepth + 1)
    (cylinder_divisible :
      (3 : ℤ) ^ (scaleDepth + width - 1) ∣
        swappedUpperCode width [.erase .c] * denominator -
            swappedLowerCode width body [.erase .c] * numerator -
          3 ^ scaleDepth * terminalDiscrepancy width * denominator) :
    (3 : ℤ) ^ (width - 1) ∣ numerator := by
  have scaleDepth_zero : scaleDepth = 0 := by
    rw [upperLength_singleton_erase_c] at length_eq
    omega
  subst scaleDepth
  have power_divides_twice : (3 : ℤ) ^ (width - 1) ∣ 2 * numerator := by
    simpa [swappedUpperCode_singleton_c, swappedLowerCode_singleton] using
      dvd_neg.mpr cylinder_divisible
  have coprime : IsCoprime ((3 : ℤ) ^ (width - 1)) 2 :=
    (by norm_num : IsCoprime (3 : ℤ) 2).pow_left
  exact coprime.dvd_of_dvd_mul_left power_divides_twice

/-- A literal `D_c` predecessor of a primitive full-marker successor has numerator divisible by
`3^(width-1)`. -/
theorem literalDeletionC_divisibleSuccessor_numerator
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    {numerator denominator nextNumerator nextDenominator scale : ℤ}
    (primitive : IsCoprime numerator denominator)
    (next_primitive : IsCoprime nextNumerator nextDenominator)
    (scale_ne : scale ≠ 0)
    (gap_ne : nextDenominator - nextNumerator ≠ 0)
    (gap_divisible : widthScale width ∣ nextDenominator - nextNumerator)
    (numerator_eq :
      nextCarrierNumerator width body [.erase .c] numerator denominator =
        scale * nextNumerator)
    (denominator_eq :
      nextCarrierDenominator width body [.erase .c] numerator denominator =
        scale * nextDenominator) :
    (3 : ℤ) ^ (width - 1) ∣ numerator := by
  have role_block : IsRoleBlock ([.erase .c] : List NearyTile) := by
    exact ⟨[], .c, by simp⟩
  obtain ⟨scaleDepth, _, length_eq, cylinder_divisible⟩ :=
    primitiveDivisibleSuccessor_predecessorCylinder width_two body role_block
      primitive next_primitive scale_ne gap_ne gap_divisible numerator_eq denominator_eq
  exact literalDeletionC_numerator_of_predecessorCylinder body length_eq
    cylinder_divisible

/-- At a physical nonterminal full-tail pole, a literal final `D_c` forces the preceding
primitive numerator into the codimension-`width-1` residue class zero. -/
theorem literalDeletionC_erasureTailPole_forces_numeratorDivisible
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    (previous : SwappedSetterHistory.CenteredState)
    {numerator denominator nextNumerator nextDenominator scale : ℤ}
    (represented :
      SwappedSetterThresholdCarry.RepresentsDefectRatio width previous
        numerator denominator)
    (primitive : IsCoprime numerator denominator)
    (next_primitive : IsCoprime nextNumerator nextDenominator)
    (scale_ne : scale ≠ 0)
    (numerator_eq :
      nextCarrierNumerator width body [.erase .c] numerator denominator =
        scale * nextNumerator)
    (denominator_eq :
      nextCarrierDenominator width body [.erase .c] numerator denominator =
        scale * nextDenominator)
    {target : List NearyTile}
    (target_tail : SwappedSetterThresholdCarry.HasErasureTail width target)
    (current_y_ne :
      (SwappedSetterHistory.blockStep width body [.erase .c] previous).y ≠ 0)
    (pole :
      SwappedSetterHistory.poleResidual width body target
        (SwappedSetterHistory.blockStep width body [.erase .c] previous) = 0)
    (nonterminal : nextDenominator - nextNumerator ≠ 0) :
    (3 : ℤ) ^ (width - 1) ∣ numerator := by
  have role_block : IsRoleBlock ([.erase .c] : List NearyTile) := by
    exact ⟨[], .c, by simp⟩
  obtain ⟨scaleDepth, _, length_eq, cylinder_divisible⟩ :=
    erasureTailPole_forces_predecessorCylinder width_two body role_block previous
      represented primitive next_primitive scale_ne numerator_eq denominator_eq target_tail
      current_y_ne pole nonterminal
  exact literalDeletionC_numerator_of_predecessorCylinder body length_eq
    cylinder_divisible

/-- The literal-`D_c` predecessor constraint is sharp on the distinguished deletion spine: its
first primitive numerator already contains the complete preceding width power. -/
theorem widthScale_dvd_distinguishedDeletionCNumerator (offset : Nat) :
    widthScale offset ∣ distinguishedDeletionCNumerator offset := by
  rw [distinguishedDeletionCNumerator, widthScale_eq_twice_halfScale_add_one]
  exact dvd_mul_right (2 * halfScale offset + 1) (15 * halfScale offset + 7)

end MatrixMortality.SwappedSetterPredecessorCylinder
