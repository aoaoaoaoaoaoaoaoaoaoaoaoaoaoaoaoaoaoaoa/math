import MatrixMortality.SwappedSetterCarrierGap

/-!
# Last-step resonance for deep swapped carriers

A primitive carrier congruent to the distinguished ratio modulo the full marker scale cannot
enter through an arbitrary final block.  Exact normalization accounting forces the discarded
common three-adic depth to be one less than that block's upper length.  The final theorem derives
this resonance directly from a nonterminal full-erasure-tail pole.
-/

namespace MatrixMortality.SwappedSetterCarrierResonance

open PadicValuation SwappedSetterMultitransfer SwappedSetterCarrierGap

private instance factPrimeThree : Fact (Nat.Prime 3) :=
  ⟨by norm_num⟩

private theorem centeredCoefficient_isUnit
    {width : Nat} (width_pos : 0 < width) :
    IsUnit 3 (centeredCoefficient width : ℚ) := by
  apply intCast_isUnit_of_not_dvd
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
  intro divides
  obtain ⟨factor, factor_eq⟩ := divides
  simp [centeredCoefficient, widthScale, pow_succ] at factor_eq
  omega

private theorem terminalDiscrepancy_isUnit
    {width : Nat} (width_pos : 0 < width) :
    IsUnit 3 (terminalDiscrepancy width : ℚ) := by
  apply intCast_isUnit_of_not_dvd
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
  intro divides
  obtain ⟨factor, factor_eq⟩ := divides
  simp [terminalDiscrepancy, widthScale, pow_succ] at factor_eq
  omega

private theorem setterMarker_isUnit
    {width : Nat} (width_pos : 0 < width) :
    IsUnit 3 (setterMarker width : ℚ) := by
  apply intCast_isUnit_of_not_dvd
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
  intro divides
  obtain ⟨factor, factor_eq⟩ := divides
  simp [setterMarker, widthScale, pow_succ] at factor_eq
  omega

private theorem not_dvd_three_of_intCast_isUnit {value : ℤ}
    (unit : IsUnit 3 (value : ℚ)) : ¬(3 : ℤ) ∣ value := by
  intro divides
  have valuation_zero : padicValInt 3 value = 0 := by
    have rational_valuation_zero := unit.2
    rw [padicValRat.of_int] at rational_valuation_zero
    exact_mod_cast rational_valuation_zero
  rw [padicValInt.eq_zero_iff] at valuation_zero
  rcases valuation_zero with prime_one | value_zero | not_dvd
  · norm_num at prime_one
  · exact unit.1 (by exact_mod_cast value_zero)
  · exact not_dvd divides

private theorem intCast_isPositive_of_dvd
    {value : ℤ} (value_ne : value ≠ 0) (divides : (3 : ℤ) ∣ value) :
    IsPositive 3 (value : ℚ) := by
  have valuation_ne : padicValInt 3 value ≠ 0 := by
    intro valuation_zero
    rw [padicValInt.eq_zero_iff] at valuation_zero
    rcases valuation_zero with prime_one | value_zero | not_dvd
    · norm_num at prime_one
    · exact value_ne value_zero
    · exact not_dvd divides
  constructor
  · exact_mod_cast value_ne
  · rw [padicValRat.of_int]
    exact_mod_cast Nat.pos_of_ne_zero valuation_ne

private theorem roleBlock_upperLength_pos
    {width : Nat} {block : List NearyTile} (role_block : IsRoleBlock block) :
    0 < upperLength width block := by
  obtain ⟨front, letter, rfl⟩ := role_block
  rw [upperLength, spell_append]
  apply List.length_pos_of_ne_nil
  apply List.append_ne_nil_of_right_ne_nil
  simpa [spell] using nearyUpper_ne_nil width (.erase letter)

/-- For a primitive predecessor, a deep unit-denominator successor forces the predecessor
denominator to be a `3`-adic unit. -/
private theorem deepUnitSuccessor_predecessorDenominator_isUnit
    {width scaleDepth gapDepth : Nat} (width_two : 2 ≤ width)
    (body : List TagLetter) {block : List NearyTile} (role_block : IsRoleBlock block)
    {numerator denominator nextNumerator nextDenominator scale : ℤ}
    (primitive : IsCoprime numerator denominator)
    (next_denominator_unit : IsUnit 3 (nextDenominator : ℚ))
    (scale_shell : HasValue 3 (scale : ℚ) scaleDepth)
    (gap_shell : HasValue 3 (nextDenominator - nextNumerator : ℚ) gapDepth)
    (gap_deep : width ≤ gapDepth)
    (numerator_eq :
      nextCarrierNumerator width body block numerator denominator =
        scale * nextNumerator)
    (denominator_eq :
      nextCarrierDenominator width body block numerator denominator =
        scale * nextDenominator) :
    IsUnit 3 (denominator : ℚ) := by
  apply intCast_isUnit_of_not_dvd
  intro denominator_dvd
  have numerator_not_dvd : ¬(3 : ℤ) ∣ numerator := by
    intro numerator_dvd
    have three_unit := primitive.isUnit_of_dvd' numerator_dvd denominator_dvd
    rw [Int.isUnit_iff] at three_unit
    omega
  have lower_unit := roleBlock_lower_isUnit width body role_block
  have lower_not_dvd := not_dvd_three_of_intCast_isUnit lower_unit
  let residual : ℤ :=
    swappedUpperCode width block * denominator -
      swappedLowerCode width body block * numerator
  have residual_not_dvd : ¬(3 : ℤ) ∣ residual := by
    intro residual_dvd
    have upper_product_dvd :
        (3 : ℤ) ∣ swappedUpperCode width block * denominator :=
      dvd_mul_of_dvd_right denominator_dvd _
    have lower_product_dvd :
        (3 : ℤ) ∣ swappedLowerCode width body block * numerator := by
      have difference_dvd := upper_product_dvd.sub residual_dvd
      simpa [residual] using difference_dvd
    rcases (by norm_num : Prime (3 : ℤ)).dvd_mul.mp lower_product_dvd with
      lower_dvd | numerator_dvd
    · exact lower_not_dvd lower_dvd
    · exact numerator_not_dvd numerator_dvd
  have residual_unit : IsUnit 3 (residual : ℚ) :=
    intCast_isUnit_of_not_dvd residual_not_dvd
  have width_pos : 0 < width := by omega
  have centered_unit := centeredCoefficient_isUnit width_pos
  have terminal_unit := terminalDiscrepancy_isUnit width_pos
  have marker_unit := setterMarker_isUnit width_pos
  have denominator_eq_rat :
      (centeredCoefficient width : ℚ) * residual = scale * nextDenominator := by
    rw [nextCarrierDenominator] at denominator_eq
    have casted :
        (centeredCoefficient width : ℚ) *
            (swappedUpperCode width block * denominator -
              swappedLowerCode width body block * numerator) =
          scale * nextDenominator := by
      exact_mod_cast denominator_eq
    simpa [residual] using casted
  have scale_depth_zero : scaleDepth = 0 := by
    have left_shell := mul_hasValue centered_unit residual_unit
    have right_shell := mul_hasValue scale_shell next_denominator_unit
    have valuations_eq := congrArg (padicValRat 3) denominator_eq_rat
    rw [left_shell.2, right_shell.2] at valuations_eq
    exact_mod_cast valuations_eq.symm
  let obstruction : ℚ :=
    terminalDiscrepancy width * 3 ^ upperLength width block * denominator -
      3 * residual
  have residual_triple_shell : HasValue 3 (3 * (residual : ℚ)) 1 := by
    simpa using mul_hasValue (primePower_hasValue (prime := 3) 1) residual_unit
  have obstruction_shell : HasValue 3 obstruction 1 := by
    by_cases denominator_zero : denominator = 0
    · simp [obstruction, denominator_zero]
      exact neg_hasValue residual_triple_shell
    · have denominator_positive :=
        intCast_isPositive_of_dvd denominator_zero denominator_dvd
      have denominator_shell :
          HasValue 3 (denominator : ℚ) (padicValRat 3 (denominator : ℚ)) :=
        ⟨by exact_mod_cast denominator_zero, rfl⟩
      have upper_shell :
          HasValue 3
            ((terminalDiscrepancy width : ℚ) *
              3 ^ upperLength width block * denominator)
            ((upperLength width block : Nat) +
              padicValRat 3 (denominator : ℚ)) := by
        simpa using mul_hasValue
          (mul_hasValue terminal_unit
            (primePower_hasValue (prime := 3) (upperLength width block)))
          denominator_shell
      have upper_value_gt :
          (1 : ℤ) <
            (upperLength width block : Nat) +
              padicValRat 3 (denominator : ℚ) := by
        have upper_pos := roleBlock_upperLength_pos (width := width) role_block
        have denominator_value_pos := denominator_positive.2
        omega
      have summand_valuations_ne :
          padicValRat 3
              ((terminalDiscrepancy width : ℚ) *
                3 ^ upperLength width block * denominator) ≠
            padicValRat 3 (3 * (residual : ℚ)) := by
        rw [upper_shell.2, residual_triple_shell.2]
        exact ne_of_gt upper_value_gt
      have forced := sub_hasValue_min upper_shell.1 residual_triple_shell.1
        summand_valuations_ne
      rw [upper_shell.2, residual_triple_shell.2,
        min_eq_right (le_of_lt upper_value_gt)] at forced
      simpa [obstruction] using forced
  have gap_eq :
      (scale : ℚ) * (nextDenominator - nextNumerator) =
        setterMarker width * obstruction := by
    have raw_gap := nextCarrier_gap width body block numerator denominator
    rw [denominator_eq, numerator_eq] at raw_gap
    have raw_gap_rat :
        (scale : ℚ) * nextDenominator - scale * nextNumerator =
          setterMarker width *
            (terminalDiscrepancy width * 3 ^ upperLength width block * denominator -
              3 * (swappedUpperCode width block * denominator -
                swappedLowerCode width body block * numerator)) := by
      exact_mod_cast raw_gap
    calc
      (scale : ℚ) * (nextDenominator - nextNumerator) =
          scale * nextDenominator - scale * nextNumerator := by ring
      _ = setterMarker width *
          (terminalDiscrepancy width * 3 ^ upperLength width block * denominator -
            3 * (swappedUpperCode width block * denominator -
              swappedLowerCode width body block * numerator)) := raw_gap_rat
      _ = setterMarker width * obstruction := by simp [obstruction, residual]
  have left_shell := mul_hasValue scale_shell gap_shell
  have right_shell := mul_hasValue marker_unit obstruction_shell
  have valuations_eq := congrArg (padicValRat 3) gap_eq
  rw [left_shell.2, right_shell.2, scale_depth_zero] at valuations_eq
  have gap_two : 2 ≤ gapDepth := le_trans width_two gap_deep
  omega

/-- A normalized successor congruent to one modulo the full marker power can arise only when
the discarded common `3`-power has depth exactly one below the last upper length. -/
private theorem deepUnitSuccessor_forces_lastStep_resonance
    {width scaleDepth gapDepth : Nat} (width_two : 2 ≤ width)
    (body : List TagLetter) (block : List NearyTile)
    {numerator denominator nextNumerator nextDenominator scale : ℤ}
    (denominator_unit : IsUnit 3 (denominator : ℚ))
    (next_denominator_unit : IsUnit 3 (nextDenominator : ℚ))
    (scale_shell : HasValue 3 (scale : ℚ) scaleDepth)
    (gap_shell : HasValue 3 (nextDenominator - nextNumerator : ℚ) gapDepth)
    (gap_deep : width ≤ gapDepth)
    (numerator_eq :
      nextCarrierNumerator width body block numerator denominator =
        scale * nextNumerator)
    (denominator_eq :
      nextCarrierDenominator width body block numerator denominator =
        scale * nextDenominator) :
    upperLength width block = scaleDepth + 1 := by
  let residual : ℚ :=
    swappedUpperCode width block * denominator -
      swappedLowerCode width body block * numerator
  have width_pos : 0 < width := by omega
  have centered_unit := centeredCoefficient_isUnit width_pos
  have terminal_unit := terminalDiscrepancy_isUnit width_pos
  have marker_unit := setterMarker_isUnit width_pos
  have residual_eq :
      (centeredCoefficient width : ℚ) * residual =
        scale * nextDenominator := by
    rw [nextCarrierDenominator] at denominator_eq
    have denominator_eq_rat :
        (centeredCoefficient width : ℚ) *
            (swappedUpperCode width block * denominator -
              swappedLowerCode width body block * numerator) =
          scale * nextDenominator := by
      exact_mod_cast denominator_eq
    simpa [residual] using denominator_eq_rat
  have residual_shell : HasValue 3 residual scaleDepth := by
    have quotient_shell :=
      div_hasValue (mul_hasValue scale_shell next_denominator_unit) centered_unit
    have residual_division :
        residual = (scale * nextDenominator) / centeredCoefficient width := by
      apply (eq_div_iff centered_unit.1).mpr
      simpa [mul_comm] using residual_eq
    simpa [residual_division] using quotient_shell
  let obstruction : ℚ :=
    terminalDiscrepancy width * 3 ^ upperLength width block * denominator -
      3 * residual
  have gap_eq :
      (scale : ℚ) * (nextDenominator - nextNumerator) =
        setterMarker width * obstruction := by
    have raw_gap := nextCarrier_gap width body block numerator denominator
    rw [denominator_eq, numerator_eq] at raw_gap
    have raw_gap_rat :
        (scale : ℚ) * nextDenominator - scale * nextNumerator =
          setterMarker width *
            (terminalDiscrepancy width * 3 ^ upperLength width block * denominator -
              3 * (swappedUpperCode width block * denominator -
                swappedLowerCode width body block * numerator)) := by
      exact_mod_cast raw_gap
    calc
      (scale : ℚ) * (nextDenominator - nextNumerator) =
          scale * nextDenominator - scale * nextNumerator := by ring
      _ = setterMarker width *
          (terminalDiscrepancy width * 3 ^ upperLength width block * denominator -
            3 * (swappedUpperCode width block * denominator -
              swappedLowerCode width body block * numerator)) := raw_gap_rat
      _ = setterMarker width * obstruction := by rfl
  have obstruction_shell :
      HasValue 3 obstruction (scaleDepth + gapDepth : Nat) := by
    have left_shell := mul_hasValue scale_shell gap_shell
    have quotient_shell := div_hasValue left_shell marker_unit
    have obstruction_division :
        obstruction =
          (scale * (nextDenominator - nextNumerator)) / setterMarker width := by
      apply (eq_div_iff marker_unit.1).mpr
      calc
        obstruction * setterMarker width = setterMarker width * obstruction := mul_comm _ _
        _ = scale * (nextDenominator - nextNumerator) := gap_eq.symm
    simpa [obstruction_division] using quotient_shell
  have upper_shell :
      HasValue 3
        ((terminalDiscrepancy width : ℚ) * 3 ^ upperLength width block * denominator)
        (upperLength width block : Nat) := by
    simpa using mul_hasValue (mul_hasValue terminal_unit
      (primePower_hasValue (prime := 3) (upperLength width block))) denominator_unit
  have residual_triple_shell :
      HasValue 3 (3 * residual) (scaleDepth + 1 : Nat) := by
    simpa [add_comm] using
      mul_hasValue (primePower_hasValue (prime := 3) 1) residual_shell
  by_contra lengths_ne
  have summand_valuations_ne :
      padicValRat 3
          ((terminalDiscrepancy width : ℚ) * 3 ^ upperLength width block * denominator) ≠
        padicValRat 3 (3 * residual) := by
    intro valuations_eq
    rw [upper_shell.2, residual_triple_shell.2] at valuations_eq
    exact lengths_ne (by exact_mod_cast valuations_eq)
  have forced_shell :
      HasValue 3 obstruction
        (min (upperLength width block) (scaleDepth + 1) : Nat) := by
    simpa [obstruction, upper_shell.2, residual_triple_shell.2] using
      sub_hasValue_min upper_shell.1 residual_triple_shell.1 summand_valuations_ne
  have valuation_eq := obstruction_shell.2.symm.trans forced_shell.2
  have minimum_lt :
      min (upperLength width block) (scaleDepth + 1) < scaleDepth + gapDepth := by
    have gap_two : 2 ≤ gapDepth := le_trans width_two gap_deep
    rcases lt_or_gt_of_ne lengths_ne with upper_lt | upper_gt
    · rw [min_eq_left upper_lt.le]
      omega
    · rw [min_eq_right upper_gt.le]
      omega
  have valuation_ne :
      ((scaleDepth + gapDepth : Nat) : ℤ) ≠
        (min (upperLength width block) (scaleDepth + 1) : Nat) := by
    exact_mod_cast ne_of_gt minimum_lt
  exact valuation_ne valuation_eq

/-- Primitive normalization discharges the predecessor-unit hypothesis in the last-step
resonance theorem. -/
private theorem primitiveDeepUnitSuccessor_forces_lastStep_resonance
    {width scaleDepth gapDepth : Nat} (width_two : 2 ≤ width)
    (body : List TagLetter) {block : List NearyTile} (role_block : IsRoleBlock block)
    {numerator denominator nextNumerator nextDenominator scale : ℤ}
    (primitive : IsCoprime numerator denominator)
    (next_denominator_unit : IsUnit 3 (nextDenominator : ℚ))
    (scale_shell : HasValue 3 (scale : ℚ) scaleDepth)
    (gap_shell : HasValue 3 (nextDenominator - nextNumerator : ℚ) gapDepth)
    (gap_deep : width ≤ gapDepth)
    (numerator_eq :
      nextCarrierNumerator width body block numerator denominator =
        scale * nextNumerator)
    (denominator_eq :
      nextCarrierDenominator width body block numerator denominator =
        scale * nextDenominator) :
    upperLength width block = scaleDepth + 1 := by
  have denominator_unit :=
    deepUnitSuccessor_predecessorDenominator_isUnit width_two body role_block primitive
      next_denominator_unit scale_shell gap_shell gap_deep numerator_eq denominator_eq
  exact deepUnitSuccessor_forces_lastStep_resonance width_two body block denominator_unit
    next_denominator_unit scale_shell gap_shell gap_deep numerator_eq denominator_eq

/-- Divisibility by the full marker scale yields an exact last-step normalization depth. -/
private theorem primitiveDivisibleUnitSuccessor_forces_lastStep_resonance
    {width : Nat} (width_two : 2 ≤ width)
    (body : List TagLetter) {block : List NearyTile} (role_block : IsRoleBlock block)
    {numerator denominator nextNumerator nextDenominator scale : ℤ}
    (primitive : IsCoprime numerator denominator)
    (next_denominator_unit : IsUnit 3 (nextDenominator : ℚ))
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
        upperLength width block = scaleDepth + 1 := by
  let scaleDepth := padicValInt 3 scale
  let gapDepth := padicValInt 3 (nextDenominator - nextNumerator)
  have scale_shell : HasValue 3 (scale : ℚ) scaleDepth := by
    constructor
    · exact_mod_cast scale_ne
    · rw [padicValRat.of_int]
  have gap_shell :
      HasValue 3 (nextDenominator - nextNumerator : ℚ) gapDepth := by
    constructor
    · exact_mod_cast gap_ne
    · rw [← Int.cast_sub]
      rw [padicValRat.of_int]
  have gap_deep : width ≤ gapDepth := by
    have power_divisible :
        (3 : ℤ) ^ width ∣ nextDenominator - nextNumerator := by
      simpa [widthScale] using gap_divisible
    have valuation_bound :=
      (padicValInt_dvd_iff width (nextDenominator - nextNumerator)).mp power_divisible
    exact valuation_bound.resolve_left gap_ne
  refine ⟨scaleDepth, scale_shell, ?_⟩
  exact primitiveDeepUnitSuccessor_forces_lastStep_resonance width_two body role_block
    primitive next_denominator_unit scale_shell gap_shell gap_deep numerator_eq denominator_eq

/-- A primitive pair congruent modulo a positive power of three has a unit denominator. -/
theorem primitiveCongruent_denominator_isUnit
    {width : Nat} (width_pos : 0 < width)
    {numerator denominator : ℤ} (primitive : IsCoprime numerator denominator)
    (gap_divisible : widthScale width ∣ denominator - numerator) :
    IsUnit 3 (denominator : ℚ) := by
  apply intCast_isUnit_of_not_dvd
  intro denominator_dvd
  have three_dvd_scale : (3 : ℤ) ∣ widthScale width := by
    simpa [widthScale] using dvd_pow_self (3 : ℤ) (Nat.ne_of_gt width_pos)
  have gap_dvd : (3 : ℤ) ∣ denominator - numerator :=
    three_dvd_scale.trans gap_divisible
  have numerator_dvd : (3 : ℤ) ∣ numerator := by
    have difference := denominator_dvd.sub gap_dvd
    simpa using difference
  have three_unit := primitive.isUnit_of_dvd' numerator_dvd denominator_dvd
  rw [Int.isUnit_iff] at three_unit
  omega

/-- A nonterminal primitive successor congruent modulo the full marker scale forces the exact
last-step normalization resonance. -/
theorem primitiveDivisibleSuccessor_forces_lastStep_resonance
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
        upperLength width block = scaleDepth + 1 := by
  have next_denominator_unit :=
    primitiveCongruent_denominator_isUnit (by omega) next_primitive gap_divisible
  exact primitiveDivisibleUnitSuccessor_forces_lastStep_resonance width_two body role_block
    primitive next_denominator_unit scale_ne gap_ne gap_divisible numerator_eq denominator_eq

/-- Any nonterminal full-erasure-tail pole forces the exact normalization resonance at the last
completed history block. -/
theorem erasureTailPole_forces_lastStep_resonance
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
        upperLength width block = scaleDepth + 1 := by
  have raw_represented := blockStep_represents_nextCarrier width body block previous
    numerator denominator represented
  rw [numerator_eq, denominator_eq] at raw_represented
  have current_represented :=
    SwappedSetterCarrierGap.RepresentsDefectRatio.of_common_scale scale_ne raw_represented
  have threshold :=
    SwappedSetterThresholdCarry.threshold_crossProduct_of_pole width_two body target
      (SwappedSetterHistory.blockStep width body block previous) current_y_ne
      current_represented pole
  have gap_divisible : widthScale width ∣ nextDenominator - nextNumerator := by
    simpa [widthScale] using
      SwappedSetterThresholdCarry.erasureTail_threshold_dvd_gap body target_tail threshold
  exact primitiveDivisibleSuccessor_forces_lastStep_resonance width_two body role_block
    primitive next_primitive scale_ne nonterminal gap_divisible numerator_eq denominator_eq

end MatrixMortality.SwappedSetterCarrierResonance
