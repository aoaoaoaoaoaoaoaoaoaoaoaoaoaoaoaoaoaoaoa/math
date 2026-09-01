import MatrixMortality.MixedPrimeRealTrapUpperCycles

/-!
# Exact periods of guarded upper-run cycles

This module proves that the guarded `L_n, U₀^r, U₁, M_m` cycle constructed in
`MixedPrimeRealTrapUpperCycles` has exact minimal period `r+3`.

Two-adic valuations distinguish the wall, odd-denominator, and upper phases.  Strict motion
within the upper run and depth separation between phases then exclude every nonempty proper
return prefix.  The terminal existence theorem realizes every period at least three.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation
open PeriodicShell

private local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private theorem wallOddUpperFamily_twoUnit_of_odd
    {value : ℕ} (value_odd : Odd value) :
    IsUnit 2 (value : ℚ) := by
  have value_ne : value ≠ 0 := by
    intro value_zero
    rw [value_zero] at value_odd
    simp at value_odd
  refine ⟨by exact_mod_cast value_ne, ?_⟩
  rw [padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd value_odd.not_two_dvd_nat]
  norm_num

private theorem wallOddUpperFamily_largeThree_odd (depth : ℕ) :
    Odd (wallOddLargeThreePower depth) := by
  exact (by norm_num : Odd 3).pow

private theorem wallOddUpperFamily_middleThree_odd (depth : ℕ) :
    Odd (wallOddMiddleThreePower depth) := by
  exact (by norm_num : Odd 3).pow

private theorem wallOddUpperFamily_fivePower_odd (runLength : ℕ) :
    Odd (wallOddUpperRunFivePower runLength) := by
  exact (by norm_num : Odd 5).pow

private theorem wallOddUpperFamily_largeTwo_even
    {depth : ℕ} (depth_lower : 2 ≤ depth) :
    Even (wallOddLargeTwoPower depth) := by
  unfold wallOddLargeTwoPower
  exact even_two.pow_of_ne_zero (by omega)

theorem wallOddUpperFamilyHalfDenominator_odd
    (lowerDepth middleDepth runLength : ℕ) :
    Odd (wallOddUpperFamilyHalfDenominator
      lowerDepth middleDepth runLength) := by
  have leading_odd : Odd
      (123 * wallOddMiddleThreePower middleDepth *
        wallOddUpperRunFivePower runLength *
          wallOddLargeThreePower lowerDepth) :=
    (((by norm_num : Odd 123).mul
      (wallOddUpperFamily_middleThree_odd middleDepth)).mul
        (wallOddUpperFamily_fivePower_odd runLength)).mul
      (wallOddUpperFamily_largeThree_odd lowerDepth)
  have remainder_even : Even
      (2 * (wallOddMiddleThreePower middleDepth *
          wallOddUpperRunFivePower runLength *
            wallOddUpperFamilyLargePowerGap lowerDepth +
        wallOddLargeTwoPower lowerDepth *
          (wallOddMiddleThreePower middleDepth *
              wallOddUpperRunPowerGap runLength +
            wallOddUpperRunThreePower runLength *
              wallOddUpperFamilyMiddlePowerGap middleDepth))) :=
    even_two.mul_right _
  simpa only [wallOddUpperFamilyHalfDenominator] using
    leading_odd.add_even remainder_even

theorem wallOddUpperFamilyWallNumerator_odd
    {lowerDepth middleDepth runLength : ℕ}
    (lowerDepth_lower : 7 ≤ lowerDepth) :
    Odd (wallOddUpperFamilyWallNumerator
      lowerDepth middleDepth runLength) := by
  have leading_odd : Odd
      (225 * wallOddUpperRunFivePower runLength *
        wallOddLargeThreePower lowerDepth) :=
    ((by norm_num : Odd 225).mul
      (wallOddUpperFamily_fivePower_odd runLength)).mul
        (wallOddUpperFamily_largeThree_odd lowerDepth)
  have q_even := wallOddUpperFamily_largeTwo_even
    (by omega : 2 ≤ lowerDepth)
  have remainder_even : Even
      (wallOddLargeTwoPower lowerDepth *
        (16 * wallOddUpperRunThreePower runLength +
          25 * wallOddUpperRunPowerGap runLength)) :=
    q_even.mul_right _
  have inside_odd := leading_odd.add_even remainder_even
  exact (wallOddUpperFamily_middleThree_odd middleDepth).mul inside_odd

theorem wallOddUpperFamilyWallMantissa_twoValue
    {lowerDepth middleDepth runLength : ℕ}
    (lowerDepth_lower : 7 ≤ lowerDepth) :
    HasValue 2 (wallOddUpperFamilyWallMantissa
      lowerDepth middleDepth runLength) (-1) := by
  have numerator_unit := wallOddUpperFamily_twoUnit_of_odd
    (wallOddUpperFamilyWallNumerator_odd
      (middleDepth := middleDepth) (runLength := runLength) lowerDepth_lower)
  have denominator_unit := wallOddUpperFamily_twoUnit_of_odd
    (wallOddUpperFamilyHalfDenominator_odd
      lowerDepth middleDepth runLength)
  have two_value : HasValue 2 (2 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 2) 1)
  simpa [wallOddUpperFamilyWallMantissa] using
    div_hasValue numerator_unit (mul_hasValue two_value denominator_unit)

private theorem wallOddUpperFamily_natDivOdd_twoNonnegative
    {numerator denominator : ℕ} (numerator_ne : numerator ≠ 0)
    (denominator_odd : Odd denominator) :
    0 ≤ padicValRat 2 ((numerator : ℚ) / denominator) := by
  have numerator_value :
      HasValue 2 (numerator : ℚ) (padicValNat 2 numerator : ℤ) :=
    ⟨by exact_mod_cast numerator_ne, padicValRat.of_nat⟩
  have denominator_unit := wallOddUpperFamily_twoUnit_of_odd denominator_odd
  have quotient_value := div_hasValue numerator_value denominator_unit
  rw [quotient_value.2]
  omega

theorem wallOddUpperFamilyFirstOddMantissa_twoNonnegative
    (lowerDepth middleDepth runLength : ℕ) :
    0 ≤ padicValRat 2 (wallOddUpperFamilyFirstOddMantissa
      lowerDepth middleDepth runLength) := by
  have numerator_ne :
      wallOddUpperFamilyFirstOddNumerator
        lowerDepth middleDepth runLength ≠ 0 := by
    have p_pos : 0 < wallOddLargeThreePower lowerDepth := by
      simp [wallOddLargeThreePower]
    have core_pos :
        0 < wallOddUpperFamilyFirstOddCore middleDepth runLength := by
      simp only [wallOddUpperFamilyFirstOddCore]
      have leading_pos : 0 < wallOddMiddleThreePower middleDepth *
          (80 * wallOddUpperRunThreePower runLength +
            125 * wallOddUpperRunPowerGap runLength) := by
        simp [wallOddMiddleThreePower, wallOddUpperRunThreePower]
      omega
    exact (Nat.mul_pos p_pos core_pos).ne'
  simpa [wallOddUpperFamilyFirstOddMantissa] using
    wallOddUpperFamily_natDivOdd_twoNonnegative numerator_ne
      (wallOddUpperFamilyHalfDenominator_odd
        lowerDepth middleDepth runLength)

theorem wallOddUpperFamilyLastUpperMantissa_twoNonnegative
    (lowerDepth middleDepth runLength : ℕ) :
    0 ≤ padicValRat 2 (wallOddUpperFamilyLastUpperMantissa
      lowerDepth middleDepth runLength) := by
  have numerator_ne :
      wallOddUpperFamilyLastUpperNumerator
        lowerDepth middleDepth runLength ≠ 0 := by
    have core_pos :
        0 < wallOddUpperFamilyLastUpperCore
          lowerDepth middleDepth runLength := by
      simp only [wallOddUpperFamilyLastUpperCore]
      have leading_pos : 0 < wallOddUpperRunFivePower runLength *
          wallOddLargeThreePower lowerDepth *
            (40 * wallOddMiddleThreePower middleDepth +
              9 * wallOddMiddleTwoPower middleDepth) := by
        simp [wallOddUpperRunFivePower, wallOddLargeThreePower,
          wallOddMiddleThreePower]
      omega
    simp only [wallOddUpperFamilyLastUpperNumerator]
    exact (Nat.mul_pos (by norm_num) core_pos).ne'
  simpa [wallOddUpperFamilyLastUpperMantissa] using
    wallOddUpperFamily_natDivOdd_twoNonnegative numerator_ne
      (wallOddUpperFamilyHalfDenominator_odd
        lowerDepth middleDepth runLength)

theorem wallOddUpperFamilySecondOddMantissa_twoNonnegative
    (lowerDepth middleDepth runLength : ℕ) :
    0 ≤ padicValRat 2 (wallOddUpperFamilySecondOddMantissa
      lowerDepth middleDepth runLength) := by
  have numerator_ne :
      wallOddUpperFamilySecondOddNumerator
        lowerDepth middleDepth runLength ≠ 0 := by
    have leading_pos : 0 <
        15 * wallOddUpperRunFivePower runLength *
          wallOddLargeThreePower lowerDepth *
            (5 * wallOddMiddleThreePower middleDepth +
              3 * wallOddMiddleTwoPower middleDepth) := by
      simp [wallOddUpperRunFivePower, wallOddLargeThreePower,
        wallOddMiddleThreePower]
    simp only [wallOddUpperFamilySecondOddNumerator]
    omega
  simpa [wallOddUpperFamilySecondOddMantissa] using
    wallOddUpperFamily_natDivOdd_twoNonnegative numerator_ne
      (wallOddUpperFamilyHalfDenominator_odd
        lowerDepth middleDepth runLength)

private theorem upperMantissaMap_twoNonnegative
    (value : ℚ) (value_nonnegative : 0 ≤ padicValRat 2 value) :
    0 ≤ padicValRat 2 ((5 * value - 2) / 3) := by
  have three_unit : IsUnit 2 (3 : ℚ) :=
    intCast_isUnit_of_not_dvd (by norm_num)
  by_cases value_zero : value = 0
  · subst value
    have output_value : HasValue 2 ((-2 : ℚ) / 3) 1 := by
      have two_value : HasValue 2 (2 : ℚ) 1 := by
        simpa using (primePower_hasValue (prime := 2) 1)
      exact div_hasValue (neg_hasValue two_value) three_unit
    have actual_value : HasValue 2 (((5 : ℚ) * 0 - 2) / 3) 1 := by
      simpa only [mul_zero, zero_sub] using output_value
    rw [actual_value.2]
    norm_num
  have value_hasValue : HasValue 2 value (padicValRat 2 value) :=
    ⟨value_zero, rfl⟩
  have five_unit : IsUnit 2 (5 : ℚ) :=
    intCast_isUnit_of_not_dvd (by norm_num)
  have leading_value := mul_hasValue five_unit value_hasValue
  have two_value : HasValue 2 (2 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 2) 1)
  have negative_two_value := neg_hasValue two_value
  let numerator := 5 * value + (-2)
  by_cases numerator_zero : numerator = 0
  · have output_zero : (5 * value - 2) / 3 = 0 := by
      have numerator_eq : 5 * value - 2 = numerator := by
        simp only [numerator]
        ring
      rw [numerator_eq, numerator_zero]
      simp
    rw [output_zero, padicValRat.zero]
  · have numerator_lower :=
      padicValRat.min_le_padicValRat_add (p := 2) numerator_zero
    have minimum_nonnegative :
        0 ≤ min (padicValRat 2 value) 1 := by
      exact le_min value_nonnegative (by norm_num)
    have numerator_nonnegative : 0 ≤ padicValRat 2 numerator := by
      have lower : min (padicValRat 2 value) 1 ≤
          padicValRat 2 numerator := by
        simpa only [numerator, leading_value.2, negative_two_value.2,
          zero_add] using numerator_lower
      exact minimum_nonnegative.trans lower
    have numerator_eq : 5 * value - 2 = numerator := by
      simp only [numerator]
      ring
    rw [numerator_eq, padicValRat.div numerator_zero three_unit.1,
      three_unit.2, sub_zero]
    exact numerator_nonnegative

theorem wallOddUpperFamilyUpperMantissa_twoNonnegative
    (lowerDepth middleDepth runLength index : ℕ) :
    0 ≤ padicValRat 2 (wallOddUpperFamilyUpperMantissa
      lowerDepth middleDepth runLength index) := by
  induction index with
  | zero =>
      rw [wallOddUpperFamilyUpperMantissa_zero]
      exact wallOddUpperFamilyFirstOddMantissa_twoNonnegative
        lowerDepth middleDepth runLength
  | succ index induction =>
      rw [wallOddUpperFamilyUpperMantissa_succ]
      exact upperMantissaMap_twoNonnegative _ induction

theorem wallOddUpperFamilyMiddleCenter_twoValue
    {lowerDepth middleDepth runLength : ℕ}
    (lowerDepth_lower : 7 ≤ lowerDepth)
    (middleDepth_lower : 2 ≤ middleDepth) :
    HasValue 2
      (5 * wallOddUpperFamilySecondOddMantissa
          lowerDepth middleDepth runLength - 3)
      (middleDepth - 2 : ℕ) := by
  let center := 5 * wallOddUpperFamilySecondOddMantissa
    lowerDepth middleDepth runLength - 3
  have wall_value := wallOddUpperFamilyWallMantissa_twoValue
    (middleDepth := middleDepth) (runLength := runLength) lowerDepth_lower
  have wall_eq := wallOddUpperFamilyWall_eq_middle
    (middleDepth := middleDepth) (runLength := runLength) lowerDepth_lower
  have center_ne : center ≠ 0 := by
    intro center_zero
    have wall_zero : wallOddUpperFamilyWallMantissa
        lowerDepth middleDepth runLength = 0 := by
      rw [wall_eq, show 5 * wallOddUpperFamilySecondOddMantissa
        lowerDepth middleDepth runLength - 3 = center by rfl,
        center_zero, mul_zero]
    exact wall_value.1 wall_zero
  have r_unit : IsUnit 2 (wallOddMiddleThreePower middleDepth : ℚ) :=
    wallOddUpperFamily_twoUnit_of_odd
      (wallOddUpperFamily_middleThree_odd middleDepth)
  have denominator_eq :
      (2 : ℚ) * wallOddMiddleTwoPower middleDepth =
        (2 : ℚ) ^ (middleDepth - 1) := by
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le middleDepth_lower
    simp only [wallOddMiddleTwoPower]
    have left_exponent : 2 + offset - 2 = offset := by omega
    have right_exponent : 2 + offset - 1 = offset + 1 := by omega
    rw [left_exponent, right_exponent, pow_succ]
    norm_num [Nat.cast_pow]
    exact mul_comm _ _
  have denominator_value :
      HasValue 2 ((2 : ℚ) * wallOddMiddleTwoPower middleDepth)
        ((middleDepth - 1 : ℕ) : ℤ) := by
    rw [denominator_eq]
    exact primePower_hasValue (middleDepth - 1)
  have coefficient_value :
      HasValue 2
        ((wallOddMiddleThreePower middleDepth : ℚ) /
          (2 * wallOddMiddleTwoPower middleDepth))
        (-((middleDepth - 1 : ℕ) : ℤ)) := by
    have quotient := div_hasValue r_unit denominator_value
    convert quotient using 1
    ring
  have center_value : HasValue 2 center (padicValRat 2 center) :=
    ⟨center_ne, rfl⟩
  have product_value := mul_hasValue coefficient_value center_value
  have valuation_eq :
      (-1 : ℤ) = -((middleDepth - 1 : ℕ) : ℤ) + padicValRat 2 center := by
    calc
      (-1 : ℤ) = padicValRat 2
          (wallOddUpperFamilyWallMantissa
            lowerDepth middleDepth runLength) := wall_value.2.symm
      _ = padicValRat 2
          (((wallOddMiddleThreePower middleDepth : ℚ) /
              (2 * wallOddMiddleTwoPower middleDepth)) * center) := by
        rw [wall_eq]
      _ = -((middleDepth - 1 : ℕ) : ℤ) + padicValRat 2 center :=
        product_value.2
  have center_index :
      padicValRat 2 center = ((middleDepth - 2 : ℕ) : ℤ) := by
    omega
  exact ⟨center_ne, center_index⟩

theorem wallOddUpperFamilyUpperMantissa_strictAnti
    {lowerDepth middleDepth runLength left right : ℕ}
    (lowerDepth_lower : 7 ≤ lowerDepth)
    (middleDepth_lower : 2 ≤ middleDepth)
    (middleDepth_upper : middleDepth ≤ 6)
    (left_lt_right : left < right) :
    wallOddUpperFamilyUpperMantissa
        lowerDepth middleDepth runLength right <
      wallOddUpperFamilyUpperMantissa
        lowerDepth middleDepth runLength left := by
  have first_bounds := wallOddUpperFamilyFirstOddMantissa_normalized
    (runLength := runLength) lowerDepth_lower middleDepth_lower middleDepth_upper
  have power_lt :
      (5 / 3 : ℚ) ^ left < (5 / 3 : ℚ) ^ right :=
    pow_lt_pow_right₀ (a := (5 / 3 : ℚ)) (by norm_num) left_lt_right
  have gap_pos :
      0 < 1 - wallOddUpperFamilyFirstOddMantissa
        lowerDepth middleDepth runLength := by linarith
  simp only [wallOddUpperFamilyUpperMantissa]
  have scaled_lt := mul_lt_mul_of_pos_right power_lt gap_pos
  linarith

theorem wallOddUpperFamilyUpperState_injective
    {lowerDepth middleDepth runLength left right : ℕ}
    (lowerDepth_lower : 7 ≤ lowerDepth)
    (middleDepth_lower : 2 ≤ middleDepth)
    (middleDepth_upper : middleDepth ≤ 6)
    (states_eq :
      realTrapBandPoint 0
          (wallOddUpperFamilyUpperMantissa
            lowerDepth middleDepth runLength left) =
        realTrapBandPoint 0
          (wallOddUpperFamilyUpperMantissa
            lowerDepth middleDepth runLength right)) :
    left = right := by
  have mantissas_eq :
      wallOddUpperFamilyUpperMantissa
          lowerDepth middleDepth runLength left =
        wallOddUpperFamilyUpperMantissa
          lowerDepth middleDepth runLength right := by
    simp only [realTrapBandPoint, pow_zero, mul_one] at states_eq
    linarith
  rcases lt_trichotomy left right with left_lt | left_eq | right_lt
  · have strict := wallOddUpperFamilyUpperMantissa_strictAnti
      (runLength := runLength) lowerDepth_lower middleDepth_lower
        middleDepth_upper left_lt
    linarith
  · exact left_eq
  · have strict := wallOddUpperFamilyUpperMantissa_strictAnti
      (runLength := runLength) lowerDepth_lower middleDepth_lower
        middleDepth_upper right_lt
    linarith

theorem wallOddUpperFamily_distinguishedStates_pairwise_ne
    {lowerDepth middleDepth runLength : ℕ}
    (lowerDepth_lower : 7 ≤ lowerDepth)
    (middleDepth_lower : 2 ≤ middleDepth)
    (middleDepth_upper : middleDepth ≤ 6) :
    realTrapBandPoint middleDepth
        (wallOddUpperFamilyWallMantissa lowerDepth middleDepth runLength) ≠
      realTrapBandPoint lowerDepth
        (wallOddUpperFamilyFirstOddMantissa lowerDepth middleDepth runLength) ∧
    realTrapBandPoint lowerDepth
        (wallOddUpperFamilyFirstOddMantissa lowerDepth middleDepth runLength) ≠
      realTrapBandPoint 1
        (wallOddUpperFamilySecondOddMantissa lowerDepth middleDepth runLength) ∧
    realTrapBandPoint 1
        (wallOddUpperFamilySecondOddMantissa lowerDepth middleDepth runLength) ≠
      realTrapBandPoint middleDepth
        (wallOddUpperFamilyWallMantissa lowerDepth middleDepth runLength) := by
  have wall_bounds := wallOddUpperFamilyWallMantissa_normalized
    (runLength := runLength) lowerDepth_lower middleDepth_lower middleDepth_upper
  have first_bounds := wallOddUpperFamilyFirstOddMantissa_normalized
    (runLength := runLength) lowerDepth_lower middleDepth_lower middleDepth_upper
  have second_bounds := wallOddUpperFamilySecondOddMantissa_normalized
    (runLength := runLength) lowerDepth_lower middleDepth_lower middleDepth_upper
  have wall_depth := realTrapMaxPredecessorWait_bandPoint middleDepth
    (by linarith : 2 / 3 < wallOddUpperFamilyWallMantissa
      lowerDepth middleDepth runLength) (le_of_lt wall_bounds.2)
  have first_depth := realTrapMaxPredecessorWait_bandPoint lowerDepth
    first_bounds.1 (le_of_lt first_bounds.2)
  have second_depth := realTrapMaxPredecessorWait_bandPoint 1
    second_bounds.1 (le_of_lt second_bounds.2)
  constructor
  · intro states_eq
    have depth_eq := congrArg realTrapMaxPredecessorWait states_eq
    rw [wall_depth, first_depth] at depth_eq
    omega
  constructor
  · intro states_eq
    have depth_eq := congrArg realTrapMaxPredecessorWait states_eq
    rw [first_depth, second_depth] at depth_eq
    omega
  · intro states_eq
    have depth_eq := congrArg realTrapMaxPredecessorWait states_eq
    rw [second_depth, wall_depth] at depth_eq
    omega

theorem wallOddUpperFamilyUpperState_ne_distinguished
    {lowerDepth middleDepth runLength index : ℕ}
    (lowerDepth_lower : 7 ≤ lowerDepth)
    (middleDepth_lower : 2 ≤ middleDepth)
    (middleDepth_upper : middleDepth ≤ 6)
    (index_le : index ≤ runLength) :
    realTrapBandPoint 0
        (wallOddUpperFamilyUpperMantissa
          lowerDepth middleDepth runLength index) ≠
          realTrapBandPoint middleDepth
            (wallOddUpperFamilyWallMantissa
              lowerDepth middleDepth runLength) ∧
      realTrapBandPoint 0
        (wallOddUpperFamilyUpperMantissa
          lowerDepth middleDepth runLength index) ≠
          realTrapBandPoint lowerDepth
            (wallOddUpperFamilyFirstOddMantissa
              lowerDepth middleDepth runLength) ∧
      realTrapBandPoint 0
        (wallOddUpperFamilyUpperMantissa
          lowerDepth middleDepth runLength index) ≠
          realTrapBandPoint 1
            (wallOddUpperFamilySecondOddMantissa
              lowerDepth middleDepth runLength) := by
  have upper_bounds := wallOddUpperFamilyUpperMantissa_normalized
    lowerDepth_lower middleDepth_lower middleDepth_upper index_le
  have wall_bounds := wallOddUpperFamilyWallMantissa_normalized
    (runLength := runLength) lowerDepth_lower middleDepth_lower middleDepth_upper
  have first_bounds := wallOddUpperFamilyFirstOddMantissa_normalized
    (runLength := runLength) lowerDepth_lower middleDepth_lower middleDepth_upper
  have second_bounds := wallOddUpperFamilySecondOddMantissa_normalized
    (runLength := runLength) lowerDepth_lower middleDepth_lower middleDepth_upper
  have upper_depth := realTrapMaxPredecessorWait_bandPoint 0
    upper_bounds.1 (le_of_lt upper_bounds.2)
  have wall_depth := realTrapMaxPredecessorWait_bandPoint middleDepth
    (by linarith : 2 / 3 < wallOddUpperFamilyWallMantissa
      lowerDepth middleDepth runLength) (le_of_lt wall_bounds.2)
  have first_depth := realTrapMaxPredecessorWait_bandPoint lowerDepth
    first_bounds.1 (le_of_lt first_bounds.2)
  have second_depth := realTrapMaxPredecessorWait_bandPoint 1
    second_bounds.1 (le_of_lt second_bounds.2)
  constructor
  · intro states_eq
    have depth_eq := congrArg realTrapMaxPredecessorWait states_eq
    rw [upper_depth, wall_depth] at depth_eq
    omega
  constructor
  · intro states_eq
    have depth_eq := congrArg realTrapMaxPredecessorWait states_eq
    rw [upper_depth, first_depth] at depth_eq
    omega
  · intro states_eq
    have depth_eq := congrArg realTrapMaxPredecessorWait states_eq
    rw [upper_depth, second_depth] at depth_eq
    omega

theorem wallOddUpperFamily_no_early_return
    {lowerDepth middleDepth runLength prefixLength : ℕ}
    (lowerDepth_lower : 7 ≤ lowerDepth)
    (middleDepth_lower : 2 ≤ middleDepth)
    (middleDepth_upper : middleDepth ≤ 6)
    (prefixLength_pos : 0 < prefixLength)
    (prefixLength_lt :
      prefixLength <
        (wallOddUpperFamilySchedule
          lowerDepth middleDepth runLength).length) :
    shellRun
        ((wallOddUpperFamilySchedule lowerDepth middleDepth runLength).take
          prefixLength)
        (realTrapBandPoint middleDepth
          (wallOddUpperFamilyWallMantissa
            lowerDepth middleDepth runLength)) ≠
      realTrapBandPoint middleDepth
        (wallOddUpperFamilyWallMantissa
          lowerDepth middleDepth runLength) := by
  let state := realTrapBandPoint middleDepth
    (wallOddUpperFamilyWallMantissa lowerDepth middleDepth runLength)
  have schedule_length :
      (wallOddUpperFamilySchedule
        lowerDepth middleDepth runLength).length = runLength + 3 := by
    simp [wallOddUpperFamilySchedule]
  have state_lt_half : state < 1 / 2 := by
    have wall_bounds := wallOddUpperFamilyWallMantissa_normalized
      (runLength := runLength) lowerDepth_lower middleDepth_lower
        middleDepth_upper
    have power_pos : 0 < (2 / 3 : ℚ) ^ middleDepth := by positivity
    have power_le : (2 / 3 : ℚ) ^ middleDepth ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have scaled_lt :
        (2 / 3 : ℚ) ^ middleDepth *
            wallOddUpperFamilyWallMantissa
              lowerDepth middleDepth runLength < 1 := by
      calc
        _ < (2 / 3 : ℚ) ^ middleDepth * 1 :=
          mul_lt_mul_of_pos_left wall_bounds.2 power_pos
        _ ≤ 1 := by simpa using power_le
    simp only [state, realTrapBandPoint]
    linarith
  by_cases prefix_within_zeros : prefixLength ≤ runLength + 1
  · have prefix_eq :
        (wallOddUpperFamilySchedule lowerDepth middleDepth runLength).take
            prefixLength =
          List.replicate prefixLength 0 := by
      rw [wallOddUpperFamilySchedule,
        List.take_append_of_le_length]
      · rw [List.take_replicate, Nat.min_eq_left prefix_within_zeros]
      · simpa using prefix_within_zeros
    have contraction_lt : (3 / 5 : ℚ) ^ prefixLength < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) prefixLength_pos.ne'
    intro early_return
    rw [prefix_eq, shellRun_replicate_zero] at early_return
    have factor_pos : 0 < 1 - (3 / 5 : ℚ) ^ prefixLength := by
      linarith
    have gap_pos : 0 < 1 / 2 - state := by linarith
    have product_pos := mul_pos factor_pos gap_pos
    change 1 / 2 + (3 / 5 : ℚ) ^ prefixLength * (state - 1 / 2) =
      state at early_return
    nlinarith
  · have prefix_eq : prefixLength = runLength + 2 := by
      rw [schedule_length] at prefixLength_lt
      omega
    have taken_schedule :
        (wallOddUpperFamilySchedule lowerDepth middleDepth runLength).take
            prefixLength =
          List.replicate (runLength + 1) 0 ++ [lowerDepth] := by
      rw [prefix_eq, wallOddUpperFamilySchedule, List.take_append]
      simp
    have first_state_ne :=
      (wallOddUpperFamily_distinguishedStates_pairwise_ne
        (runLength := runLength) lowerDepth_lower middleDepth_lower
          middleDepth_upper).1
    intro early_return
    rw [taken_schedule, shellRun_append,
      wallOddUpperFamily_zeroPrefix lowerDepth_lower middleDepth_lower,
      shellRun_singleton, shellStep_upperPredecessor] at early_return
    exact first_state_ne early_return.symm

theorem exists_guarded_wallCycle_schedule_length
    {period : ℕ} (period_lower : 3 ≤ period) :
    ∃ waits state wallMantissa,
      waits.length = period ∧
      state = realTrapBandPoint 2 wallMantissa ∧
      9 / 10 < wallMantissa ∧ wallMantissa < 1 ∧
      HasValue 2 wallMantissa (-1) ∧
      shellRun waits state = state ∧
      ∀ front back, waits = front ++ back →
        IsUnit 5 (shellRun front state) := by
  let runLength := period - 3
  let waits := wallOddUpperFamilySchedule 7 2 runLength
  let wallMantissa := wallOddUpperFamilyWallMantissa 7 2 runLength
  let state := realTrapBandPoint 2 wallMantissa
  have length_eq : waits.length = period := by
    simp only [waits, wallOddUpperFamilySchedule, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil]
    omega
  have bounds := wallOddUpperFamilyWallMantissa_normalized
    (runLength := runLength) (by norm_num : 7 ≤ 7)
      (by norm_num : 2 ≤ 2) (by norm_num : 2 ≤ 6)
  have two_value := wallOddUpperFamilyWallMantissa_twoValue
    (middleDepth := 2) (runLength := runLength) (by norm_num : 7 ≤ 7)
  have cycle := wallOddUpperFamily_cycle
    (runLength := runLength) (by norm_num : 7 ≤ 7) (by norm_num : 2 ≤ 2)
  have guarded := wallOddUpperFamily_shellPrefixesUnit
    (runLength := runLength) (by norm_num : 7 ≤ 7) (by norm_num : 2 ≤ 2)
  exact ⟨waits, state, wallMantissa, length_eq, rfl,
    bounds.1, bounds.2, two_value, cycle, guarded⟩

theorem exists_guarded_wallCycle_exact_period
    {period : ℕ} (period_lower : 3 ≤ period) :
    ∃ waits state,
      waits.length = period ∧
      shellRun waits state = state ∧
      (∀ front back, waits = front ++ back →
        IsUnit 5 (shellRun front state)) ∧
      ∀ prefixLength, 0 < prefixLength → prefixLength < period →
        shellRun (waits.take prefixLength) state ≠ state := by
  let runLength := period - 3
  let waits := wallOddUpperFamilySchedule 7 2 runLength
  let state := realTrapBandPoint 2
    (wallOddUpperFamilyWallMantissa 7 2 runLength)
  have length_eq : waits.length = period := by
    simp only [waits, wallOddUpperFamilySchedule, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil]
    omega
  have cycle : shellRun waits state = state := by
    simpa only [waits, state] using
      (wallOddUpperFamily_cycle (runLength := runLength)
        (by norm_num : 7 ≤ 7) (by norm_num : 2 ≤ 2))
  have guarded : ∀ front back, waits = front ++ back →
      IsUnit 5 (shellRun front state) := by
    simpa only [waits, state] using
      (wallOddUpperFamily_shellPrefixesUnit (runLength := runLength)
        (by norm_num : 7 ≤ 7) (by norm_num : 2 ≤ 2))
  have no_early : ∀ prefixLength, 0 < prefixLength →
      prefixLength < period →
      shellRun (waits.take prefixLength) state ≠ state := by
    intro prefixLength prefixLength_pos prefixLength_lt
    have schedule_prefix_lt :
        prefixLength <
          (wallOddUpperFamilySchedule 7 2 runLength).length := by
      simpa only [waits] using prefixLength_lt.trans_le length_eq.ge
    simpa only [waits, state] using
      (wallOddUpperFamily_no_early_return
        (lowerDepth := 7) (middleDepth := 2) (runLength := runLength)
        (prefixLength := prefixLength) (by norm_num) (by norm_num)
        (by norm_num) prefixLength_pos schedule_prefix_lt)
  exact ⟨waits, state, length_eq, cycle, guarded, no_early⟩

end MatrixMortality.MixedPrimeDebt
