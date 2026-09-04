import MatrixMortality.MixedPrimeRealTrapLengthThreeReversing

/-!
# Reversing length-three target classifier

Prefix arithmetic and the real trap leave one generic reversing fibre. This module eliminates
the exceptional fibres, transports its exact carry, and classifies the surviving source and
target guards by a 250-by-ten semilinear residue language.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation
open PeriodicShell

private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Carry coordinate of the normalized reversing target. -/
def lengthThreeReversingTargetCarry (q A offset : ℕ) : ℚ :=
  (15 + (2 / 3 : ℚ) ^ (offset + 1) *
      (9 * (2 / 3 : ℚ) ^ (q + A + 1) -
        6 * (2 / 3 : ℚ) ^ q - 10)) /
    (1 - (2 / 3 : ℚ) ^ (offset + 1))

/-- The reversing target is the universal terminal coordinate at wait `t`. -/
theorem lengthThreeReversingTarget_eq_terminalCarryTarget
    (q A offset t : ℕ) :
    lengthThreeReversingTarget q A offset t =
      terminalCarryTarget t
        (lengthThreeReversingTargetCarry q A offset) := by
  have gap_positive : 0 < offset + 1 := by omega
  have gap_ne : 1 - (2 / 3 : ℚ) ^ (offset + 1) ≠ 0 := by
    have power_lt : (2 / 3 : ℚ) ^ (offset + 1) < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) gap_positive.ne'
    linarith
  rw [lengthThreeReversingTarget, terminalCarryTarget,
    lengthThreeReversingTargetCarry]
  field_simp [gap_ne]

/-- A guarded reversing target forces its incoming carry to exact depth two. -/
theorem lengthThreeReversingTarget_fiveUnit_forces_carry
    (q A offset t : ℕ)
    (target_unit : IsUnit 5 (lengthThreeReversingTarget q A offset t)) :
    HasValue 5 (lengthThreeReversingTargetCarry q A offset) 2 := by
  rw [lengthThreeReversingTarget_eq_terminalCarryTarget] at target_unit
  exact terminalCarryTarget_fiveUnit_forces_carry t target_unit

/-- Ten terminal residues classify a reversing target on its forced carry fibre. -/
theorem lengthThreeReversingTarget_fiveUnit_iff_mod_ten
    (q A offset t : ℕ)
    (carry_value :
      HasValue 5 (lengthThreeReversingTargetCarry q A offset) 2) :
    IsUnit 5 (lengthThreeReversingTarget q A offset t) ↔
      IsUnit 5 (lengthThreeReversingTarget q A offset (t % 10)) := by
  rw [lengthThreeReversingTarget_eq_terminalCarryTarget,
    lengthThreeReversingTarget_eq_terminalCarryTarget]
  exact terminalCarryTarget_fiveUnit_iff_mod_ten t carry_value

private theorem lengthThreeReversing_collisionTarget_fiveUnit
    (p q A offset t : ℕ)
    (target_unit : IsUnit 5 (lengthThreeReversingTarget q A offset t)) :
    IsUnit 5
      (shellRun (lengthThreeReversingLeft p q t (A + 2 + offset))
        (collisionSource
          (lengthThreeReversingLeft p q t (A + 2 + offset))
          (lengthThreeReversingRight p q t A 1))) := by
  have total_positive : A + 1 < A + 2 + offset := by omega
  have source_eq := lengthThreeReversing_collisionSource
    p q t A (A + 2 + offset) 1 total_positive
  rw [lengthThreeReversingSource_normalized] at source_eq
  have common_target :=
    (lengthThreeReversing_commonTarget p q A offset t).1
  rw [source_eq, common_target]
  exact target_unit

/-- Target acceptance forces the first reversing displacement to be even. -/
theorem lengthThreeReversingTarget_fiveUnit_forces_A_even
    (p q t : ℕ) {A offset : ℕ} (A_positive : 0 < A)
    (target_unit : IsUnit 5 (lengthThreeReversingTarget q A offset t)) :
    Even A := by
  have length_eq :
      (lengthThreeReversingLeft p q t (A + 2 + offset)).length =
        (lengthThreeReversingRight p q t A 1).length := by
    rfl
  have sum_ne :
      (lengthThreeReversingLeft p q t (A + 2 + offset)).sum ≠
        (lengthThreeReversingRight p q t A 1).sum := by
    simp only [lengthThreeReversingLeft, lengthThreeReversingRight,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  have collision_target_unit := lengthThreeReversing_collisionTarget_fiveUnit
    p q A offset t target_unit
  have first_gap :
      shellPrefixSumGap
          (lengthThreeReversingLeft p q t (A + 2 + offset))
          (lengthThreeReversingRight p q t A 1) 0 = A := by
    simp only [shellPrefixSumGap, lengthThreeReversingLeft,
      lengthThreeReversingRight, List.take, shellSlopeSumGap,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  have first_even := acceptedCollision_firstNonzeroPrefixGap_even
    length_eq sum_ne collision_target_unit (first := 0)
    (by simp [lengthThreeReversingLeft])
    (by rw [first_gap]; omega) (by omega)
  rwa [first_gap] at first_even

/-- When the even first displacement has carry depth one, the next reversing gap is odd. -/
theorem lengthThreeReversingTarget_fiveUnit_forces_nextGap_odd
    (p q t : ℕ) {A offset : ℕ} (A_two_or_four : A = 2 ∨ A = 4)
    (target_unit : IsUnit 5 (lengthThreeReversingTarget q A offset t)) :
    Odd (offset + 2) := by
  have length_eq :
      (lengthThreeReversingLeft p q t (A + 2 + offset)).length =
        (lengthThreeReversingRight p q t A 1).length := by
    rfl
  have sum_ne :
      (lengthThreeReversingLeft p q t (A + 2 + offset)).sum ≠
        (lengthThreeReversingRight p q t A 1).sum := by
    simp only [lengthThreeReversingLeft, lengthThreeReversingRight,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  have collision_target_unit := lengthThreeReversing_collisionTarget_fiveUnit
    p q A offset t target_unit
  have first_gap :
      shellPrefixSumGap
          (lengthThreeReversingLeft p q t (A + 2 + offset))
          (lengthThreeReversingRight p q t A 1) 0 = A := by
    simp only [shellPrefixSumGap, lengthThreeReversingLeft,
      lengthThreeReversingRight, List.take, shellSlopeSumGap,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  have next_gap :
      shellPrefixSumGap
          (lengthThreeReversingLeft p q t (A + 2 + offset))
          (lengthThreeReversingRight p q t A 1) 1 = offset + 2 := by
    simp only [shellPrefixSumGap, lengthThreeReversingLeft,
      lengthThreeReversingRight, List.take, shellSlopeSumGap,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  have first_depth :
      shellSlopeGapFiveDepth
          (shellPrefixSumGap
            (lengthThreeReversingLeft p q t (A + 2 + offset))
            (lengthThreeReversingRight p q t A 1) 0) = 1 := by
    rw [first_gap]
    rcases A_two_or_four with rfl | rfl <;>
      norm_num [shellSlopeGapFiveDepth, padicValNat_self]
  have next := acceptedCollision_nextPrefixGap_odd_of_firstCarryDepth_one
    length_eq sum_ne collision_target_unit (first := 0)
    (by simp [lengthThreeReversingLeft])
    (by rw [first_gap]; rcases A_two_or_four with rfl | rfl <;> norm_num)
    (by omega) first_depth
  rw [next_gap] at next
  exact next.2.2

private theorem reversingRatioPowerAffine_unit
    (constant coefficient : ℚ) (coefficient_unit : IsUnit 5 coefficient)
    (at_one_unit : IsUnit 5 (constant - coefficient))
    (at_ratio_unit : IsUnit 5 (constant - coefficient * (2 / 3 : ℚ)))
    {exponent : ℕ} (exponent_positive : 0 < exponent) :
    IsUnit 5 (constant - coefficient * (2 / 3 : ℚ) ^ exponent) := by
  rcases Nat.even_or_odd exponent with exponent_even | exponent_odd
  · have exponent_not_odd : ¬Odd exponent :=
      Nat.not_odd_iff_even.mpr exponent_even
    have gap_value := shellRatio_pow_sub_one_hasValue exponent_positive
    rw [shellSlopeGapFiveDepth, if_neg exponent_not_odd] at gap_value
    have scaled_value := mul_hasValue (neg_hasValue coefficient_unit) gap_value
    have scaled_positive :
        IsPositive 5
          (-coefficient * ((2 / 3 : ℚ) ^ exponent - 1)) :=
      ⟨scaled_value.1, by rw [scaled_value.2]; positivity⟩
    have result := unit_add_positive at_one_unit scaled_positive
    convert result using 1
    ring
  · rcases exponent_odd with ⟨half, exponent_eq⟩
    rw [exponent_eq]
    by_cases half_zero : half = 0
    · subst half
      simpa using at_ratio_unit
    · have even_gap_positive : 0 < 2 * half := by omega
      have even_gap_not_odd : ¬Odd (2 * half) :=
        Nat.not_odd_iff_even.mpr ⟨half, by omega⟩
      have even_gap_value := shellRatio_pow_sub_one_hasValue even_gap_positive
      rw [shellSlopeGapFiveDepth, if_neg even_gap_not_odd] at even_gap_value
      have ratio_unit : IsUnit 5 (2 / 3 : ℚ) :=
        div_hasValue
          (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (2 : ℤ)))
          (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (3 : ℤ)))
      have scaled_value := mul_hasValue
        (neg_hasValue (mul_hasValue coefficient_unit ratio_unit)) even_gap_value
      have scaled_positive :
          IsPositive 5
            (-(coefficient * (2 / 3 : ℚ)) *
              ((2 / 3 : ℚ) ^ (2 * half) - 1)) :=
        ⟨scaled_value.1, by rw [scaled_value.2]; positivity⟩
      have result := unit_add_positive at_ratio_unit scaled_positive
      convert result using 1
      rw [pow_add]
      ring

private theorem reversingOneSubRatioPower_hasValue
    {exponent : ℕ} (exponent_positive : 0 < exponent) :
    HasValue 5 (1 - (2 / 3 : ℚ) ^ exponent)
      (shellSlopeGapFiveDepth exponent) := by
  have negative_value := neg_hasValue
    (shellRatio_pow_sub_one_hasValue exponent_positive)
  convert negative_value using 1
  ring

/-- Exact incoming-carry value on the `q=0,A=2` fibre. -/
theorem lengthThreeReversingTargetCarry_q0_A2_hasValue
    (offset : ℕ) :
    HasValue 5 (lengthThreeReversingTargetCarry 0 2 offset)
      (1 - (shellSlopeGapFiveDepth (offset + 1) : ℤ)) := by
  have coefficient_unit : IsUnit 5 (8 / 3 : ℚ) :=
    div_hasValue
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (8 : ℤ)))
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (3 : ℤ)))
  have at_one_unit : IsUnit 5 (3 - (8 / 3 : ℚ)) := by
    convert div_hasValue
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (1 : ℤ)))
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (3 : ℤ))) using 1 <;>
      norm_num
  have at_ratio_unit :
      IsUnit 5 (3 - (8 / 3 : ℚ) * (2 / 3 : ℚ)) := by
    convert div_hasValue
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (11 : ℤ)))
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (9 : ℤ))) using 1 <;>
      norm_num
  have core_unit :
      IsUnit 5 (3 - (8 / 3 : ℚ) * (2 / 3 : ℚ) ^ (offset + 1)) :=
    reversingRatioPowerAffine_unit 3 (8 / 3 : ℚ) coefficient_unit
      at_one_unit at_ratio_unit (by omega)
  have five_value : HasValue 5 (5 : ℚ) 1 := by
    convert primePower_hasValue (prime := 5) 1 using 1 <;> norm_num
  have gap_value := reversingOneSubRatioPower_hasValue
    (show 0 < offset + 1 by omega)
  have carry_eq :
      lengthThreeReversingTargetCarry 0 2 offset =
        5 * (3 - (8 / 3 : ℚ) * (2 / 3 : ℚ) ^ (offset + 1)) /
          (1 - (2 / 3 : ℚ) ^ (offset + 1)) := by
    rw [lengthThreeReversingTargetCarry]
    norm_num
    ring
  rw [carry_eq]
  have result := div_hasValue (mul_hasValue five_value core_unit) gap_value
  convert result using 1
  ring

/-- No target in the `q=0,A=2` fibre can be a five-adic unit. -/
theorem lengthThreeReversingTarget_q0_A2_not_fiveUnit
    (offset t : ℕ) :
    ¬IsUnit 5 (lengthThreeReversingTarget 0 2 offset t) := by
  intro target_unit
  have forced := lengthThreeReversingTarget_fiveUnit_forces_carry
    0 2 offset t target_unit
  have actual := lengthThreeReversingTargetCarry_q0_A2_hasValue offset
  have value_eq :
      1 - (shellSlopeGapFiveDepth (offset + 1) : ℤ) = 2 :=
    actual.2.symm.trans forced.2
  have depth_nonnegative :
      0 ≤ (shellSlopeGapFiveDepth (offset + 1) : ℤ) := by positivity
  omega

/-- Exact incoming-carry value on the `q=1,A=4` fibre. -/
theorem lengthThreeReversingTargetCarry_q1_A4_hasValue
    (offset : ℕ) :
    HasValue 5 (lengthThreeReversingTargetCarry 1 4 offset)
      (1 - (shellSlopeGapFiveDepth (offset + 1) : ℤ)) := by
  have coefficient_unit : IsUnit 5 (214 / 81 : ℚ) :=
    div_hasValue
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (214 : ℤ)))
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (81 : ℤ)))
  have at_one_unit : IsUnit 5 (3 - (214 / 81 : ℚ)) := by
    convert div_hasValue
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (29 : ℤ)))
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (81 : ℤ))) using 1 <;>
      norm_num
  have at_ratio_unit :
      IsUnit 5 (3 - (214 / 81 : ℚ) * (2 / 3 : ℚ)) := by
    convert div_hasValue
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (301 : ℤ)))
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (243 : ℤ))) using 1 <;>
      norm_num
  have core_unit :
      IsUnit 5 (3 - (214 / 81 : ℚ) * (2 / 3 : ℚ) ^ (offset + 1)) :=
    reversingRatioPowerAffine_unit 3 (214 / 81 : ℚ) coefficient_unit
      at_one_unit at_ratio_unit (by omega)
  have five_value : HasValue 5 (5 : ℚ) 1 := by
    convert primePower_hasValue (prime := 5) 1 using 1 <;> norm_num
  have gap_value := reversingOneSubRatioPower_hasValue
    (show 0 < offset + 1 by omega)
  have carry_eq :
      lengthThreeReversingTargetCarry 1 4 offset =
        5 * (3 - (214 / 81 : ℚ) * (2 / 3 : ℚ) ^ (offset + 1)) /
          (1 - (2 / 3 : ℚ) ^ (offset + 1)) := by
    rw [lengthThreeReversingTargetCarry]
    norm_num
    ring
  rw [carry_eq]
  have result := div_hasValue (mul_hasValue five_value core_unit) gap_value
  convert result using 1
  ring

/-- No target in the `q=1,A=4` fibre can be a five-adic unit. -/
theorem lengthThreeReversingTarget_q1_A4_not_fiveUnit
    (offset t : ℕ) :
    ¬IsUnit 5 (lengthThreeReversingTarget 1 4 offset t) := by
  intro target_unit
  have forced := lengthThreeReversingTarget_fiveUnit_forces_carry
    1 4 offset t target_unit
  have actual := lengthThreeReversingTargetCarry_q1_A4_hasValue offset
  have value_eq :
      1 - (shellSlopeGapFiveDepth (offset + 1) : ℤ) = 2 :=
    actual.2.symm.trans forced.2
  have depth_nonnegative :
      0 ≤ (shellSlopeGapFiveDepth (offset + 1) : ℤ) := by positivity
  omega

private theorem lengthThreeReversingTargetCarry_q1_A2_small_hasValue
    (offset : ℕ) (offset_lower : 2 ≤ offset) (offset_upper : offset ≤ 8) :
    HasValue 5 (lengthThreeReversingTargetCarry 1 2 offset)
      (if offset = 5 then 2 else 1) := by
  interval_cases offset
  · convert primePower_mul_int_div_int_hasValue (prime := 5) 1
      (by norm_num : ¬(5 : ℤ) ∣ 553) (by norm_num : ¬(5 : ℤ) ∣ 171) using 1 <;>
      norm_num [lengthThreeReversingTargetCarry]
  · convert primePower_mul_int_div_int_hasValue (prime := 5) 1
      (by norm_num : ¬(5 : ℤ) ∣ 367) (by norm_num : ¬(5 : ℤ) ∣ 117) using 1 <;>
      norm_num [lengthThreeReversingTargetCarry]
  · convert primePower_mul_int_div_int_hasValue (prime := 5) 1
      (by norm_num : ¬(5 : ℤ) ∣ 5857) (by norm_num : ¬(5 : ℤ) ∣ 1899) using 1 <;>
      norm_num [lengthThreeReversingTargetCarry]
  · convert primePower_mul_int_div_int_hasValue (prime := 5) 2
      (by norm_num : ¬(5 : ℤ) ∣ 731) (by norm_num : ¬(5 : ℤ) ∣ 1197) using 1 <;>
      norm_num [lengthThreeReversingTargetCarry]
  · convert primePower_mul_int_div_int_hasValue (prime := 5) 1
      (by norm_num : ¬(5 : ℤ) ∣ 56233) (by norm_num : ¬(5 : ℤ) ∣ 18531) using 1 <;>
      norm_num [lengthThreeReversingTargetCarry]
  · convert primePower_mul_int_div_int_hasValue (prime := 5) 1
      (by norm_num : ¬(5 : ℤ) ∣ 34303) (by norm_num : ¬(5 : ℤ) ∣ 11349) using 1 <;>
      norm_num [lengthThreeReversingTargetCarry]
  · convert primePower_mul_int_div_int_hasValue (prime := 5) 1
      (by norm_num : ¬(5 : ℤ) ∣ 520177) (by norm_num : ¬(5 : ℤ) ∣ 172539) using 1 <;>
      norm_num [lengthThreeReversingTargetCarry]

/-- Every target at the sole depth-two carry in the finite `p=0` row has value minus one. -/
theorem lengthThreeReversingTarget_q1_A2_offsetFive_hasValue
    (t : ℕ) :
    HasValue 5 (lengthThreeReversingTarget 1 2 5 t) (-1) := by
  have coefficient_unit : IsUnit 5 (-(731 / 1197 : ℚ)) :=
    neg_hasValue (div_hasValue
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (731 : ℤ)))
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (1197 : ℤ))))
  have at_one_unit : IsUnit 5 (1 - (-(731 / 1197 : ℚ))) := by
    convert div_hasValue
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (1928 : ℤ)))
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (1197 : ℤ))) using 1 <;>
      norm_num
  have at_ratio_unit :
      IsUnit 5 (1 - (-(731 / 1197 : ℚ)) * (2 / 3 : ℚ)) := by
    convert div_hasValue
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (5053 : ℤ)))
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (3591 : ℤ))) using 1 <;>
      norm_num
  have core_unit :
      IsUnit 5 (1 - (-(731 / 1197 : ℚ)) * (2 / 3 : ℚ) ^ t) := by
    by_cases t_zero : t = 0
    · subst t
      simpa using at_one_unit
    · exact reversingRatioPowerAffine_unit 1 (-(731 / 1197 : ℚ))
        coefficient_unit at_one_unit at_ratio_unit (Nat.zero_lt_of_ne_zero t_zero)
  have target_eq :
      lengthThreeReversingTarget 1 2 5 t =
        (1 - (-(731 / 1197 : ℚ)) * (2 / 3 : ℚ) ^ t) / 5 := by
    rw [lengthThreeReversingTarget]
    norm_num
    ring
  have five_value : HasValue 5 (5 : ℚ) 1 := by
    convert primePower_hasValue (prime := 5) 1 using 1 <;> norm_num
  rw [target_eq]
  have result := div_hasValue core_unit five_value
  convert result using 1
  ring

/-- The finite real `q=1,A=2,p=0` row contains no accepted target. -/
theorem lengthThreeReversingTarget_q1_A2_smallOffset_not_fiveUnit
    (offset t : ℕ) (offset_lower : 2 ≤ offset) (offset_upper : offset ≤ 8) :
    ¬IsUnit 5 (lengthThreeReversingTarget 1 2 offset t) := by
  intro target_unit
  have forced := lengthThreeReversingTarget_fiveUnit_forces_carry
    1 2 offset t target_unit
  have actual := lengthThreeReversingTargetCarry_q1_A2_small_hasValue
    offset offset_lower offset_upper
  have offset_eq : offset = 5 := by
    by_contra offset_ne
    have value_eq : (if offset = 5 then (2 : ℤ) else 1) = 2 :=
      actual.2.symm.trans forced.2
    simp [offset_ne] at value_eq
  subst offset
  have rejected := lengthThreeReversingTarget_q1_A2_offsetFive_hasValue t
  have impossible : (-1 : ℤ) = 0 := rejected.2.symm.trans target_unit.2
  omega

/-- Real and target guards reduce the reversing chamber to two unbounded `q=1,A=2` rays. -/
theorem lengthThreeReversing_realTrap_targetUnit_parameter_cut
    (p q A offset t : ℕ) (A_positive : 0 < A)
    (source_mem :
      lengthThreeReversingNormalizedSource p q A offset ∈
        Set.Icc (1 / 5) (1 / 2))
    (target_unit : IsUnit 5 (lengthThreeReversingTarget q A offset t)) :
    q = 1 ∧ A = 2 ∧
      ((p = 1 ∧ 3 ≤ offset) ∨ (p = 2 ∧ 6 ≤ offset)) ∧
      Odd (offset + 2) := by
  have cell :=
    (lengthThreeReversingNormalizedSource_mem_realTrap_iff
      p q A offset A_positive).1 source_mem
  have A_le := lengthThreeReversingNormalizedSource_realTrap_forces_A_le_four
    p q A offset A_positive source_mem
  have A_even := lengthThreeReversingTarget_fiveUnit_forces_A_even
    p q t A_positive target_unit
  rcases A_even with ⟨half, A_eq⟩
  have A_two_or_four : A = 2 ∨ A = 4 := by omega
  rcases cell with ⟨q_zero, row⟩ | ⟨q_one, row⟩ | ⟨q_two, A_one, _, _⟩
  · subst q
    rcases A_two_or_four with rfl | rfl
    · exact (lengthThreeReversingTarget_q0_A2_not_fiveUnit
        offset t target_unit).elim
    · norm_num at row
  · subst q
    rcases A_two_or_four with rfl | rfl
    · norm_num at row
      rcases row with ⟨p_zero, offset_lower, offset_upper⟩ |
          ⟨p_one, offset_lower⟩ | ⟨p_two, offset_lower⟩
      · subst p
        exact (lengthThreeReversingTarget_q1_A2_smallOffset_not_fiveUnit
          offset t offset_lower offset_upper target_unit).elim
      · subst p
        have next_odd := lengthThreeReversingTarget_fiveUnit_forces_nextGap_odd
          1 1 t (A := 2) (offset := offset) (Or.inl rfl) target_unit
        exact ⟨rfl, rfl, Or.inl ⟨rfl, offset_lower⟩, next_odd⟩
      · subst p
        have next_odd := lengthThreeReversingTarget_fiveUnit_forces_nextGap_odd
          2 1 t (A := 2) (offset := offset) (Or.inl rfl) target_unit
        exact ⟨rfl, rfl, Or.inr ⟨rfl, offset_lower⟩, next_odd⟩
    · exact (lengthThreeReversingTarget_q1_A4_not_fiveUnit
        offset t target_unit).elim
  · omega

/-- Source numerator on the sole surviving reversing fibre. -/
def lengthThreeReversingSourceCore (offset : ℕ) : ℚ :=
  1 + (16 / 9 : ℚ) * (2 / 3 : ℚ) ^ (offset + 1)

/-- Carry numerator after removing its leading factor five on the surviving fibre. -/
def lengthThreeReversingCarryCore (offset : ℕ) : ℚ :=
  3 - (22 / 9 : ℚ) * (2 / 3 : ℚ) ^ (offset + 1)

theorem lengthThreeReversingSource_q1_A2_eq_core
    (p offset : ℕ) :
    lengthThreeReversingNormalizedSource p 1 2 offset =
      lengthThreeReversingSourceCore offset /
        (27 * (2 / 3 : ℚ) ^ (p + 4) *
          (1 - (2 / 3 : ℚ) ^ (offset + 1))) := by
  rw [lengthThreeReversingNormalizedSource,
    lengthThreeReversingSourceCore]
  norm_num
  ring

theorem lengthThreeReversingTargetCarry_q1_A2_eq_core
    (offset : ℕ) :
    lengthThreeReversingTargetCarry 1 2 offset =
      5 * lengthThreeReversingCarryCore offset /
        (1 - (2 / 3 : ℚ) ^ (offset + 1)) := by
  rw [lengthThreeReversingTargetCarry,
    lengthThreeReversingCarryCore]
  norm_num
  ring

private theorem reversingUnit_pow
    {value : ℚ} (value_unit : IsUnit 5 value) (exponent : ℕ) :
    IsUnit 5 (value ^ exponent) := by
  refine ⟨pow_ne_zero exponent value_unit.1, ?_⟩
  rw [padicValRat.pow, value_unit.2]
  simp

/-- A source unit fixes the surviving source core at exactly the gap carry depth. -/
theorem lengthThreeReversingSource_q1_A2_unit_forces_core
    (p offset : ℕ)
    (source_unit :
      IsUnit 5 (lengthThreeReversingNormalizedSource p 1 2 offset)) :
    HasValue 5 (lengthThreeReversingSourceCore offset)
      (shellSlopeGapFiveDepth (offset + 1)) := by
  have gap_ne : 1 - (2 / 3 : ℚ) ^ (offset + 1) ≠ 0 := by
    have power_lt : (2 / 3 : ℚ) ^ (offset + 1) < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    linarith
  have ratio_unit : IsUnit 5 (2 / 3 : ℚ) :=
    div_hasValue
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (2 : ℤ)))
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (3 : ℤ)))
  have baseline_unit : IsUnit 5 (27 * (2 / 3 : ℚ) ^ (p + 4)) :=
    mul_hasValue
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (27 : ℤ)))
      (reversingUnit_pow ratio_unit (p + 4))
  have gap_value := reversingOneSubRatioPower_hasValue
    (show 0 < offset + 1 by omega)
  have core_eq :
      lengthThreeReversingNormalizedSource p 1 2 offset *
          (27 * (2 / 3 : ℚ) ^ (p + 4)) *
          (1 - (2 / 3 : ℚ) ^ (offset + 1)) =
        lengthThreeReversingSourceCore offset := by
    rw [lengthThreeReversingSource_q1_A2_eq_core]
    field_simp [gap_ne]
  have core_value :=
    mul_hasValue (mul_hasValue source_unit baseline_unit) gap_value
  rw [core_eq] at core_value
  convert core_value using 1
  ring

/-- A depth-two target carry fixes the reduced carry core one level above the gap. -/
theorem lengthThreeReversingTargetCarry_q1_A2_forces_core
    (offset : ℕ)
    (carry_value : HasValue 5 (lengthThreeReversingTargetCarry 1 2 offset) 2) :
    HasValue 5 (lengthThreeReversingCarryCore offset)
      ((shellSlopeGapFiveDepth (offset + 1) : ℤ) + 1) := by
  have gap_ne : 1 - (2 / 3 : ℚ) ^ (offset + 1) ≠ 0 := by
    have power_lt : (2 / 3 : ℚ) ^ (offset + 1) < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    linarith
  have gap_value := reversingOneSubRatioPower_hasValue
    (show 0 < offset + 1 by omega)
  have five_value : HasValue 5 (5 : ℚ) 1 := by
    convert primePower_hasValue (prime := 5) 1 using 1 <;> norm_num
  have core_eq :
      lengthThreeReversingTargetCarry 1 2 offset *
            (1 - (2 / 3 : ℚ) ^ (offset + 1)) / 5 =
        lengthThreeReversingCarryCore offset := by
    rw [lengthThreeReversingTargetCarry_q1_A2_eq_core]
    field_simp [gap_ne]
  have core_value := div_hasValue (mul_hasValue carry_value gap_value) five_value
  rw [core_eq] at core_value
  convert core_value using 1
  ring

/-- Source and target units force the surviving gap to generic carry depth one. -/
theorem lengthThreeReversing_q1_A2_units_force_gapDepth_one
    (p offset t : ℕ)
    (source_unit :
      IsUnit 5 (lengthThreeReversingNormalizedSource p 1 2 offset))
    (target_unit : IsUnit 5 (lengthThreeReversingTarget 1 2 offset t)) :
    shellSlopeGapFiveDepth (offset + 1) = 1 := by
  let gapDepth := shellSlopeGapFiveDepth (offset + 1)
  have source_core_value :=
    lengthThreeReversingSource_q1_A2_unit_forces_core p offset source_unit
  have carry_value := lengthThreeReversingTarget_fiveUnit_forces_carry
    1 2 offset t target_unit
  have carry_core_value :=
    lengthThreeReversingTargetCarry_q1_A2_forces_core offset carry_value
  have elevenEighths_unit : IsUnit 5 (11 / 8 : ℚ) :=
    div_hasValue
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (11 : ℤ)))
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (8 : ℤ)))
  have scaled_source_value := mul_hasValue elevenEighths_unit source_core_value
  have sum_value := add_hasValue_right carry_core_value scaled_source_value (by omega)
  have sum_eq :
      lengthThreeReversingCarryCore offset +
          (11 / 8 : ℚ) * lengthThreeReversingSourceCore offset =
        35 / 8 := by
    rw [lengthThreeReversingCarryCore,
      lengthThreeReversingSourceCore]
    ring
  rw [sum_eq] at sum_value
  have constant_value : HasValue 5 (35 / 8 : ℚ) 1 := by
    have seven_unit : IsUnit 5 (7 : ℚ) :=
      intCast_isUnit_of_not_dvd (by norm_num)
    have five_value : HasValue 5 (5 : ℚ) 1 := by
      convert primePower_hasValue (prime := 5) 1 using 1 <;> norm_num
    have eight_unit : IsUnit 5 (8 : ℚ) :=
      intCast_isUnit_of_not_dvd (by norm_num)
    convert div_hasValue (mul_hasValue five_value seven_unit) eight_unit using 1 <;>
      norm_num
  have depth_eq : (gapDepth : ℤ) = 1 := by
    simpa [gapDepth] using sum_value.2.symm.trans constant_value.2
  exact_mod_cast depth_eq

/-- A reversing target unit forces the collision source to be a five-adic unit. -/
theorem lengthThreeReversingTarget_fiveUnit_forces_source_fiveUnit
    (p q A offset t : ℕ)
    (target_unit : IsUnit 5 (lengthThreeReversingTarget q A offset t)) :
    IsUnit 5 (lengthThreeReversingNormalizedSource p q A offset) := by
  have right_target := (lengthThreeReversing_commonTarget p q A offset t).2
  have output_unit :
      IsUnit 5
        (shellRun (lengthThreeReversingRight p q t A 1)
          (lengthThreeReversingNormalizedSource p q A offset)) := by
    rw [right_target]
    exact target_unit
  have prefixes :=
    (shellPrefixesUnit_iff (lengthThreeReversingRight p q t A 1)
      (lengthThreeReversingNormalizedSource p q A offset)).2 output_unit
  exact prefixes [] (lengthThreeReversingRight p q t A 1) (by simp)

/-- A target unit alone forces generic gap depth on the surviving fibre. -/
theorem lengthThreeReversingTarget_q1_A2_fiveUnit_forces_gapDepth_one
    (p offset t : ℕ)
    (target_unit : IsUnit 5 (lengthThreeReversingTarget 1 2 offset t)) :
    shellSlopeGapFiveDepth (offset + 1) = 1 := by
  have source_unit :=
    lengthThreeReversingTarget_fiveUnit_forces_source_fiveUnit
      p 1 2 offset t target_unit
  exact lengthThreeReversing_q1_A2_units_force_gapDepth_one
    p offset t source_unit target_unit

private theorem reversingShellSlopeGapFiveDepth_eq_one_iff
    {gap : ℕ} (gap_positive : 0 < gap) :
    shellSlopeGapFiveDepth gap = 1 ↔ Even gap ∧ ¬5 ∣ gap / 2 := by
  constructor
  · intro depth_one
    have gap_not_odd : ¬Odd gap := by
      intro gap_odd
      rw [shellSlopeGapFiveDepth, if_pos gap_odd] at depth_one
      omega
    have gap_even : Even gap := Nat.not_odd_iff_even.mp gap_not_odd
    have half_ne : gap / 2 ≠ 0 := by
      obtain ⟨half, gap_eq⟩ := gap_even
      omega
    have half_value : padicValNat 5 (gap / 2) = 0 := by
      rw [shellSlopeGapFiveDepth, if_neg gap_not_odd] at depth_one
      omega
    have half_not_dvd : ¬5 ∣ gap / 2 := by
      intro half_dvd
      have value_ne := (dvd_iff_padicValNat_ne_zero half_ne).1 half_dvd
      exact value_ne half_value
    exact ⟨gap_even, half_not_dvd⟩
  · rintro ⟨gap_even, half_not_dvd⟩
    have gap_not_odd : ¬Odd gap := Nat.not_odd_iff_even.mpr gap_even
    rw [shellSlopeGapFiveDepth, if_neg gap_not_odd,
      padicValNat.eq_zero_of_not_dvd half_not_dvd]

private theorem reversingShellSlopeGapFiveDepth_add_twoFifty_eq_one
    (offset : ℕ) (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 1) :
    shellSlopeGapFiveDepth (offset + 250 + 1) = 1 := by
  have original_class :=
    (reversingShellSlopeGapFiveDepth_eq_one_iff
      (show 0 < offset + 1 by omega)).1 gap_depth
  obtain ⟨half, gap_eq⟩ := original_class.1
  have shifted_even : Even (offset + 250 + 1) :=
    ⟨half + 125, by omega⟩
  have shifted_half_eq : (offset + 250 + 1) / 2 = half + 125 := by omega
  have original_half_eq : (offset + 1) / 2 = half := by omega
  have shifted_half_not_dvd : ¬5 ∣ (offset + 250 + 1) / 2 := by
    rw [shifted_half_eq, Nat.dvd_iff_mod_eq_zero]
    rw [Nat.dvd_iff_mod_eq_zero, original_half_eq] at original_class
    omega
  exact (reversingShellSlopeGapFiveDepth_eq_one_iff
    (show 0 < offset + 250 + 1 by omega)).2
      ⟨shifted_even, shifted_half_not_dvd⟩

private theorem reversingShellSlopeGapFiveDepth_add_twoFifty_mul_eq_one
    (offset multiplier : ℕ)
    (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 1) :
    shellSlopeGapFiveDepth (offset + 250 * multiplier + 1) = 1 := by
  induction multiplier with
  | zero => simpa using gap_depth
  | succ multiplier induction =>
      rw [Nat.mul_succ, ← Nat.add_assoc]
      exact reversingShellSlopeGapFiveDepth_add_twoFifty_eq_one
        (offset + 250 * multiplier) induction

private theorem reversingShellSlopeGapFiveDepth_twoFifty :
    shellSlopeGapFiveDepth 250 = 4 := by
  rw [shellSlopeGapFiveDepth, if_neg (by norm_num : ¬Odd 250)]
  norm_num
  rw [show (125 : ℕ) = 5 ^ 3 by norm_num, padicValNat.prime_pow]

/-- Exact Möbius transport of the surviving reversing carry under a gap shift. -/
theorem lengthThreeReversingTargetCarry_q1_A2_offset_add_sub
    (offset shift : ℕ) (shift_positive : 0 < shift) :
    lengthThreeReversingTargetCarry 1 2 (offset + shift) -
        lengthThreeReversingTargetCarry 1 2 offset =
      ((2 / 3 : ℚ) ^ (offset + 1) * (25 / 9 : ℚ) *
          ((2 / 3 : ℚ) ^ shift - 1)) /
        ((1 - (2 / 3 : ℚ) ^ (offset + shift + 1)) *
          (1 - (2 / 3 : ℚ) ^ (offset + 1))) := by
  have base_gap_ne : 1 - (2 / 3 : ℚ) ^ (offset + 1) ≠ 0 := by
    have power_lt : (2 / 3 : ℚ) ^ (offset + 1) < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    linarith
  have shifted_gap_ne :
      1 - (2 / 3 : ℚ) ^ (offset + shift + 1) ≠ 0 := by
    have power_lt : (2 / 3 : ℚ) ^ (offset + shift + 1) < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    linarith
  have shifted_gap_factor_ne :
      1 - (2 / 3 : ℚ) ^ (offset + 1) * (2 / 3 : ℚ) ^ shift ≠ 0 := by
    rw [← pow_add, ← show offset + shift + 1 = offset + 1 + shift by omega]
    exact shifted_gap_ne
  rw [lengthThreeReversingTargetCarry_q1_A2_eq_core,
    lengthThreeReversingTargetCarry_q1_A2_eq_core,
    lengthThreeReversingCarryCore,
    lengthThreeReversingCarryCore]
  rw [show offset + shift + 1 = offset + 1 + shift by omega, pow_add]
  field_simp [base_gap_ne, shifted_gap_ne, shifted_gap_factor_ne]
  ring

/-- Exact five-adic value of the surviving carry's gap transport. -/
theorem lengthThreeReversingTargetCarry_q1_A2_offset_add_sub_hasValue
    (offset shift : ℕ) (shift_positive : 0 < shift) :
    HasValue 5
      (lengthThreeReversingTargetCarry 1 2 (offset + shift) -
        lengthThreeReversingTargetCarry 1 2 offset)
      (2 + (shellSlopeGapFiveDepth shift : ℤ) -
        shellSlopeGapFiveDepth (offset + shift + 1) -
        shellSlopeGapFiveDepth (offset + 1)) := by
  have ratio_unit : IsUnit 5 (2 / 3 : ℚ) :=
    div_hasValue
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (2 : ℤ)))
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (3 : ℤ)))
  have power_unit := reversingUnit_pow ratio_unit (offset + 1)
  have constant_value : HasValue 5 (25 / 9 : ℚ) 2 := by
    have twentyFive_value : HasValue 5 (25 : ℚ) 2 := by
      convert primePower_hasValue (prime := 5) 2 using 1 <;> norm_num
    have nine_unit : IsUnit 5 (9 : ℚ) :=
      intCast_isUnit_of_not_dvd (by norm_num)
    exact div_hasValue twentyFive_value nine_unit
  have shift_value := shellRatio_pow_sub_one_hasValue shift_positive
  have shifted_gap_value := reversingOneSubRatioPower_hasValue
    (show 0 < offset + shift + 1 by omega)
  have base_gap_value := reversingOneSubRatioPower_hasValue
    (show 0 < offset + 1 by omega)
  have numerator_value :=
    mul_hasValue (mul_hasValue power_unit constant_value) shift_value
  have denominator_value := mul_hasValue shifted_gap_value base_gap_value
  rw [lengthThreeReversingTargetCarry_q1_A2_offset_add_sub
    offset shift shift_positive]
  have result := div_hasValue numerator_value denominator_value
  convert result using 1
  ring

/-- On the generic source-unit fibre, a 250-gap shift changes the carry at value four. -/
theorem lengthThreeReversingTargetCarry_q1_A2_offset_add_twoFifty_sub_hasValue
    (offset : ℕ) (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 1) :
    HasValue 5
      (lengthThreeReversingTargetCarry 1 2 (offset + 250) -
        lengthThreeReversingTargetCarry 1 2 offset) 4 := by
  have shifted_depth :=
    reversingShellSlopeGapFiveDepth_add_twoFifty_eq_one offset gap_depth
  have difference_value :=
    lengthThreeReversingTargetCarry_q1_A2_offset_add_sub_hasValue
      offset 250 (by norm_num)
  rw [reversingShellSlopeGapFiveDepth_twoFifty, shifted_depth, gap_depth] at difference_value
  norm_num at difference_value ⊢
  exact difference_value

private theorem reversingHasValue_of_sub_higher_iff
    {later earlier : ℚ} {lower higher : ℤ} (lower_lt_higher : lower < higher)
    (difference_value : HasValue 5 (later - earlier) higher) :
    HasValue 5 later lower ↔ HasValue 5 earlier lower := by
  have reverse_value : HasValue 5 (earlier - later) higher := by
    convert neg_hasValue difference_value using 1
    ring
  constructor
  · intro later_value
    have earlier_value := add_hasValue_right reverse_value later_value lower_lt_higher
    convert earlier_value using 1
    ring
  · intro earlier_value
    have later_value := add_hasValue_right difference_value earlier_value lower_lt_higher
    convert later_value using 1
    ring

/-- Exact depth-two carry is 250-periodic on the generic surviving fibre. -/
theorem lengthThreeReversingTargetCarry_q1_A2_add_twoFifty_hasValue_two_iff
    (offset : ℕ) (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 1) :
    HasValue 5 (lengthThreeReversingTargetCarry 1 2 (offset + 250)) 2 ↔
      HasValue 5 (lengthThreeReversingTargetCarry 1 2 offset) 2 := by
  exact reversingHasValue_of_sub_higher_iff (by norm_num)
    (lengthThreeReversingTargetCarry_q1_A2_offset_add_twoFifty_sub_hasValue
      offset gap_depth)

/-- Target acceptance is 250-periodic in the surviving total-gap coordinate. -/
theorem lengthThreeReversingTarget_q1_A2_offset_add_twoFifty_fiveUnit_iff
    (offset t : ℕ) (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 1) :
    IsUnit 5 (lengthThreeReversingTarget 1 2 (offset + 250) t) ↔
      IsUnit 5 (lengthThreeReversingTarget 1 2 offset t) := by
  rw [lengthThreeReversingTarget_eq_terminalCarryTarget,
    lengthThreeReversingTarget_eq_terminalCarryTarget]
  exact terminalCarryTarget_carry_sub_fiveUnit_iff t (by norm_num)
    (lengthThreeReversingTargetCarry_q1_A2_offset_add_twoFifty_sub_hasValue
      offset gap_depth)

/-- Every generic surviving carry reduces to one of 250 gap residues. -/
theorem lengthThreeReversingTargetCarry_q1_A2_hasValue_two_iff_mod_twoFifty
    (offset : ℕ) (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 1) :
    HasValue 5 (lengthThreeReversingTargetCarry 1 2 offset) 2 ↔
      HasValue 5
        (lengthThreeReversingTargetCarry 1 2 (offset % 250)) 2 := by
  have original_class :=
    (reversingShellSlopeGapFiveDepth_eq_one_iff
      (show 0 < offset + 1 by omega)).1 gap_depth
  have residue_even : Even (offset % 250 + 1) := by
    obtain ⟨half, gap_eq⟩ := original_class.1
    refine ⟨(offset % 250 + 1) / 2, ?_⟩
    omega
  have residue_half_not_dvd : ¬5 ∣ (offset % 250 + 1) / 2 := by
    rw [Nat.dvd_iff_mod_eq_zero] at original_class ⊢
    omega
  have residue_gap_depth : shellSlopeGapFiveDepth (offset % 250 + 1) = 1 :=
    (reversingShellSlopeGapFiveDepth_eq_one_iff
      (show 0 < offset % 250 + 1 by omega)).2
        ⟨residue_even, residue_half_not_dvd⟩
  have periodic (base repetitions : ℕ)
      (base_depth : shellSlopeGapFiveDepth (base + 1) = 1) :
      HasValue 5
          (lengthThreeReversingTargetCarry 1 2
            (base + 250 * repetitions)) 2 ↔
        HasValue 5 (lengthThreeReversingTargetCarry 1 2 base) 2 := by
    induction repetitions with
    | zero => simp
    | succ repetitions induction =>
        have current_depth :
            shellSlopeGapFiveDepth (base + 250 * repetitions + 1) = 1 := by
          exact reversingShellSlopeGapFiveDepth_add_twoFifty_mul_eq_one
            base repetitions base_depth
        rw [Nat.mul_succ, ← Nat.add_assoc,
          lengthThreeReversingTargetCarry_q1_A2_add_twoFifty_hasValue_two_iff
            (base + 250 * repetitions) current_depth]
        exact induction
  have decomposition : offset % 250 + 250 * (offset / 250) = offset := by omega
  have reduced := periodic (offset % 250) (offset / 250) residue_gap_depth
  rwa [decomposition] at reduced

/-- Every generic surviving target reduces to one of 250 gap residues. -/
theorem lengthThreeReversingTarget_q1_A2_fiveUnit_iff_mod_twoFifty
    (offset t : ℕ) (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 1) :
    IsUnit 5 (lengthThreeReversingTarget 1 2 offset t) ↔
      IsUnit 5 (lengthThreeReversingTarget 1 2 (offset % 250) t) := by
  have original_class :=
    (reversingShellSlopeGapFiveDepth_eq_one_iff
      (show 0 < offset + 1 by omega)).1 gap_depth
  have residue_even : Even (offset % 250 + 1) := by
    obtain ⟨half, gap_eq⟩ := original_class.1
    refine ⟨(offset % 250 + 1) / 2, ?_⟩
    omega
  have residue_half_not_dvd : ¬5 ∣ (offset % 250 + 1) / 2 := by
    rw [Nat.dvd_iff_mod_eq_zero] at original_class ⊢
    omega
  have residue_gap_depth : shellSlopeGapFiveDepth (offset % 250 + 1) = 1 :=
    (reversingShellSlopeGapFiveDepth_eq_one_iff
      (show 0 < offset % 250 + 1 by omega)).2
        ⟨residue_even, residue_half_not_dvd⟩
  have periodic (base repetitions : ℕ)
      (base_depth : shellSlopeGapFiveDepth (base + 1) = 1) :
      IsUnit 5
          (lengthThreeReversingTarget 1 2
            (base + 250 * repetitions) t) ↔
        IsUnit 5 (lengthThreeReversingTarget 1 2 base t) := by
    induction repetitions with
    | zero => simp
    | succ repetitions induction =>
        have current_depth :
            shellSlopeGapFiveDepth (base + 250 * repetitions + 1) = 1 := by
          exact reversingShellSlopeGapFiveDepth_add_twoFifty_mul_eq_one
            base repetitions base_depth
        rw [Nat.mul_succ, ← Nat.add_assoc,
          lengthThreeReversingTarget_q1_A2_offset_add_twoFifty_fiveUnit_iff
            (base + 250 * repetitions) t current_depth]
        exact induction
  have decomposition : offset % 250 + 250 * (offset / 250) = offset := by omega
  have reduced := periodic (offset % 250) (offset / 250) residue_gap_depth
  rwa [decomposition] at reduced

/-- Terminal acceptance always reduces to ten waits; either accepted endpoint supplies the
forced depth-two carry needed by the generic periodicity theorem. -/
theorem lengthThreeReversingTarget_fiveUnit_iff_mod_ten_unconditional
    (q A offset t : ℕ) :
    IsUnit 5 (lengthThreeReversingTarget q A offset t) ↔
      IsUnit 5 (lengthThreeReversingTarget q A offset (t % 10)) := by
  constructor
  · intro target_unit
    have carry_value := lengthThreeReversingTarget_fiveUnit_forces_carry
      q A offset t target_unit
    exact (lengthThreeReversingTarget_fiveUnit_iff_mod_ten
      q A offset t carry_value).1 target_unit
  · intro residue_unit
    have carry_value := lengthThreeReversingTarget_fiveUnit_forces_carry
      q A offset (t % 10) residue_unit
    exact (lengthThreeReversingTarget_fiveUnit_iff_mod_ten
      q A offset t carry_value).2 residue_unit

private theorem reversingPadicValInt_five_eq_two_iff (value : ℤ) :
    padicValInt 5 value = 2 ↔ (25 : ℤ) ∣ value ∧ ¬(125 : ℤ) ∣ value := by
  constructor
  · intro value_eq
    have value_ne : value ≠ 0 := by
      intro value_zero
      subst value
      norm_num at value_eq
    have square_dvd : (5 : ℤ) ^ 2 ∣ value :=
      (padicValInt_dvd_iff 2 value).2 (Or.inr (by rw [value_eq]))
    have cube_not_dvd : ¬(5 : ℤ) ^ 3 ∣ value := by
      intro cube_dvd
      rcases (padicValInt_dvd_iff 3 value).1 cube_dvd with impossible | three_le
      · exact value_ne impossible
      · rw [value_eq] at three_le
        omega
    norm_num at square_dvd cube_not_dvd ⊢
    exact ⟨square_dvd, cube_not_dvd⟩
  · rintro ⟨square_dvd, cube_not_dvd⟩
    have value_ne : value ≠ 0 := by
      intro value_zero
      subst value
      exact cube_not_dvd (dvd_zero _)
    have square_power_dvd : (5 : ℤ) ^ 2 ∣ value := by
      norm_num at square_dvd ⊢
      exact square_dvd
    have two_le : 2 ≤ padicValInt 5 value := by
      rcases (padicValInt_dvd_iff 2 value).1 square_power_dvd with impossible | two_le
      · exact (value_ne impossible).elim
      · exact two_le
    have not_three_le : ¬3 ≤ padicValInt 5 value := by
      intro three_le
      apply cube_not_dvd
      have cube_power_dvd := (padicValInt_dvd_iff 3 value).2 (Or.inr three_le)
      norm_num at cube_power_dvd ⊢
      exact cube_power_dvd
    omega

private theorem reversingPadicValInt_five_cast_eq_two_iff (value : ℤ) :
    (padicValInt 5 value : ℤ) = 2 ↔
      (25 : ℤ) ∣ value ∧ ¬(125 : ℤ) ∣ value := by
  norm_cast
  exact reversingPadicValInt_five_eq_two_iff value

/-- The twenty gap classes with exact depth-two incoming carry. -/
def lengthThreeReversingCarryResidue (offset : ℕ) : Prop :=
  let gapResidue := (offset + 1) % 250
  gapResidue = 6 ∨ gapResidue = 16 ∨ gapResidue = 36 ∨
    gapResidue = 46 ∨ gapResidue = 56 ∨ gapResidue = 66 ∨
    gapResidue = 86 ∨ gapResidue = 96 ∨ gapResidue = 106 ∨
    gapResidue = 116 ∨ gapResidue = 136 ∨ gapResidue = 146 ∨
    gapResidue = 156 ∨ gapResidue = 166 ∨ gapResidue = 186 ∨
    gapResidue = 196 ∨ gapResidue = 206 ∨ gapResidue = 216 ∨
    gapResidue = 236 ∨ gapResidue = 246

/-- Exact depth-two carry is precisely the displayed twenty gap classes modulo 250. -/
theorem lengthThreeReversingTargetCarry_q1_A2_hasValue_two_iff_residue
    (offset : ℕ) (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 1) :
    HasValue 5 (lengthThreeReversingTargetCarry 1 2 offset) 2 ↔
      lengthThreeReversingCarryResidue offset := by
  rw [lengthThreeReversingTargetCarry_q1_A2_hasValue_two_iff_mod_twoFifty
    offset gap_depth]
  generalize residue_eq : offset % 250 = residue
  have residue_lt : residue < 250 := by
    have := Nat.mod_lt offset (by norm_num : 0 < 250)
    omega
  have original_class :=
    (reversingShellSlopeGapFiveDepth_eq_one_iff
      (show 0 < offset + 1 by omega)).1 gap_depth
  have residue_even : Even (residue + 1) := by
    obtain ⟨half, gap_eq⟩ := original_class.1
    exact ⟨(residue + 1) / 2, by omega⟩
  have residue_half_not_dvd : ¬5 ∣ (residue + 1) / 2 := by
    rw [Nat.dvd_iff_mod_eq_zero] at original_class ⊢
    omega
  have gap_mod_eq : (offset + 1) % 250 = (residue + 1) % 250 := by
    simp [Nat.add_mod, residue_eq]
  rw [lengthThreeReversingCarryResidue, gap_mod_eq]
  interval_cases residue <;>
    norm_num at residue_even <;>
    norm_num at residue_half_not_dvd <;>
    norm_num [lengthThreeReversingTargetCarry, HasValue, padicValRat,
      padicValInt.eq_zero_of_not_dvd, padicValNat.eq_zero_of_not_dvd,
      padicValNat_self, padicValNat.mul, padicValNat.prime_pow,
      reversingPadicValInt_five_eq_two_iff,
      reversingPadicValInt_five_cast_eq_two_iff]

/-- Exact accepted gap/wait language on the surviving reversing fibre. -/
def lengthThreeReversingAcceptedResidue (offset t : ℕ) : Prop :=
  let gapResidue := (offset + 1) % 250
  let waitResidue := t % 10
  (gapResidue = 16 ∧
      (waitResidue = 0 ∨ waitResidue = 2 ∨ waitResidue = 4 ∨ waitResidue = 8)) ∨
    (gapResidue = 36 ∧
      (waitResidue = 3 ∨ waitResidue = 5 ∨ waitResidue = 7 ∨ waitResidue = 9)) ∨
    (gapResidue = 66 ∧
      (waitResidue = 0 ∨ waitResidue = 2 ∨ waitResidue = 4 ∨ waitResidue = 6)) ∨
    (gapResidue = 86 ∧
      (waitResidue = 1 ∨ waitResidue = 3 ∨ waitResidue = 5 ∨ waitResidue = 7)) ∨
    (gapResidue = 116 ∧
      (waitResidue = 2 ∨ waitResidue = 4 ∨ waitResidue = 6 ∨ waitResidue = 8)) ∨
    (gapResidue = 136 ∧
      (waitResidue = 1 ∨ waitResidue = 3 ∨ waitResidue = 5 ∨ waitResidue = 9)) ∨
    (gapResidue = 166 ∧
      (waitResidue = 0 ∨ waitResidue = 4 ∨ waitResidue = 6 ∨ waitResidue = 8)) ∨
    (gapResidue = 186 ∧
      (waitResidue = 1 ∨ waitResidue = 3 ∨ waitResidue = 7 ∨ waitResidue = 9)) ∨
    (gapResidue = 216 ∧
      (waitResidue = 0 ∨ waitResidue = 2 ∨ waitResidue = 6 ∨ waitResidue = 8)) ∨
    (gapResidue = 236 ∧
      (waitResidue = 1 ∨ waitResidue = 5 ∨ waitResidue = 7 ∨ waitResidue = 9))

private theorem lengthThreeReversingAcceptedResidue_mod
    (offset t : ℕ) :
    lengthThreeReversingAcceptedResidue (offset % 250) (t % 10) ↔
      lengthThreeReversingAcceptedResidue offset t := by
  simp only [lengthThreeReversingAcceptedResidue]
  simp [Nat.add_mod]

private theorem lengthThreeReversingAcceptedResidue_offset_lower
    {offset t : ℕ} (accepted : lengthThreeReversingAcceptedResidue offset t) :
    15 ≤ offset := by
  have residue_le : (offset + 1) % 250 ≤ offset + 1 := Nat.mod_le _ _
  rcases accepted with ⟨gap_eq, _⟩ | ⟨gap_eq, _⟩ | ⟨gap_eq, _⟩ |
      ⟨gap_eq, _⟩ | ⟨gap_eq, _⟩ | ⟨gap_eq, _⟩ |
      ⟨gap_eq, _⟩ | ⟨gap_eq, _⟩ | ⟨gap_eq, _⟩ |
      ⟨gap_eq, _⟩ <;>
    omega

private theorem lengthThreeReversing_bounded_targetUnit_forces_residue
    (offset t : ℕ) (offset_lt : offset < 250) (t_lt : t < 10)
    (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 1)
    (target_unit : IsUnit 5 (lengthThreeReversingTarget 1 2 offset t)) :
    lengthThreeReversingAcceptedResidue offset t := by
  have carry_value := lengthThreeReversingTarget_fiveUnit_forces_carry
    1 2 offset t target_unit
  have carry_residue :=
    (lengthThreeReversingTargetCarry_q1_A2_hasValue_two_iff_residue
      offset gap_depth).1 carry_value
  interval_cases offset <;>
    norm_num [lengthThreeReversingCarryResidue] at carry_residue <;>
    interval_cases t <;>
    norm_num [lengthThreeReversingTarget, HasValue, padicValRat,
      padicValInt.eq_zero_of_not_dvd, padicValNat.eq_zero_of_not_dvd,
      padicValNat_self, padicValNat.mul, padicValNat.prime_pow] at target_unit <;>
    norm_num [lengthThreeReversingAcceptedResidue]

private theorem lengthThreeReversing_bounded_residue_forces_targetUnit
    (offset t : ℕ) (offset_lt : offset < 250) (t_lt : t < 10)
    (accepted : lengthThreeReversingAcceptedResidue offset t) :
    IsUnit 5 (lengthThreeReversingTarget 1 2 offset t) := by
  interval_cases offset <;>
    norm_num [lengthThreeReversingAcceptedResidue] at accepted <;>
    interval_cases t <;>
    norm_num at accepted <;>
    norm_num [lengthThreeReversingTarget, HasValue, padicValRat,
      padicValInt.eq_zero_of_not_dvd, padicValNat.eq_zero_of_not_dvd,
      padicValNat_self, padicValNat.mul, padicValNat.prime_pow]

/-- Target acceptance is exactly the ten-by-four affine residue families displayed above. -/
theorem lengthThreeReversingTarget_q1_A2_fiveUnit_iff_residue
    (offset t : ℕ) :
    IsUnit 5 (lengthThreeReversingTarget 1 2 offset t) ↔
      lengthThreeReversingAcceptedResidue offset t := by
  let offsetResidue := offset % 250
  let waitResidue := t % 10
  have offsetResidue_lt : offsetResidue < 250 := Nat.mod_lt offset (by norm_num)
  have waitResidue_lt : waitResidue < 10 := Nat.mod_lt t (by norm_num)
  have residue_equivalence :=
    lengthThreeReversingAcceptedResidue_mod offset t
  constructor
  · intro target_unit
    have gap_depth :=
      lengthThreeReversingTarget_q1_A2_fiveUnit_forces_gapDepth_one
        0 offset t target_unit
    have offset_unit :=
      (lengthThreeReversingTarget_q1_A2_fiveUnit_iff_mod_twoFifty
        offset t gap_depth).1 target_unit
    have rectangle_unit :=
      (lengthThreeReversingTarget_fiveUnit_iff_mod_ten_unconditional
        1 2 (offset % 250) t).1 offset_unit
    have rectangle_depth :=
      lengthThreeReversingTarget_q1_A2_fiveUnit_forces_gapDepth_one
        0 (offset % 250) (t % 10) rectangle_unit
    have rectangle_accepted :=
      lengthThreeReversing_bounded_targetUnit_forces_residue
        offsetResidue waitResidue offsetResidue_lt waitResidue_lt
        rectangle_depth rectangle_unit
    exact residue_equivalence.1 rectangle_accepted
  · intro accepted
    have rectangle_accepted := residue_equivalence.2 accepted
    have rectangle_unit :=
      lengthThreeReversing_bounded_residue_forces_targetUnit
        offsetResidue waitResidue offsetResidue_lt waitResidue_lt rectangle_accepted
    have offsetResidue_unit :=
      (lengthThreeReversingTarget_fiveUnit_iff_mod_ten_unconditional
        1 2 (offset % 250) t).2 rectangle_unit
    have residue_depth :=
      lengthThreeReversingTarget_q1_A2_fiveUnit_forces_gapDepth_one
        0 (offset % 250) t offsetResidue_unit
    have transported_depth := reversingShellSlopeGapFiveDepth_add_twoFifty_mul_eq_one
      (offset % 250) (offset / 250) residue_depth
    have decomposition : offset % 250 + 250 * (offset / 250) = offset := by omega
    rw [decomposition] at transported_depth
    exact (lengthThreeReversingTarget_q1_A2_fiveUnit_iff_mod_twoFifty
      offset t transported_depth).2 offsetResidue_unit

/-- Both five-adic guards on the surviving fibre collapse to the same residue language. -/
theorem lengthThreeReversing_q1_A2_units_iff_residue
    (p offset t : ℕ) :
    IsUnit 5 (lengthThreeReversingNormalizedSource p 1 2 offset) ∧
        IsUnit 5 (lengthThreeReversingTarget 1 2 offset t) ↔
      lengthThreeReversingAcceptedResidue offset t := by
  constructor
  · exact fun guards =>
      (lengthThreeReversingTarget_q1_A2_fiveUnit_iff_residue
        offset t).1 guards.2
  · intro accepted
    have target_unit :=
      (lengthThreeReversingTarget_q1_A2_fiveUnit_iff_residue
        offset t).2 accepted
    exact ⟨lengthThreeReversingTarget_fiveUnit_forces_source_fiveUnit
      p 1 2 offset t target_unit, target_unit⟩

/-- Complete real and five-adic acceptance classifier for the reversing chamber. -/
theorem lengthThreeReversing_q1_A2_fullAcceptance_iff
    (p offset t : ℕ) :
    lengthThreeReversingNormalizedSource p 1 2 offset ∈
          Set.Icc (1 / 5) (1 / 2) ∧
        IsUnit 5 (lengthThreeReversingNormalizedSource p 1 2 offset) ∧
        IsUnit 5 (lengthThreeReversingTarget 1 2 offset t) ↔
      (p = 1 ∨ p = 2) ∧ lengthThreeReversingAcceptedResidue offset t := by
  constructor
  · rintro ⟨source_mem, source_unit, target_unit⟩
    have cut := lengthThreeReversing_realTrap_targetUnit_parameter_cut
      p 1 2 offset t (by norm_num) source_mem target_unit
    rcases cut.2.2.1 with ⟨p_one, _⟩ | ⟨p_two, _⟩
    · exact ⟨Or.inl p_one,
        (lengthThreeReversing_q1_A2_units_iff_residue
          p offset t).1 ⟨source_unit, target_unit⟩⟩
    · exact ⟨Or.inr p_two,
        (lengthThreeReversing_q1_A2_units_iff_residue
          p offset t).1 ⟨source_unit, target_unit⟩⟩
  · rintro ⟨p_one_or_two, accepted⟩
    have offset_lower :=
      lengthThreeReversingAcceptedResidue_offset_lower accepted
    have guards :=
      (lengthThreeReversing_q1_A2_units_iff_residue
        p offset t).2 accepted
    rcases p_one_or_two with rfl | rfl
    · exact ⟨(lengthThreeReversing_q1_A2_p_one_mem_realTrap_iff offset).2
        (by omega), guards⟩
    · exact ⟨(lengthThreeReversing_q1_A2_p_two_mem_realTrap_iff offset).2
        (by omega), guards⟩

end MatrixMortality.MixedPrimeDebt
