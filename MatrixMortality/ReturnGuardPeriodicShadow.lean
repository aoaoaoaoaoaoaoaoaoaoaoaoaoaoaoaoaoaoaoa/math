import MatrixMortality.ReturnGuardSmith

/-!
# Periodic-shadow obstruction

One fixed even-reset-defect depth-two guard has a fixed reset yet admits arbitrarily long legal
off-reset corridors. Every edge has nonmaximal Smith coordinate `v = 2` and exact forward
content `-4`; arbitrarily long runs of consecutive carried and Smith coordinates are primitive
and strictly height-increasing. This excludes coefficient-uniform bounded descent over all legal
corridors. Even after the remaining shadow depth and every local label are fixed, endpoint and
carried height are unbounded; any surviving decision theorem must use reset or terminal history.
-/

namespace MatrixMortality.ReturnGuard.Examples

open MatrixMortality.PadicValuation

noncomputable section

private theorem three_prime : Nat.Prime 3 := by norm_num

private instance factPrimeThree : Fact (Nat.Prime 3) :=
  ⟨three_prime⟩

private theorem val3_seventeen_div_sixteen :
    IsUnit 3 (17 / 16 : ℚ) := by
  exact div_hasValue
    (intCast_isUnit_of_not_dvd (by norm_num : ¬(3 : ℤ) ∣ (17 : ℤ)))
    (intCast_isUnit_of_not_dvd (by norm_num : ¬(3 : ℤ) ∣ (16 : ℤ)))

private theorem val3_one_div_sixteen :
    IsUnit 3 (1 / 16 : ℚ) := by
  exact div_hasValue
    (intCast_isUnit_of_not_dvd (by norm_num : ¬(3 : ℤ) ∣ (1 : ℤ)))
    (intCast_isUnit_of_not_dvd (by norm_num : ¬(3 : ℤ) ∣ (16 : ℤ)))

private theorem val3_three_div_four :
    HasValue 3 (3 / 4 : ℚ) 1 := by
  rw [show (3 / 4 : ℚ) = (3 : ℚ) ^ 1 * (1 : ℤ) / (4 : ℤ) by norm_num]
  exact primePower_mul_int_div_int_hasValue 1 (by norm_num) (by norm_num)

/-- Fixed even-reset-defect guard admitting arbitrarily deep off-reset shadows of its reset
fixed point. -/
def periodicShadowParameters : Parameters where
  prime := 3
  prime_prime := three_prime
  depth := 2
  depth_two := by norm_num
  center := 17 / 16
  reset := 3 / 4
  center_unit := val3_seventeen_div_sixteen
  center_sub_one_unit := by
    norm_num only [div_sub_one]
    exact val3_one_div_sixteen
  reset_positive := ⟨val3_three_div_four.1, by
    rw [val3_three_div_four.2]
    norm_num⟩

/-- The reset has legal wait one. -/
private theorem periodicShadow_reset_ready :
    Ready periodicShadowParameters 1 periodicShadowParameters.reset := by
  refine ⟨by norm_num, val3_three_div_four.2, ?_⟩
  have difference_value : HasValue 3 (-9 / 4 : ℚ) 2 := by
    rw [show (-9 / 4 : ℚ) = (3 : ℚ) ^ 2 * (-1 : ℤ) / (4 : ℤ) by norm_num]
    exact primePower_mul_int_div_int_hasValue 2 (by norm_num) (by norm_num)
  convert difference_value.2 using 1
  all_goals norm_num [periodicShadowParameters]

/-- The legal reset branch is a nonterminal fixed point. -/
private theorem periodicShadow_reset_fixed :
    guardedStep periodicShadowParameters 1 (some periodicShadowParameters.reset) =
      some periodicShadowParameters.reset := by
  rw [guardedStep_some periodicShadowParameters 1 _
    (by norm_num [periodicShadowParameters])]
  norm_num [periodicShadowParameters, guardDefect, drift]

/-- Denominator sequence of the periodic-shadow corridor. -/
def periodicShadowDenominator (shadowDepth index : Nat) : ℤ :=
  4 - 9 ^ (shadowDepth + 1) + 10 ^ index * 9 ^ (shadowDepth + 1 - index)

/-- Primitive endpoint pair of the periodic-shadow corridor. -/
def periodicShadowEndpoint (shadowDepth index : Nat) : ℤ × ℤ :=
  (32 * periodicShadowDenominator shadowDepth index -
      36 * periodicShadowDenominator shadowDepth (index + 1),
    periodicShadowDenominator shadowDepth index)

/-- Primitive prequotient pair carried by the periodic-shadow corridor. -/
def periodicShadowCarried (shadowDepth index : Nat) : ℤ × ℤ :=
  (periodicShadowDenominator shadowDepth index,
    -4 * periodicShadowDenominator shadowDepth (index + 1))

/-- Primitive Smith quotient of the periodic-shadow corridor. -/
def periodicShadowSmith (shadowDepth index : Nat) : ℤ × ℤ :=
  (8 * periodicShadowDenominator shadowDepth index -
      9 * periodicShadowDenominator shadowDepth (index + 1),
    4 * (periodicShadowDenominator shadowDepth index -
      periodicShadowDenominator shadowDepth (index + 1)))

private theorem nine_pow_mod_six (exponent : Nat) (positive : 0 < exponent) :
    (9 : ℤ) ^ exponent ≡ 3 [ZMOD 6] := by
  induction exponent with
  | zero => omega
  | succ exponent induction =>
      cases exponent with
      | zero => norm_num [Int.ModEq]
      | succ exponent =>
          rw [pow_succ]
          exact (induction (by omega)).mul
            (by norm_num [Int.ModEq] : (9 : ℤ) ≡ 3 [ZMOD 6]) |>.trans
              (by norm_num [Int.ModEq])

private theorem eighty_one_pow_mod_ninety
    (exponent : Nat) (positive : 0 < exponent) :
    (81 : ℤ) ^ exponent ≡ 81 [ZMOD 90] := by
  induction exponent with
  | zero => omega
  | succ exponent induction =>
      cases exponent with
      | zero => norm_num [Int.ModEq]
      | succ exponent =>
          rw [pow_succ]
          exact (induction (by omega)).mul
            (by norm_num [Int.ModEq] : (81 : ℤ) ≡ 81 [ZMOD 90]) |>.trans
              (by norm_num [Int.ModEq])

private theorem periodicShadowDenominator_mod_six
    {shadowDepth index : Nat} (index_positive : 0 < index) (index_le : index ≤ shadowDepth) :
    periodicShadowDenominator shadowDepth index ≡ 1 [ZMOD 6] := by
  have shadowDepth_power := nine_pow_mod_six (shadowDepth + 1) (by omega)
  obtain ⟨prior, index_eq⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt index_positive)
  have remaining_positive' : 0 < shadowDepth + 1 - prior.succ := by omega
  obtain ⟨remaining, remaining_eq⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt remaining_positive')
  have product_zero :
      (10 : ℤ) ^ index * 9 ^ (shadowDepth + 1 - index) ≡ 0 [ZMOD 6] := by
    rw [index_eq, remaining_eq, pow_succ, pow_succ]
    apply Int.modEq_zero_iff_dvd.mpr
    use 15 * 10 ^ prior * 9 ^ remaining
    ring
  dsimp [periodicShadowDenominator]
  exact ((Int.ModEq.refl 4).sub shadowDepth_power).add product_zero |>.trans (by norm_num)

private theorem periodicShadowDenominator_coprime_six
    {shadowDepth index : Nat} (index_positive : 0 < index) (index_le : index ≤ shadowDepth) :
    IsCoprime (periodicShadowDenominator shadowDepth index) (6 : ℤ) := by
  have congruence := periodicShadowDenominator_mod_six index_positive index_le
  obtain ⟨coefficient, equation⟩ := Int.modEq_iff_dvd.mp congruence
  refine ⟨1, coefficient, ?_⟩
  linarith

private theorem periodicShadowDenominator_three_unit
    {shadowDepth index : Nat} (index_positive : 0 < index) (index_le : index ≤ shadowDepth) :
    IsUnit 3 (periodicShadowDenominator shadowDepth index : ℚ) := by
  apply intCast_isUnit_of_not_dvd
  intro three_dvd
  obtain ⟨threeCoefficient, three_eq⟩ := three_dvd
  have congruence := periodicShadowDenominator_mod_six index_positive index_le
  obtain ⟨sixCoefficient, six_eq⟩ := Int.modEq_iff_dvd.mp congruence
  omega

private theorem periodicShadowDenominator_coprime_thirty_six
    {shadowDepth index : Nat} (index_positive : 0 < index) (index_le : index ≤ shadowDepth) :
    IsCoprime (periodicShadowDenominator shadowDepth index) (36 : ℤ) := by
  simpa [pow_two] using
    (periodicShadowDenominator_coprime_six index_positive index_le).pow_right (n := 2)

private theorem periodicShadowDenominator_recurrence
    {shadowDepth index : Nat} (index_lt : index < shadowDepth) :
    9 * periodicShadowDenominator shadowDepth (index + 2) =
      19 * periodicShadowDenominator shadowDepth (index + 1) -
        10 * periodicShadowDenominator shadowDepth index := by
  have first_sub : shadowDepth + 1 - index = (shadowDepth - index) + 1 := by omega
  have second_sub : shadowDepth + 1 - (index + 1) = shadowDepth - index := by omega
  have third_sub : shadowDepth + 1 - (index + 2) + 1 = shadowDepth - index := by omega
  simp only [periodicShadowDenominator]
  rw [first_sub, second_sub]
  have ten_succ : (10 : ℤ) ^ (index + 1) = 10 ^ index * 10 := by
    rw [pow_succ]
  have ten_succ_succ : (10 : ℤ) ^ (index + 2) = 10 ^ index * 10 ^ 2 := by
    rw [show index + 2 = index + 1 + 1 by omega, pow_succ, ten_succ]
    ring
  have third_power :
      (9 : ℤ) ^ (shadowDepth + 1 - (index + 2)) * 9 = 9 ^ (shadowDepth - index) := by
    rw [← pow_succ, third_sub]
  rw [ten_succ, ten_succ_succ]
  linear_combination
    10 ^ index * 10 ^ 2 * third_power

private theorem periodicShadowDenominator_positive
    {shadowDepth index : Nat} (index_positive : 0 < index) (index_le : index ≤ shadowDepth + 1) :
    0 < periodicShadowDenominator shadowDepth index := by
  have index_ne : index ≠ 0 := Nat.ne_of_gt index_positive
  have power_lt : (9 : ℤ) ^ index < 10 ^ index :=
    pow_lt_pow_left₀ (by norm_num) (by norm_num) index_ne
  have remaining_positive : 0 < (9 : ℤ) ^ (shadowDepth + 1 - index) := by positivity
  have scaled_lt :
      (9 : ℤ) ^ index * 9 ^ (shadowDepth + 1 - index) <
        10 ^ index * 9 ^ (shadowDepth + 1 - index) :=
    mul_lt_mul_of_pos_right power_lt remaining_positive
  have exponent_eq : index + (shadowDepth + 1 - index) = shadowDepth + 1 := by omega
  rw [← pow_add, exponent_eq] at scaled_lt
  dsimp [periodicShadowDenominator]
  linarith

private theorem periodicShadowDenominator_next_sub
    {shadowDepth index : Nat} (index_le : index ≤ shadowDepth) :
    periodicShadowDenominator shadowDepth (index + 1) -
        periodicShadowDenominator shadowDepth index =
      (10 : ℤ) ^ index * 9 ^ (shadowDepth - index) := by
  have first_sub : shadowDepth + 1 - index = (shadowDepth - index) + 1 := by omega
  have second_sub : shadowDepth + 1 - (index + 1) = shadowDepth - index := by omega
  simp only [periodicShadowDenominator]
  rw [first_sub, second_sub,
    show (10 : ℤ) ^ (index + 1) = 10 ^ index * 10 by rw [pow_succ],
    show (9 : ℤ) ^ ((shadowDepth - index) + 1) = 9 ^ (shadowDepth - index) * 9 by
      rw [pow_succ]]
  ring

private theorem periodicShadowDenominator_lt_next
    {shadowDepth index : Nat} (index_le : index ≤ shadowDepth) :
    periodicShadowDenominator shadowDepth index <
      periodicShadowDenominator shadowDepth (index + 1) := by
  have difference := periodicShadowDenominator_next_sub index_le
  have positive : 0 < (10 : ℤ) ^ index * 9 ^ (shadowDepth - index) := by positivity
  linarith

private theorem periodicShadowDenominator_index_le
    {shadowDepth index : Nat} (index_positive : 0 < index)
    (index_le : index ≤ shadowDepth + 1) :
    (index : ℤ) ≤ periodicShadowDenominator shadowDepth index := by
  induction index with
  | zero => omega
  | succ index induction =>
      by_cases index_zero : index = 0
      · subst index
        have positive :=
          periodicShadowDenominator_positive
            (shadowDepth := shadowDepth) (index := 1) (by omega) (by omega)
        norm_num at positive ⊢
        omega
      · have prior := induction (Nat.pos_of_ne_zero index_zero) (by omega)
        have ascent :=
          periodicShadowDenominator_lt_next
            (shadowDepth := shadowDepth) (index := index) (by omega)
        push_cast
        omega

private theorem periodicShadowCarried_penultimate_depth
    (index : Nat) (index_positive : 0 < index) :
    HasValue 3
      (((periodicShadowCarried (index + 1) index).2 : ℚ) /
          (periodicShadowCarried (index + 1) index).1 + 4)
      2 := by
  let source := periodicShadowDenominator (index + 1) index
  let target := periodicShadowDenominator (index + 1) (index + 1)
  have source_unit : IsUnit 3 (source : ℚ) :=
    periodicShadowDenominator_three_unit index_positive (by omega)
  have difference :=
    periodicShadowDenominator_next_sub
      (shadowDepth := index + 1) (index := index) (by omega)
  have difference_rat := congrArg (fun value : ℤ => (value : ℚ)) difference
  push_cast at difference_rat
  have minus_four_unit : IsUnit 3 (-4 : ℚ) := by
    exact intCast_isUnit_of_not_dvd (by norm_num : ¬(3 : ℤ) ∣ (-4 : ℤ))
  have ten_unit : IsUnit 3 (10 : ℚ) := by
    exact intCast_isUnit_of_not_dvd (by norm_num : ¬(3 : ℤ) ∣ (10 : ℤ))
  have ten_power_unit : IsUnit 3 ((10 : ℚ) ^ index) := by
    refine ⟨pow_ne_zero index ten_unit.1, ?_⟩
    rw [padicValRat.pow (p := 3) (q := (10 : ℚ)), ten_unit.2]
    simp
  have numerator_value :
      HasValue 3 ((3 : ℚ) ^ 2 * ((-4 : ℚ) * 10 ^ index)) 2 := by
    simpa using
      mul_hasValue (primePower_hasValue (prime := 3) 2)
        (mul_hasValue minus_four_unit ten_power_unit)
  have quotient_value := div_hasValue numerator_value source_unit
  have expression :
      ((periodicShadowCarried (index + 1) index).2 : ℚ) /
            (periodicShadowCarried (index + 1) index).1 + 4 =
        (3 : ℚ) ^ 2 * ((-4 : ℚ) * 10 ^ index) / source := by
    simp only [periodicShadowCarried, Int.cast_mul,
      Int.cast_neg, Int.cast_ofNat]
    change (-4 : ℚ) * target / source + 4 =
      (3 : ℚ) ^ 2 * ((-4 : ℚ) * 10 ^ index) / source
    have exponent_eq : index + 1 - index = 1 := by omega
    rw [exponent_eq, pow_one] at difference_rat
    have target_eq : (target : ℚ) = source + 10 ^ index * 9 := by
      linarith
    rw [target_eq]
    field_simp [source_unit.1]
    ring
  rw [expression]
  exact quotient_value

private theorem periodicShadowDenominator_constant_relation
    {shadowDepth index : Nat} (index_le : index ≤ shadowDepth) :
    10 * periodicShadowDenominator shadowDepth index -
        9 * periodicShadowDenominator shadowDepth (index + 1) =
      4 - 9 ^ (shadowDepth + 1) := by
  have first_sub : shadowDepth + 1 - index = (shadowDepth - index) + 1 := by omega
  have second_sub : shadowDepth + 1 - (index + 1) = shadowDepth - index := by omega
  simp only [periodicShadowDenominator]
  rw [first_sub, second_sub, pow_succ, pow_succ]
  ring

private theorem periodicShadowDenominator_coprime_constant
    {shadowDepth index : Nat} (shadowDepth_odd : Odd shadowDepth)
    (shadowDepth_three : 3 ≤ shadowDepth) :
    IsCoprime (periodicShadowDenominator shadowDepth index)
      (9 ^ (shadowDepth + 1) - 4 : ℤ) := by
  obtain ⟨half, shadowDepth_eq⟩ := shadowDepth_odd
  have exponent_eq : shadowDepth + 1 = 2 * (half + 1) := by omega
  have nine_square_mod_ninety : (9 : ℤ) ^ 2 ≡ 81 [ZMOD 90] := by norm_num
  have power_mod : (9 : ℤ) ^ (shadowDepth + 1) ≡ 81 [ZMOD 90] := by
    rw [exponent_eq, pow_mul]
    have square_power := nine_square_mod_ninety.pow (half + 1)
    have eighty_one_idempotent : (81 : ℤ) ^ (half + 1) ≡ 81 [ZMOD 90] :=
      eighty_one_pow_mod_ninety (half + 1) (by omega)
    exact square_power.trans eighty_one_idempotent
  obtain ⟨quotient, power_eq⟩ := Int.modEq_iff_dvd.mp power_mod
  have fixed_coprime_ninety : IsCoprime (9 ^ (shadowDepth + 1) - 4 : ℤ) 90 := by
    refine ⟨-7, 6 - 7 * quotient, ?_⟩
    linarith
  have fixed_coprime_ten :
      IsCoprime (9 ^ (shadowDepth + 1) - 4 : ℤ) 10 :=
    IsCoprime.of_isCoprime_of_dvd_right fixed_coprime_ninety (by norm_num)
  have fixed_coprime_nine :
      IsCoprime (9 ^ (shadowDepth + 1) - 4 : ℤ) 9 :=
    IsCoprime.of_isCoprime_of_dvd_right fixed_coprime_ninety (by norm_num)
  have fixed_coprime_product :
      IsCoprime (9 ^ (shadowDepth + 1) - 4 : ℤ)
        (10 ^ index * 9 ^ (shadowDepth + 1 - index)) :=
    (fixed_coprime_ten.pow_right).mul_right (fixed_coprime_nine.pow_right)
  have denominator_eq :
      periodicShadowDenominator shadowDepth index =
        -(9 ^ (shadowDepth + 1) - 4) +
          10 ^ index * 9 ^ (shadowDepth + 1 - index) := by
    simp [periodicShadowDenominator]
  rw [denominator_eq]
  simpa [add_comm] using fixed_coprime_product.symm.add_mul_left_left (-1)

private theorem periodicShadowDenominators_coprime
    {shadowDepth index : Nat} (shadowDepth_odd : Odd shadowDepth)
    (shadowDepth_three : 3 ≤ shadowDepth)
    (index_le : index ≤ shadowDepth) :
    IsCoprime (periodicShadowDenominator shadowDepth index)
      (periodicShadowDenominator shadowDepth (index + 1)) := by
  have source_coprime_constant :=
    periodicShadowDenominator_coprime_constant (index := index)
      shadowDepth_odd shadowDepth_three
  obtain ⟨left, right, bezout⟩ := source_coprime_constant
  refine ⟨left - 10 * right, 9 * right, ?_⟩
  have relation := periodicShadowDenominator_constant_relation index_le
  linear_combination bezout - right * relation

private theorem periodicShadowEndpoint_coprime
    {shadowDepth index : Nat} (shadowDepth_odd : Odd shadowDepth)
    (shadowDepth_three : 3 ≤ shadowDepth)
    (index_positive : 0 < index) (index_le : index ≤ shadowDepth) :
    IsCoprime (periodicShadowEndpoint shadowDepth index).1
      (periodicShadowEndpoint shadowDepth index).2 := by
  have consecutive := periodicShadowDenominators_coprime shadowDepth_odd shadowDepth_three
    index_le
  have source_coprime_thirty_six :=
    periodicShadowDenominator_coprime_thirty_six index_positive
      (by omega : index ≤ shadowDepth)
  have source_coprime_scaled_target := source_coprime_thirty_six.mul_right consecutive
  obtain ⟨sourceCoefficient, targetCoefficient, bezout⟩ :=
    source_coprime_scaled_target
  dsimp [periodicShadowEndpoint]
  refine ⟨-targetCoefficient, sourceCoefficient + 32 * targetCoefficient, ?_⟩
  linear_combination bezout

private theorem periodicShadowEndpoint_target_coprime
    {shadowDepth index : Nat} (shadowDepth_odd : Odd shadowDepth)
    (shadowDepth_three : 3 ≤ shadowDepth)
    (index_positive : 0 < index) (index_lt : index < shadowDepth) :
    IsCoprime (periodicShadowEndpoint shadowDepth (index + 1)).1
      (periodicShadowEndpoint shadowDepth (index + 1)).2 := by
  exact periodicShadowEndpoint_coprime shadowDepth_odd shadowDepth_three
    (by omega) (by omega)

/-- Every internal edge of the fixed periodic-shadow family is an exact primitive wait-one
reduction with forward content `-4`. -/
private theorem periodicShadow_reduction
    {shadowDepth index : Nat} (shadowDepth_odd : Odd shadowDepth)
    (shadowDepth_three : 3 ≤ shadowDepth)
    (index_positive : 0 < index) (index_lt : index < shadowDepth) :
    PrimitiveEndpointReduction 3 2 17 (-5) 16 1
      (periodicShadowEndpoint shadowDepth index)
      (periodicShadowEndpoint shadowDepth (index + 1)) (-4) := by
  refine ⟨periodicShadowEndpoint_coprime shadowDepth_odd shadowDepth_three
      index_positive index_lt.le,
    periodicShadowEndpoint_target_coprime shadowDepth_odd shadowDepth_three
      index_positive index_lt,
    by norm_num, by norm_num, ?_⟩
  constructor
  · simp only [periodicShadowEndpoint]
    ring
  · simp only [periodicShadowEndpoint]
    have recurrence := periodicShadowDenominator_recurrence index_lt
    linear_combination 16 * recurrence

/-- Rational guard state represented by one periodic-shadow endpoint. -/
def periodicShadowState (shadowDepth index : Nat) : ℚ :=
  endpointState 16 (periodicShadowEndpoint shadowDepth index)

private theorem periodicShadowState_eq
    {shadowDepth index : Nat} (index_positive : 0 < index) (index_le : index ≤ shadowDepth + 1) :
    periodicShadowState shadowDepth index =
      3 - 9 * periodicShadowDenominator shadowDepth (index + 1) /
        (4 * periodicShadowDenominator shadowDepth index) := by
  have denominator_ne : (periodicShadowDenominator shadowDepth index : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt (periodicShadowDenominator_positive index_positive index_le)
  simp only [periodicShadowState, endpointState, periodicShadowEndpoint]
  field_simp [denominator_ne]
  push_cast
  ring

/-- Every internal periodic-shadow state is ready at wait one. Its exact shadow depth is not
part of the finite wait label. -/
private theorem periodicShadow_ready
    {shadowDepth index : Nat} (index_positive : 0 < index) (index_lt : index < shadowDepth) :
    Ready periodicShadowParameters 1 (periodicShadowState shadowDepth index) := by
  have source_unit := periodicShadowDenominator_three_unit index_positive index_lt.le
  have target_unit := periodicShadowDenominator_three_unit (by omega : 0 < index + 1)
    (by omega : index + 1 ≤ shadowDepth)
  have four_unit : IsUnit 3 (4 : ℚ) :=
    intCast_isUnit_of_not_dvd (by norm_num)
  have error_value :
      HasValue 3
        (-(9 * periodicShadowDenominator shadowDepth (index + 1) /
          (4 * periodicShadowDenominator shadowDepth index) : ℚ)) 2 := by
    have numerator_value :=
      mul_hasValue (primePower_hasValue (prime := 3) 2) (neg_hasValue target_unit)
    have denominator_value := mul_hasValue four_unit source_unit
    convert div_hasValue numerator_value denominator_value using 1
    · ring
    · norm_num
  have state_value :
      HasValue 3 (periodicShadowState shadowDepth index) 1 := by
    rw [periodicShadowState_eq index_positive (by omega : index ≤ shadowDepth + 1),
      sub_eq_add_neg]
    simpa using add_hasValue_left (primePower_hasValue (prime := 3) 1)
      error_value (by norm_num)
  refine ⟨by norm_num, state_value.2, ?_⟩
  rw [periodicShadowState_eq index_positive (by omega : index ≤ shadowDepth + 1)]
  norm_num only [periodicShadowParameters, Nat.cast_ofNat, pow_one]
  simpa using error_value.2

/-- The endpoint corridor is the actual rational guard orbit, not merely a formal integral
recurrence. -/
private theorem periodicShadow_guardedStep
    {shadowDepth index : Nat} (shadowDepth_odd : Odd shadowDepth)
    (shadowDepth_three : 3 ≤ shadowDepth)
    (index_positive : 0 < index) (index_lt : index < shadowDepth) :
    guardedStep periodicShadowParameters 1 (some (periodicShadowState shadowDepth index)) =
      some (periodicShadowState shadowDepth (index + 1)) := by
  apply PrimitiveEndpointReduction.guardedStep_endpointState periodicShadowParameters
    (periodicShadow_reduction shadowDepth_odd shadowDepth_three index_positive index_lt)
  · norm_num [periodicShadowParameters]
  · norm_num [periodicShadowParameters, drift]
  · norm_num
  · exact ne_of_gt (periodicShadowDenominator_positive index_positive (by omega))
  · exact ne_of_gt (periodicShadowDenominator_positive (by omega) (by omega))

/-- Every displayed shadow state lies off the reset ray. -/
private theorem periodicShadowState_ne_reset
    {shadowDepth index : Nat} (index_positive : 0 < index) (index_le : index ≤ shadowDepth) :
    periodicShadowState shadowDepth index ≠ periodicShadowParameters.reset := by
  intro state_eq
  have formula := periodicShadowState_eq index_positive (by omega : index ≤ shadowDepth + 1)
  rw [formula] at state_eq
  norm_num only [periodicShadowParameters] at state_eq
  have denominator_ne : (periodicShadowDenominator shadowDepth index : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt (periodicShadowDenominator_positive index_positive (by omega))
  field_simp [denominator_ne] at state_eq
  have growth := periodicShadowDenominator_lt_next index_le
  have same_rat : (periodicShadowDenominator shadowDepth index : ℚ) =
      periodicShadowDenominator shadowDepth (index + 1) := by
    linarith
  have same : periodicShadowDenominator shadowDepth index =
      periodicShadowDenominator shadowDepth (index + 1) := by
    exact_mod_cast same_rat
  exact (ne_of_lt growth) same

/-- The carried prequotient pair on every periodic-shadow edge is primitive. -/
private theorem periodicShadowCarried_coprime
    {shadowDepth index : Nat} (shadowDepth_odd : Odd shadowDepth)
    (shadowDepth_three : 3 ≤ shadowDepth)
    (index_positive : 0 < index) (index_lt : index < shadowDepth) :
    IsCoprime (periodicShadowCarried shadowDepth index).1
      (periodicShadowCarried shadowDepth index).2 := by
  have source_coprime_four :
      IsCoprime (periodicShadowDenominator shadowDepth index) (4 : ℤ) :=
    IsCoprime.of_isCoprime_of_dvd_right
      (periodicShadowDenominator_coprime_thirty_six index_positive index_lt.le)
      (by norm_num)
  have consecutive := periodicShadowDenominators_coprime shadowDepth_odd
    shadowDepth_three index_lt.le
  simpa [periodicShadowCarried] using
    (source_coprime_four.mul_right consecutive).neg_right

/-- Carried primitive height rises on every periodic-shadow edge. -/
private theorem periodicShadowCarried_height_lt
    {shadowDepth index : Nat} (index_positive : 0 < index) (index_lt : index < shadowDepth) :
    integralPairHeight (periodicShadowCarried shadowDepth index).1
        (periodicShadowCarried shadowDepth index).2 <
      integralPairHeight (periodicShadowCarried shadowDepth (index + 1)).1
        (periodicShadowCarried shadowDepth (index + 1)).2 := by
  let source := periodicShadowDenominator shadowDepth index
  let middle := periodicShadowDenominator shadowDepth (index + 1)
  let target := periodicShadowDenominator shadowDepth (index + 2)
  have source_positive : 0 < source :=
    periodicShadowDenominator_positive index_positive (by omega)
  have middle_positive : 0 < middle :=
    periodicShadowDenominator_positive (by omega) (by omega)
  have source_lt_middle : source < middle :=
    periodicShadowDenominator_lt_next index_lt.le
  have middle_lt_target : middle < target :=
    periodicShadowDenominator_lt_next (by omega)
  have source_abs_lt_middle_scaled : source.natAbs < (-4 * middle).natAbs := by
    simpa [Int.natAbs_mul] using
      Int.natAbs_lt_natAbs_of_nonneg_of_lt source_positive.le
        (by nlinarith : source < 4 * middle)
  have middle_scaled_lt_target_scaled :
      (-4 * middle).natAbs < (-4 * target).natAbs := by
    simpa [Int.natAbs_mul] using
      (Nat.mul_lt_mul_left (by norm_num : 0 < 4)).mpr
        (Int.natAbs_lt_natAbs_of_nonneg_of_lt middle_positive.le middle_lt_target)
  rw [integralPairHeight, integralPairHeight]
  simp only [periodicShadowCarried]
  change max source.natAbs (-4 * middle).natAbs <
    max middle.natAbs (-4 * target).natAbs
  rw [max_eq_right source_abs_lt_middle_scaled.le]
  exact middle_scaled_lt_target_scaled.trans_le (le_max_right _ _)

/-- The same nonmaximal Smith allocation belongs to every wait-one periodic-shadow edge. -/
def periodicShadowSmithSplit : SmithRubanSplit (-80) 2 (-4) 40 where
  u := 1
  eta := -4
  theta := 20
  v := 2
  u_pos := by norm_num
  v_pos := by norm_num
  content_eq := by norm_num
  complement_eq := by norm_num
  fixed_eq := by norm_num
  shift_eq := by norm_num
  u_coprime_theta := by norm_num [IsCoprime]

/-- The Smith decoder output is exactly four times the displayed primitive quotient. -/
private theorem periodicShadowSmith_raw_eq (shadowDepth index : Nat) :
    smithRubanQuotient 3 16 periodicShadowSmithSplit.u periodicShadowSmithSplit.v
        periodicShadowSmithSplit.eta
        (periodicShadowEndpoint shadowDepth index).2
        (periodicShadowEndpoint shadowDepth (index + 1)).2 =
      4 • pairVector (periodicShadowSmith shadowDepth index) := by
  ext coordinate
  fin_cases coordinate <;>
    simp [periodicShadowSmithSplit, smithRubanQuotient, pairVector,
      periodicShadowSmith, periodicShadowEndpoint] <;>
    ring

private theorem periodicShadowSmith_first_mod_six
    {shadowDepth index : Nat} (index_positive : 0 < index) (index_lt : index < shadowDepth) :
    (periodicShadowSmith shadowDepth index).1 ≡ -1 [ZMOD 6] := by
  have source_mod := periodicShadowDenominator_mod_six index_positive index_lt.le
  have target_mod := periodicShadowDenominator_mod_six (by omega : 0 < index + 1)
    (by omega : index + 1 ≤ shadowDepth)
  have combined :=
    (source_mod.mul (Int.ModEq.refl 8)).sub
      (target_mod.mul (Int.ModEq.refl 9))
  simpa [periodicShadowSmith, mul_comm] using combined

/-- The live Smith quotient after its exact fixed factor four is primitive. -/
private theorem periodicShadowSmith_coprime
    {shadowDepth index : Nat} (shadowDepth_odd : Odd shadowDepth)
    (shadowDepth_three : 3 ≤ shadowDepth)
    (index_positive : 0 < index) (index_lt : index < shadowDepth) :
    IsCoprime (periodicShadowSmith shadowDepth index).1
      (periodicShadowSmith shadowDepth index).2 := by
  let source := periodicShadowDenominator shadowDepth index
  let target := periodicShadowDenominator shadowDepth (index + 1)
  let first := 8 * source - 9 * target
  let difference := source - target
  have first_mod : first ≡ -1 [ZMOD 6] := by
    simpa [first, source, target, periodicShadowSmith] using
      periodicShadowSmith_first_mod_six index_positive index_lt
  obtain ⟨coefficient, equation⟩ := Int.modEq_iff_dvd.mp first_mod
  have first_coprime_six : IsCoprime first (6 : ℤ) := by
    refine ⟨-1, -coefficient, ?_⟩
    linarith
  have first_coprime_two : IsCoprime first (2 : ℤ) :=
    IsCoprime.of_isCoprime_of_dvd_right first_coprime_six (by norm_num)
  have first_coprime_four : IsCoprime first (4 : ℤ) := by
    simpa [pow_two] using first_coprime_two.pow_right (n := 2)
  have consecutive := periodicShadowDenominators_coprime shadowDepth_odd
    shadowDepth_three index_lt.le
  have target_coprime_difference : IsCoprime target difference := by
    obtain ⟨sourceCoefficient, targetCoefficient, bezout⟩ := consecutive
    refine ⟨sourceCoefficient + targetCoefficient, sourceCoefficient, ?_⟩
    dsimp [source, target, difference] at bezout ⊢
    linear_combination bezout
  have first_coprime_difference : IsCoprime first difference := by
    obtain ⟨targetCoefficient, differenceCoefficient, bezout⟩ :=
      target_coprime_difference
    refine ⟨-targetCoefficient, differenceCoefficient + 8 * targetCoefficient, ?_⟩
    dsimp [first, source, target, difference] at bezout ⊢
    linear_combination bezout
  simpa [periodicShadowSmith, first, source, target, difference] using
    first_coprime_four.mul_right first_coprime_difference

/-- Primitive Smith height rises on every periodic-shadow edge despite `v = 2`. -/
private theorem periodicShadowSmith_height_lt
    {shadowDepth index : Nat} (index_positive : 0 < index) (index_lt : index < shadowDepth) :
    integralPairHeight (periodicShadowSmith shadowDepth index).1
        (periodicShadowSmith shadowDepth index).2 <
      integralPairHeight (periodicShadowSmith shadowDepth (index + 1)).1
        (periodicShadowSmith shadowDepth (index + 1)).2 := by
  let source := periodicShadowDenominator shadowDepth index
  let middle := periodicShadowDenominator shadowDepth (index + 1)
  let target := periodicShadowDenominator shadowDepth (index + 2)
  let first := 8 * source - 9 * middle
  let second := 4 * (source - middle)
  let nextFirst := 8 * middle - 9 * target
  have source_positive : 0 < source :=
    periodicShadowDenominator_positive index_positive (by omega)
  have source_lt_middle : source < middle :=
    periodicShadowDenominator_lt_next index_lt.le
  have recurrence := periodicShadowDenominator_recurrence index_lt
  have second_negative : second < 0 := by dsimp [second]; linarith
  have first_lt_second : first < second := by
    dsimp [first, second]
    linarith
  have next_first_lt : nextFirst < first := by
    dsimp [nextFirst, first, source, middle, target]
    dsimp [source, middle, target] at source_lt_middle
    linarith
  have second_abs_lt_first_abs : second.natAbs < first.natAbs := by
    have absolute := Int.natAbs_lt_natAbs_of_nonneg_of_lt
      (by linarith : 0 ≤ -second) (by linarith : -second < -first)
    simpa only [Int.natAbs_neg] using absolute
  have first_abs_lt_next_first_abs : first.natAbs < nextFirst.natAbs := by
    have absolute := Int.natAbs_lt_natAbs_of_nonneg_of_lt
      (by linarith : 0 ≤ -first) (by linarith : -first < -nextFirst)
    simpa only [Int.natAbs_neg] using absolute
  rw [integralPairHeight, integralPairHeight]
  simp only [periodicShadowSmith]
  change max first.natAbs second.natAbs <
    max nextFirst.natAbs (4 * (middle - target)).natAbs
  rw [max_eq_left second_abs_lt_first_abs.le]
  exact first_abs_lt_next_first_abs.trans_le (le_max_left _ _)

/-- Every internal shadow edge is an actual legal guard transition. -/
private theorem periodicShadow_legalStep
    {shadowDepth index : Nat} (shadowDepth_odd : Odd shadowDepth)
    (shadowDepth_three : 3 ≤ shadowDepth)
    (index_positive : 0 < index) (index_lt : index < shadowDepth) :
    LegalStep periodicShadowParameters (periodicShadowState shadowDepth index)
      (periodicShadowState shadowDepth (index + 1)) := by
  exact ⟨0, periodicShadow_ready index_positive index_lt,
    periodicShadow_guardedStep shadowDepth_odd shadowDepth_three index_positive index_lt⟩

private theorem periodicShadow_reachesIn
    {shadowDepth start length : Nat} (shadowDepth_odd : Odd shadowDepth)
    (shadowDepth_three : 3 ≤ shadowDepth)
    (start_positive : 0 < start) (end_le : start + length ≤ shadowDepth) :
    Relation.ReachesIn (LegalStep periodicShadowParameters) length
      (periodicShadowState shadowDepth start)
      (periodicShadowState shadowDepth (start + length)) := by
  induction length generalizing start with
  | zero => exact .refl _
  | succ length induction =>
      have start_lt : start < shadowDepth := by omega
      have first := periodicShadow_legalStep shadowDepth_odd shadowDepth_three
        start_positive start_lt
      have tail_bound : start + 1 + length ≤ shadowDepth := by omega
      have later := induction (start := start + 1) (by omega) tail_bound
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Relation.ReachesIn.head first later

/-- The fixed reset coexists with arbitrarily long primitive off-reset corridors carrying
arbitrarily long nonmaximal runs with strictly rising carried and primitive Smith heights. -/
theorem periodicShadow_obstruction (bound : Nat) :
    Ready periodicShadowParameters 1 periodicShadowParameters.reset ∧
      periodicShadowParameters.reset ≠ 1 ∧
      guardedStep periodicShadowParameters 1
          (some periodicShadowParameters.reset) =
        some periodicShadowParameters.reset ∧
      ∃ length,
      bound < length ∧
        Relation.ReachesIn (LegalStep periodicShadowParameters) length
          (periodicShadowState (length + 1) 1)
          (periodicShadowState (length + 1) (length + 1)) ∧
        (∀ offset, offset ≤ length →
          periodicShadowState (length + 1) (offset + 1) ≠
            periodicShadowParameters.reset) ∧
        periodicShadowSmithSplit.v = 2 ∧
        ∀ offset, offset < length →
          PrimitiveEndpointReduction 3 2 17 (-5) 16 1
              (periodicShadowEndpoint (length + 1) (offset + 1))
              (periodicShadowEndpoint (length + 1) (offset + 2)) (-4) ∧
            IsCoprime (periodicShadowCarried (length + 1) (offset + 1)).1
              (periodicShadowCarried (length + 1) (offset + 1)).2 ∧
            integralPairHeight (periodicShadowCarried (length + 1) (offset + 1)).1
                (periodicShadowCarried (length + 1) (offset + 1)).2 <
              integralPairHeight (periodicShadowCarried (length + 1) (offset + 2)).1
                (periodicShadowCarried (length + 1) (offset + 2)).2 ∧
            smithRubanQuotient 3 16 periodicShadowSmithSplit.u
                periodicShadowSmithSplit.v periodicShadowSmithSplit.eta
                (periodicShadowEndpoint (length + 1) (offset + 1)).2
                (periodicShadowEndpoint (length + 1) (offset + 2)).2 =
              4 • pairVector (periodicShadowSmith (length + 1) (offset + 1)) ∧
            IsCoprime (periodicShadowSmith (length + 1) (offset + 1)).1
              (periodicShadowSmith (length + 1) (offset + 1)).2 ∧
            integralPairHeight (periodicShadowSmith (length + 1) (offset + 1)).1
                (periodicShadowSmith (length + 1) (offset + 1)).2 <
              integralPairHeight (periodicShadowSmith (length + 1) (offset + 2)).1
                (periodicShadowSmith (length + 1) (offset + 2)).2 := by
  refine ⟨periodicShadow_reset_ready, by norm_num [periodicShadowParameters],
    periodicShadow_reset_fixed, ?_⟩
  let length := 2 * (bound + 1)
  have shadowDepth_odd : Odd (length + 1) := by
    exact ⟨bound + 1, by simp [length]⟩
  have shadowDepth_three : 3 ≤ length + 1 := by simp [length]
  have execution := periodicShadow_reachesIn (start := 1) (length := length)
    shadowDepth_odd shadowDepth_three (by omega) (by omega)
  refine ⟨length, by simp [length]; omega, ?_, ?_, rfl, ?_⟩
  · simpa [Nat.add_comm] using execution
  · intro offset offset_le
    exact periodicShadowState_ne_reset (by omega) (by omega)
  intro offset offset_lt
  have index_positive : 0 < offset + 1 := by omega
  have index_lt : offset + 1 < length + 1 := by omega
  exact ⟨
    periodicShadow_reduction shadowDepth_odd shadowDepth_three index_positive index_lt,
    periodicShadowCarried_coprime shadowDepth_odd shadowDepth_three index_positive index_lt,
    periodicShadowCarried_height_lt index_positive index_lt,
    periodicShadowSmith_raw_eq _ _,
    periodicShadowSmith_coprime shadowDepth_odd shadowDepth_three index_positive index_lt,
    periodicShadowSmith_height_lt index_positive index_lt⟩

/-- Fixed coefficients, wait, content, Smith label, and remaining shadow depth do not bound the
endpoint or carried height of a legal primitive edge. -/
theorem periodicShadow_shatters_localCompactness (bound : Nat) :
    ∃ shadowDepth index,
      LegalStep periodicShadowParameters
          (periodicShadowState shadowDepth index)
          (periodicShadowState shadowDepth (index + 1)) ∧
        periodicShadowState shadowDepth index ≠ periodicShadowParameters.reset ∧
        PrimitiveEndpointReduction 3 2 17 (-5) 16 1
          (periodicShadowEndpoint shadowDepth index)
          (periodicShadowEndpoint shadowDepth (index + 1)) (-4) ∧
        periodicShadowSmithSplit.v = 2 ∧
        IsCoprime (periodicShadowCarried shadowDepth index).1
          (periodicShadowCarried shadowDepth index).2 ∧
        HasValue 3
          (((periodicShadowCarried shadowDepth index).2 : ℚ) /
              (periodicShadowCarried shadowDepth index).1 + 4)
          2 ∧
        bound <
          integralPairHeight (periodicShadowEndpoint shadowDepth index).1
            (periodicShadowEndpoint shadowDepth index).2 ∧
        bound <
          integralPairHeight (periodicShadowCarried shadowDepth index).1
            (periodicShadowCarried shadowDepth index).2 := by
  let index := 2 * (bound + 1)
  let shadowDepth := index + 1
  have shadowDepth_odd : Odd shadowDepth := by
    exact ⟨bound + 1, by simp [shadowDepth, index]⟩
  have shadowDepth_three : 3 ≤ shadowDepth := by simp [shadowDepth, index]
  have index_positive : 0 < index := by simp [index]
  have index_lt : index < shadowDepth := by simp [shadowDepth]
  have denominator_positive :=
    periodicShadowDenominator_positive
      (shadowDepth := shadowDepth) (index := index) index_positive (by omega)
  have index_le_denominator :=
    periodicShadowDenominator_index_le
      (shadowDepth := shadowDepth) (index := index) index_positive (by omega)
  have index_le_abs :
      index ≤ (periodicShadowDenominator shadowDepth index).natAbs := by
    have cast_bound :
        (index : ℤ) ≤
          ((periodicShadowDenominator shadowDepth index).natAbs : ℤ) := by
      rw [Int.natAbs_of_nonneg denominator_positive.le]
      exact index_le_denominator
    exact_mod_cast cast_bound
  have bound_lt_abs :
      bound < (periodicShadowDenominator shadowDepth index).natAbs :=
    (by omega : bound < index).trans_le index_le_abs
  refine ⟨shadowDepth, index,
    periodicShadow_legalStep shadowDepth_odd shadowDepth_three index_positive index_lt,
    periodicShadowState_ne_reset index_positive index_lt.le,
    periodicShadow_reduction shadowDepth_odd shadowDepth_three index_positive index_lt,
    rfl,
    periodicShadowCarried_coprime shadowDepth_odd shadowDepth_three
      index_positive index_lt,
    ?_, ?_, ?_⟩
  · simpa [shadowDepth] using
      periodicShadowCarried_penultimate_depth index index_positive
  · apply bound_lt_abs.trans_le
    have denominator_le_height :
        (periodicShadowDenominator shadowDepth index).natAbs ≤
          integralPairHeight (periodicShadowEndpoint shadowDepth index).1
            (periodicShadowEndpoint shadowDepth index).2 := by
      change
        (periodicShadowDenominator shadowDepth index).natAbs ≤
          max
            (32 * periodicShadowDenominator shadowDepth index -
              36 * periodicShadowDenominator shadowDepth (index + 1)).natAbs
            (periodicShadowDenominator shadowDepth index).natAbs
      exact le_max_right _ _
    exact denominator_le_height
  · apply bound_lt_abs.trans_le
    have denominator_le_height :
        (periodicShadowDenominator shadowDepth index).natAbs ≤
          integralPairHeight (periodicShadowCarried shadowDepth index).1
            (periodicShadowCarried shadowDepth index).2 := by
      change
        (periodicShadowDenominator shadowDepth index).natAbs ≤
          max (periodicShadowDenominator shadowDepth index).natAbs
            (-4 * periodicShadowDenominator shadowDepth (index + 1)).natAbs
      exact le_max_left _ _
    exact denominator_le_height

end
end MatrixMortality.ReturnGuard.Examples
