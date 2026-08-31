import MatrixMortality.MixedPrimeRealTrapWall

/-!
# Two-adic absorption outside the mixed-prime secondary wall

The three reverse branches admit exact normalized mantissa coordinates. If a reduced source
mantissa has denominator divisible by four, every branch remains at rational two-adic value at
most minus two. This cone is therefore absorbing: a lower-wall under-cancellation or a middle
exit can never return to the secondary wall. Lower-wall exits split exactly into the absorbing
cone, the finite wall nucleus, and the odd-denominator cone. Only the last cone can support a
genuine return.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation

private local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

/-- Centered numerator obtained by normalizing the upper predecessor into a displayed band. -/
def upperCenteredNumerator (a b : ℕ) : ℕ :=
  5 * a - 2 * b

/-- Centered numerator obtained by normalizing the middle predecessor into a displayed band. -/
def middleCenteredNumerator (a b : ℕ) : ℕ :=
  5 * a - 3 * b

/-- Mantissa of the upper predecessor when it occupies the displayed depth. -/
def upperNormalizedMantissa (depth a b : ℕ) : ℚ :=
  (3 : ℚ) ^ depth * upperCenteredNumerator a b /
    (3 * (2 : ℚ) ^ depth * b)

/-- Mantissa of the middle predecessor when it occupies the displayed depth. -/
def middleNormalizedMantissa (depth a b : ℕ) : ℚ :=
  (2 : ℚ) * 3 ^ depth * middleCenteredNumerator a b /
    (9 * 2 ^ depth * b)

private theorem unit_pow
    {prime : ℕ} [Fact prime.Prime] {value : ℚ}
    (unit : IsUnit prime value) (exponent : ℕ) :
    IsUnit prime (value ^ exponent) := by
  refine ⟨pow_ne_zero exponent unit.1, ?_⟩
  rw [padicValRat.pow, unit.2]
  simp

/-- The upper normalized coordinate reconstructs the exact upper predecessor state. -/
theorem realTrapBandPoint_upperNormalizedMantissa
    {depth a b : ℕ} (b_ne : b ≠ 0) (positive : 2 * b ≤ 5 * a) :
    realTrapBandPoint depth (upperNormalizedMantissa depth a b) =
      (a : ℚ) / (2 * b) := by
  have residual_cast :
      (upperCenteredNumerator a b : ℚ) = 5 * a - 2 * b := by
    rw [upperCenteredNumerator, Nat.cast_sub positive]
    norm_num
  have two_power_ne : (2 : ℚ) ^ depth ≠ 0 := by positivity
  have three_power_ne : (3 : ℚ) ^ depth ≠ 0 := by positivity
  have power_cancel : (2 / 3 : ℚ) ^ depth * 3 ^ depth = 2 ^ depth := by
    rw [div_pow]
    field_simp
  simp only [realTrapBandPoint, upperNormalizedMantissa, residual_cast]
  field_simp
  linear_combination (50 * (a : ℚ) - 20 * b) * power_cancel

/-- The middle normalized coordinate reconstructs the exact middle predecessor state. -/
theorem realTrapBandPoint_middleNormalizedMantissa
    {depth a b : ℕ} (b_ne : b ≠ 0) (positive : 3 * b ≤ 5 * a) :
    realTrapBandPoint depth (middleNormalizedMantissa depth a b) =
      (a : ℚ) / (3 * b) := by
  have residual_cast :
      (middleCenteredNumerator a b : ℚ) = 5 * a - 3 * b := by
    rw [middleCenteredNumerator, Nat.cast_sub positive]
    norm_num
  have two_power_ne : (2 : ℚ) ^ depth ≠ 0 := by positivity
  have three_power_ne : (3 : ℚ) ^ depth ≠ 0 := by positivity
  have power_cancel : (2 / 3 : ℚ) ^ depth * 3 ^ depth = 2 ^ depth := by
    rw [div_pow]
    field_simp
  simp only [realTrapBandPoint, middleNormalizedMantissa, residual_cast]
  field_simp
  linear_combination (450 * (a : ℚ) - 270 * b) * power_cancel

/-- A reduced denominator divisible by four makes the upper centered numerator odd. -/
theorem upperCenteredNumerator_twoValue_of_four_dvd_denominator
    {a b : ℕ} (ab : a.Coprime b) (four_dvd : 4 ∣ b)
    (positive : 2 * b < 5 * a) :
    padicValNat 2 (upperCenteredNumerator a b) = 0 := by
  obtain ⟨quarter, rfl⟩ := four_dvd
  have two_dvd_b : 2 ∣ 4 * quarter := ⟨2 * quarter, by omega⟩
  have a_odd : Odd a := (ab.of_dvd_right two_dvd_b).odd_of_right
  obtain ⟨half, rfl⟩ := a_odd
  have residual_odd : Odd (upperCenteredNumerator (2 * half + 1) (4 * quarter)) := by
    refine ⟨5 * half + 2 - 4 * quarter, ?_⟩
    simp only [upperCenteredNumerator]
    omega
  apply padicValNat.eq_zero_of_not_dvd
  exact Nat.prime_two.coprime_iff_not_dvd.mp residual_odd.coprime_two_left

/-- A reduced denominator divisible by four makes the middle centered numerator odd. -/
theorem middleCenteredNumerator_twoValue_of_four_dvd_denominator
    {a b : ℕ} (ab : a.Coprime b) (four_dvd : 4 ∣ b)
    (positive : 3 * b < 5 * a) :
    padicValNat 2 (middleCenteredNumerator a b) = 0 := by
  obtain ⟨quarter, rfl⟩ := four_dvd
  have two_dvd_b : 2 ∣ 4 * quarter := ⟨2 * quarter, by omega⟩
  have a_odd : Odd a := (ab.of_dvd_right two_dvd_b).odd_of_right
  obtain ⟨half, rfl⟩ := a_odd
  have residual_odd : Odd (middleCenteredNumerator (2 * half + 1) (4 * quarter)) := by
    refine ⟨5 * half + 2 - 6 * quarter, ?_⟩
    simp only [middleCenteredNumerator]
    omega
  apply padicValNat.eq_zero_of_not_dvd
  exact Nat.prime_two.coprime_iff_not_dvd.mp residual_odd.coprime_two_left

/-- Exact upper-branch two-adic transition from a reduced four-divisible denominator. -/
theorem upperNormalizedMantissa_twoValue_of_four_dvd_denominator
    {depth a b : ℕ} (b_ne : b ≠ 0) (ab : a.Coprime b) (four_dvd : 4 ∣ b)
    (positive : 2 * b < 5 * a) :
    HasValue 2 (upperNormalizedMantissa depth a b)
      (-((depth : ℕ) : ℤ) - padicValNat 2 b) := by
  have residual_ne : upperCenteredNumerator a b ≠ 0 := by
    simp only [upperCenteredNumerator]
    omega
  have residual_value :=
    upperCenteredNumerator_twoValue_of_four_dvd_denominator ab four_dvd positive
  have residual_unit : IsUnit 2 (upperCenteredNumerator a b : ℚ) := by
    refine ⟨by exact_mod_cast residual_ne, ?_⟩
    rw [padicValRat.of_nat, residual_value]
    norm_num
  have three_unit : IsUnit 2 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have numerator_unit := mul_hasValue (unit_pow three_unit depth) residual_unit
  have two_power_value : HasValue 2 ((2 : ℚ) ^ depth) depth :=
    primePower_hasValue depth
  have denominator_value : HasValue 2 ((3 : ℚ) * 2 ^ depth * b)
      ((depth : ℕ) + padicValNat 2 b) := by
    have b_value : HasValue 2 (b : ℚ) (padicValNat 2 b : ℤ) := by
      refine ⟨by exact_mod_cast b_ne, padicValRat.of_nat⟩
    simpa only [zero_add] using
      mul_hasValue (mul_hasValue three_unit two_power_value) b_value
  have final_value := div_hasValue numerator_unit denominator_value
  refine ⟨final_value.1, ?_⟩
  change padicValRat 2
    ((3 : ℚ) ^ depth * upperCenteredNumerator a b / (3 * 2 ^ depth * b)) = _
  rw [final_value.2]
  ring

/-- Exact middle-branch two-adic transition from a reduced four-divisible denominator. -/
theorem middleNormalizedMantissa_twoValue_of_four_dvd_denominator
    {depth a b : ℕ} (b_ne : b ≠ 0) (ab : a.Coprime b) (four_dvd : 4 ∣ b)
    (positive : 3 * b < 5 * a) :
    HasValue 2 (middleNormalizedMantissa depth a b)
      (1 - (depth : ℕ) - padicValNat 2 b) := by
  have residual_ne : middleCenteredNumerator a b ≠ 0 := by
    simp only [middleCenteredNumerator]
    omega
  have residual_value :=
    middleCenteredNumerator_twoValue_of_four_dvd_denominator ab four_dvd positive
  have residual_unit : IsUnit 2 (middleCenteredNumerator a b : ℚ) := by
    refine ⟨by exact_mod_cast residual_ne, ?_⟩
    rw [padicValRat.of_nat, residual_value]
    norm_num
  have two_value : HasValue 2 (2 : ℚ) 1 := by
    simpa using primePower_hasValue (prime := 2) 1
  have three_unit : IsUnit 2 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have numerator_value :=
    mul_hasValue (mul_hasValue two_value (unit_pow three_unit depth)) residual_unit
  have two_power_value : HasValue 2 ((2 : ℚ) ^ depth) depth :=
    primePower_hasValue depth
  have nine_unit : IsUnit 2 (9 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have denominator_value : HasValue 2 ((9 : ℚ) * 2 ^ depth * b)
      ((depth : ℕ) + padicValNat 2 b) := by
    have b_value : HasValue 2 (b : ℚ) (padicValNat 2 b : ℤ) := by
      refine ⟨by exact_mod_cast b_ne, padicValRat.of_nat⟩
    simpa only [zero_add] using
      mul_hasValue (mul_hasValue nine_unit two_power_value) b_value
  have final_value := div_hasValue numerator_value denominator_value
  refine ⟨final_value.1, ?_⟩
  change padicValRat 2
    ((2 : ℚ) * 3 ^ depth * middleCenteredNumerator a b / (9 * 2 ^ depth * b)) = _
  rw [final_value.2]
  ring

/-- Exact lower-branch two-adic transition from a reduced four-divisible denominator. -/
theorem lowerNormalizedMantissa_twoValue_of_four_dvd_denominator
    {depth a b : ℕ} (b_ne : b ≠ 0) (ab : a.Coprime b) (four_dvd : 4 ∣ b)
    (positive : 9 * b < 10 * a) :
    HasValue 2 (lowerNormalizedMantissa depth a b)
      (1 - ((depth - 1 : ℕ) : ℤ) - padicValNat 2 b) := by
  have center_ne : lowerCenteredNumerator a b ≠ 0 := by
    simp only [lowerCenteredNumerator]
    omega
  have general := lowerNormalizedMantissa_twoValue (depth := depth) b_ne center_ne
  rw [lowerCenteredNumerator_twoValue_of_four_dvd_denominator ab four_dvd positive] at general
  simpa only [Nat.cast_one] using general

private theorem four_dvd_denominator_of_fraction_twoValue_le_negTwo
    {value : ℚ} {numerator denominator : ℕ} {shell : ℤ}
    (denominator_ne : denominator ≠ 0)
    (fraction_eq : value = (numerator : ℚ) / denominator)
    (value_shell : HasValue 2 value shell) (shell_le : shell ≤ -2) :
    4 ∣ denominator := by
  have numerator_ne : numerator ≠ 0 := by
    intro numerator_zero
    apply value_shell.1
    rw [fraction_eq, numerator_zero]
    norm_num
  have numerator_value : HasValue 2 (numerator : ℚ) (padicValNat 2 numerator : ℤ) := by
    refine ⟨by exact_mod_cast numerator_ne, padicValRat.of_nat⟩
  have denominator_value : HasValue 2 (denominator : ℚ)
      (padicValNat 2 denominator : ℤ) := by
    refine ⟨by exact_mod_cast denominator_ne, padicValRat.of_nat⟩
  have fraction_value := div_hasValue numerator_value denominator_value
  have valuation_eq :
      (padicValNat 2 numerator : ℤ) - padicValNat 2 denominator = shell := by
    calc
      (padicValNat 2 numerator : ℤ) - padicValNat 2 denominator =
          padicValRat 2 ((numerator : ℚ) / denominator) := fraction_value.2.symm
      _ = padicValRat 2 value := congrArg (padicValRat 2) fraction_eq.symm
      _ = shell := value_shell.2
  have denominator_value_two : 2 ≤ padicValNat 2 denominator := by omega
  exact (padicValNat_dvd_iff_le (p := 2) (n := 2) denominator_ne).mpr
    denominator_value_two

/-- The upper branch cannot leave the four-divisible denominator cone. -/
theorem upperNormalizedMantissa_four_dvd_successorDenominator
    {depth a b nextA nextB : ℕ} (b_ne : b ≠ 0) (ab : a.Coprime b)
    (four_dvd : 4 ∣ b) (positive : 2 * b < 5 * a) (nextB_ne : nextB ≠ 0)
    (next_eq : upperNormalizedMantissa depth a b = (nextA : ℚ) / nextB) :
    4 ∣ nextB := by
  have source_value_two : 2 ≤ padicValNat 2 b :=
    (padicValNat_dvd_iff_le (p := 2) (n := 2) b_ne).mp four_dvd
  have output_value :=
    upperNormalizedMantissa_twoValue_of_four_dvd_denominator
      (depth := depth) b_ne ab four_dvd positive
  apply four_dvd_denominator_of_fraction_twoValue_le_negTwo nextB_ne next_eq output_value
  omega

/-- At every actual middle depth, the middle branch cannot leave the four-divisible denominator
cone. -/
theorem middleNormalizedMantissa_four_dvd_successorDenominator
    {depth a b nextA nextB : ℕ} (depth_lower : 2 ≤ depth) (b_ne : b ≠ 0)
    (ab : a.Coprime b) (four_dvd : 4 ∣ b) (positive : 3 * b < 5 * a)
    (nextB_ne : nextB ≠ 0)
    (next_eq : middleNormalizedMantissa depth a b = (nextA : ℚ) / nextB) :
    4 ∣ nextB := by
  have source_value_two : 2 ≤ padicValNat 2 b :=
    (padicValNat_dvd_iff_le (p := 2) (n := 2) b_ne).mp four_dvd
  have output_value :=
    middleNormalizedMantissa_twoValue_of_four_dvd_denominator
      (depth := depth) b_ne ab four_dvd positive
  apply four_dvd_denominator_of_fraction_twoValue_le_negTwo nextB_ne next_eq output_value
  omega

/-- At every actual lower depth, the lower branch cannot leave the four-divisible denominator
cone. -/
theorem lowerNormalizedMantissa_four_dvd_successorDenominator
    {depth a b nextA nextB : ℕ} (depth_lower : 3 ≤ depth) (b_ne : b ≠ 0)
    (ab : a.Coprime b) (four_dvd : 4 ∣ b) (positive : 9 * b < 10 * a)
    (nextB_ne : nextB ≠ 0)
    (next_eq : lowerNormalizedMantissa depth a b = (nextA : ℚ) / nextB) :
    4 ∣ nextB := by
  have source_value_two : 2 ≤ padicValNat 2 b :=
    (padicValNat_dvd_iff_le (p := 2) (n := 2) b_ne).mp four_dvd
  have output_value :=
    lowerNormalizedMantissa_twoValue_of_four_dvd_denominator
      (depth := depth) b_ne ab four_dvd positive
  apply four_dvd_denominator_of_fraction_twoValue_le_negTwo nextB_ne next_eq output_value
  omega

/-- A lower branch from the secondary wall lands in exactly one of the absorbing cone, the wall,
or the nonnegative two-adic cone. -/
theorem lowerWall_outgoing_twoAdic_trichotomy
    {depth a c : ℕ} (depth_lower : 3 ≤ depth) (ab : a.Coprime (2 * c))
    (c_odd : Odd c) (positive : 18 * c < 10 * a) :
    let residualValue := padicValNat 2 (5 * a - 9 * c)
    (residualValue < depth - 2 ∧
        ∃ shell ≤ -2, HasValue 2 (lowerNormalizedMantissa depth a (2 * c)) shell) ∨
      (residualValue = depth - 2 ∧
        HasValue 2 (lowerNormalizedMantissa depth a (2 * c)) (-1)) ∨
      (depth - 2 < residualValue ∧
        ∃ shell, 0 ≤ shell ∧
          HasValue 2 (lowerNormalizedMantissa depth a (2 * c)) shell) := by
  let residualValue := padicValNat 2 (5 * a - 9 * c)
  have output_value :=
    lowerNormalizedMantissa_twoValue_of_exactlyOne_denominator
      (depth := depth) ab c_odd positive
  rcases lt_trichotomy residualValue (depth - 2) with
    residual_lt | residual_eq | residual_gt
  · left
    refine ⟨residual_lt, (residualValue : ℤ) - ((depth - 1 : ℕ) : ℤ), ?_, output_value⟩
    omega
  · right
    left
    refine ⟨residual_eq, ?_⟩
    convert output_value using 1
    omega
  · right
    right
    refine ⟨residual_gt, (residualValue : ℤ) - ((depth - 1 : ℕ) : ℤ), ?_, output_value⟩
    omega

end MatrixMortality.MixedPrimeDebt
