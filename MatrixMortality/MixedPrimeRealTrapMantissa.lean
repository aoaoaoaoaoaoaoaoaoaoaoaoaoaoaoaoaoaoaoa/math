import MatrixMortality.MixedPrimeRealTrapDepth

/-!
# Exact reverse mantissa recurrence in the mixed-prime real trap

A normalized target has three explicit predecessors, occupying disjoint source intervals. The
lowest branch is the only unbounded depth reset. In reduced coordinates its centered numerator
has no hidden cancellation outside the prime two, and the denominator wall at exact two-adic
value one is the sole secondary cancellation locus.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation

private local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
private local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The upper reverse candidate for a normalized target. -/
theorem shellStep_upperPredecessor (wait : ℕ) (mantissa : ℚ) :
    shellStep wait (mantissa / 2) = realTrapBandPoint wait mantissa := by
  simp only [shellStep, realTrapBandPoint]
  ring

/-- The middle reverse candidate for a normalized target. -/
theorem shellStep_middlePredecessor (wait : ℕ) (mantissa : ℚ) :
    shellStep wait (mantissa / 3) = realTrapBandPoint (wait + 1) mantissa := by
  simp only [shellStep, realTrapBandPoint, pow_add]
  norm_num
  ring

/-- The lower reverse candidate for a normalized target. -/
theorem shellStep_lowerPredecessor (wait : ℕ) (mantissa : ℚ) :
    shellStep wait (2 * mantissa / 9) = realTrapBandPoint (wait + 2) mantissa := by
  simp only [shellStep, realTrapBandPoint, pow_add]
  norm_num
  ring

/-- The upper candidate always occupies the upper source interval. -/
theorem upperPredecessor_mem
    {mantissa : ℚ} (lower : 2 / 3 < mantissa) (upper : mantissa ≤ 1) :
    mantissa / 2 ∈ Set.Ioc (1 / 3 : ℚ) (1 / 2) := by
  constructor <;> linarith

/-- The middle candidate always occupies the middle source interval. -/
theorem middlePredecessor_mem
    {mantissa : ℚ} (lower : 2 / 3 < mantissa) (upper : mantissa ≤ 1) :
    mantissa / 3 ∈ Set.Ioc (2 / 9 : ℚ) (1 / 3) := by
  constructor <;> linarith

/-- The lower candidate enters the real trap exactly above the pole mantissa `9/10`. -/
theorem lowerPredecessor_mem_iff
    {mantissa : ℚ} (upper : mantissa ≤ 1) :
    2 * mantissa / 9 ∈ Set.Ioc (1 / 5 : ℚ) (2 / 9) ↔ 9 / 10 < mantissa := by
  constructor
  · intro mem
    linarith [mem.1]
  · intro lower
    constructor <;> linarith

/-- Complete reverse address of one normalized real-trap target. The target depth chooses the
wait; the mantissa alone chooses the predecessor state. -/
theorem shellStep_realTrapBandPoint_iff_three_predecessors
    {state mantissa : ℚ} (state_mem : state ∈ Set.Ioc (1 / 5 : ℚ) (1 / 2))
    (mantissa_lower : 2 / 3 < mantissa) (mantissa_upper : mantissa ≤ 1)
    (wait depth : ℕ) :
    shellStep wait state = realTrapBandPoint depth mantissa ↔
      (depth = wait ∧ state = mantissa / 2) ∨
        (depth = wait + 1 ∧ state = mantissa / 3) ∨
          (depth = wait + 2 ∧ 9 / 10 < mantissa ∧ state = 2 * mantissa / 9) := by
  constructor
  · intro step_eq
    have target_mem := realTrapBandPoint_mem depth mantissa_lower mantissa_upper
    have wait_window := shellStep_realTrap_wait_window
      target_mem.1 target_mem.2 state_mem step_eq
    rw [realTrapMaxPredecessorWait_bandPoint depth mantissa_lower mantissa_upper] at wait_window
    rcases (show depth = wait ∨ depth = wait + 1 ∨ depth = wait + 2 by omega) with
      depth_eq | depth_eq | depth_eq
    · left
      refine ⟨depth_eq, ?_⟩
      apply shellStep_injective wait
      rw [step_eq, depth_eq]
      exact (shellStep_upperPredecessor wait mantissa).symm
    · right
      left
      refine ⟨depth_eq, ?_⟩
      apply shellStep_injective wait
      rw [step_eq, depth_eq]
      exact (shellStep_middlePredecessor wait mantissa).symm
    · right
      right
      have state_eq : state = 2 * mantissa / 9 := by
        apply shellStep_injective wait
        rw [step_eq, depth_eq]
        exact (shellStep_lowerPredecessor wait mantissa).symm
      have mantissa_nine_tenths : 9 / 10 < mantissa := by
        rw [state_eq] at state_mem
        exact (lowerPredecessor_mem_iff mantissa_upper).mp ⟨state_mem.1, by linarith⟩
      exact ⟨depth_eq, mantissa_nine_tenths, state_eq⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, _, rfl⟩)
    · exact shellStep_upperPredecessor _ mantissa
    · exact shellStep_middlePredecessor _ mantissa
    · exact shellStep_lowerPredecessor _ mantissa

/-- Centered numerator of the lower predecessor for a reduced mantissa `a/b`. -/
def lowerCenteredNumerator (a b : ℕ) : ℕ :=
  10 * a - 9 * b

/-- Normalized mantissa obtained when the lower predecessor lies in the displayed depth. -/
def lowerNormalizedMantissa (depth a b : ℕ) : ℚ :=
  3 ^ (depth - 3) * (lowerCenteredNumerator a b : ℚ) /
    (2 ^ (depth - 1) * b)

/-- For a reduced five-adic-unit mantissa, the lower centered numerator cancels with its old
denominator only at the prime two. -/
theorem lowerCenteredNumerator_gcd
    {a b : ℕ} (ab : a.Coprime b) (five_b : Nat.Coprime 5 b)
    (positive : 9 * b ≤ 10 * a) :
    Nat.gcd (lowerCenteredNumerator a b) b = Nat.gcd 2 b := by
  apply Nat.dvd_antisymm
  · let divisor := Nat.gcd (lowerCenteredNumerator a b) b
    have divisor_residual : divisor ∣ lowerCenteredNumerator a b := Nat.gcd_dvd_left _ _
    have divisor_b : divisor ∣ b := Nat.gcd_dvd_right _ _
    have divisor_ten_a : divisor ∣ 10 * a := by
      rw [show 10 * a = lowerCenteredNumerator a b + 9 * b by
        simp only [lowerCenteredNumerator]
        omega]
      exact Nat.dvd_add divisor_residual (dvd_mul_of_dvd_right divisor_b 9)
    have divisor_coprime_a : divisor.Coprime a :=
      ab.symm.of_dvd_left divisor_b
    have divisor_ten : divisor ∣ 10 := by
      rw [mul_comm] at divisor_ten_a
      exact divisor_coprime_a.dvd_of_dvd_mul_left divisor_ten_a
    have divisor_coprime_five : divisor.Coprime 5 :=
      five_b.symm.of_dvd_left divisor_b
    have divisor_two : divisor ∣ 2 := by
      have divisor_two_five : divisor ∣ 2 * 5 := by
        norm_num at divisor_ten ⊢
        exact divisor_ten
      exact divisor_coprime_five.dvd_of_dvd_mul_right divisor_two_five
    exact Nat.dvd_gcd divisor_two divisor_b
  · let divisor := Nat.gcd 2 b
    have divisor_two : divisor ∣ 2 := Nat.gcd_dvd_left _ _
    have divisor_b : divisor ∣ b := Nat.gcd_dvd_right _ _
    have divisor_ten_a : divisor ∣ 10 * a :=
      dvd_mul_of_dvd_left (dvd_mul_of_dvd_left divisor_two 5) a
    have divisor_nine_b : divisor ∣ 9 * b := dvd_mul_of_dvd_right divisor_b 9
    exact Nat.dvd_gcd (Nat.dvd_sub divisor_ten_a divisor_nine_b) divisor_b

/-- An odd old denominator gives no two-adic centered cancellation. -/
theorem lowerCenteredNumerator_twoValue_of_oddDenominator
    {a b : ℕ} (b_odd : Odd b) (positive : 9 * b < 10 * a) :
    padicValNat 2 (lowerCenteredNumerator a b) = 0 := by
  rcases b_odd with ⟨half, rfl⟩
  have residual_odd : Odd (lowerCenteredNumerator a (2 * half + 1)) := by
    refine ⟨5 * a - 9 * half - 5, ?_⟩
    simp only [lowerCenteredNumerator]
    omega
  apply padicValNat.eq_zero_of_not_dvd
  exact Nat.prime_two.coprime_iff_not_dvd.mp residual_odd.coprime_two_left

/-- A denominator divisible by four forces exactly one two-adic factor in the centered
numerator. -/
theorem lowerCenteredNumerator_twoValue_of_four_dvd_denominator
    {a b : ℕ} (ab : a.Coprime b) (four_dvd : 4 ∣ b)
    (positive : 9 * b < 10 * a) :
    padicValNat 2 (lowerCenteredNumerator a b) = 1 := by
  obtain ⟨quarter, rfl⟩ := four_dvd
  have two_dvd_b : 2 ∣ 4 * quarter := ⟨2 * quarter, by omega⟩
  have a_odd : Odd a := (ab.of_dvd_right two_dvd_b).odd_of_right
  obtain ⟨half, rfl⟩ := a_odd
  have residual_ne : lowerCenteredNumerator (2 * half + 1) (4 * quarter) ≠ 0 := by
    simp only [lowerCenteredNumerator]
    omega
  have two_dvd_residual : 2 ∣ lowerCenteredNumerator (2 * half + 1) (4 * quarter) := by
    refine ⟨5 * (2 * half + 1) - 18 * quarter, ?_⟩
    simp only [lowerCenteredNumerator]
    omega
  have not_four_dvd_residual : ¬4 ∣ lowerCenteredNumerator (2 * half + 1) (4 * quarter) := by
    rintro ⟨value, value_eq⟩
    simp only [lowerCenteredNumerator] at value_eq
    omega
  have one_le : 1 ≤ padicValNat 2 (lowerCenteredNumerator (2 * half + 1) (4 * quarter)) :=
    (padicValNat_dvd_iff_le residual_ne).mp (by simpa using two_dvd_residual)
  have not_two_le :
      ¬2 ≤ padicValNat 2 (lowerCenteredNumerator (2 * half + 1) (4 * quarter)) := by
    intro two_le
    have four_dvd := (padicValNat_dvd_iff_le residual_ne).mpr two_le
    norm_num at four_dvd
    exact not_four_dvd_residual four_dvd
  omega

/-- On the exact denominator wall `b=2c`, the centered numerator is twice the secondary
residual. -/
theorem lowerCenteredNumerator_eq_twice_center
    {a c : ℕ} (positive : 18 * c < 10 * a) :
    lowerCenteredNumerator a (2 * c) = 2 * (5 * a - 9 * c) := by
  simp only [lowerCenteredNumerator]
  omega

/-- The exact denominator wall exposes every remaining two-adic cancellation in the secondary
residual `5a-9c`. -/
theorem lowerCenteredNumerator_twoValue_of_exactlyOne_denominator
    {a c : ℕ} (ab : a.Coprime (2 * c)) (c_odd : Odd c)
    (positive : 18 * c < 10 * a) :
    padicValNat 2 (lowerCenteredNumerator a (2 * c)) =
      1 + padicValNat 2 (5 * a - 9 * c) := by
  have two_dvd_b : 2 ∣ 2 * c := by simp
  have a_odd : Odd a := (ab.of_dvd_right two_dvd_b).odd_of_right
  obtain ⟨aHalf, rfl⟩ := a_odd
  obtain ⟨cHalf, rfl⟩ := c_odd
  have center_ne : 5 * (2 * aHalf + 1) - 9 * (2 * cHalf + 1) ≠ 0 := by omega
  rw [lowerCenteredNumerator_eq_twice_center positive,
    padicValNat.mul (by norm_num : (2 : ℕ) ≠ 0) center_ne, padicValNat_self]

/-- Exact two-adic value of the normalized lower-branch mantissa, including every gcd
cancellation. -/
theorem lowerNormalizedMantissa_twoValue
    {depth a b : ℕ} (b_ne : b ≠ 0) (center_ne : lowerCenteredNumerator a b ≠ 0) :
    HasValue 2 (lowerNormalizedMantissa depth a b)
      ((padicValNat 2 (lowerCenteredNumerator a b) : ℤ) -
        ((depth - 1 : ℕ) : ℤ) - padicValNat 2 b) := by
  have three_unit : IsUnit 2 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have three_power_unit : IsUnit 2 ((3 : ℚ) ^ (depth - 3)) := by
    refine ⟨pow_ne_zero _ three_unit.1, ?_⟩
    rw [padicValRat.pow, three_unit.2]
    simp
  have center_value :
      HasValue 2 (lowerCenteredNumerator a b : ℚ)
        (padicValNat 2 (lowerCenteredNumerator a b) : ℤ) := by
    refine ⟨by exact_mod_cast center_ne, padicValRat.of_nat⟩
  have numerator_value := mul_hasValue three_power_unit center_value
  have two_power_value :
      HasValue 2 ((2 : ℚ) ^ (depth - 1)) ((depth - 1 : ℕ) : ℤ) :=
    primePower_hasValue (depth - 1)
  have b_value : HasValue 2 (b : ℚ) (padicValNat 2 b : ℤ) := by
    refine ⟨by exact_mod_cast b_ne, padicValRat.of_nat⟩
  have denominator_value := mul_hasValue two_power_value b_value
  have final_value := div_hasValue numerator_value denominator_value
  have valuation_eq :
      (padicValNat 2 (lowerCenteredNumerator a b) : ℤ) -
          ((depth - 1 : ℕ) : ℤ) - padicValNat 2 b =
        0 + (padicValNat 2 (lowerCenteredNumerator a b) : ℤ) -
          (((depth - 1 : ℕ) : ℤ) + padicValNat 2 b) := by
    ring
  rw [valuation_eq]
  simpa only [lowerNormalizedMantissa] using final_value

/-- Exact three-adic value of the normalized lower-branch mantissa. -/
theorem lowerNormalizedMantissa_threeValue
    {depth a b : ℕ} (b_ne : b ≠ 0) (center_ne : lowerCenteredNumerator a b ≠ 0) :
    HasValue 3 (lowerNormalizedMantissa depth a b)
      (((depth - 3 : ℕ) : ℤ) + padicValNat 3 (lowerCenteredNumerator a b) -
        padicValNat 3 b) := by
  have three_power_value :
      HasValue 3 ((3 : ℚ) ^ (depth - 3)) ((depth - 3 : ℕ) : ℤ) :=
    primePower_hasValue (depth - 3)
  have center_value :
      HasValue 3 (lowerCenteredNumerator a b : ℚ)
        (padicValNat 3 (lowerCenteredNumerator a b) : ℤ) := by
    refine ⟨by exact_mod_cast center_ne, padicValRat.of_nat⟩
  have numerator_value := mul_hasValue three_power_value center_value
  have two_unit : IsUnit 3 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have two_power_unit : IsUnit 3 ((2 : ℚ) ^ (depth - 1)) := by
    refine ⟨pow_ne_zero _ two_unit.1, ?_⟩
    rw [padicValRat.pow, two_unit.2]
    simp
  have b_value : HasValue 3 (b : ℚ) (padicValNat 3 b : ℤ) := by
    refine ⟨by exact_mod_cast b_ne, padicValRat.of_nat⟩
  have denominator_value := mul_hasValue two_power_unit b_value
  have final_value := div_hasValue numerator_value denominator_value
  have valuation_eq :
      ((depth - 3 : ℕ) : ℤ) + padicValNat 3 (lowerCenteredNumerator a b) -
          padicValNat 3 b =
        (((depth - 3 : ℕ) : ℤ) + padicValNat 3 (lowerCenteredNumerator a b)) -
          (0 + padicValNat 3 b) := by
    ring
  rw [valuation_eq]
  simpa only [lowerNormalizedMantissa] using final_value

/-- On the secondary wall, the outgoing two-adic value is exactly the centered residual value
minus the displayed depth cost. -/
theorem lowerNormalizedMantissa_twoValue_of_exactlyOne_denominator
    {depth a c : ℕ} (ab : a.Coprime (2 * c)) (c_odd : Odd c)
    (positive : 18 * c < 10 * a) :
    HasValue 2 (lowerNormalizedMantissa depth a (2 * c))
      ((padicValNat 2 (5 * a - 9 * c) : ℤ) - ((depth - 1 : ℕ) : ℤ)) := by
  have c_ne : c ≠ 0 := by
    rintro rfl
    simp at c_odd
  have denominator_ne : 2 * c ≠ 0 := mul_ne_zero (by norm_num) c_ne
  have center_ne : 5 * a - 9 * c ≠ 0 := by omega
  have residual_ne : lowerCenteredNumerator a (2 * c) ≠ 0 := by
    rw [lowerCenteredNumerator_eq_twice_center positive]
    exact mul_ne_zero (by norm_num) center_ne
  have denominator_value : padicValNat 2 (2 * c) = 1 := by
    rw [padicValNat.mul (by norm_num : (2 : ℕ) ≠ 0) c_ne,
      padicValNat_self, padicValNat.eq_zero_of_not_dvd]
    exact Nat.prime_two.coprime_iff_not_dvd.mp c_odd.coprime_two_left
  have general := lowerNormalizedMantissa_twoValue
    (depth := depth) denominator_ne residual_ne
  rw [lowerCenteredNumerator_twoValue_of_exactlyOne_denominator ab c_odd positive,
    denominator_value] at general
  simp only [Nat.cast_add, Nat.cast_one] at general
  convert general using 1
  ring

/-- The displayed lower mantissa is exactly the normalized coordinate of the lower predecessor. -/
theorem realTrapBandPoint_lowerNormalizedMantissa
    {depth a b : ℕ} (depth_lower : 3 ≤ depth) (b_ne : b ≠ 0)
    (positive : 9 * b ≤ 10 * a) :
    realTrapBandPoint depth (lowerNormalizedMantissa depth a b) =
      2 * ((a : ℚ) / b) / 9 := by
  have center_cast :
      (lowerCenteredNumerator a b : ℚ) = 10 * a - 9 * b := by
    rw [lowerCenteredNumerator, Nat.cast_sub positive]
    norm_num
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le depth_lower
  simp only [realTrapBandPoint, lowerNormalizedMantissa, center_cast]
  simp only [Nat.add_sub_cancel_left, pow_add]
  norm_num [pow_succ]
  rw [div_pow]
  field_simp
  ring

end MatrixMortality.MixedPrimeDebt
