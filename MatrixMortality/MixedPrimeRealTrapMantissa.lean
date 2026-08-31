import MatrixMortality.MixedPrimeRealTrapDepth

/-!
# Exact reverse mantissa recurrence in the mixed-prime real trap

A normalized target has three explicit predecessors, occupying disjoint source intervals. The
lowest branch is the only unbounded depth reset. In reduced coordinates its centered numerator
has no hidden cancellation outside the prime two, and the denominator wall at exact two-adic
value one is the sole secondary cancellation locus. An explicit reduced five-adic-unit fixed
family on that wall has unbounded centered cancellation, so no strict height or odd-part descent
can hold across all repeated lower branches.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation
open PeriodicShell

private local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
private local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

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

private theorem two_pow_six_add_le_three_pow_four_add (offset : ℕ) :
    2 ^ (6 + offset) ≤ 3 ^ (4 + offset) := by
  induction offset with
  | zero => norm_num
  | succ offset induction =>
      rw [Nat.add_succ, Nat.add_succ, pow_succ, pow_succ]
      exact (Nat.mul_le_mul_right 2 induction).trans
        (Nat.mul_le_mul_left (3 ^ (4 + offset)) (by norm_num))

/-- Numerator of the centered lower-branch fixed mantissa at one displayed depth. -/
def lowerFixedNumerator (depth : ℕ) : ℕ :=
  3 ^ (depth - 1)

/-- Denominator of the centered lower-branch fixed mantissa at one displayed depth. -/
def lowerFixedDenominator (depth : ℕ) : ℕ :=
  10 * 3 ^ (depth - 3) - 2 ^ (depth - 1)

private theorem lowerFixed_power_le
    {depth : ℕ} (depth_lower : 7 ≤ depth) :
    2 ^ (depth - 1) ≤ 3 ^ (depth - 3) := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le depth_lower
  have left_exponent : 7 + offset - 1 = 6 + offset := by omega
  have right_exponent : 7 + offset - 3 = 4 + offset := by omega
  rw [left_exponent, right_exponent]
  exact two_pow_six_add_le_three_pow_four_add offset

private theorem lowerFixedNumerator_eq_nine_mul
    {depth : ℕ} (depth_lower : 3 ≤ depth) :
    lowerFixedNumerator depth = 9 * 3 ^ (depth - 3) := by
  have exponent : depth - 3 + 2 = depth - 1 := by omega
  rw [lowerFixedNumerator, ← exponent, pow_add]
  norm_num
  ring

private theorem lowerFixedNumerator_le_denominator
    {depth : ℕ} (depth_lower : 7 ≤ depth) :
    lowerFixedNumerator depth ≤ lowerFixedDenominator depth := by
  have power_le := lowerFixed_power_le depth_lower
  rw [lowerFixedNumerator_eq_nine_mul (by omega), lowerFixedDenominator]
  omega

/-- The fixed-family lower centered numerator is an explicit growing power of two. -/
theorem lowerFixed_centeredNumerator
    {depth : ℕ} (depth_lower : 7 ≤ depth) :
    lowerCenteredNumerator (lowerFixedNumerator depth) (lowerFixedDenominator depth) =
      9 * 2 ^ (depth - 1) := by
  have power_le := lowerFixed_power_le depth_lower
  have numerator_eq := lowerFixedNumerator_eq_nine_mul (by omega : 3 ≤ depth)
  simp only [lowerCenteredNumerator, lowerFixedNumerator, lowerFixedDenominator]
  simp only [lowerFixedNumerator] at numerator_eq
  rw [numerator_eq]
  omega

private theorem lowerFixed_denominator_ne
    {depth : ℕ} (depth_lower : 7 ≤ depth) : lowerFixedDenominator depth ≠ 0 := by
  have numerator_positive : 0 < lowerFixedNumerator depth := by
    simp [lowerFixedNumerator]
  have numerator_le := lowerFixedNumerator_le_denominator depth_lower
  omega

private theorem lowerFixed_three_not_dvd_denominator
    {depth : ℕ} (depth_lower : 7 ≤ depth) : ¬3 ∣ lowerFixedDenominator depth := by
  intro three_dvd_b
  have power_le := lowerFixed_power_le depth_lower
  have two_power_le_first : 2 ^ (depth - 1) ≤ 10 * 3 ^ (depth - 3) := by omega
  have decomposition :
      lowerFixedDenominator depth + 2 ^ (depth - 1) = 10 * 3 ^ (depth - 3) := by
    exact Nat.sub_add_cancel two_power_le_first
  have three_dvd_first : 3 ∣ 10 * 3 ^ (depth - 3) := by
    exact dvd_mul_of_dvd_right (dvd_pow_self 3 (by omega)) 10
  have three_dvd_two_power : 3 ∣ 2 ^ (depth - 1) := by
    rw [← decomposition] at three_dvd_first
    exact (Nat.dvd_add_iff_right three_dvd_b).mpr three_dvd_first
  have three_two_power_coprime : Nat.Coprime 3 (2 ^ (depth - 1)) :=
    (by norm_num : Nat.Coprime 3 2).pow_right (depth - 1)
  have three_eq_one := three_two_power_coprime.eq_one_of_dvd three_dvd_two_power
  omega

/-- The fixed-family numerator and denominator are reduced. -/
theorem lowerFixed_coprime
    {depth : ℕ} (depth_lower : 7 ≤ depth) :
    (lowerFixedNumerator depth).Coprime (lowerFixedDenominator depth) := by
  have three_coprime : Nat.Coprime 3 (lowerFixedDenominator depth) :=
    Nat.prime_three.coprime_iff_not_dvd.mpr
      (lowerFixed_three_not_dvd_denominator depth_lower)
  simpa only [lowerFixedNumerator] using three_coprime.pow_left (depth - 1)

/-- The fixed-family denominator is coprime to five. -/
theorem lowerFixed_five_coprime_denominator
    {depth : ℕ} (depth_lower : 7 ≤ depth) :
    Nat.Coprime 5 (lowerFixedDenominator depth) := by
  apply Nat.prime_five.coprime_iff_not_dvd.mpr
  intro five_dvd_b
  have power_le := lowerFixed_power_le depth_lower
  have two_power_le_first : 2 ^ (depth - 1) ≤ 10 * 3 ^ (depth - 3) := by omega
  have decomposition :
      lowerFixedDenominator depth + 2 ^ (depth - 1) = 10 * 3 ^ (depth - 3) := by
    exact Nat.sub_add_cancel two_power_le_first
  have five_dvd_first : 5 ∣ 10 * 3 ^ (depth - 3) :=
    ⟨2 * 3 ^ (depth - 3), by ring⟩
  have five_dvd_two_power : 5 ∣ 2 ^ (depth - 1) := by
    rw [← decomposition] at five_dvd_first
    exact (Nat.dvd_add_iff_right five_dvd_b).mpr five_dvd_first
  have five_two_power_coprime : Nat.Coprime 5 (2 ^ (depth - 1)) :=
    (by norm_num : Nat.Coprime 5 2).pow_right (depth - 1)
  have five_eq_one := five_two_power_coprime.eq_one_of_dvd five_dvd_two_power
  omega

/-- Every fixed-family denominator lies on the secondary wall `v₂(b)=1`. -/
theorem lowerFixed_denominator_twoValue
    {depth : ℕ} (depth_lower : 7 ≤ depth) :
    padicValNat 2 (lowerFixedDenominator depth) = 1 := by
  have power_le := lowerFixed_power_le depth_lower
  have two_power_le_first : 2 ^ (depth - 1) ≤ 10 * 3 ^ (depth - 3) := by omega
  have four_dvd_two_power : 4 ∣ 2 ^ (depth - 1) := by
    change 2 ^ 2 ∣ 2 ^ (depth - 1)
    exact pow_dvd_pow 2 (by omega)
  have two_dvd_first : 2 ∣ 10 * 3 ^ (depth - 3) :=
    dvd_mul_of_dvd_left (by norm_num) _
  have two_dvd_two_power : 2 ∣ 2 ^ (depth - 1) := dvd_pow_self 2 (by omega)
  have two_dvd_denominator : 2 ∣ lowerFixedDenominator depth := by
    exact Nat.dvd_sub two_dvd_first two_dvd_two_power
  have not_four_dvd_denominator : ¬4 ∣ lowerFixedDenominator depth := by
    intro four_dvd
    have four_dvd_first : 4 ∣ 10 * 3 ^ (depth - 3) := by
      have decomposition := Nat.sub_add_cancel two_power_le_first
      rw [← decomposition]
      exact Nat.dvd_add four_dvd four_dvd_two_power
    have four_three_power_coprime : Nat.Coprime 4 (3 ^ (depth - 3)) :=
      (by norm_num : Nat.Coprime 4 3).pow_right (depth - 3)
    have four_dvd_ten : 4 ∣ 10 :=
      four_three_power_coprime.dvd_of_dvd_mul_right four_dvd_first
    norm_num at four_dvd_ten
  have denominator_ne := lowerFixed_denominator_ne depth_lower
  have one_le := (padicValNat_dvd_iff_le (p := 2) (n := 1) denominator_ne).mp (by
    simpa using two_dvd_denominator)
  have not_two_le : ¬2 ≤ padicValNat 2 (lowerFixedDenominator depth) := by
    intro two_le
    have four_dvd :=
      (padicValNat_dvd_iff_le (p := 2) (n := 2) denominator_ne).mpr two_le
    norm_num at four_dvd
    exact not_four_dvd_denominator four_dvd
  omega

/-- The fixed-family centered numerator has unbounded exact two-adic value. -/
theorem lowerFixed_centeredNumerator_twoValue
    {depth : ℕ} (depth_lower : 7 ≤ depth) :
    padicValNat 2
        (lowerCenteredNumerator (lowerFixedNumerator depth) (lowerFixedDenominator depth)) =
      depth - 1 := by
  rw [lowerFixed_centeredNumerator depth_lower, padicValNat.mul]
  · rw [padicValNat.prime_pow]
    norm_num
  · norm_num
  · positivity

/-- The fixed-family secondary center has unbounded exact two-adic value. -/
theorem lowerFixed_secondaryCenter_twoValue
    {depth : ℕ} (depth_lower : 7 ≤ depth) :
    padicValNat 2
        (5 * lowerFixedNumerator depth - 9 * (lowerFixedDenominator depth / 2)) =
      depth - 2 := by
  have denominator_ne := lowerFixed_denominator_ne depth_lower
  have denominator_value := lowerFixed_denominator_twoValue depth_lower
  have one_le : 1 ≤ padicValNat 2 (lowerFixedDenominator depth) := by omega
  have two_dvd : 2 ∣ lowerFixedDenominator depth :=
    (padicValNat_dvd_iff_le (p := 2) (n := 1) denominator_ne).mpr one_le
  have denominator_eq : 2 * (lowerFixedDenominator depth / 2) =
      lowerFixedDenominator depth := Nat.mul_div_cancel' two_dvd
  have half_ne : lowerFixedDenominator depth / 2 ≠ 0 := by
    intro half_zero
    rw [half_zero, mul_zero] at denominator_eq
    exact denominator_ne denominator_eq.symm
  have half_not_even : ¬2 ∣ lowerFixedDenominator depth / 2 := by
    intro half_even
    have four_dvd : 2 ^ 2 ∣ lowerFixedDenominator depth := by
      rw [← denominator_eq, pow_two]
      exact Nat.mul_dvd_mul_left 2 half_even
    have two_le :=
      (padicValNat_dvd_iff_le (p := 2) (n := 2) denominator_ne).mp four_dvd
    omega
  have half_odd : Odd (lowerFixedDenominator depth / 2) :=
    Nat.prime_two.coprime_iff_not_dvd.mpr half_not_even |>.odd_of_left
  have coprime : (lowerFixedNumerator depth).Coprime
      (2 * (lowerFixedDenominator depth / 2)) := by
    rw [denominator_eq]
    exact lowerFixed_coprime depth_lower
  have positive : 18 * (lowerFixedDenominator depth / 2) <
      10 * lowerFixedNumerator depth := by
    rw [show 18 * (lowerFixedDenominator depth / 2) =
      9 * lowerFixedDenominator depth by omega]
    have centered := lowerFixed_centeredNumerator depth_lower
    have centered_positive : 0 < lowerCenteredNumerator
        (lowerFixedNumerator depth) (lowerFixedDenominator depth) := by
      rw [centered]
      positivity
    simpa only [lowerCenteredNumerator, Nat.sub_pos_iff_lt] using centered_positive
  have wall_value := lowerCenteredNumerator_twoValue_of_exactlyOne_denominator
    coprime half_odd positive
  rw [denominator_eq, lowerFixed_centeredNumerator_twoValue depth_lower] at wall_value
  omega

/-- The lower normalized recurrence fixes the displayed reduced mantissa exactly. -/
theorem lowerNormalizedMantissa_fixed
    {depth : ℕ} (depth_lower : 7 ≤ depth) :
    lowerNormalizedMantissa depth (lowerFixedNumerator depth) (lowerFixedDenominator depth) =
      (lowerFixedNumerator depth : ℚ) / lowerFixedDenominator depth := by
  have denominator_ne := lowerFixed_denominator_ne depth_lower
  have centered := lowerFixed_centeredNumerator depth_lower
  have depth_three : depth - 3 + 2 = depth - 1 := by omega
  rw [lowerNormalizedMantissa, centered, lowerFixedNumerator]
  rw [← depth_three, pow_add]
  simp only [pow_add]
  norm_num
  field_simp

/-- Reduced mantissa of the lower-branch fixed point at one depth. -/
def lowerFixedMantissa (depth : ℕ) : ℚ :=
  (lowerFixedNumerator depth : ℚ) / lowerFixedDenominator depth

/-- Every fixed-family mantissa lies strictly above the lower-branch threshold and at most one. -/
theorem lowerFixedMantissa_normalized
    {depth : ℕ} (depth_lower : 7 ≤ depth) :
    9 / 10 < lowerFixedMantissa depth ∧ lowerFixedMantissa depth ≤ 1 := by
  have denominator_ne := lowerFixed_denominator_ne depth_lower
  have numerator_le := lowerFixedNumerator_le_denominator depth_lower
  have centered := lowerFixed_centeredNumerator depth_lower
  have centered_positive : 0 < lowerCenteredNumerator
      (lowerFixedNumerator depth) (lowerFixedDenominator depth) := by
    rw [centered]
    positivity
  have lower_nat : 9 * lowerFixedDenominator depth < 10 * lowerFixedNumerator depth := by
    simpa only [lowerCenteredNumerator, Nat.sub_pos_iff_lt] using centered_positive
  have denominator_positive : (0 : ℚ) < lowerFixedDenominator depth := by
    exact_mod_cast Nat.zero_lt_of_ne_zero denominator_ne
  have lower_rat :
      (9 : ℚ) * lowerFixedDenominator depth < 10 * lowerFixedNumerator depth := by
    exact_mod_cast lower_nat
  constructor
  · rw [lowerFixedMantissa, lt_div_iff₀ denominator_positive]
    nlinarith
  · rw [lowerFixedMantissa, div_le_one denominator_positive]
    exact_mod_cast numerator_le

/-- The fixed-family band point is its own lower predecessor. -/
theorem realTrapBandPoint_lowerFixedMantissa_eq_lowerPredecessor
    {depth : ℕ} (depth_lower : 7 ≤ depth) :
    realTrapBandPoint depth (lowerFixedMantissa depth) =
      2 * lowerFixedMantissa depth / 9 := by
  have normalized := lowerNormalizedMantissa_fixed depth_lower
  have predecessor := realTrapBandPoint_lowerNormalizedMantissa
    (a := lowerFixedNumerator depth) (b := lowerFixedDenominator depth)
    (depth := depth) (by omega) (lowerFixed_denominator_ne depth_lower) (by
      have centered := lowerFixed_centeredNumerator depth_lower
      have centered_positive : 0 < lowerCenteredNumerator
          (lowerFixedNumerator depth) (lowerFixedDenominator depth) := by
        rw [centered]
        positivity
      exact (Nat.sub_pos_iff_lt.mp
        (by simpa only [lowerCenteredNumerator] using centered_positive)).le)
  rw [normalized] at predecessor
  exact predecessor

/-- Every depth at least seven carries a rational lower-branch fixed point. -/
theorem shellStep_lowerFixedPoint
    {depth : ℕ} (depth_lower : 7 ≤ depth) :
    shellStep (depth - 2) (realTrapBandPoint depth (lowerFixedMantissa depth)) =
      realTrapBandPoint depth (lowerFixedMantissa depth) := by
  have state_eq := realTrapBandPoint_lowerFixedMantissa_eq_lowerPredecessor depth_lower
  calc
    shellStep (depth - 2) (realTrapBandPoint depth (lowerFixedMantissa depth)) =
        shellStep (depth - 2) (2 * lowerFixedMantissa depth / 9) := by rw [state_eq]
    _ = realTrapBandPoint ((depth - 2) + 2) (lowerFixedMantissa depth) :=
      shellStep_lowerPredecessor (depth - 2) (lowerFixedMantissa depth)
    _ = realTrapBandPoint depth (lowerFixedMantissa depth) := by
      rw [Nat.sub_add_cancel (by omega : 2 ≤ depth)]

private theorem lowerFixedMantissa_fiveUnit
    {depth : ℕ} (depth_lower : 7 ≤ depth) :
    IsUnit 5 (lowerFixedMantissa depth) := by
  have numerator_unit : IsUnit 5 (lowerFixedNumerator depth : ℚ) := by
    rw [lowerFixedNumerator, Nat.cast_pow]
    have three_unit : IsUnit 5 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
    have three_value : padicValRat 5 ((3 : ℕ) : ℚ) = 0 := by
      simpa using three_unit.2
    refine ⟨pow_ne_zero _ three_unit.1, ?_⟩
    rw [padicValRat.pow, three_value]
    simp
  have denominator_not_dvd_nat : ¬5 ∣ lowerFixedDenominator depth :=
    Nat.prime_five.coprime_iff_not_dvd.mp
      (lowerFixed_five_coprime_denominator depth_lower)
  have denominator_not_dvd_int :
      ¬(5 : ℤ) ∣ (lowerFixedDenominator depth : ℤ) := by
    exact_mod_cast denominator_not_dvd_nat
  have denominator_unit : IsUnit 5 (lowerFixedDenominator depth : ℚ) := by
    simpa using intCast_isUnit_of_not_dvd (prime := 5) denominator_not_dvd_int
  exact div_hasValue numerator_unit denominator_unit

/-- Every lower-branch fixed state is a five-adic unit. -/
theorem lowerFixedPoint_fiveUnit
    {depth : ℕ} (depth_lower : 7 ≤ depth) :
    IsUnit 5 (realTrapBandPoint depth (lowerFixedMantissa depth)) := by
  have two_unit : IsUnit 5 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have nine_unit : IsUnit 5 (9 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  rw [realTrapBandPoint_lowerFixedMantissa_eq_lowerPredecessor depth_lower]
  exact div_hasValue
    (mul_hasValue two_unit (lowerFixedMantissa_fiveUnit depth_lower)) nine_unit

/-- Every repetition of the lower wait fixes its displayed state. -/
theorem shellRun_replicate_lowerFixedPoint
    {depth : ℕ} (depth_lower : 7 ≤ depth) (repetitions : ℕ) :
    shellRun (List.replicate repetitions (depth - 2))
        (realTrapBandPoint depth (lowerFixedMantissa depth)) =
      realTrapBandPoint depth (lowerFixedMantissa depth) := by
  induction repetitions with
  | zero => rfl
  | succ repetitions induction =>
      rw [List.replicate_succ, shellRun_cons,
        shellStep_lowerFixedPoint depth_lower, induction]

/-- Every phase of every repeated lower fixed-point schedule is accepted. -/
theorem shellRun_replicate_lowerFixedPoint_guarded
    {depth : ℕ} (depth_lower : 7 ≤ depth) (repetitions : ℕ) :
    ∀ front back,
      List.replicate repetitions (depth - 2) = front ++ back →
        IsUnit 5
          (shellRun front (realTrapBandPoint depth (lowerFixedMantissa depth))) := by
  apply (shellPrefixesUnit_iff (List.replicate repetitions (depth - 2))
    (realTrapBandPoint depth (lowerFixedMantissa depth))).2
  rw [shellRun_replicate_lowerFixedPoint depth_lower repetitions]
  exact lowerFixedPoint_fiveUnit depth_lower

end MatrixMortality.MixedPrimeDebt
