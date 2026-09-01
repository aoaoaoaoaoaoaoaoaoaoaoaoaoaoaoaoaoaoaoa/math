import MatrixMortality.MixedPrimeRealTrapPrefixCarry

/-!
# Length-two mixed-sign shell crossings

Every positive-source cross-grade pair of two-wait schedules has, up to swapping, one canonical
mixed-sign normal form. Its collision source and common target are explicit. Source acceptance
is equality of two parity/LTE depths; target acceptance forces the next depth and then depends
on only ten tail residues. The real trap forces the transfer gap to one or two; the remaining
gap lies in one of two explicit residue families and has target period fifty or 250. For fixed
gaps, the real-trap gauge occupies at most three consecutive natural numbers.

The accepted length-two parameter language is therefore an explicit finite union of affine
congruence families. This does not bound longer crossing walks or collapse their higher-depth
tied carry trees.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation
open PeriodicShell

private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Left schedule in the canonical positive length-two crossing orientation. -/
def lengthTwoCrossingLeft (b c k gap : ℕ) : List ℕ :=
  [c + k + gap, b]

/-- Right schedule in the canonical positive length-two crossing orientation. -/
def lengthTwoCrossingRight (b c k : ℕ) : List ℕ :=
  [c, b + k]

/-- Collision source of the canonical length-two crossing family. -/
def lengthTwoCrossingSource (c k gap : ℕ) : ℚ :=
  (1 - (2 / 3 : ℚ) ^ k) /
    (3 * (2 / 3 : ℚ) ^ (c + k) * (1 - (2 / 3 : ℚ) ^ gap))

/-- Common target of the canonical length-two crossing family. -/
def lengthTwoCrossingTarget (b k gap : ℕ) : ℚ :=
  (5 + 3 * (2 / 3 : ℚ) ^ b *
      (1 - (2 / 3 : ℚ) ^ (gap + k)) / (1 - (2 / 3 : ℚ) ^ gap)) / 25

/-- Numerator remaining after clearing the target's forced gap and square five-power. -/
def lengthTwoCrossingTargetNumerator (b k gap : ℕ) : ℚ :=
  5 * (1 - (2 / 3 : ℚ) ^ gap) +
    3 * (2 / 3 : ℚ) ^ b * (1 - (2 / 3 : ℚ) ^ (gap + k))

theorem lengthTwoCrossing_normalForm_iff (a b c d : ℕ) :
    b < d ∧ c + d < a + b ↔
      ∃ k gap, 0 < k ∧ 0 < gap ∧ a = c + k + gap ∧ d = b + k := by
  constructor
  · rintro ⟨tail_lt, total_lt⟩
    refine ⟨d - b, a + b - (c + d), by omega, by omega, ?_, by omega⟩
    omega
  · rintro ⟨k, gap, k_positive, gap_positive, rfl, rfl⟩
    omega

theorem lengthTwoCrossing_normalForm_unique
    {leftHead leftTail rightHead rightTail k₁ gap₁ k₂ gap₂ : ℕ}
    (first : leftHead = rightHead + k₁ + gap₁ ∧ rightTail = leftTail + k₁)
    (second : leftHead = rightHead + k₂ + gap₂ ∧ rightTail = leftTail + k₂) :
    k₁ = k₂ ∧ gap₁ = gap₂ := by
  omega

private theorem shellOffset_pair (first second : ℕ) :
    shellOffset [first, second] = shellScale second + 5 := by
  have run_nil : shellRun [] (0 : ℚ) = 0 := rfl
  have offset_nil : shellOffset [] = 0 := by
    rw [shellOffset, shellIntercept, run_nil]
    norm_num
  rw [shellOffset_cons, shellOffset_cons, offset_nil]
  simp [shellScale]

theorem lengthTwoCrossing_collisionSource
    (b c k : ℕ) {gap : ℕ} (gap_positive : 0 < gap) :
    collisionSource (lengthTwoCrossingLeft b c k gap)
        (lengthTwoCrossingRight b c k) =
      lengthTwoCrossingSource c k gap := by
  have length_eq :
      (lengthTwoCrossingLeft b c k gap).length =
        (lengthTwoCrossingRight b c k).length := by
    rfl
  have sum_ne :
      (lengthTwoCrossingLeft b c k gap).sum ≠
        (lengthTwoCrossingRight b c k).sum := by
    simp only [lengthTwoCrossingLeft, lengthTwoCrossingRight, List.sum_cons,
      List.sum_nil, Nat.add_zero]
    omega
  rw [collisionSource_eq_clearedBalance length_eq sum_ne]
  simp only [lengthTwoCrossingLeft, lengthTwoCrossingRight, shellOffset_pair,
    shellGain, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, shellScale, lengthTwoCrossingSource]
  have gap_power_ne : 1 - (2 / 3 : ℚ) ^ gap ≠ 0 := by
    have gap_power_lt : (2 / 3 : ℚ) ^ gap < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) gap_positive.ne'
    linarith
  have base_ne : (2 / 3 : ℚ) ≠ 0 := by norm_num
  simp only [pow_add]
  have gain_gap_ne :
      (2 / 3 : ℚ) ^ b * (2 / 3 : ℚ) ^ k * (2 / 3 : ℚ) ^ c -
          (2 / 3 : ℚ) ^ b * (2 / 3 : ℚ) ^ k * (2 / 3 : ℚ) ^ c *
            (2 / 3 : ℚ) ^ gap ≠ 0 := by
    rw [show
      (2 / 3 : ℚ) ^ b * (2 / 3 : ℚ) ^ k * (2 / 3 : ℚ) ^ c -
          (2 / 3 : ℚ) ^ b * (2 / 3 : ℚ) ^ k * (2 / 3 : ℚ) ^ c *
            (2 / 3 : ℚ) ^ gap =
        ((2 / 3 : ℚ) ^ b * (2 / 3 : ℚ) ^ k * (2 / 3 : ℚ) ^ c) *
          (1 - (2 / 3 : ℚ) ^ gap) by ring]
    exact mul_ne_zero (by positivity) gap_power_ne
  field_simp [gap_power_ne, base_ne, gain_gap_ne]
  ring

theorem lengthTwoCrossing_commonTarget
    (b c k : ℕ) {gap : ℕ} (gap_positive : 0 < gap) :
    shellRun (lengthTwoCrossingLeft b c k gap)
        (lengthTwoCrossingSource c k gap) =
      lengthTwoCrossingTarget b k gap ∧
    shellRun (lengthTwoCrossingRight b c k)
        (lengthTwoCrossingSource c k gap) =
      lengthTwoCrossingTarget b k gap := by
  have source_eq := lengthTwoCrossing_collisionSource b c k gap_positive
  have sum_ne :
      (lengthTwoCrossingLeft b c k gap).sum ≠
        (lengthTwoCrossingRight b c k).sum := by
    simp only [lengthTwoCrossingLeft, lengthTwoCrossingRight, List.sum_cons,
      List.sum_nil, Nat.add_zero]
    omega
  have slope_ne :
      shellSlope (lengthTwoCrossingLeft b c k gap) ≠
        shellSlope (lengthTwoCrossingRight b c k) := by
    intro slope_eq
    exact sum_ne
      ((shellSlope_eq_iff_length_sum
        (lengthTwoCrossingLeft b c k gap)
        (lengthTwoCrossingRight b c k)).1 slope_eq).2
  have collision := shellRun_collisionSource
    (lengthTwoCrossingLeft b c k gap) (lengthTwoCrossingRight b c k) slope_ne
  rw [source_eq] at collision
  constructor
  · rw [lengthTwoCrossingLeft, shellRun_cons, shellRun_singleton]
    simp only [shellStep, lengthTwoCrossingSource, lengthTwoCrossingTarget]
    have gap_power_ne : 1 - (2 / 3 : ℚ) ^ gap ≠ 0 := by
      have gap_power_lt : (2 / 3 : ℚ) ^ gap < 1 :=
        pow_lt_one₀ (by norm_num) (by norm_num) gap_positive.ne'
      linarith
    have base_ne : (2 / 3 : ℚ) ≠ 0 := by norm_num
    field_simp [gap_power_ne, base_ne]
    rw [pow_add, pow_add, pow_add]
    ring
  · rw [← collision]
    rw [lengthTwoCrossingLeft, shellRun_cons, shellRun_singleton]
    simp only [shellStep, lengthTwoCrossingSource, lengthTwoCrossingTarget]
    have gap_power_ne : 1 - (2 / 3 : ℚ) ^ gap ≠ 0 := by
      have gap_power_lt : (2 / 3 : ℚ) ^ gap < 1 :=
        pow_lt_one₀ (by norm_num) (by norm_num) gap_positive.ne'
      linarith
    have base_ne : (2 / 3 : ℚ) ≠ 0 := by norm_num
    field_simp [gap_power_ne, base_ne]
    rw [pow_add, pow_add, pow_add]
    ring

theorem lengthTwoCrossingTarget_eq_cleared
    (b k : ℕ) {gap : ℕ} (gap_positive : 0 < gap) :
    lengthTwoCrossingTarget b k gap =
      lengthTwoCrossingTargetNumerator b k gap /
        (25 * (1 - (2 / 3 : ℚ) ^ gap)) := by
  have gap_power_ne : 1 - (2 / 3 : ℚ) ^ gap ≠ 0 := by
    have gap_power_lt : (2 / 3 : ℚ) ^ gap < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) gap_positive.ne'
    linarith
  rw [lengthTwoCrossingTarget, lengthTwoCrossingTargetNumerator]
  field_simp [gap_power_ne]

private theorem lengthTwo_unit_pow
    {value : ℚ} (value_unit : IsUnit 5 value) (exponent : ℕ) :
    IsUnit 5 (value ^ exponent) := by
  refine ⟨pow_ne_zero exponent value_unit.1, ?_⟩
  rw [padicValRat.pow, value_unit.2]
  simp

private theorem one_sub_shellRatio_pow_hasValue
    {exponent : ℕ} (exponent_positive : 0 < exponent) :
    HasValue 5 (1 - (2 / 3 : ℚ) ^ exponent)
      (shellSlopeGapFiveDepth exponent) := by
  have negative_value := neg_hasValue
    (shellRatio_pow_sub_one_hasValue exponent_positive)
  convert negative_value using 1
  ring

/-- The source valuation is the difference of the two parity/LTE carry depths. -/
theorem lengthTwoCrossingSource_hasValue
    (c : ℕ) {k gap : ℕ} (k_positive : 0 < k) (gap_positive : 0 < gap) :
    HasValue 5 (lengthTwoCrossingSource c k gap)
      ((shellSlopeGapFiveDepth k : ℤ) - shellSlopeGapFiveDepth gap) := by
  have numerator_value := one_sub_shellRatio_pow_hasValue k_positive
  have two_unit : IsUnit 5 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have three_unit : IsUnit 5 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have ratio_unit : IsUnit 5 ((2 : ℚ) / 3) := div_hasValue two_unit three_unit
  have power_unit : IsUnit 5 ((2 / 3 : ℚ) ^ (c + k)) :=
    lengthTwo_unit_pow ratio_unit (c + k)
  have gap_value := one_sub_shellRatio_pow_hasValue gap_positive
  have denominator_value :=
    mul_hasValue (mul_hasValue three_unit power_unit) gap_value
  rw [lengthTwoCrossingSource]
  convert div_hasValue numerator_value denominator_value using 1
  ring

/-- The canonical positive length-two source is a five-adic unit exactly when its two gap
carries agree. -/
theorem lengthTwoCrossingSource_fiveUnit_iff
    (c : ℕ) {k gap : ℕ} (k_positive : 0 < k) (gap_positive : 0 < gap) :
    IsUnit 5 (lengthTwoCrossingSource c k gap) ↔
      shellSlopeGapFiveDepth k = shellSlopeGapFiveDepth gap := by
  have source_value :=
    lengthTwoCrossingSource_hasValue c k_positive gap_positive
  constructor
  · intro source_unit
    have values_eq :
        (0 : ℤ) =
          (shellSlopeGapFiveDepth k : ℤ) - shellSlopeGapFiveDepth gap := by
      rw [← source_unit.2, source_value.2]
    exact_mod_cast (sub_eq_zero.mp values_eq.symm)
  · intro depths_eq
    simpa [depths_eq] using source_value

/-- Target acceptance is one exact valuation of the cleared length-two numerator. -/
theorem lengthTwoCrossingTarget_fiveUnit_iff
    (b k : ℕ) {gap : ℕ} (gap_positive : 0 < gap) :
    IsUnit 5 (lengthTwoCrossingTarget b k gap) ↔
      HasValue 5 (lengthTwoCrossingTargetNumerator b k gap)
        ((2 : ℤ) + shellSlopeGapFiveDepth gap) := by
  have twentyfive_value : HasValue 5 (25 : ℚ) 2 := by
    convert primePower_hasValue (prime := 5) 2 using 1
    · norm_num
    · norm_num
  have gap_value := one_sub_shellRatio_pow_hasValue gap_positive
  have denominator_value := mul_hasValue twentyfive_value gap_value
  have target_eq := lengthTwoCrossingTarget_eq_cleared b k gap_positive
  rw [target_eq]
  constructor
  · intro target_unit
    have numerator_value := mul_hasValue target_unit denominator_value
    have numerator_eq :
        lengthTwoCrossingTargetNumerator b k gap /
              (25 * (1 - (2 / 3 : ℚ) ^ gap)) *
            (25 * (1 - (2 / 3 : ℚ) ^ gap)) =
          lengthTwoCrossingTargetNumerator b k gap :=
      div_mul_cancel₀ _ denominator_value.1
    rw [numerator_eq] at numerator_value
    convert numerator_value using 1
    ring
  · intro numerator_value
    have target_value := div_hasValue numerator_value denominator_value
    convert target_value using 1
    ring

/-- Target acceptance forces the two target summands to meet at one carry above the gap. -/
theorem lengthTwoCrossingTarget_fiveUnit_forces_carry
    (b k : ℕ) {gap : ℕ} (gap_positive : 0 < gap)
    (target_unit : IsUnit 5 (lengthTwoCrossingTarget b k gap)) :
    shellSlopeGapFiveDepth (gap + k) =
      shellSlopeGapFiveDepth gap + 1 := by
  have five_value : HasValue 5 (5 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 5) 1)
  have gap_value := one_sub_shellRatio_pow_hasValue gap_positive
  have left_value :
      HasValue 5 (5 * (1 - (2 / 3 : ℚ) ^ gap))
        ((1 : ℤ) + shellSlopeGapFiveDepth gap) :=
    mul_hasValue five_value gap_value
  have two_unit : IsUnit 5 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have three_unit : IsUnit 5 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have ratio_unit : IsUnit 5 ((2 : ℚ) / 3) := div_hasValue two_unit three_unit
  have power_unit : IsUnit 5 ((2 / 3 : ℚ) ^ b) :=
    lengthTwo_unit_pow ratio_unit b
  have combined_positive : 0 < gap + k := by omega
  have combined_value := one_sub_shellRatio_pow_hasValue combined_positive
  have right_value :
      HasValue 5
        (3 * (2 / 3 : ℚ) ^ b * (1 - (2 / 3 : ℚ) ^ (gap + k)))
        (shellSlopeGapFiveDepth (gap + k)) := by
    simpa using mul_hasValue (mul_hasValue three_unit power_unit) combined_value
  have numerator_value :=
    (lengthTwoCrossingTarget_fiveUnit_iff b k gap_positive).1 target_unit
  have numerator_eq :
      lengthTwoCrossingTargetNumerator b k gap =
        5 * (1 - (2 / 3 : ℚ) ^ gap) +
          3 * (2 / 3 : ℚ) ^ b * (1 - (2 / 3 : ℚ) ^ (gap + k)) := by
    rfl
  rw [numerator_eq] at numerator_value
  rcases lt_trichotomy
      ((1 : ℤ) + shellSlopeGapFiveDepth gap)
      (shellSlopeGapFiveDepth (gap + k)) with lower | equal | higher
  · have surviving := add_hasValue_left left_value right_value lower
    have impossible :
        (1 : ℤ) + shellSlopeGapFiveDepth gap =
          2 + shellSlopeGapFiveDepth gap := by
      rw [← surviving.2, numerator_value.2]
    omega
  · omega
  · have surviving := add_hasValue_right left_value right_value higher
    have impossible :
        (shellSlopeGapFiveDepth (gap + k) : ℤ) =
          2 + (shellSlopeGapFiveDepth gap : ℤ) := by
      rw [← surviving.2, numerator_value.2]
    omega

/-- Under the forced carry tie, a positive tail-gauge shift changes the common target by the
shift's parity/LTE depth minus one. -/
theorem lengthTwoCrossingTarget_add_sub_hasValue
    (b k : ℕ) {gap shift : ℕ} (gap_positive : 0 < gap) (shift_positive : 0 < shift)
    (carry : shellSlopeGapFiveDepth (gap + k) =
      shellSlopeGapFiveDepth gap + 1) :
    HasValue 5
      (lengthTwoCrossingTarget (b + shift) k gap -
        lengthTwoCrossingTarget b k gap)
      ((shellSlopeGapFiveDepth shift : ℤ) - 1) := by
  have combined_positive : 0 < gap + k := by omega
  have gap_value := one_sub_shellRatio_pow_hasValue gap_positive
  have combined_value := one_sub_shellRatio_pow_hasValue combined_positive
  have quotient_value :
      HasValue 5
        ((1 - (2 / 3 : ℚ) ^ (gap + k)) /
          (1 - (2 / 3 : ℚ) ^ gap)) 1 := by
    have value := div_hasValue combined_value gap_value
    convert value using 1
    rw [carry]
    norm_num
  have two_unit : IsUnit 5 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have three_unit : IsUnit 5 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have ratio_unit : IsUnit 5 ((2 : ℚ) / 3) := div_hasValue two_unit three_unit
  have power_unit : IsUnit 5 ((2 / 3 : ℚ) ^ b) :=
    lengthTwo_unit_pow ratio_unit b
  have shift_value := shellRatio_pow_sub_one_hasValue shift_positive
  have twentyfive_value : HasValue 5 (25 : ℚ) 2 := by
    convert primePower_hasValue (prime := 5) 2 using 1 <;> norm_num
  have difference_eq :
      lengthTwoCrossingTarget (b + shift) k gap -
          lengthTwoCrossingTarget b k gap =
        (3 * (2 / 3 : ℚ) ^ b * ((2 / 3 : ℚ) ^ shift - 1) *
          ((1 - (2 / 3 : ℚ) ^ (gap + k)) /
            (1 - (2 / 3 : ℚ) ^ gap))) / 25 := by
    rw [lengthTwoCrossingTarget, lengthTwoCrossingTarget, pow_add]
    field_simp [gap_value.1]
    ring
  rw [difference_eq]
  have numerator_value := mul_hasValue
    (mul_hasValue (mul_hasValue three_unit power_unit) shift_value) quotient_value
  have difference_value := div_hasValue numerator_value twentyfive_value
  convert difference_value using 1
  ring

/-- A ten-step tail-gauge shift changes the common target by exact five-adic value one. -/
theorem lengthTwoCrossingTarget_add_ten_sub_hasValue
    (b k : ℕ) {gap : ℕ} (gap_positive : 0 < gap)
    (carry : shellSlopeGapFiveDepth (gap + k) =
      shellSlopeGapFiveDepth gap + 1) :
    HasValue 5
      (lengthTwoCrossingTarget (b + 10) k gap -
        lengthTwoCrossingTarget b k gap) 1 := by
  have value := lengthTwoCrossingTarget_add_sub_hasValue
    b k gap_positive (show 0 < 10 by norm_num) carry
  have ten_depth : shellSlopeGapFiveDepth 10 = 2 := by
    rw [shellSlopeGapFiveDepth, if_neg (by norm_num : ¬Odd 10)]
    norm_num [padicValNat_self]
  rw [ten_depth] at value
  norm_num at value ⊢
  exact value

/-- Once the necessary carry tie holds, target acceptance is exactly ten-periodic in the tail
gauge. -/
theorem lengthTwoCrossingTarget_fiveUnit_add_ten_iff
    (b k : ℕ) {gap : ℕ} (gap_positive : 0 < gap)
    (carry : shellSlopeGapFiveDepth (gap + k) =
      shellSlopeGapFiveDepth gap + 1) :
    IsUnit 5 (lengthTwoCrossingTarget (b + 10) k gap) ↔
      IsUnit 5 (lengthTwoCrossingTarget b k gap) := by
  have difference_value :=
    lengthTwoCrossingTarget_add_ten_sub_hasValue b k gap_positive carry
  have difference_positive :
      IsPositive 5
        (lengthTwoCrossingTarget (b + 10) k gap -
          lengthTwoCrossingTarget b k gap) :=
    ⟨difference_value.1, by rw [difference_value.2]; norm_num⟩
  have reverse_value :
      HasValue 5
        (lengthTwoCrossingTarget b k gap -
          lengthTwoCrossingTarget (b + 10) k gap) 1 := by
    have negated := neg_hasValue difference_value
    convert negated using 1
    ring
  have reverse_positive :
      IsPositive 5
        (lengthTwoCrossingTarget b k gap -
          lengthTwoCrossingTarget (b + 10) k gap) :=
    ⟨reverse_value.1, by rw [reverse_value.2]; norm_num⟩
  constructor
  · intro later_unit
    have earlier_unit := unit_add_positive later_unit reverse_positive
    convert earlier_unit using 1
    ring
  · intro earlier_unit
    have later_unit := unit_add_positive earlier_unit difference_positive
    convert later_unit using 1
    ring

/-- If one tail gauge is accepted, every positive odd shift has target value minus one and is
therefore rejected. -/
theorem lengthTwoCrossingTarget_oddShift_hasValue_negOne
    (b k : ℕ) {gap shift : ℕ} (gap_positive : 0 < gap) (shift_positive : 0 < shift)
    (shift_odd : Odd shift)
    (carry : shellSlopeGapFiveDepth (gap + k) =
      shellSlopeGapFiveDepth gap + 1)
    (target_unit : IsUnit 5 (lengthTwoCrossingTarget b k gap)) :
    HasValue 5 (lengthTwoCrossingTarget (b + shift) k gap) (-1) := by
  have difference_value := lengthTwoCrossingTarget_add_sub_hasValue
    b k gap_positive shift_positive carry
  have shift_depth : shellSlopeGapFiveDepth shift = 0 := by
    rw [shellSlopeGapFiveDepth, if_pos shift_odd]
  rw [shift_depth] at difference_value
  norm_num at difference_value
  have sum_value := add_hasValue_left difference_value target_unit (by norm_num)
  convert sum_value using 1
  ring

/-- A gap shift three carry levels deeper than a source-tied gap changes the common target at
exact five-adic value one. -/
theorem lengthTwoCrossingTarget_gap_add_sub_hasValue
    (b : ℕ) {k gap shift : ℕ}
    (k_positive : 0 < k) (gap_positive : 0 < gap) (shift_positive : 0 < shift)
    (source_depth : shellSlopeGapFiveDepth k = shellSlopeGapFiveDepth gap)
    (shifted_depth : shellSlopeGapFiveDepth (gap + shift) = shellSlopeGapFiveDepth gap)
    (period_depth : shellSlopeGapFiveDepth shift = shellSlopeGapFiveDepth gap + 3) :
    HasValue 5
      (lengthTwoCrossingTarget b k (gap + shift) -
        lengthTwoCrossingTarget b k gap) 1 := by
  have shifted_positive : 0 < gap + shift := by omega
  have gap_value := one_sub_shellRatio_pow_hasValue gap_positive
  have shifted_value := one_sub_shellRatio_pow_hasValue shifted_positive
  have shift_value := one_sub_shellRatio_pow_hasValue shift_positive
  have k_value := shellRatio_pow_sub_one_hasValue k_positive
  have two_unit : IsUnit 5 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have three_unit : IsUnit 5 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have ratio_unit : IsUnit 5 ((2 : ℚ) / 3) := div_hasValue two_unit three_unit
  have gap_power_unit : IsUnit 5 ((2 / 3 : ℚ) ^ gap) :=
    lengthTwo_unit_pow ratio_unit gap
  have b_power_unit : IsUnit 5 ((2 / 3 : ℚ) ^ b) :=
    lengthTwo_unit_pow ratio_unit b
  have twentyfive_value : HasValue 5 (25 : ℚ) 2 := by
    convert primePower_hasValue (prime := 5) 2 using 1 <;> norm_num
  have quotient_value := div_hasValue
    (mul_hasValue (mul_hasValue gap_power_unit k_value) shift_value)
    (mul_hasValue shifted_value gap_value)
  have difference_eq :
      lengthTwoCrossingTarget b k (gap + shift) -
          lengthTwoCrossingTarget b k gap =
        (3 * (2 / 3 : ℚ) ^ b *
          (((2 / 3 : ℚ) ^ gap * ((2 / 3 : ℚ) ^ k - 1) *
              (1 - (2 / 3 : ℚ) ^ shift)) /
            ((1 - (2 / 3 : ℚ) ^ (gap + shift)) *
              (1 - (2 / 3 : ℚ) ^ gap)))) / 25 := by
    rw [lengthTwoCrossingTarget, lengthTwoCrossingTarget]
    field_simp [gap_value.1, shifted_value.1]
    rw [pow_add, pow_add, pow_add]
    ring
  rw [difference_eq]
  have numerator_value :=
    mul_hasValue (mul_hasValue three_unit b_power_unit) quotient_value
  have result := div_hasValue numerator_value twentyfive_value
  convert result using 1
  rw [source_depth, shifted_depth, period_depth]
  push_cast
  ring

/-- Under the same carry-depth hypotheses, the gap shift preserves target acceptance. -/
theorem lengthTwoCrossingTarget_gap_add_fiveUnit_iff
    (b : ℕ) {k gap shift : ℕ}
    (k_positive : 0 < k) (gap_positive : 0 < gap) (shift_positive : 0 < shift)
    (source_depth : shellSlopeGapFiveDepth k = shellSlopeGapFiveDepth gap)
    (shifted_depth : shellSlopeGapFiveDepth (gap + shift) = shellSlopeGapFiveDepth gap)
    (period_depth : shellSlopeGapFiveDepth shift = shellSlopeGapFiveDepth gap + 3) :
    IsUnit 5 (lengthTwoCrossingTarget b k (gap + shift)) ↔
      IsUnit 5 (lengthTwoCrossingTarget b k gap) := by
  have difference_value := lengthTwoCrossingTarget_gap_add_sub_hasValue b
    k_positive gap_positive shift_positive source_depth shifted_depth period_depth
  have difference_positive :
      IsPositive 5
        (lengthTwoCrossingTarget b k (gap + shift) -
          lengthTwoCrossingTarget b k gap) :=
    ⟨difference_value.1, by rw [difference_value.2]; norm_num⟩
  have reverse_value :
      HasValue 5
        (lengthTwoCrossingTarget b k gap -
          lengthTwoCrossingTarget b k (gap + shift)) 1 := by
    have negated := neg_hasValue difference_value
    convert negated using 1
    ring
  have reverse_positive :
      IsPositive 5
        (lengthTwoCrossingTarget b k gap -
          lengthTwoCrossingTarget b k (gap + shift)) :=
    ⟨reverse_value.1, by rw [reverse_value.2]; norm_num⟩
  constructor
  · intro shifted_unit
    have original_unit := unit_add_positive shifted_unit reverse_positive
    convert original_unit using 1
    ring
  · intro original_unit
    have shifted_unit := unit_add_positive original_unit difference_positive
    convert shifted_unit using 1
    ring

/-- Ten residue tests classify target acceptance on every tied length-two crossing fibre. -/
theorem lengthTwoCrossingTarget_fiveUnit_iff_mod_ten
    (b k : ℕ) {gap : ℕ} (gap_positive : 0 < gap)
    (carry : shellSlopeGapFiveDepth (gap + k) =
      shellSlopeGapFiveDepth gap + 1) :
    IsUnit 5 (lengthTwoCrossingTarget b k gap) ↔
      IsUnit 5 (lengthTwoCrossingTarget (b % 10) k gap) := by
  have periodic (base repetitions : ℕ) :
      IsUnit 5 (lengthTwoCrossingTarget (base + 10 * repetitions) k gap) ↔
        IsUnit 5 (lengthTwoCrossingTarget base k gap) := by
    induction repetitions with
    | zero => simp
    | succ repetitions induction =>
        rw [Nat.mul_succ, ← Nat.add_assoc,
          lengthTwoCrossingTarget_fiveUnit_add_ten_iff
            (base + 10 * repetitions) k gap_positive carry]
        exact induction
  have decomposition : b % 10 + 10 * (b / 10) = b := by omega
  have reduced := periodic (b % 10) (b / 10)
  rw [decomposition] at reduced
  exact reduced

/-- Source-trap membership, both five-adic guards, and the two exact carry equations reduce
length-two acceptance to ten target residues. -/
theorem lengthTwoCrossing_acceptance_iff_mod_ten
    (b c : ℕ) {k gap : ℕ} (k_positive : 0 < k) (gap_positive : 0 < gap) :
    lengthTwoCrossingSource c k gap ∈ Set.Icc (1 / 5) (1 / 2) ∧
        IsUnit 5 (lengthTwoCrossingSource c k gap) ∧
        IsUnit 5 (lengthTwoCrossingTarget b k gap) ↔
      lengthTwoCrossingSource c k gap ∈ Set.Icc (1 / 5) (1 / 2) ∧
        shellSlopeGapFiveDepth k = shellSlopeGapFiveDepth gap ∧
        shellSlopeGapFiveDepth (gap + k) = shellSlopeGapFiveDepth gap + 1 ∧
        IsUnit 5 (lengthTwoCrossingTarget (b % 10) k gap) := by
  constructor
  · rintro ⟨source_mem, source_unit, target_unit⟩
    have source_carry :=
      (lengthTwoCrossingSource_fiveUnit_iff c k_positive gap_positive).1 source_unit
    have target_carry :=
      lengthTwoCrossingTarget_fiveUnit_forces_carry b k gap_positive target_unit
    have target_residue :=
      (lengthTwoCrossingTarget_fiveUnit_iff_mod_ten b k gap_positive target_carry).1
        target_unit
    exact ⟨source_mem, source_carry, target_carry, target_residue⟩
  · rintro ⟨source_mem, source_carry, target_carry, target_residue⟩
    have source_unit :=
      (lengthTwoCrossingSource_fiveUnit_iff c k_positive gap_positive).2 source_carry
    have target_unit :=
      (lengthTwoCrossingTarget_fiveUnit_iff_mod_ten b k gap_positive target_carry).2
        target_residue
    exact ⟨source_mem, source_unit, target_unit⟩

theorem lengthTwoCrossingSource_positive
    (c : ℕ) {k gap : ℕ} (k_positive : 0 < k) (gap_positive : 0 < gap) :
    0 < lengthTwoCrossingSource c k gap := by
  have k_power_lt : (2 / 3 : ℚ) ^ k < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) k_positive.ne'
  have gap_power_lt : (2 / 3 : ℚ) ^ gap < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) gap_positive.ne'
  rw [lengthTwoCrossingSource]
  positivity

theorem lengthTwoCrossingSource_add
    (c k : ℕ) {gap : ℕ} (gap_positive : 0 < gap) (shift : ℕ) :
    lengthTwoCrossingSource (c + shift) k gap =
      (3 / 2 : ℚ) ^ shift * lengthTwoCrossingSource c k gap := by
  have gap_power_ne : 1 - (2 / 3 : ℚ) ^ gap ≠ 0 := by
    have gap_power_lt : (2 / 3 : ℚ) ^ gap < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) gap_positive.ne'
    linarith
  have base_ne : (2 / 3 : ℚ) ≠ 0 := by norm_num
  have inverse_power :
      (2 / 3 : ℚ) ^ shift * (3 / 2 : ℚ) ^ shift = 1 := by
    rw [← mul_pow]
    norm_num
  rw [lengthTwoCrossingSource, lengthTwoCrossingSource,
    show c + shift + k = c + k + shift by omega, pow_add]
  field_simp [gap_power_ne, base_ne]
  rw [div_pow]
  field_simp
  calc
    (3 : ℚ) ^ k - 2 ^ k = ((3 : ℚ) ^ k - 2 ^ k) * 1 := by ring
    _ = ((3 : ℚ) ^ k - 2 ^ k) *
        ((2 / 3 : ℚ) ^ shift * (3 / 2 : ℚ) ^ shift) := by rw [inverse_power]
    _ = ((3 : ℚ) ^ k - 2 ^ k) * (2 / 3 : ℚ) ^ shift *
        (3 / 2 : ℚ) ^ shift := by ring

theorem lengthTwoCrossingSource_strictMono
    {k gap : ℕ} (k_positive : 0 < k) (gap_positive : 0 < gap) :
    StrictMono (fun c => lengthTwoCrossingSource c k gap) := by
  intro c d c_lt_d
  have shift_positive : 0 < d - c := by omega
  have decomposition : c + (d - c) = d := by omega
  have scale_gt_one : (1 : ℚ) < (3 / 2) ^ (d - c) :=
    one_lt_pow₀ (by norm_num) shift_positive.ne'
  have source_positive :=
    lengthTwoCrossingSource_positive c k_positive gap_positive
  change lengthTwoCrossingSource c k gap <
    lengthTwoCrossingSource d k gap
  rw [← decomposition, lengthTwoCrossingSource_add c k gap_positive]
  nlinarith

/-- Advancing the gauge by three moves every real-trap source beyond its upper wall. -/
theorem lengthTwoCrossingSource_add_three_gt_half
    (c k : ℕ) {gap : ℕ} (gap_positive : 0 < gap)
    (source_lower : 1 / 5 ≤ lengthTwoCrossingSource c k gap) :
    1 / 2 < lengthTwoCrossingSource (c + 3) k gap := by
  rw [lengthTwoCrossingSource_add c k gap_positive]
  norm_num
  nlinarith

/-- For fixed positive crossing gaps, all real-trap gauges have diameter at most two. -/
theorem lengthTwoCrossing_realTrap_gauge_lt_three
    {c d k gap : ℕ} (k_positive : 0 < k) (gap_positive : 0 < gap)
    (c_mem : lengthTwoCrossingSource c k gap ∈ Set.Icc (1 / 5) (1 / 2))
    (d_mem : lengthTwoCrossingSource d k gap ∈ Set.Icc (1 / 5) (1 / 2)) :
    d < c + 3 := by
  by_contra d_not_lt
  have c_three_le_d : c + 3 ≤ d := by omega
  have c_three_high :=
    lengthTwoCrossingSource_add_three_gt_half c k gap_positive c_mem.1
  have ordered :=
    (lengthTwoCrossingSource_strictMono k_positive gap_positive).monotone c_three_le_d
  exact (not_lt_of_ge d_mem.2) (lt_of_lt_of_le c_three_high ordered)

/-- Any two admissible gauges on one normal-form fibre differ by at most two. -/
theorem lengthTwoCrossing_realTrap_gauge_distance_lt_three
    {c d k gap : ℕ} (k_positive : 0 < k) (gap_positive : 0 < gap)
    (c_mem : lengthTwoCrossingSource c k gap ∈ Set.Icc (1 / 5) (1 / 2))
    (d_mem : lengthTwoCrossingSource d k gap ∈ Set.Icc (1 / 5) (1 / 2)) :
    d < c + 3 ∧ c < d + 3 :=
  ⟨lengthTwoCrossing_realTrap_gauge_lt_three k_positive gap_positive c_mem d_mem,
    lengthTwoCrossing_realTrap_gauge_lt_three k_positive gap_positive d_mem c_mem⟩

/-- A length-two normal-form source can meet the real trap only for transfer gap one or two. -/
theorem lengthTwoCrossing_realTrap_forces_k_le_two
    (c : ℕ) {k gap : ℕ} (k_positive : 0 < k) (gap_positive : 0 < gap)
    (source_mem : lengthTwoCrossingSource c k gap ∈ Set.Icc (1 / 5) (1 / 2)) :
    k ≤ 2 := by
  have base_le :=
    (lengthTwoCrossingSource_strictMono k_positive gap_positive).monotone (Nat.zero_le c)
  have base_upper : lengthTwoCrossingSource 0 k gap ≤ 1 / 2 :=
    le_trans base_le source_mem.2
  by_contra k_large
  have three_le : 3 ≤ k := by omega
  have k_power_upper : (2 / 3 : ℚ) ^ k ≤ 8 / 27 := by
    have power_order := pow_le_pow_of_le_one
      (show 0 ≤ (2 / 3 : ℚ) by norm_num) (show (2 / 3 : ℚ) ≤ 1 by norm_num) three_le
    norm_num at power_order ⊢
    exact power_order
  have gap_power_positive : 0 < (2 / 3 : ℚ) ^ gap := by positivity
  have gap_factor_lt_one : 1 - (2 / 3 : ℚ) ^ gap < 1 := by linarith
  have denominator_positive :
      0 < 3 * (2 / 3 : ℚ) ^ k * (1 - (2 / 3 : ℚ) ^ gap) := by
    have gap_power_lt : (2 / 3 : ℚ) ^ gap < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) gap_positive.ne'
    positivity
  have denominator_upper :
      3 * (2 / 3 : ℚ) ^ k * (1 - (2 / 3 : ℚ) ^ gap) < 8 / 9 := by
    calc
      3 * (2 / 3 : ℚ) ^ k * (1 - (2 / 3 : ℚ) ^ gap) <
          3 * (2 / 3 : ℚ) ^ k * 1 :=
        mul_lt_mul_of_pos_left gap_factor_lt_one (by positivity)
      _ ≤ 3 * (8 / 27) * 1 := by gcongr
      _ = 8 / 9 := by norm_num
  have numerator_lower : 19 / 27 ≤ 1 - (2 / 3 : ℚ) ^ k := by
    linarith
  have base_gt_half : 1 / 2 < lengthTwoCrossingSource 0 k gap := by
    rw [lengthTwoCrossingSource]
    simp only [Nat.zero_add]
    apply (lt_div_iff₀ denominator_positive).2
    nlinarith
  exact (not_lt_of_ge base_upper) base_gt_half

private theorem shellSlopeGapFiveDepth_one : shellSlopeGapFiveDepth 1 = 0 := by
  simp [shellSlopeGapFiveDepth]

private theorem shellSlopeGapFiveDepth_two : shellSlopeGapFiveDepth 2 = 1 := by
  norm_num [shellSlopeGapFiveDepth, padicValNat.eq_zero_of_not_dvd]

private theorem shellSlopeGapFiveDepth_eq_zero_iff_odd (gap : ℕ) :
    shellSlopeGapFiveDepth gap = 0 ↔ Odd gap := by
  constructor
  · intro depth_zero
    by_contra gap_not_odd
    rw [shellSlopeGapFiveDepth, if_neg gap_not_odd] at depth_zero
    omega
  · intro gap_odd
    simp [shellSlopeGapFiveDepth, gap_odd]

private theorem shellSlopeGapFiveDepth_eq_one_iff
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

private theorem padicValNat_five_eq_one_iff
    {value : ℕ} (value_positive : 0 < value) :
    padicValNat 5 value = 1 ↔ 5 ∣ value ∧ ¬25 ∣ value := by
  have value_ne : value ≠ 0 := Nat.ne_of_gt value_positive
  constructor
  · intro value_one
    have five_power_dvd : 5 ^ 1 ∣ value :=
      (padicValNat_dvd_iff_le value_ne).2 (by omega)
    have five_dvd : 5 ∣ value := by simpa using five_power_dvd
    have twentyfive_not_dvd : ¬25 ∣ value := by
      intro twentyfive_dvd
      have square_dvd : 5 ^ 2 ∣ value := by
        norm_num at twentyfive_dvd ⊢
        exact twentyfive_dvd
      have two_le := (padicValNat_dvd_iff_le value_ne).1 square_dvd
      omega
    exact ⟨five_dvd, twentyfive_not_dvd⟩
  · rintro ⟨five_dvd, twentyfive_not_dvd⟩
    have five_power_dvd : 5 ^ 1 ∣ value := by simpa using five_dvd
    have one_le := (padicValNat_dvd_iff_le value_ne).1 five_power_dvd
    have not_two_le : ¬2 ≤ padicValNat 5 value := by
      intro two_le
      have square_dvd := (padicValNat_dvd_iff_le value_ne).2 two_le
      apply twentyfive_not_dvd
      norm_num at square_dvd ⊢
      exact square_dvd
    omega

private theorem oddGap_nextDepth_eq_one_iff_modTen_ne_nine
    {gap : ℕ} (gap_odd : Odd gap) :
    shellSlopeGapFiveDepth (gap + 1) = 1 ↔ gap % 10 ≠ 9 := by
  obtain ⟨half, gap_eq⟩ := gap_odd
  have next_positive : 0 < gap + 1 := by omega
  have next_even : Even (gap + 1) := ⟨half + 1, by omega⟩
  have half_eq : (gap + 1) / 2 = half + 1 := by omega
  have dvd_iff_mod : 5 ∣ (gap + 1) / 2 ↔ gap % 10 = 9 := by
    rw [half_eq, Nat.dvd_iff_mod_eq_zero]
    omega
  rw [shellSlopeGapFiveDepth_eq_one_iff next_positive, and_iff_right next_even]
  exact not_congr dvd_iff_mod

private theorem evenGap_depthPair_iff_residues
    {gap : ℕ} (gap_positive : 0 < gap) :
    (shellSlopeGapFiveDepth gap = 1 ∧ shellSlopeGapFiveDepth (gap + 2) = 2) ↔
      gap % 10 = 8 ∧ gap % 50 ≠ 48 := by
  constructor
  · rintro ⟨gap_depth, next_depth⟩
    obtain ⟨gap_even, half_not_dvd⟩ :=
      (shellSlopeGapFiveDepth_eq_one_iff gap_positive).1 gap_depth
    obtain ⟨half, gap_eq⟩ := gap_even
    have half_eq : gap / 2 = half := by omega
    have next_half_eq : (gap + 2) / 2 = half + 1 := by omega
    have next_not_odd : ¬Odd (gap + 2) :=
      Nat.not_odd_iff_even.mpr ⟨half + 1, by omega⟩
    have next_half_value : padicValNat 5 (half + 1) = 1 := by
      rw [shellSlopeGapFiveDepth, if_neg next_not_odd, next_half_eq] at next_depth
      omega
    have half_successor_positive : 0 < half + 1 := by omega
    obtain ⟨five_dvd, twentyfive_not_dvd⟩ :=
      (padicValNat_five_eq_one_iff half_successor_positive).1 next_half_value
    rw [Nat.dvd_iff_mod_eq_zero] at five_dvd twentyfive_not_dvd
    constructor <;> omega
  · rintro ⟨mod_ten, mod_fifty⟩
    let half := gap / 2
    have gap_even : Even gap := by
      refine ⟨half, ?_⟩
      dsimp only [half]
      omega
    have gap_eq : gap = half + half := by
      obtain ⟨witness, gap_eq⟩ := gap_even
      have witness_eq : witness = half := by
        dsimp only [half]
        omega
      omega
    have half_not_dvd : ¬5 ∣ half := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    have gap_depth : shellSlopeGapFiveDepth gap = 1 :=
      (shellSlopeGapFiveDepth_eq_one_iff gap_positive).2 ⟨gap_even, by
        simpa [half] using half_not_dvd⟩
    have five_dvd_successor : 5 ∣ half + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    have twentyfive_not_dvd_successor : ¬25 ∣ half + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    have successor_value : padicValNat 5 (half + 1) = 1 :=
      (padicValNat_five_eq_one_iff (by omega)).2
        ⟨five_dvd_successor, twentyfive_not_dvd_successor⟩
    have next_not_odd : ¬Odd (gap + 2) :=
      Nat.not_odd_iff_even.mpr ⟨half + 1, by omega⟩
    have next_half_eq : (gap + 2) / 2 = half + 1 := by omega
    have next_depth : shellSlopeGapFiveDepth (gap + 2) = 2 := by
      rw [shellSlopeGapFiveDepth, if_neg next_not_odd, next_half_eq,
        successor_value]
    exact ⟨gap_depth, next_depth⟩

/-- With the real-trap bound `k ≤ 2`, the two acceptance carries are exactly two residue
families. -/
theorem lengthTwoGapDepths_iff_residues
    {k gap : ℕ} (k_positive : 0 < k) (gap_positive : 0 < gap) (k_le_two : k ≤ 2) :
    (shellSlopeGapFiveDepth k = shellSlopeGapFiveDepth gap ∧
      shellSlopeGapFiveDepth (gap + k) = shellSlopeGapFiveDepth gap + 1) ↔
      (k = 1 ∧ Odd gap ∧ gap % 10 ≠ 9) ∨
        (k = 2 ∧ gap % 10 = 8 ∧ gap % 50 ≠ 48) := by
  have k_cases : k = 1 ∨ k = 2 := by omega
  rcases k_cases with rfl | rfl
  · rw [shellSlopeGapFiveDepth_one]
    constructor
    · rintro ⟨gap_depth, next_depth⟩
      have gap_odd := (shellSlopeGapFiveDepth_eq_zero_iff_odd gap).1 gap_depth.symm
      have residue :=
        (oddGap_nextDepth_eq_one_iff_modTen_ne_nine gap_odd).1 (by omega)
      exact Or.inl ⟨rfl, gap_odd, residue⟩
    · rintro (⟨_, gap_odd, residue⟩ | ⟨impossible, _⟩)
      · have gap_depth := (shellSlopeGapFiveDepth_eq_zero_iff_odd gap).2 gap_odd
        have next_depth :=
          (oddGap_nextDepth_eq_one_iff_modTen_ne_nine gap_odd).2 residue
        exact ⟨gap_depth.symm, by omega⟩
      · omega
  · rw [shellSlopeGapFiveDepth_two]
    constructor
    · rintro ⟨gap_depth, next_depth⟩
      have pair :
          shellSlopeGapFiveDepth gap = 1 ∧
            shellSlopeGapFiveDepth (gap + 2) = 2 := by
        constructor <;> omega
      have residues := (evenGap_depthPair_iff_residues gap_positive).1 pair
      exact Or.inr ⟨rfl, residues⟩
    · rintro (⟨impossible, _⟩ | ⟨_, mod_ten, mod_fifty⟩)
      · omega
      · have pair := (evenGap_depthPair_iff_residues gap_positive).2
          ⟨mod_ten, mod_fifty⟩
        constructor <;> omega

/-- In the `k = 1` residue family, target acceptance is fifty-periodic in every positive odd
gap. -/
theorem lengthTwoCrossingTarget_one_gap_add_fifty_fiveUnit_iff
    (b : ℕ) {gap : ℕ} (gap_positive : 0 < gap) (gap_odd : Odd gap) :
    IsUnit 5 (lengthTwoCrossingTarget b 1 (gap + 50)) ↔
      IsUnit 5 (lengthTwoCrossingTarget b 1 gap) := by
  have gap_depth : shellSlopeGapFiveDepth gap = 0 :=
    (shellSlopeGapFiveDepth_eq_zero_iff_odd gap).2 gap_odd
  obtain ⟨half, gap_eq⟩ := gap_odd
  have shifted_odd : Odd (gap + 50) := ⟨half + 25, by omega⟩
  have shifted_depth : shellSlopeGapFiveDepth (gap + 50) = 0 :=
    (shellSlopeGapFiveDepth_eq_zero_iff_odd (gap + 50)).2 shifted_odd
  have fifty_depth : shellSlopeGapFiveDepth 50 = 3 := by
    rw [shellSlopeGapFiveDepth, if_neg (by norm_num : ¬Odd 50)]
    norm_num
    rw [show (25 : ℕ) = 5 ^ 2 by norm_num, padicValNat.prime_pow]
  apply lengthTwoCrossingTarget_gap_add_fiveUnit_iff b
    (k := 1) (gap := gap) (shift := 50) (by norm_num) gap_positive (by norm_num)
  · rw [shellSlopeGapFiveDepth_one, gap_depth]
  · exact shifted_depth.trans gap_depth.symm
  · rw [gap_depth, fifty_depth]

/-- In the `k = 2` residue family, target acceptance is 250-periodic in every gap congruent to
eight modulo ten. -/
theorem lengthTwoCrossingTarget_two_gap_add_twoFifty_fiveUnit_iff
    (b : ℕ) {gap : ℕ} (gap_positive : 0 < gap) (gap_mod : gap % 10 = 8) :
    IsUnit 5 (lengthTwoCrossingTarget b 2 (gap + 250)) ↔
      IsUnit 5 (lengthTwoCrossingTarget b 2 gap) := by
  have gap_even : Even gap := by
    refine ⟨gap / 2, ?_⟩
    omega
  have gap_half_not_dvd : ¬5 ∣ gap / 2 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have gap_depth : shellSlopeGapFiveDepth gap = 1 :=
    (shellSlopeGapFiveDepth_eq_one_iff gap_positive).2 ⟨gap_even, gap_half_not_dvd⟩
  have shifted_positive : 0 < gap + 250 := by omega
  have shifted_mod : (gap + 250) % 10 = 8 := by omega
  have shifted_even : Even (gap + 250) := by
    refine ⟨(gap + 250) / 2, ?_⟩
    omega
  have shifted_half_not_dvd : ¬5 ∣ (gap + 250) / 2 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have shifted_depth : shellSlopeGapFiveDepth (gap + 250) = 1 :=
    (shellSlopeGapFiveDepth_eq_one_iff shifted_positive).2
      ⟨shifted_even, shifted_half_not_dvd⟩
  have twoFifty_depth : shellSlopeGapFiveDepth 250 = 4 := by
    rw [shellSlopeGapFiveDepth, if_neg (by norm_num : ¬Odd 250)]
    norm_num
    rw [show (125 : ℕ) = 5 ^ 3 by norm_num, padicValNat.prime_pow]
  apply lengthTwoCrossingTarget_gap_add_fiveUnit_iff b
    (k := 2) (gap := gap) (shift := 250) (by norm_num) gap_positive (by norm_num)
  · rw [shellSlopeGapFiveDepth_two, gap_depth]
  · exact shifted_depth.trans gap_depth.symm
  · rw [gap_depth, twoFifty_depth]

/-- Odd `k = 1` gaps reduce completely to their positive residue modulo fifty. -/
theorem lengthTwoCrossingTarget_one_gap_fiveUnit_iff_mod_fifty
    (b : ℕ) {gap : ℕ} (gap_odd : Odd gap) :
    IsUnit 5 (lengthTwoCrossingTarget b 1 gap) ↔
      IsUnit 5 (lengthTwoCrossingTarget b 1 (gap % 50)) := by
  obtain ⟨half, gap_eq⟩ := gap_odd
  have residue_odd : Odd (gap % 50) := by
    refine ⟨(gap % 50) / 2, ?_⟩
    omega
  have residue_positive : 0 < gap % 50 := by
    obtain ⟨residue_half, residue_eq⟩ := residue_odd
    omega
  have periodic (base repetitions : ℕ) (base_positive : 0 < base)
      (base_odd : Odd base) :
      IsUnit 5 (lengthTwoCrossingTarget b 1 (base + 50 * repetitions)) ↔
        IsUnit 5 (lengthTwoCrossingTarget b 1 base) := by
    induction repetitions with
    | zero => simp
    | succ repetitions induction =>
        have current_positive : 0 < base + 50 * repetitions := by omega
        obtain ⟨base_half, base_eq⟩ := base_odd
        have current_odd : Odd (base + 50 * repetitions) :=
          ⟨base_half + 25 * repetitions, by omega⟩
        rw [Nat.mul_succ, ← Nat.add_assoc,
          lengthTwoCrossingTarget_one_gap_add_fifty_fiveUnit_iff
            b current_positive current_odd]
        exact induction
  have decomposition : gap % 50 + 50 * (gap / 50) = gap := Nat.mod_add_div gap 50
  have reduced := periodic (gap % 50) (gap / 50) residue_positive residue_odd
  rw [decomposition] at reduced
  exact reduced

/-- Every `k = 2` gap congruent to eight modulo ten reduces completely modulo 250. -/
theorem lengthTwoCrossingTarget_two_gap_fiveUnit_iff_mod_twoFifty
    (b : ℕ) {gap : ℕ} (gap_mod : gap % 10 = 8) :
    IsUnit 5 (lengthTwoCrossingTarget b 2 gap) ↔
      IsUnit 5 (lengthTwoCrossingTarget b 2 (gap % 250)) := by
  have residue_mod : (gap % 250) % 10 = 8 := by omega
  have residue_positive : 0 < gap % 250 := by omega
  have periodic (base repetitions : ℕ) (base_positive : 0 < base)
      (base_mod : base % 10 = 8) :
      IsUnit 5 (lengthTwoCrossingTarget b 2 (base + 250 * repetitions)) ↔
        IsUnit 5 (lengthTwoCrossingTarget b 2 base) := by
    induction repetitions with
    | zero => simp
    | succ repetitions induction =>
        have current_positive : 0 < base + 250 * repetitions := by omega
        have current_mod : (base + 250 * repetitions) % 10 = 8 := by omega
        rw [Nat.mul_succ, ← Nat.add_assoc,
          lengthTwoCrossingTarget_two_gap_add_twoFifty_fiveUnit_iff
            b current_positive current_mod]
        exact induction
  have decomposition : gap % 250 + 250 * (gap / 250) = gap := Nat.mod_add_div gap 250
  have reduced := periodic (gap % 250) (gap / 250) residue_positive residue_mod
  rw [decomposition] at reduced
  exact reduced

/-- Accepted `(gap mod 50, tail mod 10)` pairs in the `k = 1` family. -/
def lengthTwoOneTargetResidue (gap tail : ℕ) : Prop :=
  (gap = 1 ∧ (tail = 1 ∨ tail = 3 ∨ tail = 7 ∨ tail = 9)) ∨
  (gap = 7 ∧ (tail = 0 ∨ tail = 4 ∨ tail = 6 ∨ tail = 8)) ∨
  (gap = 11 ∧ (tail = 1 ∨ tail = 5 ∨ tail = 7 ∨ tail = 9)) ∨
  (gap = 17 ∧ (tail = 0 ∨ tail = 2 ∨ tail = 6 ∨ tail = 8)) ∨
  (gap = 21 ∧ (tail = 3 ∨ tail = 5 ∨ tail = 7 ∨ tail = 9)) ∨
  (gap = 27 ∧ (tail = 0 ∨ tail = 2 ∨ tail = 4 ∨ tail = 8)) ∨
  (gap = 31 ∧ (tail = 1 ∨ tail = 3 ∨ tail = 5 ∨ tail = 7)) ∨
  (gap = 37 ∧ (tail = 0 ∨ tail = 2 ∨ tail = 4 ∨ tail = 6)) ∨
  (gap = 41 ∧ (tail = 1 ∨ tail = 3 ∨ tail = 5 ∨ tail = 9)) ∨
  gap = 47 ∧ (tail = 2 ∨ tail = 4 ∨ tail = 6 ∨ tail = 8)

/-- The first finite rectangle is exactly the displayed forty accepted residue pairs. -/
theorem lengthTwoCrossingTarget_one_fiveUnit_iff_residue
    (b : ℕ) {gap : ℕ} (gap_positive : 0 < gap) (gap_odd : Odd gap)
    (gap_mod : gap % 10 ≠ 9) :
    IsUnit 5 (lengthTwoCrossingTarget b 1 gap) ↔
      lengthTwoOneTargetResidue (gap % 50) (b % 10) := by
  have gap_depth : shellSlopeGapFiveDepth gap = 0 :=
    (shellSlopeGapFiveDepth_eq_zero_iff_odd gap).2 gap_odd
  have next_depth :=
    (oddGap_nextDepth_eq_one_iff_modTen_ne_nine gap_odd).2 gap_mod
  have carry : shellSlopeGapFiveDepth (gap + 1) =
      shellSlopeGapFiveDepth gap + 1 := by
    rw [next_depth, gap_depth]
  rw [lengthTwoCrossingTarget_fiveUnit_iff_mod_ten b 1 gap_positive carry,
    lengthTwoCrossingTarget_one_gap_fiveUnit_iff_mod_fifty (b % 10) gap_odd]
  generalize gap_eq : gap % 50 = gapResidue
  generalize tail_eq : b % 10 = tailResidue
  have gap_lt : gapResidue < 50 := by
    have := Nat.mod_lt gap (by norm_num : 0 < 50)
    omega
  have tail_lt : tailResidue < 10 := by
    have := Nat.mod_lt b (by norm_num : 0 < 10)
    omega
  interval_cases gapResidue <;> interval_cases tailResidue <;>
    norm_num [lengthTwoOneTargetResidue, lengthTwoCrossingTarget, HasValue, padicValRat,
      padicValInt.eq_zero_of_not_dvd, padicValNat.eq_zero_of_not_dvd,
      padicValNat_self, padicValNat.mul, padicValNat.prime_pow]

/-- Accepted `(gap mod 250, tail mod 10)` pairs in the `k = 2` family. -/
def lengthTwoTwoTargetResidue (gap tail : ℕ) : Prop :=
  (gap = 18 ∧ (tail = 0 ∨ tail = 2 ∨ tail = 4 ∨ tail = 6)) ∨
  (gap = 28 ∧ (tail = 1 ∨ tail = 3 ∨ tail = 5 ∨ tail = 9)) ∨
  (gap = 68 ∧ (tail = 0 ∨ tail = 4 ∨ tail = 6 ∨ tail = 8)) ∨
  (gap = 78 ∧ (tail = 1 ∨ tail = 5 ∨ tail = 7 ∨ tail = 9)) ∨
  (gap = 118 ∧ (tail = 0 ∨ tail = 2 ∨ tail = 4 ∨ tail = 8)) ∨
  (gap = 128 ∧ (tail = 1 ∨ tail = 3 ∨ tail = 5 ∨ tail = 7)) ∨
  (gap = 168 ∧ (tail = 2 ∨ tail = 4 ∨ tail = 6 ∨ tail = 8)) ∨
  (gap = 178 ∧ (tail = 1 ∨ tail = 3 ∨ tail = 7 ∨ tail = 9)) ∨
  (gap = 218 ∧ (tail = 0 ∨ tail = 2 ∨ tail = 6 ∨ tail = 8)) ∨
  gap = 228 ∧ (tail = 3 ∨ tail = 5 ∨ tail = 7 ∨ tail = 9)

/-- The second finite rectangle is exactly the displayed forty accepted residue pairs. -/
theorem lengthTwoCrossingTarget_two_fiveUnit_iff_residue
    (b : ℕ) {gap : ℕ} (gap_positive : 0 < gap)
    (gap_mod_ten : gap % 10 = 8) (gap_mod_fifty : gap % 50 ≠ 48) :
    IsUnit 5 (lengthTwoCrossingTarget b 2 gap) ↔
      lengthTwoTwoTargetResidue (gap % 250) (b % 10) := by
  have depth_pair := (evenGap_depthPair_iff_residues gap_positive).2
    ⟨gap_mod_ten, gap_mod_fifty⟩
  have carry : shellSlopeGapFiveDepth (gap + 2) =
      shellSlopeGapFiveDepth gap + 1 := by
    rw [depth_pair.1, depth_pair.2]
  rw [lengthTwoCrossingTarget_fiveUnit_iff_mod_ten b 2 gap_positive carry,
    lengthTwoCrossingTarget_two_gap_fiveUnit_iff_mod_twoFifty (b % 10) gap_mod_ten]
  generalize gap_eq : gap % 250 = gapResidue
  generalize tail_eq : b % 10 = tailResidue
  have gap_lt : gapResidue < 250 := by
    have := Nat.mod_lt gap (by norm_num : 0 < 250)
    omega
  have tail_lt : tailResidue < 10 := by
    have := Nat.mod_lt b (by norm_num : 0 < 10)
    omega
  have residue_mod_ten : gapResidue % 10 = 8 := by omega
  have residue_mod_fifty : gapResidue % 50 ≠ 48 := by omega
  have gap_cases :
      gapResidue = 8 ∨ gapResidue = 18 ∨ gapResidue = 28 ∨ gapResidue = 38 ∨
      gapResidue = 58 ∨ gapResidue = 68 ∨ gapResidue = 78 ∨ gapResidue = 88 ∨
      gapResidue = 108 ∨ gapResidue = 118 ∨ gapResidue = 128 ∨ gapResidue = 138 ∨
      gapResidue = 158 ∨ gapResidue = 168 ∨ gapResidue = 178 ∨ gapResidue = 188 ∨
      gapResidue = 208 ∨ gapResidue = 218 ∨ gapResidue = 228 ∨ gapResidue = 238 := by
    omega
  rcases gap_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases tailResidue <;>
    norm_num [lengthTwoTwoTargetResidue, lengthTwoCrossingTarget, HasValue, padicValRat,
      padicValInt.eq_zero_of_not_dvd, padicValNat.eq_zero_of_not_dvd,
      padicValNat_self, padicValNat.mul, padicValNat.prime_pow]

private theorem lengthTwoCrossingOneSource_eq
    (c : ℕ) {gap : ℕ} (gap_positive : 0 < gap) :
    lengthTwoCrossingSource c 1 gap =
      (3 / 2 : ℚ) ^ c * (1 / 2) / (3 * (1 - (2 / 3 : ℚ) ^ gap)) := by
  calc
    lengthTwoCrossingSource c 1 gap =
        (3 / 2 : ℚ) ^ c * lengthTwoCrossingSource 0 1 gap := by
      simpa using (lengthTwoCrossingSource_add 0 1 gap_positive c)
    _ = (3 / 2 : ℚ) ^ c * (1 / 2) /
        (3 * (1 - (2 / 3 : ℚ) ^ gap)) := by
      have gap_ne : 1 - (2 / 3 : ℚ) ^ gap ≠ 0 := by
        have gap_lt : (2 / 3 : ℚ) ^ gap < 1 :=
          pow_lt_one₀ (by norm_num) (by norm_num) gap_positive.ne'
        linarith
      rw [lengthTwoCrossingSource]
      norm_num
      field_simp [gap_ne]

private theorem lengthTwoCrossingOneSource_gap_one (c : ℕ) :
    lengthTwoCrossingSource c 1 1 = (3 / 2 : ℚ) ^ c / 2 := by
  rw [lengthTwoCrossingOneSource_eq c (by norm_num)]
  norm_num
  ring

private theorem lengthTwoCrossingOneSource_gap_three (c : ℕ) :
    lengthTwoCrossingSource c 1 3 = (3 / 2 : ℚ) ^ c * (9 / 38) := by
  rw [lengthTwoCrossingOneSource_eq c (by norm_num)]
  norm_num
  ring

/-- The real-trap head gauges in the `k = 1` family are completely explicit. -/
theorem lengthTwoCrossingOneSource_mem_realTrap_iff
    (c : ℕ) {gap : ℕ} (gap_positive : 0 < gap) (gap_odd : Odd gap) :
    lengthTwoCrossingSource c 1 gap ∈ Set.Icc (1 / 5) (1 / 2) ↔
      (gap = 1 ∧ c = 0) ∨ (gap = 3 ∧ c ≤ 1) ∨
        (5 ≤ gap ∧ (c = 1 ∨ c = 2)) := by
  have gap_cases : gap = 1 ∨ gap = 3 ∨ 5 ≤ gap := by
    obtain ⟨half, gap_eq⟩ := gap_odd
    omega
  rcases gap_cases with rfl | rfl | gap_large
  · rw [lengthTwoCrossingOneSource_gap_one]
    norm_num
    constructor
    · rintro ⟨lower, upper⟩
      by_contra c_ne
      have one_le_c : 1 ≤ c := by omega
      have power_lower : (3 / 2 : ℚ) ^ 1 ≤ (3 / 2 : ℚ) ^ c :=
        pow_right_mono₀ (by norm_num) one_le_c
      norm_num at power_lower
      nlinarith
    · rintro rfl
      norm_num
  · rw [lengthTwoCrossingOneSource_gap_three]
    norm_num
    constructor
    · rintro ⟨lower, upper⟩
      by_contra c_large
      have two_le_c : 2 ≤ c := by omega
      have power_lower : (3 / 2 : ℚ) ^ 2 ≤ (3 / 2 : ℚ) ^ c :=
        pow_right_mono₀ (by norm_num) two_le_c
      norm_num at power_lower
      nlinarith
    · intro c_le
      have c_cases : c = 0 ∨ c = 1 := by omega
      rcases c_cases with rfl | rfl <;> norm_num
  · have gap_ne_one : gap ≠ 1 := by omega
    have gap_ne_three : gap ≠ 3 := by omega
    rw [lengthTwoCrossingOneSource_eq c gap_positive]
    let denominator : ℚ := 3 * (1 - (2 / 3 : ℚ) ^ gap)
    have denominator_positive : 0 < denominator := by
      have gap_power_lt : (2 / 3 : ℚ) ^ gap < 1 :=
        pow_lt_one₀ (by norm_num) (by norm_num) gap_positive.ne'
      dsimp only [denominator]
      positivity
    have gap_power_upper : (2 / 3 : ℚ) ^ gap ≤ (2 / 3 : ℚ) ^ 5 :=
      (pow_right_strictAnti₀ (show 0 < (2 / 3 : ℚ) by norm_num)
        (show (2 / 3 : ℚ) < 1 by norm_num)).antitone gap_large
    have denominator_lower : (211 / 81 : ℚ) ≤ denominator := by
      dsimp only [denominator]
      norm_num at gap_power_upper ⊢
      linarith
    have denominator_lt_three : denominator < 3 := by
      have gap_power_positive : 0 < (2 / 3 : ℚ) ^ gap := by positivity
      dsimp only [denominator]
      nlinarith
    have source_iff :
        (3 / 2 : ℚ) ^ c * (1 / 2) / denominator ∈ Set.Icc (1 / 5) (1 / 2) ↔
          c = 1 ∨ c = 2 := by
      constructor
      · rintro ⟨source_lower, source_upper⟩
        have c_positive : 0 < c := by
          by_contra c_not_positive
          have c_zero : c = 0 := by omega
          subst c
          norm_num at source_lower
          have source_low : (1 / 2 : ℚ) / denominator < 1 / 5 := by
            apply (div_lt_iff₀ denominator_positive).2
            nlinarith
          exact (not_lt_of_ge source_lower) source_low
        have c_lt_three : c < 3 := by
          by_contra c_not_small
          have three_le_c : 3 ≤ c := by omega
          have power_lower : (3 / 2 : ℚ) ^ 3 ≤ (3 / 2 : ℚ) ^ c :=
            pow_right_mono₀ (by norm_num) three_le_c
          norm_num at power_lower
          have source_high :
              1 / 2 < (3 / 2 : ℚ) ^ c * (1 / 2) / denominator := by
            apply (lt_div_iff₀ denominator_positive).2
            nlinarith
          exact (not_lt_of_ge source_upper) source_high
        omega
      · rintro (rfl | rfl)
        · constructor
          · apply (le_div_iff₀ denominator_positive).2
            norm_num
            nlinarith
          · apply (div_le_iff₀ denominator_positive).2
            norm_num
            nlinarith
        · constructor
          · apply (le_div_iff₀ denominator_positive).2
            norm_num
            nlinarith
          · apply (div_le_iff₀ denominator_positive).2
            norm_num
            nlinarith
    simpa [gap_ne_one, gap_ne_three, gap_large] using source_iff

private theorem lengthTwoCrossingTwoSource_eq
    (c : ℕ) {gap : ℕ} (gap_positive : 0 < gap) :
    lengthTwoCrossingSource c 2 gap =
      (3 / 2 : ℚ) ^ c * 5 / (12 * (1 - (2 / 3 : ℚ) ^ gap)) := by
  calc
    lengthTwoCrossingSource c 2 gap =
        (3 / 2 : ℚ) ^ c * lengthTwoCrossingSource 0 2 gap := by
      simpa using (lengthTwoCrossingSource_add 0 2 gap_positive c)
    _ = (3 / 2 : ℚ) ^ c * 5 /
        (12 * (1 - (2 / 3 : ℚ) ^ gap)) := by
      have gap_ne : 1 - (2 / 3 : ℚ) ^ gap ≠ 0 := by
        have gap_lt : (2 / 3 : ℚ) ^ gap < 1 :=
          pow_lt_one₀ (by norm_num) (by norm_num) gap_positive.ne'
        linarith
      rw [lengthTwoCrossingSource]
      norm_num
      field_simp [gap_ne]
      ring

/-- Every surviving `k = 2` gap has the unique real-trap head gauge zero. -/
theorem lengthTwoCrossingTwoSource_mem_realTrap_iff
    (c : ℕ) {gap : ℕ} (gap_positive : 0 < gap) (gap_large : 8 ≤ gap) :
    lengthTwoCrossingSource c 2 gap ∈ Set.Icc (1 / 5) (1 / 2) ↔ c = 0 := by
  rw [lengthTwoCrossingTwoSource_eq c gap_positive]
  let denominator : ℚ := 12 * (1 - (2 / 3 : ℚ) ^ gap)
  have denominator_positive : 0 < denominator := by
    have gap_power_lt : (2 / 3 : ℚ) ^ gap < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) gap_positive.ne'
    dsimp only [denominator]
    positivity
  have gap_power_upper : (2 / 3 : ℚ) ^ gap ≤ (2 / 3 : ℚ) ^ 8 :=
    (pow_right_strictAnti₀ (show 0 < (2 / 3 : ℚ) by norm_num)
      (show (2 / 3 : ℚ) < 1 by norm_num)).antitone gap_large
  have denominator_gt_ten : 10 < denominator := by
    dsimp only [denominator]
    norm_num at gap_power_upper ⊢
    linarith
  have denominator_lt_twelve : denominator < 12 := by
    have gap_power_positive : 0 < (2 / 3 : ℚ) ^ gap := by positivity
    dsimp only [denominator]
    nlinarith
  constructor
  · rintro ⟨source_lower, source_upper⟩
    by_contra c_ne
    have one_le_c : 1 ≤ c := by omega
    have power_lower : (3 / 2 : ℚ) ^ 1 ≤ (3 / 2 : ℚ) ^ c :=
      pow_right_mono₀ (by norm_num) one_le_c
    norm_num at power_lower
    have source_high : 1 / 2 < (3 / 2 : ℚ) ^ c * 5 / denominator := by
      apply (lt_div_iff₀ denominator_positive).2
      nlinarith
    exact (not_lt_of_ge source_upper) source_high
  · rintro rfl
    norm_num
    constructor
    · apply (le_div_iff₀ denominator_positive).2
      nlinarith
    · apply (div_le_iff₀ denominator_positive).2
      nlinarith

/-- Every fully guarded real-trap length-two crossing lies in one of two residue families. -/
theorem lengthTwoCrossing_acceptance_forces_residueFamily
    (b c : ℕ) {k gap : ℕ} (k_positive : 0 < k) (gap_positive : 0 < gap)
    (source_mem : lengthTwoCrossingSource c k gap ∈ Set.Icc (1 / 5) (1 / 2))
    (source_unit : IsUnit 5 (lengthTwoCrossingSource c k gap))
    (target_unit : IsUnit 5 (lengthTwoCrossingTarget b k gap)) :
    (k = 1 ∧ Odd gap ∧ gap % 10 ≠ 9) ∨
      (k = 2 ∧ gap % 10 = 8 ∧ gap % 50 ≠ 48) := by
  have k_le_two := lengthTwoCrossing_realTrap_forces_k_le_two
    c k_positive gap_positive source_mem
  have source_depth :=
    (lengthTwoCrossingSource_fiveUnit_iff c k_positive gap_positive).1 source_unit
  have target_depth :=
    lengthTwoCrossingTarget_fiveUnit_forces_carry b k gap_positive target_unit
  exact (lengthTwoGapDepths_iff_residues k_positive gap_positive k_le_two).1
    ⟨source_depth, target_depth⟩

/-- Full length-two acceptance is exactly one explicit finite semilinear table. -/
theorem lengthTwoCrossing_acceptance_iff_semilinearTable
    (b c : ℕ) {k gap : ℕ} (k_positive : 0 < k) (gap_positive : 0 < gap) :
    lengthTwoCrossingSource c k gap ∈ Set.Icc (1 / 5) (1 / 2) ∧
        IsUnit 5 (lengthTwoCrossingSource c k gap) ∧
        IsUnit 5 (lengthTwoCrossingTarget b k gap) ↔
      (k = 1 ∧ Odd gap ∧ gap % 10 ≠ 9 ∧
        ((gap = 1 ∧ c = 0) ∨ (gap = 3 ∧ c ≤ 1) ∨
          (5 ≤ gap ∧ (c = 1 ∨ c = 2))) ∧
        lengthTwoOneTargetResidue (gap % 50) (b % 10)) ∨
      (k = 2 ∧ gap % 10 = 8 ∧ gap % 50 ≠ 48 ∧ c = 0 ∧
        lengthTwoTwoTargetResidue (gap % 250) (b % 10)) := by
  constructor
  · rintro ⟨source_mem, source_unit, target_unit⟩
    have family := lengthTwoCrossing_acceptance_forces_residueFamily b c
      k_positive gap_positive source_mem source_unit target_unit
    rcases family with ⟨k_eq, gap_odd, gap_mod⟩ | ⟨k_eq, gap_mod_ten, gap_mod_fifty⟩
    · subst k
      have gauge :=
        (lengthTwoCrossingOneSource_mem_realTrap_iff
          c gap_positive gap_odd).1 source_mem
      have target_residue :=
        (lengthTwoCrossingTarget_one_fiveUnit_iff_residue
          b gap_positive gap_odd gap_mod).1 target_unit
      exact Or.inl ⟨rfl, gap_odd, gap_mod, gauge, target_residue⟩
    · subst k
      have gap_large : 8 ≤ gap := by omega
      have gauge :=
        (lengthTwoCrossingTwoSource_mem_realTrap_iff
          c gap_positive gap_large).1 source_mem
      have target_residue :=
        (lengthTwoCrossingTarget_two_fiveUnit_iff_residue
          b gap_positive gap_mod_ten gap_mod_fifty).1 target_unit
      exact Or.inr
        ⟨rfl, gap_mod_ten, gap_mod_fifty, gauge, target_residue⟩
  · rintro (⟨k_eq, gap_odd, gap_mod, gauge, target_residue⟩ |
      ⟨k_eq, gap_mod_ten, gap_mod_fifty, c_zero, target_residue⟩)
    · subst k
      have source_mem :=
        (lengthTwoCrossingOneSource_mem_realTrap_iff
          c gap_positive gap_odd).2 gauge
      have depths := (lengthTwoGapDepths_iff_residues
        (show 0 < 1 by norm_num) gap_positive (show 1 ≤ 2 by norm_num)).2
        (Or.inl ⟨rfl, gap_odd, gap_mod⟩)
      have source_unit :=
        (lengthTwoCrossingSource_fiveUnit_iff c (by norm_num) gap_positive).2 depths.1
      have target_unit :=
        (lengthTwoCrossingTarget_one_fiveUnit_iff_residue
          b gap_positive gap_odd gap_mod).2 target_residue
      exact ⟨source_mem, source_unit, target_unit⟩
    · subst k
      subst c
      have gap_large : 8 ≤ gap := by omega
      have source_mem :=
        (lengthTwoCrossingTwoSource_mem_realTrap_iff
          0 gap_positive gap_large).2 rfl
      have depths := (lengthTwoGapDepths_iff_residues
        (show 0 < 2 by norm_num) gap_positive (show 2 ≤ 2 by norm_num)).2
        (Or.inr ⟨rfl, gap_mod_ten, gap_mod_fifty⟩)
      have source_unit :=
        (lengthTwoCrossingSource_fiveUnit_iff 0 (by norm_num) gap_positive).2 depths.1
      have target_unit :=
        (lengthTwoCrossingTarget_two_fiveUnit_iff_residue
          b gap_positive gap_mod_ten gap_mod_fifty).2 target_residue
      exact ⟨source_mem, source_unit, target_unit⟩

private theorem collisionSource_swap (left right : List ℕ) :
    collisionSource left right = collisionSource right left := by
  simp only [collisionSource]
  calc
    (shellIntercept right - shellIntercept left) /
        (shellSlope left - shellSlope right) =
      (-(shellIntercept left - shellIntercept right)) /
        (-(shellSlope right - shellSlope left)) := by
          congr 1 <;> ring
    _ = (shellIntercept left - shellIntercept right) /
        (shellSlope right - shellSlope left) := neg_div_neg_eq _ _

private theorem lengthTwoPositiveCollision_orientedNormalForm
    {leftHead leftTail rightHead rightTail : ℕ}
    (sum_gt : rightHead + rightTail < leftHead + leftTail)
    (source_positive :
      0 < collisionSource [leftHead, leftTail] [rightHead, rightTail]) :
    ∃ k gap : ℕ, 0 < k ∧ 0 < gap ∧
      leftHead = rightHead + k + gap ∧ rightTail = leftTail + k := by
  have sum_ne : [leftHead, leftTail].sum ≠ [rightHead, rightTail].sum := by
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  have distinct : [leftHead, leftTail] ≠ [rightHead, rightTail] := by
    intro schedules_eq
    exact sum_ne (congrArg List.sum schedules_eq)
  have slope_ne :
      shellSlope [leftHead, leftTail] ≠ shellSlope [rightHead, rightTail] := by
    intro slope_eq
    exact sum_ne
      ((shellSlope_eq_iff_length_sum [leftHead, leftTail]
        [rightHead, rightTail]).1 slope_eq).2
  have collision := shellRun_collisionSource
    [leftHead, leftTail] [rightHead, rightTail] slope_ne
  have crossing := sameLength_positiveSource_collision_suffixSums_cross
    (show [leftHead, leftTail].length = [rightHead, rightTail].length by rfl)
    distinct source_positive collision
  obtain ⟨cut, proper_gap⟩ := crossing.2
  have tail_lt : leftTail < rightTail := by
    cases cut with
    | zero =>
        simp only [List.drop_zero, List.sum_cons, List.sum_nil, Nat.add_zero] at proper_gap
        omega
    | succ cut =>
        cases cut with
        | zero =>
            simpa only [List.drop_succ_cons, List.drop_zero, List.sum_cons,
              List.sum_nil, Nat.add_zero] using proper_gap
        | succ cut =>
            simp only [List.drop_succ_cons] at proper_gap
            exact (lt_irrefl _ proper_gap).elim
  refine ⟨rightTail - leftTail,
    leftHead + leftTail - (rightHead + rightTail), ?_, ?_, ?_, ?_⟩ <;> omega

/-- Every positive cross-grade length-two collision has, uniquely up to swapping the two
schedules, the canonical mixed-sign normal form. -/
theorem lengthTwoCollisionSource_pos_iff_crossingNormalForm
    (leftHead leftTail rightHead rightTail : ℕ) :
    (leftHead + leftTail ≠ rightHead + rightTail ∧
      0 < collisionSource [leftHead, leftTail] [rightHead, rightTail]) ↔
      (∃ k gap : ℕ, 0 < k ∧ 0 < gap ∧
        leftHead = rightHead + k + gap ∧ rightTail = leftTail + k) ∨
      (∃ k gap : ℕ, 0 < k ∧ 0 < gap ∧
        rightHead = leftHead + k + gap ∧ leftTail = rightTail + k) := by
  constructor
  · rintro ⟨sum_ne, source_positive⟩
    rcases lt_or_gt_of_ne sum_ne with sum_lt | sum_gt
    · right
      have swapped_positive :
          0 < collisionSource [rightHead, rightTail] [leftHead, leftTail] := by
        rw [collisionSource_swap]
        exact source_positive
      exact lengthTwoPositiveCollision_orientedNormalForm sum_lt swapped_positive
    · left
      exact lengthTwoPositiveCollision_orientedNormalForm sum_gt source_positive
  · rintro (⟨k, gap, k_positive, gap_positive, head_eq, tail_eq⟩ |
      ⟨k, gap, k_positive, gap_positive, head_eq, tail_eq⟩)
    · constructor
      · omega
      · rw [head_eq, tail_eq]
        change 0 < collisionSource (lengthTwoCrossingLeft leftTail rightHead k gap)
          (lengthTwoCrossingRight leftTail rightHead k)
        rw [lengthTwoCrossing_collisionSource leftTail rightHead k gap_positive]
        exact lengthTwoCrossingSource_positive rightHead k_positive gap_positive
    · constructor
      · omega
      · rw [collisionSource_swap, head_eq, tail_eq]
        change 0 < collisionSource (lengthTwoCrossingLeft rightTail leftHead k gap)
          (lengthTwoCrossingRight rightTail leftHead k)
        rw [lengthTwoCrossing_collisionSource rightTail leftHead k gap_positive]
        exact lengthTwoCrossingSource_positive leftHead k_positive gap_positive

end MatrixMortality.MixedPrimeDebt
