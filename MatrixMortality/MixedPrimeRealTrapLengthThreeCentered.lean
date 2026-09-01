import MatrixMortality.MixedPrimeRealTrapLengthThree

/-!
# Centered carry walls in the falling length-three chamber

The two positive-valuation denominator branches of the last open length-three chamber have a
common form. After multiplication by a five-adic unit, the target carry is a fixed residual
divided by `1-(2/3)^(2h)`, minus one coefficient. Target acceptance forces that coefficient to
have value one and the fixed residual to lie exactly one five-adic level below the moving wall.
The wall parameter has potentially unbounded depth; accepted points can occur only at its exact
residual match.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation
open PeriodicShell

private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private theorem fallingCentered_unit_pow
    {value : ℚ} (value_unit : IsUnit 5 value) (exponent : ℕ) :
    IsUnit 5 (value ^ exponent) := by
  refine ⟨pow_ne_zero exponent value_unit.1, ?_⟩
  rw [padicValRat.pow, value_unit.2]
  simp

private theorem fallingCentered_shellRatio_unit : IsUnit 5 (2 / 3 : ℚ) :=
  div_hasValue
    (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (2 : ℤ)))
    (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (3 : ℤ)))

private theorem fallingCentered_one_sub_shellRatio_pow_hasValue
    {exponent : ℕ} (exponent_positive : 0 < exponent) :
    HasValue 5 (1 - (2 / 3 : ℚ) ^ exponent)
      (shellSlopeGapFiveDepth exponent) := by
  have negative_value := neg_hasValue
    (shellRatio_pow_sub_one_hasValue exponent_positive)
  convert negative_value using 1
  ring

private theorem fallingCentered_fifteen_hasValue : HasValue 5 (15 : ℚ) 1 := by
  have three_unit : IsUnit 5 (3 : ℚ) :=
    intCast_isUnit_of_not_dvd (by norm_num)
  have five_value : HasValue 5 (5 : ℚ) 1 := by
    convert primePower_hasValue (prime := 5) 1 using 1 <;> norm_num
  convert mul_hasValue three_unit five_value using 1 <;> norm_num

/-- Cleared coefficient in the `k=1`, odd-`B` centered branch. -/
def lengthThreeFallingOneOddWallCoefficient (q a : ℕ) : ℚ :=
  9 * (2 / 3 : ℚ) ^ (q + 1) * (1 - (2 / 3 : ℚ) ^ (2 * a)) -
    10 * (2 / 3 : ℚ) ^ (2 * a)

/-- Fixed residual left when the `k=1`, odd-`B` denominator reaches its wall. -/
def lengthThreeFallingOneOddWallResidual (q a : ℕ) : ℚ :=
  15 * (2 / 3 : ℚ) ^ (2 * a) +
    lengthThreeFallingOneOddWallCoefficient q a

/-- Cleared coefficient in the `k=2`, even-`B` centered branch. -/
def lengthThreeFallingTwoEvenWallCoefficient (a : ℕ) : ℚ :=
  9 - 24 * (2 / 3 : ℚ) ^ (2 * a)

/-- Fixed residual left when the `k=2`, even-`B` denominator reaches its wall. -/
def lengthThreeFallingTwoEvenWallResidual (a : ℕ) : ℚ :=
  15 * (2 / 3 : ℚ) ^ (2 * a) +
    (2 / 3 : ℚ) ^ 2 * lengthThreeFallingTwoEvenWallCoefficient a

/-- Uncleared numerator at a fixed odd `k=1` wall, with `m` the half-gap below the wall. -/
def lengthThreeFallingOneOddWallNumerator (q m wall : ℕ) : ℚ :=
  15 + 9 * (2 / 3 : ℚ) ^ (q + 1) * (2 / 3 : ℚ) ^ (2 * m) -
    (9 * (2 / 3 : ℚ) ^ (q + 1) + 10) * (2 / 3 : ℚ) ^ (2 * wall)

/-- Uncleared numerator at a fixed even `k=2` wall, with `b` the half-middle gap. -/
def lengthThreeFallingTwoEvenWallNumerator (b wall : ℕ) : ℚ :=
  15 + 9 * (2 / 3 : ℚ) ^ (2 * b) -
    24 * (2 / 3 : ℚ) ^ (2 * wall)

/-- Exact centered quotient in the `k=1`, odd-`B` branch. -/
theorem lengthThreeFalling_one_odd_targetCarry_centered
    (q a b : ℕ) (wall_positive : 0 < a + b) :
    (2 / 3 : ℚ) ^ (2 * a) *
        lengthThreeFallingTargetCarry q (2 * a) (2 * b + 1) 1 =
      lengthThreeFallingOneOddWallResidual q a /
          ((2 / 3 : ℚ) * (1 - (2 / 3 : ℚ) ^ (2 * (a + b)))) -
        lengthThreeFallingOneOddWallCoefficient q a / (2 / 3 : ℚ) := by
  have base_ne : (2 / 3 : ℚ) ≠ 0 := by norm_num
  have wall_power_lt : (2 / 3 : ℚ) ^ (2 * (a + b)) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have wall_ne : 1 - (2 / 3 : ℚ) ^ (2 * (a + b)) ≠ 0 := by
    linarith
  have wall_product_ne :
      1 - (2 / 3 : ℚ) ^ (2 * a) * (2 / 3 : ℚ) ^ (2 * b) ≠ 0 := by
    rw [← pow_add, show 2 * a + 2 * b = 2 * (a + b) by omega]
    exact wall_ne
  rw [lengthThreeFallingTargetCarry, lengthThreeFallingSourceCarry,
    lengthThreeFallingGainGap, lengthThreeFallingOneOddWallResidual,
    lengthThreeFallingOneOddWallCoefficient]
  simp only [pow_one]
  rw [show 2 * a + (2 * b + 1) = 1 + (2 * a + 2 * b) by omega,
    show 2 * b + 1 = 1 + 2 * b by omega,
    show 2 * (a + b) = 2 * a + 2 * b by omega]
  simp only [pow_add, pow_one]
  field_simp [base_ne, wall_product_ne]
  ring

/-- Cleared centered numerator in the `k=1`, odd-`B` branch. -/
theorem lengthThreeFalling_one_odd_targetCarry_cleared
    (q a b : ℕ) (wall_positive : 0 < a + b) :
    ((2 / 3 : ℚ) ^ (2 * a) *
          lengthThreeFallingTargetCarry q (2 * a) (2 * b + 1) 1) *
        ((2 / 3 : ℚ) * (1 - (2 / 3 : ℚ) ^ (2 * (a + b)))) =
      15 * (2 / 3 : ℚ) ^ (2 * a) +
        (2 / 3 : ℚ) ^ (2 * (a + b)) *
          lengthThreeFallingOneOddWallCoefficient q a := by
  have wall_power_lt : (2 / 3 : ℚ) ^ (2 * (a + b)) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have wall_ne : 1 - (2 / 3 : ℚ) ^ (2 * (a + b)) ≠ 0 := by
    linarith
  rw [lengthThreeFalling_one_odd_targetCarry_centered q a b wall_positive,
    lengthThreeFallingOneOddWallResidual]
  field_simp [wall_ne]
  ring

/-- The centered `k=1` quotient clears to the fixed-wall numerator. -/
theorem lengthThreeFalling_one_odd_targetCarry_mul_wall
    (q a b : ℕ) (wall_positive : 0 < a + b) :
    lengthThreeFallingTargetCarry q (2 * a) (2 * b + 1) 1 *
        ((2 / 3 : ℚ) * (1 - (2 / 3 : ℚ) ^ (2 * (a + b)))) =
      lengthThreeFallingOneOddWallNumerator q b (a + b) := by
  have source_scale_ne : (2 / 3 : ℚ) ^ (2 * a) ≠ 0 := by positivity
  have cleared :=
    lengthThreeFalling_one_odd_targetCarry_cleared q a b wall_positive
  rw [lengthThreeFallingOneOddWallCoefficient] at cleared
  rw [lengthThreeFallingOneOddWallNumerator]
  rw [show 2 * (a + b) = 2 * a + 2 * b by omega, pow_add] at cleared ⊢
  field_simp [source_scale_ne] at cleared ⊢
  nlinarith

/-- Depth two of the odd `k=1` carry is exactly depth two above its moving-wall numerator. -/
theorem lengthThreeFalling_one_odd_targetCarry_hasValue_two_iff_numerator
    (q a b : ℕ) (wall_positive : 0 < a + b) :
    HasValue 5
        (lengthThreeFallingTargetCarry q (2 * a) (2 * b + 1) 1) 2 ↔
      HasValue 5 (lengthThreeFallingOneOddWallNumerator q b (a + b))
        ((shellSlopeGapFiveDepth (2 * (a + b)) : ℤ) + 2) := by
  have wall_value :
      HasValue 5 (1 - (2 / 3 : ℚ) ^ (2 * (a + b)))
        (shellSlopeGapFiveDepth (2 * (a + b))) :=
    fallingCentered_one_sub_shellRatio_pow_hasValue (by omega)
  have denominator_value :
      HasValue 5
        ((2 / 3 : ℚ) * (1 - (2 / 3 : ℚ) ^ (2 * (a + b))))
        (shellSlopeGapFiveDepth (2 * (a + b))) := by
    simpa using mul_hasValue fallingCentered_shellRatio_unit wall_value
  have cleared :=
    lengthThreeFalling_one_odd_targetCarry_mul_wall q a b wall_positive
  constructor
  · intro carry_value
    have numerator_value := mul_hasValue carry_value denominator_value
    rw [cleared] at numerator_value
    simpa [add_comm] using numerator_value
  · intro numerator_value
    have quotient_value := div_hasValue numerator_value denominator_value
    have carry_eq :
        lengthThreeFallingTargetCarry q (2 * a) (2 * b + 1) 1 =
          lengthThreeFallingOneOddWallNumerator q b (a + b) /
            ((2 / 3 : ℚ) * (1 - (2 / 3 : ℚ) ^ (2 * (a + b)))) :=
      (eq_div_iff denominator_value.1).2 cleared
    rw [carry_eq]
    simpa using quotient_value

/-- At a fixed odd `k=1` wall, shifting the split coordinate has exactly the expected
state-dependent valuation. -/
theorem lengthThreeFallingOneOddWallNumerator_add_sub_hasValue
    (q m wall : ℕ) {shift : ℕ} (shift_positive : 0 < shift) :
    HasValue 5
      (lengthThreeFallingOneOddWallNumerator q (m + shift) wall -
        lengthThreeFallingOneOddWallNumerator q m wall)
      (shellSlopeGapFiveDepth (2 * shift)) := by
  have coefficient_unit :
      IsUnit 5
        (9 * (2 / 3 : ℚ) ^ (q + 1) * (2 / 3 : ℚ) ^ (2 * m)) := by
    have nine_unit : IsUnit 5 (9 : ℚ) :=
      intCast_isUnit_of_not_dvd (by norm_num)
    exact mul_hasValue
      (mul_hasValue nine_unit
        (fallingCentered_unit_pow fallingCentered_shellRatio_unit (q + 1)))
      (fallingCentered_unit_pow fallingCentered_shellRatio_unit (2 * m))
  have shift_value := shellRatio_pow_sub_one_hasValue
    (show 0 < 2 * shift by omega)
  have product_value := mul_hasValue coefficient_unit shift_value
  convert product_value using 1
  · rw [lengthThreeFallingOneOddWallNumerator,
      lengthThreeFallingOneOddWallNumerator,
      show 2 * (m + shift) = 2 * m + 2 * shift by omega, pow_add]
    ring
  · ring

/-- Depth-two target carry on an odd `k=1` wall forces the fixed residual to sit exactly one
level below that wall. -/
theorem lengthThreeFalling_one_odd_targetCarry_forces_residualDepth
    (q a b : ℕ) (wall_positive : 0 < a + b)
    (carry_value :
      HasValue 5
        (lengthThreeFallingTargetCarry q (2 * a) (2 * b + 1) 1) 2) :
    HasValue 5 (lengthThreeFallingOneOddWallResidual q a)
      ((shellSlopeGapFiveDepth (2 * (a + b)) : ℤ) + 1) := by
  have source_scale_unit : IsUnit 5 ((2 / 3 : ℚ) ^ (2 * a)) :=
    fallingCentered_unit_pow fallingCentered_shellRatio_unit (2 * a)
  have wall_power_unit : IsUnit 5 ((2 / 3 : ℚ) ^ (2 * (a + b))) :=
    fallingCentered_unit_pow fallingCentered_shellRatio_unit (2 * (a + b))
  have wall_value :
      HasValue 5 (1 - (2 / 3 : ℚ) ^ (2 * (a + b)))
        (shellSlopeGapFiveDepth (2 * (a + b))) :=
    fallingCentered_one_sub_shellRatio_pow_hasValue (by omega)
  have denominator_value :
      HasValue 5
        ((2 / 3 : ℚ) * (1 - (2 / 3 : ℚ) ^ (2 * (a + b))))
        (shellSlopeGapFiveDepth (2 * (a + b))) := by
    simpa using mul_hasValue fallingCentered_shellRatio_unit wall_value
  have scaled_carry_value :
      HasValue 5
        ((2 / 3 : ℚ) ^ (2 * a) *
          lengthThreeFallingTargetCarry q (2 * a) (2 * b + 1) 1) 2 := by
    simpa using mul_hasValue source_scale_unit carry_value
  have cleared_value :
      HasValue 5
        (((2 / 3 : ℚ) ^ (2 * a) *
            lengthThreeFallingTargetCarry q (2 * a) (2 * b + 1) 1) *
          ((2 / 3 : ℚ) * (1 - (2 / 3 : ℚ) ^ (2 * (a + b)))))
        ((shellSlopeGapFiveDepth (2 * (a + b)) : ℤ) + 2) := by
    simpa [add_comm] using mul_hasValue scaled_carry_value denominator_value
  have source_scale_baseline :
      HasValue 5 (15 * (2 / 3 : ℚ) ^ (2 * a)) 1 := by
    simpa using mul_hasValue fallingCentered_fifteen_hasValue source_scale_unit
  have coefficient_scaled_value :
      HasValue 5
        ((2 / 3 : ℚ) ^ (2 * (a + b)) *
          lengthThreeFallingOneOddWallCoefficient q a) 1 := by
    have difference_value := add_hasValue_right cleared_value
      (neg_hasValue source_scale_baseline) (by omega)
    have difference_eq :
        (((2 / 3 : ℚ) ^ (2 * a) *
              lengthThreeFallingTargetCarry q (2 * a) (2 * b + 1) 1) *
            ((2 / 3 : ℚ) * (1 - (2 / 3 : ℚ) ^ (2 * (a + b))))) +
            -(15 * (2 / 3 : ℚ) ^ (2 * a)) =
          (2 / 3 : ℚ) ^ (2 * (a + b)) *
            lengthThreeFallingOneOddWallCoefficient q a := by
      rw [lengthThreeFalling_one_odd_targetCarry_cleared q a b wall_positive]
      ring
    rwa [difference_eq] at difference_value
  have coefficient_value :
      HasValue 5 (lengthThreeFallingOneOddWallCoefficient q a) 1 := by
    have quotient_value := div_hasValue coefficient_scaled_value wall_power_unit
    have quotient_eq :
        ((2 / 3 : ℚ) ^ (2 * (a + b)) *
            lengthThreeFallingOneOddWallCoefficient q a) /
            (2 / 3 : ℚ) ^ (2 * (a + b)) =
          lengthThreeFallingOneOddWallCoefficient q a := by
      field_simp [wall_power_unit.1]
    rw [quotient_eq] at quotient_value
    simpa using quotient_value
  have correction_value :
      HasValue 5
        (lengthThreeFallingOneOddWallCoefficient q a *
          (1 - (2 / 3 : ℚ) ^ (2 * (a + b))))
        ((shellSlopeGapFiveDepth (2 * (a + b)) : ℤ) + 1) := by
    simpa [add_comm] using mul_hasValue coefficient_value wall_value
  have residual_eq :
      lengthThreeFallingOneOddWallResidual q a =
        (((2 / 3 : ℚ) ^ (2 * a) *
              lengthThreeFallingTargetCarry q (2 * a) (2 * b + 1) 1) *
            ((2 / 3 : ℚ) * (1 - (2 / 3 : ℚ) ^ (2 * (a + b))))) +
          lengthThreeFallingOneOddWallCoefficient q a *
            (1 - (2 / 3 : ℚ) ^ (2 * (a + b))) := by
    rw [lengthThreeFalling_one_odd_targetCarry_cleared q a b wall_positive,
      lengthThreeFallingOneOddWallResidual]
    ring
  rw [residual_eq]
  exact add_hasValue_right cleared_value correction_value (by omega)

/-- An accepted `k=1`, odd-`B` target forces the centered residual-depth match. -/
theorem lengthThreeFalling_one_odd_target_forces_residualDepth
    (q t a b : ℕ) (wall_positive : 0 < a + b)
    (target_unit :
      IsUnit 5 (lengthThreeFallingTarget q t (2 * a) (2 * b + 1) 1)) :
    HasValue 5 (lengthThreeFallingOneOddWallResidual q a)
      ((shellSlopeGapFiveDepth (2 * (a + b)) : ℤ) + 1) := by
  rw [lengthThreeFallingTarget_eq_terminalCarryTarget] at target_unit
  have carry_value := terminalCarryTarget_fiveUnit_forces_carry (t + 1) target_unit
  exact lengthThreeFalling_one_odd_targetCarry_forces_residualDepth
    q a b wall_positive carry_value

/-- Exact centered quotient in the `k=2`, even-`B` branch. -/
theorem lengthThreeFalling_two_even_targetCarry_centered
    (a b : ℕ) (wall_positive : 0 < a + b) :
    (2 / 3 : ℚ) ^ (2 * a) *
        lengthThreeFallingTargetCarry 0 (2 * a) (2 * (b + 1)) 2 =
      lengthThreeFallingTwoEvenWallResidual a /
          ((2 / 3 : ℚ) ^ 2 * (1 - (2 / 3 : ℚ) ^ (2 * (a + b)))) -
        lengthThreeFallingTwoEvenWallCoefficient a := by
  have base_ne : (2 / 3 : ℚ) ≠ 0 := by norm_num
  have wall_power_lt : (2 / 3 : ℚ) ^ (2 * (a + b)) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have wall_ne : 1 - (2 / 3 : ℚ) ^ (2 * (a + b)) ≠ 0 := by
    linarith
  have wall_product_ne :
      1 - (2 / 3 : ℚ) ^ (2 * a) * (2 / 3 : ℚ) ^ (2 * b) ≠ 0 := by
    rw [← pow_add, show 2 * a + 2 * b = 2 * (a + b) by omega]
    exact wall_ne
  rw [lengthThreeFallingTargetCarry, lengthThreeFallingSourceCarry,
    lengthThreeFallingGainGap, lengthThreeFallingTwoEvenWallResidual,
    lengthThreeFallingTwoEvenWallCoefficient]
  simp only [pow_zero]
  rw [show 2 * a + 2 * (b + 1) = 2 + (2 * a + 2 * b) by omega,
    show 2 * (b + 1) = 2 + 2 * b by omega,
    show 2 * (a + b) = 2 * a + 2 * b by omega]
  simp only [pow_add]
  field_simp [base_ne, wall_product_ne]
  ring

/-- Cleared centered numerator in the `k=2`, even-`B` branch. -/
theorem lengthThreeFalling_two_even_targetCarry_cleared
    (a b : ℕ) (wall_positive : 0 < a + b) :
    ((2 / 3 : ℚ) ^ (2 * a) *
          lengthThreeFallingTargetCarry 0 (2 * a) (2 * (b + 1)) 2) *
        ((2 / 3 : ℚ) ^ 2 * (1 - (2 / 3 : ℚ) ^ (2 * (a + b)))) =
      15 * (2 / 3 : ℚ) ^ (2 * a) +
        (2 / 3 : ℚ) ^ (2 * (a + b + 1)) *
          lengthThreeFallingTwoEvenWallCoefficient a := by
  have wall_power_lt : (2 / 3 : ℚ) ^ (2 * (a + b)) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have wall_ne : 1 - (2 / 3 : ℚ) ^ (2 * (a + b)) ≠ 0 := by
    linarith
  rw [lengthThreeFalling_two_even_targetCarry_centered a b wall_positive,
    lengthThreeFallingTwoEvenWallResidual]
  field_simp [wall_ne]
  rw [show 2 * (a + b + 1) = 2 + 2 * (a + b) by omega, pow_add]
  ring

/-- The centered `k=2` quotient clears to the fixed-wall numerator. -/
theorem lengthThreeFalling_two_even_targetCarry_mul_wall
    (a b : ℕ) (wall_positive : 0 < a + b) :
    lengthThreeFallingTargetCarry 0 (2 * a) (2 * (b + 1)) 2 *
        ((2 / 3 : ℚ) ^ 2 * (1 - (2 / 3 : ℚ) ^ (2 * (a + b)))) =
      lengthThreeFallingTwoEvenWallNumerator (b + 1) (a + b + 1) := by
  have source_scale_ne : (2 / 3 : ℚ) ^ (2 * a) ≠ 0 := by positivity
  have cleared :=
    lengthThreeFalling_two_even_targetCarry_cleared a b wall_positive
  rw [lengthThreeFallingTwoEvenWallCoefficient] at cleared
  rw [lengthThreeFallingTwoEvenWallNumerator]
  rw [show 2 * (a + b + 1) = 2 * a + 2 * (b + 1) by omega,
    pow_add] at cleared ⊢
  field_simp [source_scale_ne] at cleared ⊢
  nlinarith

/-- Depth two of the even `k=2` carry is exactly depth two above its moving-wall numerator. -/
theorem lengthThreeFalling_two_even_targetCarry_hasValue_two_iff_numerator
    (a b : ℕ) (wall_positive : 0 < a + b) :
    HasValue 5
        (lengthThreeFallingTargetCarry 0 (2 * a) (2 * (b + 1)) 2) 2 ↔
      HasValue 5 (lengthThreeFallingTwoEvenWallNumerator (b + 1) (a + b + 1))
        ((shellSlopeGapFiveDepth (2 * (a + b)) : ℤ) + 2) := by
  have square_ratio_unit : IsUnit 5 ((2 / 3 : ℚ) ^ 2) :=
    fallingCentered_unit_pow fallingCentered_shellRatio_unit 2
  have wall_value :
      HasValue 5 (1 - (2 / 3 : ℚ) ^ (2 * (a + b)))
        (shellSlopeGapFiveDepth (2 * (a + b))) :=
    fallingCentered_one_sub_shellRatio_pow_hasValue (by omega)
  have denominator_value :
      HasValue 5
        ((2 / 3 : ℚ) ^ 2 * (1 - (2 / 3 : ℚ) ^ (2 * (a + b))))
        (shellSlopeGapFiveDepth (2 * (a + b))) := by
    simpa using mul_hasValue square_ratio_unit wall_value
  have cleared :=
    lengthThreeFalling_two_even_targetCarry_mul_wall a b wall_positive
  constructor
  · intro carry_value
    have numerator_value := mul_hasValue carry_value denominator_value
    rw [cleared] at numerator_value
    simpa [add_comm] using numerator_value
  · intro numerator_value
    have quotient_value := div_hasValue numerator_value denominator_value
    have carry_eq :
        lengthThreeFallingTargetCarry 0 (2 * a) (2 * (b + 1)) 2 =
          lengthThreeFallingTwoEvenWallNumerator (b + 1) (a + b + 1) /
            ((2 / 3 : ℚ) ^ 2 * (1 - (2 / 3 : ℚ) ^ (2 * (a + b)))) :=
      (eq_div_iff denominator_value.1).2 cleared
    rw [carry_eq]
    simpa using quotient_value

/-- At a fixed even `k=2` wall, shifting the split coordinate has exactly the expected
state-dependent valuation. -/
theorem lengthThreeFallingTwoEvenWallNumerator_add_sub_hasValue
    (b wall : ℕ) {shift : ℕ} (shift_positive : 0 < shift) :
    HasValue 5
      (lengthThreeFallingTwoEvenWallNumerator (b + shift) wall -
        lengthThreeFallingTwoEvenWallNumerator b wall)
      (shellSlopeGapFiveDepth (2 * shift)) := by
  have coefficient_unit :
      IsUnit 5 (9 * (2 / 3 : ℚ) ^ (2 * b)) := by
    have nine_unit : IsUnit 5 (9 : ℚ) :=
      intCast_isUnit_of_not_dvd (by norm_num)
    exact mul_hasValue nine_unit
      (fallingCentered_unit_pow fallingCentered_shellRatio_unit (2 * b))
  have shift_value := shellRatio_pow_sub_one_hasValue
    (show 0 < 2 * shift by omega)
  have product_value := mul_hasValue coefficient_unit shift_value
  convert product_value using 1
  · rw [lengthThreeFallingTwoEvenWallNumerator,
      lengthThreeFallingTwoEvenWallNumerator,
      show 2 * (b + shift) = 2 * b + 2 * shift by omega, pow_add]
    ring
  · ring

/-- Depth-two target carry on an even `k=2` wall forces the fixed residual to sit exactly one
level below that wall. -/
theorem lengthThreeFalling_two_even_targetCarry_forces_residualDepth
    (a b : ℕ) (wall_positive : 0 < a + b)
    (carry_value :
      HasValue 5
        (lengthThreeFallingTargetCarry 0 (2 * a) (2 * (b + 1)) 2) 2) :
    HasValue 5 (lengthThreeFallingTwoEvenWallResidual a)
      ((shellSlopeGapFiveDepth (2 * (a + b)) : ℤ) + 1) := by
  have source_scale_unit : IsUnit 5 ((2 / 3 : ℚ) ^ (2 * a)) :=
    fallingCentered_unit_pow fallingCentered_shellRatio_unit (2 * a)
  have wall_power_unit : IsUnit 5 ((2 / 3 : ℚ) ^ (2 * (a + b))) :=
    fallingCentered_unit_pow fallingCentered_shellRatio_unit (2 * (a + b))
  have coefficient_scale_unit :
      IsUnit 5 ((2 / 3 : ℚ) ^ (2 * (a + b + 1))) :=
    fallingCentered_unit_pow fallingCentered_shellRatio_unit (2 * (a + b + 1))
  have square_ratio_unit : IsUnit 5 ((2 / 3 : ℚ) ^ 2) :=
    fallingCentered_unit_pow fallingCentered_shellRatio_unit 2
  have wall_value :
      HasValue 5 (1 - (2 / 3 : ℚ) ^ (2 * (a + b)))
        (shellSlopeGapFiveDepth (2 * (a + b))) :=
    fallingCentered_one_sub_shellRatio_pow_hasValue (by omega)
  have denominator_value :
      HasValue 5
        ((2 / 3 : ℚ) ^ 2 * (1 - (2 / 3 : ℚ) ^ (2 * (a + b))))
        (shellSlopeGapFiveDepth (2 * (a + b))) := by
    simpa using mul_hasValue square_ratio_unit wall_value
  have scaled_carry_value :
      HasValue 5
        ((2 / 3 : ℚ) ^ (2 * a) *
          lengthThreeFallingTargetCarry 0 (2 * a) (2 * (b + 1)) 2) 2 := by
    simpa using mul_hasValue source_scale_unit carry_value
  have cleared_value :
      HasValue 5
        (((2 / 3 : ℚ) ^ (2 * a) *
            lengthThreeFallingTargetCarry 0 (2 * a) (2 * (b + 1)) 2) *
          ((2 / 3 : ℚ) ^ 2 * (1 - (2 / 3 : ℚ) ^ (2 * (a + b)))))
        ((shellSlopeGapFiveDepth (2 * (a + b)) : ℤ) + 2) := by
    simpa [add_comm] using mul_hasValue scaled_carry_value denominator_value
  have source_scale_baseline :
      HasValue 5 (15 * (2 / 3 : ℚ) ^ (2 * a)) 1 := by
    simpa using mul_hasValue fallingCentered_fifteen_hasValue source_scale_unit
  have coefficient_scaled_value :
      HasValue 5
        ((2 / 3 : ℚ) ^ (2 * (a + b + 1)) *
          lengthThreeFallingTwoEvenWallCoefficient a) 1 := by
    have difference_value := add_hasValue_right cleared_value
      (neg_hasValue source_scale_baseline) (by omega)
    have difference_eq :
        (((2 / 3 : ℚ) ^ (2 * a) *
              lengthThreeFallingTargetCarry 0 (2 * a) (2 * (b + 1)) 2) *
            ((2 / 3 : ℚ) ^ 2 * (1 - (2 / 3 : ℚ) ^ (2 * (a + b))))) +
            -(15 * (2 / 3 : ℚ) ^ (2 * a)) =
          (2 / 3 : ℚ) ^ (2 * (a + b + 1)) *
            lengthThreeFallingTwoEvenWallCoefficient a := by
      rw [lengthThreeFalling_two_even_targetCarry_cleared a b wall_positive]
      ring
    rwa [difference_eq] at difference_value
  have coefficient_value :
      HasValue 5 (lengthThreeFallingTwoEvenWallCoefficient a) 1 := by
    have quotient_value := div_hasValue coefficient_scaled_value coefficient_scale_unit
    have quotient_eq :
        ((2 / 3 : ℚ) ^ (2 * (a + b + 1)) *
            lengthThreeFallingTwoEvenWallCoefficient a) /
            (2 / 3 : ℚ) ^ (2 * (a + b + 1)) =
          lengthThreeFallingTwoEvenWallCoefficient a := by
      field_simp [coefficient_scale_unit.1]
    rw [quotient_eq] at quotient_value
    simpa using quotient_value
  have correction_value :
      HasValue 5
        ((2 / 3 : ℚ) ^ 2 * lengthThreeFallingTwoEvenWallCoefficient a *
          (1 - (2 / 3 : ℚ) ^ (2 * (a + b))))
        ((shellSlopeGapFiveDepth (2 * (a + b)) : ℤ) + 1) := by
    have scaled_coefficient_value := mul_hasValue square_ratio_unit coefficient_value
    simpa [add_comm, add_left_comm] using
      mul_hasValue scaled_coefficient_value wall_value
  have residual_eq :
      lengthThreeFallingTwoEvenWallResidual a =
        (((2 / 3 : ℚ) ^ (2 * a) *
              lengthThreeFallingTargetCarry 0 (2 * a) (2 * (b + 1)) 2) *
            ((2 / 3 : ℚ) ^ 2 * (1 - (2 / 3 : ℚ) ^ (2 * (a + b))))) +
          (2 / 3 : ℚ) ^ 2 * lengthThreeFallingTwoEvenWallCoefficient a *
            (1 - (2 / 3 : ℚ) ^ (2 * (a + b))) := by
    rw [lengthThreeFalling_two_even_targetCarry_cleared a b wall_positive,
      lengthThreeFallingTwoEvenWallResidual,
      show 2 * (a + b + 1) = 2 + 2 * (a + b) by omega, pow_add]
    ring
  rw [residual_eq]
  exact add_hasValue_right cleared_value correction_value (by omega)

/-- An accepted `k=2`, even-`B` target forces the centered residual-depth match. -/
theorem lengthThreeFalling_two_even_target_forces_residualDepth
    (t a b : ℕ) (wall_positive : 0 < a + b)
    (target_unit :
      IsUnit 5 (lengthThreeFallingTarget 0 t (2 * a) (2 * (b + 1)) 2)) :
    HasValue 5 (lengthThreeFallingTwoEvenWallResidual a)
      ((shellSlopeGapFiveDepth (2 * (a + b)) : ℤ) + 1) := by
  rw [lengthThreeFallingTarget_eq_terminalCarryTarget] at target_unit
  have carry_value := terminalCarryTarget_fiveUnit_forces_carry (t + 2) target_unit
  exact lengthThreeFalling_two_even_targetCarry_forces_residualDepth
    a b wall_positive carry_value

end MatrixMortality.MixedPrimeDebt
