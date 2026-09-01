import MatrixMortality.MixedPrimeRealTrapCentralizer

/-!
# Universal depth-two terminal carry

Every surviving length-three shell chamber reaches a terminal coordinate of the form

```text
T(wait,E)=(25+(2/3)^wait E)/125.
```

The target guard forces `v₅(E)=2`. On that fibre, a positive wait shift `s` changes the
target at exact value `κ(s)-1`; acceptance is ten-periodic, and every positive odd shift from
an accepted wait is rejected at value minus one. These facts belong to the coordinate itself,
independently of a chamber's source equation.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation
open PeriodicShell

private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Universal terminal coordinate for a length-three carry. -/
def terminalCarryTarget (wait : ℕ) (carry : ℚ) : ℚ :=
  (25 + (2 / 3 : ℚ) ^ wait * carry) / 125

private theorem terminalCarry_unit_pow
    {value : ℚ} (value_unit : IsUnit 5 value) (exponent : ℕ) :
    IsUnit 5 (value ^ exponent) := by
  refine ⟨pow_ne_zero exponent value_unit.1, ?_⟩
  rw [padicValRat.pow, value_unit.2]
  simp

private theorem terminalCarry_ratio_power_unit (exponent : ℕ) :
    IsUnit 5 ((2 / 3 : ℚ) ^ exponent) := by
  have two_unit : IsUnit 5 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have three_unit : IsUnit 5 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  exact terminalCarry_unit_pow (div_hasValue two_unit three_unit) exponent

/-- Changing only the carry shifts the terminal coordinate three five-adic levels downward. -/
theorem terminalCarryTarget_carry_sub_hasValue
    (wait : ℕ) {later earlier : ℚ} {value : ℤ}
    (carry_sub_value : HasValue 5 (later - earlier) value) :
    HasValue 5
      (terminalCarryTarget wait later - terminalCarryTarget wait earlier)
      (value - 3) := by
  have power_unit := terminalCarry_ratio_power_unit wait
  have denominator_value : HasValue 5 (125 : ℚ) 3 := by
    convert primePower_hasValue (prime := 5) 3 using 1 <;> norm_num
  have difference_eq :
      terminalCarryTarget wait later - terminalCarryTarget wait earlier =
        ((2 / 3 : ℚ) ^ wait * (later - earlier)) / 125 := by
    rw [terminalCarryTarget, terminalCarryTarget]
    ring
  rw [difference_eq]
  have numerator_value := mul_hasValue power_unit carry_sub_value
  convert div_hasValue numerator_value denominator_value using 1
  ring

/-- A carry perturbation of value at least four preserves terminal acceptance. -/
theorem terminalCarryTarget_carry_sub_fiveUnit_iff
    (wait : ℕ) {later earlier : ℚ} {value : ℤ} (four_le : 4 ≤ value)
    (carry_sub_value : HasValue 5 (later - earlier) value) :
    IsUnit 5 (terminalCarryTarget wait later) ↔
      IsUnit 5 (terminalCarryTarget wait earlier) := by
  have target_sub_value :=
    terminalCarryTarget_carry_sub_hasValue wait carry_sub_value
  have target_sub_positive :
      IsPositive 5
        (terminalCarryTarget wait later - terminalCarryTarget wait earlier) :=
    ⟨target_sub_value.1, by rw [target_sub_value.2]; omega⟩
  have reverse_value := neg_hasValue target_sub_value
  have reverse_positive :
      IsPositive 5
        (terminalCarryTarget wait earlier - terminalCarryTarget wait later) := by
    convert (show IsPositive 5
      (-(terminalCarryTarget wait later - terminalCarryTarget wait earlier)) from
        ⟨reverse_value.1, by rw [reverse_value.2]; omega⟩) using 1
    ring
  constructor
  · intro later_unit
    have earlier_unit := unit_add_positive later_unit reverse_positive
    convert earlier_unit using 1
    ring
  · intro earlier_unit
    have later_unit := unit_add_positive earlier_unit target_sub_positive
    convert later_unit using 1
    ring

/-- Target acceptance is exact depth three of the universal terminal numerator. -/
theorem terminalCarryTarget_fiveUnit_iff_numerator
    (wait : ℕ) (carry : ℚ) :
    IsUnit 5 (terminalCarryTarget wait carry) ↔
      HasValue 5 (25 + (2 / 3 : ℚ) ^ wait * carry) 3 := by
  have denominator_value : HasValue 5 (125 : ℚ) 3 := by
    convert primePower_hasValue (prime := 5) 3 using 1 <;> norm_num
  rw [terminalCarryTarget]
  constructor
  · intro target_unit
    have numerator_value := mul_hasValue target_unit denominator_value
    have numerator_eq :
        (25 + (2 / 3 : ℚ) ^ wait * carry) / 125 * 125 =
          25 + (2 / 3 : ℚ) ^ wait * carry :=
      div_mul_cancel₀ _ denominator_value.1
    rwa [numerator_eq] at numerator_value
  · intro numerator_value
    exact div_hasValue numerator_value denominator_value

/-- A terminal unit forces the incoming carry to have exact depth two. -/
theorem terminalCarryTarget_fiveUnit_forces_carry
    (wait : ℕ) {carry : ℚ}
    (target_unit : IsUnit 5 (terminalCarryTarget wait carry)) :
    HasValue 5 carry 2 := by
  have twentyFive_value : HasValue 5 (25 : ℚ) 2 := by
    convert primePower_hasValue (prime := 5) 2 using 1 <;> norm_num
  have numerator_value :=
    (terminalCarryTarget_fiveUnit_iff_numerator wait carry).1 target_unit
  have power_unit := terminalCarry_ratio_power_unit wait
  by_cases carry_zero : carry = 0
  · rw [carry_zero, mul_zero, add_zero] at numerator_value
    have impossible : (2 : ℤ) = 3 := by
      rw [← twentyFive_value.2, numerator_value.2]
    omega
  · let carryValue := padicValRat 5 carry
    have carry_value : HasValue 5 carry carryValue := ⟨carry_zero, rfl⟩
    have scaled_value :
        HasValue 5 ((2 / 3 : ℚ) ^ wait * carry) carryValue := by
      simpa only [zero_add] using mul_hasValue power_unit carry_value
    rcases lt_trichotomy (2 : ℤ) carryValue with lower | equal | higher
    · have surviving := add_hasValue_left twentyFive_value scaled_value lower
      have impossible : (2 : ℤ) = 3 := by
        rw [← surviving.2, numerator_value.2]
      omega
    · convert carry_value using 1
    · have surviving := add_hasValue_right twentyFive_value scaled_value higher
      have impossible : carryValue = 3 := by
        rw [← surviving.2, numerator_value.2]
      omega

/-- A positive terminal-wait shift changes the target by the shift's parity/LTE depth minus
one. -/
theorem terminalCarryTarget_add_sub_hasValue
    (wait : ℕ) {carry : ℚ} {shift : ℕ} (shift_positive : 0 < shift)
    (carry_value : HasValue 5 carry 2) :
    HasValue 5
      (terminalCarryTarget (wait + shift) carry - terminalCarryTarget wait carry)
      ((shellSlopeGapFiveDepth shift : ℤ) - 1) := by
  have shift_value := shellRatio_pow_sub_one_hasValue shift_positive
  have power_unit := terminalCarry_ratio_power_unit wait
  have denominator_value : HasValue 5 (125 : ℚ) 3 := by
    convert primePower_hasValue (prime := 5) 3 using 1 <;> norm_num
  have difference_eq :
      terminalCarryTarget (wait + shift) carry - terminalCarryTarget wait carry =
        ((2 / 3 : ℚ) ^ wait * ((2 / 3 : ℚ) ^ shift - 1) * carry) / 125 := by
    rw [terminalCarryTarget, terminalCarryTarget, pow_add]
    ring
  rw [difference_eq]
  have numerator_value :=
    mul_hasValue (mul_hasValue power_unit shift_value) carry_value
  have difference_value := div_hasValue numerator_value denominator_value
  convert difference_value using 1
  ring

/-- Under the forced depth-two carry, terminal acceptance is ten-periodic. -/
theorem terminalCarryTarget_fiveUnit_add_ten_iff
    (wait : ℕ) {carry : ℚ} (carry_value : HasValue 5 carry 2) :
    IsUnit 5 (terminalCarryTarget (wait + 10) carry) ↔
      IsUnit 5 (terminalCarryTarget wait carry) := by
  have difference_value := terminalCarryTarget_add_sub_hasValue
    wait (show 0 < 10 by norm_num) carry_value
  have ten_depth : shellSlopeGapFiveDepth 10 = 2 := by
    rw [shellSlopeGapFiveDepth, if_neg (by norm_num : ¬Odd 10)]
    norm_num [padicValNat_self]
  rw [ten_depth] at difference_value
  norm_num at difference_value
  have forward_positive :
      IsPositive 5
        (terminalCarryTarget (wait + 10) carry - terminalCarryTarget wait carry) :=
    ⟨difference_value.1, by rw [difference_value.2]; norm_num⟩
  have reverse_value := neg_hasValue difference_value
  have reverse_positive :
      IsPositive 5
        (terminalCarryTarget wait carry - terminalCarryTarget (wait + 10) carry) := by
    convert (show IsPositive 5
      (-(terminalCarryTarget (wait + 10) carry - terminalCarryTarget wait carry)) from
        ⟨reverse_value.1, by rw [reverse_value.2]; norm_num⟩) using 1
    ring
  constructor
  · intro later_unit
    have earlier_unit := unit_add_positive later_unit reverse_positive
    convert earlier_unit using 1
    ring
  · intro earlier_unit
    have later_unit := unit_add_positive earlier_unit forward_positive
    convert later_unit using 1
    ring

/-- Ten literal waits classify every terminal target on a depth-two carry fibre. -/
theorem terminalCarryTarget_fiveUnit_iff_mod_ten
    (wait : ℕ) {carry : ℚ} (carry_value : HasValue 5 carry 2) :
    IsUnit 5 (terminalCarryTarget wait carry) ↔
      IsUnit 5 (terminalCarryTarget (wait % 10) carry) := by
  have periodic (base repetitions : ℕ) :
      IsUnit 5 (terminalCarryTarget (base + 10 * repetitions) carry) ↔
        IsUnit 5 (terminalCarryTarget base carry) := by
    induction repetitions with
    | zero => simp
    | succ repetitions induction =>
        rw [Nat.mul_succ, ← Nat.add_assoc,
          terminalCarryTarget_fiveUnit_add_ten_iff
            (base + 10 * repetitions) carry_value]
        exact induction
  have decomposition : wait % 10 + 10 * (wait / 10) = wait := by omega
  have reduced := periodic (wait % 10) (wait / 10)
  rwa [decomposition] at reduced

/-- From an accepted wait, every positive odd terminal shift lands at value minus one. -/
theorem terminalCarryTarget_oddShift_hasValue_negOne
    (wait : ℕ) {carry : ℚ} {shift : ℕ} (shift_positive : 0 < shift)
    (shift_odd : Odd shift)
    (target_unit : IsUnit 5 (terminalCarryTarget wait carry)) :
    HasValue 5 (terminalCarryTarget (wait + shift) carry) (-1) := by
  have carry_value :=
    terminalCarryTarget_fiveUnit_forces_carry wait target_unit
  have difference_value := terminalCarryTarget_add_sub_hasValue
    wait shift_positive carry_value
  have shift_depth : shellSlopeGapFiveDepth shift = 0 := by
    rw [shellSlopeGapFiveDepth, if_pos shift_odd]
  rw [shift_depth] at difference_value
  norm_num at difference_value
  have shifted_value := add_hasValue_left difference_value target_unit (by norm_num)
  convert shifted_value using 1
  ring

end MatrixMortality.MixedPrimeDebt
