import Mathlib.Tactic.NormNum.Prime
import MatrixMortality.CubicContinuantMismatchClock
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Self-balancing cleanup for the cubic continuant comparator

The split endpoint bridge rejects both too few and too many cleanup readers. The obstruction is
an exact parity clash: a forward clock gap has odd `5`-adic valuation, while a reverse gap has
odd `2`-adic valuation, but every nonzero signed mismatch radix has even valuation at both
primes.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Common diagonal ratio of the normalized cubic mismatch clock. -/
abbrev continuantMismatchClockRatio : ℚ := 4 / 25

/-- The true radix writer normalized to lower-right entry one. -/
def continuantMismatchClock : Square (Fin 2) ℚ :=
  (25 : ℚ)⁻¹ • continuantRadixGenerator true

/-- The exact inverse of the normalized cubic mismatch clock. -/
def continuantMismatchClockReader : Square (Fin 2) ℚ :=
  continuantRadixReader true

/-- Every digit belongs to the signed binary error alphabet. -/
def ContinuantMismatchDigits (digits : List ℤ) : Prop :=
  ∀ digit ∈ digits, digit = -1 ∨ digit = 0 ∨ digit = 1

private theorem val2_two : padicValRat 2 (2 : ℚ) = 1 :=
  padicValRat.self (by norm_num)

private theorem val2_odd (n : ℕ) (odd : ¬2 ∣ n) :
    padicValRat 2 (n : ℚ) = 0 := by
  rw [padicValRat.of_nat]
  exact_mod_cast padicValNat.eq_zero_of_not_dvd odd

private theorem val5_five : padicValRat 5 (5 : ℚ) = 1 :=
  padicValRat.self (by norm_num)

private theorem val5_unit (n : ℕ) (unit : ¬5 ∣ n) :
    padicValRat 5 (n : ℚ) = 0 := by
  rw [padicValRat.of_nat]
  exact_mod_cast padicValNat.eq_zero_of_not_dvd unit

private theorem mismatchClockRatio_val_two :
    padicValRat 2 continuantMismatchClockRatio = 2 := by
  have val2_five : padicValRat 2 (5 : ℚ) = 0 := by
    simpa using val2_odd 5 (by norm_num)
  rw [continuantMismatchClockRatio, show (4 : ℚ) = 2 ^ 2 by norm_num,
    show (25 : ℚ) = 5 ^ 2 by norm_num,
    padicValRat.div (by norm_num) (by norm_num), padicValRat.pow,
    padicValRat.pow, val2_two, val2_five]
  norm_num

private theorem mismatchClockRatio_val_five :
    padicValRat 5 continuantMismatchClockRatio = -2 := by
  have val5_two : padicValRat 5 (2 : ℚ) = 0 := by
    simpa using val5_unit 2 (by norm_num)
  rw [continuantMismatchClockRatio, show (4 : ℚ) = 2 ^ 2 by norm_num,
    show (25 : ℚ) = 5 ^ 2 by norm_num,
    padicValRat.div (by norm_num) (by norm_num), padicValRat.pow,
    padicValRat.pow, val5_two, val5_five]
  norm_num

private theorem digit_val_two {digit : ℤ}
    (range : digit = -1 ∨ digit = 0 ∨ digit = 1) (nonzero : (digit : ℚ) ≠ 0) :
    padicValRat 2 (digit : ℚ) = 0 := by
  rcases range with rfl | rfl | rfl <;> simp

private theorem digit_val_five {digit : ℤ}
    (range : digit = -1 ∨ digit = 0 ∨ digit = 1) (nonzero : (digit : ℚ) ≠ 0) :
    padicValRat 5 (digit : ℚ) = 0 := by
  rcases range with rfl | rfl | rfl <;> simp

private theorem mismatchRadix_val_two_even {digits : List ℤ}
    (range : ContinuantMismatchDigits digits) (nonzero : continuantMismatchDefect digits ≠ 0) :
    ∃ exponent : ℕ,
      padicValRat 2 (continuantMismatchDefect digits) = 2 * exponent := by
  induction digits with
  | nil => simp [continuantMismatchDefect] at nonzero
  | cons digit digits induction =>
      have head_range := range digit (by simp)
      have tail_range : ContinuantMismatchDigits digits := by
        intro tail membership
        exact range tail (by simp [membership])
      by_cases digit_zero : digit = 0
      · subst digit
        have tail_nonzero : continuantMismatchDefect digits ≠ 0 := by
          intro tail_zero
          apply nonzero
          simp [continuantMismatchDefect, tail_zero]
        obtain ⟨exponent, valuation⟩ := induction tail_range tail_nonzero
        refine ⟨exponent + 1, ?_⟩
        rw [continuantMismatchDefect, Int.cast_zero, zero_add,
          padicValRat.mul (by norm_num [continuantMismatchClockRatio]) tail_nonzero,
          mismatchClockRatio_val_two, valuation]
        push_cast
        ring
      · have digit_nonzero : (digit : ℚ) ≠ 0 := by exact_mod_cast digit_zero
        by_cases tail_zero : continuantMismatchDefect digits = 0
        · rw [continuantMismatchDefect, tail_zero, mul_zero, add_zero,
            digit_val_two head_range digit_nonzero]
          exact ⟨0, by norm_num⟩
        · obtain ⟨exponent, valuation⟩ := induction tail_range tail_zero
          have scaled_nonzero :
              continuantMismatchClockRatio * continuantMismatchDefect digits ≠ 0 :=
            mul_ne_zero (by norm_num [continuantMismatchClockRatio]) tail_zero
          have scaled_val :
              padicValRat 2 (continuantMismatchClockRatio * continuantMismatchDefect digits) =
                2 + 2 * exponent := by
            rw [padicValRat.mul (by norm_num [continuantMismatchClockRatio]) tail_zero,
              mismatchClockRatio_val_two, valuation]
          have digit_val := digit_val_two head_range digit_nonzero
          have strict :
              padicValRat 2 (digit : ℚ) <
                padicValRat 2 (continuantMismatchClockRatio * continuantMismatchDefect digits) := by
            rw [digit_val, scaled_val]
            omega
          refine ⟨0, ?_⟩
          rw [continuantMismatchDefect,
            padicValRat.add_eq_of_lt nonzero digit_nonzero scaled_nonzero strict,
            digit_val]
          norm_num

private theorem mismatchRadix_val_five_even {digits : List ℤ}
    (range : ContinuantMismatchDigits digits) (nonzero : continuantMismatchDefect digits ≠ 0) :
    ∃ exponent : ℕ,
      padicValRat 5 (continuantMismatchDefect digits) = -(2 * exponent) := by
  induction digits with
  | nil => simp [continuantMismatchDefect] at nonzero
  | cons digit digits induction =>
      have head_range := range digit (by simp)
      have tail_range : ContinuantMismatchDigits digits := by
        intro tail membership
        exact range tail (by simp [membership])
      by_cases tail_zero : continuantMismatchDefect digits = 0
      · have digit_nonzero : (digit : ℚ) ≠ 0 := by
          intro digit_cast_zero
          have digit_zero : digit = 0 := by exact_mod_cast digit_cast_zero
          apply nonzero
          simp [continuantMismatchDefect, digit_zero, tail_zero]
        rw [continuantMismatchDefect, tail_zero, mul_zero, add_zero,
          digit_val_five head_range digit_nonzero]
        exact ⟨0, by norm_num⟩
      · obtain ⟨exponent, valuation⟩ := induction tail_range tail_zero
        have scaled_nonzero :
            continuantMismatchClockRatio * continuantMismatchDefect digits ≠ 0 :=
          mul_ne_zero (by norm_num [continuantMismatchClockRatio]) tail_zero
        have scaled_val :
            padicValRat 5 (continuantMismatchClockRatio * continuantMismatchDefect digits) =
              -(2 * (exponent + 1)) := by
          rw [padicValRat.mul (by norm_num [continuantMismatchClockRatio]) tail_zero,
            mismatchClockRatio_val_five, valuation]
          ring
        by_cases digit_zero : digit = 0
        · subst digit
          refine ⟨exponent + 1, ?_⟩
          simpa [continuantMismatchDefect] using scaled_val
        · have digit_nonzero : (digit : ℚ) ≠ 0 := by exact_mod_cast digit_zero
          have digit_val := digit_val_five head_range digit_nonzero
          have strict :
              padicValRat 5 (continuantMismatchClockRatio * continuantMismatchDefect digits) <
                padicValRat 5 (digit : ℚ) := by
            rw [scaled_val, digit_val]
            omega
          have sum_nonzero :
              continuantMismatchClockRatio * continuantMismatchDefect digits + digit ≠ 0 := by
            simpa [continuantMismatchDefect, add_comm] using nonzero
          refine ⟨exponent + 1, ?_⟩
          rw [continuantMismatchDefect, add_comm,
            padicValRat.add_eq_of_lt sum_nonzero
              scaled_nonzero digit_nonzero strict,
            scaled_val]
          push_cast
          ring

/-- An upper affine matrix with explicit ratio and translation. -/
def continuantMismatchAffine (ratio shift : ℚ) : Square (Fin 2) ℚ :=
  !![ratio, shift; 0, 1]

/-- The normalized clocked affine product of a signed mismatch schedule. -/
def continuantMismatchClockProduct : List ℤ → Square (Fin 2) ℚ
  | [] => 1
  | digit :: digits =>
      continuantDefectTranslation (digit * (125 / 48)) *
        continuantMismatchClock * continuantMismatchClockProduct digits

/-- Multiplication of normalized upper affine matrices. -/
theorem continuantMismatchAffine_mul
    (leftRatio leftShift rightRatio rightShift : ℚ) :
    continuantMismatchAffine leftRatio leftShift *
        continuantMismatchAffine rightRatio rightShift =
      continuantMismatchAffine (leftRatio * rightRatio)
        (leftShift + leftRatio * rightShift) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [continuantMismatchAffine, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      ring)

private theorem mismatchTranslation_eq_affine (shift : ℚ) :
    continuantDefectTranslation shift = continuantMismatchAffine 1 shift := rfl

/-- The true radix clock in fixed-point affine coordinates. -/
theorem continuantMismatchClock_eq_affine :
    continuantMismatchClock =
      continuantMismatchAffine continuantMismatchClockRatio
        ((149 / 252) * (1 - continuantMismatchClockRatio)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [continuantMismatchClock, continuantMismatchClockRatio, continuantMismatchAffine,
      continuantRadixGenerator, continuantRadixDigit, Matrix.smul_apply]

/-- The true radix reader in fixed-point affine coordinates. -/
theorem continuantMismatchClockReader_eq_affine :
    continuantMismatchClockReader =
      continuantMismatchAffine continuantMismatchClockRatio⁻¹
        ((149 / 252) * (1 - continuantMismatchClockRatio⁻¹)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [continuantMismatchClockReader, continuantMismatchClockRatio, continuantMismatchAffine,
      continuantRadixReader, continuantRadixDigit]

/-- Exact affine normal form of a complete signed clock schedule. -/
theorem continuantMismatchClockProduct_affine (digits : List ℤ) :
    continuantMismatchClockProduct digits =
      continuantMismatchAffine (continuantMismatchClockRatio ^ digits.length)
        ((149 / 252) * (1 - continuantMismatchClockRatio ^ digits.length) +
          (125 / 48) * continuantMismatchDefect digits) := by
  induction digits with
  | nil =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [continuantMismatchClockProduct, continuantMismatchAffine,
          continuantMismatchDefect, Matrix.one_apply]
  | cons digit digits induction =>
      rw [continuantMismatchClockProduct, mismatchTranslation_eq_affine,
        continuantMismatchClock_eq_affine, induction, continuantMismatchAffine_mul,
        continuantMismatchAffine_mul]
      ext i j
      fin_cases i <;> fin_cases j <;>
        (simp [continuantMismatchAffine, continuantMismatchDefect, List.length_cons, pow_succ,
            continuantMismatchClockRatio] <;>
          ring)

/-- Exact affine normal form of an arbitrary true-reader cleanup run. -/
theorem continuantMismatchClockReader_pow_affine (cleanup : ℕ) :
    continuantMismatchClockReader ^ cleanup =
      continuantMismatchAffine (continuantMismatchClockRatio⁻¹ ^ cleanup)
        ((149 / 252) * (1 - continuantMismatchClockRatio⁻¹ ^ cleanup)) := by
  induction cleanup with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [continuantMismatchAffine, Matrix.one_apply]
  | succ cleanup induction =>
      rw [pow_succ', induction, continuantMismatchClockReader_eq_affine,
        continuantMismatchAffine_mul]
      ext i j
      fin_cases i <;> fin_cases j <;>
        (simp [continuantMismatchAffine, pow_succ] <;>
          ring)

/-- Exact affine normal form of a signed clock schedule followed by arbitrary cleanup. -/
theorem continuantMismatchClockProduct_cleanup_affine
    (digits : List ℤ) (cleanup : ℕ) :
    continuantMismatchClockProduct digits * continuantMismatchClockReader ^ cleanup =
      continuantMismatchAffine
        (continuantMismatchClockRatio ^ digits.length * continuantMismatchClockRatio⁻¹ ^ cleanup)
        ((149 / 252) *
            (1 - continuantMismatchClockRatio ^ digits.length *
              continuantMismatchClockRatio⁻¹ ^ cleanup) +
          (125 / 48) * continuantMismatchDefect digits) := by
  rw [continuantMismatchClockProduct_affine,
    continuantMismatchClockReader_pow_affine,
    continuantMismatchAffine_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [continuantMismatchAffine] <;>
      ring)

/-- Endpoint-balance coefficient forced by the true clock fixed point. -/
def continuantMismatchBalanceConstant : ℚ := 344 / 2625

private theorem mismatchBalanceConstant_val_two :
    padicValRat 2 continuantMismatchBalanceConstant = 3 := by
  have val2_three : padicValRat 2 (3 : ℚ) = 0 := by
    simpa using val2_odd 3 (by norm_num)
  have val2_five : padicValRat 2 (5 : ℚ) = 0 := by
    simpa using val2_odd 5 (by norm_num)
  have val2_seven : padicValRat 2 (7 : ℚ) = 0 := by
    simpa using val2_odd 7 (by norm_num)
  have val2_fortyThree : padicValRat 2 (43 : ℚ) = 0 := by
    simpa using val2_odd 43 (by norm_num)
  rw [continuantMismatchBalanceConstant, show (344 : ℚ) = 2 ^ 3 * 43 by norm_num,
    show (2625 : ℚ) = 3 * 5 ^ 3 * 7 by norm_num,
    padicValRat.div (by norm_num) (by norm_num),
    padicValRat.mul (by norm_num) (by norm_num), padicValRat.pow,
    padicValRat.mul (by norm_num) (by norm_num),
    padicValRat.mul (by norm_num) (by norm_num), padicValRat.pow,
    val2_two, val2_fortyThree, val2_three, val2_five, val2_seven]
  norm_num

private theorem mismatchBalanceConstant_val_five :
    padicValRat 5 continuantMismatchBalanceConstant = -3 := by
  have val5_two : padicValRat 5 (2 : ℚ) = 0 := by
    simpa using val5_unit 2 (by norm_num)
  have val5_three : padicValRat 5 (3 : ℚ) = 0 := by
    simpa using val5_unit 3 (by norm_num)
  have val5_seven : padicValRat 5 (7 : ℚ) = 0 := by
    simpa using val5_unit 7 (by norm_num)
  have val5_fortyThree : padicValRat 5 (43 : ℚ) = 0 := by
    simpa using val5_unit 43 (by norm_num)
  rw [continuantMismatchBalanceConstant, show (344 : ℚ) = 2 ^ 3 * 43 by norm_num,
    show (2625 : ℚ) = 3 * 5 ^ 3 * 7 by norm_num,
    padicValRat.div (by norm_num) (by norm_num),
    padicValRat.mul (by norm_num) (by norm_num), padicValRat.pow,
    padicValRat.mul (by norm_num) (by norm_num),
    padicValRat.mul (by norm_num) (by norm_num), padicValRat.pow,
    val5_two, val5_fortyThree, val5_three, val5_five, val5_seven]
  norm_num

/-- The normalized mismatch-clock ratio is nonzero. -/
theorem continuantMismatchClockRatio_ne_zero : continuantMismatchClockRatio ≠ 0 := by
  norm_num [continuantMismatchClockRatio]

private theorem mismatchClockRatio_pow_ne_one {exponent : ℕ}
    (positive : 0 < exponent) : continuantMismatchClockRatio ^ exponent ≠ 1 := by
  intro power_one
  have valuation_eq := congrArg (padicValRat 5) power_one
  rw [padicValRat.pow, mismatchClockRatio_val_five] at valuation_eq
  simp at valuation_eq
  omega

private theorem mismatchClockRatio_one_sub_pow_val_five {exponent : ℕ}
    (positive : 0 < exponent) :
    padicValRat 5 (1 - continuantMismatchClockRatio ^ exponent) = -(2 * exponent) := by
  have power_nonzero : continuantMismatchClockRatio ^ exponent ≠ 0 :=
    pow_ne_zero _ continuantMismatchClockRatio_ne_zero
  have difference_nonzero : 1 - continuantMismatchClockRatio ^ exponent ≠ 0 := by
    intro difference_zero
    apply mismatchClockRatio_pow_ne_one positive
    linarith
  have power_val :
      padicValRat 5 (-(continuantMismatchClockRatio ^ exponent)) = -(2 * exponent) := by
    rw [padicValRat.neg, padicValRat.pow, mismatchClockRatio_val_five]
    ring
  have strict :
      padicValRat 5 (-(continuantMismatchClockRatio ^ exponent)) <
        padicValRat 5 (1 : ℚ) := by
    rw [power_val]
    simp
    omega
  have sum_nonzero : -(continuantMismatchClockRatio ^ exponent) + 1 ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using difference_nonzero
  have valuation :=
    padicValRat.add_eq_of_lt sum_nonzero (neg_ne_zero.mpr power_nonzero)
      one_ne_zero strict
  rw [power_val] at valuation
  simpa [sub_eq_add_neg, add_comm] using valuation

private theorem mismatchClockRatio_inv_pow_ne_one {exponent : ℕ}
    (positive : 0 < exponent) : continuantMismatchClockRatio⁻¹ ^ exponent ≠ 1 := by
  intro power_one
  have valuation_eq := congrArg (padicValRat 2) power_one
  rw [padicValRat.pow, padicValRat.inv, mismatchClockRatio_val_two] at valuation_eq
  simp at valuation_eq
  omega

private theorem mismatchClockRatio_one_sub_inv_pow_val_two {exponent : ℕ}
    (positive : 0 < exponent) :
    padicValRat 2 (1 - continuantMismatchClockRatio⁻¹ ^ exponent) = -(2 * exponent) := by
  have inverse_nonzero : continuantMismatchClockRatio⁻¹ ≠ 0 :=
    inv_ne_zero continuantMismatchClockRatio_ne_zero
  have power_nonzero : continuantMismatchClockRatio⁻¹ ^ exponent ≠ 0 :=
    pow_ne_zero _ inverse_nonzero
  have difference_nonzero : 1 - continuantMismatchClockRatio⁻¹ ^ exponent ≠ 0 := by
    intro difference_zero
    apply mismatchClockRatio_inv_pow_ne_one positive
    linarith
  have power_val :
      padicValRat 2 (-(continuantMismatchClockRatio⁻¹ ^ exponent)) = -(2 * exponent) := by
    rw [padicValRat.neg, padicValRat.pow, padicValRat.inv,
      mismatchClockRatio_val_two]
    ring
  have strict :
      padicValRat 2 (-(continuantMismatchClockRatio⁻¹ ^ exponent)) <
        padicValRat 2 (1 : ℚ) := by
    rw [power_val]
    simp
    omega
  have sum_nonzero : -(continuantMismatchClockRatio⁻¹ ^ exponent) + 1 ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using difference_nonzero
  have valuation :=
    padicValRat.add_eq_of_lt sum_nonzero (neg_ne_zero.mpr power_nonzero)
      one_ne_zero strict
  rw [power_val] at valuation
  simpa [sub_eq_add_neg, add_comm] using valuation

/-- Cancelling at most as many inverse clocks as forward clocks leaves the exponent gap. -/
theorem continuantMismatchClock_pow_mul_inverse_pow_of_le {count cleanup : ℕ}
    (le : cleanup ≤ count) :
    continuantMismatchClockRatio ^ count * continuantMismatchClockRatio⁻¹ ^ cleanup =
      continuantMismatchClockRatio ^ (count - cleanup) := by
  obtain ⟨remainder, rfl⟩ := Nat.exists_eq_add_of_le le
  rw [Nat.add_sub_cancel_left]
  calc
    continuantMismatchClockRatio ^ (cleanup + remainder) *
          continuantMismatchClockRatio⁻¹ ^ cleanup =
        (continuantMismatchClockRatio ^ cleanup * continuantMismatchClockRatio⁻¹ ^ cleanup) *
          continuantMismatchClockRatio ^ remainder := by
      rw [pow_add]
      ring
    _ = (continuantMismatchClockRatio * continuantMismatchClockRatio⁻¹) ^ cleanup *
          continuantMismatchClockRatio ^ remainder := by
      rw [mul_pow]
    _ = continuantMismatchClockRatio ^ remainder := by
      rw [mul_inv_cancel₀ continuantMismatchClockRatio_ne_zero, one_pow, one_mul]

/-- Cancelling at least as many inverse clocks as forward clocks leaves the inverse exponent
gap. -/
theorem continuantMismatchClock_pow_mul_inverse_pow_of_le_reverse {count cleanup : ℕ}
    (le : count ≤ cleanup) :
    continuantMismatchClockRatio ^ count * continuantMismatchClockRatio⁻¹ ^ cleanup =
      continuantMismatchClockRatio⁻¹ ^ (cleanup - count) := by
  obtain ⟨remainder, rfl⟩ := Nat.exists_eq_add_of_le le
  rw [Nat.add_sub_cancel_left]
  calc
    continuantMismatchClockRatio ^ count *
          continuantMismatchClockRatio⁻¹ ^ (count + remainder) =
        (continuantMismatchClockRatio ^ count * continuantMismatchClockRatio⁻¹ ^ count) *
          continuantMismatchClockRatio⁻¹ ^ remainder := by
      rw [pow_add]
      ring
    _ = (continuantMismatchClockRatio * continuantMismatchClockRatio⁻¹) ^ count *
          continuantMismatchClockRatio⁻¹ ^ remainder := by
      rw [mul_pow]
    _ = continuantMismatchClockRatio⁻¹ ^ remainder := by
      rw [mul_inv_cancel₀ continuantMismatchClockRatio_ne_zero, one_pow, one_mul]

private theorem mismatchBalanceConstant_ne_zero : continuantMismatchBalanceConstant ≠ 0 := by
  norm_num [continuantMismatchBalanceConstant]

private theorem mismatchBalance_forward_val_five {exponent : ℕ}
    (positive : 0 < exponent) :
    padicValRat 5
        (-continuantMismatchBalanceConstant *
          (1 - continuantMismatchClockRatio ^ exponent)) =
      -(2 * exponent + 3) := by
  have difference_nonzero : 1 - continuantMismatchClockRatio ^ exponent ≠ 0 := by
    intro difference_zero
    apply mismatchClockRatio_pow_ne_one positive
    linarith
  rw [padicValRat.mul (neg_ne_zero.mpr mismatchBalanceConstant_ne_zero)
      difference_nonzero,
    padicValRat.neg, mismatchBalanceConstant_val_five,
    mismatchClockRatio_one_sub_pow_val_five positive]
  ring

private theorem mismatchBalance_reverse_val_two {exponent : ℕ}
    (positive : 0 < exponent) :
    padicValRat 2
        (-continuantMismatchBalanceConstant *
          (1 - continuantMismatchClockRatio⁻¹ ^ exponent)) =
      3 - 2 * exponent := by
  have difference_nonzero : 1 - continuantMismatchClockRatio⁻¹ ^ exponent ≠ 0 := by
    intro difference_zero
    apply mismatchClockRatio_inv_pow_ne_one positive
    linarith
  rw [padicValRat.mul (neg_ne_zero.mpr mismatchBalanceConstant_ne_zero)
      difference_nonzero,
    padicValRat.neg, mismatchBalanceConstant_val_two,
    mismatchClockRatio_one_sub_inv_pow_val_two positive]
  ring

/-- The endpoint balance equation forces the exact cleanup count and a zero error schedule. -/
theorem continuantMismatchBalanceEquation_forces (digits : List ℤ) (cleanup : ℕ)
    (range : ContinuantMismatchDigits digits)
    (equation :
      continuantMismatchDefect digits =
        -continuantMismatchBalanceConstant *
          (1 - continuantMismatchClockRatio ^ digits.length *
            continuantMismatchClockRatio⁻¹ ^ cleanup)) :
    cleanup = digits.length ∧ ∀ digit ∈ digits, digit = 0 := by
  rcases lt_trichotomy cleanup digits.length with cleanup_lt | cleanup_eq | count_lt
  · have ratio_eq :
        continuantMismatchClockRatio ^ digits.length * continuantMismatchClockRatio⁻¹ ^ cleanup =
          continuantMismatchClockRatio ^ (digits.length - cleanup) :=
      continuantMismatchClock_pow_mul_inverse_pow_of_le (Nat.le_of_lt cleanup_lt)
    rw [ratio_eq] at equation
    have exponent_positive : 0 < digits.length - cleanup := by omega
    have difference_nonzero :
        1 - continuantMismatchClockRatio ^ (digits.length - cleanup) ≠ 0 := by
      intro difference_zero
      apply mismatchClockRatio_pow_ne_one exponent_positive
      linarith
    have radix_nonzero : continuantMismatchDefect digits ≠ 0 := by
      rw [equation]
      exact mul_ne_zero (neg_ne_zero.mpr mismatchBalanceConstant_ne_zero)
        difference_nonzero
    obtain ⟨radixExponent, radixVal⟩ :=
      mismatchRadix_val_five_even range radix_nonzero
    have valuation_eq := congrArg (padicValRat 5) equation
    rw [radixVal,
      mismatchBalance_forward_val_five exponent_positive] at valuation_eq
    omega
  · subst cleanup
    have ratio_eq :
        continuantMismatchClockRatio ^ digits.length *
            continuantMismatchClockRatio⁻¹ ^ digits.length = 1 := by
      simpa using
        continuantMismatchClock_pow_mul_inverse_pow_of_le (count := digits.length)
          (cleanup := digits.length) (le_refl digits.length)
    rw [ratio_eq, sub_self, mul_zero] at equation
    exact ⟨rfl, (continuantMismatchDefect_eq_zero_iff digits range).mp equation⟩
  · have ratio_eq :
        continuantMismatchClockRatio ^ digits.length * continuantMismatchClockRatio⁻¹ ^ cleanup =
          continuantMismatchClockRatio⁻¹ ^ (cleanup - digits.length) :=
      continuantMismatchClock_pow_mul_inverse_pow_of_le_reverse (Nat.le_of_lt count_lt)
    rw [ratio_eq] at equation
    have exponent_positive : 0 < cleanup - digits.length := by omega
    have difference_nonzero :
        1 - continuantMismatchClockRatio⁻¹ ^ (cleanup - digits.length) ≠ 0 := by
      intro difference_zero
      apply mismatchClockRatio_inv_pow_ne_one exponent_positive
      linarith
    have radix_nonzero : continuantMismatchDefect digits ≠ 0 := by
      rw [equation]
      exact mul_ne_zero (neg_ne_zero.mpr mismatchBalanceConstant_ne_zero)
        difference_nonzero
    obtain ⟨radixExponent, radixVal⟩ :=
      mismatchRadix_val_two_even range radix_nonzero
    have valuation_eq := congrArg (padicValRat 2) equation
    rw [radixVal,
      mismatchBalance_reverse_val_two exponent_positive] at valuation_eq
    omega

private theorem mismatchRadix_eq_zero_of_all_zero (digits : List ℤ)
    (all_zero : ∀ digit ∈ digits, digit = 0) : continuantMismatchDefect digits = 0 := by
  have range : ContinuantMismatchDigits digits := by
    intro digit membership
    exact Or.inr (Or.inl (all_zero digit membership))
  exact (continuantMismatchDefect_eq_zero_iff digits range).mpr all_zero

/-- The split endpoint bridge reads one affine functional as a singular scalar multiple. -/
theorem continuantMismatchBridge_detects_affine (ratio shift : ℚ) :
    falseWaitReturn 0 * falseWaitReturn 12 * continuantMismatchAffine ratio shift *
          wordProduct falseWaitReturn [12, 8, 12, 12, 15, 8] *
        falseWaitReturn 0 =
      (-15092357529600000 * (ratio + 4 * shift - 1)) •
        falseWaitReturn 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (norm_num [continuantMismatchAffine, wordProduct_cons, wordProduct_nil,
        falseWaitReturn_eq_state, falseWaitReturnOfState, cubicDefectState,
        CubicDefectState.next, Matrix.mul_apply, Matrix.smul_apply,
        Fin.sum_univ_succ] <;>
      ring)

/-- The normalized endpoint bridge vanishes exactly on a zero schedule with balanced cleanup. -/
theorem continuantMismatchBridge_zero_iff (digits : List ℤ) (cleanup : ℕ)
    (range : ContinuantMismatchDigits digits) :
    falseWaitReturn 0 * falseWaitReturn 12 *
            (continuantMismatchClockProduct digits * continuantMismatchClockReader ^ cleanup) *
          wordProduct falseWaitReturn [12, 8, 12, 12, 15, 8] *
        falseWaitReturn 0 = 0 ↔
      cleanup = digits.length ∧ ∀ digit ∈ digits, digit = 0 := by
  rw [continuantMismatchClockProduct_cleanup_affine,
    continuantMismatchBridge_detects_affine]
  let ratio :=
    continuantMismatchClockRatio ^ digits.length * continuantMismatchClockRatio⁻¹ ^ cleanup
  let shift :=
    149 / 252 * (1 - ratio) + 125 / 48 * continuantMismatchDefect digits
  change
    (-15092357529600000 * (ratio + 4 * shift - 1)) • falseWaitReturn 0 = 0 ↔ _
  constructor
  · intro zero
    have entry_zero := congrFun (congrFun zero 0) 1
    norm_num [falseWaitReturn_eq_state, falseWaitReturnOfState,
      cubicDefectState, Matrix.smul_apply, ratio, shift] at entry_zero
    have affine_zero : ratio + 4 * shift - 1 = 0 := by
      simpa [ratio, shift] using entry_zero
    have equation :
        continuantMismatchDefect digits =
          -continuantMismatchBalanceConstant * (1 - ratio) := by
      rw [continuantMismatchBalanceConstant]
      dsimp [shift] at affine_zero
      linarith
    exact continuantMismatchBalanceEquation_forces digits cleanup range equation
  · rintro ⟨cleanup_eq, all_zero⟩
    have ratio_eq : ratio = 1 := by
      dsimp [ratio]
      rw [cleanup_eq]
      simpa using
        continuantMismatchClock_pow_mul_inverse_pow_of_le (count := digits.length)
          (cleanup := digits.length) (le_refl digits.length)
    have radix_zero : continuantMismatchDefect digits = 0 :=
      mismatchRadix_eq_zero_of_all_zero digits all_zero
    dsimp [shift]
    rw [ratio_eq, radix_zero]
    norm_num [shift]

/-- Physical clocked checks followed by an arbitrary number of true-reader cleanup blocks. -/
def continuantReadWordWithCleanup (checks : List (Bool × Bool)) (cleanup : ℕ) : List Nat :=
  checks.flatMap continuantClockedReadWord ++
    continuantRepeatWord (continuantRadixReaderWord true) cleanup

/-- The split endpoint bridge containing a clocked comparison with arbitrary cleanup. -/
def continuantCheckedZeroWordWithCleanup
    (checks : List (Bool × Bool)) (cleanup : ℕ) : List Nat :=
  [0, 12] ++
    (continuantReadWordWithCleanup checks cleanup ++ [12, 8, 12, 12, 15, 8, 0])

private theorem continuantClockedReadGenerator_eq_normalized (digit : ℤ) :
    continuantClockedReadGenerator digit =
      (25 : ℚ) •
        (continuantDefectTranslation (digit * (125 / 48)) * continuantMismatchClock) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (norm_num [continuantClockedReadGenerator, continuantDefectTranslation,
        continuantMismatchClock, continuantRadixGenerator, continuantRadixDigit,
        Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_succ] <;>
      ring)

private theorem continuantClockedReadGenerators_eq_normalized (digits : List ℤ) :
    wordProduct continuantClockedReadGenerator digits =
      (25 ^ digits.length : ℚ) • continuantMismatchClockProduct digits := by
  induction digits with
  | nil =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [continuantMismatchClockProduct, Matrix.one_apply, Matrix.smul_apply]
  | cons digit digits induction =>
      rw [wordProduct_cons, continuantClockedReadGenerator_eq_normalized, induction,
        Matrix.smul_mul, Matrix.mul_smul, continuantMismatchClockProduct, List.length_cons,
        pow_succ]
      simp only [smul_smul]
      congr 1
      ring

private theorem continuantClockedReadWords_projectivelyRealize_normalized
    (checks : List (Bool × Bool)) :
    continuantProjectivelyRealizes (checks.flatMap continuantClockedReadWord)
      (continuantMismatchClockProduct (checks.map continuantReadError)) := by
  rcases continuantClockedReadWords_projectivelyRealize checks with
    ⟨scale, scale_ne, product⟩
  rw [continuantClockedReadGenerators_eq_normalized] at product
  refine ⟨scale * 25 ^ checks.length,
    mul_ne_zero scale_ne (pow_ne_zero _ (by norm_num)), ?_⟩
  rw [product, List.length_map]
  simp only [smul_smul]

/-- The physical comparison with arbitrary cleanup realizes the normalized clock product and
reader power up to one nonzero rational scale. -/
theorem continuantReadWordWithCleanup_projectivelyRealizes
    (checks : List (Bool × Bool)) (cleanup : ℕ) :
    continuantProjectivelyRealizes (continuantReadWordWithCleanup checks cleanup)
      (continuantMismatchClockProduct (checks.map continuantReadError) *
        continuantMismatchClockReader ^ cleanup) := by
  have clocked := continuantClockedReadWords_projectivelyRealize_normalized checks
  have cleanupRealizes := continuantProjectivelyRealizes_repeat
    (continuantRadixReaderWord_projectivelyRealizes true) cleanup
  have combined := continuantProjectivelyRealizes_append clocked cleanupRealizes
  simpa only [continuantReadWordWithCleanup, continuantMismatchClockReader] using combined

/-- Every wait in a clocked comparison with arbitrary cleanup is strictly positive. -/
theorem continuantReadWordWithCleanup_positive
    (checks : List (Bool × Bool)) (cleanup : ℕ) :
    ∀ wait ∈ continuantReadWordWithCleanup checks cleanup, 0 < wait := by
  intro wait membership
  rw [continuantReadWordWithCleanup, List.mem_append] at membership
  rcases membership with clocked_mem | cleanup_mem
  · obtain ⟨check, _, block_mem⟩ := List.mem_flatMap.mp clocked_mem
    rw [continuantClockedReadWord, List.mem_append] at block_mem
    rcases block_mem with reader_mem | writer_or_clock
    · exact continuantRadixReaderWord_positive check.1 wait reader_mem
    · rw [List.mem_append] at writer_or_clock
      rcases writer_or_clock with writer_mem | clock_mem
      · exact continuantRadixEncoding_positive [check.2] wait (by
          simpa [continuantRadixEncoding] using writer_mem)
      · exact continuantRadixEncoding_positive [true] wait (by
          simpa [continuantRadixEncoding] using clock_mem)
  · exact continuantRepeatWord_positive
      (continuantRadixReaderWord_positive true) cleanup wait cleanup_mem

private theorem continuantMatrix_mul_smul_mul (scale : ℚ)
    (left middle right : Square (Fin 2) ℚ) :
    left * ((scale • middle) * right) = scale • (left * middle * right) := by
  rw [Matrix.smul_mul, Matrix.mul_smul]
  simp only [Matrix.mul_assoc]

/-- The physical endpoint bridge self-checks its cleanup count: it vanishes exactly when there
is one cleanup reader per check and every guessed bit matches its writer. -/
theorem continuantCheckedZeroWordWithCleanup_zero_iff
    (checks : List (Bool × Bool)) (cleanup : ℕ) :
    wordProduct falseWaitReturn (continuantCheckedZeroWordWithCleanup checks cleanup) = 0 ↔
      cleanup = checks.length ∧ ∀ check ∈ checks, check.1 = check.2 := by
  let digits := checks.map continuantReadError
  have range : ContinuantMismatchDigits digits := continuantReadErrors_range checks
  have errors_zero_iff :
      (∀ digit ∈ digits, digit = 0) ↔ ∀ check ∈ checks, check.1 = check.2 :=
    (continuantMismatchDefect_eq_zero_iff digits range).symm.trans
      (continuantReadDefect_eq_zero_iff checks)
  rcases continuantReadWordWithCleanup_projectivelyRealizes checks cleanup with
    ⟨scale, scale_ne, middleProduct⟩
  let normalized := continuantMismatchClockProduct digits * continuantMismatchClockReader ^ cleanup
  have product_eq :
      wordProduct falseWaitReturn (continuantCheckedZeroWordWithCleanup checks cleanup) =
        scale •
          (falseWaitReturn 0 * falseWaitReturn 12 * normalized *
            wordProduct falseWaitReturn [12, 8, 12, 12, 15, 8] *
              falseWaitReturn 0) := by
    change wordProduct falseWaitReturn (continuantReadWordWithCleanup checks cleanup) =
      scale • normalized at middleProduct
    rw [continuantCheckedZeroWordWithCleanup, wordProduct_append, wordProduct_append,
      middleProduct]
    calc
      wordProduct falseWaitReturn [0, 12] *
            ((scale • normalized) *
              wordProduct falseWaitReturn [12, 8, 12, 12, 15, 8, 0]) =
          scale •
            (wordProduct falseWaitReturn [0, 12] * normalized *
              wordProduct falseWaitReturn [12, 8, 12, 12, 15, 8, 0]) :=
        continuantMatrix_mul_smul_mul scale _ _ _
      _ = scale •
          (falseWaitReturn 0 * falseWaitReturn 12 * normalized *
            wordProduct falseWaitReturn [12, 8, 12, 12, 15, 8] *
              falseWaitReturn 0) := by
        simp only [wordProduct_cons, wordProduct_nil, Matrix.mul_one, Matrix.mul_assoc]
  rw [product_eq, smul_eq_zero]
  simp only [scale_ne, false_or]
  change
    falseWaitReturn 0 * falseWaitReturn 12 *
            (continuantMismatchClockProduct digits * continuantMismatchClockReader ^ cleanup) *
          wordProduct falseWaitReturn [12, 8, 12, 12, 15, 8] *
        falseWaitReturn 0 = 0 ↔ _
  rw [continuantMismatchBridge_zero_iff digits cleanup range, List.length_map, errors_zero_iff]

end MatrixMortality.CubicReturn.NonPure
