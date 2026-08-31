import MatrixMortality.MixedPrimeRealTrapAddress
import Mathlib.NumberTheory.Multiplicity

/-!
# Five-adic shell-guard periods

For every five-adic unit source, one-step shell acceptance is exactly periodic in the wait with
period ten.  A fixed tail of length `ℓ` raises the sufficient wait period to `2·5^(ℓ+1)`, and
zero preimages prove that this precision exponent is sharp uniformly.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation
open PeriodicShell

private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private theorem unit_pow
    {value : ℚ} (value_unit : IsUnit 5 value) (exponent : ℕ) :
    IsUnit 5 (value ^ exponent) := by
  refine ⟨pow_ne_zero exponent value_unit.1, ?_⟩
  rw [padicValRat.pow, value_unit.2]
  simp

private theorem shellRatio_precisionPeriod_sub_one_hasValue (precision : ℕ) :
    HasValue 5 ((2 / 3 : ℚ) ^ (2 * 5 ^ precision) - 1) (precision + 1) := by
  let exponent := 5 ^ precision
  have exponent_ne : exponent ≠ 0 := by simp [exponent]
  have lte :
      padicValNat 5 (9 ^ exponent - 4 ^ exponent) = precision + 1 := by
    have lifted := padicValNat.pow_sub_pow (p := 5) (by norm_num : Odd 5)
      (by norm_num : 4 < 9) (by norm_num : 5 ∣ 9 - 4) (by norm_num : ¬5 ∣ 9)
      exponent_ne
    rw [show 9 - 4 = 5 by norm_num, padicValNat_self,
      show exponent = 5 ^ precision by rfl, padicValNat.prime_pow] at lifted
    simpa [Nat.add_comm] using lifted
  have numerator_positive : 0 < 9 ^ exponent - 4 ^ exponent :=
    Nat.sub_pos_of_lt (Nat.pow_lt_pow_left (by norm_num) exponent_ne)
  have numerator_value :
      HasValue 5 ((9 ^ exponent - 4 ^ exponent : ℕ) : ℚ) (precision + 1) := by
    refine ⟨by positivity, ?_⟩
    rw [padicValRat.of_nat, lte]
    norm_num
  have nine_unit : IsUnit 5 (9 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have denominator_unit : IsUnit 5 ((9 : ℚ) ^ exponent) :=
    unit_pow nine_unit exponent
  have negative_value := neg_hasValue (div_hasValue numerator_value denominator_unit)
  have powers_le : 4 ^ exponent ≤ 9 ^ exponent :=
    Nat.pow_le_pow_left (by norm_num) exponent
  convert negative_value using 1
  · simp only [exponent]
    rw [pow_mul, div_pow]
    norm_num
    rw [div_pow, Nat.cast_sub powers_le]
    push_cast
    field_simp
    ring
  · omega

private theorem shellStep_add_precisionPeriod_sub_hasValue
    (wait precision : ℕ) {state : ℚ} (state_unit : IsUnit 5 state) :
    HasValue 5
      (shellStep (wait + 2 * 5 ^ precision) state - shellStep wait state) precision := by
  have two_unit : IsUnit 5 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have three_unit : IsUnit 5 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have five_value : HasValue 5 (5 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 5) 1)
  have ratio_unit : IsUnit 5 (2 / 3 : ℚ) := div_hasValue two_unit three_unit
  have prefix_unit :
      IsUnit 5 (3 * (2 / 3 : ℚ) ^ wait * state) :=
    mul_hasValue (mul_hasValue three_unit (unit_pow ratio_unit wait)) state_unit
  have numerator_value :
      HasValue 5
        (3 * (2 / 3 : ℚ) ^ wait * state *
          ((2 / 3 : ℚ) ^ (2 * 5 ^ precision) - 1)) (precision + 1) := by
    simpa using
      mul_hasValue prefix_unit (shellRatio_precisionPeriod_sub_one_hasValue precision)
  have quotient_value := div_hasValue numerator_value five_value
  have quotient_value' :
      HasValue 5
        (3 * (2 / 3 : ℚ) ^ wait * state *
          ((2 / 3 : ℚ) ^ (2 * 5 ^ precision) - 1) / 5) precision := by
    convert quotient_value using 1
    omega
  convert quotient_value' using 1
  simp only [shellStep, pow_add]
  ring

/-- At a five-adic unit source, adding ten to a wait preserves one-step shell acceptance. -/
theorem shellStep_fiveUnit_add_ten_iff
    (wait : ℕ) {state : ℚ} (state_unit : IsUnit 5 state) :
    IsUnit 5 (shellStep (wait + 10) state) ↔ IsUnit 5 (shellStep wait state) := by
  have difference_value :
      HasValue 5 (shellStep (wait + 10) state - shellStep wait state) 1 := by
    simpa using shellStep_add_precisionPeriod_sub_hasValue wait 1 state_unit
  have difference_positive :
      IsPositive 5 (shellStep (wait + 10) state - shellStep wait state) :=
    ⟨difference_value.1, by rw [difference_value.2]; norm_num⟩
  constructor
  · intro later_unit
    have negative_difference_positive :
        IsPositive 5 (-(shellStep (wait + 10) state - shellStep wait state)) := by
      have negative_value := neg_hasValue difference_value
      exact ⟨negative_value.1, by rw [negative_value.2]; norm_num⟩
    have recovered := unit_add_positive later_unit negative_difference_positive
    convert recovered using 1
    ring
  · intro earlier_unit
    have advanced := unit_add_positive earlier_unit difference_positive
    convert advanced using 1
    ring

/-- Adding any multiple of ten to a wait preserves one-step shell acceptance. -/
theorem shellStep_fiveUnit_add_ten_mul_iff
    (wait period : ℕ) {state : ℚ} (state_unit : IsUnit 5 state) :
    IsUnit 5 (shellStep (wait + 10 * period) state) ↔ IsUnit 5 (shellStep wait state) := by
  induction period with
  | zero => simp
  | succ period induction =>
      rw [Nat.mul_succ, ← Nat.add_assoc,
        shellStep_fiveUnit_add_ten_iff (wait + 10 * period) state_unit]
      exact induction

/-- Ten residue tests classify all guarded waits from one five-adic unit source. -/
theorem shellStep_fiveUnit_iff_mod_ten
    (wait : ℕ) {state : ℚ} (state_unit : IsUnit 5 state) :
    IsUnit 5 (shellStep wait state) ↔ IsUnit 5 (shellStep (wait % 10) state) := by
  have wait_decomposition : wait % 10 + 10 * (wait / 10) = wait := by omega
  have periodic :=
    shellStep_fiveUnit_add_ten_mul_iff (wait % 10) (wait / 10) state_unit
  rw [wait_decomposition] at periodic
  exact periodic

/-- A wait perturbation of five-adic precision `precision` loses one valuation unit at every
later block. -/
private theorem shellRun_tail_add_period_sub_hasValue
    (wait precision : ℕ) (tail : List ℕ) {state : ℚ} (state_unit : IsUnit 5 state) :
    HasValue 5
      (shellRun tail (shellStep (wait + 2 * 5 ^ precision) state) -
        shellRun tail (shellStep wait state))
      ((precision : ℤ) - tail.length) := by
  have step_difference :=
    shellStep_add_precisionPeriod_sub_hasValue wait precision state_unit
  have slope_value := shellSlope_hasValue_five tail
  have transported := mul_hasValue slope_value step_difference
  rw [shellRun_sub_shellRun]
  convert transported using 1
  ring

/-- The guard after a fixed tail sees its incoming wait only modulo
`2·5^(tail.length+1)`. -/
theorem shellRun_tail_fiveUnit_add_precisionPeriod_iff
    (wait : ℕ) (tail : List ℕ) {state : ℚ} (state_unit : IsUnit 5 state) :
    IsUnit 5
        (shellRun tail (shellStep (wait + 2 * 5 ^ (tail.length + 1)) state)) ↔
      IsUnit 5 (shellRun tail (shellStep wait state)) := by
  have difference_value :=
    show HasValue 5
        (shellRun tail (shellStep (wait + 2 * 5 ^ (tail.length + 1)) state) -
          shellRun tail (shellStep wait state)) 1 by
      convert shellRun_tail_add_period_sub_hasValue wait (tail.length + 1) tail state_unit
        using 1
      omega
  have difference_positive :
      IsPositive 5
        (shellRun tail (shellStep (wait + 2 * 5 ^ (tail.length + 1)) state) -
          shellRun tail (shellStep wait state)) :=
    ⟨difference_value.1, by rw [difference_value.2]; norm_num⟩
  constructor
  · intro later_unit
    have negative_difference_positive :
        IsPositive 5
          (-(shellRun tail (shellStep (wait + 2 * 5 ^ (tail.length + 1)) state) -
            shellRun tail (shellStep wait state))) := by
      have negative_value := neg_hasValue difference_value
      exact ⟨negative_value.1, by rw [negative_value.2]; norm_num⟩
    have recovered := unit_add_positive later_unit negative_difference_positive
    convert recovered using 1
    ring
  · intro earlier_unit
    have advanced := unit_add_positive earlier_unit difference_positive
    convert advanced using 1
    ring

/-- Adding any multiple of the tail-precision period preserves the final guard. -/
theorem shellRun_tail_fiveUnit_add_precisionPeriod_mul_iff
    (wait repetitions : ℕ) (tail : List ℕ) {state : ℚ} (state_unit : IsUnit 5 state) :
    IsUnit 5
        (shellRun tail
          (shellStep (wait + (2 * 5 ^ (tail.length + 1)) * repetitions) state)) ↔
      IsUnit 5 (shellRun tail (shellStep wait state)) := by
  let period := 2 * 5 ^ (tail.length + 1)
  change IsUnit 5 (shellRun tail (shellStep (wait + period * repetitions) state)) ↔ _
  induction repetitions with
  | zero => simp
  | succ repetitions induction =>
      rw [Nat.mul_succ, ← Nat.add_assoc]
      have one_period :=
        shellRun_tail_fiveUnit_add_precisionPeriod_iff
          (wait + period * repetitions) tail state_unit
      simpa only [period] using one_period.trans induction

/-- For a fixed tail, one finite residue classifies every possible incoming wait. -/
theorem shellRun_tail_fiveUnit_iff_mod_precisionPeriod
    (wait : ℕ) (tail : List ℕ) {state : ℚ} (state_unit : IsUnit 5 state) :
    IsUnit 5 (shellRun tail (shellStep wait state)) ↔
      IsUnit 5
        (shellRun tail (shellStep (wait % (2 * 5 ^ (tail.length + 1))) state)) := by
  let period := 2 * 5 ^ (tail.length + 1)
  change IsUnit 5 (shellRun tail (shellStep wait state)) ↔
    IsUnit 5 (shellRun tail (shellStep (wait % period) state))
  have periodic :=
    shellRun_tail_fiveUnit_add_precisionPeriod_mul_iff
      (wait % period) (wait / period) tail state_unit
  have decomposition : wait % period + period * (wait / period) = wait :=
    Nat.mod_add_div wait period
  rw [decomposition] at periodic
  exact periodic

/-- The unique source sent to zero by one nonempty shell schedule. -/
def shellZeroPreimage (waits : List ℕ) : ℚ :=
  -shellIntercept waits / shellSlope waits

/-- Every shell schedule sends its displayed zero preimage to zero. -/
theorem shellRun_shellZeroPreimage (waits : List ℕ) :
    shellRun waits (shellZeroPreimage waits) = 0 := by
  have slope_ne := (shellSlope_hasValue_five waits).1
  rw [shellRun_eq_slope_mul_add_intercept]
  simp only [shellZeroPreimage]
  field_simp
  ring

/-- The zero preimage of every nonempty shell schedule is a five-adic unit. -/
theorem shellZeroPreimage_fiveUnit
    {waits : List ℕ} (waits_ne : waits ≠ []) :
    IsUnit 5 (shellZeroPreimage waits) := by
  have intercept_value := shellIntercept_hasValue_five waits_ne
  have slope_value := shellSlope_hasValue_five waits
  simpa [shellZeroPreimage] using div_hasValue (neg_hasValue intercept_value) slope_value

/-- The tail-precision exponent is sharp uniformly: lowering it by one admits a unit source
whose original output is zero while the perturbed output is a unit. -/
theorem shellRun_tail_precisionPeriod_sharp (wait : ℕ) (tail : List ℕ) :
    let source := shellZeroPreimage (wait :: tail)
    IsUnit 5 source ∧
      shellRun tail (shellStep wait source) = 0 ∧
      IsUnit 5
        (shellRun tail (shellStep (wait + 2 * 5 ^ tail.length) source)) := by
  let source := shellZeroPreimage (wait :: tail)
  have source_unit : IsUnit 5 source :=
    shellZeroPreimage_fiveUnit (waits := wait :: tail) (by simp)
  have original_zero : shellRun tail (shellStep wait source) = 0 := by
    rw [← shellRun_cons]
    exact shellRun_shellZeroPreimage (wait :: tail)
  have difference_unit :
      IsUnit 5
        (shellRun tail (shellStep (wait + 2 * 5 ^ tail.length) source) -
          shellRun tail (shellStep wait source)) := by
    convert shellRun_tail_add_period_sub_hasValue wait tail.length tail source_unit using 1
    simp
  refine ⟨source_unit, original_zero, ?_⟩
  simpa only [original_zero, sub_zero] using difference_unit

end MatrixMortality.MixedPrimeDebt
