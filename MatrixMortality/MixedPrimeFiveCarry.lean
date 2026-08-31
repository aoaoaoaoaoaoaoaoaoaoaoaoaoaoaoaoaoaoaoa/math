import MatrixMortality.MixedPrimeRealTrapAddress

/-!
# Period-ten five-adic shell guard

For every five-adic unit source, one-step shell acceptance is exactly periodic in the wait with
period ten.  Hence ten residue tests classify every outgoing guarded wait.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation

private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private theorem unit_pow
    {value : ℚ} (value_unit : IsUnit 5 value) (exponent : ℕ) :
    IsUnit 5 (value ^ exponent) := by
  refine ⟨pow_ne_zero exponent value_unit.1, ?_⟩
  rw [padicValRat.pow, value_unit.2]
  simp

private theorem shellRatio_ten_sub_one_hasValue :
    HasValue 5 ((2 / 3 : ℚ) ^ 10 - 1) 2 := by
  convert primePower_mul_int_div_int_hasValue (prime := 5) 2
    (numerator := (-2321 : ℤ)) (denominator := (59049 : ℤ)) (by norm_num) (by norm_num)
    using 1 <;> norm_num

private theorem shellStep_add_ten_sub_hasValue
    (wait : ℕ) {state : ℚ} (state_unit : IsUnit 5 state) :
    HasValue 5 (shellStep (wait + 10) state - shellStep wait state) 1 := by
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
        (3 * (2 / 3 : ℚ) ^ wait * state * ((2 / 3 : ℚ) ^ 10 - 1)) 2 := by
    simpa using mul_hasValue prefix_unit shellRatio_ten_sub_one_hasValue
  have quotient_value := div_hasValue numerator_value five_value
  have quotient_value' :
      HasValue 5
        (3 * (2 / 3 : ℚ) ^ wait * state * ((2 / 3 : ℚ) ^ 10 - 1) / 5) 1 := by
    simpa using quotient_value
  convert quotient_value' using 1
  simp only [shellStep, pow_add]
  ring

/-- At a five-adic unit source, adding ten to a wait preserves one-step shell acceptance. -/
theorem shellStep_fiveUnit_add_ten_iff
    (wait : ℕ) {state : ℚ} (state_unit : IsUnit 5 state) :
    IsUnit 5 (shellStep (wait + 10) state) ↔ IsUnit 5 (shellStep wait state) := by
  have difference_value := shellStep_add_ten_sub_hasValue wait state_unit
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

end MatrixMortality.MixedPrimeDebt
