import MatrixMortality.MixedPrimeExit

/-!
# Spectator-prime denominator invariant

At every prime where `2`, `3`, and `5` are units, mixed-prime shell execution preserves the
negative part of the endpoint valuation.  Equivalently, every reduced-denominator exponent away
from the active primes `2`, `3`, and `5` is invariant through both shell prefixes and first exits.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation
open PeriodicShell

private theorem primeCast_not_dvd_of_ne
    {prime active : ℕ} [Fact prime.Prime] (active_prime : active.Prime)
    (prime_ne : prime ≠ active) :
    ¬(prime : ℤ) ∣ (active : ℤ) := by
  intro prime_dvd
  have prime_dvd_nat : prime ∣ active := Int.natCast_dvd_natCast.mp prime_dvd
  exact prime_ne ((Nat.prime_dvd_prime_iff_eq (Fact.out : prime.Prime) active_prime).mp
    prime_dvd_nat)

private theorem shellScale_spectatorUnit
    {prime : ℕ} [Fact prime.Prime]
    (two_unit : IsUnit prime (2 : ℚ)) (three_unit : IsUnit prime (3 : ℚ))
    (wait : ℕ) :
    IsUnit prime (3 * (2 / 3 : ℚ) ^ wait) := by
  have ratio_unit : IsUnit prime (2 / 3 : ℚ) := div_hasValue two_unit three_unit
  have ratio_power_unit : IsUnit prime ((2 / 3 : ℚ) ^ wait) := by
    induction wait with
    | zero =>
        simpa only [pow_zero] using
          (show IsUnit prime (1 : ℚ) from ⟨one_ne_zero, padicValRat.one⟩)
    | succ wait induction =>
        rw [pow_succ]
        exact mul_hasValue induction ratio_unit
  exact mul_hasValue three_unit ratio_power_unit

private theorem shellStep_spectatorNegative
    {prime : ℕ} [Fact prime.Prime]
    (two_unit : IsUnit prime (2 : ℚ)) (three_unit : IsUnit prime (3 : ℚ))
    (five_unit : IsUnit prime (5 : ℚ)) (wait : ℕ)
    {state : ℚ} {stateValue : ℤ} (state_value : HasValue prime state stateValue)
    (state_negative : stateValue < 0) :
    HasValue prime (shellStep wait state) stateValue := by
  have scale_unit := shellScale_spectatorUnit two_unit three_unit wait
  have leading_value :
      HasValue prime (3 * (2 / 3 : ℚ) ^ wait * state) stateValue := by
    simpa using mul_hasValue scale_unit state_value
  have numerator_value := add_hasValue_left leading_value
    (show IsUnit prime (1 : ℚ) from ⟨one_ne_zero, padicValRat.one⟩) state_negative
  simpa [shellStep] using div_hasValue numerator_value five_unit

private theorem shellStep_spectatorNonnegative
    {prime : ℕ} [Fact prime.Prime]
    (two_unit : IsUnit prime (2 : ℚ)) (three_unit : IsUnit prime (3 : ℚ))
    (five_unit : IsUnit prime (5 : ℚ)) (wait : ℕ) (state : ℚ)
    (state_nonnegative : 0 ≤ padicValRat prime state) :
    0 ≤ padicValRat prime (shellStep wait state) := by
  by_cases state_zero : state = 0
  · subst state
    have output_unit : IsUnit prime (shellStep wait 0) := by
      simpa [shellStep] using div_hasValue
        (show IsUnit prime (1 : ℚ) from ⟨one_ne_zero, padicValRat.one⟩) five_unit
    rw [output_unit.2]
  have scale_unit := shellScale_spectatorUnit two_unit three_unit wait
  have state_value : HasValue prime state (padicValRat prime state) :=
    ⟨state_zero, rfl⟩
  have leading_value := mul_hasValue scale_unit state_value
  let numerator := 3 * (2 / 3 : ℚ) ^ wait * state + 1
  by_cases numerator_zero : numerator = 0
  · have output_zero : shellStep wait state = 0 := by
      simp only [shellStep, numerator] at numerator_zero ⊢
      rw [numerator_zero]
      simp
    rw [output_zero, padicValRat.zero]
  · have numerator_lower :=
      padicValRat.min_le_padicValRat_add (p := prime) numerator_zero
    have numerator_nonnegative : 0 ≤ padicValRat prime numerator := by
      simpa only [numerator, leading_value.2, padicValRat.one,
        zero_add, min_eq_right state_nonnegative] using numerator_lower
    rw [shellStep, padicValRat.div numerator_zero five_unit.1, five_unit.2, sub_zero]
    exact numerator_nonnegative

private theorem shellRun_spectatorNegative
    {prime : ℕ} [Fact prime.Prime]
    (two_unit : IsUnit prime (2 : ℚ)) (three_unit : IsUnit prime (3 : ℚ))
    (five_unit : IsUnit prime (5 : ℚ)) (waits : List ℕ)
    {state : ℚ} {stateValue : ℤ} (state_value : HasValue prime state stateValue)
    (state_negative : stateValue < 0) :
    HasValue prime (shellRun waits state) stateValue := by
  induction waits generalizing state with
  | nil => exact state_value
  | cons wait waits induction =>
      rw [shellRun_cons]
      exact induction
        (shellStep_spectatorNegative two_unit three_unit five_unit wait
          state_value state_negative)

private theorem shellRun_spectatorNonnegative
    {prime : ℕ} [Fact prime.Prime]
    (two_unit : IsUnit prime (2 : ℚ)) (three_unit : IsUnit prime (3 : ℚ))
    (five_unit : IsUnit prime (5 : ℚ)) (waits : List ℕ) (state : ℚ)
    (state_nonnegative : 0 ≤ padicValRat prime state) :
    0 ≤ padicValRat prime (shellRun waits state) := by
  induction waits generalizing state with
  | nil => exact state_nonnegative
  | cons wait waits induction =>
      rw [shellRun_cons]
      exact induction _
        (shellStep_spectatorNonnegative two_unit three_unit five_unit wait state
          state_nonnegative)

/-- Shell execution preserves the denominator exponent at every prime where `2`, `3`, and `5`
are units.  The `min` expression is the negative part of the rational valuation. -/
theorem shellRun_spectatorDenominator
    {prime : ℕ} [Fact prime.Prime]
    (two_unit : IsUnit prime (2 : ℚ)) (three_unit : IsUnit prime (3 : ℚ))
    (five_unit : IsUnit prime (5 : ℚ)) (waits : List ℕ) (state : ℚ) :
    min (padicValRat prime (shellRun waits state)) 0 =
      min (padicValRat prime state) 0 := by
  by_cases state_nonnegative : 0 ≤ padicValRat prime state
  · have output_nonnegative :=
      shellRun_spectatorNonnegative two_unit three_unit five_unit waits state
        state_nonnegative
    rw [min_eq_right output_nonnegative, min_eq_right state_nonnegative]
  · have state_negative : padicValRat prime state < 0 := lt_of_not_ge state_nonnegative
    have state_ne : state ≠ 0 := by
      intro state_zero
      subst state
      rw [padicValRat.zero] at state_negative
      omega
    have output_value :=
      shellRun_spectatorNegative two_unit three_unit five_unit waits
        (show HasValue prime state (padicValRat prime state) from ⟨state_ne, rfl⟩)
        state_negative
    rw [output_value.2, min_eq_left state_negative.le]

/-- Every prime other than `2`, `3`, and `5` satisfies the spectator denominator invariant. -/
theorem shellRun_spectatorDenominator_of_ne_active
    {prime : ℕ} [Fact prime.Prime] (prime_ne_two : prime ≠ 2)
    (prime_ne_three : prime ≠ 3) (prime_ne_five : prime ≠ 5)
    (waits : List ℕ) (state : ℚ) :
    min (padicValRat prime (shellRun waits state)) 0 =
      min (padicValRat prime state) 0 := by
  exact shellRun_spectatorDenominator
    (intCast_isUnit_of_not_dvd
      (primeCast_not_dvd_of_ne (by norm_num : Nat.Prime 2) prime_ne_two))
    (intCast_isUnit_of_not_dvd
      (primeCast_not_dvd_of_ne (by norm_num : Nat.Prime 3) prime_ne_three))
    (intCast_isUnit_of_not_dvd
      (primeCast_not_dvd_of_ne (by norm_num : Nat.Prime 5) prime_ne_five)) waits state

/-- A proposed shell endpoint with a different spectator-prime denominator exponent is
unreachable, including as a first-exit image. -/
theorem shellRun_ne_of_spectatorDenominator_ne
    {prime : ℕ} [Fact prime.Prime]
    (two_unit : IsUnit prime (2 : ℚ)) (three_unit : IsUnit prime (3 : ℚ))
    (five_unit : IsUnit prime (5 : ℚ)) (waits : List ℕ) {source target : ℚ}
    (denominator_ne :
      min (padicValRat prime source) 0 ≠ min (padicValRat prime target) 0) :
    shellRun waits source ≠ target := by
  intro reaches
  apply denominator_ne
  rw [← reaches]
  exact (shellRun_spectatorDenominator two_unit three_unit five_unit waits source).symm

end MatrixMortality.MixedPrimeDebt
