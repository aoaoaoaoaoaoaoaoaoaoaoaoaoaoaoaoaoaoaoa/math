import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Exact rational p-adic shells

`padicValRat` deliberately assigns zero valuation to zero. The predicates below retain the
nonzero side condition and expose the three shells used by valuation guards: negative, unit,
and positive valuation.
-/

namespace MatrixMortality.PadicValuation

/-- A nonzero rational with prescribed finite `prime`-adic valuation. -/
def HasValue (prime : Nat) (value : ℚ) (valuation : ℤ) : Prop :=
  value ≠ 0 ∧ padicValRat prime value = valuation

/-- A nonzero rational in the unit shell at `prime`. -/
abbrev IsUnit (prime : Nat) (value : ℚ) : Prop :=
  HasValue prime value 0

/-- An integer not divisible by the valuation prime is a rational unit. -/
theorem intCast_isUnit_of_not_dvd
    {prime : Nat} {value : ℤ}
    (not_dvd : ¬(prime : ℤ) ∣ value) :
    IsUnit prime (value : ℚ) := by
  refine ⟨?_, ?_⟩
  · exact_mod_cast fun value_zero : value = 0 =>
      not_dvd (value_zero ▸ dvd_zero (prime : ℤ))
  · rw [padicValRat.of_int]
    exact_mod_cast padicValInt.eq_zero_of_not_dvd not_dvd

/-- A nonzero rational in the positive-valuation shell at `prime`. -/
def IsPositive (prime : Nat) (value : ℚ) : Prop :=
  value ≠ 0 ∧ 0 < padicValRat prime value

/-- A nonzero rational in the negative-valuation shell at `prime`. -/
def IsNegative (prime : Nat) (value : ℚ) : Prop :=
  value ≠ 0 ∧ padicValRat prime value < 0

theorem primePower_ne_zero
    {prime : Nat} (prime_prime : prime.Prime) (exponent : Nat) :
    (prime : ℚ) ^ exponent ≠ 0 :=
  pow_ne_zero exponent (Nat.cast_ne_zero.mpr prime_prime.ne_zero)

theorem primePower_valuation
    {prime : Nat} [prime_fact : Fact prime.Prime] (exponent : Nat) :
    padicValRat prime ((prime : ℚ) ^ exponent) = exponent := by
  rw [padicValRat.pow (p := prime) (prime : ℚ) (k := exponent),
    padicValRat.self prime_fact.out.one_lt]
  simp

theorem primePower_hasValue
    {prime : Nat} [prime_fact : Fact prime.Prime] (exponent : Nat) :
    HasValue prime ((prime : ℚ) ^ exponent) exponent :=
  ⟨primePower_ne_zero prime_fact.out exponent, primePower_valuation exponent⟩

theorem mul_hasValue
    {prime : Nat} [Fact prime.Prime] {left right : ℚ} {leftValue rightValue : ℤ}
    (left_value : HasValue prime left leftValue)
    (right_value : HasValue prime right rightValue) :
    HasValue prime (left * right) (leftValue + rightValue) :=
  ⟨mul_ne_zero left_value.1 right_value.1, by
    rw [padicValRat.mul left_value.1 right_value.1, left_value.2, right_value.2]⟩

theorem div_hasValue
    {prime : Nat} [Fact prime.Prime] {numerator denominator : ℚ}
    {numeratorValue denominatorValue : ℤ}
    (numerator_value : HasValue prime numerator numeratorValue)
    (denominator_value : HasValue prime denominator denominatorValue) :
    HasValue prime (numerator / denominator) (numeratorValue - denominatorValue) :=
  ⟨div_ne_zero numerator_value.1 denominator_value.1, by
    rw [padicValRat.div numerator_value.1 denominator_value.1,
      numerator_value.2, denominator_value.2]⟩

/-- A prime power times a quotient of two prime-free integers has the displayed valuation. -/
theorem primePower_mul_int_div_int_hasValue
    {prime : Nat} [Fact prime.Prime] (exponent : Nat)
    {numerator denominator : ℤ}
    (numerator_not_dvd : ¬(prime : ℤ) ∣ numerator)
    (denominator_not_dvd : ¬(prime : ℤ) ∣ denominator) :
    HasValue prime
      ((prime : ℚ) ^ exponent * numerator / denominator) exponent := by
  simpa using
    div_hasValue
      (mul_hasValue (primePower_hasValue exponent)
        (intCast_isUnit_of_not_dvd numerator_not_dvd))
      (intCast_isUnit_of_not_dvd denominator_not_dvd)

/-- Every positive-valuation rational is a positive prime power times a unit. -/
theorem positive_eq_primePower_mul_unit
    {prime : Nat} [Fact prime.Prime] {value : ℚ}
    (value_positive : IsPositive prime value) :
    ∃ exponent : Nat, 0 < exponent ∧
      ∃ unit : ℚ, IsUnit prime unit ∧
        value = prime ^ exponent * unit := by
  obtain ⟨exponent, exponent_eq⟩ :=
    Int.eq_ofNat_of_zero_le (le_of_lt value_positive.2)
  have exponent_positive : 0 < exponent := by
    exact Int.natCast_pos.mp (exponent_eq ▸ value_positive.2)
  let unit := value / (prime : ℚ) ^ exponent
  have value_hasValue :
      HasValue prime value exponent := by
    exact ⟨value_positive.1, exponent_eq⟩
  have unit_shell : IsUnit prime unit := by
    simpa [unit] using
      div_hasValue value_hasValue (primePower_hasValue exponent)
  refine ⟨exponent, exponent_positive, unit, unit_shell, ?_⟩
  have power_ne := primePower_ne_zero (Fact.out : prime.Prime) exponent
  calc
    value = unit * prime ^ exponent := by
      exact (div_mul_cancel₀ value power_ne).symm
    _ = prime ^ exponent * unit := mul_comm _ _

theorem neg_hasValue
    {prime : Nat} {value : ℚ} {valuation : ℤ}
    (has_value : HasValue prime value valuation) :
    HasValue prime (-value) valuation :=
  ⟨neg_ne_zero.mpr has_value.1, by rw [padicValRat.neg, has_value.2]⟩

/-- In a sum with unequal prescribed valuations, the smaller left valuation survives. -/
theorem add_hasValue_left
    {prime : Nat} [Fact prime.Prime] {left right : ℚ} {leftValue rightValue : ℤ}
    (left_value : HasValue prime left leftValue)
    (right_value : HasValue prime right rightValue)
    (valuation_lt : leftValue < rightValue) :
    HasValue prime (left + right) leftValue := by
  have sum_ne : left + right ≠ 0 := by
    intro sum_zero
    have left_eq : left = -right := eq_neg_of_add_eq_zero_left sum_zero
    have equal_value := congrArg (padicValRat prime) left_eq
    rw [padicValRat.neg, left_value.2, right_value.2] at equal_value
    exact (ne_of_lt valuation_lt) equal_value
  exact ⟨sum_ne, by
    rw [padicValRat.add_eq_of_lt sum_ne left_value.1 right_value.1]
    · exact left_value.2
    · simpa [left_value.2, right_value.2] using valuation_lt⟩

/-- In a sum with unequal prescribed valuations, the smaller right valuation survives. -/
theorem add_hasValue_right
    {prime : Nat} [Fact prime.Prime] {left right : ℚ} {leftValue rightValue : ℤ}
    (left_value : HasValue prime left leftValue)
    (right_value : HasValue prime right rightValue)
    (valuation_gt : rightValue < leftValue) :
    HasValue prime (left + right) rightValue := by
  rw [add_comm]
  exact add_hasValue_left right_value left_value valuation_gt

/-- Unequal finite valuations cannot belong to equal rationals. -/
theorem ne_of_valuation_ne
    {prime : Nat} {left right : ℚ}
    (valuation_ne : padicValRat prime left ≠ padicValRat prime right) :
    left ≠ right := by
  intro equal
  exact valuation_ne (congrArg (padicValRat prime) equal)

/-- The smaller valuation wins a subtraction with unequal valuations. -/
theorem sub_eq_left_of_lt
    {prime : Nat} [Fact prime.Prime] {left right : ℚ}
    (left_ne : left ≠ 0) (right_ne : right ≠ 0)
    (valuation_lt : padicValRat prime left < padicValRat prime right) :
    padicValRat prime (left - right) = padicValRat prime left := by
  have difference_ne : left + -right ≠ 0 := by
    simpa only [sub_eq_add_neg] using
      sub_ne_zero.mpr (ne_of_valuation_ne (ne_of_lt valuation_lt))
  simpa only [sub_eq_add_neg, padicValRat.neg] using
    padicValRat.add_eq_of_lt (p := prime) difference_ne left_ne (neg_ne_zero.mpr right_ne)
      (by simpa using valuation_lt)

/-- The smaller valuation wins a subtraction with unequal valuations, right-oriented. -/
theorem sub_eq_right_of_gt
    {prime : Nat} [Fact prime.Prime] {left right : ℚ}
    (left_ne : left ≠ 0) (right_ne : right ≠ 0)
    (valuation_gt : padicValRat prime right < padicValRat prime left) :
    padicValRat prime (left - right) = padicValRat prime right := by
  rw [show left - right = -(right - left) by ring, padicValRat.neg]
  exact sub_eq_left_of_lt right_ne left_ne valuation_gt

/-- A subtraction with unequal valuations has their minimum valuation. -/
theorem sub_hasValue_min
    {prime : Nat} [Fact prime.Prime] {left right : ℚ}
    (left_ne : left ≠ 0) (right_ne : right ≠ 0)
    (valuation_ne : padicValRat prime left ≠ padicValRat prime right) :
    HasValue prime (left - right)
      (min (padicValRat prime left) (padicValRat prime right)) := by
  have difference_ne :=
    sub_ne_zero.mpr (ne_of_valuation_ne valuation_ne)
  have difference_ne' : left + -right ≠ 0 := by
    simpa only [sub_eq_add_neg] using difference_ne
  have valuation_ne' :
      padicValRat prime left ≠ padicValRat prime (-right) := by
    simpa only [padicValRat.neg] using valuation_ne
  refine ⟨difference_ne, ?_⟩
  simpa only [sub_eq_add_neg, padicValRat.neg] using
    padicValRat.add_eq_min (p := prime) difference_ne' left_ne
      (neg_ne_zero.mpr right_ne) valuation_ne'

/-- The valuation of a nonzero sum is at least the minimum of its summands. -/
theorem min_le_sub
    {prime : Nat} [Fact prime.Prime] {left right : ℚ}
    (difference_ne : left - right ≠ 0) :
    min (padicValRat prime left) (padicValRat prime right) ≤
      padicValRat prime (left - right) := by
  have difference_ne' : left + -right ≠ 0 := by
    simpa only [sub_eq_add_neg] using difference_ne
  simpa only [sub_eq_add_neg, padicValRat.neg] using
    padicValRat.min_le_padicValRat_add (p := prime) difference_ne'

/-- A unit minus a positive-shell point remains a unit. -/
theorem unit_sub_positive
    {prime : Nat} [Fact prime.Prime] {unit live : ℚ}
    (unit_shell : IsUnit prime unit) (positive_shell : IsPositive prime live) :
    IsUnit prime (unit - live) := by
  refine ⟨?_, ?_⟩
  · exact sub_ne_zero.mpr (ne_of_valuation_ne (by
      rw [unit_shell.2]
      exact ne_of_lt positive_shell.2))
  · simpa [unit_shell.2] using
      sub_eq_left_of_lt (prime := prime) unit_shell.1 positive_shell.1
        (by rw [unit_shell.2]; exact positive_shell.2)

/-- Subtracting a positive-shell point from one has valuation zero. -/
theorem one_sub_positive
    {prime : Nat} [Fact prime.Prime] {live : ℚ}
    (positive_shell : IsPositive prime live) :
    IsUnit prime (1 - live) :=
  unit_sub_positive ⟨one_ne_zero, padicValRat.one⟩ positive_shell

/-- A positive-shell point minus one has valuation zero. -/
theorem positive_sub_one
    {prime : Nat} [Fact prime.Prime] {live : ℚ}
    (positive_shell : IsPositive prime live) :
    IsUnit prime (live - 1) := by
  have opposite := one_sub_positive positive_shell
  rw [show live - 1 = -(1 - live) by ring]
  exact ⟨neg_ne_zero.mpr opposite.1, by
    rw [padicValRat.neg]
    exact opposite.2⟩

/-- A unit plus a positive-shell perturbation remains a unit. -/
theorem unit_add_positive
    {prime : Nat} [Fact prime.Prime] {unit error : ℚ}
    (unit_shell : IsUnit prime unit) (positive_shell : IsPositive prime error) :
    IsUnit prime (unit + error) := by
  have sum_ne : unit + error ≠ 0 := by
    intro sum_zero
    have unit_eq : unit = -error := eq_neg_of_add_eq_zero_left sum_zero
    have valuation_eq := congrArg (padicValRat prime) unit_eq
    rw [padicValRat.neg, unit_shell.2] at valuation_eq
    exact (ne_of_lt positive_shell.2) valuation_eq
  refine ⟨sum_ne, ?_⟩
  simpa [unit_shell.2] using
    padicValRat.add_eq_of_lt (p := prime) sum_ne unit_shell.1 positive_shell.1
      (by rw [unit_shell.2]; exact positive_shell.2)

/-- A negative-shell leading term dominates a unit perturbation. -/
theorem negative_add_unit
    {prime : Nat} [Fact prime.Prime] {negative unit : ℚ}
    (negative_shell : IsNegative prime negative) (unit_shell : IsUnit prime unit) :
    IsNegative prime (negative + unit) := by
  have sum_ne : negative + unit ≠ 0 := by
    intro sum_zero
    have negative_eq : negative = -unit := eq_neg_of_add_eq_zero_left sum_zero
    have valuation_eq := congrArg (padicValRat prime) negative_eq
    rw [padicValRat.neg, unit_shell.2] at valuation_eq
    exact (ne_of_lt negative_shell.2) valuation_eq
  refine ⟨sum_ne, ?_⟩
  rw [padicValRat.add_eq_of_lt sum_ne negative_shell.1 unit_shell.1]
  · exact negative_shell.2
  · simpa [unit_shell.2] using negative_shell.2

/-- A prime admitting adjacent rational units cannot be two. -/
theorem odd_prime_of_adjacent_units
    {prime : Nat} [Fact prime.Prime] {value : ℚ}
    (value_unit : IsUnit prime value)
    (predecessor_unit : IsUnit prime (value - 1)) :
    Odd prime := by
  apply (Fact.out : prime.Prime).odd_of_ne_two
  intro prime_two
  subst prime
  let numerator := value.num
  let denominator := value.den
  have numerator_ne : numerator ≠ 0 :=
    Rat.num_ne_zero.mpr value_unit.1
  have denominator_ne : denominator ≠ 0 := value.den_nz
  have denominator_ne_rat : (denominator : ℚ) ≠ 0 := by
    exact_mod_cast denominator_ne
  have valuation_eq :
      padicValInt 2 numerator = padicValNat 2 denominator := by
    have unit_valuation := value_unit.2
    change (padicValInt 2 numerator : ℤ) - padicValNat 2 denominator = 0 at unit_valuation
    exact_mod_cast sub_eq_zero.mp unit_valuation
  have common_valuation_zero : padicValInt 2 numerator = 0 := by
    by_contra valuation_ne
    have valuation_positive : 1 ≤ padicValInt 2 numerator :=
      Nat.one_le_iff_ne_zero.mpr valuation_ne
    have two_dvd_numerator : (2 : ℤ) ∣ numerator := by
      simpa using (padicValInt_dvd_iff (p := 2) 1 numerator).mpr
        (Or.inr valuation_positive)
    have two_dvd_numerator_abs : 2 ∣ numerator.natAbs := by
      have divisibility :=
        (Int.natAbs_dvd_natAbs (a := (2 : ℤ)) (b := numerator)).mpr
          two_dvd_numerator
      norm_num at divisibility ⊢
      exact divisibility
    have denominator_valuation_positive : 1 ≤ padicValNat 2 denominator := by
      rw [← valuation_eq]
      exact valuation_positive
    have two_dvd_denominator : 2 ∣ denominator := by
      simpa using (padicValNat_dvd_iff (p := 2) 1 denominator).mpr
        (Or.inr denominator_valuation_positive)
    have two_dvd_gcd : 2 ∣ Nat.gcd numerator.natAbs denominator :=
      Nat.dvd_gcd two_dvd_numerator_abs two_dvd_denominator
    rw [value.reduced.gcd_eq_one] at two_dvd_gcd
    norm_num at two_dvd_gcd
  have denominator_valuation_zero : padicValNat 2 denominator = 0 := by
    rw [← valuation_eq, common_valuation_zero]
  have numerator_odd : Odd numerator := by
    rw [← Int.not_even_iff_odd]
    intro numerator_even
    have valuation_positive : 1 ≤ padicValInt 2 numerator := by
      have divisibility :=
        (padicValInt_dvd_iff (p := 2) 1 numerator).mp (by
          simpa using numerator_even.two_dvd)
      exact divisibility.resolve_left numerator_ne
    omega
  have denominator_odd : Odd (denominator : ℤ) := by
    rw [← Int.not_even_iff_odd]
    intro denominator_even
    have two_dvd_denominator : 2 ∣ denominator := by
      exact_mod_cast denominator_even.two_dvd
    have valuation_positive : 1 ≤ padicValNat 2 denominator := by
      exact ((padicValNat_dvd_iff (p := 2) 1 denominator).mp (by
        simpa using two_dvd_denominator)).resolve_left denominator_ne
    omega
  have predecessor_eq :
      value - 1 = ((numerator - denominator : ℤ) : ℚ) / denominator := by
    dsimp [numerator, denominator]
    calc
      value - 1 = (value.num : ℚ) / value.den - 1 :=
        congrArg (fun rational : ℚ ↦ rational - 1) value.num_div_den.symm
      _ = ((value.num - value.den : ℤ) : ℚ) / value.den := by
        rw [div_sub_one]
        · norm_num
        · exact_mod_cast denominator_ne
  have difference_ne : numerator - (denominator : ℤ) ≠ 0 := by
    intro difference_zero
    apply predecessor_unit.1
    rw [predecessor_eq, difference_zero]
    norm_num
  have difference_valuation_zero :
      padicValInt 2 (numerator - (denominator : ℤ)) = 0 := by
    have unit_valuation := predecessor_unit.2
    rw [predecessor_eq,
      padicValRat.div (by exact_mod_cast difference_ne) denominator_ne_rat,
      padicValRat.of_int, padicValRat.of_nat] at unit_valuation
    change (padicValInt 2 (numerator - (denominator : ℤ)) : ℤ) -
      padicValNat 2 denominator = 0 at unit_valuation
    rw [denominator_valuation_zero] at unit_valuation
    have cast_valuation :
        (padicValInt 2 (numerator - (denominator : ℤ)) : ℤ) = 0 := by
      simpa only [Nat.cast_zero, sub_zero] using unit_valuation
    exact Int.ofNat_inj.mp cast_valuation
  have difference_even : Even (numerator - (denominator : ℤ)) :=
    numerator_odd.sub_odd denominator_odd
  have difference_valuation_positive :
      1 ≤ padicValInt 2 (numerator - (denominator : ℤ)) := by
    exact ((padicValInt_dvd_iff (p := 2) 1
      (numerator - (denominator : ℤ))).mp (by
        simpa using difference_even.two_dvd)).resolve_left difference_ne
  omega

end MatrixMortality.PadicValuation
