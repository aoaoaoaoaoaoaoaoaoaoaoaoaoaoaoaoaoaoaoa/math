import MatrixMortality.MixedPrimeRealTrap

/-!
# Guarded pole resets in the mixed-prime real trap

The deepest real-trap predecessor branch can reset to arbitrary Archimedean depth. An explicit
period-fifty subfamily proves that this reset survives the five-adic shell guard.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation
open PeriodicShell

private local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
private local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private theorem unit_pow
    {value : ℚ} (value_unit : IsUnit 5 value) (exponent : ℕ) :
    IsUnit 5 (value ^ exponent) := by
  refine ⟨pow_ne_zero exponent value_unit.1, ?_⟩
  rw [padicValRat.pow, value_unit.2]
  simp

private theorem hasValue_pow
    {prime : ℕ} [Fact prime.Prime] {value : ℚ} {valuation : ℤ}
    (value_hasValue : HasValue prime value valuation) (exponent : ℕ) :
    HasValue prime (value ^ exponent) (exponent * valuation) := by
  refine ⟨pow_ne_zero exponent value_hasValue.1, ?_⟩
  rw [padicValRat.pow, value_hasValue.2]

private theorem natCast_fiveValue_one
    {value : ℕ} (five_dvd : 5 ∣ value) (twentyfive_not_dvd : ¬25 ∣ value) :
    HasValue 5 (value : ℚ) 1 := by
  obtain ⟨quotient, value_eq⟩ := five_dvd
  have quotient_not_dvd : ¬5 ∣ quotient := by
    intro five_dvd_quotient
    apply twentyfive_not_dvd
    obtain ⟨factor, quotient_eq⟩ := five_dvd_quotient
    refine ⟨factor, ?_⟩
    omega
  have five_value : HasValue 5 (5 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 5) 1)
  have quotient_unit : IsUnit 5 (quotient : ℚ) := by
    exact intCast_isUnit_of_not_dvd (by exact_mod_cast quotient_not_dvd)
  convert mul_hasValue five_value quotient_unit using 1
  · norm_num [value_eq]
  · norm_num

private theorem natCast_fiveValue_two
    {value : ℕ} (twentyfive_dvd : 25 ∣ value)
    (onehundredtwentyfive_not_dvd : ¬125 ∣ value) :
    HasValue 5 (value : ℚ) 2 := by
  obtain ⟨quotient, value_eq⟩ := twentyfive_dvd
  have quotient_not_dvd : ¬5 ∣ quotient := by
    intro five_dvd_quotient
    apply onehundredtwentyfive_not_dvd
    obtain ⟨factor, quotient_eq⟩ := five_dvd_quotient
    refine ⟨factor, ?_⟩
    omega
  have twentyfive_value : HasValue 5 (25 : ℚ) 2 := by
    convert primePower_hasValue (prime := 5) 2 using 1 <;> norm_num
  have quotient_unit : IsUnit 5 (quotient : ℚ) := by
    exact intCast_isUnit_of_not_dvd (by exact_mod_cast quotient_not_dvd)
  convert mul_hasValue twentyfive_value quotient_unit using 1
  · norm_num [value_eq]
  · norm_num

private theorem realTrapBandPoint_one_twoUnit
    {depth : ℕ} (depth_lower : 2 ≤ depth) :
    IsUnit 2 (realTrapBandPoint depth 1) := by
  have one_unit : IsUnit 2 (1 : ℚ) := ⟨one_ne_zero, padicValRat.one⟩
  have five_unit : IsUnit 2 (5 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have offset_unit : IsUnit 2 (1 / 5 : ℚ) := div_hasValue one_unit five_unit
  have two_value : HasValue 2 (2 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 2) 1)
  have three_unit : IsUnit 2 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have ten_value : HasValue 2 (10 : ℚ) 1 := by
    have five_mul := mul_hasValue two_value five_unit
    convert five_mul using 1 <;> norm_num
  have coefficient_value : HasValue 2 (3 / 10 : ℚ) (-1) := by
    simpa using div_hasValue three_unit ten_value
  have ratio_value : HasValue 2 (2 / 3 : ℚ) 1 := by
    simpa using div_hasValue two_value three_unit
  have scaled_value :
      HasValue 2 ((3 / 10 : ℚ) * (2 / 3 : ℚ) ^ depth) (depth - 1) := by
    simpa [sub_eq_add_neg, add_comm] using
      mul_hasValue coefficient_value (hasValue_pow ratio_value depth)
  have scaled_positive : IsPositive 2 ((3 / 10 : ℚ) * (2 / 3 : ℚ) ^ depth) :=
    ⟨scaled_value.1, by rw [scaled_value.2]; omega⟩
  simpa [realTrapBandPoint] using unit_add_positive offset_unit scaled_positive

private theorem realTrapBandPoint_one_threeValue
    {depth : ℕ} (depth_lower : 2 ≤ depth) :
    HasValue 3 (realTrapBandPoint depth 1) (1 - depth) := by
  have one_unit : IsUnit 3 (1 : ℚ) := ⟨one_ne_zero, padicValRat.one⟩
  have five_unit : IsUnit 3 (5 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have offset_unit : IsUnit 3 (1 / 5 : ℚ) := div_hasValue one_unit five_unit
  have three_value : HasValue 3 (3 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 3) 1)
  have ten_unit : IsUnit 3 (10 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have coefficient_value : HasValue 3 (3 / 10 : ℚ) 1 := by
    simpa using div_hasValue three_value ten_unit
  have two_unit : IsUnit 3 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have ratio_value : HasValue 3 (2 / 3 : ℚ) (-1) := by
    simpa using div_hasValue two_unit three_value
  have scaled_value :
      HasValue 3 ((3 / 10 : ℚ) * (2 / 3 : ℚ) ^ depth) (1 - depth) := by
    have raw := mul_hasValue coefficient_value (hasValue_pow ratio_value depth)
    convert raw using 1
    omega
  simpa [realTrapBandPoint] using
    add_hasValue_right offset_unit scaled_value (by omega)

private theorem poleReset_sourceNumerator_mod (period : ℕ) :
    3 ^ (50 * period + 49) + 2 ^ (50 * period + 49) ≡
      20 * 124 ^ period [MOD 125] := by
  have two50 : 2 ^ 50 ≡ 124 [MOD 125] := by norm_num
  have three50 : 3 ^ 50 ≡ 124 [MOD 125] := by norm_num
  have two49 : 2 ^ 49 ≡ 62 [MOD 125] := by norm_num
  have three49 : 3 ^ 49 ≡ 83 [MOD 125] := by norm_num
  rw [pow_add, pow_add, pow_mul, pow_mul]
  calc
    (3 ^ 50) ^ period * 3 ^ 49 + (2 ^ 50) ^ period * 2 ^ 49 ≡
        124 ^ period * 83 + 124 ^ period * 62 [MOD 125] :=
      ((three50.pow period).mul three49).add ((two50.pow period).mul two49)
    _ = 145 * 124 ^ period := by ring
    _ ≡ 20 * 124 ^ period [MOD 125] :=
      (by norm_num : 145 ≡ 20 [MOD 125]).mul_right _

private theorem poleReset_targetNumerator_mod (period : ℕ) :
    19 * 3 ^ (50 * period + 49) + 4 * 2 ^ (50 * period + 49) ≡
      75 * 124 ^ period [MOD 125] := by
  have two50 : 2 ^ 50 ≡ 124 [MOD 125] := by norm_num
  have three50 : 3 ^ 50 ≡ 124 [MOD 125] := by norm_num
  have two49 : 2 ^ 49 ≡ 62 [MOD 125] := by norm_num
  have three49 : 3 ^ 49 ≡ 83 [MOD 125] := by norm_num
  rw [pow_add, pow_add, pow_mul, pow_mul]
  calc
    19 * ((3 ^ 50) ^ period * 3 ^ 49) +
        4 * ((2 ^ 50) ^ period * 2 ^ 49) ≡
        19 * (124 ^ period * 83) + 4 * (124 ^ period * 62) [MOD 125] :=
      (((three50.pow period).mul three49).mul_left 19).add
        (((two50.pow period).mul two49).mul_left 4)
    _ = 1825 * 124 ^ period := by ring
    _ ≡ 75 * 124 ^ period [MOD 125] :=
      (by norm_num : 1825 ≡ 75 [MOD 125]).mul_right _

private theorem poleReset_sourceNumerator_value (period : ℕ) :
    HasValue 5
      ((3 : ℚ) ^ (50 * period + 49) + 2 ^ (50 * period + 49)) 1 := by
  let numerator := 3 ^ (50 * period + 49) + 2 ^ (50 * period + 49)
  have numerator_mod : numerator ≡ 20 * 124 ^ period [MOD 125] := by
    simpa only [numerator] using poleReset_sourceNumerator_mod period
  have five_dvd : 5 ∣ numerator := by
    have reduced := numerator_mod.of_dvd (by norm_num : 5 ∣ 125)
    have right_zero : 20 * 124 ^ period ≡ 0 [MOD 5] :=
      (dvd_mul_of_dvd_left (by norm_num : 5 ∣ 20) _).modEq_zero_nat
    exact Nat.modEq_zero_iff_dvd.mp (reduced.trans right_zero)
  have twentyfive_not_dvd : ¬25 ∣ numerator := by
    intro twentyfive_dvd
    have numerator_zero : numerator ≡ 0 [MOD 25] := twentyfive_dvd.modEq_zero_nat
    have reduced := numerator_mod.of_dvd (by norm_num : 25 ∣ 125)
    have right_dvd : 25 ∣ 20 * 124 ^ period :=
      Nat.modEq_zero_iff_dvd.mp (reduced.symm.trans numerator_zero)
    have coprime : Nat.Coprime 25 (124 ^ period) :=
      (by norm_num : Nat.Coprime 25 124).pow_right period
    have impossible : 25 ∣ 20 := coprime.dvd_of_dvd_mul_right right_dvd
    norm_num at impossible
  simpa only [numerator, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using
    natCast_fiveValue_one five_dvd twentyfive_not_dvd

private theorem poleReset_targetNumerator_value (period : ℕ) :
    HasValue 5
      (19 * (3 : ℚ) ^ (50 * period + 49) +
        4 * 2 ^ (50 * period + 49)) 2 := by
  let numerator := 19 * 3 ^ (50 * period + 49) + 4 * 2 ^ (50 * period + 49)
  have numerator_mod : numerator ≡ 75 * 124 ^ period [MOD 125] := by
    simpa only [numerator] using poleReset_targetNumerator_mod period
  have twentyfive_dvd : 25 ∣ numerator := by
    have right_zero : 75 * 124 ^ period ≡ 0 [MOD 25] :=
      (dvd_mul_of_dvd_left (by norm_num : 25 ∣ 75) _).modEq_zero_nat
    have reduced := numerator_mod.of_dvd (by norm_num : 25 ∣ 125)
    exact Nat.modEq_zero_iff_dvd.mp (reduced.trans right_zero)
  have onehundredtwentyfive_not_dvd : ¬125 ∣ numerator := by
    intro numerator_dvd
    have numerator_zero : numerator ≡ 0 [MOD 125] := numerator_dvd.modEq_zero_nat
    have right_dvd : 125 ∣ 75 * 124 ^ period :=
      Nat.modEq_zero_iff_dvd.mp (numerator_mod.symm.trans numerator_zero)
    have coprime : Nat.Coprime 125 (124 ^ period) :=
      (by norm_num : Nat.Coprime 125 124).pow_right period
    have impossible : 125 ∣ 75 := coprime.dvd_of_dvd_mul_right right_dvd
    norm_num at impossible
  simpa only [numerator, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
    natCast_fiveValue_two twentyfive_dvd onehundredtwentyfive_not_dvd

private theorem poleReset_units (period : ℕ) :
    let depth := 50 * period + 50
    let source := realTrapBandPoint depth 1
    IsUnit 5 source ∧ IsUnit 5 (shellStep 2 source) := by
  let exponent := 50 * period + 49
  let depth := 50 * period + 50
  let source := realTrapBandPoint depth 1
  have depth_eq : depth = exponent + 1 := by
    simp only [depth, exponent]
  have source_eq :
      source = ((3 : ℚ) ^ exponent + 2 ^ exponent) / (5 * 3 ^ exponent) := by
    simp only [source, realTrapBandPoint]
    rw [depth_eq, pow_succ, div_pow]
    field_simp
    ring
  have sourceNumerator := poleReset_sourceNumerator_value period
  have three_unit : IsUnit 5 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have five_value : HasValue 5 (5 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 5) 1)
  have sourceDenominator : HasValue 5 (5 * (3 : ℚ) ^ exponent) 1 := by
    simpa using mul_hasValue five_value (unit_pow three_unit exponent)
  have source_unit : IsUnit 5 source := by
    rw [source_eq]
    simpa using div_hasValue sourceNumerator sourceDenominator
  have target_eq :
      shellStep 2 source =
        (19 * (3 : ℚ) ^ exponent + 4 * 2 ^ exponent) / (75 * 3 ^ exponent) := by
    rw [source_eq]
    simp only [shellStep]
    field_simp
    ring
  have targetNumerator := poleReset_targetNumerator_value period
  have twentyfive_value : HasValue 5 (25 : ℚ) 2 := by
    convert primePower_hasValue (prime := 5) 2 using 1 <;> norm_num
  have seventyfive_value : HasValue 5 (75 : ℚ) 2 := by
    have three_mul := mul_hasValue three_unit twentyfive_value
    convert three_mul using 1 <;> norm_num
  have targetDenominator : HasValue 5 (75 * (3 : ℚ) ^ exponent) 2 := by
    simpa using mul_hasValue seventyfive_value (unit_pow three_unit exponent)
  have target_unit : IsUnit 5 (shellStep 2 source) := by
    rw [target_eq]
    simpa using div_hasValue targetNumerator targetDenominator
  exact ⟨source_unit, target_unit⟩

/-- The deepest real-trap branch survives the shell guard at unbounded source depth. Every
period gives a unit edge from depth `50·period+50` to depth four with wait two. -/
theorem shellStep_realTrap_guardedPoleReset (period : ℕ) :
    let sourceDepth := 50 * period + 50
    let source := realTrapBandPoint sourceDepth 1
    let targetMantissa :=
      9 / 10 + (27 / 20 : ℚ) * (2 / 3 : ℚ) ^ sourceDepth
    let target := realTrapBandPoint 4 targetMantissa
    source ∈ Set.Ioc (1 / 5 : ℚ) (1 / 2) ∧
      target ∈ Set.Ioc (1 / 5 : ℚ) (1 / 2) ∧
      IsUnit 5 source ∧ IsUnit 5 target ∧
      realTrapMaxPredecessorWait source = sourceDepth ∧
      realTrapMaxPredecessorWait target = 4 ∧
      shellStep 2 source = target := by
  let sourceDepth := 50 * period + 50
  let source := realTrapBandPoint sourceDepth 1
  let targetMantissa :=
    9 / 10 + (27 / 20 : ℚ) * (2 / 3 : ℚ) ^ sourceDepth
  let target := realTrapBandPoint 4 targetMantissa
  have sourceDepth_lower : 7 ≤ sourceDepth := by
    simp only [sourceDepth]
    omega
  obtain ⟨source_mem, target_mem, source_candidate, target_candidate, step_eq⟩ :=
    shellStep_realTrap_poleBranch_full (targetDepth := 4) (sourceDepth := sourceDepth)
      (by norm_num) sourceDepth_lower (mantissa := 1) (by norm_num) (by norm_num)
  obtain ⟨source_unit, output_unit⟩ := poleReset_units period
  have target_mem' : target ∈ Set.Ioc (1 / 5 : ℚ) (1 / 2) := by
    simpa only [target, targetMantissa, mul_one] using target_mem
  have target_candidate' : realTrapMaxPredecessorWait target = 4 := by
    simpa only [target, targetMantissa, mul_one] using target_candidate
  have step_eq' : shellStep 2 source = target := by
    simpa only [source, target, targetMantissa, mul_one] using step_eq
  have target_unit : IsUnit 5 target := by
    rw [← step_eq']
    simpa only [source] using output_unit
  exact ⟨source_mem, target_mem', by simpa only [source] using source_unit, target_unit,
    source_candidate, target_candidate', step_eq'⟩

/-- The guarded pole reset keeps the two-adic wall clear while its three-adic debt grows by one.
The fixed real target depth therefore hides unbounded three-adic depth. -/
theorem shellStep_realTrap_guardedPoleReset_twoThreeValues (period : ℕ) :
    let depth := 50 * period + 50
    let source := realTrapBandPoint depth 1
    IsUnit 2 source ∧ IsUnit 2 (shellStep 2 source) ∧
      HasValue 3 source (1 - depth) ∧ HasValue 3 (shellStep 2 source) (-depth) := by
  let depth := 50 * period + 50
  let source := realTrapBandPoint depth 1
  have depth_lower : 2 ≤ depth := by
    simp only [depth]
    omega
  have source_two := realTrapBandPoint_one_twoUnit depth_lower
  have target_two := shellStep_two_aboveWall 2 source_two (by norm_num)
  have source_three := realTrapBandPoint_one_threeValue depth_lower
  have target_three := shellStep_three_belowWall 2 source_three (by
    simp only [depth]
    omega)
  exact ⟨source_two, target_two, source_three, by
    convert target_three using 1
    simp only [depth]
    omega⟩

/-- Distinct guarded pole-reset periods have distinct targets; the reset ray does not create an
infinite fixed-target fibre. -/
theorem shellStep_realTrap_guardedPoleReset_target_injective : Function.Injective
    (fun period : ℕ => shellStep 2 (realTrapBandPoint (50 * period + 50) 1)) := by
  intro left right targets_eq
  have sources_eq := shellStep_injective 2 targets_eq
  have candidates_eq := congrArg realTrapMaxPredecessorWait sources_eq
  rw [realTrapMaxPredecessorWait_bandPoint (50 * left + 50) (by norm_num) (by norm_num),
    realTrapMaxPredecessorWait_bandPoint (50 * right + 50) (by norm_num) (by norm_num)]
    at candidates_eq
  omega

end MatrixMortality.MixedPrimeDebt
