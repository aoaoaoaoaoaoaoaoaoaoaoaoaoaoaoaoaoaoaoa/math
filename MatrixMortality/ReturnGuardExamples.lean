import MatrixMortality.ReturnGuardAddress
import MatrixMortality.ReturnGuardResonance

/-!
# Exact examples for the amalgamated valuation guard

The first pair is the concrete one-step mortal integer pair from the construction. The second
parameter set has a ready nonterminal fixed point. The third has an exact rational period-three
decoded orbit with waits `1, 2, 3`, proving that nested resonance is not confined to fixed points
or two-cycles.
-/

namespace MatrixMortality.ReturnGuard.Examples

open MatrixMortality.PadicValuation
open scoped Matrix

noncomputable section

private theorem five_prime : Nat.Prime 5 := by norm_num

private instance factPrimeFive : Fact (Nat.Prime 5) :=
  ⟨five_prime⟩

private theorem three_prime : Nat.Prime 3 := by norm_num

private instance factPrimeThree : Fact (Nat.Prime 3) :=
  ⟨three_prime⟩

private theorem val5_int_unit (z : Int) (not_dvd : ¬(5 : Int) ∣ z) :
    padicValRat 5 (z : ℚ) = 0 := by
  rw [padicValRat.of_int]
  exact_mod_cast padicValInt.eq_zero_of_not_dvd not_dvd

private theorem val5_self : padicValRat 5 (5 : ℚ) = 1 :=
  padicValRat.self (p := 5) (by norm_num)

private theorem val5_square : padicValRat 5 ((5 : ℚ) ^ 2) = 2 :=
  primePower_valuation 2

private theorem val5_869_div_28 :
    padicValRat 5 (869 / 28 : ℚ) = 0 := by
  rw [padicValRat.div (by norm_num) (by norm_num)]
  change padicValRat 5 ((869 : Int) : ℚ) -
    padicValRat 5 ((28 : Int) : ℚ) = 0
  rw [val5_int_unit 869 (by norm_num), val5_int_unit 28 (by norm_num)]
  norm_num

private theorem val5_841_div_28 :
    padicValRat 5 (841 / 28 : ℚ) = 0 := by
  rw [padicValRat.div (by norm_num) (by norm_num)]
  change padicValRat 5 ((841 : Int) : ℚ) -
    padicValRat 5 ((28 : Int) : ℚ) = 0
  rw [val5_int_unit 841 (by norm_num), val5_int_unit 28 (by norm_num)]
  norm_num

private theorem val5_thirty : padicValRat 5 (30 : ℚ) = 1 := by
  rw [show (30 : ℚ) = 5 * 6 by norm_num,
    padicValRat.mul (by norm_num) (by norm_num), val5_self]
  change 1 + padicValRat 5 ((6 : Int) : ℚ) = 1
  rw [val5_int_unit 6 (by norm_num)]
  norm_num

private theorem val5_twenty_five : padicValRat 5 (25 : ℚ) = 2 := by
  rw [show (25 : ℚ) = (5 : ℚ) ^ 2 by norm_num, val5_square]

private theorem val5_five_div_six : padicValRat 5 (5 / 6 : ℚ) = 1 := by
  rw [padicValRat.div (by norm_num) (by norm_num), val5_self]
  change 1 - padicValRat 5 ((6 : Int) : ℚ) = 1
  rw [val5_int_unit 6 (by norm_num)]
  norm_num

private theorem val5_neg_twenty_five_div_six :
    padicValRat 5 (-(25 / 6) : ℚ) = 2 := by
  rw [padicValRat.neg, padicValRat.div (by norm_num) (by norm_num)]
  rw [show (25 : ℚ) = (5 : ℚ) ^ 2 by norm_num, val5_square]
  change 2 - padicValRat 5 ((6 : Int) : ℚ) = 2
  rw [val5_int_unit 6 (by norm_num)]
  norm_num

/-- Concrete ready parameter set whose sole first legal step reaches the terminal point. -/
def mortalParameters : Parameters where
  prime := 5
  prime_prime := five_prime
  depth := 2
  depth_two := by norm_num
  center := 869 / 28
  reset := 30
  center_unit := ⟨by norm_num, val5_869_div_28⟩
  center_sub_one_unit := ⟨by norm_num, by
    norm_num only [div_sub_one]
    exact val5_841_div_28⟩
  reset_positive := ⟨by norm_num, by rw [val5_thirty]; norm_num⟩

theorem mortal_reset_ready :
    Ready mortalParameters 1 30 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · exact val5_thirty
  · norm_num only [mortalParameters, Nat.cast_ofNat, pow_one]
    exact val5_twenty_five

theorem mortal_guarded_step :
    guardedStep mortalParameters 1 (some 30) = some 1 := by
  rw [guardedStep_some mortalParameters 1 30 (by norm_num [mortalParameters])]
  norm_num [mortalParameters, guardDefect, drift]

theorem mortal_reachable : GuardedReachable mortalParameters :=
  Relation.TransGen.single
    ⟨0, by simpa using mortal_reset_ready, by simpa using mortal_guarded_step⟩

theorem mortal_rational_pair :
    IsMortal
      (ReturnFamily.pairGenerator
        (ambient (5 : ℚ) 2)
        (cut (869 / 28) 30)) :=
  (physical_isMortal_iff_guardedReachable mortalParameters).mpr mortal_reachable

/-- Denominator-cleared ambient generator of the concrete mortal pair. -/
def integerAmbient : Square (Fin 3) ℤ :=
  !![5, 0, 0;
     0, 1, 0;
     0, 0, 25]

/-- Denominator-cleared rank-two cut of the concrete mortal pair. -/
def integerCut : Square (Fin 3) ℤ :=
  !![-28, 28, 0;
     -869, 869, -29;
     -841, 841, -29]

theorem integerAmbient_eq :
    integerAmbient.map ((↑) : ℤ → ℚ) =
      5 • ambient (5 : ℚ) 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [integerAmbient, ambient, Matrix.smul_apply,
      Matrix.diagonal_apply]
  all_goals split <;> simp_all [Fin.ext_iff]

theorem integerCut_eq :
    integerCut.map ((↑) : ℤ → ℚ) =
      28 • cut (869 / 28) 30 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [integerCut, cut, input, output, drift,
      Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Explicit denominator-cleared zero word `B² A B²`. -/
theorem integer_zero_word :
    integerCut ^ 2 * integerAmbient * integerCut ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [integerAmbient, integerCut, pow_two,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- Concrete ready parameter set with a legal nonterminal fixed point. -/
def fixedParameters : Parameters where
  prime := 5
  prime_prime := five_prime
  depth := 2
  depth_two := by norm_num
  center := 2
  reset := 5 / 6
  center_unit := ⟨by norm_num, val5_int_unit 2 (by norm_num)⟩
  center_sub_one_unit := ⟨by norm_num, by norm_num⟩
  reset_positive := ⟨by norm_num, by rw [val5_five_div_six]; norm_num⟩

theorem fixed_reset_ready :
    Ready fixedParameters 1 (5 / 6) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · exact val5_five_div_six
  · norm_num only [fixedParameters, Nat.cast_ofNat, pow_one]
    exact val5_neg_twenty_five_div_six

theorem fixed_guarded_step :
    guardedStep fixedParameters 1 (some (5 / 6)) = some (5 / 6) := by
  rw [guardedStep_some fixedParameters 1 (5 / 6)
    (by norm_num [fixedParameters])]
  norm_num [fixedParameters, guardDefect, drift]

private theorem val3_int_unit (z : Int) (not_dvd : ¬(3 : Int) ∣ z) :
    padicValRat 3 (z : ℚ) = 0 := by
  rw [padicValRat.of_int]
  exact_mod_cast padicValInt.eq_zero_of_not_dvd not_dvd

private theorem val3_scaled_fraction
    (power : Nat) (numerator denominator : Int)
    (numerator_ne : numerator ≠ 0) (denominator_ne : denominator ≠ 0)
    (numerator_unit : ¬(3 : Int) ∣ numerator)
    (denominator_unit : ¬(3 : Int) ∣ denominator) :
    padicValRat 3
        ((3 : ℚ) ^ power * (numerator : ℚ) / (denominator : ℚ)) =
      power := by
  have numerator_has_value :
      IsUnit 3 (numerator : ℚ) :=
    ⟨by exact_mod_cast numerator_ne, val3_int_unit numerator numerator_unit⟩
  have denominator_has_value :
      IsUnit 3 (denominator : ℚ) :=
    ⟨by exact_mod_cast denominator_ne, val3_int_unit denominator denominator_unit⟩
  exact
    (div_hasValue
      (mul_hasValue (primePower_hasValue power) numerator_has_value)
      denominator_has_value).2

private theorem val3_neg_three_div_fourteen :
    padicValRat 3 (-3 / 14 : ℚ) = 1 := by
  rw [show (-3 / 14 : ℚ) = (3 : ℚ) ^ 1 * (-1 : ℚ) / 14 by norm_num]
  exact val3_scaled_fraction 1 (-1) 14 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

private theorem val3_neg_forty_five_div_fourteen :
    padicValRat 3 (-45 / 14 : ℚ) = 2 := by
  rw [show (-45 / 14 : ℚ) = (3 : ℚ) ^ 2 * (-5 : ℚ) / 14 by norm_num]
  exact val3_scaled_fraction 2 (-5) 14 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

private theorem val3_117_div_400 :
    padicValRat 3 (117 / 400 : ℚ) = 2 := by
  rw [show (117 / 400 : ℚ) = (3 : ℚ) ^ 2 * (13 : ℚ) / 400 by norm_num]
  exact val3_scaled_fraction 2 13 400 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

private theorem val3_neg_3483_div_400 :
    padicValRat 3 (-3483 / 400 : ℚ) = 4 := by
  rw [show (-3483 / 400 : ℚ) = (3 : ℚ) ^ 4 * (-43 : ℚ) / 400 by norm_num]
  exact val3_scaled_fraction 4 (-43) 400 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

private theorem val3_27_div_28 :
    padicValRat 3 (27 / 28 : ℚ) = 3 := by
  rw [show (27 / 28 : ℚ) = (3 : ℚ) ^ 3 * (1 : ℚ) / 28 by norm_num]
  exact val3_scaled_fraction 3 1 28 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

private theorem val3_neg_729_div_28 :
    padicValRat 3 (-729 / 28 : ℚ) = 6 := by
  rw [show (-729 / 28 : ℚ) = (3 : ℚ) ^ 6 * (-1 : ℚ) / 28 by norm_num]
  exact val3_scaled_fraction 6 (-1) 28 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

private theorem val3_neg_953_div_2240 :
    padicValRat 3 (-953 / 2240 : ℚ) = 0 := by
  rw [show (-953 / 2240 : ℚ) = (3 : ℚ) ^ 0 * (-953 : ℚ) / 2240 by norm_num]
  exact val3_scaled_fraction 0 (-953) 2240 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

private theorem val3_neg_3193_div_2240 :
    padicValRat 3 (-3193 / 2240 : ℚ) = 0 := by
  rw [show (-3193 / 2240 : ℚ) = (3 : ℚ) ^ 0 * (-3193 : ℚ) / 2240 by norm_num]
  exact val3_scaled_fraction 0 (-3193) 2240 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

private theorem val3_neg_1857_div_2365 :
    padicValRat 3 (-1857 / 2365 : ℚ) = 1 := by
  rw [show (-1857 / 2365 : ℚ) =
    (3 : ℚ) ^ 1 * (-619 : ℚ) / 2365 by norm_num]
  exact val3_scaled_fraction 1 (-619) 2365 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

private theorem val3_neg_3447_div_473 :
    padicValRat 3 (-3447 / 473 : ℚ) = 2 := by
  rw [show (-3447 / 473 : ℚ) =
    (3 : ℚ) ^ 2 * (-383 : ℚ) / 473 by norm_num]
  exact val3_scaled_fraction 2 (-383) 473 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

private theorem val3_neg_12291_div_473 :
    padicValRat 3 (-12291 / 473 : ℚ) = 1 := by
  rw [show (-12291 / 473 : ℚ) =
    (3 : ℚ) ^ 1 * (-4097 : ℚ) / 473 by norm_num]
  exact val3_scaled_fraction 1 (-4097) 473 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- Parameters whose decoded orbit has exact period three with waits `1, 2, 3`. -/
def cycleParameters : Parameters where
  prime := 3
  prime_prime := three_prime
  depth := 2
  depth_two := by norm_num
  center := -953 / 2240
  reset := -3 / 14
  center_unit := ⟨by norm_num, val3_neg_953_div_2240⟩
  center_sub_one_unit := ⟨by norm_num, by
    norm_num only [div_sub_one]
    simpa only [neg_div] using val3_neg_3193_div_2240⟩
  reset_positive := ⟨by norm_num, by
    rw [val3_neg_three_div_fourteen]
    norm_num⟩

theorem cycle_state_zero_ready :
    Ready cycleParameters 1 (-3 / 14) := by
  refine ⟨by norm_num, val3_neg_three_div_fourteen, ?_⟩
  norm_num only [cycleParameters, Nat.cast_ofNat, pow_one]
  simpa only [neg_div] using val3_neg_forty_five_div_fourteen

theorem cycle_state_one_ready :
    Ready cycleParameters 2 (117 / 400) := by
  refine ⟨by norm_num, val3_117_div_400, ?_⟩
  norm_num only [cycleParameters, Nat.cast_ofNat, pow_two]
  simpa only [neg_div] using val3_neg_3483_div_400

theorem cycle_state_two_ready :
    Ready cycleParameters 3 (27 / 28) := by
  refine ⟨by norm_num, val3_27_div_28, ?_⟩
  norm_num only [cycleParameters, Nat.cast_ofNat, pow_succ, pow_two]
  simpa only [neg_div] using val3_neg_729_div_28

theorem cycle_residual_states :
    stateOfResidual cycleParameters 1 = -3 / 14 ∧
      stateOfResidual cycleParameters (5 / 17) = 117 / 400 ∧
        stateOfResidual cycleParameters (43 / 283) = 27 / 28 := by
  norm_num [stateOfResidual, cycleParameters, drift]

theorem cycle_step_zero :
    DecodedStep cycleParameters 1 (5 / 17) := by
  refine ⟨1, ?_, ?_⟩
  · rw [residualBranch_iff_ready]
    simpa [cycle_residual_states.1] using cycle_state_zero_ready
  · norm_num [residualStep, prefixDecode, centerTransform, cycleParameters, drift]

theorem cycle_step_one :
    DecodedStep cycleParameters (5 / 17) (43 / 283) := by
  refine ⟨2, ?_, ?_⟩
  · rw [residualBranch_iff_ready]
    rw [cycle_residual_states.2.1]
    exact cycle_state_one_ready
  · norm_num [residualStep, prefixDecode, centerTransform, cycleParameters, drift]

theorem cycle_step_two :
    DecodedStep cycleParameters (43 / 283) 1 := by
  refine ⟨3, ?_, ?_⟩
  · rw [residualBranch_iff_ready]
    rw [cycle_residual_states.2.2]
    exact cycle_state_two_ready
  · norm_num [residualStep, prefixDecode, centerTransform, cycleParameters, drift]

/-- Exact rational period-three survivor with wait itinerary `1, 2, 3`. -/
theorem cycle_decoded_orbit :
    Relation.TransGen (DecodedStep cycleParameters) 1 1 :=
  ((Relation.TransGen.single cycle_step_zero).tail cycle_step_one).tail cycle_step_two

theorem cycle_terminalResidual :
    terminalResidual cycleParameters = 473 / 3193 := by
  norm_num [terminalResidual, cycleParameters, drift]

theorem cycle_is_nonterminal :
    terminalResidual cycleParameters ≠ 1 := by
  rw [cycle_terminalResidual]
  norm_num

theorem cycle_ready_tails :
    readyTail cycleParameters 1 (-3 / 14) = -14 / 5 ∧
      readyTail cycleParameters 2 (117 / 400) = -400 / 43 ∧
        readyTail cycleParameters 3 (27 / 28) = -28 := by
  norm_num [readyTail, cycleParameters]

theorem cycle_resonanceCenter :
    resonanceCenter cycleParameters = -953 / 473 := by
  norm_num [resonanceCenter, cycleParameters, drift]

/-- The first two legs of the period-three orbit are consecutive equal-depth resonances. -/
theorem cycle_first_two_resonant :
    ResonantTail cycleParameters 1
        (readyTail cycleParameters 1 (-3 / 14)) ∧
      ResonantTail cycleParameters 2
        (readyTail cycleParameters 2 (117 / 400)) := by
  constructor
  · rw [resonantTail_iff_hasValue, cycle_ready_tails.1,
      cycle_resonanceCenter]
    refine ⟨by norm_num, ?_⟩
    norm_num only
    simpa only [neg_div] using val3_neg_1857_div_2365
  · rw [resonantTail_iff_hasValue, cycle_ready_tails.2.1,
      cycle_resonanceCenter]
    refine ⟨by norm_num, ?_⟩
    norm_num only
    simpa only [neg_div] using val3_neg_3447_div_473

/-- The third leg is genuinely nonresonant; it descends from wait three back to wait one. -/
theorem cycle_third_nonresonant :
    ¬ResonantTail cycleParameters 3
      (readyTail cycleParameters 3 (27 / 28)) := by
  rw [resonantTail_iff_hasValue, cycle_ready_tails.2.2,
    cycle_resonanceCenter]
  rintro ⟨_, valuation⟩
  norm_num only at valuation
  change padicValRat 3 (-(12291 / 473) : ℚ) = 3 at valuation
  have actual :
      padicValRat 3 (-(12291 / 473) : ℚ) = 1 := by
    simpa only [neg_div] using val3_neg_12291_div_473
  rw [actual] at valuation
  norm_num at valuation

end
end MatrixMortality.ReturnGuard.Examples
