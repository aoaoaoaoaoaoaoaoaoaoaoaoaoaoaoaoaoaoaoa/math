import MatrixMortality.IndexedExecution
import MatrixMortality.ReturnGuardAddress
import MatrixMortality.ReturnGuardCumulative
import MatrixMortality.ReturnGuardEndpointCompleteness
import MatrixMortality.ReturnGuardResonance

/-!
# Exact examples for the amalgamated valuation guard

The examples include a one-step mortal integer pair, two-return mortal guards, a ready nonterminal
fixed point, an exact rational period-three decoded orbit, a legal order-breaking reset-ball
ejection, and a lawful guard whose unique positive terminal word is `[1, 1, 1]`.
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

private theorem val5_scaled_fraction
    (power : Nat) (numerator denominator : Int)
    (numerator_ne : numerator ≠ 0) (denominator_ne : denominator ≠ 0)
    (numerator_unit : ¬(5 : Int) ∣ numerator)
    (denominator_unit : ¬(5 : Int) ∣ denominator) :
    padicValRat 5
        ((5 : ℚ) ^ power * (numerator : ℚ) / (denominator : ℚ)) =
      power := by
  have numerator_has_value :
      IsUnit 5 (numerator : ℚ) :=
    ⟨by exact_mod_cast numerator_ne, val5_int_unit numerator numerator_unit⟩
  have denominator_has_value :
      IsUnit 5 (denominator : ℚ) :=
    ⟨by exact_mod_cast denominator_ne, val5_int_unit denominator denominator_unit⟩
  exact
    (div_hasValue
      (mul_hasValue (primePower_hasValue power) numerator_has_value)
      denominator_has_value).2

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

/-- The three decoded residuals contain every continuation from the reset. -/
def cycleResidualInvariant : Set ℚ :=
  {1, 5 / 17, 43 / 283}

theorem cycleResidualInvariant_closed
    {source target : ℚ}
    (source_mem : source ∈ cycleResidualInvariant)
    (step : DecodedStep cycleParameters source target) :
    target ∈ cycleResidualInvariant := by
  simp only [cycleResidualInvariant, Set.mem_insert_iff,
    Set.mem_singleton_iff] at source_mem ⊢
  rcases source_mem with rfl | rfl | rfl
  · exact Or.inr (Or.inl
      (decodedStep_functional cycleParameters step cycle_step_zero))
  · exact Or.inr (Or.inr
      (decodedStep_functional cycleParameters step cycle_step_one))
  · exact Or.inl
      (decodedStep_functional cycleParameters step cycle_step_two)

theorem cycleResidualInvariant_terminal_absent :
    terminalResidual cycleParameters ∉ cycleResidualInvariant := by
  rw [cycle_terminalResidual]
  norm_num [cycleResidualInvariant]

/-- The rational period-three survivor never reaches the terminal residual. -/
theorem cycle_not_decodedReachable :
    ¬DecodedReachable cycleParameters := by
  intro reachable
  obtain ⟨steps, _, execution⟩ :=
    Relation.transGen_iff_exists_pos_reachesIn.mp reachable
  have target_mem :
      terminalResidual cycleParameters ∈ cycleResidualInvariant :=
    execution.target_mem
      (fun source_mem step =>
        cycleResidualInvariant_closed source_mem step)
      (by simp [cycleResidualInvariant])
  exact cycleResidualInvariant_terminal_absent target_mem

/-- The period-three parameters give a genuine immortal pair of rational `3 × 3` matrices. -/
theorem cycle_not_physical_isMortal :
    ¬IsMortal
      (ReturnFamily.pairGenerator
        (ambient (cycleParameters.prime : ℚ) cycleParameters.depth)
        (cut cycleParameters.center cycleParameters.reset)) := by
  rw [physical_isMortal_iff_decodedReachable]
  exact cycle_not_decodedReachable

/-- The endpoint coefficient at prime `31` excludes every terminal word for the period-three
parameters.  This strictly subsumes the older orbit-specific terminal exclusion. -/
theorem cycle_no_endpointTerminalWord (waits : List Nat) :
    ¬EndpointTerminalWord 3 2 (-953) 473 2240 waits := by
  letI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  exact
    not_endpointTerminalWord_of_prime_dvd_centerDifference
      (factor := 31) (by norm_num) (by norm_num) (by norm_num) waits

/-- The former four-step collision-ladder candidate is excluded at the coefficient boundary
before any tangent analysis: `5 ∣ -64 - 1`, while drift and base survive modulo five. -/
theorem collisionLadder_no_endpointTerminalWord (waits : List Nat) :
    ¬EndpointTerminalWord 3 2 (-64) 52633 1 waits := by
  exact
    not_endpointTerminalWord_of_prime_dvd_centerDifference
      (factor := 5) (by norm_num) (by norm_num) (by norm_num) waits

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

/-- Integral primitive-pair realization of the first period-three leg. -/
theorem cycle_integral_step_zero :
    IntegralStep 3 2 (-953) 473 2240 1 1 1 (-800) (-2720) := by
  norm_num [IntegralStep, integralStepNumerator, terminalDefect]

/-- Integral primitive-pair realization of the second period-three leg. -/
theorem cycle_integral_step_one :
    IntegralStep 3 2 (-953) 473 2240 2 5 17 (-1204) (-7924) := by
  norm_num [IntegralStep, integralStepNumerator, terminalDefect]

/-- Integral primitive-pair realization of the third period-three leg. -/
theorem cycle_integral_step_two :
    IntegralStep 3 2 (-953) 473 2240 3 43 283 (-3440) (-3440) := by
  norm_num [IntegralStep, integralStepNumerator, terminalDefect]

/-- The three raw outputs reduce by factors `160`, `28`, and `3440` to the checked residual
cycle. -/
theorem cycle_integral_reductions :
    (-800 : ℤ) = -160 * 5 ∧ (-2720 : ℤ) = -160 * 17 ∧
      (-1204 : ℤ) = -28 * 43 ∧ (-7924 : ℤ) = -28 * 283 ∧
        (-3440 : ℤ) = -3440 * 1 ∧ (-3440 : ℤ) = -3440 * 1 := by
  norm_num

/-- Every cancellation factor in the period-three survivor is supported by the fixed parameter
product `DL`; no novel cyclotomic prime is swallowed. -/
theorem cycle_commonFactors_dvd_fixedSupport :
    (160 : ℤ) ∣ 473 * 2240 ∧
      (28 : ℤ) ∣ 473 * 2240 ∧
        (3440 : ℤ) ∣ 473 * 2240 := by
  norm_num

/-- Guard with the exact decreasing wait itinerary `3, 1` from reset to terminal. -/
def decreasingMortalParameters : Parameters where
  prime := 3
  prime_prime := three_prime
  depth := 2
  depth_two := by norm_num
  center := 467 / 124
  reset := 108 / 31
  center_unit := ⟨by norm_num, by
    rw [show (467 / 124 : ℚ) =
      (3 : ℚ) ^ 0 * (467 : ℚ) / 124 by norm_num]
    exact val3_scaled_fraction 0 467 124
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩
  center_sub_one_unit := ⟨by norm_num, by
    rw [show (467 / 124 - 1 : ℚ) =
      (3 : ℚ) ^ 0 * (343 : ℚ) / 124 by norm_num]
    exact val3_scaled_fraction 0 343 124
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩
  reset_positive := ⟨by norm_num, by
    have value :=
      val3_scaled_fraction 3 4 31
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at value ⊢
    exact value ▸ by norm_num⟩

theorem decreasingMortal_reset_ready :
    Ready decreasingMortalParameters 3 (108 / 31) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [show (108 / 31 : ℚ) =
      (3 : ℚ) ^ 3 * (4 : ℚ) / 31 by norm_num]
    exact val3_scaled_fraction 3 4 31
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num only [decreasingMortalParameters, Nat.cast_ofNat, pow_succ,
      pow_two]
    have value :=
      val3_scaled_fraction 6 (-1) 31
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at value ⊢
    exact value

theorem decreasingMortal_middle_ready :
    Ready decreasingMortalParameters 1 (1581 / 62) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [show (1581 / 62 : ℚ) =
      (3 : ℚ) ^ 1 * (527 : ℚ) / 62 by norm_num]
    exact val3_scaled_fraction 1 527 62
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num only [decreasingMortalParameters, Nat.cast_ofNat, pow_one]
    have value :=
      val3_scaled_fraction 2 155 62
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at value ⊢
    exact value

theorem decreasingMortal_first_step :
    guardedStep decreasingMortalParameters 3 (some (108 / 31)) =
      some (1581 / 62) := by
  rw [guardedStep_some decreasingMortalParameters 3 (108 / 31)
    (by norm_num [decreasingMortalParameters])]
  norm_num [decreasingMortalParameters, guardDefect, drift]

theorem decreasingMortal_second_step :
    guardedStep decreasingMortalParameters 1 (some (1581 / 62)) =
      some 1 := by
  rw [guardedStep_some decreasingMortalParameters 1 (1581 / 62)
    (by norm_num [decreasingMortalParameters])]
  norm_num [decreasingMortalParameters, guardDefect, drift]

/-- A terminal-reaching legal orbit need not be one-step or monotone increasing in its waits. -/
theorem decreasingMortal_reachable :
    GuardedReachable decreasingMortalParameters :=
  (Relation.TransGen.single
    ⟨2, decreasingMortal_reset_ready, decreasingMortal_first_step⟩).tail
      ⟨0, decreasingMortal_middle_ready, decreasingMortal_second_step⟩

theorem decreasingMortal_terminalCoordinates :
    terminalCoordinate 467 (-35) 124 1 = 308 ∧
      terminalCoordinate 467 (-35) 124 (-1 / 77) = 3038 ∧
        terminalCoordinate 467 (-35) 124 (5 / 49) = 0 := by
  norm_num [terminalCoordinate]

/-- Guard with the exact increasing wait itinerary `2, 3` from reset to terminal. -/
def increasingMortalParameters : Parameters where
  prime := 5
  prime_prime := five_prime
  depth := 2
  depth_two := by norm_num
  center := -57803 / 10304
  reset := -7175 / 1288
  center_unit := ⟨by norm_num, by
    rw [show (-57803 / 10304 : ℚ) =
      (5 : ℚ) ^ 0 * (-57803 : ℚ) / 10304 by norm_num]
    exact val5_scaled_fraction 0 (-57803) 10304
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩
  center_sub_one_unit := ⟨by norm_num, by
    rw [show (-57803 / 10304 - 1 : ℚ) =
      (5 : ℚ) ^ 0 * (-68107 : ℚ) / 10304 by norm_num]
    exact val5_scaled_fraction 0 (-68107) 10304
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩
  reset_positive := ⟨by norm_num, by
    have value :=
      val5_scaled_fraction 2 (-287) 1288
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at value ⊢
    exact value ▸ by norm_num⟩

theorem increasingMortal_reset_ready :
    Ready increasingMortalParameters 2 (-7175 / 1288) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [show (-7175 / 1288 : ℚ) =
      (5 : ℚ) ^ 2 * (-287 : ℚ) / 1288 by norm_num]
    exact val5_scaled_fraction 2 (-287) 1288
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num only [increasingMortalParameters, Nat.cast_ofNat, pow_two]
    have value :=
      val5_scaled_fraction 4 (-63) 1288
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at value ⊢
    exact value

theorem increasingMortal_middle_ready :
    Ready increasingMortalParameters 3 (-1375 / 3864) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [show (-1375 / 3864 : ℚ) =
      (5 : ℚ) ^ 3 * (-11 : ℚ) / 3864 by norm_num]
    exact val5_scaled_fraction 3 (-11) 3864
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num only [increasingMortalParameters, Nat.cast_ofNat, pow_succ,
      pow_two]
    have value :=
      val5_scaled_fraction 6 (-31) 3864
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at value ⊢
    exact value

theorem increasingMortal_first_step :
    guardedStep increasingMortalParameters 2 (some (-7175 / 1288)) =
      some (-1375 / 3864) := by
  rw [guardedStep_some increasingMortalParameters 2 (-7175 / 1288)
    (by norm_num [increasingMortalParameters])]
  norm_num [increasingMortalParameters, guardDefect, drift]

theorem increasingMortal_second_step :
    guardedStep increasingMortalParameters 3 (some (-1375 / 3864)) =
      some 1 := by
  rw [guardedStep_some increasingMortalParameters 3 (-1375 / 3864)
    (by norm_num [increasingMortalParameters])]
  norm_num [increasingMortalParameters, guardDefect, drift]

/-- Terminal-reaching waits can increase strictly. -/
theorem increasingMortal_reachable :
    GuardedReachable increasingMortalParameters :=
  (Relation.TransGen.single
    ⟨1, increasingMortal_reset_ready, increasingMortal_first_step⟩).tail
      ⟨2, increasingMortal_middle_ready, increasingMortal_second_step⟩

theorem increasingMortal_terminalCoordinates :
    terminalCoordinate (-57803) 403 10304 1 = -67704 ∧
      terminalCoordinate (-57803) 403 10304 (3 / 403) =
        -41912 / 3 ∧
        terminalCoordinate (-57803) 403 10304 (403 / 68107) = 0 := by
  norm_num [terminalCoordinate]

/-- Even-resultant guard exposing the exact-order bridge obstruction. Its endpoint reset is
`249398`; wait four enters the strict `5`-adic reset ball, and wait one breaks the order of `3`
modulo `5`. -/
def orderBreakerParameters : Parameters where
  prime := 3
  prime_prime := three_prime
  depth := 2
  depth_two := by norm_num
  center := 249398
  reset := 249399
  center_unit := ⟨by norm_num, val3_int_unit 249398 (by norm_num)⟩
  center_sub_one_unit := ⟨by norm_num, by
    norm_num only [sub_self]
    exact val3_int_unit 249397 (by norm_num)⟩
  reset_positive := ⟨by norm_num, by
    have value :=
      val3_scaled_fraction 4 3079 1 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    norm_num at value ⊢
    exact value ▸ by norm_num⟩

private theorem orderBreaker_reset_ready :
    Ready orderBreakerParameters 4 249399 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [show (249399 : ℚ) = (3 : ℚ) ^ 4 * 3079 / 1 by norm_num]
    exact val3_scaled_fraction 4 3079 1 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · norm_num only [orderBreakerParameters, Nat.cast_ofNat, pow_succ, pow_two]
    rw [show (249318 : ℚ) = (3 : ℚ) ^ 8 * 38 / 1 by norm_num]
    exact val3_scaled_fraction 8 38 1 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)

private theorem orderBreaker_middle_ready :
    Ready orderBreakerParameters 1 (4863261 / 19) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [show (4863261 / 19 : ℚ) =
      (3 : ℚ) ^ 1 * 1621087 / 19 by norm_num]
    exact val3_scaled_fraction 1 1621087 19 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · norm_num only [orderBreakerParameters, Nat.cast_ofNat, pow_one]
    rw [show (4863204 / 19 : ℚ) =
      (3 : ℚ) ^ 2 * 540356 / 19 by norm_num]
    exact val3_scaled_fraction 2 540356 19 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)

private theorem orderBreaker_first_step :
    guardedStep orderBreakerParameters 4 (some 249399) = some (4863261 / 19) := by
  rw [guardedStep_some orderBreakerParameters 4 249399
    (by norm_num [orderBreakerParameters])]
  norm_num [orderBreakerParameters, guardDefect, drift]

private theorem orderBreaker_second_step :
    guardedStep orderBreakerParameters 1 (some (4863261 / 19)) =
      some (67384284465 / 270178) := by
  rw [guardedStep_some orderBreakerParameters 1 (4863261 / 19)
    (by norm_num [orderBreakerParameters])]
  norm_num [orderBreakerParameters, guardDefect, drift]

private theorem orderBreaker_target_ready :
    Ready orderBreakerParameters 1 (67384284465 / 270178) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [show (67384284465 / 270178 : ℚ) =
      (3 : ℚ) ^ 1 * 22461428155 / 270178 by norm_num]
    exact val3_scaled_fraction 1 22461428155 270178 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · norm_num only [orderBreakerParameters, Nat.cast_ofNat, pow_one]
    rw [show (67383473931 / 270178 : ℚ) =
      (3 : ℚ) ^ 2 * 7487052659 / 270178 by norm_num]
    exact val3_scaled_fraction 2 7487052659 270178 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)

private theorem orderBreaker_endpoint_values :
    padicValRat 5 ((4863261 / 19 : ℚ) - 1 - 249398) = 1 ∧
      padicValRat 5 (249398 : ℚ) = 0 ∧
        padicValRat 5 ((67384284465 / 270178 : ℚ) - 1 - 249398) = 0 := by
  constructor
  · rw [show ((4863261 / 19 : ℚ) - 1 - 249398) =
      (5 : ℚ) ^ 1 * 24936 / 19 by norm_num]
    exact val5_scaled_fraction 1 24936 19 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  constructor
  · exact val5_int_unit 249398 (by norm_num)
  · rw [show ((67384284465 / 270178 : ℚ) - 1 - 249398) =
      (5 : ℚ) ^ 0 * 2161443 / 270178 by norm_num]
    exact val5_scaled_fraction 0 2161443 270178 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)

private theorem orderBreaker_raw_endpoint :
    endpointTransfer (3 : ℤ) 2 249398 1 1 1 *ᵥ ![(4863242 : ℤ), 19] =
      ![(1212912257166 : ℤ), 4863204] := by
  ext i
  fin_cases i <;>
    norm_num [endpointTransfer, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_succ]

/-- A strict exact-order reset-ball entry can be destroyed by its first legal order-breaking
bridge without auxiliary-prime cancellation, and its target remains ready. The bridge's raw
endpoint pair reduces by exactly `18`; the primitive denominator grows from `19` to `270178`. -/
theorem orderBreaker_shatters_resetBall :
    Ready orderBreakerParameters 4 249399 ∧
      guardedStep orderBreakerParameters 4 (some 249399) = some (4863261 / 19) ∧
      Ready orderBreakerParameters 1 (4863261 / 19) ∧
      guardedStep orderBreakerParameters 1 (some (4863261 / 19)) =
        some (67384284465 / 270178) ∧
      Ready orderBreakerParameters 1 (67384284465 / 270178) ∧
      IsPrimitivePrimeDivisor 5 3 4 ∧
      padicValRat 5 ((4863261 / 19 : ℚ) - 1 - 249398) = 1 ∧
      padicValRat 5 (249398 : ℚ) = 0 ∧
      padicValRat 5 ((67384284465 / 270178 : ℚ) - 1 - 249398) = 0 ∧
      endpointTransfer (3 : ℤ) 2 249398 1 1 1 *ᵥ ![(4863242 : ℤ), 19] =
        ![(1212912257166 : ℤ), 4863204] ∧
      Nat.gcd 1212912257166 4863204 = 18 ∧
      ¬(5 : ℤ) ∣ (18 : ℤ) := by
  have primitive : IsPrimitivePrimeDivisor 5 3 4 := by
    refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    intro earlier positive less
    interval_cases earlier <;> norm_num at positive less ⊢
  refine ⟨orderBreaker_reset_ready, orderBreaker_first_step,
    orderBreaker_middle_ready, orderBreaker_second_step, orderBreaker_target_ready, primitive,
    orderBreaker_endpoint_values.1, orderBreaker_endpoint_values.2.1,
    orderBreaker_endpoint_values.2.2, orderBreaker_raw_endpoint, by norm_num, by norm_num⟩

/-- Retaining removed content turns the decreasing mortal orbit into one exact integral
execution; no primitive normalization variable remains. -/
theorem decreasingMortal_cumulativeExecution :
    CumulativeEndpointExecution 3 2 467 (-35) 124 [3, 1]
      (308, 1) (0, -1240) := by
  exact .cons (middle := (-12152, -4)) (by constructor <;> norm_num)
    (.cons (by constructor <;> norm_num) (.nil _))

/-- The lawful first-hit word `[3, 1]` creates primitive angular primes absent from every
coefficient and branch-cyclotomic factor.  Thus determinant support does not contain the
terminal pole support. -/
theorem decreasingMortal_emergentAngularPrimes :
    endpointProduct (3 : ℤ) 2 467 (-35) 124 [3, 1] =
        !![-789880, 243283040; -25420, -306280] ∧
      endpointProduct (3 : ℤ) 2 467 (-35) 124 [3, 1] *ᵥ ![308, 1] =
        ![0, -8135640] ∧
      Nat.gcd 8135640 25420 = 620 ∧
      (308 * (-25420) - (-8135640) : ℤ) = 620 * 494 ∧
      (-25420 : ℤ) = 620 * (-41) ∧
      (494 : ℤ) = 2 * 13 * 19 ∧
      ¬(19 : ℤ) ∣
        3 * 467 * 35 * 124 * 343 * 308 * (3 ^ 3 - 1) * (3 ^ 1 - 1) ∧
      ¬(41 : ℤ) ∣
        3 * 467 * 35 * 124 * 343 * 308 * (3 ^ 3 - 1) * (3 ^ 1 - 1) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [endpointProduct, endpointTransfer, Matrix.mul_apply,
        Fin.sum_univ_succ]
  constructor
  · ext i
    fin_cases i <;>
      norm_num [endpointProduct, endpointTransfer, Matrix.mulVec,
        Matrix.mul_apply, Matrix.dotProduct, Fin.sum_univ_succ]
  all_goals norm_num

/-- The increasing mortal orbit obeys the same content-free recurrence. -/
theorem increasingMortal_cumulativeExecution :
    CumulativeEndpointExecution 5 2 (-57803) 403 10304 [2, 3]
      (-67704, 1) (0, 41664) := by
  exact .cons (middle := (7041216, -504)) (by constructor <;> norm_num)
    (.cons (by constructor <;> norm_num) (.nil _))

/-- The rational period-three orbit is an integral projective cycle: after waits `1, 2, 3`,
the cumulative pair returns to its initial ray with scale `-15411200`. -/
theorem cycle_cumulativeExecution :
    CumulativeEndpointExecution 3 2 (-953) 473 2240 [1, 2, 3]
      (-2720, 1) (41918464000, -15411200) := by
  exact .cons (middle := (1267840, -800)) (by constructor <;> norm_num)
    (.cons (middle := (-15411200, 192640)) (by constructor <;> norm_num)
      (.cons (by constructor <;> norm_num) (.nil _)))

theorem cycle_cumulativeTarget_eq_scaledReset :
    (41918464000, -15411200) =
      ((-15411200 : ℤ) * (-2720), (-15411200 : ℤ) * 1) := by
  norm_num

private theorem val3_threeReturn_center :
    padicValRat 3 (122753 / 39232 : ℚ) = 0 := by
  rw [show (122753 / 39232 : ℚ) =
    (3 : ℚ) ^ 0 * 122753 / 39232 by norm_num]
  exact val3_scaled_fraction 0 122753 39232
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem val3_threeReturn_center_sub_one :
    padicValRat 3 (83521 / 39232 : ℚ) = 0 := by
  rw [show (83521 / 39232 : ℚ) =
    (3 : ℚ) ^ 0 * 83521 / 39232 by norm_num]
  exact val3_scaled_fraction 0 83521 39232
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem val3_threeReturn_reset :
    padicValRat 3 (7671 / 2452 : ℚ) = 1 := by
  rw [show (7671 / 2452 : ℚ) =
    (3 : ℚ) ^ 1 * 2557 / 2452 by norm_num]
  exact val3_scaled_fraction 1 2557 2452
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- A lawful depth-two guard whose unique terminal schedule has three positive returns. -/
def threeReturnParameters : Parameters where
  prime := 3
  prime_prime := three_prime
  depth := 2
  depth_two := by norm_num
  center := 122753 / 39232
  reset := 7671 / 2452
  center_unit := ⟨by norm_num, val3_threeReturn_center⟩
  center_sub_one_unit := ⟨by norm_num, by
    norm_num only [div_sub_one]
    exact val3_threeReturn_center_sub_one⟩
  reset_positive := ⟨by norm_num, by
    rw [val3_threeReturn_reset]
    norm_num⟩

/-- The submitted three-return endpoint product reaches the terminal hyperplane exactly. -/
theorem threeReturn_endpointTerminalWord :
    EndpointTerminalWord 3 2 122753 (-17) 39232 [1, 1, 1] := by
  norm_num [EndpointTerminalWord, endpointProduct, endpointTransfer,
    Matrix.mulVec, Matrix.dotProduct, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Every positive endpoint word for these coefficients is terminal exactly when it is the
three-letter schedule `[1, 1, 1]`; in particular no one- or two-return bound is possible. -/
theorem threeReturn_endpointTerminalWord_iff
    {waits : List Nat} (positive : PositiveAddress waits) :
    EndpointTerminalWord 3 2 122753 (-17) 39232 waits ↔
      waits = [1, 1, 1] := by
  constructor
  · intro terminal
    exact endpointTerminalWord_unique threeReturnParameters
      (by norm_num [threeReturnParameters])
      (by norm_num [threeReturnParameters, drift]) (by norm_num)
      positive (by simp [PositiveAddress]) terminal threeReturn_endpointTerminalWord
  · rintro rfl
    exact threeReturn_endpointTerminalWord

/-- The unique three-return endpoint word is a genuine mortality witness for the rational
rank-`(3,2)` pair. -/
theorem threeReturn_physical_isMortal :
    IsMortal
      (ReturnFamily.pairGenerator
        (ambient (3 : ℚ) 2)
        (cut (122753 / 39232) (7671 / 2452))) := by
  apply
    (physical_isMortal_iff_endpointTerminalWord threeReturnParameters
      (centerNumerator := 122753) (driftNumerator := -17) (scale := 39232)
      (by norm_num [threeReturnParameters])
      (by norm_num [threeReturnParameters, drift]) (by norm_num)).2
  exact ⟨[1, 1, 1], by simp, by simp [PositiveAddress],
    threeReturn_endpointTerminalWord⟩

/-- A reset-terminal step can have a same-address primitive companion whose complementary
reverse content is arbitrarily smaller than the terminal step's forward content.  The exterior
displacement of the two sources is the exact square `-9(12n+1)²`; hence neither terminal
anchoring nor one-step shadow comparison gives a monotone contraction. -/
theorem resetCompanion_counterfamily
    (n : ℤ) (n_positive : 0 < n) :
    let c := 24 * n + 1
    let reset := 24 * n + 2
    let halfScale := (12 * n + 1) * (108 * n + 5)
    let scale := 2 * halfScale
    PrimitiveEndpointReduction 3 2 (scale + 1) c scale 1
        (reset, 1) (0, 1) (-c * reset) ∧
      PrimitiveEndpointReduction 3 2 (scale + 1) c scale 1
        (halfScale, -2) (reset, 1) halfScale ∧
      (-c * reset) * (-(9 * c + 1)) = c * scale * (3 ^ 1 - 1) ∧
      halfScale * (4 * c) = c * scale * (3 ^ 1 - 1) ∧
      projectivePairCross (reset, 1) (halfScale, -2) =
        -9 * (12 * n + 1) ^ 2 ∧
      2 * (c * reset) = (4 * c) * (12 * n + 1) ∧
      4 * c < c * reset := by
  dsimp
  constructor
  · refine ⟨⟨0, 1, by ring⟩, ⟨0, 1, by ring⟩, by norm_num, ?_, ?_⟩
    · have c_positive : 0 < 24 * n + 1 := by omega
      have reset_positive : 0 < 24 * n + 2 := by omega
      exact mul_ne_zero (neg_ne_zero.mpr (ne_of_gt c_positive))
        (ne_of_gt reset_positive)
    · constructor <;> ring
  constructor
  · refine ⟨?_, ⟨0, 1, by ring⟩, by norm_num, ?_, ?_⟩
    · refine ⟨1, 648 * n ^ 2 + 84 * n + 2, ?_⟩
      ring
    · have left_positive : 0 < 12 * n + 1 := by omega
      have right_positive : 0 < 108 * n + 5 := by omega
      exact mul_ne_zero (ne_of_gt left_positive) (ne_of_gt right_positive)
    · constructor <;> ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · simp [projectivePairCross]
    ring
  constructor
  · ring
  · nlinarith

end
end MatrixMortality.ReturnGuard.Examples
