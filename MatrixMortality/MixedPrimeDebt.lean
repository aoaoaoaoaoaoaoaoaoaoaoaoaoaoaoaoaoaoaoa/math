import MatrixMortality.PeriodicShell

/-!
# Mixed-prime debt chamber

The critical-shell map has exact one-counter dynamics whenever its state has negative
three-adic valuation.  This file exposes that chamber without imposing an artificial integral
carrier: the carrier is a rational unit at three and five.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation
open PeriodicShell

private local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
private local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private theorem unit_pow
    {prime : ℕ} [Fact prime.Prime] {value : ℚ}
    (value_unit : IsUnit prime value) (exponent : ℕ) :
    IsUnit prime (value ^ exponent) := by
  refine ⟨pow_ne_zero exponent value_unit.1, ?_⟩
  rw [padicValRat.pow, value_unit.2]
  simp

private theorem hasValue_pow
    {prime : ℕ} [Fact prime.Prime] {value : ℚ} {valuation : ℤ}
    (value_hasValue : HasValue prime value valuation) (exponent : ℕ) :
    HasValue prime (value ^ exponent) (exponent * valuation) := by
  refine ⟨pow_ne_zero exponent value_hasValue.1, ?_⟩
  rw [padicValRat.pow, value_hasValue.2]

/-- One guarded-shell wait, written independently of its raw two-letter factorization. -/
def shellStep (wait : ℕ) (state : ℚ) : ℚ :=
  (3 * (2 / 3) ^ wait * state + 1) / 5

/-- Rational carrier coordinates for a point at three-adic depth `depth`. -/
def debtState (carrier : ℚ) (depth : ℕ) : ℚ :=
  carrier / 3 ^ depth

/-- Counter update in the uninterrupted three-adic debt chamber. -/
def debtNextDepth (depth wait : ℕ) : ℕ :=
  depth + wait - 1

/-- Carrier update paired with `debtNextDepth`. -/
def debtNextCarrier (carrier : ℚ) (depth wait : ℕ) : ℚ :=
  (2 ^ wait * carrier + 3 ^ debtNextDepth depth wait) / 5

/-- Reverse carrier forced by a target debt state and one proposed wait. -/
def debtPredecessorCarrier (target : ℚ) (targetDepth wait : ℕ) : ℚ :=
  (5 * target - 3 ^ targetDepth) / 2 ^ wait

/-- Reverse depth forced by a target debt state and one proposed wait. -/
def debtPredecessorDepth (targetDepth wait : ℕ) : ℕ :=
  targetDepth + 1 - wait

/-- Depth reached by an uninterrupted debt-chamber schedule. -/
def debtRunDepth : ℕ → List ℕ → ℕ
  | depth, [] => depth
  | depth, wait :: waits => debtRunDepth (debtNextDepth depth wait) waits

/-- Carrier reached by the debt recurrence along a schedule. -/
def debtRunCarrier : ℚ → ℕ → List ℕ → ℚ
  | carrier, _, [] => carrier
  | carrier, depth, wait :: waits =>
      debtRunCarrier (debtNextCarrier carrier depth wait)
        (debtNextDepth depth wait) waits

/-- Every post-step depth of the schedule remains strictly inside the debt chamber. -/
def DebtSafe : ℕ → List ℕ → Prop
  | _, [] => True
  | depth, wait :: waits =>
      0 < debtNextDepth depth wait ∧ DebtSafe (debtNextDepth depth wait) waits

/-- Linear coefficient of one shell schedule. -/
def shellSlope (waits : List ℕ) : ℚ :=
  (waits.map shellScale).prod / 5 ^ waits.length

/-- A singleton schedule is one shell step. -/
theorem shellRun_singleton (wait : ℕ) (state : ℚ) :
    shellRun [wait] state = shellStep wait state := by
  rfl

/-- Below the two-adic wall `v₂(state)+wait=0`, the incoming debt survives exactly. -/
theorem shellStep_two_belowWall
    (wait : ℕ) {state : ℚ} {stateValue : ℤ}
    (state_value : HasValue 2 state stateValue)
    (below_wall : stateValue + wait < 0) :
    HasValue 2 (shellStep wait state) (stateValue + wait) := by
  have two_value : HasValue 2 (2 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 2) 1)
  have three_unit : IsUnit 2 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have five_unit : IsUnit 2 (5 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have ratio_value : HasValue 2 ((2 : ℚ) / 3) 1 := by
    simpa using div_hasValue two_value three_unit
  have scale_value : HasValue 2 (3 * (2 / 3 : ℚ) ^ wait) wait := by
    simpa using mul_hasValue three_unit (hasValue_pow ratio_value wait)
  have leading_value :
      HasValue 2 (3 * (2 / 3 : ℚ) ^ wait * state) (stateValue + wait) := by
    simpa [add_comm] using mul_hasValue scale_value state_value
  have numerator_value := add_hasValue_left leading_value
    (show IsUnit 2 (1 : ℚ) from ⟨one_ne_zero, padicValRat.one⟩) below_wall
  simpa [shellStep] using div_hasValue numerator_value five_unit

/-- Above the two-adic wall, the unit summand clears all incoming two-debt. -/
theorem shellStep_two_aboveWall
    (wait : ℕ) {state : ℚ} {stateValue : ℤ}
    (state_value : HasValue 2 state stateValue)
    (above_wall : 0 < stateValue + wait) :
    IsUnit 2 (shellStep wait state) := by
  have two_value : HasValue 2 (2 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 2) 1)
  have three_unit : IsUnit 2 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have five_unit : IsUnit 2 (5 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have ratio_value : HasValue 2 ((2 : ℚ) / 3) 1 := by
    simpa using div_hasValue two_value three_unit
  have scale_value : HasValue 2 (3 * (2 / 3 : ℚ) ^ wait) wait := by
    simpa using mul_hasValue three_unit (hasValue_pow ratio_value wait)
  have leading_value :
      HasValue 2 (3 * (2 / 3 : ℚ) ^ wait * state) (stateValue + wait) := by
    simpa [add_comm] using mul_hasValue scale_value state_value
  have numerator_value := add_hasValue_right leading_value
    (show IsUnit 2 (1 : ℚ) from ⟨one_ne_zero, padicValRat.one⟩) above_wall
  simpa [shellStep] using div_hasValue numerator_value five_unit

/-- Below the three-adic wall `v₃(state)+1−wait=0`, the chosen wait creates or deepens debt. -/
theorem shellStep_three_belowWall
    (wait : ℕ) {state : ℚ} {stateValue : ℤ}
    (state_value : HasValue 3 state stateValue)
    (below_wall : stateValue + 1 - wait < 0) :
    HasValue 3 (shellStep wait state) (stateValue + 1 - wait) := by
  have two_unit : IsUnit 3 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have three_value : HasValue 3 (3 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 3) 1)
  have five_unit : IsUnit 3 (5 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have ratio_value : HasValue 3 ((2 : ℚ) / 3) (-1) := by
    simpa using div_hasValue two_unit three_value
  have scale_value : HasValue 3 (3 * (2 / 3 : ℚ) ^ wait) (1 - wait) := by
    simpa [sub_eq_add_neg] using mul_hasValue three_value (hasValue_pow ratio_value wait)
  have leading_value :
      HasValue 3 (3 * (2 / 3 : ℚ) ^ wait * state) (stateValue + 1 - wait) := by
    simpa only [add_sub_assoc, add_comm, add_left_comm] using
      mul_hasValue scale_value state_value
  have numerator_value := add_hasValue_left leading_value
    (show IsUnit 3 (1 : ℚ) from ⟨one_ne_zero, padicValRat.one⟩) below_wall
  simpa [shellStep] using div_hasValue numerator_value five_unit

/-- Above the three-adic wall, the unit summand clears all incoming three-credit. -/
theorem shellStep_three_aboveWall
    (wait : ℕ) {state : ℚ} {stateValue : ℤ}
    (state_value : HasValue 3 state stateValue)
    (above_wall : 0 < stateValue + 1 - wait) :
    IsUnit 3 (shellStep wait state) := by
  have two_unit : IsUnit 3 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have three_value : HasValue 3 (3 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 3) 1)
  have five_unit : IsUnit 3 (5 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have ratio_value : HasValue 3 ((2 : ℚ) / 3) (-1) := by
    simpa using div_hasValue two_unit three_value
  have scale_value : HasValue 3 (3 * (2 / 3 : ℚ) ^ wait) (1 - wait) := by
    simpa [sub_eq_add_neg] using mul_hasValue three_value (hasValue_pow ratio_value wait)
  have leading_value :
      HasValue 3 (3 * (2 / 3 : ℚ) ^ wait * state) (stateValue + 1 - wait) := by
    simpa only [add_sub_assoc, add_comm, add_left_comm] using
      mul_hasValue scale_value state_value
  have numerator_value := add_hasValue_right leading_value
    (show IsUnit 3 (1 : ℚ) from ⟨one_ne_zero, padicValRat.one⟩) above_wall
  simpa [shellStep] using div_hasValue numerator_value five_unit

/-- Away from the unique zero-depth boundary, one shell step is exactly the debt-counter
recurrence `d' = d + m - 1`, `c' = (2^m c + 3^d') / 5`. -/
theorem shellStep_debtState
    (carrier : ℚ) (depth wait : ℕ) (depth_wait_positive : 0 < depth + wait) :
    shellStep wait (debtState carrier depth) =
      debtState (debtNextCarrier carrier depth wait) (debtNextDepth depth wait) := by
  have depth_wait : debtNextDepth depth wait + 1 = depth + wait := by
    simp only [debtNextDepth]
    omega
  have scale_eq :
      3 * (2 / 3 : ℚ) ^ wait * 3 ^ debtNextDepth depth wait =
        3 ^ depth * 2 ^ wait := by
    rw [div_pow]
    field_simp
    have depth_wait' : debtNextDepth depth wait + 1 = wait + depth := by omega
    rw [← pow_add, ← depth_wait', pow_succ]
    ring
  simp only [shellStep, debtState, debtNextCarrier]
  field_simp
  calc
    (3 * (2 / 3) ^ wait * carrier + 3 ^ depth) *
          3 ^ debtNextDepth depth wait =
        (3 * (2 / 3) ^ wait * 3 ^ debtNextDepth depth wait) * carrier +
          3 ^ depth * 3 ^ debtNextDepth depth wait := by ring
    _ = 3 ^ depth * (carrier * 2 ^ wait + 3 ^ debtNextDepth depth wait) := by
      rw [scale_eq]
      ring

/-- A unit carrier at three has exactly the advertised negative valuation after division by the
depth power. -/
theorem debtState_hasValue_three (carrier : ℚ) (depth : ℕ)
    (carrier_unit : IsUnit 3 carrier) :
    HasValue 3 (debtState carrier depth) (-(depth : ℤ)) := by
  simpa [debtState] using
    div_hasValue carrier_unit (primePower_hasValue (prime := 3) depth)

/-- A five-adic unit carrier remains a unit after three-power depth normalization. -/
theorem debtState_fiveUnit (carrier : ℚ) (depth : ℕ)
    (carrier_unit : IsUnit 5 carrier) :
    IsUnit 5 (debtState carrier depth) := by
  have three_unit : IsUnit 5 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  simpa [debtState] using div_hasValue carrier_unit (unit_pow three_unit depth)

/-- Inside the chamber, the updated carrier remains a three-adic unit. -/
theorem debtNextCarrier_threeUnit
    (carrier : ℚ) (depth wait : ℕ) (carrier_unit : IsUnit 3 carrier)
    (nextDepth_positive : 0 < debtNextDepth depth wait) :
    IsUnit 3 (debtNextCarrier carrier depth wait) := by
  have two_unit : IsUnit 3 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have five_unit : IsUnit 3 (5 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have leading_unit : IsUnit 3 ((2 : ℚ) ^ wait * carrier) :=
    mul_hasValue (unit_pow two_unit wait) carrier_unit
  have depth_positive : IsPositive 3 ((3 : ℚ) ^ debtNextDepth depth wait) := by
    have depth_value := primePower_hasValue (prime := 3) (debtNextDepth depth wait)
    refine ⟨depth_value.1, ?_⟩
    have valuation_eq := depth_value.2
    exact valuation_eq ▸ (by exact_mod_cast nextDepth_positive)
  exact div_hasValue (unit_add_positive leading_unit depth_positive) five_unit

/-- Every uninterrupted debt step has depth `d + m - 1`; no cancellation can alter it. -/
theorem shellStep_threeDebt
    (carrier : ℚ) (depth wait : ℕ) (carrier_unit : IsUnit 3 carrier)
    (nextDepth_positive : 0 < debtNextDepth depth wait)
    (depth_wait_positive : 0 < depth + wait) :
    HasValue 3 (shellStep wait (debtState carrier depth))
      (-(debtNextDepth depth wait : ℤ)) := by
  rw [shellStep_debtState carrier depth wait depth_wait_positive]
  exact debtState_hasValue_three _ _
    (debtNextCarrier_threeUnit carrier depth wait carrier_unit nextDepth_positive)

/-- The sole boundary step out of depth one is an ordinary unit-plus-one division. -/
theorem shellStep_debtBoundary (carrier : ℚ) :
    shellStep 0 (debtState carrier 1) = (carrier + 1) / 5 := by
  norm_num [shellStep, debtState]
  field_simp

private theorem unit_add_one_not_negative
    (carrier : ℚ) (carrier_unit : IsUnit 3 carrier) :
    ¬IsNegative 3 (carrier + 1) := by
  intro sum_negative
  have lower := padicValRat.min_le_padicValRat_add (p := 3) sum_negative.1
  rw [carrier_unit.2, padicValRat.one, min_self] at lower
  exact (not_lt_of_ge lower) sum_negative.2

/-- The boundary step cannot remain at negative three-adic valuation. -/
theorem shellStep_debtBoundary_not_negative
    (carrier : ℚ) (carrier_unit : IsUnit 3 carrier) :
    ¬IsNegative 3 (shellStep 0 (debtState carrier 1)) := by
  intro output_negative
  have five_unit : IsUnit 3 (5 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have output_value :
      HasValue 3 (shellStep 0 (debtState carrier 1))
        (padicValRat 3 (shellStep 0 (debtState carrier 1))) :=
    ⟨output_negative.1, rfl⟩
  have product_value := mul_hasValue five_unit output_value
  apply unit_add_one_not_negative carrier carrier_unit
  have product_eq :
      5 * shellStep 0 (debtState carrier 1) = carrier + 1 := by
    rw [shellStep_debtBoundary]
    ring
  rw [← product_eq]
  exact ⟨product_value.1, by
    rw [product_value.2]
    simpa using output_negative.2⟩

/-- A shell step has nonzero slope, hence is injective for each fixed wait. -/
theorem shellStep_injective (wait : ℕ) : Function.Injective (shellStep wait) := by
  intro left right equal
  have scale_ne : (3 * (2 / 3 : ℚ) ^ wait) ≠ 0 := by positivity
  dsimp only [shellStep] at equal
  apply (mul_left_cancel₀ scale_ne)
  linarith

/-- Every proposed wait not exceeding the target depth has one explicit predecessor in the debt
chamber. -/
theorem shellStep_debtPredecessor
    (target : ℚ) (targetDepth wait : ℕ) (wait_le_depth : wait ≤ targetDepth) :
    shellStep wait
        (debtState (debtPredecessorCarrier target targetDepth wait)
          (debtPredecessorDepth targetDepth wait)) =
      debtState target targetDepth := by
  have predecessorDepth_wait :
      debtPredecessorDepth targetDepth wait + wait = targetDepth + 1 := by
    simp only [debtPredecessorDepth]
    omega
  have depth_wait_positive :
      0 < debtPredecessorDepth targetDepth wait + wait := by omega
  rw [shellStep_debtState _ _ _ depth_wait_positive]
  have nextDepth :
      debtNextDepth (debtPredecessorDepth targetDepth wait) wait = targetDepth := by
    simp only [debtNextDepth]
    omega
  rw [nextDepth]
  simp only [debtState, debtNextCarrier, debtPredecessorCarrier, nextDepth]
  field_simp
  ring

/-- The predecessor fan is complete: an equality between two negative-depth states forces the
wait into `0,…,targetDepth` and forces the displayed predecessor carrier. -/
theorem shellStep_debtState_eq_iff
    (source target : ℚ) (sourceDepth targetDepth wait : ℕ)
    (source_unit : IsUnit 3 source) (target_unit : IsUnit 3 target)
    (sourceDepth_positive : 0 < sourceDepth) (targetDepth_positive : 0 < targetDepth) :
    shellStep wait (debtState source sourceDepth) = debtState target targetDepth ↔
      sourceDepth + wait = targetDepth + 1 ∧
        source = debtPredecessorCarrier target targetDepth wait := by
  constructor
  · intro step_eq
    have depth_wait_positive : 0 < sourceDepth + wait := by omega
    have nextDepth_cases :
        debtNextDepth sourceDepth wait = 0 ∨
          0 < debtNextDepth sourceDepth wait := by omega
    rcases nextDepth_cases with nextDepth_zero | nextDepth_positive
    · have sourceDepth_eq : sourceDepth = 1 := by
        simp only [debtNextDepth] at nextDepth_zero
        omega
      have wait_eq : wait = 0 := by
        simp only [debtNextDepth] at nextDepth_zero
        omega
      subst sourceDepth
      subst wait
      have target_value := debtState_hasValue_three target targetDepth target_unit
      have target_negative : IsNegative 3 (debtState target targetDepth) :=
        ⟨target_value.1, by rw [target_value.2]; omega⟩
      have output_negative : IsNegative 3 (shellStep 0 (debtState source 1)) := by
        rw [step_eq]
        exact target_negative
      exact (shellStep_debtBoundary_not_negative source source_unit output_negative).elim
    · have source_value := shellStep_threeDebt source sourceDepth wait source_unit
        nextDepth_positive depth_wait_positive
      have target_value := debtState_hasValue_three target targetDepth target_unit
      have valuation_eq := congrArg (padicValRat 3) step_eq
      rw [source_value.2, target_value.2] at valuation_eq
      have depth_eq : debtNextDepth sourceDepth wait = targetDepth := by omega
      have depth_balance : sourceDepth + wait = targetDepth + 1 := by
        simp only [debtNextDepth] at depth_eq
        omega
      have wait_le_depth : wait ≤ targetDepth := by omega
      have predecessor_eq :=
        shellStep_debtPredecessor target targetDepth wait wait_le_depth
      have states_eq :
          debtState source sourceDepth =
            debtState (debtPredecessorCarrier target targetDepth wait)
              (debtPredecessorDepth targetDepth wait) :=
        shellStep_injective wait (step_eq.trans predecessor_eq.symm)
      have predecessorDepth_eq :
          debtPredecessorDepth targetDepth wait = sourceDepth := by
        simp only [debtPredecessorDepth]
        omega
      rw [predecessorDepth_eq] at states_eq
      have denominator_ne : (3 : ℚ) ^ sourceDepth ≠ 0 := by positivity
      refine ⟨depth_balance, ?_⟩
      exact (div_left_inj' denominator_ne).mp states_eq
  · rintro ⟨depth_balance, source_eq⟩
    have wait_le_depth : wait ≤ targetDepth := by omega
    have predecessorDepth_eq :
        debtPredecessorDepth targetDepth wait = sourceDepth := by
      simp only [debtPredecessorDepth]
      omega
    rw [source_eq, ← predecessorDepth_eq]
    exact shellStep_debtPredecessor target targetDepth wait wait_le_depth

/-- Reverse debt predecessors keep a three-adic unit carrier. -/
theorem debtPredecessorCarrier_threeUnit
    (target : ℚ) (targetDepth wait : ℕ) (target_unit : IsUnit 3 target)
    (targetDepth_positive : 0 < targetDepth) :
    IsUnit 3 (debtPredecessorCarrier target targetDepth wait) := by
  have two_unit : IsUnit 3 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have five_unit : IsUnit 3 (5 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have leading_unit : IsUnit 3 (5 * target) := mul_hasValue five_unit target_unit
  have depth_positive : IsPositive 3 ((3 : ℚ) ^ targetDepth) := by
    have depth_value := primePower_hasValue (prime := 3) targetDepth
    refine ⟨depth_value.1, ?_⟩
    have valuation_eq := depth_value.2
    exact valuation_eq ▸ (by exact_mod_cast targetDepth_positive)
  exact div_hasValue (unit_sub_positive leading_unit depth_positive)
    (unit_pow two_unit wait)

/-- Reverse debt predecessors also keep a five-adic unit carrier. -/
theorem debtPredecessorCarrier_fiveUnit
    (target : ℚ) (targetDepth wait : ℕ) (target_unit : IsUnit 5 target) :
    IsUnit 5 (debtPredecessorCarrier target targetDepth wait) := by
  have two_unit : IsUnit 5 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have three_unit : IsUnit 5 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have five_value : HasValue 5 (5 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 5) 1)
  have leading_positive : IsPositive 5 (5 * target) := by
    have leading_value := mul_hasValue five_value target_unit
    exact ⟨leading_value.1, by rw [leading_value.2]; norm_num⟩
  have depth_unit : IsUnit 5 ((3 : ℚ) ^ targetDepth) := unit_pow three_unit targetDepth
  have numerator_unit : IsUnit 5 (5 * target - 3 ^ targetDepth) := by
    have opposite := unit_sub_positive depth_unit leading_positive
    simpa only [neg_sub] using neg_hasValue opposite
  exact div_hasValue numerator_unit (unit_pow two_unit wait)

/-- A target at depth `d` has one legal debt predecessor for each wait `0,…,d`; every such
predecessor stays in both the three-adic debt chamber and the five-adic shell. -/
theorem debtPredecessor_fan
    (target : ℚ) (targetDepth wait : ℕ)
    (target_threeUnit : IsUnit 3 target) (target_fiveUnit : IsUnit 5 target)
    (targetDepth_positive : 0 < targetDepth) (wait_le_depth : wait ≤ targetDepth) :
    0 < debtPredecessorDepth targetDepth wait ∧
      IsUnit 3 (debtPredecessorCarrier target targetDepth wait) ∧
      IsUnit 5 (debtPredecessorCarrier target targetDepth wait) ∧
      shellStep wait
          (debtState (debtPredecessorCarrier target targetDepth wait)
            (debtPredecessorDepth targetDepth wait)) =
        debtState target targetDepth := by
  refine ⟨by simp only [debtPredecessorDepth]; omega,
    debtPredecessorCarrier_threeUnit target targetDepth wait target_threeUnit
      targetDepth_positive,
    debtPredecessorCarrier_fiveUnit target targetDepth wait target_fiveUnit,
    shellStep_debtPredecessor target targetDepth wait wait_le_depth⟩

/-- Distinct waits in the complete predecessor fan produce distinct source states. -/
theorem debtPredecessor_state_injective
    (target : ℚ) (targetDepth : ℕ) (target_unit : IsUnit 3 target)
    (targetDepth_positive : 0 < targetDepth)
    {left right : ℕ} (left_le_depth : left ≤ targetDepth)
    (right_le_depth : right ≤ targetDepth)
    (states_eq :
      debtState (debtPredecessorCarrier target targetDepth left)
          (debtPredecessorDepth targetDepth left) =
        debtState (debtPredecessorCarrier target targetDepth right)
          (debtPredecessorDepth targetDepth right)) :
    left = right := by
  let source :=
    debtState (debtPredecessorCarrier target targetDepth left)
      (debtPredecessorDepth targetDepth left)
  have left_map := shellStep_debtPredecessor target targetDepth left left_le_depth
  have right_map := shellStep_debtPredecessor target targetDepth right right_le_depth
  rw [← states_eq] at right_map
  have steps_eq : shellStep left source = shellStep right source :=
    left_map.trans right_map.symm
  have sourceDepth_positive : 0 < debtPredecessorDepth targetDepth left := by
    simp only [debtPredecessorDepth]
    omega
  have sourceCarrier_unit := debtPredecessorCarrier_threeUnit target targetDepth left
    target_unit targetDepth_positive
  have source_value := debtState_hasValue_three
    (debtPredecessorCarrier target targetDepth left)
    (debtPredecessorDepth targetDepth left) sourceCarrier_unit
  have source_ne : source ≠ 0 := source_value.1
  have scaled_eq : (2 / 3 : ℚ) ^ left * source = (2 / 3 : ℚ) ^ right * source := by
    dsimp only [shellStep] at steps_eq
    linarith
  have powers_eq : (2 / 3 : ℚ) ^ left = (2 / 3 : ℚ) ^ right :=
    (mul_right_cancel₀ source_ne) scaled_eq
  exact pow_right_injective₀ (by norm_num : (0 : ℚ) < 2 / 3) (by norm_num) powers_eq

/-- The debt recurrence computes every uninterrupted schedule, not merely a fixed or periodic
one. -/
theorem shellRun_debtSafe
    (waits : List ℕ) (carrier : ℚ) (depth : ℕ)
    (carrier_unit : IsUnit 3 carrier) (depth_positive : 0 < depth)
    (safe : DebtSafe depth waits) :
    IsUnit 3 (debtRunCarrier carrier depth waits) ∧
      shellRun waits (debtState carrier depth) =
        debtState (debtRunCarrier carrier depth waits) (debtRunDepth depth waits) := by
  induction waits generalizing carrier depth with
  | nil =>
      exact ⟨carrier_unit, rfl⟩
  | cons wait waits induction =>
      have nextDepth_positive : 0 < debtNextDepth depth wait := safe.1
      have depth_wait_positive : 0 < depth + wait := by omega
      have nextCarrier_unit : IsUnit 3 (debtNextCarrier carrier depth wait) :=
        debtNextCarrier_threeUnit carrier depth wait carrier_unit nextDepth_positive
      have tail := induction (debtNextCarrier carrier depth wait)
        (debtNextDepth depth wait) nextCarrier_unit nextDepth_positive safe.2
      refine ⟨tail.1, ?_⟩
      rw [show wait :: waits = [wait] ++ waits by rfl, shellRun_append,
        shellRun_singleton, shellStep_debtState carrier depth wait depth_wait_positive,
        tail.2]
      rfl

/-- A debt-safe schedule is a Łukasiewicz bridge: its total wait is determined by its length and
the two endpoint depths. -/
theorem debtRunDepth_balance
    (waits : List ℕ) (depth : ℕ) (safe : DebtSafe depth waits) :
    debtRunDepth depth waits + waits.length = depth + waits.sum := by
  induction waits generalizing depth with
  | nil => simp [debtRunDepth]
  | cons wait waits induction =>
      have nextDepth_positive : 0 < debtNextDepth depth wait := safe.1
      have step_balance : debtNextDepth depth wait + 1 = depth + wait := by
        simp only [debtNextDepth] at nextDepth_positive ⊢
        omega
      have tail := induction (debtNextDepth depth wait) safe.2
      simp only [debtRunDepth, List.length_cons, List.sum_cons]
      omega

/-- Every debt-safe schedule ends at the depth prescribed by its total wait and length. -/
theorem debtRunDepth_eq_of_balance
    (waits : List ℕ) (startDepth endDepth : ℕ) (safe : DebtSafe startDepth waits)
    (ends_at : debtRunDepth startDepth waits = endDepth) :
    endDepth + waits.length = startDepth + waits.sum := by
  rw [← ends_at]
  exact debtRunDepth_balance waits startDepth safe

/-- The displacement between two trajectories following one schedule is multiplied by its
exact shell slope. -/
theorem shellRun_sub_shellRun (waits : List ℕ) (left right : ℚ) :
    shellRun waits left - shellRun waits right = shellSlope waits * (left - right) := by
  induction waits generalizing left right with
  | nil =>
      have left_nil : shellRun [] left = left := rfl
      have right_nil : shellRun [] right = right := rfl
      rw [left_nil, right_nil]
      simp [shellSlope]
  | cons wait waits induction =>
      have left_run :
          shellRun (wait :: waits) left = shellRun waits (shellStep wait left) := by
        rw [show wait :: waits = [wait] ++ waits by rfl, shellRun_append,
          shellRun_singleton]
      have right_run :
          shellRun (wait :: waits) right = shellRun waits (shellStep wait right) := by
        rw [show wait :: waits = [wait] ++ waits by rfl, shellRun_append,
          shellRun_singleton]
      rw [left_run, right_run, induction]
      simp only [shellSlope, List.map_cons, List.prod_cons, List.length_cons, pow_succ]
      dsimp only [shellStep, shellScale]
      ring

/-- The slope remembers only schedule length and total wait. -/
theorem shellSlope_eq_length_sum (waits : List ℕ) :
    shellSlope waits =
      3 ^ waits.length * (2 / 3 : ℚ) ^ waits.sum / 5 ^ waits.length := by
  simp only [shellSlope]
  congr 1
  induction waits with
  | nil => simp
  | cons wait waits induction =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, List.sum_cons, shellScale,
        induction, pow_succ, pow_add]
      ring

/-- Equal length and equal total wait force equal shell slopes. -/
theorem shellSlope_eq_of_length_sum
    {left right : List ℕ} (length_eq : left.length = right.length)
    (sum_eq : left.sum = right.sum) :
    shellSlope left = shellSlope right := by
  rw [shellSlope_eq_length_sum, shellSlope_eq_length_sum, length_eq, sum_eq]

/-- Within fixed debt endpoints and fixed length, a point collision is already a global affine
relation. Source-specific collisions can occur only across different lengths. -/
theorem debtSafe_sameLength_collision_global
    {left right : List ℕ} {startDepth endDepth : ℕ} {source : ℚ}
    (left_safe : DebtSafe startDepth left) (right_safe : DebtSafe startDepth right)
    (left_ends : debtRunDepth startDepth left = endDepth)
    (right_ends : debtRunDepth startDepth right = endDepth)
    (length_eq : left.length = right.length)
    (collision : shellRun left source = shellRun right source) :
    ∀ state, shellRun left state = shellRun right state := by
  have left_balance := debtRunDepth_eq_of_balance left startDepth endDepth
    left_safe left_ends
  have right_balance := debtRunDepth_eq_of_balance right startDepth endDepth
    right_safe right_ends
  have sum_eq : left.sum = right.sum := by omega
  have slope_eq : shellSlope left = shellSlope right :=
    shellSlope_eq_of_length_sum length_eq sum_eq
  intro state
  have left_displacement := shellRun_sub_shellRun left state source
  have right_displacement := shellRun_sub_shellRun right state source
  rw [slope_eq, collision] at left_displacement
  linarith

end MatrixMortality.MixedPrimeDebt
