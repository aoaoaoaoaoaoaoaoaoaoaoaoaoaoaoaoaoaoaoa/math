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

/-- Constant coefficient of one shell schedule. -/
def shellIntercept (waits : List ℕ) : ℚ :=
  shellRun waits 0

/-- Intercept with its forced five-power denominator cleared. -/
def shellOffset (waits : List ℕ) : ℚ :=
  5 ^ waits.length * shellIntercept waits

/-- Unique source where two shell schedules with different slopes collide. -/
def collisionSource (left right : List ℕ) : ℚ :=
  (shellIntercept right - shellIntercept left) / (shellSlope left - shellSlope right)

/-- A singleton schedule is one shell step. -/
theorem shellRun_singleton (wait : ℕ) (state : ℚ) :
    shellRun [wait] state = shellStep wait state := by
  rfl

/-- A schedule executes its first wait before its remaining tail. -/
theorem shellRun_cons (wait : ℕ) (waits : List ℕ) (state : ℚ) :
    shellRun (wait :: waits) state = shellRun waits (shellStep wait state) := by
  rw [show wait :: waits = [wait] ++ waits by rfl, shellRun_append, shellRun_singleton]

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

/-- Every shell schedule is its slope times the source plus its intercept. -/
theorem shellRun_eq_slope_mul_add_intercept (waits : List ℕ) (state : ℚ) :
    shellRun waits state = shellSlope waits * state + shellIntercept waits := by
  have displacement := shellRun_sub_shellRun waits state 0
  simpa [shellIntercept] using (sub_eq_iff_eq_add.mp displacement)

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

private theorem shellScale_fiveUnit (wait : ℕ) : IsUnit 5 (shellScale wait) := by
  have two_unit : IsUnit 5 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have three_unit : IsUnit 5 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  exact mul_hasValue three_unit (unit_pow (div_hasValue two_unit three_unit) wait)

/-- One shell step lowers every negative five-adic valuation by exactly one. -/
theorem shellStep_fiveNegative
    (wait : ℕ) {state : ℚ} {stateValue : ℤ}
    (state_value : HasValue 5 state stateValue) (state_negative : stateValue < 0) :
    HasValue 5 (shellStep wait state) (stateValue - 1) := by
  have scale_unit : IsUnit 5 (3 * (2 / 3 : ℚ) ^ wait) := shellScale_fiveUnit wait
  have leading_value :
      HasValue 5 (3 * (2 / 3 : ℚ) ^ wait * state) stateValue := by
    simpa using mul_hasValue scale_unit state_value
  have numerator_value := add_hasValue_left leading_value
    (show IsUnit 5 (1 : ℚ) from ⟨one_ne_zero, padicValRat.one⟩) state_negative
  have five_value : HasValue 5 (5 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 5) 1)
  simpa [shellStep] using div_hasValue numerator_value five_value

/-- A negative five-adic source loses one valuation unit per scheduled wait. -/
theorem shellRun_fiveNegative
    (waits : List ℕ) {state : ℚ} {stateValue : ℤ}
    (state_value : HasValue 5 state stateValue) (state_negative : stateValue < 0) :
    HasValue 5 (shellRun waits state) (stateValue - waits.length) := by
  induction waits generalizing state stateValue with
  | nil =>
      have run_nil : shellRun [] state = state := rfl
      rw [run_nil]
      simpa using state_value
  | cons wait waits induction =>
      have next_value := shellStep_fiveNegative wait state_value state_negative
      have next_negative : stateValue - 1 < 0 := by omega
      have tail := induction next_value next_negative
      rw [shellRun_cons]
      convert tail using 1
      simp
      ring

/-- A schedule slope has five-adic valuation equal to the negative schedule length. -/
theorem shellSlope_hasValue_five (waits : List ℕ) :
    HasValue 5 (shellSlope waits) (-(waits.length : ℤ)) := by
  have two_unit : IsUnit 5 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have three_unit : IsUnit 5 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have ratio_unit : IsUnit 5 ((2 : ℚ) / 3) := div_hasValue two_unit three_unit
  have numerator_unit :
      IsUnit 5 (3 ^ waits.length * (2 / 3 : ℚ) ^ waits.sum) :=
    mul_hasValue (unit_pow three_unit waits.length) (unit_pow ratio_unit waits.sum)
  have denominator_value : HasValue 5 ((5 : ℚ) ^ waits.length) waits.length :=
    primePower_hasValue waits.length
  rw [shellSlope_eq_length_sum]
  simpa using div_hasValue numerator_unit denominator_value

/-- Every nonempty schedule intercept has five-adic valuation equal to the negative schedule
length. -/
theorem shellIntercept_hasValue_five
    {waits : List ℕ} (waits_ne : waits ≠ []) :
    HasValue 5 (shellIntercept waits) (-(waits.length : ℤ)) := by
  obtain ⟨wait, waits, rfl⟩ := List.exists_cons_of_ne_nil waits_ne
  have first_value : HasValue 5 (shellStep wait 0) (-1) := by
    have five_value : HasValue 5 (5 : ℚ) 1 := by
      simpa using (primePower_hasValue (prime := 5) 1)
    simpa [shellStep] using
      div_hasValue (show IsUnit 5 (1 : ℚ) from ⟨one_ne_zero, padicValRat.one⟩) five_value
  have tail := shellRun_fiveNegative waits first_value (by norm_num)
  rw [shellIntercept, shellRun_cons]
  convert tail using 1
  simp
  ring

/-- Clearing the forced five-power denominator makes every nonempty schedule offset a
five-adic unit. -/
theorem shellOffset_fiveUnit {waits : List ℕ} (waits_ne : waits ≠ []) :
    IsUnit 5 (shellOffset waits) := by
  have power_value : HasValue 5 ((5 : ℚ) ^ waits.length) waits.length :=
    primePower_hasValue waits.length
  have intercept_value := shellIntercept_hasValue_five waits_ne
  simpa [shellOffset] using mul_hasValue power_value intercept_value

/-- The cleared offset is a suffix recurrence; the first wait does not enter it. -/
theorem shellOffset_cons (wait : ℕ) (waits : List ℕ) :
    shellOffset (wait :: waits) =
      3 ^ waits.length * (2 / 3 : ℚ) ^ waits.sum + 5 * shellOffset waits := by
  rw [shellOffset, List.length_cons, pow_succ, shellIntercept, shellRun_cons,
    shellRun_eq_slope_mul_add_intercept, shellSlope_eq_length_sum]
  simp only [shellStep, mul_zero, zero_add]
  rw [shellOffset]
  field_simp

/-- Different schedule lengths force different shell slopes. -/
theorem shellSlope_ne_of_length_ne
    {left right : List ℕ} (length_ne : left.length ≠ right.length) :
    shellSlope left ≠ shellSlope right := by
  apply ne_of_valuation_ne
  rw [(shellSlope_hasValue_five left).2, (shellSlope_hasValue_five right).2]
  omega

/-- The explicit collision source is where two different-slope schedules meet. -/
theorem shellRun_collisionSource
    (left right : List ℕ) (slope_ne : shellSlope left ≠ shellSlope right) :
    shellRun left (collisionSource left right) =
      shellRun right (collisionSource left right) := by
  rw [shellRun_eq_slope_mul_add_intercept, shellRun_eq_slope_mul_add_intercept]
  simp only [collisionSource]
  field_simp
  ring

/-- The common collision target is the affine determinant divided by the slope difference. -/
theorem shellRun_collisionSource_eq_targetQuotient
    (left right : List ℕ) (slope_ne : shellSlope left ≠ shellSlope right) :
    shellRun left (collisionSource left right) =
      (shellSlope left * shellIntercept right - shellSlope right * shellIntercept left) /
        (shellSlope left - shellSlope right) := by
  rw [shellRun_eq_slope_mul_add_intercept]
  simp only [collisionSource]
  field_simp
  ring

/-- A collision between different-slope schedules forces the explicit source. -/
theorem collisionSource_eq_of_shellRun_eq
    (left right : List ℕ) (slope_ne : shellSlope left ≠ shellSlope right)
    {source : ℚ} (collision : shellRun left source = shellRun right source) :
    collisionSource left right = source := by
  rw [shellRun_eq_slope_mul_add_intercept,
    shellRun_eq_slope_mul_add_intercept] at collision
  simp only [collisionSource]
  field_simp
  linarith

/-- The unique collision source of two nonempty unequal-length schedules is automatically a
five-adic unit. The source shell therefore cannot prune cross-length collisions. -/
theorem collisionSource_fiveUnit
    {left right : List ℕ} (left_ne : left ≠ []) (right_ne : right ≠ [])
    (length_ne : left.length ≠ right.length) :
    IsUnit 5 (collisionSource left right) := by
  have left_slope := shellSlope_hasValue_five left
  have right_slope := shellSlope_hasValue_five right
  have left_intercept := shellIntercept_hasValue_five left_ne
  have right_intercept := shellIntercept_hasValue_five right_ne
  have valuation_ne : -(left.length : ℤ) ≠ -(right.length : ℤ) := by omega
  have numerator_value := sub_hasValue_min right_intercept.1 left_intercept.1
    (by rw [right_intercept.2, left_intercept.2]; exact valuation_ne.symm)
  have denominator_value := sub_hasValue_min left_slope.1 right_slope.1
    (by rw [left_slope.2, right_slope.2]; exact valuation_ne)
  have numerator_value' :
      HasValue 5 (shellIntercept right - shellIntercept left)
        (min (-(right.length : ℤ)) (-(left.length : ℤ))) := by
    simpa [right_intercept.2, left_intercept.2] using numerator_value
  have denominator_value' :
      HasValue 5 (shellSlope left - shellSlope right)
        (min (-(left.length : ℤ)) (-(right.length : ℤ))) := by
    simpa [left_slope.2, right_slope.2] using denominator_value
  have quotient_value := div_hasValue numerator_value' denominator_value'
  simpa [collisionSource, min_comm] using quotient_value

/-- For unequal lengths, the common collision target is a five-adic unit exactly when the
affine determinant has valuation `−max(left.length, right.length)`. The displayed minimum of
the two negative lengths is that value. -/
theorem collisionTarget_fiveUnit_iff
    {left right : List ℕ} (length_ne : left.length ≠ right.length) :
    IsUnit 5 (shellRun left (collisionSource left right)) ↔
      HasValue 5
        (shellSlope left * shellIntercept right - shellSlope right * shellIntercept left)
        (min (-(left.length : ℤ)) (-(right.length : ℤ))) := by
  have slope_ne : shellSlope left ≠ shellSlope right :=
    shellSlope_ne_of_length_ne length_ne
  have left_slope := shellSlope_hasValue_five left
  have right_slope := shellSlope_hasValue_five right
  have valuation_ne : -(left.length : ℤ) ≠ -(right.length : ℤ) := by omega
  have denominator_min := sub_hasValue_min left_slope.1 right_slope.1
    (by rw [left_slope.2, right_slope.2]; exact valuation_ne)
  have denominator_value :
      HasValue 5 (shellSlope left - shellSlope right)
        (min (-(left.length : ℤ)) (-(right.length : ℤ))) := by
    simpa [left_slope.2, right_slope.2] using denominator_min
  have target_eq := shellRun_collisionSource_eq_targetQuotient left right slope_ne
  constructor
  · intro target_unit
    have product_value := mul_hasValue target_unit denominator_value
    have product_eq :
        shellRun left (collisionSource left right) *
            (shellSlope left - shellSlope right) =
          shellSlope left * shellIntercept right -
            shellSlope right * shellIntercept left := by
      rw [target_eq]
      exact div_mul_cancel₀ _ (sub_ne_zero.mpr slope_ne)
    rw [product_eq] at product_value
    simpa using product_value
  · intro determinant_value
    rw [target_eq]
    have quotient_value := div_hasValue determinant_value denominator_value
    simpa using quotient_value

/-- Two debt-safe bridges with the same endpoint depths and lengths differing by one have slopes
in the fixed ratio `2/5`. -/
theorem adjacentDebtBridge_slope
    {short long : List ℕ} {startDepth endDepth : ℕ}
    (short_safe : DebtSafe startDepth short) (long_safe : DebtSafe startDepth long)
    (short_ends : debtRunDepth startDepth short = endDepth)
    (long_ends : debtRunDepth startDepth long = endDepth)
    (length_eq : long.length = short.length + 1) :
    shellSlope long = (2 / 5 : ℚ) * shellSlope short := by
  have short_balance := debtRunDepth_eq_of_balance short startDepth endDepth
    short_safe short_ends
  have long_balance := debtRunDepth_eq_of_balance long startDepth endDepth
    long_safe long_ends
  have sum_eq : long.sum = short.sum + 1 := by omega
  rw [shellSlope_eq_length_sum, shellSlope_eq_length_sum, length_eq, sum_eq]
  simp only [pow_succ]
  ring

/-- For adjacent-length debt bridges with common endpoint depths, the collision target is the
difference of their cleared offsets divided by the shorter forced denominator. -/
theorem adjacentDebtBridge_collisionTarget
    {short long : List ℕ} {startDepth endDepth : ℕ}
    (short_safe : DebtSafe startDepth short) (long_safe : DebtSafe startDepth long)
    (short_ends : debtRunDepth startDepth short = endDepth)
    (long_ends : debtRunDepth startDepth long = endDepth)
    (length_eq : long.length = short.length + 1) :
    shellRun short (collisionSource short long) =
      (shellOffset long - 2 * shellOffset short) /
        (3 * 5 ^ short.length) := by
  have slope_ratio := adjacentDebtBridge_slope short_safe long_safe short_ends long_ends length_eq
  have slope_ne : shellSlope short ≠ shellSlope long := by
    apply shellSlope_ne_of_length_ne
    omega
  have short_slope_ne : shellSlope short ≠ 0 := (shellSlope_hasValue_five short).1
  rw [shellRun_collisionSource_eq_targetQuotient short long slope_ne, slope_ratio]
  simp only [shellOffset, length_eq, pow_succ]
  field_simp
  ring

/-- An adjacent-length debt-bridge collision is accepted by the five-adic shell exactly when
the two cleared offsets cancel to the shorter schedule length. -/
theorem adjacentDebtBridge_collisionTarget_fiveUnit_iff
    {short long : List ℕ} {startDepth endDepth : ℕ}
    (short_safe : DebtSafe startDepth short) (long_safe : DebtSafe startDepth long)
    (short_ends : debtRunDepth startDepth short = endDepth)
    (long_ends : debtRunDepth startDepth long = endDepth)
    (length_eq : long.length = short.length + 1) :
    IsUnit 5 (shellRun short (collisionSource short long)) ↔
      HasValue 5 (shellOffset long - 2 * shellOffset short) short.length := by
  have target_eq := adjacentDebtBridge_collisionTarget short_safe long_safe short_ends
    long_ends length_eq
  have three_unit : IsUnit 5 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have power_value : HasValue 5 ((5 : ℚ) ^ short.length) short.length :=
    primePower_hasValue short.length
  have denominator_value : HasValue 5 (3 * (5 : ℚ) ^ short.length) short.length := by
    simpa using mul_hasValue three_unit power_value
  constructor
  · intro target_unit
    have product_value := mul_hasValue target_unit denominator_value
    have product_eq :
        shellRun short (collisionSource short long) * (3 * 5 ^ short.length) =
          shellOffset long - 2 * shellOffset short := by
      rw [target_eq]
      exact div_mul_cancel₀ _ denominator_value.1
    rw [product_eq] at product_value
    simpa using product_value
  · intro offset_value
    rw [target_eq]
    have quotient_value := div_hasValue offset_value denominator_value
    simpa using quotient_value

/-- The positive carrier orientation is realized by an exact unequal-length debt collision. -/
theorem positiveOrientation_crossLengthCollision :
    shellRun [1] (1 / 3) = 1 / 3 ∧
      shellRun [1, 1] (1 / 3) = 1 / 3 ∧
      debtState 1 1 = 1 / 3 ∧
      IsUnit 5 (1 / 3 : ℚ) := by
  constructor
  · rw [shellRun_singleton]
    norm_num [shellStep]
  constructor
  · rw [shellRun_cons, shellRun_singleton]
    norm_num [shellStep]
  constructor
  · norm_num [debtState]
  · exact div_hasValue
      (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 1))
      (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 3))

/-- Source unitality does not force target acceptance, even for adjacent-length debt bridges.
The displayed pair stays inside the negative three-adic chamber from depth two to depth five,
but its common target has five-adic valuation one. -/
theorem adjacentDebtBridge_targetOvercancellation :
    DebtSafe 2 [4] ∧
      DebtSafe 2 [0, 5] ∧
      debtRunDepth 2 [4] = 5 ∧
      debtRunDepth 2 [0, 5] = 5 ∧
      collisionSource [4] [0, 5] = 2 / 9 ∧
      shellRun [4] (2 / 9) = 55 / 243 ∧
      shellRun [0, 5] (2 / 9) = 55 / 243 ∧
      IsUnit 5 (2 / 9 : ℚ) ∧
      HasValue 5 (55 / 243 : ℚ) 1 := by
  have slope_ne : shellSlope [4] ≠ shellSlope [0, 5] := by
    apply shellSlope_ne_of_length_ne
    norm_num
  have collision : shellRun [4] (2 / 9) = shellRun [0, 5] (2 / 9) := by
    rw [shellRun_singleton, shellRun_cons, shellRun_singleton]
    norm_num [shellStep]
  have source_eq := collisionSource_eq_of_shellRun_eq [4] [0, 5] slope_ne collision
  refine ⟨by norm_num [DebtSafe, debtNextDepth],
    by norm_num [DebtSafe, debtNextDepth],
    by norm_num [debtRunDepth, debtNextDepth],
    by norm_num [debtRunDepth, debtNextDepth], source_eq, ?_, ?_, ?_, ?_⟩
  · rw [shellRun_singleton]
    norm_num [shellStep]
  · rw [shellRun_cons, shellRun_singleton]
    norm_num [shellStep]
  · exact div_hasValue
      (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 2))
      (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 9))
  · convert primePower_mul_int_div_int_hasValue (prime := 5) 1
      (by norm_num : ¬(5 : ℤ) ∣ 11) (by norm_num : ¬(5 : ℤ) ∣ 243) using 1 <;>
      norm_num

/-- Two distinct adjacent-length debt bridges collide from the fixed source `43/24` for every
terminal wait. Their common target remains an explicit one-parameter rational. -/
theorem fixedSourceAdjacentFamily (wait : ℕ) :
    DebtSafe 1 [1, wait + 2] ∧
      DebtSafe 1 [3, 1, wait] ∧
      debtRunDepth 1 [1, wait + 2] = wait + 2 ∧
      debtRunDepth 1 [3, 1, wait] = wait + 2 ∧
      [1, wait + 2] ≠ [3, 1, wait] ∧
      collisionSource [1, wait + 2] [3, 1, wait] = 43 / 24 ∧
      shellRun [1, wait + 2] (43 / 24) =
        (11 * (2 / 3 : ℚ) ^ wait + 9) / 45 ∧
      shellRun [3, 1, wait] (43 / 24) =
        (11 * (2 / 3 : ℚ) ^ wait + 9) / 45 := by
  have collision :
      shellRun [1, wait + 2] (43 / 24) =
        shellRun [3, 1, wait] (43 / 24) := by
    rw [shellRun_cons, shellRun_singleton, shellRun_cons, shellRun_cons,
      shellRun_singleton]
    simp only [shellStep, pow_add]
    norm_num
    ring
  have slope_ne :
      shellSlope [1, wait + 2] ≠ shellSlope [3, 1, wait] := by
    apply shellSlope_ne_of_length_ne
    norm_num
  have source_eq := collisionSource_eq_of_shellRun_eq
    [1, wait + 2] [3, 1, wait] slope_ne collision
  have short_target :
      shellRun [1, wait + 2] (43 / 24) =
        (11 * (2 / 3 : ℚ) ^ wait + 9) / 45 := by
    rw [shellRun_cons, shellRun_singleton]
    simp only [shellStep, pow_add]
    norm_num
    ring
  refine ⟨by simp [DebtSafe, debtNextDepth],
    by simp [DebtSafe, debtNextDepth], ?_, ?_, by norm_num, source_eq, short_target, ?_⟩
  · simp [debtRunDepth, debtNextDepth]
  · simp [debtRunDepth, debtNextDepth]
    omega
  · exact collision.symm.trans short_target

/-- Distinct terminal waits in the fixed-source family have distinct targets. -/
theorem fixedSourceAdjacentFamily_target_injective : Function.Injective
    (fun wait : ℕ => (11 * (2 / 3 : ℚ) ^ wait + 9) / 45) := by
  intro left right target_eq
  have power_eq : (2 / 3 : ℚ) ^ left = (2 / 3 : ℚ) ^ right := by
    have normalized := target_eq
    field_simp at normalized
    linarith
  exact pow_right_injective₀ (a := (2 / 3 : ℚ)) (by norm_num) (by norm_num) power_eq

/-- Every target in the fixed-source family meets the complementary two-adic endpoint pole. In
the normalized critical-shell coordinate this pole is `v₂(1-2u)=0`. -/
theorem fixedSourceAdjacentFamily_targetPole (wait : ℕ) :
    IsUnit 2 (1 - 2 * ((11 * (2 / 3 : ℚ) ^ wait + 9) / 45)) := by
  have two_value : HasValue 2 (2 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 2) 1)
  have eleven_unit : IsUnit 2 (11 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have twenty_two_value : HasValue 2 (22 : ℚ) 1 := by
    convert mul_hasValue two_value eleven_unit using 1 <;> norm_num
  have three_unit : IsUnit 2 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have ratio_value : HasValue 2 (2 / 3 : ℚ) 1 := div_hasValue two_value three_unit
  have scaled_value :
      HasValue 2 (22 * (2 / 3 : ℚ) ^ wait) (1 + wait) := by
    simpa [add_comm] using mul_hasValue twenty_two_value (hasValue_pow ratio_value wait)
  have scaled_positive : IsPositive 2 (22 * (2 / 3 : ℚ) ^ wait) :=
    ⟨scaled_value.1, by rw [scaled_value.2]; omega⟩
  have twenty_seven_unit : IsUnit 2 (27 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have numerator_unit := unit_sub_positive twenty_seven_unit scaled_positive
  have forty_five_unit : IsUnit 2 (45 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have quotient_unit := div_hasValue numerator_unit forty_five_unit
  convert quotient_unit using 1 <;> ring

/-- The sole possible terminal wait for a prescribed target on the fixed-source ray. -/
def fixedSourceAdjacentWaitCandidate (target : ℚ) : ℕ :=
  Int.toNat (padicValRat 2 ((45 * target - 9) / 11))

/-- Fixed-target intersection with the parametric ray is one explicit rational equality test. -/
theorem fixedSourceAdjacentFamily_target_exists_iff (target : ℚ) :
    (∃ wait : ℕ, (11 * (2 / 3 : ℚ) ^ wait + 9) / 45 = target) ↔
      (11 * (2 / 3 : ℚ) ^ fixedSourceAdjacentWaitCandidate target + 9) / 45 = target := by
  constructor
  · rintro ⟨wait, target_eq⟩
    have power_eq : (45 * target - 9) / 11 = (2 / 3 : ℚ) ^ wait := by
      rw [← target_eq]
      ring
    have two_value : HasValue 2 (2 : ℚ) 1 := by
      simpa using (primePower_hasValue (prime := 2) 1)
    have three_unit : IsUnit 2 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
    have ratio_value : HasValue 2 (2 / 3 : ℚ) 1 := div_hasValue two_value three_unit
    have candidate_eq : fixedSourceAdjacentWaitCandidate target = wait := by
      rw [fixedSourceAdjacentWaitCandidate, power_eq, padicValRat.pow, ratio_value.2]
      simp
    simpa [candidate_eq] using target_eq
  · intro candidate_hits
    exact ⟨fixedSourceAdjacentWaitCandidate target, candidate_hits⟩

/-- The period-ten cleared target numerator has one explicit residue modulo twenty-five. -/
theorem fixedSourceAdjacentFamily_ten_mul_numerator_mod (period : ℕ) :
    11 * 2 ^ (10 * period) + 9 * 3 ^ (10 * period) ≡
      20 * 24 ^ period [MOD 25] := by
  have two_mod : 2 ^ 10 ≡ 24 [MOD 25] := by norm_num
  have three_mod : 3 ^ 10 ≡ 24 [MOD 25] := by norm_num
  rw [pow_mul, pow_mul]
  calc
    11 * (2 ^ 10) ^ period + 9 * (3 ^ 10) ^ period ≡
        11 * 24 ^ period + 9 * 24 ^ period [MOD 25] :=
      ((two_mod.pow period).mul_left 11).add ((three_mod.pow period).mul_left 9)
    _ = 20 * 24 ^ period := by ring

/-- The cleared numerator of every period-ten target has five-adic valuation exactly one. -/
theorem fixedSourceAdjacentFamily_ten_mul_numerator (period : ℕ) :
    HasValue 5
      (11 * (2 : ℚ) ^ (10 * period) + 9 * 3 ^ (10 * period)) 1 := by
  let numerator : ℕ :=
    11 * 2 ^ (10 * period) + 9 * 3 ^ (10 * period)
  have numerator_mod : numerator ≡ 20 * 24 ^ period [MOD 25] := by
    simpa [numerator] using fixedSourceAdjacentFamily_ten_mul_numerator_mod period
  have five_dvd_numerator : 5 ∣ numerator := by
    have reduced := numerator_mod.of_dvd (by norm_num : 5 ∣ 25)
    have right_zero : 20 * 24 ^ period ≡ 0 [MOD 5] :=
      (dvd_mul_of_dvd_left (by norm_num : 5 ∣ 20) _).modEq_zero_nat
    exact Nat.modEq_zero_iff_dvd.mp (reduced.trans right_zero)
  have twentyfive_not_dvd_numerator : ¬25 ∣ numerator := by
    intro twentyfive_dvd
    have numerator_zero : numerator ≡ 0 [MOD 25] := twentyfive_dvd.modEq_zero_nat
    have right_zero := numerator_mod.symm.trans numerator_zero
    have right_dvd : 25 ∣ 20 * 24 ^ period := Nat.modEq_zero_iff_dvd.mp right_zero
    have coprime : Nat.Coprime 25 (24 ^ period) :=
      (by norm_num : Nat.Coprime 25 24).pow_right period
    have impossible : 25 ∣ 20 := coprime.dvd_of_dvd_mul_right right_dvd
    norm_num at impossible
  have numerator_ne_int : (numerator : ℤ) ≠ 0 := by positivity
  have numerator_value_int : padicValInt 5 (numerator : ℤ) = 1 := by
    have one_le : 1 ≤ padicValInt 5 (numerator : ℤ) :=
      ((padicValInt_dvd_iff (p := 5) 1 (numerator : ℤ)).mp (by
        simpa using (show (5 : ℤ) ∣ numerator by
          exact_mod_cast five_dvd_numerator))).resolve_left numerator_ne_int
    have not_two_le : ¬2 ≤ padicValInt 5 (numerator : ℤ) := by
      intro two_le
      have twentyfive_dvd_int :=
        (padicValInt_dvd_iff (p := 5) 2 (numerator : ℤ)).mpr (Or.inr two_le)
      have twentyfive_dvd_nat : 25 ∣ numerator := by
        exact_mod_cast twentyfive_dvd_int
      exact twentyfive_not_dvd_numerator twentyfive_dvd_nat
    omega
  have numerator_value : HasValue 5 (numerator : ℚ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [padicValRat.of_nat, ← padicValInt.of_nat]
    exact_mod_cast numerator_value_int
  simpa [numerator] using numerator_value

/-- Every terminal wait divisible by ten gives an accepted member of the fixed-source adjacent
family. Thus one rational source supports infinitely many chamber-contained cross-length
collisions with unbounded waits. -/
theorem fixedSourceAdjacentFamily_ten_mul_accepted (period : ℕ) :
    IsUnit 5 (43 / 24 : ℚ) ∧
      HasValue 5
        (11 * (2 : ℚ) ^ (10 * period) + 9 * 3 ^ (10 * period)) 1 ∧
      IsUnit 5 ((11 * (2 / 3 : ℚ) ^ (10 * period) + 9) / 45) ∧
      (∀ front back,
        [1, 10 * period + 2] = front ++ back →
          IsUnit 5 (shellRun front (43 / 24))) ∧
      (∀ front back,
        [3, 1, 10 * period] = front ++ back →
          IsUnit 5 (shellRun front (43 / 24))) ∧
      shellRun [1, 10 * period + 2] (43 / 24) =
        (11 * (2 / 3 : ℚ) ^ (10 * period) + 9) / 45 ∧
      shellRun [3, 1, 10 * period] (43 / 24) =
        (11 * (2 / 3 : ℚ) ^ (10 * period) + 9) / 45 := by
  have numerator_value := fixedSourceAdjacentFamily_ten_mul_numerator period
  have three_unit : IsUnit 5 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have fortyfive_value : HasValue 5 (45 : ℚ) 1 := by
    have five_value : HasValue 5 (5 : ℚ) 1 := by
      simpa using (primePower_hasValue (prime := 5) 1)
    have nine_unit : IsUnit 5 (9 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
    convert mul_hasValue five_value nine_unit using 1 <;> norm_num
  have denominator_value :
      HasValue 5 (45 * (3 : ℚ) ^ (10 * period)) 1 := by
    simpa using mul_hasValue fortyfive_value (unit_pow three_unit (10 * period))
  have rational_eq :
      (11 * (2 / 3 : ℚ) ^ (10 * period) + 9) / 45 =
        (11 * (2 : ℚ) ^ (10 * period) + 9 * 3 ^ (10 * period)) /
          (45 * 3 ^ (10 * period)) := by
    rw [div_pow]
    field_simp
  have target_unit :
      IsUnit 5 ((11 * (2 / 3 : ℚ) ^ (10 * period) + 9) / 45) := by
    rw [rational_eq]
    simpa using div_hasValue numerator_value denominator_value
  have source_unit : IsUnit 5 (43 / 24 : ℚ) := div_hasValue
    (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 43))
    (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 24))
  obtain ⟨_, _, _, _, _, _, short_target, long_target⟩ :=
    fixedSourceAdjacentFamily (10 * period)
  have short_output_unit :
      IsUnit 5 (shellRun [1, 10 * period + 2] (43 / 24)) := by
    rw [short_target]
    exact target_unit
  have long_output_unit :
      IsUnit 5 (shellRun [3, 1, 10 * period] (43 / 24)) := by
    rw [long_target]
    exact target_unit
  have short_phases :=
    (shellPrefixesUnit_iff [1, 10 * period + 2] (43 / 24)).2 short_output_unit
  have long_phases :=
    (shellPrefixesUnit_iff [3, 1, 10 * period] (43 / 24)).2 long_output_unit
  exact ⟨source_unit, numerator_value, target_unit, short_phases, long_phases,
    short_target, long_target⟩

/-- The opposite carrier orientation is also realized by an exact unequal-length debt
collision. Both endpoints remain five-adic units. -/
theorem negativeOrientation_crossLengthCollision :
    shellRun [1] (19 / 42) = 8 / 21 ∧
      shellRun [1, 2, 0] (19 / 42) = 8 / 21 ∧
      debtState (19 / 14) 1 = 19 / 42 ∧
      debtState (8 / 7) 1 = 8 / 21 ∧
      IsUnit 5 (19 / 42 : ℚ) ∧
      IsUnit 5 (8 / 21 : ℚ) ∧
      HasValue 3 (19 / 14 + 1) 1 ∧
      HasValue 3 (8 / 7 + 1) 1 := by
  constructor
  · rw [shellRun_singleton]
    norm_num [shellStep]
  constructor
  · rw [shellRun_cons, shellRun_cons, shellRun_singleton]
    norm_num [shellStep]
  constructor
  · norm_num [debtState]
  constructor
  · norm_num [debtState]
  constructor
  · exact div_hasValue
      (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 19))
      (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 42))
  constructor
  · exact div_hasValue
      (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 8))
      (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 21))
  constructor
  · convert primePower_mul_int_div_int_hasValue (prime := 3) 1
      (by norm_num : ¬(3 : ℤ) ∣ 11) (by norm_num : ¬(3 : ℤ) ∣ 14) using 1 <;>
      norm_num
  · convert primePower_mul_int_div_int_hasValue (prime := 3) 1
      (by norm_num : ¬(3 : ℤ) ∣ 5) (by norm_num : ¬(3 : ℤ) ∣ 7) using 1 <;>
      norm_num

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
