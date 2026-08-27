import MatrixMortality.PadicValuation
import MatrixMortality.ReturnGuard

/-!
# Dynamics of the amalgamated valuation guard

The return algebra supplies a free physical wait. The valuation guard turns that choice into a
deterministic instruction: a live state survives only when the selected wait is exactly its
`p`-adic valuation and its unit tail has the prescribed carry depth. Every other projective
state enters a forward-invariant trap.
-/

namespace MatrixMortality.ReturnGuard
open MatrixMortality.PadicValuation
noncomputable section
/-- Arithmetic envelope for an amalgamated valuation guard. The apparently stronger hypothesis
that the prime is odd is exactly replaced by the two unit hypotheses on `center`. -/
structure Parameters where
  /-- Prime supporting the valuation guard. -/
  prime : Nat
  prime_prime : prime.Prime
  /-- Carry depth required of every surviving live step. -/
  depth : Nat
  depth_two : 2 ≤ depth
  /-- Unit residue ball into which illegal steps collapse. -/
  center : ℚ
  /-- Positive-valuation point emitted by the internal separator. -/
  reset : ℚ
  center_unit : IsUnit prime center
  center_sub_one_unit : IsUnit prime (center - 1)
  reset_positive : IsPositive prime reset

namespace Parameters
instance (parameters : Parameters) : Fact parameters.prime.Prime :=
  ⟨parameters.prime_prime⟩
theorem prime_two (parameters : Parameters) : 2 ≤ parameters.prime :=
  parameters.prime_prime.two_le

/-- The adjacent unit conditions exclude residue characteristic two. -/
theorem prime_odd (parameters : Parameters) : Odd parameters.prime :=
  odd_prime_of_adjacent_units parameters.center_unit parameters.center_sub_one_unit

theorem prime_ne_zero (parameters : Parameters) : (parameters.prime : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr parameters.prime_prime.ne_zero
theorem depth_positive (parameters : Parameters) : 0 < parameters.depth := by
  exact lt_of_lt_of_le Nat.zero_lt_two parameters.depth_two
/-- The reset-center displacement is automatically a unit. -/
theorem drift_unit (parameters : Parameters) :
    IsUnit parameters.prime (drift parameters.center parameters.reset) := by
  have center_sub_reset :=
    unit_sub_positive parameters.center_unit parameters.reset_positive
  rw [drift, show parameters.reset - parameters.center =
    -(parameters.center - parameters.reset) by ring]
  exact neg_hasValue center_sub_reset
theorem drift_ne_zero (parameters : Parameters) :
    drift parameters.center parameters.reset ≠ 0 :=
  parameters.drift_unit.1
end Parameters
/-- A finite projective point in the positive-valuation live region. -/
def Live (parameters : Parameters) : ProjectiveLine.Point ℚ → Prop
  | some z => IsPositive parameters.prime z
  | none => False
/-- Everything outside the live region and the unique terminal point. -/
def Trap (parameters : Parameters) (point : ProjectiveLine.Point ℚ) : Prop :=
  point ≠ some 1 ∧ ¬Live parameters point
/-- A live point whose selected valuation also has the exact required carry depth. -/
def Ready (parameters : Parameters) (wait : Nat) (z : ℚ) : Prop :=
  0 < wait ∧
    padicValRat parameters.prime z = wait ∧
      padicValRat parameters.prime (z - parameters.prime ^ wait) =
        parameters.depth * wait
/-- The guard step specialized to an arithmetic envelope. -/
def guardedStep (parameters : Parameters) (wait : Nat) :
    ProjectiveLine.Point ℚ → ProjectiveLine.Point ℚ :=
  projectiveStep parameters.prime parameters.depth
    parameters.center parameters.reset wait
/-- Positive return family, indexed from zero for list words. -/
def positiveGuardTransfer (parameters : Parameters) (index : Nat) :
    Square (Fin 2) ℚ :=
  guardTransfer parameters.prime parameters.depth
    parameters.center parameters.reset (index + 1)
/-- Projective state reached by a positive-return bridge, read in physical matrix order. -/
def guardedOrbit (parameters : Parameters) (waits : List Nat) :
    ProjectiveLine.Point ℚ :=
  rayState (fun index => guardedStep parameters (index + 1))
    waits (some parameters.reset)
/-- Affine verifier defect carried by a non-pole step. -/
def guardDefect (parameters : Parameters) (wait : Nat) (z : ℚ) : ℚ :=
  drift parameters.center parameters.reset *
      parameters.prime ^ (parameters.depth * wait) *
        (z - 1) / (z - parameters.prime ^ wait)
theorem live_some_iff (parameters : Parameters) (z : ℚ) :
    Live parameters (some z) ↔ IsPositive parameters.prime z :=
  Iff.rfl
@[simp]
theorem live_infinity (parameters : Parameters) :
    ¬Live parameters none := by
  simp [Live]
@[simp]
theorem trap_infinity (parameters : Parameters) :
    Trap parameters none := by
  simp [Trap, Live]
theorem trap_some_iff (parameters : Parameters) (z : ℚ) :
    Trap parameters (some z) ↔ z ≠ 1 ∧ ¬IsPositive parameters.prime z := by
  simp [Trap, Live]
theorem not_trap_iff (parameters : Parameters) (point : ProjectiveLine.Point ℚ) :
    ¬Trap parameters point ↔ point = some 1 ∨ Live parameters point := by
  constructor
  · intro not_trap
    by_cases terminal : point = some 1
    · exact Or.inl terminal
    · exact Or.inr (by
        by_contra not_live
        exact not_trap ⟨terminal, not_live⟩)
  · rintro (terminal | live)
    · intro trapped
      exact trapped.1 terminal
    · intro trapped
      exact trapped.2 live
theorem positiveGuardTransfer_eq
    (parameters : Parameters) (index : Nat) :
    positiveGuardTransfer parameters index =
      (parameters.prime : ℚ) ^ (index + 1) •
        positiveTransfer parameters.prime parameters.depth
          parameters.center parameters.reset index :=
  rfl
theorem guardedOrbit_eq_rayState
    (parameters : Parameters) (waits : List Nat) :
    guardedOrbit parameters waits =
      rayState
        (fun index => ProjectiveLine.act (positiveGuardTransfer parameters index))
        waits (some parameters.reset) :=
  rfl
/-- The scalar bridge vanishes exactly when its total projective orbit reaches the target one. -/
theorem positiveBridge_zero_iff_guardedOrbit
    (parameters : Parameters) (waits : List Nat) :
    positiveBridge parameters.prime parameters.depth
        parameters.center parameters.reset waits = 0 ↔
      guardedOrbit parameters waits = some 1 := by
  have generator_unit :
      ∀ index, IsUnit (positiveGuardTransfer parameters index) := by
    intro index
    exact guardTransfer_isUnit parameters.prime parameters.depth
      parameters.center parameters.reset parameters.prime_two parameters.depth_two
      parameters.drift_ne_zero (index + 1) (by omega)
  have projective_cut :=
    ProjectiveLine.targetOne_word_iff
      (positiveGuardTransfer parameters) generator_unit waits
      (some parameters.reset)
  rw [← guardedOrbit_eq_rayState] at projective_cut
  have scaled_product :
      wordProduct (positiveGuardTransfer parameters) waits =
        (waits.map (fun index => (parameters.prime : ℚ) ^ (index + 1))).prod •
          wordProduct
            (positiveTransfer parameters.prime parameters.depth
              parameters.center parameters.reset) waits := by
    change wordProduct
      (fun index => (parameters.prime : ℚ) ^ (index + 1) •
        positiveTransfer parameters.prime parameters.depth
          parameters.center parameters.reset index) waits = _
    exact wordProduct_smulMatrix
      (fun index => (parameters.prime : ℚ) ^ (index + 1))
      (positiveTransfer parameters.prime parameters.depth
        parameters.center parameters.reset) waits
  have scale_ne :
      (waits.map (fun index => (parameters.prime : ℚ) ^ (index + 1))).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro zero_mem
    obtain ⟨index, _, power_zero⟩ := List.mem_map.mp zero_mem
    exact primePower_ne_zero parameters.prime_prime (index + 1) power_zero
  rw [scaled_product] at projective_cut
  rw [Matrix.smul_mulVec, dotProduct_smul] at projective_cut
  simpa [positiveBridge, bridgeScalar, ProjectiveLine.ray, smul_eq_mul,
    scale_ne] using projective_cut

/-- The physical matrix pair is mortal exactly when one positive-return orbit reaches one. -/
theorem physical_isMortal_iff_guardedOrbit (parameters : Parameters) :
    IsMortal
        (ReturnFamily.pairGenerator
          (ambient (parameters.prime : ℚ) parameters.depth)
          (cut parameters.center parameters.reset)) ↔
      ∃ waits, guardedOrbit parameters waits = some 1 := by
  rw [physical_isMortal_iff_positiveBridge
    parameters.prime parameters.depth parameters.center parameters.reset
    parameters.prime_prime.ne_zero parameters.drift_ne_zero]
  apply exists_congr
  exact positiveBridge_zero_iff_guardedOrbit parameters

/-- Total projective action on a finite non-pole point. -/
theorem guardedStep_some
    (parameters : Parameters) (wait : Nat) (z : ℚ)
    (not_pole : z ≠ parameters.prime ^ wait) :
    guardedStep parameters wait (some z) =
      some (parameters.center + guardDefect parameters wait z) := by
  have denominator_ne :
      projectiveDenominator parameters.prime wait z ≠ 0 := by
    simpa [projectiveDenominator] using sub_ne_zero.mpr not_pole
  rw [guardedStep, projectiveStep_some
    parameters.prime parameters.depth parameters.center parameters.reset z wait
    parameters.prime_ne_zero parameters.depth_positive denominator_ne]
  congr 1
  rw [projectiveValue_eq_center_add_defect
    parameters.prime parameters.depth parameters.center parameters.reset z wait
    denominator_ne]
  rfl

/-- The selected wait power is the unique affine pole. -/
theorem guardedStep_pole (parameters : Parameters) (wait : Nat) :
    guardedStep parameters wait (some (parameters.prime ^ wait)) = none :=
  projectiveStep_pole parameters.prime parameters.depth
    parameters.center parameters.reset wait
    parameters.prime_ne_zero parameters.depth_positive

/-- Infinity immediately enters the residue ball about the center. -/
theorem guardedStep_infinity (parameters : Parameters) (wait : Nat) :
    guardedStep parameters wait none =
      some
        (parameters.center +
          drift parameters.center parameters.reset *
            parameters.prime ^ (parameters.depth * wait)) :=
  projectiveStep_infinity parameters.prime parameters.depth
    parameters.center parameters.reset wait
    parameters.prime_ne_zero parameters.depth_positive

/-- Exact valuation bookkeeping for the affine verifier defect. -/
theorem guardDefect_hasValue
    (parameters : Parameters) (wait : Nat) (z : ℚ)
    {targetValue denominatorValue : ℤ}
    (target_value :
      HasValue parameters.prime (z - 1) targetValue)
    (denominator_value :
      HasValue parameters.prime
        (z - parameters.prime ^ wait) denominatorValue) :
    HasValue parameters.prime (guardDefect parameters wait z)
      (parameters.depth * wait + targetValue - denominatorValue) := by
  have scaled_drift :
      HasValue parameters.prime
        (drift parameters.center parameters.reset *
          (parameters.prime : ℚ) ^ (parameters.depth * wait))
        (parameters.depth * wait) := by
    simpa using mul_hasValue parameters.drift_unit
      (primePower_hasValue (parameters.depth * wait))
  have numerator_value :=
    mul_hasValue scaled_drift target_value
  simpa [guardDefect, Int.natCast_mul] using
    div_hasValue numerator_value denominator_value

/-- A positive verifier defect lands in the permanent unit trap. -/
theorem center_add_positive_is_trap
    (parameters : Parameters) {error : ℚ}
    (error_positive : IsPositive parameters.prime error) :
    Trap parameters (some (parameters.center + error)) := by
  have output_unit := unit_add_positive parameters.center_unit error_positive
  have output_sub_one_unit : IsUnit parameters.prime
      (parameters.center + error - 1) := by
    rw [show parameters.center + error - 1 =
      (parameters.center - 1) + error by ring]
    exact unit_add_positive parameters.center_sub_one_unit error_positive
  rw [trap_some_iff]
  exact ⟨sub_ne_zero.mp output_sub_one_unit.1, fun output_positive => by
    have impossible := output_positive.2
    rw [output_unit.2] at impossible
    exact lt_irrefl 0 impossible⟩

/-- A negative verifier defect dominates the center and also lands in the permanent trap. -/
theorem center_add_negative_is_trap
    (parameters : Parameters) {error : ℚ}
    (error_negative : IsNegative parameters.prime error) :
    Trap parameters (some (parameters.center + error)) := by
  have output_negative : IsNegative parameters.prime
      (parameters.center + error) := by
    rw [add_comm]
    exact negative_add_unit error_negative parameters.center_unit
  have output_sub_one_negative : IsNegative parameters.prime
      (parameters.center + error - 1) := by
    rw [show parameters.center + error - 1 =
      error + (parameters.center - 1) by ring]
    exact negative_add_unit error_negative parameters.center_sub_one_unit
  rw [trap_some_iff]
  exact ⟨sub_ne_zero.mp output_sub_one_negative.1, fun output_positive =>
    (lt_asymm output_negative.2 output_positive.2)⟩

theorem primePower_positive
    (parameters : Parameters) (exponent : Nat) (exponent_positive : 0 < exponent) :
    IsPositive parameters.prime ((parameters.prime : ℚ) ^ exponent) := by
  refine ⟨primePower_ne_zero parameters.prime_prime exponent, ?_⟩
  rw [primePower_valuation]
  exact_mod_cast exponent_positive

/-- Infinity is poisoned after every positive wait. -/
theorem infinity_step_is_trap
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait) :
    Trap parameters (guardedStep parameters wait none) := by
  rw [guardedStep_infinity]
  apply center_add_positive_is_trap
  have exponent_positive : 0 < parameters.depth * wait :=
    Nat.mul_pos parameters.depth_positive wait_positive
  have error_value :=
    mul_hasValue parameters.drift_unit
      (primePower_hasValue (parameters.depth * wait))
  exact ⟨error_value.1, by
    rw [error_value.2]
    have exponent_positive_int :
        (0 : ℤ) < parameters.depth * wait := by
      exact_mod_cast exponent_positive
    simpa using exponent_positive_int⟩

/-- Zero is poisoned after every positive wait. -/
theorem zero_step_is_trap
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait) :
    Trap parameters (guardedStep parameters wait (some 0)) := by
  have not_pole : (0 : ℚ) ≠ parameters.prime ^ wait :=
    (primePower_ne_zero parameters.prime_prime wait).symm
  rw [guardedStep_some parameters wait 0 not_pole]
  apply center_add_positive_is_trap
  have target_value : HasValue parameters.prime ((0 : ℚ) - 1) 0 := by
    norm_num [HasValue]
  have denominator_value :
      HasValue parameters.prime
        ((0 : ℚ) - parameters.prime ^ wait) wait := by
    rw [zero_sub]
    exact neg_hasValue (primePower_hasValue wait)
  have error_value :=
    guardDefect_hasValue parameters wait 0 target_value denominator_value
  refine ⟨error_value.1, ?_⟩
  rw [error_value.2]
  have growth : (wait : ℤ) < parameters.depth * wait := by
    exact_mod_cast (show wait < parameters.depth * wait by
      nlinarith [parameters.depth_two])
  omega

/-- A nonterminal unit input is poisoned after every positive wait. -/
theorem unit_step_is_trap
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait)
    (z : ℚ) (z_unit : IsUnit parameters.prime z) (not_target : z ≠ 1) :
    Trap parameters (guardedStep parameters wait (some z)) := by
  have power_positive := primePower_positive parameters wait wait_positive
  have denominator_value :
      IsUnit parameters.prime (z - parameters.prime ^ wait) :=
    unit_sub_positive z_unit power_positive
  rw [guardedStep_some parameters wait z
    (sub_ne_zero.mp denominator_value.1)]
  apply center_add_positive_is_trap
  have target_ne : z - 1 ≠ 0 := sub_ne_zero.mpr not_target
  let targetValue := padicValRat parameters.prime (z - 1)
  have target_value :
      HasValue parameters.prime (z - 1) targetValue :=
    ⟨target_ne, rfl⟩
  have target_nonnegative : 0 ≤ targetValue := by
    have lower := min_le_sub (prime := parameters.prime) target_ne
    simpa [targetValue, z_unit.2] using lower
  have error_value :=
    guardDefect_hasValue parameters wait z target_value denominator_value
  refine ⟨error_value.1, ?_⟩
  rw [error_value.2]
  have exponent_positive : 0 < parameters.depth * wait :=
    Nat.mul_pos parameters.depth_positive wait_positive
  omega

/-- A negative-valuation input is poisoned after every positive wait. -/
theorem negative_step_is_trap
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait)
    (z : ℚ) (z_negative : IsNegative parameters.prime z) :
    Trap parameters (guardedStep parameters wait (some z)) := by
  have power_positive := primePower_positive parameters wait wait_positive
  have target_value :
      HasValue parameters.prime (z - 1)
        (padicValRat parameters.prime z) := by
    refine ⟨sub_ne_zero.mpr ?_, ?_⟩
    · exact ne_of_valuation_ne (by
        rw [padicValRat.one]
        exact ne_of_lt z_negative.2)
    · exact sub_eq_left_of_lt z_negative.1 one_ne_zero
        (by simpa using z_negative.2)
  have denominator_value :
      HasValue parameters.prime (z - parameters.prime ^ wait)
        (padicValRat parameters.prime z) := by
    refine ⟨sub_ne_zero.mpr ?_, ?_⟩
    · exact ne_of_valuation_ne (by
        rw [primePower_valuation]
        exact ne_of_lt (lt_trans z_negative.2
          (by exact_mod_cast wait_positive)))
    · exact sub_eq_left_of_lt z_negative.1 power_positive.1
        (lt_trans z_negative.2 power_positive.2)
  rw [guardedStep_some parameters wait z
    (sub_ne_zero.mp denominator_value.1)]
  apply center_add_positive_is_trap
  have error_value :=
    guardDefect_hasValue parameters wait z target_value denominator_value
  refine ⟨error_value.1, ?_⟩
  rw [error_value.2]
  have exponent_positive : 0 < parameters.depth * wait :=
    Nat.mul_pos parameters.depth_positive wait_positive
  omega

/-- The trap is forward invariant under every positive return. -/
theorem trap_forward
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait)
    {point : ProjectiveLine.Point ℚ} (trapped : Trap parameters point) :
    Trap parameters (guardedStep parameters wait point) := by
  cases point with
  | none => exact infinity_step_is_trap parameters wait wait_positive
  | some z =>
      have not_target : z ≠ 1 := by
        intro target
        exact trapped.1 (congrArg some target)
      by_cases z_zero : z = 0
      · subst z
        exact zero_step_is_trap parameters wait wait_positive
      · have not_positive : ¬0 < padicValRat parameters.prime z := by
          intro positive
          exact trapped.2 ⟨z_zero, positive⟩
        have nonpositive : padicValRat parameters.prime z ≤ 0 :=
          le_of_not_gt not_positive
        rcases nonpositive.eq_or_lt with valuation_zero | valuation_negative
        · exact unit_step_is_trap parameters wait wait_positive z
            ⟨z_zero, valuation_zero⟩ not_target
        · exact negative_step_is_trap parameters wait wait_positive z
            ⟨z_zero, valuation_negative⟩

/-- Choosing a wait different from a live state's valuation is poisoned immediately. -/
theorem wrong_wait_is_trap
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait)
    (z : ℚ) (z_positive : IsPositive parameters.prime z)
    (wait_mismatch : padicValRat parameters.prime z ≠ wait) :
    Trap parameters (guardedStep parameters wait (some z)) := by
  have power_positive := primePower_positive parameters wait wait_positive
  have valuation_ne :
      padicValRat parameters.prime z ≠
        padicValRat parameters.prime (parameters.prime ^ wait) := by
    rw [primePower_valuation]
    exact wait_mismatch
  have denominator_value :=
    sub_hasValue_min z_positive.1 power_positive.1 valuation_ne
  have denominator_value_normalized :
      HasValue parameters.prime (z - parameters.prime ^ wait)
        (min (padicValRat parameters.prime z) (wait : ℤ)) := by
    simpa [primePower_valuation] using denominator_value
  rw [guardedStep_some parameters wait z
    (sub_ne_zero.mp denominator_value_normalized.1)]
  apply center_add_positive_is_trap
  have target_value := positive_sub_one z_positive
  have error_value :=
    guardDefect_hasValue parameters wait z target_value denominator_value_normalized
  refine ⟨error_value.1, ?_⟩
  rw [error_value.2]
  have wait_lt_scaled : (wait : ℤ) < parameters.depth * wait := by
    exact_mod_cast (show wait < parameters.depth * wait by
      nlinarith [parameters.depth_two])
  have denominator_le_wait :
      min (padicValRat parameters.prime z) (wait : ℤ) ≤ wait :=
    min_le_right _ _
  omega

/-- Even the correct wait is poisoned unless the denominator has exactly the prescribed depth. -/
theorem depth_mismatch_is_trap
    (parameters : Parameters) (wait : Nat)
    (z : ℚ) (z_positive : IsPositive parameters.prime z)
    (depth_mismatch :
      padicValRat parameters.prime (z - parameters.prime ^ wait) ≠
        parameters.depth * wait) :
    Trap parameters (guardedStep parameters wait (some z)) := by
  by_cases pole : z = parameters.prime ^ wait
  · subst z
    rw [guardedStep_pole]
    exact trap_infinity parameters
  · rw [guardedStep_some parameters wait z pole]
    have target_value := positive_sub_one z_positive
    let denominatorValue :=
      padicValRat parameters.prime (z - parameters.prime ^ wait)
    have denominator_value :
        HasValue parameters.prime (z - parameters.prime ^ wait)
          denominatorValue :=
      ⟨sub_ne_zero.mpr pole, rfl⟩
    have error_value :=
      guardDefect_hasValue parameters wait z target_value denominator_value
    rcases lt_or_gt_of_ne depth_mismatch with shallow | excessive
    · apply center_add_positive_is_trap
      exact ⟨error_value.1, by
        rw [error_value.2]
        omega⟩
    · apply center_add_negative_is_trap
      exact ⟨error_value.1, by
        rw [error_value.2]
        omega⟩

/-- Any live step that avoids the trap must choose exactly the state's valuation. -/
theorem live_step_forces_wait
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait)
    (z : ℚ) (z_positive : IsPositive parameters.prime z)
    (survives : ¬Trap parameters (guardedStep parameters wait (some z))) :
    padicValRat parameters.prime z = wait := by
  by_contra mismatch
  exact survives (wrong_wait_is_trap parameters wait wait_positive z z_positive mismatch)

/-- Surviving a positive return forces both the unique wait and the exact carry depth. -/
theorem live_step_forces_ready
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait)
    (z : ℚ) (z_positive : IsPositive parameters.prime z)
    (survives : ¬Trap parameters (guardedStep parameters wait (some z))) :
    Ready parameters wait z := by
  have wait_matches :=
    live_step_forces_wait parameters wait wait_positive z z_positive survives
  refine ⟨wait_positive, wait_matches, ?_⟩
  by_contra depth_mismatch
  exact survives
    (depth_mismatch_is_trap parameters wait z z_positive depth_mismatch)

/-- Unit tail extracted from a ready point. -/
def readyTail (parameters : Parameters) (wait : Nat) (z : ℚ) : ℚ :=
  parameters.prime ^ (parameters.depth * wait) /
    (z - parameters.prime ^ wait)

/-- Canonical point in the ready cylinder indexed by `wait`. -/
def readyState (parameters : Parameters) (wait : Nat) (tail : ℚ) : ℚ :=
  parameters.prime ^ wait +
    parameters.prime ^ (parameters.depth * wait) / tail

/-- Exact payload update performed by a legal wait. -/
def legalValue (parameters : Parameters) (wait : Nat) (tail : ℚ) : ℚ :=
  parameters.center +
    drift parameters.center parameters.reset *
      (parameters.prime ^ (parameters.depth * wait) +
        (parameters.prime ^ wait - 1) * tail)

/-- Inverse tail selecting an arbitrary next ready cylinder. -/
def inverseTail
    (parameters : Parameters) (wait nextWait : Nat) (nextTail : ℚ) : ℚ :=
  (readyState parameters nextWait nextTail -
      parameters.center -
        drift parameters.center parameters.reset *
          parameters.prime ^ (parameters.depth * wait)) /
    (drift parameters.center parameters.reset *
      (parameters.prime ^ wait - 1))

/-- Unique tail that makes one legal step hit the terminal point. -/
def targetTail (parameters : Parameters) (wait : Nat) : ℚ :=
  (1 - parameters.center -
      drift parameters.center parameters.reset *
        parameters.prime ^ (parameters.depth * wait)) /
    (drift parameters.center parameters.reset *
      (parameters.prime ^ wait - 1))

/-- Every ready point has a p-adic unit tail. -/
theorem readyTail_isUnit
    (parameters : Parameters) (wait : Nat) (z : ℚ)
    (ready : Ready parameters wait z) :
    IsUnit parameters.prime (readyTail parameters wait z) := by
  have exponent_positive : (0 : ℤ) < parameters.depth * wait := by
    exact_mod_cast Nat.mul_pos parameters.depth_positive ready.1
  have denominator_ne :
      z - parameters.prime ^ wait ≠ 0 := by
    intro denominator_zero
    have impossible := ready.2.2
    rw [denominator_zero, padicValRat.zero] at impossible
    omega
  have denominator_value :
      HasValue parameters.prime (z - parameters.prime ^ wait)
        (parameters.depth * wait) :=
    ⟨denominator_ne, ready.2.2⟩
  have quotient_value :=
    div_hasValue (primePower_hasValue (parameters.depth * wait))
      denominator_value
  simpa [readyTail] using quotient_value

/-- Tail extraction reconstructs the ready point exactly. -/
theorem readyState_readyTail
    (parameters : Parameters) (wait : Nat) (z : ℚ) :
    readyState parameters wait (readyTail parameters wait z) = z := by
  have power_ne :
      (parameters.prime : ℚ) ^ (parameters.depth * wait) ≠ 0 :=
    primePower_ne_zero parameters.prime_prime _
  simp [readyState, readyTail]
  field_simp [power_ne]
  ring

/-- Every unit tail names a ready point in its indexed cylinder. -/
theorem readyState_ready
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait)
    (tail : ℚ) (tail_unit : IsUnit parameters.prime tail) :
    Ready parameters wait (readyState parameters wait tail) := by
  have low_value := primePower_hasValue (prime := parameters.prime) wait
  have high_value :
      HasValue parameters.prime
        ((parameters.prime : ℚ) ^ (parameters.depth * wait) / tail)
        (parameters.depth * wait) := by
    simpa using div_hasValue
      (primePower_hasValue (parameters.depth * wait)) tail_unit
  have valuation_lt : (wait : ℤ) < parameters.depth * wait := by
    exact_mod_cast (show wait < parameters.depth * wait by
      nlinarith [parameters.depth_two])
  have state_value :
      HasValue parameters.prime (readyState parameters wait tail) wait := by
    simpa [readyState] using
      add_hasValue_left low_value high_value valuation_lt
  refine ⟨wait_positive, state_value.2, ?_⟩
  rw [show
      readyState parameters wait tail - parameters.prime ^ wait =
        parameters.prime ^ (parameters.depth * wait) / tail by
      simp [readyState]]
  exact high_value.2

/-- On a ready cylinder, the projective return performs the affine tail update exactly. -/
theorem ready_step
    (parameters : Parameters) (wait : Nat) (tail : ℚ) (tail_ne : tail ≠ 0) :
    guardedStep parameters wait (some (readyState parameters wait tail)) =
      some (legalValue parameters wait tail) := by
  have power_ne :
      (parameters.prime : ℚ) ^ (parameters.depth * wait) ≠ 0 :=
    primePower_ne_zero parameters.prime_prime _
  have not_pole :
      readyState parameters wait tail ≠ parameters.prime ^ wait := by
    intro pole
    have quotient_zero :
        (parameters.prime : ℚ) ^ (parameters.depth * wait) / tail = 0 := by
      rw [readyState] at pole
      linarith
    exact div_ne_zero power_ne tail_ne quotient_zero
  rw [guardedStep_some parameters wait _ not_pole]
  congr 1
  simp [guardDefect, readyState, legalValue]
  field_simp [tail_ne, power_ne]
  ring

/-- Readiness includes membership in the positive-valuation live region. -/
theorem ready_isPositive
    (parameters : Parameters) (wait : Nat) (z : ℚ)
    (ready : Ready parameters wait z) :
    IsPositive parameters.prime z := by
  have valuation_positive : (0 : ℤ) < wait := by
    exact_mod_cast ready.1
  refine ⟨?_, ?_⟩
  · intro z_zero
    have impossible := ready.2.1
    rw [z_zero, padicValRat.zero] at impossible
    omega
  · rw [ready.2.1]
    exact valuation_positive

/-- Every target cylinder has a unit inverse tail from every source cylinder. -/
theorem inverseTail_isUnit
    (parameters : Parameters)
    (wait nextWait : Nat) (wait_positive : 0 < wait)
    (nextWait_positive : 0 < nextWait)
    (nextTail : ℚ) (nextTail_unit : IsUnit parameters.prime nextTail) :
    IsUnit parameters.prime
      (inverseTail parameters wait nextWait nextTail) := by
  have next_ready :=
    readyState_ready parameters nextWait nextWait_positive nextTail nextTail_unit
  have next_positive :=
    ready_isPositive parameters nextWait
      (readyState parameters nextWait nextTail) next_ready
  have state_sub_center_unit :
      IsUnit parameters.prime
        (readyState parameters nextWait nextTail - parameters.center) := by
    have center_sub_state :=
      unit_sub_positive parameters.center_unit next_positive
    rw [show readyState parameters nextWait nextTail - parameters.center =
      -(parameters.center - readyState parameters nextWait nextTail) by ring]
    exact neg_hasValue center_sub_state
  have scaled_drift_positive :
      IsPositive parameters.prime
        (drift parameters.center parameters.reset *
          parameters.prime ^ (parameters.depth * wait)) := by
    have scaled_value :=
      mul_hasValue parameters.drift_unit
        (primePower_hasValue (parameters.depth * wait))
    exact ⟨scaled_value.1, by
      rw [scaled_value.2]
      have positive_int : (0 : ℤ) < parameters.depth * wait := by
        exact_mod_cast Nat.mul_pos parameters.depth_positive wait_positive
      simpa using positive_int⟩
  have numerator_unit :
      IsUnit parameters.prime
        (readyState parameters nextWait nextTail -
          parameters.center -
            drift parameters.center parameters.reset *
              parameters.prime ^ (parameters.depth * wait)) :=
    unit_sub_positive state_sub_center_unit scaled_drift_positive
  have power_sub_one_unit :
      IsUnit parameters.prime (parameters.prime ^ wait - 1) :=
    positive_sub_one (primePower_positive parameters wait wait_positive)
  have denominator_unit :
      IsUnit parameters.prime
        (drift parameters.center parameters.reset *
          (parameters.prime ^ wait - 1)) :=
    mul_hasValue parameters.drift_unit power_sub_one_unit
  simpa [inverseTail] using
    div_hasValue numerator_unit denominator_unit

/-- The inverse tail realizes its named target state exactly. -/
theorem legalValue_inverseTail
    (parameters : Parameters)
    (wait nextWait : Nat) (wait_positive : 0 < wait) (nextTail : ℚ) :
    legalValue parameters wait
        (inverseTail parameters wait nextWait nextTail) =
      readyState parameters nextWait nextTail := by
  have denominator_ne :
      drift parameters.center parameters.reset *
          (parameters.prime ^ wait - 1) ≠ 0 := by
    refine mul_ne_zero parameters.drift_ne_zero ?_
    exact (primePower_positive parameters wait wait_positive |>
      positive_sub_one).1
  have power_sub_one_ne : (parameters.prime : ℚ) ^ wait - 1 ≠ 0 :=
    (primePower_positive parameters wait wait_positive |> positive_sub_one).1
  simp [legalValue, inverseTail]
  field_simp [denominator_ne, parameters.drift_ne_zero, power_sub_one_ne]
  ring

/-- The terminal tail is itself a p-adic unit. -/
theorem targetTail_isUnit
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait) :
    IsUnit parameters.prime (targetTail parameters wait) := by
  have one_sub_center_unit :
      IsUnit parameters.prime (1 - parameters.center) := by
    rw [show (1 : ℚ) - parameters.center =
      -(parameters.center - 1) by ring]
    exact neg_hasValue parameters.center_sub_one_unit
  have scaled_drift_positive :
      IsPositive parameters.prime
        (drift parameters.center parameters.reset *
          parameters.prime ^ (parameters.depth * wait)) := by
    have scaled_value :=
      mul_hasValue parameters.drift_unit
        (primePower_hasValue (parameters.depth * wait))
    exact ⟨scaled_value.1, by
      rw [scaled_value.2]
      have positive_int : (0 : ℤ) < parameters.depth * wait := by
        exact_mod_cast Nat.mul_pos parameters.depth_positive wait_positive
      simpa using positive_int⟩
  have numerator_unit :=
    unit_sub_positive one_sub_center_unit scaled_drift_positive
  have denominator_unit :
      IsUnit parameters.prime
        (drift parameters.center parameters.reset *
          (parameters.prime ^ wait - 1)) :=
    mul_hasValue parameters.drift_unit
      (positive_sub_one (primePower_positive parameters wait wait_positive))
  simpa [targetTail] using
    div_hasValue numerator_unit denominator_unit

/-- The displayed terminal tail makes the legal affine update exactly one. -/
theorem legalValue_targetTail
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait) :
    legalValue parameters wait (targetTail parameters wait) = 1 := by
  have denominator_ne :
      drift parameters.center parameters.reset *
          (parameters.prime ^ wait - 1) ≠ 0 :=
    (mul_hasValue parameters.drift_unit
      (positive_sub_one
        (primePower_positive parameters wait wait_positive))).1
  have power_sub_one_ne : (parameters.prime : ℚ) ^ wait - 1 ≠ 0 :=
    (primePower_positive parameters wait wait_positive |> positive_sub_one).1
  simp [legalValue, targetTail]
  field_simp [denominator_ne, parameters.drift_ne_zero, power_sub_one_ne]
  ring

/-- The terminal tail is the unique legal payload that reaches one. -/
theorem legalValue_eq_one_iff
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait)
    (tail : ℚ) :
    legalValue parameters wait tail = 1 ↔
      tail = targetTail parameters wait := by
  have coefficient_ne :
      drift parameters.center parameters.reset *
          (parameters.prime ^ wait - 1) ≠ 0 :=
    (mul_hasValue parameters.drift_unit
      (positive_sub_one
        (primePower_positive parameters wait wait_positive))).1
  constructor
  · intro reaches
    rw [targetTail, eq_div_iff coefficient_ne]
    rw [legalValue] at reaches
    linarith
  · rintro rfl
    exact legalValue_targetTail parameters wait wait_positive

/-- The legal symbolic graph on positive ready cylinders is complete. -/
theorem ready_transition
    (parameters : Parameters)
    (wait nextWait : Nat) (wait_positive : 0 < wait)
    (nextWait_positive : 0 < nextWait)
    (nextTail : ℚ) (nextTail_unit : IsUnit parameters.prime nextTail) :
    guardedStep parameters wait
        (some
          (readyState parameters wait
            (inverseTail parameters wait nextWait nextTail))) =
      some (readyState parameters nextWait nextTail) := by
  rw [ready_step parameters wait
    (inverseTail parameters wait nextWait nextTail)
    (inverseTail_isUnit parameters wait nextWait wait_positive
      nextWait_positive nextTail nextTail_unit).1]
  congr 1
  exact legalValue_inverseTail parameters wait nextWait wait_positive nextTail

/-- The center itself is a nonterminal unit in the trap. -/
theorem center_is_trap (parameters : Parameters) :
    Trap parameters (some parameters.center) := by
  rw [trap_some_iff]
  refine ⟨sub_ne_zero.mp parameters.center_sub_one_unit.1, ?_⟩
  intro center_positive
  have impossible := center_positive.2
  rw [parameters.center_unit.2] at impossible
  exact lt_irrefl 0 impossible

/-- A positive wait applied after the terminal point falls into the trap. -/
theorem target_step_is_trap
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait) :
    Trap parameters (guardedStep parameters wait (some 1)) := by
  have not_pole : (1 : ℚ) ≠ parameters.prime ^ wait := by
    exact ne_of_valuation_ne (by
      rw [padicValRat.one, primePower_valuation]
      exact ne_of_lt (by exact_mod_cast wait_positive))
  rw [guardedStep_some parameters wait 1 not_pole]
  simpa [guardDefect] using center_is_trap parameters

/-- One deterministic legal transition between ready affine states. -/
def LegalStep (parameters : Parameters) (source target : ℚ) : Prop :=
  ∃ index,
    Ready parameters (index + 1) source ∧
      guardedStep parameters (index + 1) (some source) = some target

/-- Deterministic target reachability induced by the guarded arithmetic map. -/
abbrev GuardedReachable (parameters : Parameters) : Prop :=
  Relation.TransGen (LegalStep parameters) parameters.reset 1

theorem legalStep_source_live
    (parameters : Parameters) {source target : ℚ}
    (step : LegalStep parameters source target) :
    IsPositive parameters.prime source := by
  obtain ⟨index, ready, _⟩ := step
  exact ready_isPositive parameters (index + 1) source ready

/-- The legal-step relation is single-valued. -/
theorem legalStep_functional
    (parameters : Parameters) {source left right : ℚ}
    (left_step : LegalStep parameters source left)
    (right_step : LegalStep parameters source right) :
    left = right := by
  obtain ⟨leftIndex, left_ready, left_action⟩ := left_step
  obtain ⟨rightIndex, right_ready, right_action⟩ := right_step
  have wait_eq : leftIndex + 1 = rightIndex + 1 := by
    exact_mod_cast left_ready.2.1.symm.trans right_ready.2.1
  have index_eq : leftIndex = rightIndex := Nat.add_right_cancel wait_eq
  subst rightIndex
  rw [left_action] at right_action
  exact Option.some.inj right_action

/-- Every surviving physical orbit is a legal deterministic path from the reset. -/
theorem guardedOrbit_survives
    (parameters : Parameters) (waits : List Nat)
    (survives : ¬Trap parameters (guardedOrbit parameters waits)) :
    ∃ z,
      guardedOrbit parameters waits = some z ∧
        Relation.ReflTransGen (LegalStep parameters) parameters.reset z := by
  induction waits with
  | nil =>
      exact ⟨parameters.reset, rfl, Relation.ReflTransGen.refl⟩
  | cons index tail induction =>
      have tail_survives :
          ¬Trap parameters (guardedOrbit parameters tail) := by
        intro tail_trapped
        apply survives
        simpa [guardedOrbit, rayState] using
          trap_forward parameters (index + 1) (by omega) tail_trapped
      obtain ⟨middle, middle_action, middle_reachable⟩ :=
        induction tail_survives
      change
        rayState (fun index => guardedStep parameters (index + 1))
          tail (some parameters.reset) = some middle at middle_action
      have middle_not_target : middle ≠ 1 := by
        intro middle_target
        apply survives
        change Trap parameters
          (guardedStep parameters (index + 1)
            (rayState (fun index => guardedStep parameters (index + 1))
              tail (some parameters.reset)))
        rw [middle_action, middle_target]
        exact target_step_is_trap parameters (index + 1) (by omega)
      have middle_live : IsPositive parameters.prime middle := by
        have middle_survives : ¬Trap parameters (some middle) := by
          intro middle_trapped
          apply tail_survives
          change Trap parameters
            (rayState (fun index => guardedStep parameters (index + 1))
              tail (some parameters.reset))
          rw [middle_action]
          exact middle_trapped
        have alternatives :=
          (not_trap_iff parameters (some middle)).mp middle_survives
        rcases alternatives with target | live
        · exact (middle_not_target (Option.some.inj target)).elim
        · exact live
      have final_survives :
          ¬Trap parameters
            (guardedStep parameters (index + 1) (some middle)) := by
        intro final_trapped
        apply survives
        change Trap parameters
          (guardedStep parameters (index + 1)
            (rayState (fun index => guardedStep parameters (index + 1))
              tail (some parameters.reset)))
        rw [middle_action]
        exact final_trapped
      have ready :=
        live_step_forces_ready parameters (index + 1) (by omega)
          middle middle_live final_survives
      cases final_action :
          guardedStep parameters (index + 1) (some middle) with
      | none =>
          apply (final_survives (by
            rw [final_action]
            exact trap_infinity parameters)).elim
      | some target =>
          refine ⟨target, ?_, middle_reachable.tail ?_⟩
          · change
              guardedStep parameters (index + 1)
                (rayState (fun index => guardedStep parameters (index + 1))
                  tail (some parameters.reset)) = some target
            rw [middle_action, final_action]
          · exact ⟨index, ready, final_action⟩

/-- Every legal path has a physical positive-return word with the same endpoint. -/
theorem reflTransGen_exists_guardedOrbit
    (parameters : Parameters) {target : ℚ}
    (reachable :
      Relation.ReflTransGen (LegalStep parameters) parameters.reset target) :
    ∃ waits, guardedOrbit parameters waits = some target := by
  induction reachable with
  | refl => exact ⟨[], rfl⟩
  | tail _ edge induction =>
      obtain ⟨waits, orbit_eq⟩ := induction
      change
        rayState (fun index => guardedStep parameters (index + 1))
          waits (some parameters.reset) = some _ at orbit_eq
      obtain ⟨index, _, step_eq⟩ := edge
      exact ⟨index :: waits, by
        change
          guardedStep parameters (index + 1)
            (rayState (fun index => guardedStep parameters (index + 1))
              waits (some parameters.reset)) = some _
        rw [orbit_eq, step_eq]⟩

/-- The matrix pair is mortal exactly when the single guarded arithmetic orbit reaches one. -/
theorem physical_isMortal_iff_guardedReachable (parameters : Parameters) :
    IsMortal
        (ReturnFamily.pairGenerator
          (ambient (parameters.prime : ℚ) parameters.depth)
          (cut parameters.center parameters.reset)) ↔
      GuardedReachable parameters := by
  rw [physical_isMortal_iff_guardedOrbit]
  constructor
  · rintro ⟨waits, reaches_target⟩
    have target_survives : ¬Trap parameters (guardedOrbit parameters waits) := by
      rw [reaches_target, Trap]
      simp [Live]
    obtain ⟨target, target_eq, reachable⟩ :=
      guardedOrbit_survives parameters waits target_survives
    have target_one : target = 1 := by
      rw [reaches_target] at target_eq
      exact Option.some.inj target_eq.symm
    subst target
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp reachable with
      reset_target | reaches
    · have reset_ne_one := (positive_sub_one parameters.reset_positive).1
      exact (reset_ne_one (sub_eq_zero.mpr reset_target.symm)).elim
    · exact reaches
  · intro reaches
    obtain ⟨waits, orbit_eq⟩ :=
      reflTransGen_exists_guardedOrbit parameters reaches.to_reflTransGen
    exact ⟨waits, orbit_eq⟩

/-- The guarded return series is intrinsically three-dimensional. -/
theorem parameters_three_le_card_of_exact_realization
    (parameters : Parameters)
    {Big : Type*} [Fintype Big] [DecidableEq Big]
    (otherAmbient : Square Big ℚ)
    (otherInput : Matrix Big (Fin 2) ℚ)
    (otherOutput : Matrix (Fin 2) Big ℚ)
    (exact :
      ∀ wait,
        ReturnFamily.returnMatrix otherAmbient otherInput otherOutput wait =
          returnAt parameters.prime parameters.depth
            parameters.center parameters.reset wait) :
    3 ≤ Fintype.card Big := by
  have prime_gt_one : (1 : ℚ) < parameters.prime := by
    exact_mod_cast parameters.prime_prime.one_lt
  have inverse_lt_one : (parameters.prime : ℚ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ prime_gt_one
  have exponent_positive : 0 < parameters.depth - 1 := by
    exact Nat.sub_pos_of_lt
      (lt_of_lt_of_le Nat.one_lt_two parameters.depth_two)
  have expanding_gt_one :
      (1 : ℚ) < parameters.prime ^ (parameters.depth - 1) :=
    one_lt_pow₀ prime_gt_one exponent_positive.ne'
  exact three_le_card_of_exact_realization
    parameters.prime parameters.depth parameters.center parameters.reset
    otherAmbient otherInput otherOutput exact
    parameters.center_unit.1 parameters.drift_ne_zero
    (by linarith) (by linarith)

end
end MatrixMortality.ReturnGuard
