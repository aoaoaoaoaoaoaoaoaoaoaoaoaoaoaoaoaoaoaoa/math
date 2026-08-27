import MatrixMortality.ReturnGuardIntegralLift
import MatrixMortality.ReturnGuardValuation

/-!
# Exact expansion and rational gaps in decoded guard dynamics

On one legal residual branch the guard map is an exact p-adic similarity: it subtracts
`depth * wait` from every finite separation depth.  A legal word therefore expands by the
sum of its wait weights.  This makes recurrence to a fixed rational checkpoint rigid, because
distinct primitive rational rays have an Archimedean height-controlled p-adic gap.

The resulting pumping lemmas rule out an unbounded counter stored by increasingly accurate
returns of one fixed macro.  Any surviving universal mechanism must move its checkpoint or its
macro rather than deepen a fixed rational recurrence.
-/

namespace MatrixMortality.ReturnGuard

open MatrixMortality.PadicValuation

noncomputable section

/-- Forward execution of a prescribed decoded wait schedule. -/
def residualRun (parameters : Parameters) : List Nat → ℚ → ℚ
  | [], source => source
  | wait :: waits, source =>
      residualRun parameters waits (residualStep parameters wait source)

/-- Every successive residual lies on the branch selected by the prescribed schedule. -/
def FollowsResidualSchedule
    (parameters : Parameters) : List Nat → ℚ → Prop
  | [], _ => True
  | wait :: waits, source =>
      ResidualBranch parameters wait source ∧
        FollowsResidualSchedule parameters waits
          (residualStep parameters wait source)

/-- Total p-adic expansion weight of a wait schedule. -/
def scheduleWeight (parameters : Parameters) (waits : List Nat) : ℤ :=
  parameters.depth * waits.sum

/-- Natural-number form of the schedule weight. -/
def scheduleNatWeight (parameters : Parameters) (waits : List Nat) : Nat :=
  parameters.depth * waits.sum

theorem scheduleWeight_eq_natCast
    (parameters : Parameters) (waits : List Nat) :
    scheduleWeight parameters waits = scheduleNatWeight parameters waits := by
  simp [scheduleWeight, scheduleNatWeight]

@[simp]
theorem residualRun_nil (parameters : Parameters) (source : ℚ) :
    residualRun parameters [] source = source := rfl

@[simp]
theorem residualRun_cons
    (parameters : Parameters) (wait : Nat) (waits : List Nat) (source : ℚ) :
    residualRun parameters (wait :: waits) source =
      residualRun parameters waits (residualStep parameters wait source) := rfl

@[simp]
theorem followsResidualSchedule_nil
    (parameters : Parameters) (source : ℚ) :
    FollowsResidualSchedule parameters [] source := trivial

@[simp]
theorem followsResidualSchedule_cons
    (parameters : Parameters) (wait : Nat) (waits : List Nat) (source : ℚ) :
    FollowsResidualSchedule parameters (wait :: waits) source ↔
      ResidualBranch parameters wait source ∧
        FollowsResidualSchedule parameters waits
          (residualStep parameters wait source) := Iff.rfl

@[simp]
theorem scheduleWeight_nil (parameters : Parameters) :
    scheduleWeight parameters [] = 0 := by
  simp [scheduleWeight]

@[simp]
theorem scheduleWeight_cons
    (parameters : Parameters) (wait : Nat) (waits : List Nat) :
    scheduleWeight parameters (wait :: waits) =
      parameters.depth * wait + scheduleWeight parameters waits := by
  simp [scheduleWeight]
  ring

theorem scheduleWeight_append
    (parameters : Parameters) (left right : List Nat) :
    scheduleWeight parameters (left ++ right) =
      scheduleWeight parameters left + scheduleWeight parameters right := by
  simp [scheduleWeight]
  ring

theorem residualRun_append
    (parameters : Parameters) (left right : List Nat) (source : ℚ) :
    residualRun parameters (left ++ right) source =
      residualRun parameters right (residualRun parameters left source) := by
  induction left generalizing source with
  | nil => rfl
  | cons wait waits induction =>
      simp only [List.cons_append, residualRun_cons]
      exact induction (residualStep parameters wait source)

theorem followsResidualSchedule_append
    (parameters : Parameters) (left right : List Nat) (source : ℚ) :
    FollowsResidualSchedule parameters (left ++ right) source ↔
      FollowsResidualSchedule parameters left source ∧
        FollowsResidualSchedule parameters right
          (residualRun parameters left source) := by
  induction left generalizing source with
  | nil => simp
  | cons wait waits induction =>
      simp only [List.cons_append, followsResidualSchedule_cons,
        residualRun_cons]
      rw [induction]
      tauto

/-- Exact determinant identity for the decoded Möbius branch. -/
theorem residualStep_sub
    (parameters : Parameters) (wait : Nat) (left right : ℚ)
    (left_denominator_ne :
      (parameters.center - 1) * left +
        drift parameters.center parameters.reset ≠ 0)
    (right_denominator_ne :
      (parameters.center - 1) * right +
        drift parameters.center parameters.reset ≠ 0) :
    residualStep parameters wait left -
        residualStep parameters wait right =
      drift parameters.center parameters.reset *
          (1 - parameters.prime ^ wait) * (left - right) /
        (parameters.prime ^ (parameters.depth * wait) *
          ((parameters.center - 1) * left +
            drift parameters.center parameters.reset) *
          ((parameters.center - 1) * right +
            drift parameters.center parameters.reset)) := by
  rw [residualStep_eq parameters wait left left_denominator_ne,
    residualStep_eq parameters wait right right_denominator_ne]
  have power_ne :
      (parameters.prime : ℚ) ^ (parameters.depth * wait) ≠ 0 :=
    primePower_ne_zero parameters.prime_prime _
  rw [div_sub_div _ _
    (mul_ne_zero power_ne left_denominator_ne)
    (mul_ne_zero power_ne right_denominator_ne)]
  field_simp [power_ne, left_denominator_ne, right_denominator_ne]
  ring

/-- One common legal branch subtracts exactly `depth * wait` from p-adic separation. -/
theorem residualStep_sub_hasValue
    (parameters : Parameters) {wait : Nat} {left right : ℚ}
    {separation : ℤ}
    (left_branch : ResidualBranch parameters wait left)
    (right_branch : ResidualBranch parameters wait right)
    (difference : HasValue parameters.prime (left - right) separation) :
    HasValue parameters.prime
      (residualStep parameters wait left -
        residualStep parameters wait right)
      (separation - parameters.depth * wait) := by
  have left_denominator :=
    centerTransform_denominator_isUnit_of_branch
      parameters wait left left_branch
  have right_denominator :=
    centerTransform_denominator_isUnit_of_branch
      parameters wait right right_branch
  rw [residualStep_sub parameters wait left right
    left_denominator.1 right_denominator.1]
  have wait_power_positive :
      IsPositive parameters.prime ((parameters.prime : ℚ) ^ wait) := by
    exact ⟨primePower_ne_zero parameters.prime_prime wait, by
      rw [primePower_valuation]
      exact_mod_cast left_branch.1⟩
  have cyclotomic_unit : IsUnit parameters.prime
      (1 - (parameters.prime : ℚ) ^ wait) :=
    one_sub_positive wait_power_positive
  have numerator_value :
      HasValue parameters.prime
        (drift parameters.center parameters.reset *
          (1 - parameters.prime ^ wait) * (left - right))
        separation := by
    convert
      mul_hasValue
        (mul_hasValue parameters.drift_unit cyclotomic_unit)
        difference using 1
    ring
  have denominator_value :
      HasValue parameters.prime
        (parameters.prime ^ (parameters.depth * wait) *
          ((parameters.center - 1) * left +
            drift parameters.center parameters.reset) *
          ((parameters.center - 1) * right +
            drift parameters.center parameters.reset))
        (parameters.depth * wait) := by
    convert
      mul_hasValue
        (mul_hasValue (primePower_hasValue (parameters.depth * wait))
          left_denominator)
        right_denominator using 1
    push_cast
    ring
  simpa using div_hasValue numerator_value denominator_value

/-- A perturbation deeper than one branch sphere preserves that branch. -/
theorem residualBranch_of_deep_sub
    (parameters : Parameters) {wait : Nat} {left right : ℚ}
    {separation : ℤ}
    (left_branch : ResidualBranch parameters wait left)
    (difference : HasValue parameters.prime (left - right) separation)
    (deeper : parameters.depth * wait < separation) :
    ResidualBranch parameters wait right := by
  refine ⟨left_branch.1, ?_⟩
  have translated :
      right - residualBranchCenter parameters wait =
        (left - residualBranchCenter parameters wait) - (left - right) := by
    ring
  rw [translated]
  have result :=
    add_hasValue_left left_branch.2 (neg_hasValue difference) deeper
  simpa only [sub_eq_add_neg] using result

/-- A common legal word subtracts exactly its total weight from separation depth. -/
theorem residualRun_sub_hasValue
    (parameters : Parameters) (waits : List Nat) {left right : ℚ}
    {separation : ℤ}
    (left_follows : FollowsResidualSchedule parameters waits left)
    (right_follows : FollowsResidualSchedule parameters waits right)
    (difference : HasValue parameters.prime (left - right) separation) :
    HasValue parameters.prime
      (residualRun parameters waits left -
        residualRun parameters waits right)
      (separation - scheduleWeight parameters waits) := by
  induction waits generalizing left right separation with
  | nil =>
      simpa using difference
  | cons wait waits induction =>
      rw [followsResidualSchedule_cons] at left_follows right_follows
      have stepped :=
        residualStep_sub_hasValue parameters
          left_follows.1 right_follows.1 difference
      have tail :=
        induction left_follows.2 right_follows.2 stepped
      convert tail using 1
      · simp only [residualRun_cons]
      · rw [scheduleWeight_cons]
        ring

/-- A perturbation deeper than the full schedule weight follows the same legal schedule. -/
theorem followsResidualSchedule_of_deep_sub
    (parameters : Parameters) (waits : List Nat) {left right : ℚ}
    {separation : ℤ}
    (left_follows : FollowsResidualSchedule parameters waits left)
    (difference : HasValue parameters.prime (left - right) separation)
    (deeper : scheduleWeight parameters waits < separation) :
    FollowsResidualSchedule parameters waits right := by
  induction waits generalizing left right separation with
  | nil => trivial
  | cons wait waits induction =>
      rw [followsResidualSchedule_cons] at left_follows ⊢
      have head_deeper : parameters.depth * wait < separation := by
        rw [scheduleWeight_cons] at deeper
        have tail_weight_nonnegative :
            0 ≤ scheduleWeight parameters waits := by
          simp only [scheduleWeight, Nat.cast_nonneg, mul_nonneg]
        omega
      have right_branch :=
        residualBranch_of_deep_sub parameters left_follows.1
          difference head_deeper
      refine ⟨right_branch, ?_⟩
      have stepped :=
        residualStep_sub_hasValue parameters
          left_follows.1 right_branch difference
      apply induction left_follows.2 stepped
      rw [scheduleWeight_cons] at deeper
      omega

/-- Determinant measuring whether two integral projective rays coincide. -/
def projectivePairCross (source target : ℤ × ℤ) : ℤ :=
  target.2 * source.1 - target.1 * source.2

/-- Height of an integral projective pair. -/
def projectivePairHeight (pair : ℤ × ℤ) : Nat :=
  integralPairHeight pair.1 pair.2

/-- A projective determinant is bounded by twice the product of the two ray heights. -/
theorem projectivePairCross_natAbs_le
    (source target : ℤ × ℤ) :
    (projectivePairCross source target).natAbs ≤
      2 * projectivePairHeight source * projectivePairHeight target := by
  have source_numerator_le :
      source.1.natAbs ≤ projectivePairHeight source :=
    le_max_left _ _
  have source_denominator_le :
      source.2.natAbs ≤ projectivePairHeight source :=
    le_max_right _ _
  have target_numerator_le :
      target.1.natAbs ≤ projectivePairHeight target :=
    le_max_left _ _
  have target_denominator_le :
      target.2.natAbs ≤ projectivePairHeight target :=
    le_max_right _ _
  calc
    (projectivePairCross source target).natAbs ≤
        (target.2 * source.1).natAbs +
          (target.1 * source.2).natAbs := by
      simpa only [projectivePairCross] using
        Int.natAbs_sub_le (target.2 * source.1) (target.1 * source.2)
    _ =
        target.2.natAbs * source.1.natAbs +
          target.1.natAbs * source.2.natAbs := by
      simp only [Int.natAbs_mul]
    _ ≤
        projectivePairHeight target * projectivePairHeight source +
          projectivePairHeight target * projectivePairHeight source :=
      Nat.add_le_add
        (Nat.mul_le_mul target_denominator_le source_numerator_le)
        (Nat.mul_le_mul target_numerator_le source_denominator_le)
    _ = 2 * projectivePairHeight source * projectivePairHeight target := by
      ring

/-- A nonzero determinant divisible by `prime^depth` has correspondingly large height. -/
theorem primePower_le_pairHeight_of_dvd_cross
    {prime depth : Nat} {source target : ℤ × ℤ}
    (cross_ne : projectivePairCross source target ≠ 0)
    (divides :
      (prime : ℤ) ^ depth ∣ projectivePairCross source target) :
    prime ^ depth ≤
      2 * projectivePairHeight source * projectivePairHeight target := by
  have divisor_le :
      ((prime : ℤ) ^ depth).natAbs ≤
        (projectivePairCross source target).natAbs :=
    Int.natAbs_le_of_dvd_ne_zero divides cross_ne
  have cast_abs :
      ((prime : ℤ) ^ depth).natAbs = prime ^ depth := by
    rw [Int.natAbs_pow, Int.natAbs_natCast]
  rw [cast_abs] at divisor_le
  exact divisor_le.trans (projectivePairCross_natAbs_le source target)

/-- The canonical rational pair determinant represents the ordinary rational difference. -/
theorem rationalPairCross_div_denominators
    (left right : ℚ) :
    (projectivePairCross (rationalPair left) (rationalPair right) : ℚ) /
        ((left.den : ℚ) * right.den) =
      left - right := by
  have left_den_ne : (left.den : ℚ) ≠ 0 := by
    exact_mod_cast left.den_ne_zero
  have right_den_ne : (right.den : ℚ) ≠ 0 := by
    exact_mod_cast right.den_ne_zero
  calc
    _ =
        (left.num : ℚ) / left.den -
          (right.num : ℚ) / right.den := by
      simp only [projectivePairCross, rationalPair_fst, rationalPair_snd,
        Int.cast_sub, Int.cast_mul, Int.cast_natCast]
      field_simp [left_den_ne, right_den_ne]
    _ = left - right := by rw [left.num_div_den, right.num_div_den]

/-- Distinct rationals have distinct canonical projective rays. -/
theorem rationalPairCross_ne_zero
    {left right : ℚ} (distinct : left ≠ right) :
    projectivePairCross (rationalPair left) (rationalPair right) ≠ 0 := by
  intro cross_zero
  apply distinct
  have represented := rationalPairCross_div_denominators left right
  rw [cross_zero] at represented
  simpa only [Int.cast_zero, zero_div, sub_eq_zero] using represented.symm

/-- For p-adic units, rational separation depth is exactly the valuation of the canonical
projective determinant. -/
theorem rationalPairCross_padicValInt
    (parameters : Parameters) {left right : ℚ} {separation : Nat}
    (left_unit : IsUnit parameters.prime left)
    (right_unit : IsUnit parameters.prime right)
    (difference :
      HasValue parameters.prime (left - right) separation) :
    padicValInt parameters.prime
        (projectivePairCross (rationalPair left) (rationalPair right)) =
      separation := by
  have left_den_unit :
      IsUnit parameters.prime (left.den : ℚ) :=
    intCast_isUnit_of_not_dvd
      (rat_denominator_not_dvd_of_isUnit left_unit)
  have right_den_unit :
      IsUnit parameters.prime (right.den : ℚ) :=
    intCast_isUnit_of_not_dvd
      (rat_denominator_not_dvd_of_isUnit right_unit)
  have denominator_unit :
      IsUnit parameters.prime ((left.den : ℚ) * right.den) :=
    mul_hasValue left_den_unit right_den_unit
  have cross_eq :
      (projectivePairCross (rationalPair left) (rationalPair right) : ℚ) =
        (left - right) * ((left.den : ℚ) * right.den) := by
    apply (div_eq_iff denominator_unit.1).1
    exact rationalPairCross_div_denominators left right
  have cross_value :
      HasValue parameters.prime
        (projectivePairCross (rationalPair left) (rationalPair right) : ℚ)
        separation := by
    rw [cross_eq]
    exact mul_hasValue difference denominator_unit
  have valuation_eq :
      (padicValInt parameters.prime
        (projectivePairCross (rationalPair left) (rationalPair right)) : ℤ) =
      separation := by
    simpa only [padicValRat.of_int] using cross_value.2
  exact_mod_cast valuation_eq

/-- Fixed-rational-target gap: distinct unit rationals cannot be p-adically closer than their
primitive projective heights permit. -/
theorem primePower_le_rationalPairHeight
    (parameters : Parameters) {left right : ℚ} {separation : Nat}
    (left_unit : IsUnit parameters.prime left)
    (right_unit : IsUnit parameters.prime right)
    (distinct : left ≠ right)
    (difference :
      HasValue parameters.prime (left - right) separation) :
    parameters.prime ^ separation ≤
      2 * projectivePairHeight (rationalPair left) *
        projectivePairHeight (rationalPair right) := by
  apply primePower_le_pairHeight_of_dvd_cross
    (rationalPairCross_ne_zero distinct)
  rw [padicValInt_dvd_iff]
  exact Or.inr (by
    rw [rationalPairCross_padicValInt parameters
      left_unit right_unit difference])

/-- Parameter-dependent one-step height coefficient. -/
def guardHeightCoefficient
    (centerNumerator driftNumerator scale : ℤ) : Nat :=
  centerNumerator.natAbs + driftNumerator.natAbs + scale.natAbs

/-- One decoded legal step grows canonical projective height by at most the fixed parameter
coefficient. -/
theorem decodedStep_rationalPairHeight_le
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    {source target : ℚ}
    (decoded : DecodedStep parameters source target) :
    projectivePairHeight (rationalPair target) ≤
      guardHeightCoefficient centerNumerator driftNumerator scale *
        projectivePairHeight (rationalPair source) := by
  obtain ⟨wait, branch, image_eq⟩ := decoded
  have target_unit :
      IsUnit parameters.prime target := by
    rw [← image_eq]
    exact residualStep_isUnit_of_branch parameters wait source branch
  have terminal_ne :
      terminalDefect centerNumerator driftNumerator scale
        source.num source.den ≠ 0 := by
    intro terminal_zero
    have ratio :=
      residualStep_eq_integralRatio parameters center_eq drift_eq scale_ne branch
    rw [terminal_zero] at ratio
    simp only [Int.cast_zero, mul_zero, div_zero] at ratio
    exact target_unit.1 (image_eq ▸ ratio)
  have lifted :=
    decodedStep_primitiveIntegralStep
      parameters center_eq drift_eq scale_ne
      ⟨wait, branch, image_eq⟩
  rcases lifted with
    ⟨_, _, liftedWait, nextNumerator, nextDenominator, common,
      integral, numerator_reduced, denominator_reduced⟩
  have common_ne : common ≠ 0 := by
    intro common_zero
    apply terminal_ne
    have terminal_zero :
        terminalDefect centerNumerator driftNumerator scale
            (rationalPair source).1 (rationalPair source).2 =
          0 := by
      rw [← integral.2, denominator_reduced, common_zero, zero_mul]
    simpa using terminal_zero
  simpa [projectivePairHeight, guardHeightCoefficient] using
    integralStep_reduced_height_le integral
      numerator_reduced denominator_reduced common_ne
      parameters.prime_prime.pos parameters.depth_positive

/-- An `n`-step decoded execution grows canonical height by at most the `n`th power of the
fixed one-step coefficient. -/
theorem decodedExecution_rationalPairHeight_le
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    {steps : Nat} {source target : ℚ}
    (execution :
      Relation.ReachesIn (DecodedStep parameters) steps source target) :
    projectivePairHeight (rationalPair target) ≤
      guardHeightCoefficient centerNumerator driftNumerator scale ^ steps *
        projectivePairHeight (rationalPair source) := by
  induction execution with
  | refl => simp
  | @head steps before middle after first _ induction =>
      have first_bound :=
        decodedStep_rationalPairHeight_le parameters center_eq drift_eq
          scale_ne first
      calc
        projectivePairHeight (rationalPair after) ≤
            guardHeightCoefficient centerNumerator driftNumerator scale ^ steps *
              projectivePairHeight (rationalPair middle) :=
          induction
        _ ≤
            guardHeightCoefficient centerNumerator driftNumerator scale ^ steps *
              (guardHeightCoefficient centerNumerator driftNumerator scale *
                projectivePairHeight (rationalPair before)) :=
          Nat.mul_le_mul_left _ first_bound
        _ =
            guardHeightCoefficient centerNumerator driftNumerator scale ^
                (steps + 1) *
              projectivePairHeight (rationalPair before) := by
          rw [pow_succ]
          ring

/-- Canonical decoded schedules are exact indexed executions. -/
theorem followsResidualSchedule_reachesIn
    (parameters : Parameters) (waits : List Nat) (source : ℚ)
    (follows : FollowsResidualSchedule parameters waits source) :
    Relation.ReachesIn (DecodedStep parameters) waits.length source
      (residualRun parameters waits source) := by
  induction waits generalizing source with
  | nil => exact .refl source
  | cons wait waits induction =>
      rw [followsResidualSchedule_cons] at follows
      exact .head ⟨wait, follows.1, rfl⟩
        (induction (residualStep parameters wait source) follows.2)

/-- Height envelope for one canonical decoded schedule. -/
theorem residualRun_rationalPairHeight_le
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    (waits : List Nat) (source : ℚ)
    (follows : FollowsResidualSchedule parameters waits source) :
    projectivePairHeight
        (rationalPair (residualRun parameters waits source)) ≤
      guardHeightCoefficient centerNumerator driftNumerator scale ^
          waits.length *
        projectivePairHeight (rationalPair source) :=
  decodedExecution_rationalPairHeight_le
    parameters center_eq drift_eq scale_ne
    (followsResidualSchedule_reachesIn parameters waits source follows)

/-- Repetition of one fixed wait macro. -/
def repeatSchedule (waits : List Nat) : Nat → List Nat
  | 0 => []
  | repetitions + 1 => repeatSchedule waits repetitions ++ waits

/-- Orbit under repeated application of one decoded macro. -/
def residualMacroOrbit
    (parameters : Parameters) (waits : List Nat) (source : ℚ) : Nat → ℚ
  | 0 => source
  | repetitions + 1 =>
      residualRun parameters waits
        (residualMacroOrbit parameters waits source repetitions)

@[simp]
theorem repeatSchedule_zero (waits : List Nat) :
    repeatSchedule waits 0 = [] := rfl

@[simp]
theorem repeatSchedule_succ (waits : List Nat) (repetitions : Nat) :
    repeatSchedule waits (repetitions + 1) =
      repeatSchedule waits repetitions ++ waits := rfl

@[simp]
theorem residualMacroOrbit_zero
    (parameters : Parameters) (waits : List Nat) (source : ℚ) :
    residualMacroOrbit parameters waits source 0 = source := rfl

@[simp]
theorem residualMacroOrbit_succ
    (parameters : Parameters) (waits : List Nat) (source : ℚ)
    (repetitions : Nat) :
    residualMacroOrbit parameters waits source (repetitions + 1) =
      residualRun parameters waits
        (residualMacroOrbit parameters waits source repetitions) := rfl

theorem residualRun_repeatSchedule
    (parameters : Parameters) (waits : List Nat) (source : ℚ)
    (repetitions : Nat) :
    residualRun parameters (repeatSchedule waits repetitions) source =
      residualMacroOrbit parameters waits source repetitions := by
  induction repetitions generalizing source with
  | zero => rfl
  | succ repetitions induction =>
      rw [repeatSchedule_succ, residualRun_append, residualMacroOrbit_succ]
      rw [induction]

theorem repeatSchedule_succ_eq_prepend
    (waits : List Nat) (repetitions : Nat) :
    repeatSchedule waits (repetitions + 1) =
      waits ++ repeatSchedule waits repetitions := by
  induction repetitions with
  | zero => simp
  | succ repetitions induction =>
      calc
        repeatSchedule waits (repetitions + 2) =
            repeatSchedule waits (repetitions + 1) ++ waits := rfl
        _ = (waits ++ repeatSchedule waits repetitions) ++ waits := by
          rw [induction]
        _ = waits ++ (repeatSchedule waits repetitions ++ waits) := by
          rw [List.append_assoc]
        _ = waits ++ repeatSchedule waits (repetitions + 1) := rfl

theorem scheduleWeight_repeatSchedule
    (parameters : Parameters) (waits : List Nat) (repetitions : Nat) :
    scheduleWeight parameters (repeatSchedule waits repetitions) =
      repetitions * scheduleNatWeight parameters waits := by
  induction repetitions with
  | zero => simp
  | succ repetitions induction =>
      rw [repeatSchedule_succ, scheduleWeight_append, induction,
        scheduleWeight_eq_natCast]
      push_cast
      ring

/-- Every legal schedule ending in the residual unit shell stays in that shell. -/
theorem residualRun_isUnit
    (parameters : Parameters) (waits : List Nat) (source : ℚ)
    (source_unit : IsUnit parameters.prime source)
    (follows : FollowsResidualSchedule parameters waits source) :
    IsUnit parameters.prime (residualRun parameters waits source) := by
  induction waits generalizing source with
  | nil => exact source_unit
  | cons wait waits induction =>
      rw [followsResidualSchedule_cons] at follows
      have next_unit :=
        residualStep_isUnit_of_branch parameters wait source follows.1
      exact induction (residualStep parameters wait source) next_unit follows.2

/-- A deep return to one checkpoint pumps every bounded number of repetitions of the same
macro, with exactly linear loss of return depth. -/
theorem residualMacroOrbit_follows_and_separates
    (parameters : Parameters) (waits : List Nat) (checkpoint : ℚ)
    {returnDepth : Nat}
    (checkpoint_follows :
      FollowsResidualSchedule parameters waits checkpoint)
    (returns :
      HasValue parameters.prime
        (residualMacroOrbit parameters waits checkpoint 1 - checkpoint)
        returnDepth) :
    ∀ repetitions : Nat,
      repetitions * scheduleNatWeight parameters waits < returnDepth →
        FollowsResidualSchedule parameters waits
            (residualMacroOrbit parameters waits checkpoint repetitions) ∧
          HasValue parameters.prime
            (residualMacroOrbit parameters waits checkpoint (repetitions + 1) -
              residualMacroOrbit parameters waits checkpoint repetitions)
            ((returnDepth : ℤ) -
              (repetitions : ℤ) *
                scheduleNatWeight parameters waits) := by
  intro repetitions
  induction repetitions with
  | zero =>
      intro _
      simpa using ⟨checkpoint_follows, returns⟩
  | succ repetitions induction =>
      intro bound
      have split_weight :
          (repetitions + 1) * scheduleNatWeight parameters waits =
            repetitions * scheduleNatWeight parameters waits +
              scheduleNatWeight parameters waits := by
        ring
      have prior_bound :
          repetitions * scheduleNatWeight parameters waits < returnDepth := by
        rw [split_weight] at bound
        omega
      obtain ⟨prior_follows, prior_separation⟩ := induction prior_bound
      have one_weight_deep :
          scheduleWeight parameters waits <
            (returnDepth : ℤ) -
              (repetitions : ℤ) *
                scheduleNatWeight parameters waits := by
        rw [scheduleWeight_eq_natCast]
        have nat_deep :
            scheduleNatWeight parameters waits +
                repetitions * scheduleNatWeight parameters waits <
              returnDepth := by
          rw [split_weight] at bound
          omega
        have cast_deep :
            (scheduleNatWeight parameters waits : ℤ) +
                (repetitions : ℤ) *
                  scheduleNatWeight parameters waits <
              (returnDepth : ℤ) := by
          exact_mod_cast nat_deep
        apply (lt_sub_iff_add_lt).2
        simpa [add_comm] using cast_deep
      have current_follows :
          FollowsResidualSchedule parameters waits
            (residualMacroOrbit parameters waits checkpoint
              (repetitions + 1)) := by
        have reversed :
            HasValue parameters.prime
              (residualMacroOrbit parameters waits checkpoint repetitions -
                residualMacroOrbit parameters waits checkpoint
                  (repetitions + 1))
              ((returnDepth : ℤ) -
                (repetitions : ℤ) *
                  scheduleNatWeight parameters waits) := by
          rw [show
            residualMacroOrbit parameters waits checkpoint repetitions -
                residualMacroOrbit parameters waits checkpoint
                  (repetitions + 1) =
              -(residualMacroOrbit parameters waits checkpoint
                  (repetitions + 1) -
                residualMacroOrbit parameters waits checkpoint repetitions) by
              ring]
          exact neg_hasValue prior_separation
        apply followsResidualSchedule_of_deep_sub
          parameters waits prior_follows reversed
        exact one_weight_deep
      refine ⟨current_follows, ?_⟩
      have transported :=
        residualRun_sub_hasValue parameters waits
          current_follows prior_follows prior_separation
      convert transported using 1
      · simp only [residualMacroOrbit_succ]
      · rw [scheduleWeight_eq_natCast]
        push_cast
        ring

/-- A repeated legal macro forces its first return to be at least linearly deep unless that
return is already exact. -/
theorem repeatedMacro_returnDepth_le
    (parameters : Parameters) (waits : List Nat) (checkpoint : ℚ)
    {repetitions returnDepth : Nat}
    (repetitions_positive : 0 < repetitions)
    (checkpoint_unit : IsUnit parameters.prime checkpoint)
    (return_depth :
      HasValue parameters.prime
        (residualMacroOrbit parameters waits checkpoint 1 - checkpoint)
        returnDepth)
    (checkpoint_repeats :
      FollowsResidualSchedule parameters
        (repeatSchedule waits repetitions) checkpoint) :
    (repetitions - 1) * scheduleNatWeight parameters waits ≤ returnDepth := by
  obtain ⟨prior, repetitions_eq⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt repetitions_positive)
  subst repetitions
  have checkpoint_tail :
      FollowsResidualSchedule parameters
        (repeatSchedule waits prior) checkpoint := by
    have repeated_append := checkpoint_repeats
    rw [repeatSchedule_succ,
      followsResidualSchedule_append] at repeated_append
    exact repeated_append.1
  have return_tail :
      FollowsResidualSchedule parameters
        (repeatSchedule waits prior)
        (residualMacroOrbit parameters waits checkpoint 1) := by
    have repeated_prepend := checkpoint_repeats
    rw [repeatSchedule_succ_eq_prepend,
      followsResidualSchedule_append] at repeated_prepend
    simpa using repeated_prepend.2
  have transported :=
    residualRun_sub_hasValue parameters
      (repeatSchedule waits prior)
      return_tail checkpoint_tail return_depth
  rw [scheduleWeight_repeatSchedule] at transported
  have checkpoint_follows :
      FollowsResidualSchedule parameters waits checkpoint := by
    have repeated_prepend := checkpoint_repeats
    rw [repeatSchedule_succ_eq_prepend,
      followsResidualSchedule_append] at repeated_prepend
    exact repeated_prepend.1
  have return_unit :
      IsUnit parameters.prime
        (residualMacroOrbit parameters waits checkpoint 1) := by
    simpa only [residualMacroOrbit_succ, residualMacroOrbit_zero] using
      residualRun_isUnit parameters waits checkpoint
        checkpoint_unit checkpoint_follows
  have final_left_unit :
      IsUnit parameters.prime
        (residualRun parameters (repeatSchedule waits prior)
          (residualMacroOrbit parameters waits checkpoint 1)) := by
    exact residualRun_isUnit parameters (repeatSchedule waits prior)
      (residualMacroOrbit parameters waits checkpoint 1)
      return_unit return_tail
  have final_right_unit :
      IsUnit parameters.prime
        (residualRun parameters (repeatSchedule waits prior) checkpoint) := by
    exact residualRun_isUnit parameters (repeatSchedule waits prior)
      checkpoint checkpoint_unit checkpoint_tail
  have nonnegative :
      0 ≤
        padicValRat parameters.prime
          (residualRun parameters (repeatSchedule waits prior)
              (residualMacroOrbit parameters waits checkpoint 1) -
            residualRun parameters (repeatSchedule waits prior) checkpoint) := by
    have lower :=
      min_le_sub (prime := parameters.prime) transported.1
    rw [final_left_unit.2, final_right_unit.2, min_self] at lower
    exact lower
  rw [transported.2] at nonnegative
  simp only [Nat.succ_sub_one]
  omega

/-- Prefix-power gap theorem. A legal repetition of one fixed macro is either already an exact
cycle at the first return, or its repetition count is bounded by the fixed rational height
envelope. -/
theorem repeatedMacro_exact_or_power_le
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    (waits : List Nat) {repetitions : Nat}
    (repetitions_positive : 0 < repetitions)
    (repeats :
      FollowsResidualSchedule parameters
        (repeatSchedule waits repetitions) 1) :
    residualMacroOrbit parameters waits 1 1 = 1 ∨
      parameters.prime ^
          ((repetitions - 1) * scheduleNatWeight parameters waits) ≤
        2 *
          guardHeightCoefficient centerNumerator driftNumerator scale ^
            waits.length := by
  by_cases exact_cycle : residualMacroOrbit parameters waits 1 1 = 1
  · exact Or.inl exact_cycle
  · right
    obtain ⟨prior, repetitions_eq⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt repetitions_positive)
    subst repetitions
    have first_follows :
        FollowsResidualSchedule parameters waits 1 := by
      have repeated_prepend := repeats
      rw [repeatSchedule_succ_eq_prepend,
        followsResidualSchedule_append] at repeated_prepend
      exact repeated_prepend.1
    have endpoint_unit :
        IsUnit parameters.prime
          (residualMacroOrbit parameters waits 1 1) := by
      simpa only [residualMacroOrbit_succ, residualMacroOrbit_zero] using
        residualRun_isUnit parameters waits 1
          ⟨one_ne_zero, padicValRat.one⟩ first_follows
    have difference_ne :
        residualMacroOrbit parameters waits 1 1 - 1 ≠ 0 :=
      sub_ne_zero.mpr exact_cycle
    have difference_nonnegative :
        0 ≤
          padicValRat parameters.prime
            (residualMacroOrbit parameters waits 1 1 - 1) := by
      have lower :=
        min_le_sub (prime := parameters.prime) difference_ne
      rw [endpoint_unit.2, padicValRat.one, min_self] at lower
      exact lower
    obtain ⟨returnDepth, returnDepth_eq⟩ :=
      Int.eq_ofNat_of_zero_le difference_nonnegative
    have return_depth :
        HasValue parameters.prime
          (residualMacroOrbit parameters waits 1 1 - 1)
          returnDepth :=
      ⟨difference_ne, returnDepth_eq⟩
    have repetition_depth :=
      repeatedMacro_returnDepth_le parameters waits 1
        (Nat.succ_pos prior) ⟨one_ne_zero, padicValRat.one⟩
        return_depth repeats
    have depth_power_le :
        parameters.prime ^
            (prior * scheduleNatWeight parameters waits) ≤
          parameters.prime ^ returnDepth :=
      Nat.pow_le_pow_right parameters.prime_prime.pos repetition_depth
    have rational_gap :=
      primePower_le_rationalPairHeight parameters
        endpoint_unit ⟨one_ne_zero, padicValRat.one⟩ exact_cycle return_depth
    have endpoint_height :=
      residualRun_rationalPairHeight_le parameters
        center_eq drift_eq scale_ne waits 1 first_follows
    have one_height :
        projectivePairHeight (rationalPair 1) = 1 := by
      norm_num [projectivePairHeight, rationalPair, integralPairHeight]
    rw [one_height, mul_one] at endpoint_height
    calc
      parameters.prime ^
          ((prior + 1 - 1) * scheduleNatWeight parameters waits) =
          parameters.prime ^
            (prior * scheduleNatWeight parameters waits) := by simp
      _ ≤ parameters.prime ^ returnDepth := depth_power_le
      _ ≤
          2 *
            projectivePairHeight
              (rationalPair
                (residualMacroOrbit parameters waits 1 1)) *
            projectivePairHeight (rationalPair 1) :=
        rational_gap
      _ ≤
          2 *
            (guardHeightCoefficient centerNumerator driftNumerator scale ^
              waits.length) := by
        have endpoint_eq :
            residualMacroOrbit parameters waits 1 1 =
              residualRun parameters waits 1 := rfl
        rw [endpoint_eq, one_height, mul_one]
        exact Nat.mul_le_mul_left 2 endpoint_height

/-- A numerical violation of the gap bound forces the first macro return to be an exact
cycle. -/
theorem repeatedMacro_exact_of_power_gt
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    (waits : List Nat) {repetitions : Nat}
    (repetitions_positive : 0 < repetitions)
    (repeats :
      FollowsResidualSchedule parameters
        (repeatSchedule waits repetitions) 1)
    (too_many :
      2 *
          guardHeightCoefficient centerNumerator driftNumerator scale ^
            waits.length <
        parameters.prime ^
          ((repetitions - 1) * scheduleNatWeight parameters waits)) :
    residualMacroOrbit parameters waits 1 1 = 1 := by
  rcases repeatedMacro_exact_or_power_le parameters
      center_eq drift_eq scale_ne waits repetitions_positive repeats with
    exact_cycle | bounded
  · exact exact_cycle
  · exact (not_lt_of_ge bounded too_many).elim

end
end MatrixMortality.ReturnGuard
