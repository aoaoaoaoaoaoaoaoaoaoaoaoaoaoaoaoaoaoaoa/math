import MatrixMortality.ReturnGuardShift

/-!
# Decoded residual dynamics for the amalgamated valuation guard

The reciprocal center displacement is the canonical global coordinate:

```text
z = center + drift / residual.
```

In this coordinate every positive wait is one fractional-linear branch.  Its inverse maps the
unit shell bijectively onto one exact `p`-adic sphere.  The spheres are disjoint, so the state
itself determines the wait; no external clock remains.
-/

namespace MatrixMortality.ReturnGuard

open MatrixMortality.PadicValuation

noncomputable section

/-- Residual at which the original guarded state is the terminal point one. -/
def terminalResidual (parameters : Parameters) : ℚ :=
  -drift parameters.center parameters.reset / (parameters.center - 1)

/-- Zero of the numerator of the fixed center transformation. -/
def residualRoot (parameters : Parameters) : ℚ :=
  -drift parameters.center parameters.reset / parameters.center

/-- Center of the exact residual sphere selecting `wait`. -/
def residualBranchCenter (parameters : Parameters) (wait : Nat) : ℚ :=
  -drift parameters.center parameters.reset /
    (parameters.center - parameters.prime ^ wait)

/-- Inverse of one transported residual branch. -/
def inverseResidual
    (parameters : Parameters) (wait : Nat) (target : ℚ) : ℚ :=
  drift parameters.center parameters.reset *
      (parameters.prime ^ (parameters.depth * wait) * target - 1) /
    (parameters.center - parameters.prime ^ wait -
      (parameters.center - 1) *
        parameters.prime ^ (parameters.depth * wait) * target)

/-- Original affine guarded state represented by a decoded residual. -/
def stateOfResidual (parameters : Parameters) (residual : ℚ) : ℚ :=
  parameters.center +
    drift parameters.center parameters.reset / residual

/-- Decoded residual represented by a noncentral guarded state. -/
def residualOfState (parameters : Parameters) (state : ℚ) : ℚ :=
  drift parameters.center parameters.reset / (state - parameters.center)

/-- Exact sphere on which the unique legal wait is `wait`. -/
def ResidualBranch
    (parameters : Parameters) (wait : Nat) (residual : ℚ) : Prop :=
  0 < wait ∧
    HasValue parameters.prime
      (residual - residualBranchCenter parameters wait)
      (parameters.depth * wait)

/-- One deterministic legal transition in decoded residual coordinates. -/
def DecodedStep (parameters : Parameters) (source target : ℚ) : Prop :=
  ∃ wait,
    ResidualBranch parameters wait source ∧
      residualStep parameters wait source = target

/-- Terminal reachability in decoded residual coordinates. -/
def DecodedReachable (parameters : Parameters) : Prop :=
  Relation.TransGen (DecodedStep parameters) 1 (terminalResidual parameters)

/-- Iterated inverse branches, written in forward address order. -/
def inverseAddress
    (parameters : Parameters) : List Nat → ℚ → ℚ
  | [], target => target
  | wait :: waits, target =>
      inverseResidual parameters wait (inverseAddress parameters waits target)

/-- Every wait in an inverse address is positive. -/
def PositiveAddress (waits : List Nat) : Prop :=
  ∀ wait ∈ waits, 0 < wait

/-- Cross-multiplied finite fixed-point equation for one residual branch. -/
def ResidualFixed
    (parameters : Parameters) (wait : Nat) (residual : ℚ) : Prop :=
  parameters.prime ^ (parameters.depth * wait) * residual *
      ((parameters.center - 1) * residual +
        drift parameters.center parameters.reset) =
    (parameters.center - parameters.prime ^ wait) * residual +
      drift parameters.center parameters.reset

theorem terminalResidual_isUnit (parameters : Parameters) :
    IsUnit parameters.prime (terminalResidual parameters) := by
  simpa [terminalResidual] using
    div_hasValue (neg_hasValue parameters.drift_unit)
      parameters.center_sub_one_unit

theorem residualRoot_isUnit (parameters : Parameters) :
    IsUnit parameters.prime (residualRoot parameters) := by
  simpa [residualRoot] using
    div_hasValue (neg_hasValue parameters.drift_unit) parameters.center_unit

/-- The branch denominator `center - p^wait` is a unit for every positive wait. -/
theorem center_sub_primePower_isUnit
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait) :
    IsUnit parameters.prime
      (parameters.center - parameters.prime ^ wait) :=
  unit_sub_positive parameters.center_unit
    (primePower_positive parameters wait wait_positive)

theorem residualBranchCenter_isUnit
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait) :
    IsUnit parameters.prime (residualBranchCenter parameters wait) := by
  simpa [residualBranchCenter] using
    div_hasValue (neg_hasValue parameters.drift_unit)
      (center_sub_primePower_isUnit parameters wait wait_positive)

/-- The center of branch `wait` lies at exact distance `p^wait` from the common root. -/
theorem residualBranchCenter_sub_root_hasValue
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait) :
    HasValue parameters.prime
      (residualBranchCenter parameters wait - residualRoot parameters) wait := by
  have branch_unit :=
    center_sub_primePower_isUnit parameters wait wait_positive
  have numerator_value :
      HasValue parameters.prime
        (-drift parameters.center parameters.reset *
          parameters.prime ^ wait) wait := by
    simpa using
      neg_hasValue
        (mul_hasValue parameters.drift_unit (primePower_hasValue wait))
  have denominator_unit :
      IsUnit parameters.prime
        (parameters.center *
          (parameters.center - parameters.prime ^ wait)) :=
    mul_hasValue parameters.center_unit branch_unit
  have quotient_value :=
    div_hasValue numerator_value denominator_unit
  convert quotient_value using 1
  simp [residualBranchCenter, residualRoot]
  field_simp [parameters.center_unit.1, branch_unit.1]
  ring

/-- Denominator of the inverse branch. -/
def inverseResidualDenominator
    (parameters : Parameters) (wait : Nat) (target : ℚ) : ℚ :=
  parameters.center - parameters.prime ^ wait -
    (parameters.center - 1) *
      parameters.prime ^ (parameters.depth * wait) * target

theorem inverseResidualDenominator_isUnit
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait)
    (target : ℚ) (target_unit : IsUnit parameters.prime target) :
    IsUnit parameters.prime
      (inverseResidualDenominator parameters wait target) := by
  have branch_unit :=
    center_sub_primePower_isUnit parameters wait wait_positive
  have scaled_value :
      HasValue parameters.prime
        ((parameters.center - 1) *
          parameters.prime ^ (parameters.depth * wait) * target)
        (parameters.depth * wait) := by
    simpa [add_assoc] using
      mul_hasValue
        (mul_hasValue parameters.center_sub_one_unit
          (primePower_hasValue (parameters.depth * wait)))
        target_unit
  have scaled_positive :
      IsPositive parameters.prime
        ((parameters.center - 1) *
          parameters.prime ^ (parameters.depth * wait) * target) := by
    refine ⟨scaled_value.1, ?_⟩
    rw [scaled_value.2]
    exact_mod_cast Nat.mul_pos parameters.depth_positive wait_positive
  simpa [inverseResidualDenominator] using
    unit_sub_positive branch_unit scaled_positive

/-- Exact displacement of an inverse image from its branch center. -/
theorem inverseResidual_sub_branchCenter
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait)
    (target : ℚ) (target_unit : IsUnit parameters.prime target) :
    inverseResidual parameters wait target -
        residualBranchCenter parameters wait =
      parameters.prime ^ (parameters.depth * wait) *
        drift parameters.center parameters.reset * target *
        (1 - parameters.prime ^ wait) /
      ((parameters.center - parameters.prime ^ wait) *
        inverseResidualDenominator parameters wait target) := by
  have branch_unit :=
    center_sub_primePower_isUnit parameters wait wait_positive
  have inverse_denominator_unit :=
    inverseResidualDenominator_isUnit parameters wait wait_positive
      target target_unit
  change
    drift parameters.center parameters.reset *
          (parameters.prime ^ (parameters.depth * wait) * target - 1) /
          inverseResidualDenominator parameters wait target -
        (-drift parameters.center parameters.reset /
          (parameters.center - parameters.prime ^ wait)) =
      _
  field_simp [branch_unit.1, inverse_denominator_unit.1]
  simp [inverseResidualDenominator]
  ring

/-- Every inverse image lies on its branch's exact sphere. -/
theorem inverseResidual_mem_branch
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait)
    (target : ℚ) (target_unit : IsUnit parameters.prime target) :
    ResidualBranch parameters wait
      (inverseResidual parameters wait target) := by
  refine ⟨wait_positive, ?_⟩
  rw [inverseResidual_sub_branchCenter parameters wait wait_positive target target_unit]
  have power_sub_one_unit :
      IsUnit parameters.prime (1 - parameters.prime ^ wait) :=
    one_sub_positive (primePower_positive parameters wait wait_positive)
  have numerator_value :
      HasValue parameters.prime
        (parameters.prime ^ (parameters.depth * wait) *
          drift parameters.center parameters.reset * target *
          (1 - parameters.prime ^ wait))
        (parameters.depth * wait) := by
    simpa [add_assoc] using
      mul_hasValue
        (mul_hasValue
          (mul_hasValue (primePower_hasValue (parameters.depth * wait))
            parameters.drift_unit)
          target_unit)
        power_sub_one_unit
  have denominator_unit :
      IsUnit parameters.prime
        ((parameters.center - parameters.prime ^ wait) *
          inverseResidualDenominator parameters wait target) :=
    mul_hasValue
      (center_sub_primePower_isUnit parameters wait wait_positive)
      (inverseResidualDenominator_isUnit parameters wait wait_positive
        target target_unit)
  simpa using div_hasValue numerator_value denominator_unit

/-- Membership in an exact branch sphere already forces the residual to be a unit. -/
theorem residualBranch_isUnit
    (parameters : Parameters) (wait : Nat) (residual : ℚ)
    (branch : ResidualBranch parameters wait residual) :
    IsUnit parameters.prime residual := by
  have center_unit :=
    residualBranchCenter_isUnit parameters wait branch.1
  have displacement_positive : IsPositive parameters.prime
      (residual - residualBranchCenter parameters wait) := by
    refine ⟨branch.2.1, ?_⟩
    rw [branch.2.2]
    exact_mod_cast Nat.mul_pos parameters.depth_positive branch.1
  rw [show residual =
    residualBranchCenter parameters wait +
      (residual - residualBranchCenter parameters wait) by ring]
  exact unit_add_positive center_unit displacement_positive

/-- A branch sphere has the wait as its exact distance from the common residual root. -/
theorem residualBranch_sub_root_hasValue
    (parameters : Parameters) (wait : Nat) (residual : ℚ)
    (branch : ResidualBranch parameters wait residual) :
    HasValue parameters.prime (residual - residualRoot parameters) wait := by
  have center_value :=
    residualBranchCenter_sub_root_hasValue parameters wait branch.1
  have displacement_value := branch.2
  have wait_lt_depth : (wait : ℤ) < parameters.depth * wait := by
    exact_mod_cast (show wait < parameters.depth * wait by
      nlinarith [parameters.depth_two, branch.1])
  rw [show residual - residualRoot parameters =
    (residualBranchCenter parameters wait - residualRoot parameters) +
      (residual - residualBranchCenter parameters wait) by ring]
  exact add_hasValue_left center_value displacement_value wait_lt_depth

/-- Distinct waits have disjoint branch spheres. -/
theorem residualBranch_wait_unique
    (parameters : Parameters) {left right : Nat} {residual : ℚ}
    (left_branch : ResidualBranch parameters left residual)
    (right_branch : ResidualBranch parameters right residual) :
    left = right := by
  have left_value :=
    residualBranch_sub_root_hasValue parameters left residual left_branch
  have right_value :=
    residualBranch_sub_root_hasValue parameters right residual right_branch
  exact_mod_cast left_value.2.symm.trans right_value.2

theorem inverseResidual_isUnit
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait)
    (target : ℚ) (target_unit : IsUnit parameters.prime target) :
    IsUnit parameters.prime (inverseResidual parameters wait target) :=
  residualBranch_isUnit parameters wait _
    (inverseResidual_mem_branch parameters wait wait_positive target target_unit)

/-- The fixed-transform denominator of an inverse image is an explicit unit quotient. -/
theorem centerTransform_denominator_inverseResidual
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait)
    (target : ℚ) (target_unit : IsUnit parameters.prime target) :
    (parameters.center - 1) * inverseResidual parameters wait target +
        drift parameters.center parameters.reset =
      drift parameters.center parameters.reset *
          (1 - parameters.prime ^ wait) /
        inverseResidualDenominator parameters wait target := by
  have inverse_denominator_unit :=
    inverseResidualDenominator_isUnit parameters wait wait_positive
      target target_unit
  change
    (parameters.center - 1) *
          (drift parameters.center parameters.reset *
              (parameters.prime ^ (parameters.depth * wait) * target - 1) /
            inverseResidualDenominator parameters wait target) +
        drift parameters.center parameters.reset =
      _
  field_simp [inverse_denominator_unit.1]
  simp [inverseResidualDenominator]
  ring

theorem centerTransform_denominator_inverseResidual_isUnit
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait)
    (target : ℚ) (target_unit : IsUnit parameters.prime target) :
    IsUnit parameters.prime
      ((parameters.center - 1) * inverseResidual parameters wait target +
        drift parameters.center parameters.reset) := by
  rw [centerTransform_denominator_inverseResidual parameters wait wait_positive
    target target_unit]
  have power_sub_one_unit :
      IsUnit parameters.prime (1 - parameters.prime ^ wait) :=
    one_sub_positive (primePower_positive parameters wait wait_positive)
  exact div_hasValue
    (mul_hasValue parameters.drift_unit power_sub_one_unit)
    (inverseResidualDenominator_isUnit parameters wait wait_positive
      target target_unit)

/-- The variable numerator of an inverse image carries exactly the target and branch scale. -/
theorem centerTransform_numerator_inverseResidual
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait)
    (target : ℚ) (target_unit : IsUnit parameters.prime target) :
    (parameters.center - parameters.prime ^ wait) *
        inverseResidual parameters wait target +
        drift parameters.center parameters.reset =
      parameters.prime ^ (parameters.depth * wait) *
        drift parameters.center parameters.reset * target *
          (1 - parameters.prime ^ wait) /
        inverseResidualDenominator parameters wait target := by
  have inverse_denominator_unit :=
    inverseResidualDenominator_isUnit parameters wait wait_positive
      target target_unit
  change
    (parameters.center - parameters.prime ^ wait) *
          (drift parameters.center parameters.reset *
              (parameters.prime ^ (parameters.depth * wait) * target - 1) /
            inverseResidualDenominator parameters wait target) +
        drift parameters.center parameters.reset =
      _
  field_simp [inverse_denominator_unit.1]
  simp [inverseResidualDenominator]
  ring

/-- Each inverse branch is a genuine right inverse of the transported residual map. -/
theorem residualStep_inverseResidual
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait)
    (target : ℚ) (target_unit : IsUnit parameters.prime target) :
    residualStep parameters wait
      (inverseResidual parameters wait target) = target := by
  have transform_denominator_unit :=
    centerTransform_denominator_inverseResidual_isUnit
      parameters wait wait_positive target target_unit
  rw [residualStep_eq parameters wait _ transform_denominator_unit.1]
  rw [centerTransform_numerator_inverseResidual parameters wait wait_positive
    target target_unit]
  rw [centerTransform_denominator_inverseResidual parameters wait wait_positive
    target target_unit]
  have inverse_denominator_unit :=
    inverseResidualDenominator_isUnit parameters wait wait_positive
      target target_unit
  have power_ne :
      (parameters.prime : ℚ) ^ (parameters.depth * wait) ≠ 0 :=
    primePower_ne_zero parameters.prime_prime _
  have power_sub_one_ne :
      (1 : ℚ) - parameters.prime ^ wait ≠ 0 :=
    (one_sub_positive
      (primePower_positive parameters wait wait_positive)).1
  field_simp [inverse_denominator_unit.1, transform_denominator_unit.1,
    power_ne, parameters.drift_ne_zero, power_sub_one_ne]
  ring

/-- The residual-map numerator is the branch displacement times its unit coefficient. -/
theorem centerTransform_numerator_eq_branchDisplacement
    (parameters : Parameters) (wait : Nat) (residual : ℚ) :
    (parameters.center - parameters.prime ^ wait) * residual +
        drift parameters.center parameters.reset =
      (parameters.center - parameters.prime ^ wait) *
        (residual - residualBranchCenter parameters wait) := by
  by_cases wait_zero : wait = 0
  · subst wait
    simp [residualBranchCenter]
    field_simp [parameters.center_sub_one_unit.1]
    ring
  · have wait_positive : 0 < wait := Nat.pos_of_ne_zero wait_zero
    have branch_unit :=
      center_sub_primePower_isUnit parameters wait wait_positive
    simp [residualBranchCenter]
    field_simp [branch_unit.1]
    ring

/-- On a branch sphere the fixed-transform denominator remains a unit. -/
theorem centerTransform_denominator_isUnit_of_branch
    (parameters : Parameters) (wait : Nat) (residual : ℚ)
    (branch : ResidualBranch parameters wait residual) :
    IsUnit parameters.prime
      ((parameters.center - 1) * residual +
        drift parameters.center parameters.reset) := by
  have branch_coefficient_unit :=
    center_sub_primePower_isUnit parameters wait branch.1
  have power_sub_one_unit :
      IsUnit parameters.prime (1 - parameters.prime ^ wait) :=
    one_sub_positive (primePower_positive parameters wait branch.1)
  have center_value :
      IsUnit parameters.prime
        (drift parameters.center parameters.reset *
            (1 - parameters.prime ^ wait) /
          (parameters.center - parameters.prime ^ wait)) :=
    div_hasValue
      (mul_hasValue parameters.drift_unit power_sub_one_unit)
      branch_coefficient_unit
  have perturbation_value :
      HasValue parameters.prime
        ((parameters.center - 1) *
          (residual - residualBranchCenter parameters wait))
        (parameters.depth * wait) := by
    simpa using
      mul_hasValue parameters.center_sub_one_unit branch.2
  have perturbation_positive :
      IsPositive parameters.prime
        ((parameters.center - 1) *
          (residual - residualBranchCenter parameters wait)) := by
    refine ⟨perturbation_value.1, ?_⟩
    rw [perturbation_value.2]
    exact_mod_cast Nat.mul_pos parameters.depth_positive branch.1
  rw [show
      (parameters.center - 1) * residual +
          drift parameters.center parameters.reset =
        drift parameters.center parameters.reset *
            (1 - parameters.prime ^ wait) /
            (parameters.center - parameters.prime ^ wait) +
          (parameters.center - 1) *
            (residual - residualBranchCenter parameters wait) by
    have coefficient_ne := branch_coefficient_unit.1
    simp [residualBranchCenter]
    field_simp [coefficient_ne]
    ring]
  exact unit_add_positive center_value perturbation_positive

/-- The transported image of every point on a branch sphere is a unit. -/
theorem residualStep_isUnit_of_branch
    (parameters : Parameters) (wait : Nat) (residual : ℚ)
    (branch : ResidualBranch parameters wait residual) :
    IsUnit parameters.prime (residualStep parameters wait residual) := by
  have transform_denominator_unit :=
    centerTransform_denominator_isUnit_of_branch
      parameters wait residual branch
  rw [residualStep_eq parameters wait residual transform_denominator_unit.1]
  rw [centerTransform_numerator_eq_branchDisplacement]
  have numerator_value :
      HasValue parameters.prime
        ((parameters.center - parameters.prime ^ wait) *
          (residual - residualBranchCenter parameters wait))
        (parameters.depth * wait) :=
    by
      simpa using
        mul_hasValue
          (center_sub_primePower_isUnit parameters wait branch.1) branch.2
  have denominator_value :
      HasValue parameters.prime
        (parameters.prime ^ (parameters.depth * wait) *
          ((parameters.center - 1) * residual +
            drift parameters.center parameters.reset))
        (parameters.depth * wait) :=
    mul_hasValue (primePower_hasValue (parameters.depth * wait))
      transform_denominator_unit
  simpa using div_hasValue numerator_value denominator_value

/-- Restricting to an exact branch sphere makes the displayed inverse a left inverse too. -/
theorem inverseResidual_residualStep
    (parameters : Parameters) (wait : Nat) (residual : ℚ)
    (branch : ResidualBranch parameters wait residual) :
    inverseResidual parameters wait (residualStep parameters wait residual) =
      residual := by
  have transform_denominator_unit :=
    centerTransform_denominator_isUnit_of_branch
      parameters wait residual branch
  rw [residualStep_eq parameters wait residual transform_denominator_unit.1]
  have power_ne :
      (parameters.prime : ℚ) ^ (parameters.depth * wait) ≠ 0 :=
    primePower_ne_zero parameters.prime_prime _
  have power_sub_one_ne :
      (1 : ℚ) - parameters.prime ^ wait ≠ 0 :=
    (one_sub_positive
      (primePower_positive parameters wait branch.1)).1
  have collapsed_ne :
      drift parameters.center parameters.reset *
          parameters.prime ^ (parameters.depth * wait) -
        drift parameters.center parameters.reset *
            parameters.prime ^ (parameters.depth * wait) *
          parameters.prime ^ wait ≠ 0 := by
    rw [show
      drift parameters.center parameters.reset *
            parameters.prime ^ (parameters.depth * wait) -
          drift parameters.center parameters.reset *
              parameters.prime ^ (parameters.depth * wait) *
            parameters.prime ^ wait =
        drift parameters.center parameters.reset *
          parameters.prime ^ (parameters.depth * wait) *
          (1 - parameters.prime ^ wait) by ring]
    exact mul_ne_zero
      (mul_ne_zero parameters.drift_ne_zero power_ne) power_sub_one_ne
  simp [inverseResidual, inverseResidualDenominator]
  field_simp [transform_denominator_unit.1, power_ne,
    parameters.drift_ne_zero, power_sub_one_ne]
  rw [show
      drift parameters.center parameters.reset *
          (parameters.prime ^ (parameters.depth * wait) *
              ((parameters.center - parameters.prime ^ wait) * residual +
                drift parameters.center parameters.reset) -
            parameters.prime ^ (parameters.depth * wait) *
              ((parameters.center - 1) * residual +
                drift parameters.center parameters.reset)) =
        (drift parameters.center parameters.reset *
              parameters.prime ^ (parameters.depth * wait) -
            drift parameters.center parameters.reset *
                parameters.prime ^ (parameters.depth * wait) *
              parameters.prime ^ wait) * residual by ring]
  rw [show
      (parameters.center - parameters.prime ^ wait) *
            (parameters.prime ^ (parameters.depth * wait) *
              ((parameters.center - 1) * residual +
                drift parameters.center parameters.reset)) -
          (parameters.center - 1) *
              parameters.prime ^ (parameters.depth * wait) *
            ((parameters.center - parameters.prime ^ wait) * residual +
              drift parameters.center parameters.reset) =
        drift parameters.center parameters.reset *
            parameters.prime ^ (parameters.depth * wait) -
          drift parameters.center parameters.reset *
              parameters.prime ^ (parameters.depth * wait) *
            parameters.prime ^ wait by ring]
  exact mul_div_cancel_left₀ residual collapsed_ne

/-- Exact branch spheres are precisely the images of the unit shell under one inverse branch. -/
theorem residualBranch_iff_exists_inverseResidual
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait)
    (residual : ℚ) :
    ResidualBranch parameters wait residual ↔
      ∃ target, IsUnit parameters.prime target ∧
        residual = inverseResidual parameters wait target := by
  constructor
  · intro branch
    let target := residualStep parameters wait residual
    have target_unit :=
      residualStep_isUnit_of_branch parameters wait residual branch
    exact ⟨target, target_unit,
      (inverseResidual_residualStep parameters wait residual branch).symm⟩
  · rintro ⟨target, target_unit, rfl⟩
    exact inverseResidual_mem_branch parameters wait wait_positive
      target target_unit

/-- The original reset is residual one. -/
theorem stateOfResidual_one (parameters : Parameters) :
    stateOfResidual parameters 1 = parameters.reset := by
  simp [stateOfResidual, drift]

/-- The terminal residual represents the original target one. -/
theorem stateOfResidual_terminalResidual (parameters : Parameters) :
    stateOfResidual parameters (terminalResidual parameters) = 1 := by
  have drift_ne := parameters.drift_ne_zero
  simp [stateOfResidual, terminalResidual]
  field_simp [drift_ne]
  ring

theorem residualOfState_reset (parameters : Parameters) :
    residualOfState parameters parameters.reset = 1 := by
  change
    drift parameters.center parameters.reset /
      drift parameters.center parameters.reset = 1
  exact div_self parameters.drift_ne_zero

theorem residualOfState_one (parameters : Parameters) :
    residualOfState parameters 1 = terminalResidual parameters := by
  change
    drift parameters.center parameters.reset / (1 - parameters.center) =
      -drift parameters.center parameters.reset / (parameters.center - 1)
  rw [show (1 : ℚ) - parameters.center =
    -(parameters.center - 1) by ring]
  rw [div_neg]
  exact (neg_div _ _).symm

/-- The two decoded coordinate maps are total inverses under rational zero-division. -/
theorem residualOfState_stateOfResidual
    (parameters : Parameters) (residual : ℚ) :
    residualOfState parameters (stateOfResidual parameters residual) = residual := by
  have drift_ne := parameters.drift_ne_zero
  simp [residualOfState, stateOfResidual]
  field_simp [drift_ne]

theorem stateOfResidual_residualOfState
    (parameters : Parameters) (state : ℚ) :
    stateOfResidual parameters (residualOfState parameters state) = state := by
  have drift_ne := parameters.drift_ne_zero
  simp [residualOfState, stateOfResidual]
  field_simp [drift_ne]

/-- Canonical equivalence between guarded states and decoded residuals. -/
def residualEquiv (parameters : Parameters) : ℚ ≃ ℚ where
  toFun := stateOfResidual parameters
  invFun := residualOfState parameters
  left_inv := residualOfState_stateOfResidual parameters
  right_inv := stateOfResidual_residualOfState parameters

theorem stateOfResidual_injective
    (parameters : Parameters) :
    Function.Injective (stateOfResidual parameters) :=
  (residualEquiv parameters).injective

theorem stateOfResidual_ne_center
    (parameters : Parameters) (residual : ℚ) (residual_ne : residual ≠ 0) :
    stateOfResidual parameters residual ≠ parameters.center := by
  intro equal
  have quotient_zero :
      drift parameters.center parameters.reset / residual = 0 := by
    rw [stateOfResidual] at equal
    linarith
  exact
    (div_ne_zero parameters.drift_ne_zero residual_ne) quotient_zero

/-- Original state factored through the common residual root. -/
theorem stateOfResidual_eq_rootQuotient
    (parameters : Parameters) (residual : ℚ) (residual_ne : residual ≠ 0) :
    stateOfResidual parameters residual =
      parameters.center * (residual - residualRoot parameters) / residual := by
  have center_ne := parameters.center_unit.1
  simp [stateOfResidual, residualRoot]
  field_simp [residual_ne, center_ne]
  ring

/-- The readiness defect is the branch displacement in decoded coordinates. -/
theorem stateOfResidual_sub_primePower
    (parameters : Parameters) (wait : Nat) (residual : ℚ)
    (residual_ne : residual ≠ 0) :
    stateOfResidual parameters residual - parameters.prime ^ wait =
      (parameters.center - parameters.prime ^ wait) *
        (residual - residualBranchCenter parameters wait) / residual := by
  by_cases wait_zero : wait = 0
  · subst wait
    have center_defect_ne := parameters.center_sub_one_unit.1
    simp [stateOfResidual, residualBranchCenter]
    field_simp [residual_ne, center_defect_ne]
    ring
  · have wait_positive : 0 < wait := Nat.pos_of_ne_zero wait_zero
    have coefficient_ne :=
      (center_sub_primePower_isUnit parameters wait wait_positive).1
    simp [stateOfResidual, residualBranchCenter]
    field_simp [residual_ne, coefficient_ne]
    ring

/-- An exact residual sphere is exactly an original ready cylinder. -/
theorem residualBranch_ready
    (parameters : Parameters) (wait : Nat) (residual : ℚ)
    (branch : ResidualBranch parameters wait residual) :
    Ready parameters wait (stateOfResidual parameters residual) := by
  have residual_unit :=
    residualBranch_isUnit parameters wait residual branch
  have root_value :=
    residualBranch_sub_root_hasValue parameters wait residual branch
  have state_value :
      HasValue parameters.prime (stateOfResidual parameters residual) wait := by
    rw [stateOfResidual_eq_rootQuotient parameters residual residual_unit.1]
    simpa using
      div_hasValue
        (mul_hasValue parameters.center_unit root_value) residual_unit
  have defect_value :
      HasValue parameters.prime
        (stateOfResidual parameters residual - parameters.prime ^ wait)
        (parameters.depth * wait) := by
    rw [stateOfResidual_sub_primePower parameters wait residual residual_unit.1]
    exact div_hasValue
      (by
        simpa using
          mul_hasValue
            (center_sub_primePower_isUnit parameters wait branch.1) branch.2)
      residual_unit
  exact ⟨branch.1, state_value.2, defect_value.2⟩

/-- Every original ready cylinder is one exact sphere in decoded residual coordinates. -/
theorem ready_residualBranch
    (parameters : Parameters) (wait : Nat) (residual : ℚ)
    (ready : Ready parameters wait (stateOfResidual parameters residual)) :
    ResidualBranch parameters wait residual := by
  have state_positive :=
    ready_isPositive parameters wait (stateOfResidual parameters residual) ready
  have residual_ne : residual ≠ 0 := by
    intro residual_zero
    have state_eq :
        stateOfResidual parameters residual = parameters.center := by
      simp [stateOfResidual, residual_zero]
    have impossible := ready.2.1
    rw [state_eq, parameters.center_unit.2] at impossible
    have wait_zero : wait = 0 := by exact_mod_cast impossible.symm
    exact ready.1.ne' wait_zero
  have state_sub_center_unit :
      IsUnit parameters.prime
        (stateOfResidual parameters residual - parameters.center) := by
    have center_sub_state :=
      unit_sub_positive parameters.center_unit state_positive
    rw [show
      stateOfResidual parameters residual - parameters.center =
        -(parameters.center - stateOfResidual parameters residual) by ring]
    exact neg_hasValue center_sub_state
  have residual_eq :
      residual =
        drift parameters.center parameters.reset /
          (stateOfResidual parameters residual - parameters.center) := by
    simpa [residualOfState] using
      (residualOfState_stateOfResidual parameters residual).symm
  have residual_unit : IsUnit parameters.prime residual := by
    rw [residual_eq]
    exact div_hasValue parameters.drift_unit state_sub_center_unit
  refine ⟨ready.1, ?_⟩
  rw [show
      residual - residualBranchCenter parameters wait =
        residual *
            (stateOfResidual parameters residual - parameters.prime ^ wait) /
          (parameters.center - parameters.prime ^ wait) by
    rw [stateOfResidual_sub_primePower parameters wait residual residual_ne]
    have coefficient_ne :=
      (center_sub_primePower_isUnit parameters wait ready.1).1
    field_simp [residual_ne, coefficient_ne]]
  simpa using
    div_hasValue
      (mul_hasValue residual_unit
        ⟨by
          intro defect_zero
          have impossible := ready.2.2
          rw [defect_zero, padicValRat.zero] at impossible
          have scaled_positive :
              0 < parameters.depth * wait :=
            Nat.mul_pos parameters.depth_positive ready.1
          omega,
         ready.2.2⟩)
      (center_sub_primePower_isUnit parameters wait ready.1)

theorem residualBranch_iff_ready
    (parameters : Parameters) (wait : Nat) (residual : ℚ) :
    ResidualBranch parameters wait residual ↔
      Ready parameters wait (stateOfResidual parameters residual) :=
  ⟨residualBranch_ready parameters wait residual,
    ready_residualBranch parameters wait residual⟩

/-- The decoded residual update is conjugate to the original guarded step. -/
theorem guardedStep_stateOfResidual
    (parameters : Parameters) (wait : Nat) (residual : ℚ)
    (branch : ResidualBranch parameters wait residual) :
    guardedStep parameters wait (some (stateOfResidual parameters residual)) =
      some
        (stateOfResidual parameters
          (residualStep parameters wait residual)) := by
  have ready :=
    residualBranch_ready parameters wait residual branch
  have residual_unit :=
    residualBranch_isUnit parameters wait residual branch
  have transform_denominator_unit :=
    centerTransform_denominator_isUnit_of_branch
      parameters wait residual branch
  have source_not_pole :
      stateOfResidual parameters residual ≠ parameters.prime ^ wait := by
    intro equal
    have impossible := ready.2.2
    rw [equal, sub_self, padicValRat.zero] at impossible
    have scaled_positive :
        0 < parameters.depth * wait :=
      Nat.mul_pos parameters.depth_positive branch.1
    omega
  rw [guardedStep_some parameters wait _ source_not_pole]
  congr 1
  rw [residualStep_eq parameters wait residual transform_denominator_unit.1]
  simp [stateOfResidual, guardDefect]
  field_simp [residual_unit.1, transform_denominator_unit.1,
    parameters.drift_ne_zero]
  ring

/-- Decoded steps transport to legal guarded steps under the canonical state coordinate. -/
theorem decodedStep_legalStep
    (parameters : Parameters) {source target : ℚ}
    (step : DecodedStep parameters source target) :
    LegalStep parameters
      (stateOfResidual parameters source)
      (stateOfResidual parameters target) := by
  obtain ⟨wait, branch, image_eq⟩ := step
  have wait_eq : wait - 1 + 1 = wait := by
    have wait_positive := branch.1
    omega
  refine ⟨wait - 1, ?_, ?_⟩
  · simpa [wait_eq] using
      residualBranch_ready parameters wait source branch
  · simpa [wait_eq, image_eq] using
      guardedStep_stateOfResidual parameters wait source branch

/-- A decoded transition cannot land at the residual pole zero. -/
theorem decodedStep_target_isUnit
    (parameters : Parameters) {source target : ℚ}
    (step : DecodedStep parameters source target) :
    IsUnit parameters.prime target := by
  obtain ⟨wait, branch, image_eq⟩ := step
  rw [← image_eq]
  exact residualStep_isUnit_of_branch parameters wait source branch

/-- Legal guarded steps between decoded states are exactly decoded residual steps. -/
theorem legalStep_stateOfResidual_iff
    (parameters : Parameters) {source target : ℚ} :
    LegalStep parameters
        (stateOfResidual parameters source)
        (stateOfResidual parameters target) ↔
      DecodedStep parameters source target := by
  constructor
  · rintro ⟨index, ready, action_eq⟩
    let wait := index + 1
    have branch :
        ResidualBranch parameters wait source := by
      exact ready_residualBranch parameters wait source ready
    have canonical_action :=
      guardedStep_stateOfResidual parameters wait source branch
    rw [action_eq] at canonical_action
    have image_eq :
        residualStep parameters wait source = target :=
      stateOfResidual_injective parameters
        (Option.some.inj canonical_action).symm
    exact ⟨wait, branch, image_eq⟩
  · exact decodedStep_legalStep parameters

theorem legalStep_source_ne_center
    (parameters : Parameters) {source target : ℚ}
    (step : LegalStep parameters source target) :
    source ≠ parameters.center := by
  have source_positive := legalStep_source_live parameters step
  intro source_eq
  have impossible := source_positive.2
  rw [source_eq, parameters.center_unit.2] at impossible
  exact (lt_irrefl 0 impossible).elim

theorem legalStep_target_ne_center
    (parameters : Parameters) {source target : ℚ}
    (step : LegalStep parameters source target) :
    target ≠ parameters.center := by
  obtain ⟨index, ready, action_eq⟩ := step
  let wait := index + 1
  let residual := residualOfState parameters source
  have source_eq :
      stateOfResidual parameters residual = source :=
    stateOfResidual_residualOfState parameters source
  have branch :
      ResidualBranch parameters wait residual := by
    apply ready_residualBranch parameters wait residual
    simpa [source_eq] using ready
  have canonical_action :=
    guardedStep_stateOfResidual parameters wait residual branch
  rw [source_eq, action_eq] at canonical_action
  have image_unit :=
    residualStep_isUnit_of_branch parameters wait residual branch
  have target_eq :
      target =
        stateOfResidual parameters (residualStep parameters wait residual) :=
    Option.some.inj canonical_action
  rw [target_eq]
  exact stateOfResidual_ne_center parameters _ image_unit.1

/-- Every original legal step pulls back to one decoded residual step. -/
theorem legalStep_decodedStep
    (parameters : Parameters) {source target : ℚ}
    (step : LegalStep parameters source target) :
    DecodedStep parameters
      (residualOfState parameters source)
      (residualOfState parameters target) := by
  apply (legalStep_stateOfResidual_iff parameters).mp
  simpa only [
    stateOfResidual_residualOfState parameters source,
    stateOfResidual_residualOfState parameters target]
    using step

theorem decodedTransGen_legalTransGen
    (parameters : Parameters) {source target : ℚ}
    (path : Relation.TransGen (DecodedStep parameters) source target) :
    Relation.TransGen (LegalStep parameters)
      (stateOfResidual parameters source)
      (stateOfResidual parameters target) := by
  induction path with
  | single step =>
      exact Relation.TransGen.single (decodedStep_legalStep parameters step)
  | tail _ step induction =>
      exact induction.tail (decodedStep_legalStep parameters step)

theorem legalTransGen_decodedTransGen
    (parameters : Parameters) {source target : ℚ}
    (path : Relation.TransGen (LegalStep parameters) source target) :
    Relation.TransGen (DecodedStep parameters)
      (residualOfState parameters source)
      (residualOfState parameters target) := by
  induction path with
  | single step =>
      exact Relation.TransGen.single (legalStep_decodedStep parameters step)
  | tail _ step induction =>
      exact induction.tail (legalStep_decodedStep parameters step)

/-- The canonical residual coordinate preserves the complete deterministic reachability
problem, including reset and terminal boundaries. -/
theorem guardedReachable_iff_decodedReachable (parameters : Parameters) :
    GuardedReachable parameters ↔ DecodedReachable parameters := by
  constructor
  · intro reachable
    have decoded :=
      legalTransGen_decodedTransGen parameters reachable
    simpa only [residualOfState_reset, residualOfState_one] using decoded
  · intro reachable
    have guarded :=
      decodedTransGen_legalTransGen parameters reachable
    simpa only [stateOfResidual_one, stateOfResidual_terminalResidual] using guarded

/-- Physical mortality is finite target reachability in the decoded residual system. -/
theorem physical_isMortal_iff_decodedReachable (parameters : Parameters) :
    IsMortal
        (ReturnFamily.pairGenerator
          (ambient (parameters.prime : ℚ) parameters.depth)
          (cut parameters.center parameters.reset)) ↔
      DecodedReachable parameters := by
  rw [physical_isMortal_iff_guardedReachable,
    guardedReachable_iff_decodedReachable]

end
end MatrixMortality.ReturnGuard
