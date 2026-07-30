import MatrixMortality.ReturnGuardParameterLift
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Parameter sensitivity of legal guard dynamics

The fixed-reset parameter lift has a total, orbitwise derivative.  At a ready state, changing
the center changes both the affine return itself and the unit tail extracted from the moving
state.  Their exact chain rule is a one-dimensional sensitivity recurrence.

Its singular term dominates p-adically: if the current sensitivity has negative valuation,
one legal step lowers that valuation by exactly `depth * wait`.  This supplies the differential
part of any parameter-lifting argument.  Exact readiness is annular, however, so sensitivity
alone does not guarantee that an incidence lift preserves the preceding prefix; that separate
compatibility law is isolated in `ReturnGuardAntiHensel`.
-/

namespace MatrixMortality.ReturnGuard

open MatrixMortality.PadicValuation

noncomputable section

/-- Legal affine update with the reset fixed and the center left as an explicit parameter. -/
def fixedResetLegalValue
    (prime depth wait : Nat) (reset center tail : ℚ) : ℚ :=
  center + (reset - center) *
    ((prime : ℚ) ^ (depth * wait) +
      ((prime : ℚ) ^ wait - 1) * tail)

/-- Total center sensitivity of one ready legal update.

The last term is the transported sensitivity of the moving input state; the preceding terms
differentiate the explicit center and drift coefficients. -/
def parameterSensitivityStep
    (prime depth wait : Nat)
    (driftValue tail sensitivity : ℚ) : ℚ :=
  1 - (prime : ℚ) ^ (depth * wait) -
      ((prime : ℚ) ^ wait - 1) * tail -
    driftValue * ((prime : ℚ) ^ wait - 1) * tail ^ 2 /
      (prime : ℚ) ^ (depth * wait) * sensitivity

/-- The explicit fixed-reset update is the existing legal guard value. -/
theorem fixedResetLegalValue_eq_legalValue
    (parameters : Parameters) (wait : Nat) (tail : ℚ) :
    fixedResetLegalValue parameters.prime parameters.depth wait
        parameters.reset parameters.center tail =
      legalValue parameters wait tail := by
  simp [fixedResetLegalValue, legalValue, drift]

/-- Differentiating the tail extracted from a moving ready state. -/
theorem readyTail_hasDerivAt
    (prime depth wait : Nat) (center : ℚ)
    (state : ℚ → ℚ) (stateDerivative : ℚ)
    (state_derivative : HasDerivAt state stateDerivative center)
    (pole_ne : state center - (prime : ℚ) ^ wait ≠ 0) :
    HasDerivAt
        (fun parameter =>
          (prime : ℚ) ^ (depth * wait) /
            (state parameter - (prime : ℚ) ^ wait))
        (-(prime : ℚ) ^ (depth * wait) * stateDerivative /
          (state center - (prime : ℚ) ^ wait) ^ 2)
        center := by
  convert
    (hasDerivAt_const center ((prime : ℚ) ^ (depth * wait))).div
      (state_derivative.sub_const ((prime : ℚ) ^ wait)) pole_ne using 1
  ring

/-- Chain rule for the fixed-reset affine update with a moving tail. -/
theorem fixedResetLegalValue_hasDerivAt
    (prime depth wait : Nat) (reset center tailValue : ℚ)
    (tail : ℚ → ℚ) (tailDerivative : ℚ)
    (tail_derivative : HasDerivAt tail tailDerivative center)
    (tail_value : tail center = tailValue) :
    HasDerivAt
        (fun parameter =>
          fixedResetLegalValue prime depth wait reset parameter
            (tail parameter))
        (1 -
          ((prime : ℚ) ^ (depth * wait) +
            ((prime : ℚ) ^ wait - 1) * tailValue) +
          (reset - center) *
            ((prime : ℚ) ^ wait - 1) * tailDerivative)
        center := by
  convert
    (hasDerivAt_id center).add
      ((hasDerivAt_const center reset).sub (hasDerivAt_id center) |>.mul
        (((hasDerivAt_const center
          ((prime : ℚ) ^ (depth * wait))).add
            ((hasDerivAt_const center
              ((prime : ℚ) ^ wait - 1)).mul tail_derivative)))) using 1
  simp [tail_value]
  ring

/-- Exact total-sensitivity recurrence at a ready state.

The curve `state` need not itself be a guard orbit.  The theorem is the local chain rule from
which orbitwise sensitivity follows by induction. -/
theorem readyLegalValue_hasDerivAt
    (prime depth wait : Nat) (reset center tailValue : ℚ)
    (state : ℚ → ℚ) (stateDerivative : ℚ)
    (state_derivative : HasDerivAt state stateDerivative center)
    (power_ne : (prime : ℚ) ^ (depth * wait) ≠ 0)
    (tail_ne : tailValue ≠ 0)
    (state_value :
      state center =
        (prime : ℚ) ^ wait +
          (prime : ℚ) ^ (depth * wait) / tailValue) :
    HasDerivAt
        (fun parameter =>
          fixedResetLegalValue prime depth wait reset parameter
            ((prime : ℚ) ^ (depth * wait) /
              (state parameter - (prime : ℚ) ^ wait)))
        (parameterSensitivityStep prime depth wait
          (reset - center) tailValue stateDerivative)
        center := by
  have pole_ne :
      state center - (prime : ℚ) ^ wait ≠ 0 := by
    rw [state_value]
    simpa using div_ne_zero power_ne tail_ne
  have tail_derivative :
      HasDerivAt
          (fun parameter =>
            (prime : ℚ) ^ (depth * wait) /
              (state parameter - (prime : ℚ) ^ wait))
          (-tailValue ^ 2 /
            (prime : ℚ) ^ (depth * wait) * stateDerivative)
          center := by
    have raw :=
      readyTail_hasDerivAt prime depth wait center state
        stateDerivative state_derivative pole_ne
    have state_sub :
        state center - (prime : ℚ) ^ wait =
          (prime : ℚ) ^ (depth * wait) / tailValue := by
      rw [state_value]
      ring
    rw [state_sub] at raw
    convert raw using 1
    field_simp [tail_ne, power_ne]
    ring
  have tail_value :
      (prime : ℚ) ^ (depth * wait) /
          (state center - (prime : ℚ) ^ wait) =
        tailValue := by
    have state_sub :
        state center - (prime : ℚ) ^ wait =
          (prime : ℚ) ^ (depth * wait) / tailValue := by
      rw [state_value]
      ring
    rw [state_sub]
    field_simp [tail_ne, power_ne]
  convert
    fixedResetLegalValue_hasDerivAt prime depth wait reset center
      tailValue
      (fun parameter =>
        (prime : ℚ) ^ (depth * wait) /
          (state parameter - (prime : ℚ) ^ wait))
      (-tailValue ^ 2 /
        (prime : ℚ) ^ (depth * wait) * stateDerivative)
      tail_derivative tail_value using 1
  simp [parameterSensitivityStep]
  ring

/-- A legal step transports negative parameter sensitivity by subtracting exactly its
depth-scaled wait.

The regular part of the derivative is p-adically integral.  The transported term has negative
valuation and therefore dominates without any cancellation ambiguity. -/
theorem parameterSensitivityStep_hasValue
    {prime : Nat} [Fact prime.Prime]
    {depth wait : Nat} {driftValue tailValue sensitivity : ℚ}
    {sensitivityValue : ℤ}
    (depth_positive : 0 < depth) (wait_positive : 0 < wait)
    (drift_unit : IsUnit prime driftValue)
    (tail_unit : IsUnit prime tailValue)
    (sensitivity_value :
      HasValue prime sensitivity sensitivityValue)
    (sensitivity_negative : sensitivityValue < 0) :
    HasValue prime
      (parameterSensitivityStep prime depth wait
        driftValue tailValue sensitivity)
      (sensitivityValue - depth * wait) := by
  let waitPower : ℚ := prime ^ wait
  let depthPower : ℚ := prime ^ (depth * wait)
  let tailCoefficient : ℚ := (waitPower - 1) * tailValue
  let regular : ℚ := 1 - depthPower - tailCoefficient
  let singular : ℚ :=
    driftValue * (waitPower - 1) * tailValue ^ 2 /
      depthPower * sensitivity
  have waitPower_positive : IsPositive prime waitPower := by
    refine ⟨primePower_ne_zero (Fact.out : prime.Prime) wait, ?_⟩
    rw [primePower_valuation]
    exact_mod_cast wait_positive
  have depthExponent_positive : 0 < depth * wait :=
    Nat.mul_pos depth_positive wait_positive
  have depthPower_positive : IsPositive prime depthPower := by
    refine
      ⟨primePower_ne_zero (Fact.out : prime.Prime)
        (depth * wait), ?_⟩
    rw [primePower_valuation]
    exact_mod_cast depthExponent_positive
  have wait_sub_one_unit : IsUnit prime (waitPower - 1) :=
    positive_sub_one waitPower_positive
  have tailCoefficient_unit : IsUnit prime tailCoefficient :=
    mul_hasValue wait_sub_one_unit tail_unit
  have one_sub_depth_unit : IsUnit prime (1 - depthPower) :=
    one_sub_positive depthPower_positive
  have tail_square_unit : IsUnit prime (tailValue ^ 2) := by
    simpa [pow_two] using mul_hasValue tail_unit tail_unit
  have singular_value :
      HasValue prime singular
        (sensitivityValue - depth * wait) := by
    have numerator_unit :
        IsUnit prime
          (driftValue * (waitPower - 1) * tailValue ^ 2) :=
      mul_hasValue
        (mul_hasValue drift_unit wait_sub_one_unit)
        tail_square_unit
    have coefficient_value :
        HasValue prime
          (driftValue * (waitPower - 1) * tailValue ^ 2 /
            depthPower)
          (-(depth * wait : ℤ)) := by
      convert
        div_hasValue numerator_unit
          (primePower_hasValue (prime := prime)
            (depth * wait)) using 1
      omega
    convert mul_hasValue coefficient_value sensitivity_value using 1
    ring
  have singular_negative :
      sensitivityValue - (depth * wait : ℤ) < 0 := by
    omega
  change
    HasValue prime (regular - singular)
      (sensitivityValue - depth * wait)
  by_cases regular_zero : regular = 0
  · rw [regular_zero, zero_sub]
    exact neg_hasValue singular_value
  · have regular_value :
        HasValue prime regular (padicValRat prime regular) :=
      ⟨regular_zero, rfl⟩
    have regular_nonnegative :
        0 ≤ padicValRat prime regular := by
      have bound :=
        min_le_sub (prime := prime)
          (left := 1 - depthPower) (right := tailCoefficient)
          (by simpa [regular] using regular_zero)
      simpa [one_sub_depth_unit.2, tailCoefficient_unit.2,
        regular] using bound
    have singular_lt_regular :
        sensitivityValue - (depth * wait : ℤ) <
          padicValRat prime regular :=
      lt_of_lt_of_le singular_negative regular_nonnegative
    rw [sub_eq_add_neg]
    exact
      add_hasValue_right regular_value (neg_hasValue singular_value)
        singular_lt_regular

end
end MatrixMortality.ReturnGuard
