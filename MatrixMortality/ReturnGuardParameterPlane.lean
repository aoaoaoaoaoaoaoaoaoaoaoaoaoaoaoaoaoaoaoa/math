import MatrixMortality.ReturnGuardAntiHensel

/-!
# Two-parameter guard lifting

The guard has two arithmetic parameters: center and reset.  A simultaneous perturbation moves
one homogeneous residual image along the same projective tangent as a center-only perturbation,
but its scalar coefficient is a genuine linear form in two parameter digits.

At the differential level, the center/reset sensitivity is a two-vector.  One legal step is an
affine rank-one recurrence.  Its exterior product with the incoming sensitivity is independent
of the singular transported term.  Whenever two successive sensitivities span the parameter
plane, one can impose a new affine incidence while assigning the old normalized annular
coefficient any prescribed nonzero value.  This is the exact escape unavailable to a
one-parameter Hensel lift.
-/

namespace MatrixMortality.ReturnGuard

open scoped Matrix

noncomputable section

/-- Parameter-plane coefficient induced by changing center by `centerDigit` and reset by
`resetDigit` on a homogeneous residual source. -/
def centerResetCoefficient
    {R : Type*} [Ring R]
    (centerDigit resetDigit numerator denominator : R) : R :=
  centerDigit * (numerator - denominator) + resetDigit * denominator

/-- Rank-one residual displacement produced by a center/reset parameter digit. -/
def centerResetTangent
    {R : Type*} [CommRing R]
    (power centerDigit resetDigit numerator denominator : R) : Fin 2 → R :=
  centerResetCoefficient centerDigit resetDigit numerator denominator •
    ![1, power]

/-- Moving center and reset independently changes a homogeneous transfer in one exact
rank-one direction.  In center/drift coordinates, a reset perturbation `η` changes drift by
`η-ε` when center changes by `ε`. -/
theorem integralResidualTransfer_centerReset_add_mulVec
    {R : Type*} [CommRing R]
    (prime : R) (depth : Nat)
    (center driftNumerator scale centerPerturbation resetPerturbation : R)
    (wait : Nat) (numerator denominator : R) :
    integralResidualTransfer prime depth
          (center + centerPerturbation)
          (driftNumerator + (resetPerturbation - centerPerturbation))
          scale wait *ᵥ ![numerator, denominator] =
      integralResidualTransfer prime depth center driftNumerator
          scale wait *ᵥ ![numerator, denominator] +
        centerResetTangent (prime ^ (depth * wait))
          centerPerturbation resetPerturbation numerator denominator := by
  ext i
  fin_cases i <;>
    simp [integralResidualTransfer, centerResetTangent,
      centerResetCoefficient, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_succ, smul_eq_mul]
  all_goals ring

/-- A common-factor parameter-plane perturbation preserves that factor and exposes both
digits on the reduced exit. -/
theorem integralResidualTransfer_centerReset_factor
    {R : Type*} [CommRing R]
    (prime : R) (depth : Nat)
    (center driftNumerator scale common centerDigit resetDigit : R)
    (wait : Nat) (numerator denominator : R) (target : Fin 2 → R)
    (image :
      integralResidualTransfer prime depth center driftNumerator scale wait *ᵥ
          ![numerator, denominator] =
        common • target) :
    integralResidualTransfer prime depth
          (center + common * centerDigit)
          (driftNumerator + common * (resetDigit - centerDigit))
          scale wait *ᵥ ![numerator, denominator] =
      common •
        (target +
          centerResetTangent (prime ^ (depth * wait))
            centerDigit resetDigit numerator denominator) := by
  rw [mul_sub]
  rw [integralResidualTransfer_centerReset_add_mulVec, image]
  have tangent_scale :
      centerResetTangent (prime ^ (depth * wait))
          (common * centerDigit) (common * resetDigit)
          numerator denominator =
        common •
          centerResetTangent (prime ^ (depth * wait))
            centerDigit resetDigit numerator denominator := by
    ext i
    fin_cases i <;>
      simp [centerResetTangent, centerResetCoefficient, mul_smul]
    all_goals ring
  rw [tangent_scale, smul_add]

/-- Determinant of two vectors in the parameter plane. -/
def planeCross
    {R : Type*} [Ring R] (left right : Fin 2 → R) : R :=
  left 0 * right 1 - left 1 * right 0

/-- Evaluation of an affine first-order condition on a parameter digit. -/
def affinePlaneValue
    {R : Type*} [CommRing R]
    (intercept : R) (gradient digit : Fin 2 → R) : R :=
  intercept + gradient ⬝ᵥ digit

/-- Unique digit assigning `oldTarget` to one affine condition and zero to another when their
gradients span the parameter plane. -/
def planeSolveDigit
    {K : Type*} [Field K]
    (oldValue : K) (oldGradient : Fin 2 → K)
    (newValue : K) (newGradient : Fin 2 → K)
    (oldTarget : K) : Fin 2 → K :=
  ![
    ((oldTarget - oldValue) * newGradient 1 + oldGradient 1 * newValue) /
      planeCross oldGradient newGradient,
    (-oldGradient 0 * newValue -
        (oldTarget - oldValue) * newGradient 0) /
      planeCross oldGradient newGradient
  ]

/-- The parameter-plane solver satisfies both prescribed affine conditions. -/
theorem planeSolveDigit_spec
    {K : Type*} [Field K]
    (oldValue : K) (oldGradient : Fin 2 → K)
    (newValue : K) (newGradient : Fin 2 → K)
    (oldTarget : K)
    (transverse : planeCross oldGradient newGradient ≠ 0) :
    affinePlaneValue newValue newGradient
          (planeSolveDigit oldValue oldGradient newValue newGradient oldTarget) = 0 ∧
      affinePlaneValue oldValue oldGradient
          (planeSolveDigit oldValue oldGradient newValue newGradient oldTarget) =
        oldTarget := by
  constructor
  · simp [affinePlaneValue, planeSolveDigit, Matrix.dotProduct,
      Fin.sum_univ_succ]
    field_simp [transverse]
    simp [planeCross]
    ring
  · simp [affinePlaneValue, planeSolveDigit, Matrix.dotProduct,
      Fin.sum_univ_succ]
    field_simp [transverse]
    simp [planeCross]
    ring

/-- Unique digit assigning value one to the old annulus and zero to the new incidence when
their gradients span the parameter plane. -/
def planeEscapeDigit
    {K : Type*} [Field K]
    (oldValue : K) (oldGradient : Fin 2 → K)
    (newValue : K) (newGradient : Fin 2 → K) : Fin 2 → K :=
  planeSolveDigit oldValue oldGradient newValue newGradient 1

/-- Two independent parameter directions remove the one-dimensional anti-Hensel conflict:
the selected digit hits the new incidence and normalizes the old annulus to one. -/
theorem planeEscapeDigit_hits_and_preserves
    {K : Type*} [Field K]
    (oldValue : K) (oldGradient : Fin 2 → K)
    (newValue : K) (newGradient : Fin 2 → K)
    (transverse : planeCross oldGradient newGradient ≠ 0) :
    affinePlaneValue newValue newGradient
          (planeEscapeDigit oldValue oldGradient newValue newGradient) = 0 ∧
      affinePlaneValue oldValue oldGradient
          (planeEscapeDigit oldValue oldGradient newValue newGradient) = 1 := by
  simpa [planeEscapeDigit] using
    planeSolveDigit_spec oldValue oldGradient newValue newGradient 1 transverse

/-- A transverse parameter plane always contains a digit imposing the new incidence while
preserving the old annulus. -/
theorem exists_planeDigit_hits_and_preserves
    {K : Type*} [Field K]
    (oldValue : K) (oldGradient : Fin 2 → K)
    (newValue : K) (newGradient : Fin 2 → K)
    (transverse : planeCross oldGradient newGradient ≠ 0) :
    ∃ digit : Fin 2 → K,
      affinePlaneValue newValue newGradient digit = 0 ∧
        affinePlaneValue oldValue oldGradient digit ≠ 0 := by
  refine
    ⟨planeEscapeDigit oldValue oldGradient newValue newGradient,
      (planeEscapeDigit_hits_and_preserves
        oldValue oldGradient newValue newGradient transverse).1, ?_⟩
  rw [(planeEscapeDigit_hits_and_preserves
    oldValue oldGradient newValue newGradient transverse).2]
  exact one_ne_zero

/-- Refining a parameter digit changes an affine condition by the gradient applied to the
refinement. -/
theorem affinePlaneValue_add
    {R : Type*} [CommRing R]
    (intercept : R) (gradient digit refinement : Fin 2 → R) :
    affinePlaneValue intercept gradient (digit + refinement) =
      affinePlaneValue intercept gradient digit +
        gradient ⬝ᵥ refinement := by
  simp [affinePlaneValue, Matrix.dotProduct_add]
  ring

/-- Once an annular coefficient is a unit, every refinement invisible to its current shell
preserves that coefficient.  Historical shells therefore need not remain active after their
normalized value has been discharged to a unit. -/
theorem affinePlaneValue_isUnit_add_of_positive
    {prime : Nat} [Fact prime.Prime]
    (intercept : ℚ) (gradient digit refinement : Fin 2 → ℚ)
    (current_unit :
      PadicValuation.IsUnit prime
        (affinePlaneValue intercept gradient digit))
    (increment_positive :
      PadicValuation.IsPositive prime (gradient ⬝ᵥ refinement)) :
    PadicValuation.IsUnit prime
      (affinePlaneValue intercept gradient (digit + refinement)) := by
  rw [affinePlaneValue_add]
  exact PadicValuation.unit_add_positive current_unit increment_positive

/-- The scalar payload multiplying the center-reset drift in one legal update. -/
def legalPayload
    (prime depth wait : Nat) (tail : ℚ) : ℚ :=
  (prime : ℚ) ^ (depth * wait) +
    ((prime : ℚ) ^ wait - 1) * tail

/-- Singular coefficient transporting an incoming state sensitivity through ready-tail
extraction. -/
def sensitivityMultiplier
    (prime depth wait : Nat) (driftValue tail : ℚ) : ℚ :=
  driftValue * ((prime : ℚ) ^ wait - 1) * tail ^ 2 /
    (prime : ℚ) ^ (depth * wait)

/-- Legal update with center fixed and reset left as an explicit parameter. -/
def fixedCenterLegalValue
    (prime depth wait : Nat) (center reset tail : ℚ) : ℚ :=
  center + (reset - center) * legalPayload prime depth wait tail

/-- The explicit fixed-center update is the existing legal guard value. -/
theorem fixedCenterLegalValue_eq_legalValue
    (parameters : Parameters) (wait : Nat) (tail : ℚ) :
    fixedCenterLegalValue parameters.prime parameters.depth wait
        parameters.center parameters.reset tail =
      legalValue parameters wait tail := by
  simp [fixedCenterLegalValue, legalPayload, legalValue, drift]

/-- Chain rule for the fixed-center update with a moving tail. -/
theorem fixedCenterLegalValue_hasDerivAt
    (prime depth wait : Nat) (center reset tailValue : ℚ)
    (tail : ℚ → ℚ) (tailDerivative : ℚ)
    (tail_derivative : HasDerivAt tail tailDerivative reset)
    (tail_value : tail reset = tailValue) :
    HasDerivAt
        (fun parameter =>
          fixedCenterLegalValue prime depth wait center parameter
            (tail parameter))
        (legalPayload prime depth wait tailValue +
          (reset - center) *
            ((prime : ℚ) ^ wait - 1) * tailDerivative)
        reset := by
  convert
    (hasDerivAt_const reset center).add
      (((hasDerivAt_id reset).sub_const center).mul
        (((hasDerivAt_const reset
          ((prime : ℚ) ^ (depth * wait))).add
            ((hasDerivAt_const reset
              ((prime : ℚ) ^ wait - 1)).mul tail_derivative)))) using 1
  simp [fixedCenterLegalValue, legalPayload, tail_value]
  ring

/-- Center/reset gradient after one legal step.  Coordinate zero is center sensitivity and
coordinate one is reset sensitivity. -/
def parameterGradientStep
    (prime depth wait : Nat) (driftValue tail : ℚ)
    (gradient : Fin 2 → ℚ) : Fin 2 → ℚ :=
  ![1 - legalPayload prime depth wait tail,
      legalPayload prime depth wait tail] -
    sensitivityMultiplier prime depth wait driftValue tail • gradient

/-- The center coordinate recovers the fixed-reset sensitivity recurrence. -/
theorem parameterGradientStep_zero
    (prime depth wait : Nat) (driftValue tail : ℚ)
    (gradient : Fin 2 → ℚ) :
    parameterGradientStep prime depth wait driftValue tail gradient 0 =
      parameterSensitivityStep prime depth wait
        driftValue tail (gradient 0) := by
  simp [parameterGradientStep, parameterSensitivityStep, legalPayload,
    sensitivityMultiplier]
  ring

/-- The reset coordinate has the complementary direct derivative. -/
theorem parameterGradientStep_one
    (prime depth wait : Nat) (driftValue tail : ℚ)
    (gradient : Fin 2 → ℚ) :
    parameterGradientStep prime depth wait driftValue tail gradient 1 =
      legalPayload prime depth wait tail -
        sensitivityMultiplier prime depth wait driftValue tail *
          gradient 1 := by
  simp [parameterGradientStep]

/-- Exact reset-sensitivity recurrence at a ready state.

This is the second component of `parameterGradientStep`; together with
`readyLegalValue_hasDerivAt`, it makes that vector the actual center/reset gradient. -/
theorem readyLegalValue_reset_hasDerivAt
    (prime depth wait : Nat) (center reset tailValue : ℚ)
    (state : ℚ → ℚ) (stateDerivative : ℚ)
    (state_derivative : HasDerivAt state stateDerivative reset)
    (power_ne : (prime : ℚ) ^ (depth * wait) ≠ 0)
    (tail_ne : tailValue ≠ 0)
    (state_value :
      state reset =
        (prime : ℚ) ^ wait +
          (prime : ℚ) ^ (depth * wait) / tailValue) :
    HasDerivAt
        (fun parameter =>
          fixedCenterLegalValue prime depth wait center parameter
            ((prime : ℚ) ^ (depth * wait) /
              (state parameter - (prime : ℚ) ^ wait)))
        (legalPayload prime depth wait tailValue -
          sensitivityMultiplier prime depth wait
            (reset - center) tailValue * stateDerivative)
        reset := by
  have pole_ne :
      state reset - (prime : ℚ) ^ wait ≠ 0 := by
    rw [state_value]
    simpa using div_ne_zero power_ne tail_ne
  have tail_derivative :
      HasDerivAt
          (fun parameter =>
            (prime : ℚ) ^ (depth * wait) /
              (state parameter - (prime : ℚ) ^ wait))
          (-tailValue ^ 2 /
            (prime : ℚ) ^ (depth * wait) * stateDerivative)
          reset := by
    have raw :=
      readyTail_hasDerivAt prime depth wait reset state
        stateDerivative state_derivative pole_ne
    have state_sub :
        state reset - (prime : ℚ) ^ wait =
          (prime : ℚ) ^ (depth * wait) / tailValue := by
      rw [state_value]
      ring
    rw [state_sub] at raw
    convert raw using 1
    field_simp [tail_ne, power_ne]
    ring
  have tail_value :
      (prime : ℚ) ^ (depth * wait) /
          (state reset - (prime : ℚ) ^ wait) =
        tailValue := by
    have state_sub :
        state reset - (prime : ℚ) ^ wait =
          (prime : ℚ) ^ (depth * wait) / tailValue := by
      rw [state_value]
      ring
    rw [state_sub]
    field_simp [tail_ne, power_ne]
  convert
    fixedCenterLegalValue_hasDerivAt prime depth wait center reset
      tailValue
      (fun parameter =>
        (prime : ℚ) ^ (depth * wait) /
          (state parameter - (prime : ℚ) ^ wait))
      (-tailValue ^ 2 /
        (prime : ℚ) ^ (depth * wait) * stateDerivative)
      tail_derivative tail_value using 1
  simp [sensitivityMultiplier]
  ring

/-- The sum of the two parameter sensitivities obeys a closed affine recurrence. -/
theorem parameterGradientStep_sum
    (prime depth wait : Nat) (driftValue tail : ℚ)
    (gradient : Fin 2 → ℚ) :
    parameterGradientStep prime depth wait driftValue tail gradient 0 +
        parameterGradientStep prime depth wait driftValue tail gradient 1 =
      1 -
        sensitivityMultiplier prime depth wait driftValue tail *
          (gradient 0 + gradient 1) := by
  simp [parameterGradientStep]
  ring

/-- Exterior sensitivity transport.  The singular term is parallel to the incoming gradient
and disappears from the cross product; transversality depends only on the explicit payload. -/
theorem planeCross_parameterGradientStep
    (prime depth wait : Nat) (driftValue tail : ℚ)
    (gradient : Fin 2 → ℚ) :
    planeCross gradient
        (parameterGradientStep prime depth wait driftValue tail gradient) =
      legalPayload prime depth wait tail * (gradient 0 + gradient 1) -
        gradient 1 := by
  simp [planeCross, parameterGradientStep]
  ring

/-- Guard-specific two-parameter escape criterion.  The transported sensitivity is transverse
exactly when the displayed scalar is nonzero; then one digit imposes the next incidence while
preserving the current annulus. -/
theorem exists_planeDigit_hits_parameterGradientStep_and_preserves
    (prime depth wait : Nat) (driftValue tail oldValue newValue : ℚ)
    (gradient : Fin 2 → ℚ)
    (transverse :
      legalPayload prime depth wait tail * (gradient 0 + gradient 1) -
          gradient 1 ≠
        0) :
    ∃ digit : Fin 2 → ℚ,
      affinePlaneValue newValue
          (parameterGradientStep prime depth wait driftValue tail gradient)
          digit =
        0 ∧
      affinePlaneValue oldValue gradient digit ≠ 0 := by
  apply exists_planeDigit_hits_and_preserves
  rw [planeCross_parameterGradientStep]
  exact transverse

end
end MatrixMortality.ReturnGuard
