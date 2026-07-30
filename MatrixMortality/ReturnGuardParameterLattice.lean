import MatrixMortality.ReturnGuardParameterPlane

/-!
# Anisotropic parameter lattice

The center/reset gradient is two-dimensional over the rationals but becomes increasingly
ill-conditioned p-adically.  In mass/reset coordinates, one legal step is

```text
mass'  = 1 - C·mass,
reset' = H - C·reset,
```

where the payload `H` is a unit and the singular multiplier `C` has valuation `-s a`.  Equal
input valuations therefore remain equal and drop by exactly `s a`.

The projective gradient ray `reset/mass` has a simpler law: its displacement is the exterior
product of consecutive gradients divided by their masses.  When the exterior product is
nonzero, the displacement has positive valuation at least `s a-v`, where `v≤0` is the current
common sensitivity valuation.  Successive parameter directions hence freeze p-adically even
while their magnitudes explode.  This is the exact anisotropic precision tax hidden by bare
rational transversality.
-/

namespace MatrixMortality.ReturnGuard

open MatrixMortality.PadicValuation

noncomputable section

/-- Sum coordinate of the center/reset sensitivity. -/
def parameterGradientMass (gradient : Fin 2 → ℚ) : ℚ :=
  gradient 0 + gradient 1

/-- Projective direction of the center/reset sensitivity in mass/reset coordinates. -/
def parameterGradientRay (gradient : Fin 2 → ℚ) : ℚ :=
  gradient 1 / parameterGradientMass gradient

/-- The legal payload is a p-adic unit at every positive wait and positive depth. -/
theorem legalPayload_isUnit
    {prime : Nat} [Fact prime.Prime]
    {depth wait : Nat} {tail : ℚ}
    (depth_positive : 0 < depth) (wait_positive : 0 < wait)
    (tail_unit : IsUnit prime tail) :
    IsUnit prime (legalPayload prime depth wait tail) := by
  have waitPower_positive :
      IsPositive prime ((prime : ℚ) ^ wait) := by
    refine ⟨primePower_ne_zero (Fact.out : prime.Prime) wait, ?_⟩
    rw [primePower_valuation]
    exact_mod_cast wait_positive
  have waitCoefficient_unit :
      IsUnit prime (((prime : ℚ) ^ wait - 1) * tail) :=
    mul_hasValue (positive_sub_one waitPower_positive) tail_unit
  have depthExponent_positive : 0 < depth * wait :=
    Nat.mul_pos depth_positive wait_positive
  have depthPower_positive :
      IsPositive prime ((prime : ℚ) ^ (depth * wait)) := by
    refine
      ⟨primePower_ne_zero (Fact.out : prime.Prime) (depth * wait), ?_⟩
    rw [primePower_valuation]
    exact_mod_cast depthExponent_positive
  rw [legalPayload, add_comm]
  exact unit_add_positive waitCoefficient_unit depthPower_positive

/-- The singular sensitivity multiplier has exactly valuation `-s a`. -/
theorem sensitivityMultiplier_hasValue
    {prime : Nat} [Fact prime.Prime]
    {depth wait : Nat} {driftValue tail : ℚ}
    (wait_positive : 0 < wait)
    (drift_unit : IsUnit prime driftValue)
    (tail_unit : IsUnit prime tail) :
    HasValue prime
      (sensitivityMultiplier prime depth wait driftValue tail)
      (-(depth * wait : ℤ)) := by
  have waitCoefficient_unit :
      IsUnit prime ((prime : ℚ) ^ wait - 1) :=
    positive_sub_one
      ⟨primePower_ne_zero (Fact.out : prime.Prime) wait, by
        rw [primePower_valuation]
        exact_mod_cast wait_positive⟩
  have tail_square_unit : IsUnit prime (tail ^ 2) := by
    simpa [pow_two] using mul_hasValue tail_unit tail_unit
  have numerator_unit :
      IsUnit prime
        (driftValue * ((prime : ℚ) ^ wait - 1) * tail ^ 2) :=
    mul_hasValue
      (mul_hasValue drift_unit waitCoefficient_unit)
      tail_square_unit
  simpa [sensitivityMultiplier] using
    div_hasValue numerator_unit
      (primePower_hasValue (prime := prime) (depth * wait))

/-- Mass coordinate of one parameter-gradient step. -/
theorem parameterGradientMass_step
    (prime depth wait : Nat) (driftValue tail : ℚ)
    (gradient : Fin 2 → ℚ) :
    parameterGradientMass
        (parameterGradientStep prime depth wait driftValue tail gradient) =
      1 -
        sensitivityMultiplier prime depth wait driftValue tail *
          parameterGradientMass gradient := by
  simp [parameterGradientMass, parameterGradientStep]
  ring

/-- Equal nonpositive sensitivity valuations remain equal after one legal step and lose
exactly `s a` valuation units in the mass coordinate. -/
theorem parameterGradientMass_step_hasValue
    {prime : Nat} [Fact prime.Prime]
    {depth wait : Nat} {driftValue tail : ℚ}
    {gradient : Fin 2 → ℚ} {gradientValue : ℤ}
    (depth_positive : 0 < depth) (wait_positive : 0 < wait)
    (drift_unit : IsUnit prime driftValue)
    (mass_value :
      HasValue prime (parameterGradientMass gradient) gradientValue)
    (mass_nonpositive : gradientValue ≤ 0)
    (tail_unit : IsUnit prime tail) :
    HasValue prime
      (parameterGradientMass
        (parameterGradientStep prime depth wait driftValue tail gradient))
      (gradientValue - depth * wait) := by
  have multiplier_value :=
    sensitivityMultiplier_hasValue
      (prime := prime) (depth := depth) (wait := wait)
      wait_positive drift_unit tail_unit
  have transported_value :
      HasValue prime
        (sensitivityMultiplier prime depth wait driftValue tail *
          parameterGradientMass gradient)
        (gradientValue - depth * wait) := by
    convert mul_hasValue multiplier_value mass_value using 1
    omega
  have transported_negative :
      gradientValue - (depth * wait : ℤ) < 0 := by
    have depthWait_positive : 0 < depth * wait :=
      Nat.mul_pos depth_positive wait_positive
    omega
  rw [parameterGradientMass_step, sub_eq_add_neg]
  exact
    add_hasValue_right
      (show IsUnit prime (1 : ℚ) from ⟨one_ne_zero, padicValRat.one⟩)
      (neg_hasValue transported_value)
      (by simpa using transported_negative)

/-- Equal nonpositive sensitivity valuations remain equal after one legal step and lose
exactly `s a` valuation units in the reset coordinate. -/
theorem parameterGradientStep_one_hasValue
    {prime : Nat} [Fact prime.Prime]
    {depth wait : Nat} {driftValue tail : ℚ}
    {gradient : Fin 2 → ℚ} {gradientValue : ℤ}
    (depth_positive : 0 < depth) (wait_positive : 0 < wait)
    (drift_unit : IsUnit prime driftValue)
    (reset_value : HasValue prime (gradient 1) gradientValue)
    (reset_nonpositive : gradientValue ≤ 0)
    (tail_unit : IsUnit prime tail) :
    HasValue prime
      (parameterGradientStep prime depth wait driftValue tail gradient 1)
      (gradientValue - depth * wait) := by
  have payload_unit :=
    legalPayload_isUnit
      (prime := prime) (depth := depth) (wait := wait)
      depth_positive wait_positive tail_unit
  have multiplier_value :=
    sensitivityMultiplier_hasValue
      (prime := prime) (depth := depth) (wait := wait)
      wait_positive drift_unit tail_unit
  have transported_value :
      HasValue prime
        (sensitivityMultiplier prime depth wait driftValue tail *
          gradient 1)
        (gradientValue - depth * wait) := by
    convert mul_hasValue multiplier_value reset_value using 1
    omega
  have transported_negative :
      gradientValue - (depth * wait : ℤ) < 0 := by
    have depthWait_positive : 0 < depth * wait :=
      Nat.mul_pos depth_positive wait_positive
    omega
  rw [parameterGradientStep_one, sub_eq_add_neg]
  exact
    add_hasValue_right payload_unit (neg_hasValue transported_value)
      (by simpa [payload_unit.2] using transported_negative)

/-- Exact projective-ray displacement under one parameter-gradient step. -/
theorem parameterGradientRay_step_sub
    (prime depth wait : Nat) (driftValue tail : ℚ)
    (gradient : Fin 2 → ℚ)
    (mass_ne : parameterGradientMass gradient ≠ 0)
    (next_mass_ne :
      parameterGradientMass
        (parameterGradientStep prime depth wait driftValue tail gradient) ≠
        0) :
    parameterGradientRay
          (parameterGradientStep prime depth wait driftValue tail gradient) -
        parameterGradientRay gradient =
      planeCross gradient
          (parameterGradientStep prime depth wait driftValue tail gradient) /
        (parameterGradientMass
            (parameterGradientStep prime depth wait driftValue tail gradient) *
          parameterGradientMass gradient) := by
  simp only [parameterGradientRay, parameterGradientMass, planeCross]
  change gradient 0 + gradient 1 ≠ 0 at mass_ne
  change
    parameterGradientStep prime depth wait driftValue tail gradient 0 +
        parameterGradientStep prime depth wait driftValue tail gradient 1 ≠
      0 at next_mass_ne
  field_simp [mass_ne, next_mass_ne]
  ring

/-- The exterior sensitivity is the current mass times the discrepancy between payload and
gradient ray. -/
theorem planeCross_parameterGradientStep_eq_mass_mul_rayDefect
    (prime depth wait : Nat) (driftValue tail : ℚ)
    (gradient : Fin 2 → ℚ)
    (mass_ne : parameterGradientMass gradient ≠ 0) :
    planeCross gradient
        (parameterGradientStep prime depth wait driftValue tail gradient) =
      parameterGradientMass gradient *
        (legalPayload prime depth wait tail -
          parameterGradientRay gradient) := by
  rw [planeCross_parameterGradientStep]
  simp only [parameterGradientMass, parameterGradientRay]
  change gradient 0 + gradient 1 ≠ 0 at mass_ne
  field_simp [mass_ne]

/-- Exact valuation of the projective-ray displacement.

If mass and reset coordinates have a common nonpositive value `v`, the next ray displacement
has value

```text
v_p(H-ray) - v + s a.
```

The first term is nonnegative because both `H` and `ray` are units. -/
theorem parameterGradientRay_step_sub_hasValue
    {prime : Nat} [Fact prime.Prime]
    {depth wait : Nat} {driftValue tail : ℚ}
    {gradient : Fin 2 → ℚ} {gradientValue : ℤ}
    (depth_positive : 0 < depth) (wait_positive : 0 < wait)
    (drift_unit : IsUnit prime driftValue)
    (mass_value :
      HasValue prime (parameterGradientMass gradient) gradientValue)
    (gradient_nonpositive : gradientValue ≤ 0)
    (tail_unit : IsUnit prime tail)
    (transverse :
      planeCross gradient
        (parameterGradientStep prime depth wait driftValue tail gradient) ≠
        0) :
    HasValue prime
      (parameterGradientRay
          (parameterGradientStep prime depth wait driftValue tail gradient) -
        parameterGradientRay gradient)
      (padicValRat prime
          (legalPayload prime depth wait tail -
            parameterGradientRay gradient) -
        gradientValue + depth * wait) := by
  have next_mass_value :=
    parameterGradientMass_step_hasValue
      depth_positive wait_positive drift_unit mass_value
      gradient_nonpositive tail_unit
  have rayDefect_ne :
      legalPayload prime depth wait tail -
          parameterGradientRay gradient ≠
        0 := by
    intro defect_zero
    apply transverse
    rw [planeCross_parameterGradientStep_eq_mass_mul_rayDefect
      prime depth wait driftValue tail gradient mass_value.1,
      defect_zero, mul_zero]
  have rayDefect_value :
      HasValue prime
        (legalPayload prime depth wait tail -
          parameterGradientRay gradient)
        (padicValRat prime
          (legalPayload prime depth wait tail -
            parameterGradientRay gradient)) :=
    ⟨rayDefect_ne, rfl⟩
  have cross_value :
      HasValue prime
        (planeCross gradient
          (parameterGradientStep prime depth wait driftValue tail gradient))
        (gradientValue +
          padicValRat prime
            (legalPayload prime depth wait tail -
              parameterGradientRay gradient)) := by
    rw [planeCross_parameterGradientStep_eq_mass_mul_rayDefect
      prime depth wait driftValue tail gradient mass_value.1]
    exact mul_hasValue mass_value rayDefect_value
  have denominator_value :
      HasValue prime
        (parameterGradientMass
            (parameterGradientStep prime depth wait driftValue tail gradient) *
          parameterGradientMass gradient)
        ((gradientValue - depth * wait) + gradientValue) :=
    mul_hasValue next_mass_value mass_value
  rw [parameterGradientRay_step_sub
    prime depth wait driftValue tail gradient
    mass_value.1 next_mass_value.1]
  convert div_hasValue cross_value denominator_value using 1
  omega

/-- Consecutive parameter rays become p-adically closer by at least the current singular depth
plus the magnitude already accumulated by the gradient. -/
theorem parameterGradientRay_step_valuation_lower_bound
    {prime : Nat} [Fact prime.Prime]
    {depth wait : Nat} {driftValue tail : ℚ}
    {gradient : Fin 2 → ℚ} {gradientValue : ℤ}
    (depth_positive : 0 < depth) (wait_positive : 0 < wait)
    (drift_unit : IsUnit prime driftValue)
    (mass_value :
      HasValue prime (parameterGradientMass gradient) gradientValue)
    (reset_value : HasValue prime (gradient 1) gradientValue)
    (gradient_nonpositive : gradientValue ≤ 0)
    (tail_unit : IsUnit prime tail)
    (transverse :
      planeCross gradient
        (parameterGradientStep prime depth wait driftValue tail gradient) ≠
        0) :
    (depth * wait : ℤ) - gradientValue ≤
      padicValRat prime
        (parameterGradientRay
            (parameterGradientStep prime depth wait driftValue tail gradient) -
          parameterGradientRay gradient) := by
  have displacement_value :=
    parameterGradientRay_step_sub_hasValue
      depth_positive wait_positive drift_unit mass_value
      gradient_nonpositive tail_unit transverse
  rw [displacement_value.2]
  have ray_value :
      IsUnit prime (parameterGradientRay gradient) := by
    simpa [parameterGradientRay] using div_hasValue reset_value mass_value
  have payload_unit :=
    legalPayload_isUnit
      (prime := prime) (depth := depth) (wait := wait)
      depth_positive wait_positive tail_unit
  have defect_nonnegative :
      0 ≤
        padicValRat prime
          (legalPayload prime depth wait tail -
            parameterGradientRay gradient) := by
    have rayDefect_ne :
        legalPayload prime depth wait tail -
            parameterGradientRay gradient ≠
          0 := by
      intro defect_zero
      apply transverse
      rw [planeCross_parameterGradientStep_eq_mass_mul_rayDefect
        prime depth wait driftValue tail gradient mass_value.1,
        defect_zero, mul_zero]
    have lower := min_le_sub (prime := prime) rayDefect_ne
    simpa [payload_unit.2, ray_value.2] using lower
  omega

/-- Rational transversality survives, but consecutive parameter rays cannot remain uniformly
unimodular: every nonzero ray displacement has positive valuation. -/
theorem parameterGradientRay_step_isPositive
    {prime : Nat} [Fact prime.Prime]
    {depth wait : Nat} {driftValue tail : ℚ}
    {gradient : Fin 2 → ℚ} {gradientValue : ℤ}
    (depth_positive : 0 < depth) (wait_positive : 0 < wait)
    (drift_unit : IsUnit prime driftValue)
    (mass_value :
      HasValue prime (parameterGradientMass gradient) gradientValue)
    (reset_value : HasValue prime (gradient 1) gradientValue)
    (gradient_nonpositive : gradientValue ≤ 0)
    (tail_unit : IsUnit prime tail)
    (transverse :
      planeCross gradient
        (parameterGradientStep prime depth wait driftValue tail gradient) ≠
        0) :
    IsPositive prime
      (parameterGradientRay
          (parameterGradientStep prime depth wait driftValue tail gradient) -
        parameterGradientRay gradient) := by
  have displacement_value :=
    parameterGradientRay_step_sub_hasValue
      depth_positive wait_positive drift_unit mass_value
      gradient_nonpositive tail_unit transverse
  refine ⟨displacement_value.1, ?_⟩
  have lower :=
    parameterGradientRay_step_valuation_lower_bound
      depth_positive wait_positive drift_unit mass_value reset_value
      gradient_nonpositive tail_unit transverse
  have depthWait_positive : 0 < depth * wait :=
    Nat.mul_pos depth_positive wait_positive
  omega

end
end MatrixMortality.ReturnGuard
