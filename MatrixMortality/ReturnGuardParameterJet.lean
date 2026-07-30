import MatrixMortality.ReturnGuardParameterLattice

/-!
# Renormalized parameter jet

The center/reset sensitivity has an exact integrating factor.  If `q` is transported by

```text
q' = -Cq,
```

alongside the gradient recurrence

```text
g' = (1-H,H) - Cg,
```

then the mass/reset chart of `g/q` is translated by `(1,H)/q'`.  Its increments therefore
become increasingly p-adically small even while the raw gradient grows.

The normalized transverse defect

```text
κ(H,q,g) = (H(g₀+g₁)-g₁)/q
```

is exactly conserved through the step carrying payload `H`.  Changing the next payload is
the sole source of defect evolution.  This is the fixed-dimensional higher jet hidden behind
the freezing projective ray.

The final section proves a sharp obstruction: for every positive depth `N`, a unit tail can
make the first normalized transverse defect have valuation exactly `N`.  Renormalization
therefore removes sensitivity growth but cannot place transversality in one fixed unit
annulus.
-/

namespace MatrixMortality.ReturnGuard

open MatrixMortality.PadicValuation

noncomputable section

/-- Integrating-factor step for the singular center/reset sensitivity transport. -/
def sensitivityScaleStep
    (prime depth wait : Nat) (driftValue tail scale : ℚ) : ℚ :=
  -sensitivityMultiplier prime depth wait driftValue tail * scale

/-- Mass/reset coordinates of a parameter gradient after division by its integrating factor. -/
def renormalizedParameterGradient
    (scale : ℚ) (gradient : Fin 2 → ℚ) : Fin 2 → ℚ :=
  ![
    parameterGradientMass gradient / scale,
    gradient 1 / scale
  ]

/-- The transverse determinant after removal of the singular sensitivity scale. -/
def renormalizedTransverseDefect
    (payload scale : ℚ) (gradient : Fin 2 → ℚ) : ℚ :=
  (payload * parameterGradientMass gradient - gradient 1) / scale

/-- Iteration of one constant-coefficient parameter-gradient stage. -/
def parameterGradientOrbit
    (prime depth wait : Nat) (driftValue tail : ℚ)
    (gradient : Fin 2 → ℚ) : Nat → Fin 2 → ℚ
  | 0 => gradient
  | steps + 1 =>
      parameterGradientStep prime depth wait driftValue tail
        (parameterGradientOrbit prime depth wait driftValue tail gradient steps)

/-- Iteration of the matching sensitivity integrating factor. -/
def sensitivityScaleOrbit
    (prime depth wait : Nat) (driftValue tail scale : ℚ) : Nat → ℚ
  | 0 => scale
  | steps + 1 =>
      sensitivityScaleStep prime depth wait driftValue tail
        (sensitivityScaleOrbit prime depth wait driftValue tail scale steps)

/-- A nonzero scale and multiplier produce a nonzero next integrating factor. -/
theorem sensitivityScaleStep_ne_zero
    (prime depth wait : Nat) (driftValue tail scale : ℚ)
    (multiplier_ne :
      sensitivityMultiplier prime depth wait driftValue tail ≠ 0)
    (scale_ne : scale ≠ 0) :
    sensitivityScaleStep prime depth wait driftValue tail scale ≠ 0 := by
  simp [sensitivityScaleStep, multiplier_ne, scale_ne]

/-- The integrating factor loses exactly `s a` valuation units at one legal step. -/
theorem sensitivityScaleStep_hasValue
    {prime : Nat} [Fact prime.Prime]
    {depth wait : Nat} {driftValue tail scale : ℚ} {scaleValue : ℤ}
    (wait_positive : 0 < wait)
    (drift_unit : IsUnit prime driftValue)
    (tail_unit : IsUnit prime tail)
    (scale_value : HasValue prime scale scaleValue) :
    HasValue prime
      (sensitivityScaleStep prime depth wait driftValue tail scale)
      (scaleValue - depth * wait) := by
  have multiplier_value :=
    sensitivityMultiplier_hasValue
      (prime := prime) (depth := depth) (wait := wait)
      wait_positive drift_unit tail_unit
  have stepped :=
    mul_hasValue (neg_hasValue multiplier_value) scale_value
  convert stepped using 1
  ring

/-- Exact integrating-factor normal form of one parameter-gradient step. -/
theorem renormalizedParameterGradient_step
    (prime depth wait : Nat) (driftValue tail scale : ℚ)
    (gradient : Fin 2 → ℚ)
    (multiplier_ne :
      sensitivityMultiplier prime depth wait driftValue tail ≠ 0)
    (scale_ne : scale ≠ 0) :
    renormalizedParameterGradient
        (sensitivityScaleStep prime depth wait driftValue tail scale)
        (parameterGradientStep prime depth wait driftValue tail gradient) =
      renormalizedParameterGradient scale gradient +
        ![
          1 /
            sensitivityScaleStep prime depth wait driftValue tail scale,
          legalPayload prime depth wait tail /
            sensitivityScaleStep prime depth wait driftValue tail scale
        ] := by
  ext i
  fin_cases i <;>
    simp [renormalizedParameterGradient, parameterGradientMass,
      parameterGradientStep, sensitivityScaleStep]
  all_goals field_simp [multiplier_ne, scale_ne]
  all_goals ring

/-- Both coordinates of the renormalized jet move at the same exact positive precision.
The precision is the new cumulative integrating-factor depth. -/
theorem renormalizedParameterGradient_step_displacement_hasValue
    {prime : Nat} [Fact prime.Prime]
    {depth wait : Nat} {driftValue tail scale : ℚ} {scaleValue : ℤ}
    (gradient : Fin 2 → ℚ)
    (depth_positive : 0 < depth) (wait_positive : 0 < wait)
    (drift_unit : IsUnit prime driftValue)
    (tail_unit : IsUnit prime tail)
    (scale_value : HasValue prime scale scaleValue) :
    HasValue prime
        (renormalizedParameterGradient
            (sensitivityScaleStep prime depth wait driftValue tail scale)
            (parameterGradientStep prime depth wait driftValue tail
              gradient) 0 -
          renormalizedParameterGradient scale gradient 0)
        (depth * wait - scaleValue) ∧
      HasValue prime
        (renormalizedParameterGradient
            (sensitivityScaleStep prime depth wait driftValue tail scale)
            (parameterGradientStep prime depth wait driftValue tail
              gradient) 1 -
          renormalizedParameterGradient scale gradient 1)
        (depth * wait - scaleValue) := by
  have multiplier_value :=
    sensitivityMultiplier_hasValue
      (prime := prime) (depth := depth) (wait := wait)
      wait_positive drift_unit tail_unit
  have next_scale_value :=
    sensitivityScaleStep_hasValue
      (prime := prime) (depth := depth) (wait := wait)
      wait_positive drift_unit tail_unit scale_value
  have normalized_step :=
    renormalizedParameterGradient_step
      prime depth wait driftValue tail scale gradient
      multiplier_value.1 scale_value.1
  have zero_step := congrFun normalized_step 0
  have one_step := congrFun normalized_step 1
  simp only [Pi.add_apply, Matrix.cons_val_zero] at zero_step
  simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.head_cons] at one_step
  have zero_displacement :
      renormalizedParameterGradient
            (sensitivityScaleStep prime depth wait driftValue tail scale)
            (parameterGradientStep prime depth wait driftValue tail
              gradient) 0 -
          renormalizedParameterGradient scale gradient 0 =
        1 / sensitivityScaleStep prime depth wait driftValue tail scale := by
    rw [zero_step]
    ring
  have one_displacement :
      renormalizedParameterGradient
            (sensitivityScaleStep prime depth wait driftValue tail scale)
            (parameterGradientStep prime depth wait driftValue tail
              gradient) 1 -
          renormalizedParameterGradient scale gradient 1 =
        legalPayload prime depth wait tail /
          sensitivityScaleStep prime depth wait driftValue tail scale := by
    rw [one_step]
    ring
  rw [zero_displacement, one_displacement]
  have one_unit : IsUnit prime (1 : ℚ) :=
    ⟨one_ne_zero, padicValRat.one⟩
  have payload_unit :=
    legalPayload_isUnit
      (prime := prime) (depth := depth) (wait := wait)
      depth_positive wait_positive tail_unit
  constructor
  · convert div_hasValue one_unit next_scale_value using 1
    omega
  · convert div_hasValue payload_unit next_scale_value using 1
    omega

/-- The normalized transverse defect is the raw consecutive exterior product divided by the
incoming integrating factor. -/
theorem renormalizedTransverseDefect_eq_planeCross_step
    (prime depth wait : Nat) (driftValue tail scale : ℚ)
    (gradient : Fin 2 → ℚ) :
    renormalizedTransverseDefect
        (legalPayload prime depth wait tail) scale gradient =
      planeCross gradient
          (parameterGradientStep prime depth wait driftValue tail gradient) /
        scale := by
  rw [planeCross_parameterGradientStep]
  simp [renormalizedTransverseDefect, parameterGradientMass]

/-- Renormalized transversality is exactly conserved across the step whose payload defines it. -/
theorem renormalizedTransverseDefect_step
    (prime depth wait : Nat) (driftValue tail scale : ℚ)
    (gradient : Fin 2 → ℚ)
    (multiplier_ne :
      sensitivityMultiplier prime depth wait driftValue tail ≠ 0)
    (scale_ne : scale ≠ 0) :
    renormalizedTransverseDefect
        (legalPayload prime depth wait tail)
        (sensitivityScaleStep prime depth wait driftValue tail scale)
        (parameterGradientStep prime depth wait driftValue tail gradient) =
      renormalizedTransverseDefect
        (legalPayload prime depth wait tail) scale gradient := by
  simp only [renormalizedTransverseDefect]
  rw [parameterGradientMass_step, parameterGradientStep_one]
  field_simp [sensitivityScaleStep_ne_zero prime depth wait
    driftValue tail scale multiplier_ne scale_ne, scale_ne]
  simp [sensitivityScaleStep]
  ring

/-- Changing the payload transports the normalized defect by one mass-weighted difference. -/
theorem renormalizedTransverseDefect_nextPayload
    (prime depth wait : Nat) (driftValue tail scale nextPayload : ℚ)
    (gradient : Fin 2 → ℚ)
    (multiplier_ne :
      sensitivityMultiplier prime depth wait driftValue tail ≠ 0)
    (scale_ne : scale ≠ 0) :
    renormalizedTransverseDefect nextPayload
        (sensitivityScaleStep prime depth wait driftValue tail scale)
        (parameterGradientStep prime depth wait driftValue tail gradient) =
      renormalizedTransverseDefect
          (legalPayload prime depth wait tail) scale gradient +
        (nextPayload - legalPayload prime depth wait tail) *
          renormalizedParameterGradient
            (sensitivityScaleStep prime depth wait driftValue tail scale)
            (parameterGradientStep prime depth wait driftValue tail gradient) 0 := by
  calc
    _ =
        renormalizedTransverseDefect
            (legalPayload prime depth wait tail)
            (sensitivityScaleStep prime depth wait driftValue tail scale)
            (parameterGradientStep prime depth wait driftValue tail gradient) +
          (nextPayload - legalPayload prime depth wait tail) *
            renormalizedParameterGradient
              (sensitivityScaleStep prime depth wait driftValue tail scale)
              (parameterGradientStep prime depth wait driftValue tail gradient) 0 := by
      simp only [renormalizedTransverseDefect,
        renormalizedParameterGradient]
      field_simp [sensitivityScaleStep_ne_zero prime depth wait
        driftValue tail scale multiplier_ne scale_ne]
      ring
    _ = _ := by
      rw [renormalizedTransverseDefect_step
        prime depth wait driftValue tail scale gradient multiplier_ne scale_ne]

/-- The integrating factor remains nonzero through every constant-coefficient iterate. -/
theorem sensitivityScaleOrbit_ne_zero
    (prime depth wait : Nat) (driftValue tail scale : ℚ)
    (multiplier_ne :
      sensitivityMultiplier prime depth wait driftValue tail ≠ 0)
    (scale_ne : scale ≠ 0) :
    ∀ steps,
      sensitivityScaleOrbit prime depth wait driftValue tail scale steps ≠ 0 := by
  intro steps
  induction steps with
  | zero =>
      simpa [sensitivityScaleOrbit] using scale_ne
  | succ steps induction =>
      rw [sensitivityScaleOrbit]
      exact
        sensitivityScaleStep_ne_zero prime depth wait driftValue tail
          (sensitivityScaleOrbit prime depth wait driftValue tail scale steps)
          multiplier_ne induction

/-- Constant-coefficient iteration preserves the normalized transverse defect at every depth. -/
theorem renormalizedTransverseDefect_orbit
    (prime depth wait : Nat) (driftValue tail scale : ℚ)
    (gradient : Fin 2 → ℚ)
    (multiplier_ne :
      sensitivityMultiplier prime depth wait driftValue tail ≠ 0)
    (scale_ne : scale ≠ 0) :
    ∀ steps,
      renormalizedTransverseDefect
          (legalPayload prime depth wait tail)
          (sensitivityScaleOrbit prime depth wait driftValue tail scale steps)
          (parameterGradientOrbit prime depth wait driftValue tail gradient steps) =
        renormalizedTransverseDefect
          (legalPayload prime depth wait tail) scale gradient := by
  intro steps
  induction steps with
  | zero =>
      rfl
  | succ steps induction =>
      rw [parameterGradientOrbit, sensitivityScaleOrbit,
        renormalizedTransverseDefect_step
          prime depth wait driftValue tail
          (sensitivityScaleOrbit prime depth wait driftValue tail scale steps)
          (parameterGradientOrbit prime depth wait driftValue tail gradient steps)
          multiplier_ne
          (sensitivityScaleOrbit_ne_zero prime depth wait driftValue tail scale
            multiplier_ne scale_ne steps),
        induction]

/-- The constant-coefficient integrating factor has the cumulative valuation
`v_p(q₀)-nsa`. -/
theorem sensitivityScaleOrbit_hasValue
    {prime : Nat} [Fact prime.Prime]
    {depth wait : Nat} {driftValue tail scale : ℚ} {scaleValue : ℤ}
    (wait_positive : 0 < wait)
    (drift_unit : IsUnit prime driftValue)
    (tail_unit : IsUnit prime tail)
    (scale_value : HasValue prime scale scaleValue) :
    ∀ steps,
      HasValue prime
        (sensitivityScaleOrbit prime depth wait driftValue tail scale steps)
        (scaleValue - steps * (depth * wait)) := by
  intro steps
  induction steps with
  | zero =>
      simpa [sensitivityScaleOrbit] using scale_value
  | succ steps induction =>
      rw [sensitivityScaleOrbit]
      have stepped :=
        sensitivityScaleStep_hasValue
          (prime := prime) (depth := depth) (wait := wait)
          wait_positive drift_unit tail_unit induction
      convert stepped using 1
      push_cast
      ring

private theorem prime_not_dvd_one_add_pow_sub_pow
    {prime left right : Nat} (prime_prime : prime.Prime)
    (left_positive : 0 < left) (right_positive : 0 < right) :
    ¬(prime : ℤ) ∣
      1 + (prime : ℤ) ^ left - (prime : ℤ) ^ right := by
  intro total_dvd
  have left_dvd : (prime : ℤ) ∣ (prime : ℤ) ^ left :=
    (dvd_refl (prime : ℤ)).pow left_positive.ne'
  have right_dvd : (prime : ℤ) ∣ (prime : ℤ) ^ right :=
    (dvd_refl (prime : ℤ)).pow right_positive.ne'
  have difference_dvd :
      (prime : ℤ) ∣ (prime : ℤ) ^ left - (prime : ℤ) ^ right :=
    left_dvd.sub right_dvd
  have one_dvd : (prime : ℤ) ∣ 1 := by
    convert total_dvd.sub difference_dvd using 1
    ring
  have not_one : ¬(prime : ℤ) ∣ 1 := by
    exact_mod_cast prime_prime.not_dvd_one
  exact not_one one_dvd

private theorem prime_not_dvd_pow_sub_one
    {prime exponent : Nat} (prime_prime : prime.Prime)
    (exponent_positive : 0 < exponent) :
    ¬(prime : ℤ) ∣ (prime : ℤ) ^ exponent - 1 := by
  intro difference_dvd
  have power_dvd : (prime : ℤ) ∣ (prime : ℤ) ^ exponent :=
    (dvd_refl (prime : ℤ)).pow exponent_positive.ne'
  have one_dvd : (prime : ℤ) ∣ 1 := by
    convert power_dvd.sub difference_dvd using 1
    ring
  have not_one : ¬(prime : ℤ) ∣ 1 := by
    exact_mod_cast prime_prime.not_dvd_one
  exact not_one one_dvd

/-- Unit tail prescribing transverse depth `transverseDepth` at the reset gradient. -/
def prescribedTransverseDepthTail
    (prime depth wait transverseDepth : Nat) : ℚ :=
  (1 + (prime : ℚ) ^ transverseDepth -
      (prime : ℚ) ^ (depth * wait)) /
    ((prime : ℚ) ^ wait - 1)

/-- Every positive prescribed transverse depth is realized by a p-adic unit tail. -/
theorem prescribedTransverseDepthTail_isUnit
    {prime : Nat} [Fact prime.Prime]
    {depth wait transverseDepth : Nat}
    (depth_positive : 0 < depth) (wait_positive : 0 < wait)
    (transverseDepth_positive : 0 < transverseDepth) :
    IsUnit prime
      (prescribedTransverseDepthTail prime depth wait transverseDepth) := by
  have depthWait_positive : 0 < depth * wait :=
    Nat.mul_pos depth_positive wait_positive
  have numerator_unit :
      IsUnit prime
        (((1 + (prime : ℤ) ^ transverseDepth -
          (prime : ℤ) ^ (depth * wait) : ℤ) : ℚ)) :=
    intCast_isUnit_of_not_dvd
      (prime_not_dvd_one_add_pow_sub_pow
        (Fact.out : prime.Prime) transverseDepth_positive depthWait_positive)
  have denominator_unit :
      IsUnit prime
        ((((prime : ℤ) ^ wait - 1 : ℤ) : ℚ)) :=
    intCast_isUnit_of_not_dvd
      (prime_not_dvd_pow_sub_one
        (Fact.out : prime.Prime) wait_positive)
  simpa [prescribedTransverseDepthTail] using
    div_hasValue numerator_unit denominator_unit

/-- The prescribed tail makes the legal payload exactly `1+p^N`. -/
theorem legalPayload_prescribedTransverseDepthTail
    {prime : Nat} [Fact prime.Prime]
    (depth wait transverseDepth : Nat) (wait_positive : 0 < wait) :
    legalPayload prime depth wait
        (prescribedTransverseDepthTail prime depth wait transverseDepth) =
      1 + (prime : ℚ) ^ transverseDepth := by
  have denominator_ne :
      (prime : ℚ) ^ wait - 1 ≠ 0 := by
    have power_positive :
        IsPositive prime ((prime : ℚ) ^ wait) := by
      refine ⟨primePower_ne_zero (Fact.out : prime.Prime) wait, ?_⟩
      rw [primePower_valuation]
      exact_mod_cast wait_positive
    exact (positive_sub_one power_positive).1
  simp only [legalPayload, prescribedTransverseDepthTail]
  field_simp [denominator_ne]

/-- Center/reset gradient of the initial reset state. -/
def resetParameterGradient : Fin 2 → ℚ :=
  ![0, 1]

/-- The prescribed family realizes every positive normalized transverse depth exactly. -/
theorem prescribedTransverseDepth_hasValue
    {prime : Nat} [Fact prime.Prime]
    {depth wait transverseDepth : Nat}
    (wait_positive : 0 < wait) :
    HasValue prime
      (renormalizedTransverseDefect
        (legalPayload prime depth wait
          (prescribedTransverseDepthTail prime depth wait transverseDepth))
        1 resetParameterGradient)
      transverseDepth := by
  rw [legalPayload_prescribedTransverseDepthTail
    depth wait transverseDepth wait_positive]
  simpa [renormalizedTransverseDefect, parameterGradientMass,
    resetParameterGradient] using
    primePower_hasValue (prime := prime) transverseDepth

/-- Arbitrarily deep normalized transversality persists through every iterate of its constant
stage.  The integrating factor removes raw growth, but no uniform unit annulus remains. -/
theorem prescribedTransverseDepth_orbit_hasValue
    {prime : Nat} [Fact prime.Prime]
    {depth wait transverseDepth steps : Nat}
    (depth_positive : 0 < depth) (wait_positive : 0 < wait)
    (transverseDepth_positive : 0 < transverseDepth) :
    HasValue prime
      (renormalizedTransverseDefect
        (legalPayload prime depth wait
          (prescribedTransverseDepthTail prime depth wait transverseDepth))
        (sensitivityScaleOrbit prime depth wait 1
          (prescribedTransverseDepthTail prime depth wait transverseDepth)
          1 steps)
        (parameterGradientOrbit prime depth wait 1
          (prescribedTransverseDepthTail prime depth wait transverseDepth)
          resetParameterGradient steps))
      transverseDepth := by
  have tail_unit :=
    prescribedTransverseDepthTail_isUnit
      (prime := prime) (depth := depth) (wait := wait)
      (transverseDepth := transverseDepth)
      depth_positive wait_positive transverseDepth_positive
  have multiplier_ne :
      sensitivityMultiplier prime depth wait 1
          (prescribedTransverseDepthTail prime depth wait transverseDepth) ≠
        0 :=
    (sensitivityMultiplier_hasValue
      (prime := prime) (depth := depth) (wait := wait)
      wait_positive
      (show IsUnit prime (1 : ℚ) from ⟨one_ne_zero, padicValRat.one⟩)
      tail_unit).1
  rw [renormalizedTransverseDefect_orbit
    prime depth wait 1
    (prescribedTransverseDepthTail prime depth wait transverseDepth)
    1 resetParameterGradient multiplier_ne one_ne_zero steps]
  exact prescribedTransverseDepth_hasValue wait_positive

end
end MatrixMortality.ReturnGuard
