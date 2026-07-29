import MatrixMortality.ReturnGuardDynamics

/-!
# Prefix coordinates for the amalgamated valuation guard

The guarded return is a variable-length `p`-adic prefix decoder followed by one fixed
fractional-linear map.  The reciprocal residual on each branch then obeys an affine update.
Polynomial identities are stated before their affine-chart corollaries so that every excluded
pole remains explicit.
-/

namespace MatrixMortality.ReturnGuard

open MatrixMortality.PadicValuation

noncomputable section

/-- Projective coordinate sending the terminal point one to infinity. -/
def shiftCoordinate (z : ℚ) : ℚ :=
  z / (z - 1)

/-- Variable-length affine prefix decoder in the shifted coordinate. -/
def prefixDecode (parameters : Parameters) (wait : Nat) (x : ℚ) : ℚ :=
  (parameters.prime ^ wait +
      (1 - parameters.prime ^ wait) * x) /
    parameters.prime ^ (parameters.depth * wait)

/-- Fixed fractional-linear map applied after every decoded prefix. -/
def centerTransform (parameters : Parameters) (residual : ℚ) : ℚ :=
  (parameters.center * residual +
      drift parameters.center parameters.reset) /
    ((parameters.center - 1) * residual +
      drift parameters.center parameters.reset)

/-- Prefix decoder transported through the fixed center map. -/
def residualStep (parameters : Parameters) (wait : Nat) (residual : ℚ) : ℚ :=
  prefixDecode parameters wait (centerTransform parameters residual)

/-- Unit cylinder whose decoded numerator has depth `depth * wait`. -/
def branchCylinder
    (parameters : Parameters) (wait : Nat) (residual : ℚ) : ℚ :=
  (parameters.prime ^ (parameters.depth * wait) * residual -
      drift parameters.center parameters.reset) /
    (parameters.center - parameters.prime ^ wait)

/-- Reciprocal-residual multiplier on one decoded branch. -/
def residualSlope (parameters : Parameters) (wait : Nat) : ℚ :=
  drift parameters.center parameters.reset *
      (1 - parameters.prime ^ wait) /
    (parameters.center - parameters.prime ^ wait)

/-- Reciprocal-residual translation on one decoded branch. -/
def residualIntercept (parameters : Parameters) (wait : Nat) : ℚ :=
  (parameters.center - 1) *
      parameters.prime ^ (parameters.depth * wait) /
    (parameters.center - parameters.prime ^ wait)

/-- The decoder numerator before division by its `p^(depth * wait)` scale. -/
def prefixNumerator (parameters : Parameters) (wait : Nat) (z : ℚ) : ℚ :=
  z - parameters.prime ^ wait

/-- The decoder denominator in the shifted affine chart. -/
def prefixDenominator (parameters : Parameters) (wait : Nat) (z : ℚ) : ℚ :=
  parameters.prime ^ (parameters.depth * wait) * (z - 1)

/-- The guard numerator is the fixed center map applied to the raw decoded pair. -/
theorem projectiveNumerator_eq_prefixTransform
    (parameters : Parameters) (wait : Nat) (z : ℚ) :
    projectiveNumerator parameters.prime parameters.depth
        parameters.center parameters.reset wait z =
      parameters.center * prefixNumerator parameters wait z +
        drift parameters.center parameters.reset *
          prefixDenominator parameters wait z := by
  simp [projectiveNumerator, prefixNumerator, prefixDenominator]
  ring

/-- Subtracting the guard denominator yields the shifted output denominator. -/
theorem projectiveNumerator_sub_denominator_eq_prefixTransform
    (parameters : Parameters) (wait : Nat) (z : ℚ) :
    projectiveNumerator parameters.prime parameters.depth
          parameters.center parameters.reset wait z -
        projectiveDenominator parameters.prime wait z =
      (parameters.center - 1) * prefixNumerator parameters wait z +
        drift parameters.center parameters.reset *
          prefixDenominator parameters wait z := by
  simp [projectiveNumerator, projectiveDenominator, prefixNumerator,
    prefixDenominator]
  ring

/-- In the shifted chart, prefix decoding is the raw pole defect divided by its carry scale. -/
theorem prefixDecode_shiftCoordinate
    (parameters : Parameters) (wait : Nat) (z : ℚ) (not_target : z ≠ 1) :
    prefixDecode parameters wait (shiftCoordinate z) =
      prefixNumerator parameters wait z /
        prefixDenominator parameters wait z := by
  have target_defect_ne : z - 1 ≠ 0 := sub_ne_zero.mpr not_target
  have scale_ne :
      (parameters.prime : ℚ) ^ (parameters.depth * wait) ≠ 0 :=
    primePower_ne_zero parameters.prime_prime _
  simp [prefixDecode, shiftCoordinate, prefixNumerator, prefixDenominator]
  field_simp [target_defect_ne, scale_ne]
  ring

/-- The reset is the fixed center map applied to the unit residual. -/
theorem shiftCoordinate_reset_eq_centerTransform_one (parameters : Parameters) :
    shiftCoordinate parameters.reset = centerTransform parameters 1 := by
  simp [shiftCoordinate, centerTransform, drift]

/-- A positive wait power cannot equal the unit center. -/
theorem center_sub_primePower_ne_zero
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait) :
    parameters.center - parameters.prime ^ wait ≠ 0 := by
  apply sub_ne_zero.mpr
  exact ne_of_valuation_ne (by
    rw [parameters.center_unit.2, primePower_valuation]
    exact ne_of_lt (by exact_mod_cast wait_positive))

/-- The fixed Möbius denominator is the shifted guard denominator in decoded coordinates. -/
theorem centerTransform_denominator_prefixDecode
    (parameters : Parameters) (wait : Nat) (z : ℚ) (not_target : z ≠ 1) :
    ((parameters.center - 1) *
          prefixDecode parameters wait (shiftCoordinate z) +
        drift parameters.center parameters.reset) *
        prefixDenominator parameters wait z =
      projectiveNumerator parameters.prime parameters.depth
          parameters.center parameters.reset wait z -
        projectiveDenominator parameters.prime wait z := by
  rw [prefixDecode_shiftCoordinate parameters wait z not_target]
  have denominator_ne :
      prefixDenominator parameters wait z ≠ 0 := by
    apply mul_ne_zero
    · exact primePower_ne_zero parameters.prime_prime _
    · exact sub_ne_zero.mpr not_target
  field_simp [denominator_ne]
  exact
    (projectiveNumerator_sub_denominator_eq_prefixTransform
      parameters wait z).symm

/-- One nonterminal-input, non-pole guard step is prefix decoding followed by the fixed
fractional-linear formula. Lean's total division makes the equality valid when the output is
the terminal point as well. -/
theorem shift_step
    (parameters : Parameters) (wait : Nat) (z : ℚ)
    (not_target : z ≠ 1)
    (not_pole : z ≠ parameters.prime ^ wait) :
    shiftCoordinate (parameters.center + guardDefect parameters wait z) =
      centerTransform parameters
        (prefixDecode parameters wait (shiftCoordinate z)) := by
  have target_defect_ne : z - 1 ≠ 0 := sub_ne_zero.mpr not_target
  have pole_defect_ne :
      z - parameters.prime ^ wait ≠ 0 := sub_ne_zero.mpr not_pole
  have scale_ne :
      (parameters.prime : ℚ) ^ (parameters.depth * wait) ≠ 0 :=
    primePower_ne_zero parameters.prime_prime _
  simp [shiftCoordinate, centerTransform, prefixDecode, guardDefect,
    prefixDenominator, prefixNumerator, drift]
  field_simp [target_defect_ne, pole_defect_ne, scale_ne]
  ring

/-- Readiness is exactly unit membership after decoding the selected shifted prefix. -/
theorem ready_iff_prefixDecode_isUnit
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait)
    (z : ℚ) (z_positive : IsPositive parameters.prime z)
    (wait_matches : padicValRat parameters.prime z = wait) :
    Ready parameters wait z ↔
      IsUnit parameters.prime
        (prefixDecode parameters wait (shiftCoordinate z)) := by
  have not_target : z ≠ 1 :=
    ne_of_valuation_ne (by
      rw [wait_matches, padicValRat.one]
      exact ne_of_gt (by exact_mod_cast wait_positive))
  have target_defect_unit := positive_sub_one z_positive
  have denominator_value :
      HasValue parameters.prime (prefixDenominator parameters wait z)
        (parameters.depth * wait) := by
    simpa [prefixDenominator] using
      mul_hasValue (primePower_hasValue (parameters.depth * wait))
        target_defect_unit
  rw [prefixDecode_shiftCoordinate parameters wait z not_target]
  constructor
  · intro ready
    have numerator_ne :
        prefixNumerator parameters wait z ≠ 0 := by
      intro numerator_zero
      have impossible := ready.2.2
      rw [prefixNumerator] at numerator_zero
      rw [numerator_zero, padicValRat.zero] at impossible
      have scaled_positive : 0 < parameters.depth * wait :=
        Nat.mul_pos parameters.depth_positive wait_positive
      omega
    have numerator_value :
        HasValue parameters.prime (prefixNumerator parameters wait z)
          (parameters.depth * wait) :=
      ⟨numerator_ne, by simpa [prefixNumerator] using ready.2.2⟩
    simpa using div_hasValue numerator_value denominator_value
  · intro decoded_unit
    have reconstructed :
        prefixNumerator parameters wait z =
          (prefixNumerator parameters wait z /
              prefixDenominator parameters wait z) *
            prefixDenominator parameters wait z := by
      field_simp [denominator_value.1]
    have numerator_value :
        HasValue parameters.prime (prefixNumerator parameters wait z)
          (parameters.depth * wait) := by
      rw [reconstructed]
      simpa using mul_hasValue decoded_unit denominator_value
    exact ⟨wait_positive, wait_matches, by
      simpa [prefixNumerator] using numerator_value.2⟩

/-- The transported branch has the displayed fractional-linear residual update. -/
theorem residualStep_eq
    (parameters : Parameters) (wait : Nat) (residual : ℚ)
    (transform_denominator_ne :
      (parameters.center - 1) * residual +
        drift parameters.center parameters.reset ≠ 0) :
    residualStep parameters wait residual =
      ((parameters.center - parameters.prime ^ wait) * residual +
          drift parameters.center parameters.reset) /
        (parameters.prime ^ (parameters.depth * wait) *
          ((parameters.center - 1) * residual +
            drift parameters.center parameters.reset)) := by
  have scale_ne :
      (parameters.prime : ℚ) ^ (parameters.depth * wait) ≠ 0 :=
    primePower_ne_zero parameters.prime_prime _
  simp [residualStep, prefixDecode, centerTransform]
  field_simp [transform_denominator_ne, scale_ne]
  ring

/-- One branch cylinder cancels the variable numerator of the residual map. -/
theorem residualStep_branchCylinder
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait)
    (residual : ℚ)
    (transform_denominator_ne :
      (parameters.center - 1) *
          branchCylinder parameters wait residual +
        drift parameters.center parameters.reset ≠ 0) :
    residualStep parameters wait (branchCylinder parameters wait residual) =
      residual /
        ((parameters.center - 1) *
            branchCylinder parameters wait residual +
          drift parameters.center parameters.reset) := by
  rw [residualStep_eq parameters wait _ transform_denominator_ne]
  have branch_denominator_ne :=
    center_sub_primePower_ne_zero parameters wait wait_positive
  have scale_ne :
      (parameters.prime : ℚ) ^ (parameters.depth * wait) ≠ 0 :=
    primePower_ne_zero parameters.prime_prime _
  have numerator_eq :
      (parameters.center - parameters.prime ^ wait) *
          branchCylinder parameters wait residual +
        drift parameters.center parameters.reset =
      parameters.prime ^ (parameters.depth * wait) * residual := by
    simp [branchCylinder]
    field_simp [branch_denominator_ne]
  rw [numerator_eq]
  field_simp [scale_ne, transform_denominator_ne]
  ring

/-- After stripping one branch prefix, the reciprocal residual is updated affinely. -/
theorem reciprocalResidual_affine
    (parameters : Parameters) (wait : Nat) (wait_positive : 0 < wait)
    (residual : ℚ) (residual_ne : residual ≠ 0)
    (transform_denominator_ne :
      (parameters.center - 1) *
          branchCylinder parameters wait residual +
        drift parameters.center parameters.reset ≠ 0) :
    (residualStep parameters wait
        (branchCylinder parameters wait residual))⁻¹ =
      residualSlope parameters wait / residual +
        residualIntercept parameters wait := by
  rw [residualStep_branchCylinder parameters wait wait_positive residual
    transform_denominator_ne]
  have branch_denominator_ne :=
    center_sub_primePower_ne_zero parameters wait wait_positive
  simp [branchCylinder, residualSlope, residualIntercept]
  field_simp [branch_denominator_ne, residual_ne, transform_denominator_ne]
  ring

end
end MatrixMortality.ReturnGuard
