import MatrixMortality.ReturnGuardAntiHenselExamples
import MatrixMortality.ReturnGuardParameterPlane

/-!
# Two-parameter escape from a dead center cylinder

At center `998`, the fixed-reset cylinder of `ReturnGuardAntiHenselExamples` admits waits
`1, 3` and no third decoded step.  Changing only the reset by `3^8` preserves those waits and
creates a legal third wait `1`.

This is an exact guard-level witness that the anti-Hensel obstruction is one-dimensional.
The second arithmetic parameter is not redundant: at its correct anisotropic precision it
restores a direction transverse to the dead center lift.
-/

namespace MatrixMortality.ReturnGuard.Examples

open MatrixMortality.PadicValuation

noncomputable section

/-- Parameters obtained from the dead center `d=2` by moving the reset by `3^8`. -/
def resetEscapeParameters : Parameters where
  prime := 3
  prime_prime := by norm_num
  depth := 2
  depth_two := by norm_num
  center := 998
  reset := 6393
  center_unit := intCast_isUnit_of_not_dvd (by norm_num)
  center_sub_one_unit := by
    norm_num
    exact intCast_isUnit_of_not_dvd (by norm_num)
  reset_positive := by
    have reset_value :
        HasValue 3 (6393 : ℚ) 1 := by
      rw [show (6393 : ℚ) =
        (3 : ℚ) ^ 1 * (2131 : ℚ) / (1 : ℚ) by norm_num]
      exact
        primePower_mul_int_div_int_hasValue 1
          (by norm_num) (by norm_num)
    exact ⟨reset_value.1, by rw [reset_value.2]; norm_num⟩

private theorem resetEscape_ready_zero :
    Ready resetEscapeParameters 1 6393 := by
  have state_value :
      HasValue 3 (6393 : ℚ) 1 := by
    rw [show (6393 : ℚ) =
      (3 : ℚ) ^ 1 * (2131 : ℚ) / (1 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 1
        (by norm_num) (by norm_num)
  have defect_value :
      HasValue 3 ((6393 : ℚ) - 3) 2 := by
    rw [show (6393 : ℚ) - 3 =
      (3 : ℚ) ^ 2 * (710 : ℚ) / (1 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 2
        (by norm_num) (by norm_num)
  exact ⟨by norm_num, state_value.2, defect_value.2⟩

private theorem resetEscape_ready_one :
    Ready resetEscapeParameters 3 (3519342 / 71) := by
  have state_value :
      HasValue 3 (3519342 / 71 : ℚ) 3 := by
    rw [show (3519342 / 71 : ℚ) =
      (3 : ℚ) ^ 3 * (130346 : ℚ) / (71 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 3
        (by norm_num) (by norm_num)
  have defect_value :
      HasValue 3 ((3519342 / 71 : ℚ) - 3 ^ 3) 6 := by
    rw [show (3519342 / 71 : ℚ) - 3 ^ 3 =
      (3 : ℚ) ^ 6 * (4825 : ℚ) / (71 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 6
        (by norm_num) (by norm_num)
  exact ⟨by norm_num, state_value.2, defect_value.2⟩

private theorem resetEscape_ready_two :
    Ready resetEscapeParameters 1 (3798256479 / 965) := by
  have state_value :
      HasValue 3 (3798256479 / 965 : ℚ) 1 := by
    rw [show (3798256479 / 965 : ℚ) =
      (3 : ℚ) ^ 1 * (1266085493 : ℚ) / (965 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 1
        (by norm_num) (by norm_num)
  have defect_value :
      HasValue 3 ((3798256479 / 965 : ℚ) - 3) 2 := by
    rw [show (3798256479 / 965 : ℚ) - 3 =
      (3 : ℚ) ^ 2 * (422028176 : ℚ) / (965 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 2
        (by norm_num) (by norm_num)
  exact ⟨by norm_num, state_value.2, defect_value.2⟩

/-- The reset perturbation creates the legal wait prefix `1, 3, 1`. -/
theorem resetEscape_threeStepPrefix :
    DecodedStep resetEscapeParameters 1 (355 / 3196) ∧
      DecodedStep resetEscapeParameters
        (355 / 3196) (4825 / 3519271) ∧
      DecodedStep resetEscapeParameters
        (4825 / 3519271) (211014088 / 1899127757) := by
  constructor
  · refine ⟨1, ?_, ?_⟩
    · rw [residualBranch_iff_ready]
      convert resetEscape_ready_zero using 1
    · norm_num [residualStep, prefixDecode, centerTransform,
        resetEscapeParameters, drift]
  constructor
  · refine ⟨3, ?_, ?_⟩
    · rw [residualBranch_iff_ready]
      convert resetEscape_ready_one using 1
    · norm_num [residualStep, prefixDecode, centerTransform,
        resetEscapeParameters, drift]
  · refine ⟨1, ?_, ?_⟩
    · rw [residualBranch_iff_ready]
      convert resetEscape_ready_two using 1
    · norm_num [residualStep, prefixDecode, centerTransform,
        resetEscapeParameters, drift]

/-- The escape uses the same center as the dead fixed-reset cylinder and moves only reset by
`3^8`. -/
theorem resetEscape_parameter_relation :
    resetEscapeParameters.center = (deadLiftParameters 2).center ∧
      resetEscapeParameters.reset =
        (deadLiftParameters 2).reset + 3 ^ 8 := by
  norm_num [resetEscapeParameters, deadLiftParameters]

/-- Reset motion strictly enlarges the legal prefix available at the same center. -/
theorem resetEscape_strictly_extends_deadCenter :
    (¬∃ target,
        DecodedStep (deadLiftParameters 2)
          (deadLiftResidualTwo 2) target) ∧
      DecodedStep resetEscapeParameters
        (4825 / 3519271) (211014088 / 1899127757) :=
  ⟨deadLift_noThirdStep 2, resetEscape_threeStepPrefix.2.2⟩

end
end MatrixMortality.ReturnGuard.Examples
