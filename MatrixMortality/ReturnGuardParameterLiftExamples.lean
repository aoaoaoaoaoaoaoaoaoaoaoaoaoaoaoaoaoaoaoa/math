import MatrixMortality.ReturnGuardParameterLift

/-!
# Canonical collision-prefix synthesis

One fixed rational guard has five consecutive legal steps carrying novel cyclotomic
cancellation.  The fifth collision is obtained by simultaneous `3`-adic prefix preservation
and a modulo-thirteen moving-kernel condition; it strictly extends the four-step ladder in
`ReturnGuardTangentExamples`.
-/

namespace MatrixMortality.ReturnGuard.Examples

open MatrixMortality.PadicValuation

noncomputable section

/-- Parameters of a five-step canonical novel-collision ladder. -/
def fiveCollisionParameters : Parameters where
  prime := 3
  prime_prime := by norm_num
  depth := 2
  depth_two := by norm_num
  center := 23278364
  reset := 52569
  center_unit := intCast_isUnit_of_not_dvd (by norm_num)
  center_sub_one_unit := by
    norm_num
    exact intCast_isUnit_of_not_dvd (by norm_num)
  reset_positive := by
    have reset_value :
        HasValue 3 (52569 : ℚ) 4 := by
      rw [show (52569 : ℚ) =
        (3 : ℚ) ^ 4 * (649 : ℚ) / (1 : ℚ) by norm_num]
      exact
        primePower_mul_int_div_int_hasValue 4
          (by norm_num) (by norm_num)
    exact ⟨reset_value.1, by rw [reset_value.2]; norm_num⟩

private theorem fiveCollision_ready_zero :
    Ready fiveCollisionParameters 4 52569 := by
  have state_value :
      HasValue 3 (52569 : ℚ) 4 := by
    rw [show (52569 : ℚ) =
      (3 : ℚ) ^ 4 * (649 : ℚ) / (1 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 4
        (by norm_num) (by norm_num)
  have defect_value :
      HasValue 3 ((52569 : ℚ) - 3 ^ 4) 8 := by
    rw [show (52569 : ℚ) - 3 ^ 4 =
      (3 : ℚ) ^ 8 * (8 : ℚ) / (1 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 8
        (by norm_num) (by norm_num)
  exact ⟨by norm_num, state_value.2, defect_value.2⟩

private theorem fiveCollision_ready_one :
    Ready fiveCollisionParameters 2 (-152593420581) := by
  have state_value :
      HasValue 3 (-152593420581 : ℚ) 2 := by
    rw [show (-152593420581 : ℚ) =
      (3 : ℚ) ^ 2 * (-16954824509 : ℚ) / (1 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 2
        (by norm_num) (by norm_num)
  have defect_value :
      HasValue 3 ((-152593420581 : ℚ) - 3 ^ 2) 4 := by
    rw [show (-152593420581 : ℚ) - 3 ^ 2 =
      (3 : ℚ) ^ 4 * (-1883869390 : ℚ) / (1 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 4
        (by norm_num) (by norm_num)
  exact ⟨by norm_num, state_value.2, defect_value.2⟩

private theorem fiveCollision_ready_two :
    Ready fiveCollisionParameters 2
      (-350025010739743473 / 188386939) := by
  have state_value :
      HasValue 3 (-350025010739743473 / 188386939 : ℚ) 2 := by
    rw [show (-350025010739743473 / 188386939 : ℚ) =
      (3 : ℚ) ^ 2 * (-38891667859971497 : ℚ) /
        (188386939 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 2
        (by norm_num) (by norm_num)
  have defect_value :
      HasValue 3
        ((-350025010739743473 / 188386939 : ℚ) - 3 ^ 2) 4 := by
    rw [show (-350025010739743473 / 188386939 : ℚ) - 3 ^ 2 =
      (3 : ℚ) ^ 4 * (-4321296449817604 : ℚ) /
        (188386939 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 4
        (by norm_num) (by norm_num)
  exact ⟨by norm_num, state_value.2, defect_value.2⟩

private theorem fiveCollision_ready_three :
    Ready fiveCollisionParameters 1
      (-2007254109244688690714421 / 1080324112454401) := by
  have state_value :
      HasValue 3
        (-2007254109244688690714421 / 1080324112454401 : ℚ) 1 := by
    rw [show
      (-2007254109244688690714421 / 1080324112454401 : ℚ) =
        (3 : ℚ) ^ 1 * (-669084703081562896904807 : ℚ) /
          (1080324112454401 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 1
        (by norm_num) (by norm_num)
  have defect_value :
      HasValue 3
        ((-2007254109244688690714421 / 1080324112454401 : ℚ) -
          3) 2 := by
    rw [show
      (-2007254109244688690714421 / 1080324112454401 : ℚ) - 3 =
        (3 : ℚ) ^ 2 * (-223028234720629003119736 : ℚ) /
          (1080324112454401 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 2
        (by norm_num) (by norm_num)
  exact ⟨by norm_num, state_value.2, defect_value.2⟩

private theorem fiveCollision_ready_four :
    Ready fiveCollisionParameters 3
      (-20714170024605945247598029985793 /
        111514117360314501559868) := by
  have state_value :
      HasValue 3
        (-20714170024605945247598029985793 /
          111514117360314501559868 : ℚ) 3 := by
    rw [show
      (-20714170024605945247598029985793 /
          111514117360314501559868 : ℚ) =
        (3 : ℚ) ^ 3 * (-767191482392812786948075184659 : ℚ) /
          (111514117360314501559868 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 3
        (by norm_num) (by norm_num)
  have defect_value :
      HasValue 3
        ((-20714170024605945247598029985793 /
          111514117360314501559868 : ℚ) - 3 ^ 3) 6 := by
    rw [show
      (-20714170024605945247598029985793 /
          111514117360314501559868 : ℚ) - 3 ^ 3 =
        (3 : ℚ) ^ 6 * (-28414503478034449898613953501 : ℚ) /
          (111514117360314501559868 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 6
        (by norm_num) (by norm_num)
  exact ⟨by norm_num, state_value.2, defect_value.2⟩

/-- The canonical residual orbit begins with the legal wait word `4,2,2,1,3`. -/
theorem fiveCollision_decodedSteps :
    DecodedStep fiveCollisionParameters 1 (1 / 6571) ∧
      DecodedStep fiveCollisionParameters
        (1 / 6571) (941934695 / 76296710291) ∧
      DecodedStep fiveCollisionParameters
        (941934695 / 76296710291)
          (1080324112454401 / 87506252732032603) ∧
      DecodedStep fiveCollisionParameters
        (1080324112454401 / 87506252732032603)
          (111514117360314501559868 / 1003627055162506401584411) ∧
      DecodedStep fiveCollisionParameters
        (111514117360314501559868 / 1003627055162506401584411)
          (2185731036771880761431842577 /
            1593397702778466354454810118897) := by
  constructor
  · refine ⟨4, ?_, ?_⟩
    · rw [residualBranch_iff_ready]
      convert fiveCollision_ready_zero using 1
    · norm_num [residualStep, prefixDecode, centerTransform,
        fiveCollisionParameters, drift]
  constructor
  · refine ⟨2, ?_, ?_⟩
    · rw [residualBranch_iff_ready]
      convert fiveCollision_ready_one using 1
    · norm_num [residualStep, prefixDecode, centerTransform,
        fiveCollisionParameters, drift]
  constructor
  · refine ⟨2, ?_, ?_⟩
    · rw [residualBranch_iff_ready]
      convert fiveCollision_ready_two using 1
    · norm_num [residualStep, prefixDecode, centerTransform,
        fiveCollisionParameters, drift]
  constructor
  · refine ⟨1, ?_, ?_⟩
    · rw [residualBranch_iff_ready]
      convert fiveCollision_ready_three using 1
    · norm_num [residualStep, prefixDecode, centerTransform,
        fiveCollisionParameters, drift]
  · refine ⟨3, ?_, ?_⟩
    · rw [residualBranch_iff_ready]
      convert fiveCollision_ready_four using 1
    · norm_num [residualStep, prefixDecode, centerTransform,
        fiveCollisionParameters, drift]

/-- Primitive integral lift of the five canonical steps, with common factors
`8,2,20,2,13`. -/
theorem fiveCollision_primitiveSteps :
    PrimitiveIntegralStep 3 2 23278364 (-23225795) 1
        (1, 1) (1, 6571) ∧
      PrimitiveIntegralStep 3 2 23278364 (-23225795) 1
        (1, 6571) (941934695, 76296710291) ∧
      PrimitiveIntegralStep 3 2 23278364 (-23225795) 1
        (941934695, 76296710291)
          (1080324112454401, 87506252732032603) ∧
      PrimitiveIntegralStep 3 2 23278364 (-23225795) 1
        (1080324112454401, 87506252732032603)
          (111514117360314501559868, 1003627055162506401584411) ∧
      PrimitiveIntegralStep 3 2 23278364 (-23225795) 1
        (111514117360314501559868, 1003627055162506401584411)
          (2185731036771880761431842577,
            1593397702778466354454810118897) := by
  constructor
  · simpa [prescribedResetDrift, prescribedResetTargetDenominator] using
      prescribedReset_primitiveIntegralStep 3 2 4 23278364 8 10
        (by norm_num)
  constructor
  · refine ⟨by norm_num, by norm_num, 2, -1883869390,
      -152593420582, -2, ?_, by norm_num, by norm_num⟩
    norm_num [IntegralStep, integralStepNumerator, terminalDefect]
  constructor
  · refine ⟨by norm_num, by norm_num, 2, -21606482249088020,
      -1750125054640652060, -20, ?_, by norm_num, by norm_num⟩
    norm_num [IntegralStep, integralStepNumerator, terminalDefect]
  constructor
  · refine ⟨by norm_num, by norm_num, 1, -223028234720629003119736,
      -2007254110325012803168822, -2, ?_, by norm_num, by norm_num⟩
    norm_num [IntegralStep, integralStepNumerator, terminalDefect]
  · refine ⟨by norm_num, by norm_num, 3,
      -28414503478034449898613953501,
      -20714170136120062607912531545661, -13, ?_, by norm_num,
      by norm_num⟩
    norm_num [IntegralStep, integralStepNumerator, terminalDefect]

/-- Removing fixed support from `8,2,20,2,13` leaves the five nontrivial factors
`8,2,4,2,13`. -/
theorem fiveCollision_novelFactors :
    IsCoprime (8 : ℤ) ((-23225795) * 3) ∧
      IsCoprime (2 : ℤ) ((-23225795) * 3) ∧
      (20 : ℤ) = 5 * 4 ∧
      (5 : ℤ) ∣ (-23225795) ∧
      IsCoprime (4 : ℤ) ((-23225795) * 3) ∧
      IsCoprime (2 : ℤ) ((-23225795) * 3) ∧
      IsCoprime (13 : ℤ) ((-23225795) * 3) := by
  norm_num

end
end MatrixMortality.ReturnGuard.Examples
