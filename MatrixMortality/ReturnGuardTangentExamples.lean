import MatrixMortality.ReturnGuardExamples
import MatrixMortality.ReturnGuardTangentBudget

/-!
# Tangent-cocycle examples

The checked rational period-three guard also closes projectively after cancellation blow-up.
This is a canonical-reset orbit, not an arbitrary tangent input.  Consequently no scalar height
which strictly descends on every tangent step can decide the guard before fixed parameter-prime
cancellation has been separated.
-/

namespace MatrixMortality.ReturnGuard.Examples

open MatrixMortality.PadicValuation
open scoped Matrix

noncomputable section

/-- Tangent coordinates after the wait-one leg of the rational three-cycle. -/
def cycleTangentZero : Fin 2 → ℤ :=
  cancellationTangent (3 ^ (2 * 1) : ℤ) 5 17

/-- Tangent coordinates after the wait-two leg of the rational three-cycle. -/
def cycleTangentOne : Fin 2 → ℤ :=
  cancellationTangent (3 ^ (2 * 2) : ℤ) 43 283

/-- Tangent coordinates after the wait-three leg of the rational three-cycle. -/
def cycleTangentTwo : Fin 2 → ℤ :=
  cancellationTangent (3 ^ (2 * 3) : ℤ) 1 1

theorem cycleTangentZero_eq :
    cycleTangentZero = ![17, 28] := by
  norm_num [cycleTangentZero, cancellationTangent]

theorem cycleTangentOne_eq :
    cycleTangentOne = ![283, 3200] := by
  norm_num [cycleTangentOne, cancellationTangent]

theorem cycleTangentTwo_eq :
    cycleTangentTwo = ![1, 728] := by
  norm_num [cycleTangentTwo, cancellationTangent]

/-- The first tangent leg removes the primitive-reduction scalar `−28`, in addition to the
preceding depth power `9`. -/
theorem cycle_tangent_step_zero :
    tangentTransfer (-953 : ℤ) 473 2240 9 9 *ᵥ cycleTangentZero =
      (-252 : ℤ) • cycleTangentOne := by
  ext i
  fin_cases i <;>
    norm_num [cycleTangentZero, cycleTangentOne, cancellationTangent,
      tangentTransfer, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]

/-- The second tangent leg removes `81 · (−3440)`. -/
theorem cycle_tangent_step_one :
    tangentTransfer (-953 : ℤ) 473 2240 81 27 *ᵥ cycleTangentOne =
      (-278640 : ℤ) • cycleTangentTwo := by
  ext i
  fin_cases i <;>
    norm_num [cycleTangentOne, cycleTangentTwo, cancellationTangent,
      tangentTransfer, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]

/-- The third tangent leg removes `729 · (−160)` and closes the projective tangent cycle. -/
theorem cycle_tangent_step_two :
    tangentTransfer (-953 : ℤ) 473 2240 729 3 *ᵥ cycleTangentTwo =
      (-116640 : ℤ) • cycleTangentZero := by
  ext i
  fin_cases i <;>
    norm_num [cycleTangentTwo, cycleTangentZero, cancellationTangent,
      tangentTransfer, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]

/-- All three tangent normalization scalars are nonzero, so the displayed identities form a
genuine projective three-cycle rather than an annihilating orbit. -/
theorem cycle_tangent_scalars_nonzero :
    (-252 : ℤ) ≠ 0 ∧ (-278640 : ℤ) ≠ 0 ∧ (-116640 : ℤ) ≠ 0 := by
  norm_num

/-- The canonical residual source for the two-stage novel-cancellation example. -/
def nestedNovelTangentZero : Fin 2 → ℤ :=
  cancellationTangent (3 ^ (2 * 4) : ℤ) 1 1

/-- Tangent after the reset step swallows the cyclotomic divisor `20 ∣ 3⁴ - 1`. -/
def nestedNovelTangentOne : Fin 2 → ℤ :=
  cancellationTangent (3 ^ (2 * 4) : ℤ) 1 6565

/-- Tangent after the next canonical step swallows the new cyclotomic divisor `2 ∣ 3 - 1`. -/
def nestedNovelTangentTwo : Fin 2 → ℤ :=
  cancellationTangent (3 ^ (2 * 1) : ℤ) 47887663 430988968

/-- The first canonical step removes exactly `20` from its raw integral output. -/
theorem nestedNovel_primitiveStep_zero :
    PrimitiveIntegralStep 3 2 2 131299 1
      (1, 1) (1, 6565) :=
  prescribedReset_primitiveIntegralStep 3 2 4 2 20 4 (by norm_num)

/-- The second canonical step removes exactly `2`. -/
theorem nestedNovel_primitiveStep_one :
    PrimitiveIntegralStep 3 2 2 131299 1
      (1, 6565) (47887663, 430988968) := by
  refine ⟨by norm_num, by norm_num, 1, 95775326, 861977936, 2,
    ?_, by norm_num, by norm_num⟩
  norm_num [IntegralStep, integralStepNumerator, terminalDefect]

/-- Both removed factors are coprime to the fixed determinant support `D L p`. -/
theorem nestedNovel_factors_coprime_fixedSupport :
    IsCoprime (20 : ℤ) (131299 * 3) ∧
      IsCoprime (2 : ℤ) (131299 * 3) := by
  norm_num

/-- Guard parameters realizing both novel cancellations on the canonical orbit from residual
one. -/
def nestedNovelParameters : Parameters where
  prime := 3
  prime_prime := by norm_num
  depth := 2
  depth_two := by norm_num
  center := 2
  reset := 131301
  center_unit := intCast_isUnit_of_not_dvd (by norm_num)
  center_sub_one_unit := by
    norm_num
    exact intCast_isUnit_of_not_dvd (by norm_num)
  reset_positive := by
    have reset_value :
        HasValue 3 (131301 : ℚ) 4 := by
      rw [show (131301 : ℚ) = (3 : ℚ) ^ 4 * 1621 by norm_num]
      exact
        mul_hasValue (primePower_hasValue 4)
          (intCast_isUnit_of_not_dvd (by norm_num))
    exact ⟨reset_value.1, by rw [reset_value.2]; norm_num⟩

/-- The separator reset lies in the wait-four ready cylinder. -/
theorem nestedNovel_reset_ready :
    Ready nestedNovelParameters 4 131301 := by
  have reset_value :
      HasValue 3 (131301 : ℚ) 4 := by
    rw [show (131301 : ℚ) = (3 : ℚ) ^ 4 * 1621 by norm_num]
    exact
      mul_hasValue (primePower_hasValue 4)
        (intCast_isUnit_of_not_dvd (by norm_num))
  have defect_value :
      HasValue 3 ((131301 : ℚ) - 3 ^ 4) 8 := by
    rw [show (131301 : ℚ) - 3 ^ 4 = (3 : ℚ) ^ 8 * 20 by norm_num]
    exact
      mul_hasValue (primePower_hasValue 8)
        (intCast_isUnit_of_not_dvd (by norm_num))
  exact ⟨by norm_num, reset_value.2, defect_value.2⟩

/-- First canonical decoded step, from residual one through the prescribed reset collision. -/
theorem nestedNovel_decodedStep_zero :
    DecodedStep nestedNovelParameters 1 (1 / 6565) := by
  refine ⟨4, ?_, ?_⟩
  · rw [residualBranch_iff_ready]
    simpa [stateOfResidual, nestedNovelParameters, drift] using
      nestedNovel_reset_ready
  · norm_num [residualStep, prefixDecode, centerTransform,
      nestedNovelParameters, drift]

/-- The state represented by residual `1/6565` lies in the wait-one ready cylinder. -/
theorem nestedNovel_state_one_ready :
    Ready nestedNovelParameters 1 861977937 := by
  have state_value :
      HasValue 3 (861977937 : ℚ) 1 := by
    rw [show (861977937 : ℚ) = 3 * 287325979 by norm_num]
    exact
      mul_hasValue (primePower_hasValue 1)
        (intCast_isUnit_of_not_dvd (by norm_num))
  have defect_value :
      HasValue 3 ((861977937 : ℚ) - 3) 2 := by
    rw [show (861977937 : ℚ) - 3 = (3 : ℚ) ^ 2 * 95775326 by norm_num]
    exact
      mul_hasValue (primePower_hasValue 2)
        (intCast_isUnit_of_not_dvd (by norm_num))
  exact ⟨by norm_num, state_value.2, defect_value.2⟩

/-- Second canonical decoded step swallows the independent factor two. -/
theorem nestedNovel_decodedStep_one :
    DecodedStep nestedNovelParameters (1 / 6565)
      (47887663 / 430988968) := by
  refine ⟨1, ?_, ?_⟩
  · rw [residualBranch_iff_ready]
    convert nestedNovel_state_one_ready using 1
  · norm_num [residualStep, prefixDecode, centerTransform,
      nestedNovelParameters, drift]

theorem nestedNovelTangentZero_eq :
    nestedNovelTangentZero = ![1, 6560] := by
  norm_num [nestedNovelTangentZero, cancellationTangent]

theorem nestedNovelTangentOne_eq :
    nestedNovelTangentOne = ![6565, -4] := by
  norm_num [nestedNovelTangentOne, cancellationTangent]

theorem nestedNovelTangentTwo_eq :
    nestedNovelTangentTwo = ![430988968, -1] := by
  norm_num [nestedNovelTangentTwo, cancellationTangent]

/-- First exact tangent leg, including the forced chart power and primitive factor `20`. -/
theorem nestedNovel_tangentStep_zero :
    tangentTransfer (2 : ℤ) 131299 1 6561 81 *ᵥ
        nestedNovelTangentZero =
      131220 • nestedNovelTangentOne := by
  ext i
  fin_cases i <;>
    norm_num [nestedNovelTangentZero, nestedNovelTangentOne,
      cancellationTangent, tangentTransfer, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_succ]

/-- Second exact tangent leg, including the new primitive factor `2`. -/
theorem nestedNovel_tangentStep_one :
    tangentTransfer (2 : ℤ) 131299 1 6561 3 *ᵥ
        nestedNovelTangentOne =
      13122 • nestedNovelTangentTwo := by
  ext i
  fin_cases i <;>
    norm_num [nestedNovelTangentOne, nestedNovelTangentTwo,
      cancellationTangent, tangentTransfer, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_succ]

/-- The two novel collisions form one exact scaled trajectory from the canonical residual
source. -/
theorem nestedNovel_scaledTrajectory :
    ScaledTrajectory nestedNovelTangentZero
      [tangentTransfer (2 : ℤ) 131299 1 6561 81,
       tangentTransfer (2 : ℤ) 131299 1 6561 3]
      [131220, 13122] nestedNovelTangentTwo := by
  exact
    .cons nestedNovel_tangentStep_zero
      (.cons nestedNovel_tangentStep_one (.nil nestedNovelTangentTwo))

/-- The accumulated tangent scalar is exactly the content of the composed image. -/
theorem nestedNovel_composed_content :
    Int.gcd
        ((chronologicalProduct
          [tangentTransfer (2 : ℤ) 131299 1 6561 81,
           tangentTransfer (2 : ℤ) 131299 1 6561 3] *ᵥ
            nestedNovelTangentZero) 0)
        ((chronologicalProduct
          [tangentTransfer (2 : ℤ) 131299 1 6561 81,
           tangentTransfer (2 : ℤ) 131299 1 6561 3] *ᵥ
            nestedNovelTangentZero) 1) =
      (131220 * 13122 : ℤ).natAbs := by
  simpa using
    nestedNovel_scaledTrajectory.image_gcd
      (show IsCoprime (430988968 : ℤ) (-1) by norm_num)

/-- Parameters whose canonical orbit swallows novel cyclotomic support on four consecutive
legal steps. -/
def cyclotomicLadderParameters : Parameters where
  prime := 3
  prime_prime := by norm_num
  depth := 2
  depth_two := by norm_num
  center := -64
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

private theorem cyclotomicLadder_ready_zero :
    Ready cyclotomicLadderParameters 4 52569 := by
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

private theorem cyclotomicLadder_ready_one :
    Ready cyclotomicLadderParameters 2 345851379 := by
  have state_value :
      HasValue 3 (345851379 : ℚ) 2 := by
    rw [show (345851379 : ℚ) =
      (3 : ℚ) ^ 2 * (38427931 : ℚ) / (1 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 2
        (by norm_num) (by norm_num)
  have defect_value :
      HasValue 3 ((345851379 : ℚ) - 3 ^ 2) 4 := by
    rw [show (345851379 : ℚ) - 3 ^ 2 =
      (3 : ℚ) ^ 4 * (4269770 : ℚ) / (1 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 4
        (by norm_num) (by norm_num)
  exact ⟨by norm_num, state_value.2, defect_value.2⟩

private theorem cyclotomicLadder_ready_two :
    Ready cyclotomicLadderParameters 2 (124677550089 / 29245) := by
  have state_value :
      HasValue 3 (124677550089 / 29245 : ℚ) 2 := by
    rw [show (124677550089 / 29245 : ℚ) =
      (3 : ℚ) ^ 2 * (13853061121 : ℚ) / (29245 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 2
        (by norm_num) (by norm_num)
  have defect_value :
      HasValue 3 ((124677550089 / 29245 : ℚ) - 3 ^ 2) 4 := by
    rw [show (124677550089 / 29245 : ℚ) - 3 ^ 2 =
      (3 : ℚ) ^ 4 * (1539225764 : ℚ) / (29245 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 4
        (by norm_num) (by norm_num)
  exact ⟨by norm_num, state_value.2, defect_value.2⟩

private theorem cyclotomicLadder_ready_three :
    Ready cyclotomicLadderParameters 1
      (1640513361033339 / 384806441) := by
  have state_value :
      HasValue 3 (1640513361033339 / 384806441 : ℚ) 1 := by
    rw [show (1640513361033339 / 384806441 : ℚ) =
      (3 : ℚ) ^ 1 * (546837787011113 : ℚ) /
        (384806441 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 1
        (by norm_num) (by norm_num)
  have defect_value :
      HasValue 3
        ((1640513361033339 / 384806441 : ℚ) - 3) 2 := by
    rw [show (1640513361033339 / 384806441 : ℚ) - 3 =
      (3 : ℚ) ^ 2 * (182279134068224 : ℚ) /
        (384806441 : ℚ) by norm_num]
    exact
      primePower_mul_int_div_int_hasValue 2
        (by norm_num) (by norm_num)
  exact ⟨by norm_num, state_value.2, defect_value.2⟩

/-- The canonical residual orbit begins with the legal wait word `4,2,2,1`. -/
theorem cyclotomicLadder_decodedSteps :
    DecodedStep cyclotomicLadderParameters 1 (1 / 6571) ∧
      DecodedStep cyclotomicLadderParameters
        (1 / 6571) (2134885 / 172925689) ∧
      DecodedStep cyclotomicLadderParameters
        (2134885 / 172925689) (384806441 / 31169380211) ∧
      DecodedStep cyclotomicLadderParameters
        (384806441 / 31169380211)
          (91139567034112 / 820256488113449) := by
  constructor
  · refine ⟨4, ?_, ?_⟩
    · rw [residualBranch_iff_ready]
      convert cyclotomicLadder_ready_zero using 1
    · norm_num [residualStep, prefixDecode, centerTransform,
        cyclotomicLadderParameters, drift]
  constructor
  · refine ⟨2, ?_, ?_⟩
    · rw [residualBranch_iff_ready]
      convert cyclotomicLadder_ready_one using 1
    · norm_num [residualStep, prefixDecode, centerTransform,
        cyclotomicLadderParameters, drift]
  constructor
  · refine ⟨2, ?_, ?_⟩
    · rw [residualBranch_iff_ready]
      convert cyclotomicLadder_ready_two using 1
    · norm_num [residualStep, prefixDecode, centerTransform,
        cyclotomicLadderParameters, drift]
  · refine ⟨1, ?_, ?_⟩
    · rw [residualBranch_iff_ready]
      convert cyclotomicLadder_ready_three using 1
    · norm_num [residualStep, prefixDecode, centerTransform,
        cyclotomicLadderParameters, drift]

/-- Primitive integral lift of the same four canonical steps, with common factors
`8,2,292,2`. -/
theorem cyclotomicLadder_primitiveSteps :
    PrimitiveIntegralStep 3 2 (-64) 52633 1
        (1, 1) (1, 6571) ∧
      PrimitiveIntegralStep 3 2 (-64) 52633 1
        (1, 6571) (2134885, 172925689) ∧
      PrimitiveIntegralStep 3 2 (-64) 52633 1
        (2134885, 172925689) (384806441, 31169380211) ∧
      PrimitiveIntegralStep 3 2 (-64) 52633 1
        (384806441, 31169380211)
          (91139567034112, 820256488113449) := by
  constructor
  · simpa [prescribedResetDrift, prescribedResetTargetDenominator] using
      prescribedReset_primitiveIntegralStep 3 2 4 (-64) 8 10 (by norm_num)
  constructor
  · refine ⟨by norm_num, by norm_num, 2, 4269770, 345851378, 2,
      ?_, by norm_num, by norm_num⟩
    norm_num [IntegralStep, integralStepNumerator, terminalDefect]
  constructor
  · refine ⟨by norm_num, by norm_num, 2, 112363480772,
      9101459021612, 292, ?_, by norm_num, by norm_num⟩
    norm_num [IntegralStep, integralStepNumerator, terminalDefect]
  · refine ⟨by norm_num, by norm_num, 1, 182279134068224,
      1640512976226898, 2, ?_, by norm_num, by norm_num⟩
    norm_num [IntegralStep, integralStepNumerator, terminalDefect]

/-- After fixed-support factors are removed, all four legal steps still swallow nonunits:
`8,2,4,2`. -/
theorem cyclotomicLadder_novelFactors :
    IsCoprime (8 : ℤ) (52633 * 3) ∧
      IsCoprime (2 : ℤ) (52633 * 3) ∧
      (292 : ℤ) = 73 * 4 ∧
      (73 : ℤ) ∣ 52633 ∧
      IsCoprime (4 : ℤ) (52633 * 3) ∧
      IsCoprime (2 : ℤ) (52633 * 3) := by
  norm_num

end
end MatrixMortality.ReturnGuard.Examples
