import MatrixMortality.ReturnGuardGap

/-!
# Orbitwise schedule pumping

Exact branch similarity turns any legal block shared by two orbit checkpoints into a dichotomy:
the checkpoints coincide, or the block's p-adic expansion fits inside their rational height
budget.  The theorem applies to arbitrary repeated factors, not merely consecutive powers of a
single macro.
-/

namespace MatrixMortality.ReturnGuard

open MatrixMortality.PadicValuation

noncomputable section

/-- Any legal schedule shared by two checkpoints either starts at the same rational point or
its p-adic expansion weight fits inside the product of their projective heights. -/
theorem sharedSchedule_exact_or_power_le_pairHeights
    (parameters : Parameters) (waits : List Nat) {left right : ℚ}
    (left_unit : IsUnit parameters.prime left)
    (right_unit : IsUnit parameters.prime right)
    (left_follows : FollowsResidualSchedule parameters waits left)
    (right_follows : FollowsResidualSchedule parameters waits right) :
    left = right ∨
      parameters.prime ^ scheduleNatWeight parameters waits ≤
        2 * projectivePairHeight (rationalPair left) *
          projectivePairHeight (rationalPair right) := by
  by_cases exact : left = right
  · exact Or.inl exact
  · right
    have difference_ne : left - right ≠ 0 :=
      sub_ne_zero.mpr exact
    have difference_nonnegative :
        0 ≤ padicValRat parameters.prime (left - right) := by
      have lower := min_le_sub (prime := parameters.prime) difference_ne
      rw [left_unit.2, right_unit.2, min_self] at lower
      exact lower
    obtain ⟨separation, separation_eq⟩ :=
      Int.eq_ofNat_of_zero_le difference_nonnegative
    have difference :
        HasValue parameters.prime (left - right) separation :=
      ⟨difference_ne, separation_eq⟩
    have transported :=
      residualRun_sub_hasValue parameters waits
        left_follows right_follows difference
    have left_endpoint_unit :
        IsUnit parameters.prime (residualRun parameters waits left) :=
      residualRun_isUnit parameters waits left left_unit left_follows
    have right_endpoint_unit :
        IsUnit parameters.prime (residualRun parameters waits right) :=
      residualRun_isUnit parameters waits right right_unit right_follows
    have transported_nonnegative :
        0 ≤
          padicValRat parameters.prime
            (residualRun parameters waits left -
              residualRun parameters waits right) := by
      have lower :=
        min_le_sub (prime := parameters.prime) transported.1
      rw [left_endpoint_unit.2, right_endpoint_unit.2, min_self] at lower
      exact lower
    rw [transported.2, scheduleWeight_eq_natCast] at transported_nonnegative
    have weight_le :
        scheduleNatWeight parameters waits ≤ separation := by
      exact_mod_cast (sub_nonneg.mp transported_nonnegative)
    exact
      (Nat.pow_le_pow_right parameters.prime_prime.pos weight_le).trans
        (primePower_le_rationalPairHeight parameters
          left_unit right_unit exact difference)

/-- Orbitwise repeated-factor pumping: the same legal block at two decoded checkpoints is
either an exact state repetition or its expansion weight is bounded by their elapsed height
budgets. -/
theorem sharedSchedule_exact_or_power_le_heightEnvelope
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    {source left right : ℚ} {leftSteps rightSteps : Nat}
    (left_unit : IsUnit parameters.prime left)
    (right_unit : IsUnit parameters.prime right)
    (left_execution :
      Relation.ReachesIn (DecodedStep parameters) leftSteps source left)
    (right_execution :
      Relation.ReachesIn (DecodedStep parameters) rightSteps source right)
    (waits : List Nat)
    (left_follows : FollowsResidualSchedule parameters waits left)
    (right_follows : FollowsResidualSchedule parameters waits right) :
    left = right ∨
      parameters.prime ^ scheduleNatWeight parameters waits ≤
        2 *
          guardHeightCoefficient centerNumerator driftNumerator scale ^
            (leftSteps + rightSteps) *
          projectivePairHeight (rationalPair source) ^ 2 := by
  rcases
      sharedSchedule_exact_or_power_le_pairHeights parameters waits
        left_unit right_unit left_follows right_follows with
    exact | bounded
  · exact Or.inl exact
  · right
    have left_height :=
      decodedExecution_rationalPairHeight_le parameters
        center_eq drift_eq scale_ne left_execution
    have right_height :=
      decodedExecution_rationalPairHeight_le parameters
        center_eq drift_eq scale_ne right_execution
    calc
      parameters.prime ^ scheduleNatWeight parameters waits ≤
          2 * projectivePairHeight (rationalPair left) *
            projectivePairHeight (rationalPair right) :=
        bounded
      _ ≤
          2 *
              (guardHeightCoefficient centerNumerator driftNumerator scale ^
                leftSteps *
                projectivePairHeight (rationalPair source)) *
            (guardHeightCoefficient centerNumerator driftNumerator scale ^
                rightSteps *
              projectivePairHeight (rationalPair source)) :=
        Nat.mul_le_mul
          (Nat.mul_le_mul_left 2 left_height) right_height
      _ =
          2 *
            guardHeightCoefficient centerNumerator driftNumerator scale ^
              (leftSteps + rightSteps) *
            projectivePairHeight (rationalPair source) ^ 2 := by
        rw [pow_add]
        ring

end
end MatrixMortality.ReturnGuard
