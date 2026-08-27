import MatrixMortality.ReturnGuardEndpoint
import MatrixMortality.ReturnGuardGap

/-!
# Content and exterior-product budgets

Primitive normalization removes a scalar from every integral transfer.  Retaining that scalar
gives a sharper Archimedean height law.  Comparing two trajectories through the same branch
gives an exact exterior-product conservation law: cyclotomic determinant content can only be
removed on either trajectory or remain in their projective separation.
-/

namespace MatrixMortality.ReturnGuard

noncomputable section

/-- Primitive reduction scales integral projective height exactly by the removed content. -/
theorem integralPairHeight_mul
    (common numerator denominator : ℤ) :
    integralPairHeight (common * numerator) (common * denominator) =
      common.natAbs * integralPairHeight numerator denominator := by
  simp only [integralPairHeight, Int.natAbs_mul]
  by_cases ordered : numerator.natAbs ≤ denominator.natAbs
  · rw [max_eq_right ordered,
      max_eq_right (Nat.mul_le_mul_left common.natAbs ordered)]
  · have reverse : denominator.natAbs ≤ numerator.natAbs :=
      le_of_not_ge ordered
    rw [max_eq_left reverse,
      max_eq_left (Nat.mul_le_mul_left common.natAbs reverse)]

/-- Retaining the primitive reduction factor sharpens the one-step height envelope. -/
theorem integralStep_content_mul_height_le
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator : ℤ}
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator)
    (prime_positive : 0 < prime)
    (depth_positive : 0 < depth) :
    common.natAbs *
        integralPairHeight reducedNumerator reducedDenominator ≤
      (centerNumerator.natAbs + driftNumerator.natAbs +
          scale.natAbs) *
        integralPairHeight numerator denominator := by
  rw [← integralPairHeight_mul, ← numerator_reduced, ← denominator_reduced]
  exact integralStep_next_height_le step prime_positive depth_positive

/-- A nonzero reduced numerator charges the removed content and all but one wait scale to the
source height. -/
theorem integralStep_wait_content_le
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator
      common reducedNumerator : ℤ}
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (reducedNumerator_ne : reducedNumerator ≠ 0)
    (prime_positive : 0 < prime)
    (depth_positive : 0 < depth) :
    prime ^ ((depth - 1) * wait) * common.natAbs ≤
      (centerNumerator.natAbs + driftNumerator.natAbs +
          scale.natAbs) *
        integralPairHeight numerator denominator := by
  let height := integralPairHeight numerator denominator
  let coefficient :=
    centerNumerator.natAbs + driftNumerator.natAbs + scale.natAbs
  have waitPower_positive : 0 < prime ^ wait :=
    Nat.pow_pos prime_positive
  have reducedNumerator_positive : 0 < reducedNumerator.natAbs :=
    Int.natAbs_pos.mpr reducedNumerator_ne
  have scaled_content_le :
      prime ^ (depth * wait) * common.natAbs ≤
        (integralStepNumerator prime centerNumerator driftNumerator scale
          wait numerator denominator).natAbs := by
    calc
      prime ^ (depth * wait) * common.natAbs ≤
          prime ^ (depth * wait) * common.natAbs *
            reducedNumerator.natAbs :=
        Nat.le_mul_of_pos_right _ reducedNumerator_positive
      _ =
          (integralStepNumerator prime centerNumerator driftNumerator scale
            wait numerator denominator).natAbs := by
        rw [← step.1, numerator_reduced]
        simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
        ring
  have coefficient_wait_le :
      centerNumerator.natAbs + driftNumerator.natAbs +
          scale.natAbs * prime ^ wait ≤
        coefficient * prime ^ wait := by
    dsimp [coefficient]
    have center_le :
        centerNumerator.natAbs ≤
          centerNumerator.natAbs * prime ^ wait :=
      Nat.le_mul_of_pos_right _ waitPower_positive
    have drift_le :
        driftNumerator.natAbs ≤
          driftNumerator.natAbs * prime ^ wait :=
      Nat.le_mul_of_pos_right _ waitPower_positive
    calc
      centerNumerator.natAbs + driftNumerator.natAbs +
          scale.natAbs * prime ^ wait ≤
        centerNumerator.natAbs * prime ^ wait +
            driftNumerator.natAbs * prime ^ wait +
          scale.natAbs * prime ^ wait :=
        Nat.add_le_add (Nat.add_le_add center_le drift_le) le_rfl
      _ = coefficient * prime ^ wait := by
        dsimp [coefficient]
        ring
  have full_bound :
      prime ^ (depth * wait) * common.natAbs ≤
        prime ^ wait * (coefficient * height) := by
    calc
      _ ≤
          (integralStepNumerator prime centerNumerator driftNumerator scale
            wait numerator denominator).natAbs :=
        scaled_content_le
      _ ≤
          (centerNumerator.natAbs + driftNumerator.natAbs +
              scale.natAbs * prime ^ wait) * height :=
        integralStepNumerator_natAbs_le_height prime centerNumerator
          driftNumerator scale wait numerator denominator
      _ ≤ coefficient * prime ^ wait * height :=
        Nat.mul_le_mul_right height coefficient_wait_le
      _ = prime ^ wait * (coefficient * height) := by ring
  have exponent_eq :
      wait + (depth - 1) * wait = depth * wait := by
    calc
      wait + (depth - 1) * wait =
          1 * wait + (depth - 1) * wait := by simp
      _ = (1 + (depth - 1)) * wait := by rw [Nat.add_mul]
      _ = depth * wait := by
        congr 1
        omega
  have factored :
      prime ^ wait *
          (prime ^ ((depth - 1) * wait) * common.natAbs) ≤
        prime ^ wait * (coefficient * height) := by
    rwa [← mul_assoc, ← pow_add, exponent_eq]
  exact Nat.le_of_mul_le_mul_left factored waitPower_positive

/-- Two primitively reduced trajectories through one branch obey an exact all-place
exterior-product law. -/
theorem primitiveSteps_projectivePairCross
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat}
    {leftSource rightSource leftTarget rightTarget : ℤ × ℤ}
    {leftNextNumerator leftNextDenominator leftCommon
      rightNextNumerator rightNextDenominator rightCommon : ℤ}
    (leftStep :
      IntegralStep prime depth centerNumerator driftNumerator scale wait
        leftSource.1 leftSource.2 leftNextNumerator leftNextDenominator)
    (leftNumerator :
      leftNextNumerator = leftCommon * leftTarget.1)
    (leftDenominator :
      leftNextDenominator = leftCommon * leftTarget.2)
    (rightStep :
      IntegralStep prime depth centerNumerator driftNumerator scale wait
        rightSource.1 rightSource.2 rightNextNumerator rightNextDenominator)
    (rightNumerator :
      rightNextNumerator = rightCommon * rightTarget.1)
    (rightDenominator :
      rightNextDenominator = rightCommon * rightTarget.2)
    (prime_ne : prime ≠ 0) :
    (prime : ℤ) ^ (depth * wait) * leftCommon * rightCommon *
        projectivePairCross leftTarget rightTarget =
      driftNumerator * scale * (1 - (prime : ℤ) ^ wait) *
        projectivePairCross leftSource rightSource := by
  have power_ne :
      (prime : ℤ) ^ (depth * wait) ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast prime_ne)
  apply mul_left_cancel₀ power_ne
  calc
    (prime : ℤ) ^ (depth * wait) *
        ((prime : ℤ) ^ (depth * wait) * leftCommon * rightCommon *
          projectivePairCross leftTarget rightTarget) =
      ((prime : ℤ) ^ (depth * wait) *
          (leftCommon * leftTarget.1)) *
          ((prime : ℤ) ^ (depth * wait) *
            (rightCommon * rightTarget.2)) -
        ((prime : ℤ) ^ (depth * wait) *
          (rightCommon * rightTarget.1)) *
          ((prime : ℤ) ^ (depth * wait) *
            (leftCommon * leftTarget.2)) := by
      simp [projectivePairCross]
      ring
    _ =
      integralStepNumerator prime centerNumerator driftNumerator scale
          wait leftSource.1 leftSource.2 *
          ((prime : ℤ) ^ (depth * wait) * rightNextDenominator) -
        integralStepNumerator prime centerNumerator driftNumerator scale
          wait rightSource.1 rightSource.2 *
          ((prime : ℤ) ^ (depth * wait) * leftNextDenominator) := by
      rw [← leftNumerator, ← rightNumerator, ← leftDenominator,
        ← rightDenominator, leftStep.1, rightStep.1]
    _ =
      (prime : ℤ) ^ (depth * wait) *
        (driftNumerator * scale * (1 - (prime : ℤ) ^ wait) *
          projectivePairCross leftSource rightSource) := by
      rw [leftStep.2, rightStep.2]
      simp [integralStepNumerator, terminalDefect, projectivePairCross]
      ring

/-- Every portion of the cyclotomic factor coprime to the removed primitive content survives
as an exact reset congruence of the reduced target.  This retains prime-power multiplicities,
not merely the radical handled by the primewise reset-or-cancel theorem. -/
theorem cyclotomicComplement_dvd_targetDifference
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator complement : ℤ}
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator)
    (complement_cyclotomic :
      complement ∣ (prime : ℤ) ^ wait - 1)
    (complement_common : IsCoprime complement common) :
    complement ∣ reducedNumerator - reducedDenominator := by
  have complement_depth :
      complement ∣ (prime : ℤ) ^ (depth * wait) - 1 := by
    apply complement_cyclotomic.trans
    rw [Nat.mul_comm depth wait, pow_mul]
    exact sub_one_dvd_pow_sub_one ((prime : ℤ) ^ wait) depth
  have complement_raw :
      complement ∣
        (prime : ℤ) ^ (depth * wait) * nextNumerator -
          nextDenominator := by
    rw [integralStep_difference step]
    have complement_negative :
        complement ∣ 1 - (prime : ℤ) ^ wait := by
      simpa only [neg_sub] using dvd_neg.mpr complement_cyclotomic
    exact (complement_negative.mul_left scale).mul_right numerator
  have complement_scaled :
      complement ∣
        common *
          ((prime : ℤ) ^ (depth * wait) * reducedNumerator -
            reducedDenominator) := by
    simpa [numerator_reduced, denominator_reduced, mul_sub, mul_assoc,
      mul_left_comm, mul_comm] using complement_raw
  have complement_residual :
      complement ∣
        (prime : ℤ) ^ (depth * wait) * reducedNumerator -
          reducedDenominator :=
    complement_common.dvd_of_dvd_mul_left complement_scaled
  have complement_correction :
      complement ∣
        ((prime : ℤ) ^ (depth * wait) - 1) * reducedNumerator :=
    dvd_mul_of_dvd_left complement_depth reducedNumerator
  have decomposition :
      reducedNumerator - reducedDenominator =
        ((prime : ℤ) ^ (depth * wait) * reducedNumerator -
          reducedDenominator) -
        ((prime : ℤ) ^ (depth * wait) - 1) * reducedNumerator := by
    ring
  rw [decomposition]
  exact dvd_sub complement_residual complement_correction

end
end MatrixMortality.ReturnGuard
