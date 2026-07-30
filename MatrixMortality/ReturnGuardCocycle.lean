import MatrixMortality.ReturnGuardArithmetic

/-!
# Terminal-defect cocycle for decoded guard dynamics

The terminal linear form is not merely the next denominator.  In coordinates consisting of the
current numerator and terminal defect, one decoded step is an exact two-dimensional cocycle.
After primitive reduction, consecutive denominators obey a second-order recurrence whose
coefficients expose every cancellation factor.
-/

namespace MatrixMortality.ReturnGuard

noncomputable section

/-- The unscaled step numerator is the terminal defect plus one cyclotomic displacement. -/
theorem integralStepNumerator_eq_terminalDefect_add
    (prime : Nat) (centerNumerator driftNumerator scale : ℤ)
    (wait : Nat) (numerator denominator : ℤ) :
    integralStepNumerator prime centerNumerator driftNumerator scale
        wait numerator denominator =
      terminalDefect centerNumerator driftNumerator scale numerator denominator +
        scale * (1 - (prime : ℤ) ^ wait) * numerator := by
  simp [integralStepNumerator, terminalDefect]
  ring

/-- Exact transport of the terminal defect through one integral step. -/
theorem integralStep_terminalDefect
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator : ℤ}
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator) :
    (prime : ℤ) ^ (depth * wait) *
        terminalDefect centerNumerator driftNumerator scale
          nextNumerator nextDenominator =
      (centerNumerator - scale +
          driftNumerator * (prime : ℤ) ^ (depth * wait)) *
          terminalDefect centerNumerator driftNumerator scale numerator denominator +
        (centerNumerator - scale) * scale *
          (1 - (prime : ℤ) ^ wait) * numerator := by
  calc
    (prime : ℤ) ^ (depth * wait) *
        terminalDefect centerNumerator driftNumerator scale
          nextNumerator nextDenominator =
      (centerNumerator - scale) *
          ((prime : ℤ) ^ (depth * wait) * nextNumerator) +
        driftNumerator * (prime : ℤ) ^ (depth * wait) *
          nextDenominator := by
            simp [terminalDefect]
            ring
    _ =
      (centerNumerator - scale) *
          integralStepNumerator prime centerNumerator driftNumerator scale
            wait numerator denominator +
        driftNumerator * (prime : ℤ) ^ (depth * wait) *
          terminalDefect centerNumerator driftNumerator scale
            numerator denominator := by rw [step.1, step.2]
    _ =
      (centerNumerator - scale +
          driftNumerator * (prime : ℤ) ^ (depth * wait)) *
          terminalDefect centerNumerator driftNumerator scale numerator denominator +
        (centerNumerator - scale) * scale *
          (1 - (prime : ℤ) ^ wait) * numerator := by
            rw [integralStepNumerator_eq_terminalDefect_add]
            ring

/-- Consecutive primitive denominators satisfy an exact second-order recurrence.  The common
factors are retained explicitly rather than hidden inside rational normalization. -/
theorem reducedDenominator_recurrence
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat}
    {numerator denominator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator
      followingCommon followingReducedDenominator : ℤ}
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator)
    (following_denominator :
      terminalDefect centerNumerator driftNumerator scale
          reducedNumerator reducedDenominator =
        followingCommon * followingReducedDenominator) :
    common * (prime : ℤ) ^ (depth * wait) *
        followingCommon * followingReducedDenominator =
      common *
          (centerNumerator - scale * (prime : ℤ) ^ wait +
            driftNumerator * (prime : ℤ) ^ (depth * wait)) *
          reducedDenominator -
        driftNumerator * scale * (1 - (prime : ℤ) ^ wait) *
          denominator := by
  have scaled_numerator :
      (prime : ℤ) ^ (depth * wait) *
          (common * reducedNumerator) =
        integralStepNumerator prime centerNumerator driftNumerator scale
          wait numerator denominator := by
    rw [← numerator_reduced]
    exact step.1
  have current_terminal :
      common * reducedDenominator =
        terminalDefect centerNumerator driftNumerator scale
          numerator denominator := by
    rw [← denominator_reduced]
    exact step.2
  have current_numerator :
      (centerNumerator - scale) * numerator =
        common * reducedDenominator - driftNumerator * denominator := by
    rw [current_terminal]
    simp [terminalDefect]
  calc
    common * (prime : ℤ) ^ (depth * wait) *
        followingCommon * followingReducedDenominator =
      common * (prime : ℤ) ^ (depth * wait) *
        terminalDefect centerNumerator driftNumerator scale
          reducedNumerator reducedDenominator := by
            rw [following_denominator]
            ring
    common * (prime : ℤ) ^ (depth * wait) *
        terminalDefect centerNumerator driftNumerator scale
          reducedNumerator reducedDenominator =
      (centerNumerator - scale) *
          ((prime : ℤ) ^ (depth * wait) *
            (common * reducedNumerator)) +
        driftNumerator * (prime : ℤ) ^ (depth * wait) *
          (common * reducedDenominator) := by
            simp [terminalDefect]
            ring
    _ =
      (centerNumerator - scale) *
          integralStepNumerator prime centerNumerator driftNumerator scale
            wait numerator denominator +
        driftNumerator * (prime : ℤ) ^ (depth * wait) *
          terminalDefect centerNumerator driftNumerator scale
            numerator denominator := by
              rw [scaled_numerator, current_terminal]
    _ =
      (centerNumerator - scale +
          driftNumerator * (prime : ℤ) ^ (depth * wait)) *
          terminalDefect centerNumerator driftNumerator scale
            numerator denominator +
        (centerNumerator - scale) * scale *
          (1 - (prime : ℤ) ^ wait) * numerator := by
            rw [integralStepNumerator_eq_terminalDefect_add]
            ring
    _ =
      (centerNumerator - scale +
          driftNumerator * (prime : ℤ) ^ (depth * wait)) *
          (common * reducedDenominator) +
        scale * (1 - (prime : ℤ) ^ wait) *
          ((centerNumerator - scale) * numerator) := by
            rw [← current_terminal]
            ring
    _ =
      (centerNumerator - scale +
          driftNumerator * (prime : ℤ) ^ (depth * wait)) *
          (common * reducedDenominator) +
        scale * (1 - (prime : ℤ) ^ wait) *
          (common * reducedDenominator -
            driftNumerator * denominator) := by
              rw [current_numerator]
    _ =
      common *
          (centerNumerator - scale * (prime : ℤ) ^ wait +
            driftNumerator * (prime : ℤ) ^ (depth * wait)) *
          reducedDenominator -
        driftNumerator * scale * (1 - (prime : ℤ) ^ wait) *
          denominator := by ring

end
end MatrixMortality.ReturnGuard
