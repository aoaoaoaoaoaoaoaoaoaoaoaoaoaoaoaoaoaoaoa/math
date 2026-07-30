import MatrixMortality.ReturnGuardGauss
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Integral cancellation in decoded guard dynamics

Clearing the rational parameters turns one surviving decoded step into an accelerated
Collatz-type recurrence on primitive integer pairs.  A determinant argument confines every
common cancellation to fixed parameter primes or factors of `p^wait - 1`.  Primitive divisors
therefore force a projective reset unless the corresponding cyclotomic prime is swallowed by
that common cancellation.
-/

namespace MatrixMortality.ReturnGuard

noncomputable section

/-- Unscaled numerator of one decoded integer-pair step. -/
def integralStepNumerator
    (prime : Nat) (centerNumerator driftNumerator scale : ℤ)
    (wait : Nat) (numerator denominator : ℤ) : ℤ :=
  (centerNumerator - scale * prime ^ wait) * numerator +
    driftNumerator * denominator

/-- Terminal linear defect, which is also the denominator of one decoded integer-pair step. -/
def terminalDefect
    (centerNumerator driftNumerator scale : ℤ)
    (numerator denominator : ℤ) : ℤ :=
  (centerNumerator - scale) * numerator +
    driftNumerator * denominator

/-- Exact integral step after removing the forced `p^(depth * wait)` numerator factor. -/
def IntegralStep
    (prime depth : Nat) (centerNumerator driftNumerator scale : ℤ)
    (wait : Nat) (numerator denominator nextNumerator nextDenominator : ℤ) : Prop :=
  prime ^ (depth * wait) * nextNumerator =
      integralStepNumerator prime centerNumerator driftNumerator scale
        wait numerator denominator ∧
    nextDenominator =
      terminalDefect centerNumerator driftNumerator scale
        numerator denominator

/-- The integral recurrence is exactly the decoded residual map after projectivization. -/
theorem integralStep_realizes_residualStep
    (parameters : Parameters)
    {centerNumerator driftNumerator scale numerator denominator
      nextNumerator nextDenominator : ℤ} {wait : Nat}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0) (denominator_ne : denominator ≠ 0)
    (nextDenominator_ne : nextDenominator ≠ 0)
    (step :
      IntegralStep parameters.prime parameters.depth centerNumerator
        driftNumerator scale wait numerator denominator
        nextNumerator nextDenominator) :
    residualStep parameters wait ((numerator : ℚ) / denominator) =
      (nextNumerator : ℚ) / nextDenominator := by
  have transform_eq :
      (parameters.center - 1) * ((numerator : ℚ) / denominator) +
          drift parameters.center parameters.reset =
        (nextDenominator : ℚ) / (scale * denominator) := by
    rw [drift_eq, center_eq, step.2]
    dsimp [terminalDefect]
    field_simp [scale_ne, denominator_ne]
    ring
  have transform_ne :
      (parameters.center - 1) * ((numerator : ℚ) / denominator) +
          drift parameters.center parameters.reset ≠ 0 := by
    rw [transform_eq]
    exact div_ne_zero (by exact_mod_cast nextDenominator_ne)
      (mul_ne_zero (by exact_mod_cast scale_ne)
        (by exact_mod_cast denominator_ne))
  rw [residualStep_eq parameters wait _ transform_ne]
  have numerator_eq :
      (parameters.center - parameters.prime ^ wait) *
            ((numerator : ℚ) / denominator) +
          drift parameters.center parameters.reset =
        ((parameters.prime : ℚ) ^ (parameters.depth * wait) *
            nextNumerator) /
          (scale * denominator) := by
    rw [drift_eq, center_eq]
    have cast_step :
        (parameters.prime : ℚ) ^ (parameters.depth * wait) *
            (nextNumerator : ℚ) =
          ((centerNumerator : ℚ) -
              (scale : ℚ) * parameters.prime ^ wait) *
              numerator +
            (driftNumerator : ℚ) * denominator := by
      have integer_step := step.1
      dsimp [integralStepNumerator] at integer_step
      exact_mod_cast integer_step
    field_simp [scale_ne, denominator_ne]
    linear_combination
      -((scale : ℚ) ^ 2 * (denominator : ℚ)) * cast_step
  rw [numerator_eq, transform_eq]
  field_simp [parameters.prime_ne_zero, scale_ne, denominator_ne,
    nextDenominator_ne]
  ring

/-- Exact difference identity for the integral pair recurrence. -/
theorem integralStep_difference
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator : ℤ}
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator) :
    prime ^ (depth * wait) * nextNumerator - nextDenominator =
      scale * (1 - prime ^ wait) * numerator := by
  rcases step with ⟨numerator_eq, denominator_eq⟩
  rw [numerator_eq, denominator_eq]
  simp [integralStepNumerator, terminalDefect]
  ring

/-- Every divisor of a positive power minus one is coprime to the base. -/
theorem divisor_pow_sub_one_isCoprime_base
    {base exponent : Nat} {divisor : ℤ}
    (exponent_positive : 0 < exponent)
    (divides : divisor ∣ (base : ℤ) ^ exponent - 1) :
    IsCoprime divisor (base : ℤ) := by
  obtain ⟨prior, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt exponent_positive)
  obtain ⟨quotient, quotient_eq⟩ := divides
  refine ⟨-quotient, (base : ℤ) ^ prior, ?_⟩
  calc
    -quotient * divisor + (base : ℤ) ^ prior * base =
        (base : ℤ) ^ (Nat.succ prior) - divisor * quotient := by
          rw [pow_succ]
          ring
    _ = 1 := by rw [← quotient_eq]; ring

/-- A factorization through a primitive pair exposes every common divisor in its common
factor. -/
theorem divisor_dvd_commonFactor_iff
    {left right common reducedLeft reducedRight divisor : ℤ}
    (left_eq : left = common * reducedLeft)
    (right_eq : right = common * reducedRight)
    (reduced_primitive : IsCoprime reducedLeft reducedRight) :
    divisor ∣ common ↔ divisor ∣ left ∧ divisor ∣ right := by
  constructor
  · intro divides_common
    exact ⟨left_eq ▸ divides_common.mul_right reducedLeft,
      right_eq ▸ divides_common.mul_right reducedRight⟩
  · rintro ⟨divides_left, divides_right⟩
    obtain ⟨leftCoefficient, rightCoefficient, bezout⟩ := reduced_primitive
    have divides_combination :
        divisor ∣ leftCoefficient * left + rightCoefficient * right :=
      dvd_add (divides_left.mul_left leftCoefficient)
        (divides_right.mul_left rightCoefficient)
    convert divides_combination using 1
    rw [left_eq, right_eq]
    calc
      common = common * 1 := by ring
      _ = common *
          (leftCoefficient * reducedLeft +
            rightCoefficient * reducedRight) := by rw [bezout]
      _ = leftCoefficient * (common * reducedLeft) +
          rightCoefficient * (common * reducedRight) := by ring

/-- Every cancellation factor coprime to the base is exactly a common divisor of the source
terminal defect and the step's cyclotomic displacement. -/
theorem integralStep_cancel_iff_terminalDefect_and_displacement
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator divisor : ℤ}
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator)
    (reduced_primitive : IsCoprime reducedNumerator reducedDenominator)
    (base_coprime : IsCoprime divisor (prime : ℤ)) :
    divisor ∣ common ↔
      divisor ∣
          terminalDefect centerNumerator driftNumerator scale
            numerator denominator ∧
        divisor ∣ scale * (1 - (prime : ℤ) ^ wait) * numerator := by
  rw [divisor_dvd_commonFactor_iff numerator_reduced denominator_reduced
    reduced_primitive, step.2]
  constructor
  · rintro ⟨divides_numerator, divides_terminal⟩
    refine ⟨divides_terminal, ?_⟩
    have divides_nextDenominator : divisor ∣ nextDenominator := by
      rw [step.2]
      exact divides_terminal
    have divides_scaled :
        divisor ∣
          (prime : ℤ) ^ (depth * wait) * nextNumerator :=
      divides_numerator.mul_left _
    have divides_difference :=
      dvd_sub divides_scaled divides_nextDenominator
    rw [integralStep_difference step] at divides_difference
    exact divides_difference
  · rintro ⟨divides_terminal, divides_displacement⟩
    refine ⟨?_, divides_terminal⟩
    have divides_nextDenominator : divisor ∣ nextDenominator := by
      rw [step.2]
      exact divides_terminal
    have divides_difference :
        divisor ∣
          (prime : ℤ) ^ (depth * wait) * nextNumerator -
            nextDenominator := by
      rw [integralStep_difference step]
      exact divides_displacement
    have divides_scaled :
        divisor ∣
          (prime : ℤ) ^ (depth * wait) * nextNumerator := by
      have sum := dvd_add divides_difference divides_nextDenominator
      simpa only [sub_add_cancel] using sum
    have power_coprime :
        IsCoprime divisor ((prime : ℤ) ^ (depth * wait)) :=
      base_coprime.pow_right
    exact power_coprime.dvd_of_dvd_mul_left divides_scaled

/-- At every prime distinct from the base, the cancellation depth is the minimum of the terminal
and displacement depths. -/
theorem integralStep_commonFactor_padicValInt
    {prime depth factor : Nat} [Fact factor.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator : ℤ}
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator)
    (reduced_primitive : IsCoprime reducedNumerator reducedDenominator)
    (factor_base_coprime :
      IsCoprime (factor : ℤ) (prime : ℤ))
    (common_ne : common ≠ 0)
    (terminal_ne :
      terminalDefect centerNumerator driftNumerator scale
        numerator denominator ≠ 0)
    (displacement_ne :
      scale * (1 - (prime : ℤ) ^ wait) * numerator ≠ 0) :
    padicValInt factor common =
      min
        (padicValInt factor
          (terminalDefect centerNumerator driftNumerator scale
            numerator denominator))
        (padicValInt factor
          (scale * (1 - (prime : ℤ) ^ wait) * numerator)) := by
  let cancellationDepth := padicValInt factor common
  let terminalDepth :=
    padicValInt factor
      (terminalDefect centerNumerator driftNumerator scale numerator denominator)
  let displacementDepth :=
    padicValInt factor
      (scale * (1 - (prime : ℤ) ^ wait) * numerator)
  have power_base_coprime (exponent : Nat) :
      IsCoprime ((factor : ℤ) ^ exponent) (prime : ℤ) :=
    factor_base_coprime.pow_left
  have cancellation_iff (exponent : Nat) :
      (factor : ℤ) ^ exponent ∣ common ↔
        (factor : ℤ) ^ exponent ∣
            terminalDefect centerNumerator driftNumerator scale
              numerator denominator ∧
          (factor : ℤ) ^ exponent ∣
            scale * (1 - (prime : ℤ) ^ wait) * numerator :=
    integralStep_cancel_iff_terminalDefect_and_displacement step
      numerator_reduced denominator_reduced reduced_primitive
      (power_base_coprime exponent)
  apply le_antisymm
  · apply le_min
    · have divides_terminal :=
        (cancellation_iff cancellationDepth).mp
          (padicValInt_dvd common) |>.1
      exact (padicValInt_dvd_iff cancellationDepth _).mp
        divides_terminal |>.resolve_left terminal_ne
    · have divides_displacement :=
        (cancellation_iff cancellationDepth).mp
          (padicValInt_dvd common) |>.2
      exact (padicValInt_dvd_iff cancellationDepth _).mp
        divides_displacement |>.resolve_left displacement_ne
  · have divides_terminal :
        (factor : ℤ) ^ min terminalDepth displacementDepth ∣
          terminalDefect centerNumerator driftNumerator scale
            numerator denominator :=
      (padicValInt_dvd_iff _ _).mpr
        (Or.inr (min_le_left terminalDepth displacementDepth))
    have divides_displacement :
        (factor : ℤ) ^ min terminalDepth displacementDepth ∣
          scale * (1 - (prime : ℤ) ^ wait) * numerator :=
      (padicValInt_dvd_iff _ _).mpr
        (Or.inr (min_le_right terminalDepth displacementDepth))
    have divides_common :=
      (cancellation_iff (min terminalDepth displacementDepth)).mpr
        ⟨divides_terminal, divides_displacement⟩
    exact
      (padicValInt_dvd_iff (min terminalDepth displacementDepth) common).mp
        divides_common |>.resolve_left common_ne

/-- Modulo a cyclotomic factor coprime to the base, the two raw output coordinates vanish
together. -/
theorem integralStep_cyclotomic_dvd_numerator_iff_terminalDefect
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator divisor : ℤ}
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (wait_positive : 0 < wait)
    (cyclotomic_divides :
      divisor ∣ (prime : ℤ) ^ wait - 1) :
    divisor ∣ nextNumerator ↔
      divisor ∣
        terminalDefect centerNumerator driftNumerator scale
          numerator denominator := by
  have divides_negative :
      divisor ∣ 1 - (prime : ℤ) ^ wait := by
    simpa only [neg_sub] using dvd_neg.mpr cyclotomic_divides
  have divides_difference :
      divisor ∣
        (prime : ℤ) ^ (depth * wait) * nextNumerator -
          nextDenominator := by
    rw [integralStep_difference step]
    exact (divides_negative.mul_left scale).mul_right numerator
  rw [← step.2]
  constructor
  · intro divides_numerator
    have divides_scaled :
        divisor ∣
          (prime : ℤ) ^ (depth * wait) * nextNumerator :=
      divides_numerator.mul_left _
    have :
        divisor ∣
          (prime : ℤ) ^ (depth * wait) * nextNumerator -
            ((prime : ℤ) ^ (depth * wait) * nextNumerator -
              nextDenominator) :=
      dvd_sub divides_scaled divides_difference
    simpa using this
  · intro divides_denominator
    have divides_scaled :
        divisor ∣
          (prime : ℤ) ^ (depth * wait) * nextNumerator := by
      have sum := dvd_add divides_difference divides_denominator
      simpa only [sub_add_cancel] using sum
    have power_coprime :
        IsCoprime divisor ((prime : ℤ) ^ (depth * wait)) :=
      (divisor_pow_sub_one_isCoprime_base wait_positive
        cyclotomic_divides).pow_right
    exact
      power_coprime.dvd_of_dvd_mul_left divides_scaled

/-- Primitive reduction swallows an admissible cyclotomic modulus exactly when the source pair
lies on the terminal projective divisor modulo that modulus. -/
theorem integralStep_cyclotomic_cancel_iff_terminalCongruent
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator divisor : ℤ}
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator)
    (reduced_primitive : IsCoprime reducedNumerator reducedDenominator)
    (wait_positive : 0 < wait)
    (cyclotomic_divides :
      divisor ∣ (prime : ℤ) ^ wait - 1) :
    divisor ∣ common ↔
      (centerNumerator - scale) * numerator ≡
        -driftNumerator * denominator [ZMOD divisor] := by
  have base_coprime :
      IsCoprime divisor (prime : ℤ) :=
    divisor_pow_sub_one_isCoprime_base wait_positive cyclotomic_divides
  have divides_displacement :
      divisor ∣ scale * (1 - (prime : ℤ) ^ wait) * numerator := by
    have divides_negative :
        divisor ∣ 1 - (prime : ℤ) ^ wait := by
      simpa only [neg_sub] using dvd_neg.mpr cyclotomic_divides
    exact (divides_negative.mul_left scale).mul_right numerator
  rw [integralStep_cancel_iff_terminalDefect_and_displacement step
    numerator_reduced denominator_reduced reduced_primitive base_coprime,
    and_iff_left divides_displacement, Int.modEq_iff_dvd]
  constructor <;> intro divides
  · rw [show
      -driftNumerator * denominator -
          (centerNumerator - scale) * numerator =
        -terminalDefect centerNumerator driftNumerator scale
          numerator denominator by
        simp [terminalDefect]
        ring]
    exact dvd_neg.mpr divides
  · rw [show
      terminalDefect centerNumerator driftNumerator scale numerator denominator =
        -(-driftNumerator * denominator -
          (centerNumerator - scale) * numerator) by
        simp [terminalDefect]]
    exact dvd_neg.mpr divides

/-- A common divisor of the image of a primitive integer pair divides the determinant. -/
theorem commonDivisor_dvd_det
    {a b c d m n divisor : ℤ} (primitive : IsCoprime m n)
    (divides_first : divisor ∣ a * m + b * n)
    (divides_second : divisor ∣ c * m + d * n) :
    divisor ∣ a * d - b * c := by
  obtain ⟨firstQuotient, first_eq⟩ := divides_first
  obtain ⟨secondQuotient, second_eq⟩ := divides_second
  have divides_det_mul_m :
      divisor ∣ (a * d - b * c) * m := by
    refine ⟨d * firstQuotient - b * secondQuotient, ?_⟩
    calc
      (a * d - b * c) * m =
          d * (a * m + b * n) - b * (c * m + d * n) := by ring
      _ = divisor * (d * firstQuotient - b * secondQuotient) := by
        rw [first_eq, second_eq]
        ring
  have divides_det_mul_n :
      divisor ∣ (a * d - b * c) * n := by
    refine ⟨a * secondQuotient - c * firstQuotient, ?_⟩
    calc
      (a * d - b * c) * n =
          a * (c * m + d * n) - c * (a * m + b * n) := by ring
      _ = divisor * (a * secondQuotient - c * firstQuotient) := by
        rw [first_eq, second_eq]
        ring
  obtain ⟨left, right, bezout⟩ := primitive
  obtain ⟨leftQuotient, left_eq⟩ := divides_det_mul_m
  obtain ⟨rightQuotient, right_eq⟩ := divides_det_mul_n
  refine ⟨left * leftQuotient + right * rightQuotient, ?_⟩
  calc
    a * d - b * c =
        (a * d - b * c) * 1 := by ring
    _ = (a * d - b * c) * (left * m + right * n) := by rw [bezout]
    _ = left * ((a * d - b * c) * m) +
        right * ((a * d - b * c) * n) := by ring
    _ = divisor * (left * leftQuotient + right * rightQuotient) := by
      rw [left_eq, right_eq]
      ring

/-- Every common divisor after one step divides the full determinant support. -/
theorem integralStep_commonDivisor_dvd_fullSupport
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator divisor : ℤ}
    (primitive : IsCoprime numerator denominator)
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (divides_numerator : divisor ∣ nextNumerator)
    (divides_denominator : divisor ∣ nextDenominator) :
    divisor ∣
      prime ^ (depth * wait) * driftNumerator * scale *
        (1 - prime ^ wait) := by
  let power : ℤ := prime ^ (depth * wait)
  let waitPower : ℤ := prime ^ wait
  have first_divides :
      divisor ∣
        (centerNumerator - scale * waitPower) * numerator +
          driftNumerator * denominator := by
    have scaled := divides_numerator.mul_left power
    rw [step.1] at scaled
    simpa [integralStepNumerator, power, waitPower] using scaled
  have second_divides :
      divisor ∣
        (power * (centerNumerator - scale)) * numerator +
          (power * driftNumerator) * denominator := by
    have scaled := divides_denominator.mul_left power
    rw [step.2] at scaled
    convert scaled using 1
    dsimp [terminalDefect, power]
    ring
  have determinant_divides :=
    commonDivisor_dvd_det primitive first_divides second_divides
  convert determinant_divides using 1
  dsimp [power, waitPower]
  ring

/-- If the common divisor is coprime to the base, only fixed and cyclotomic factors remain. -/
theorem integralStep_commonDivisor_dvd_cyclotomicSupport
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator divisor : ℤ}
    (primitive : IsCoprime numerator denominator)
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (divides_numerator : divisor ∣ nextNumerator)
    (divides_denominator : divisor ∣ nextDenominator)
    (base_coprime : IsCoprime divisor (prime : ℤ)) :
    divisor ∣ driftNumerator * scale * (prime ^ wait - 1) := by
  have full_support :=
    integralStep_commonDivisor_dvd_fullSupport primitive step
      divides_numerator divides_denominator
  have power_coprime :
      IsCoprime divisor ((prime : ℤ) ^ (depth * wait)) :=
    base_coprime.pow_right
  have reduced :
      divisor ∣ driftNumerator * scale * (1 - (prime : ℤ) ^ wait) := by
    apply power_coprime.dvd_of_dvd_mul_left
    simpa [mul_assoc] using full_support
  rw [show
    driftNumerator * scale * ((prime : ℤ) ^ wait - 1) =
      -(driftNumerator * scale * (1 - (prime : ℤ) ^ wait)) by ring]
  exact dvd_neg.mpr reduced

/-- Away from the fixed parameter support, cancellation is exactly the intersection of the
cyclotomic divisor and the terminal projective divisor. -/
theorem integralStep_novel_cancel_iff_cyclotomic_terminalCongruent
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator divisor : ℤ}
    (primitive : IsCoprime numerator denominator)
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator)
    (reduced_primitive : IsCoprime reducedNumerator reducedDenominator)
    (wait_positive : 0 < wait)
    (base_coprime : IsCoprime divisor (prime : ℤ))
    (fixed_coprime :
      IsCoprime divisor (driftNumerator * scale)) :
    divisor ∣ common ↔
      divisor ∣ (prime : ℤ) ^ wait - 1 ∧
        (centerNumerator - scale) * numerator ≡
          -driftNumerator * denominator [ZMOD divisor] := by
  constructor
  · intro divides_common
    have divides_numerator : divisor ∣ nextNumerator := by
      rw [numerator_reduced]
      exact divides_common.mul_right reducedNumerator
    have divides_denominator : divisor ∣ nextDenominator := by
      rw [denominator_reduced]
      exact divides_common.mul_right reducedDenominator
    have support :=
      integralStep_commonDivisor_dvd_cyclotomicSupport primitive step
        divides_numerator divides_denominator base_coprime
    have cyclotomic_divides :
        divisor ∣ (prime : ℤ) ^ wait - 1 := by
      apply fixed_coprime.dvd_of_dvd_mul_left
      simpa only [mul_assoc] using support
    exact ⟨cyclotomic_divides,
      (integralStep_cyclotomic_cancel_iff_terminalCongruent step
        numerator_reduced denominator_reduced reduced_primitive
        wait_positive cyclotomic_divides).mp divides_common⟩
  · rintro ⟨cyclotomic_divides, terminal_congruent⟩
    exact
      (integralStep_cyclotomic_cancel_iff_terminalCongruent step
        numerator_reduced denominator_reduced reduced_primitive
        wait_positive cyclotomic_divides).mpr terminal_congruent

/-- A cyclotomic prime either divides the primitive-reduction factor or resets the reduced
projective pair to one. -/
theorem cyclotomic_reset_or_cancel
    {prime depth : Nat} {scale : ℤ} {wait : Nat}
    {numerator nextNumerator nextDenominator common reducedNumerator
      reducedDenominator cyclotomicPrime : ℤ}
    (difference :
      (prime : ℤ) ^ (depth * wait) * nextNumerator - nextDenominator =
        scale * (1 - (prime : ℤ) ^ wait) * numerator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator)
    (cyclotomic_prime : Prime cyclotomicPrime)
    (cyclotomic_divides :
      cyclotomicPrime ∣ (prime : ℤ) ^ wait - 1) :
    cyclotomicPrime ∣ common ∨
      cyclotomicPrime ∣ reducedNumerator - reducedDenominator := by
  have divides_power_sub_one :
      cyclotomicPrime ∣
        (prime : ℤ) ^ (depth * wait) - 1 := by
    have power_divides :
        (prime : ℤ) ^ wait - 1 ∣
          ((prime : ℤ) ^ wait) ^ depth - 1 :=
      sub_one_dvd_pow_sub_one ((prime : ℤ) ^ wait) depth
    apply cyclotomic_divides.trans
    rw [Nat.mul_comm depth wait, pow_mul]
    exact power_divides
  have divides_scaled_difference :
      cyclotomicPrime ∣
        (prime : ℤ) ^ (depth * wait) * nextNumerator -
          nextDenominator := by
    rw [difference]
    have negative :
        cyclotomicPrime ∣ 1 - (prime : ℤ) ^ wait := by
      simpa only [neg_sub] using dvd_neg.mpr cyclotomic_divides
    exact (negative.mul_left scale).mul_right numerator
  have divides_common_product :
      cyclotomicPrime ∣
        common *
          ((prime : ℤ) ^ (depth * wait) * reducedNumerator -
            reducedDenominator) := by
    simpa [numerator_reduced, denominator_reduced, mul_sub, mul_assoc,
      mul_left_comm, mul_comm] using divides_scaled_difference
  rcases cyclotomic_prime.dvd_mul.mp divides_common_product with
    cancel | residue
  · exact Or.inl cancel
  · right
    have correction :
        cyclotomicPrime ∣
          ((prime : ℤ) ^ (depth * wait) - 1) * reducedNumerator :=
      dvd_mul_of_dvd_left divides_power_sub_one reducedNumerator
    have decomposition :
        reducedNumerator - reducedDenominator =
          ((prime : ℤ) ^ (depth * wait) * reducedNumerator -
            reducedDenominator) -
          ((prime : ℤ) ^ (depth * wait) - 1) * reducedNumerator := by
      ring
    rw [decomposition]
    exact dvd_sub residue correction

/-- One actual integral guard step either swallows a cyclotomic prime in its reduction factor
or resets the reduced projective state to one modulo that prime. -/
theorem integralStep_cyclotomic_reset_or_cancel
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator cyclotomicPrime : ℤ}
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator)
    (cyclotomic_prime : Prime cyclotomicPrime)
    (cyclotomic_divides :
      cyclotomicPrime ∣ (prime : ℤ) ^ wait - 1) :
    cyclotomicPrime ∣ common ∨
      cyclotomicPrime ∣ reducedNumerator - reducedDenominator :=
  cyclotomic_reset_or_cancel
    (integralStep_difference step)
    numerator_reduced denominator_reduced cyclotomic_prime cyclotomic_divides

end
end MatrixMortality.ReturnGuard
