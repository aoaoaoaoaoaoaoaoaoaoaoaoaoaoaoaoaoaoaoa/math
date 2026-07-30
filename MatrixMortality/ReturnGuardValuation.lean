import MatrixMortality.ReturnGuardArithmetic
import Mathlib.NumberTheory.Multiplicity

/-!
# Prime-local bounds for guard cancellation

The exact cancellation law contains the source numerator in its displacement term.  On a
primitive source pair, determinant support eliminates that apparent unbounded contribution:
every cancellation factor coprime to the base divides `D L (p^a - 1)`.  Lifting the exponent
then makes each fixed odd-prime contribution logarithmic in the wait multiplier.
-/

namespace MatrixMortality.ReturnGuard

noncomputable section

/-- Integer p-adic valuation is insensitive to sign. -/
theorem padicValInt_neg (factor : Nat) (value : ℤ) :
    padicValInt factor (-value) = padicValInt factor value := by
  simp [padicValInt]

/-- The integer valuation of a positive power-minus-one is its natural valuation. -/
theorem padicValInt_pow_sub_one
    {factor base exponent : Nat}
    (power_gt_one : 1 < base ^ exponent) :
    padicValInt factor ((base : ℤ) ^ exponent - 1) =
      padicValNat factor (base ^ exponent - 1) := by
  rw [← padicValInt.of_nat]
  congr 1
  rw [Int.natCast_sub (Nat.one_le_iff_ne_zero.mpr (by omega))]
  norm_num

/-- The displacement valuation separates into the scale, cyclotomic, and source depths. -/
theorem padicValInt_displacement
    {factor base wait : Nat} [Fact factor.Prime]
    {scale numerator : ℤ}
    (scale_ne : scale ≠ 0)
    (cyclotomic_ne : (base : ℤ) ^ wait - 1 ≠ 0)
    (numerator_ne : numerator ≠ 0) :
    padicValInt factor
        (scale * (1 - (base : ℤ) ^ wait) * numerator) =
      padicValInt factor scale +
        padicValInt factor ((base : ℤ) ^ wait - 1) +
          padicValInt factor numerator := by
  have negative_cyclotomic_ne : 1 - (base : ℤ) ^ wait ≠ 0 := by
    rw [show 1 - (base : ℤ) ^ wait = -((base : ℤ) ^ wait - 1) by ring]
    exact neg_ne_zero.mpr cyclotomic_ne
  calc
    padicValInt factor
        (scale * (1 - (base : ℤ) ^ wait) * numerator) =
      padicValInt factor (scale * (1 - (base : ℤ) ^ wait)) +
        padicValInt factor numerator :=
          padicValInt.mul
            (mul_ne_zero scale_ne negative_cyclotomic_ne) numerator_ne
    _ =
      padicValInt factor scale +
          padicValInt factor (1 - (base : ℤ) ^ wait) +
        padicValInt factor numerator := by
          rw [padicValInt.mul scale_ne negative_cyclotomic_ne]
    _ =
      padicValInt factor scale +
        padicValInt factor ((base : ℤ) ^ wait - 1) +
          padicValInt factor numerator := by
            rw [show 1 - (base : ℤ) ^ wait =
              -((base : ℤ) ^ wait - 1) by ring, padicValInt_neg]

/-- The complete cancellation formula with the displacement valuation fully separated. -/
theorem integralStep_commonFactor_padicValInt_expanded
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
    (scale_ne : scale ≠ 0)
    (cyclotomic_ne : (prime : ℤ) ^ wait - 1 ≠ 0)
    (numerator_ne : numerator ≠ 0) :
    padicValInt factor common =
      min
        (padicValInt factor
          (terminalDefect centerNumerator driftNumerator scale
            numerator denominator))
        (padicValInt factor scale +
          padicValInt factor ((prime : ℤ) ^ wait - 1) +
            padicValInt factor numerator) := by
  rw [integralStep_commonFactor_padicValInt step numerator_reduced
    denominator_reduced reduced_primitive factor_base_coprime common_ne
    terminal_ne
    (mul_ne_zero (mul_ne_zero scale_ne
      (by
        rw [show 1 - (prime : ℤ) ^ wait =
          -((prime : ℤ) ^ wait - 1) by ring]
        exact neg_ne_zero.mpr cyclotomic_ne)) numerator_ne)]
  exact congrArg (min _) <|
    padicValInt_displacement scale_ne cyclotomic_ne numerator_ne

/-- Divisibility between nonzero integers is monotone for prime-adic valuation. -/
theorem padicValInt_le_of_dvd
    {factor : Nat} [Fact factor.Prime] {left right : ℤ}
    (right_ne : right ≠ 0)
    (divides : left ∣ right) :
    padicValInt factor left ≤ padicValInt factor right := by
  have power_divides :
      (factor : ℤ) ^ padicValInt factor left ∣ right :=
    (padicValInt_dvd left).trans divides
  exact (padicValInt_dvd_iff _ right).mp power_divides |>.resolve_left right_ne

/-- A primitive source removes the source numerator from the size bound: every fixed-prime
cancellation depth is bounded by the determinant support `D L (p^a - 1)`. -/
theorem integralStep_commonFactor_padicValInt_le_support
    {prime depth factor : Nat} [Fact factor.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator : ℤ}
    (source_primitive : IsCoprime numerator denominator)
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator)
    (common_base_coprime : IsCoprime common (prime : ℤ))
    (drift_ne : driftNumerator ≠ 0)
    (scale_ne : scale ≠ 0)
    (cyclotomic_ne : (prime : ℤ) ^ wait - 1 ≠ 0) :
    padicValInt factor common ≤
      padicValInt factor driftNumerator +
        padicValInt factor scale +
          padicValInt factor ((prime : ℤ) ^ wait - 1) := by
  have divides_numerator : common ∣ nextNumerator := by
    rw [numerator_reduced]
    exact ⟨reducedNumerator, rfl⟩
  have divides_denominator : common ∣ nextDenominator := by
    rw [denominator_reduced]
    exact ⟨reducedDenominator, rfl⟩
  have support_divides :
      common ∣
        driftNumerator * scale * ((prime : ℤ) ^ wait - 1) :=
    integralStep_commonDivisor_dvd_cyclotomicSupport source_primitive
      step divides_numerator divides_denominator common_base_coprime
  have support_ne :
      driftNumerator * scale * ((prime : ℤ) ^ wait - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero drift_ne scale_ne) cyclotomic_ne
  calc
    padicValInt factor common ≤
      padicValInt factor
        (driftNumerator * scale * ((prime : ℤ) ^ wait - 1)) :=
          padicValInt_le_of_dvd support_ne support_divides
    _ =
      padicValInt factor driftNumerator +
        padicValInt factor scale +
          padicValInt factor ((prime : ℤ) ^ wait - 1) := by
            rw [padicValInt.mul (mul_ne_zero drift_ne scale_ne)
              cyclotomic_ne, padicValInt.mul drift_ne scale_ne]

/-- Globally, a base-coprime primitive-reduction factor is at most the determinant support.
The variable part has size only `p^a - 1`, not `p^(s a)`. -/
theorem integralStep_commonFactor_natAbs_le_support
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator : ℤ}
    (source_primitive : IsCoprime numerator denominator)
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator)
    (common_base_coprime : IsCoprime common (prime : ℤ))
    (drift_ne : driftNumerator ≠ 0)
    (scale_ne : scale ≠ 0)
    (cyclotomic_ne : (prime : ℤ) ^ wait - 1 ≠ 0) :
    common.natAbs ≤
      driftNumerator.natAbs * scale.natAbs *
        ((prime : ℤ) ^ wait - 1).natAbs := by
  have divides_numerator : common ∣ nextNumerator := by
    rw [numerator_reduced]
    exact ⟨reducedNumerator, rfl⟩
  have divides_denominator : common ∣ nextDenominator := by
    rw [denominator_reduced]
    exact ⟨reducedDenominator, rfl⟩
  have support_divides :
      common ∣
        driftNumerator * scale * ((prime : ℤ) ^ wait - 1) :=
    integralStep_commonDivisor_dvd_cyclotomicSupport source_primitive
      step divides_numerator divides_denominator common_base_coprime
  have support_ne :
      driftNumerator * scale * ((prime : ℤ) ^ wait - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero drift_ne scale_ne) cyclotomic_ne
  simpa only [Int.natAbs_mul] using
    Int.natAbs_le_of_dvd_ne_zero support_divides support_ne

/-- Archimedean height of an integral projective pair. -/
def integralPairHeight (numerator denominator : ℤ) : Nat :=
  max numerator.natAbs denominator.natAbs

/-- The unscaled step numerator is bounded linearly in the source height, with the wait appearing
only through `p^a`. -/
theorem integralStepNumerator_natAbs_le_height
    (prime : Nat) (centerNumerator driftNumerator scale : ℤ)
    (wait : Nat) (numerator denominator : ℤ) :
    (integralStepNumerator prime centerNumerator driftNumerator scale
        wait numerator denominator).natAbs ≤
      (centerNumerator.natAbs + driftNumerator.natAbs +
          scale.natAbs * prime ^ wait) *
        integralPairHeight numerator denominator := by
  have coefficient_le :
      (centerNumerator - scale * (prime : ℤ) ^ wait).natAbs ≤
        centerNumerator.natAbs + scale.natAbs * prime ^ wait := by
    calc
      (centerNumerator - scale * (prime : ℤ) ^ wait).natAbs ≤
          centerNumerator.natAbs +
            (scale * (prime : ℤ) ^ wait).natAbs :=
        Int.natAbs_sub_le _ _
      _ = centerNumerator.natAbs + scale.natAbs * prime ^ wait := by
        simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_ofNat]
  have numerator_le :
      numerator.natAbs ≤ integralPairHeight numerator denominator :=
    le_max_left _ _
  have denominator_le :
      denominator.natAbs ≤ integralPairHeight numerator denominator :=
    le_max_right _ _
  calc
    (integralStepNumerator prime centerNumerator driftNumerator scale
        wait numerator denominator).natAbs ≤
      (centerNumerator - scale * (prime : ℤ) ^ wait).natAbs *
          numerator.natAbs +
        driftNumerator.natAbs * denominator.natAbs := by
          simpa only [integralStepNumerator, Int.natAbs_mul] using
            Int.natAbs_add_le
              ((centerNumerator - scale * (prime : ℤ) ^ wait) *
                numerator)
              (driftNumerator * denominator)
    _ ≤
      (centerNumerator.natAbs + scale.natAbs * prime ^ wait) *
          integralPairHeight numerator denominator +
        driftNumerator.natAbs *
          integralPairHeight numerator denominator :=
      Nat.add_le_add
        (Nat.mul_le_mul coefficient_le numerator_le)
        (Nat.mul_le_mul_left driftNumerator.natAbs denominator_le)
    _ =
      (centerNumerator.natAbs + driftNumerator.natAbs +
          scale.natAbs * prime ^ wait) *
        integralPairHeight numerator denominator := by ring

/-- A nonzero next numerator forces the full base power to fit inside the current unscaled
numerator. -/
theorem integralStep_power_le_numerator_natAbs
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator : ℤ}
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (nextNumerator_ne : nextNumerator ≠ 0) :
    prime ^ (depth * wait) ≤
      (integralStepNumerator prime centerNumerator driftNumerator scale
        wait numerator denominator).natAbs := by
  have nextNumerator_positive : 0 < nextNumerator.natAbs :=
    Int.natAbs_pos.mpr nextNumerator_ne
  calc
    prime ^ (depth * wait) ≤
        prime ^ (depth * wait) * nextNumerator.natAbs :=
      Nat.le_mul_of_pos_right _ nextNumerator_positive
    _ =
      (integralStepNumerator prime centerNumerator driftNumerator scale
        wait numerator denominator).natAbs := by
          rw [← step.1]
          simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_ofNat]

/-- For depth at least two, every legal nonzero step has wait logarithmic in the current
integral height. -/
theorem integralStep_wait_le_log_height
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator : ℤ}
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (nextNumerator_ne : nextNumerator ≠ 0)
    (prime_gt_one : 1 < prime)
    (depth_two_le : 2 ≤ depth) :
    wait ≤
      Nat.log prime
        ((centerNumerator.natAbs + driftNumerator.natAbs +
            scale.natAbs) *
          integralPairHeight numerator denominator) := by
  let height := integralPairHeight numerator denominator
  let coefficient :=
    centerNumerator.natAbs + driftNumerator.natAbs + scale.natAbs
  have wait_power_positive : 0 < prime ^ wait :=
    Nat.pow_pos (lt_trans Nat.zero_lt_one prime_gt_one)
  have coefficient_wait_le :
      centerNumerator.natAbs + driftNumerator.natAbs +
          scale.natAbs * prime ^ wait ≤
        coefficient * prime ^ wait := by
    dsimp [coefficient]
    have center_le :
        centerNumerator.natAbs ≤
          centerNumerator.natAbs * prime ^ wait :=
      Nat.le_mul_of_pos_right _ wait_power_positive
    have drift_le :
        driftNumerator.natAbs ≤
          driftNumerator.natAbs * prime ^ wait :=
      Nat.le_mul_of_pos_right _ wait_power_positive
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
  have full_power_le :
      prime ^ (depth * wait) ≤
        (centerNumerator.natAbs + driftNumerator.natAbs +
            scale.natAbs * prime ^ wait) * height :=
    (integralStep_power_le_numerator_natAbs step nextNumerator_ne).trans
      (integralStepNumerator_natAbs_le_height prime centerNumerator
        driftNumerator scale wait numerator denominator)
  have split_power_le :
      prime ^ wait * prime ^ ((depth - 1) * wait) ≤
        prime ^ wait * (coefficient * height) := by
    have one_le_depth : 1 ≤ depth :=
      le_trans (by decide) depth_two_le
    have depth_decomp : depth - 1 + 1 = depth :=
      Nat.sub_add_cancel one_le_depth
    have exponent_eq :
        wait + (depth - 1) * wait = depth * wait := by
      calc
        wait + (depth - 1) * wait =
            (depth - 1 + 1) * wait := by ring
        _ = depth * wait := by rw [depth_decomp]
    calc
      prime ^ wait * prime ^ ((depth - 1) * wait) =
          prime ^ (depth * wait) := by
            rw [← pow_add]
            rw [exponent_eq]
      _ ≤
          (centerNumerator.natAbs + driftNumerator.natAbs +
              scale.natAbs * prime ^ wait) * height :=
        full_power_le
      _ ≤ coefficient * prime ^ wait * height :=
        Nat.mul_le_mul_right height coefficient_wait_le
      _ = prime ^ wait * (coefficient * height) := by ring
  have remaining_power_le :
      prime ^ ((depth - 1) * wait) ≤ coefficient * height :=
    Nat.le_of_mul_le_mul_left split_power_le wait_power_positive
  have wait_le_remaining : wait ≤ (depth - 1) * wait := by
    apply Nat.le_mul_of_pos_left
    omega
  exact wait_le_remaining.trans
    (Nat.le_log_of_pow_le prime_gt_one remaining_power_le)

/-- Before primitive reduction, one legal step increases integral height by at most the fixed
parameter coefficient sum, independently of the wait. -/
theorem integralStep_next_height_le
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator : ℤ}
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (prime_positive : 0 < prime)
    (depth_positive : 0 < depth) :
    integralPairHeight nextNumerator nextDenominator ≤
      (centerNumerator.natAbs + driftNumerator.natAbs +
          scale.natAbs) *
        integralPairHeight numerator denominator := by
  let height := integralPairHeight numerator denominator
  let coefficient :=
    centerNumerator.natAbs + driftNumerator.natAbs + scale.natAbs
  let fullPower := prime ^ (depth * wait)
  have fullPower_positive : 0 < fullPower :=
    Nat.pow_pos prime_positive
  have wait_le_full : wait ≤ depth * wait :=
    Nat.le_mul_of_pos_left wait depth_positive
  have waitPower_le_fullPower :
      prime ^ wait ≤ fullPower :=
    Nat.pow_le_pow_right prime_positive wait_le_full
  have coefficient_wait_le :
      centerNumerator.natAbs + driftNumerator.natAbs +
          scale.natAbs * prime ^ wait ≤
        coefficient * fullPower := by
    dsimp [coefficient]
    have center_le :
        centerNumerator.natAbs ≤ centerNumerator.natAbs * fullPower :=
      Nat.le_mul_of_pos_right _ fullPower_positive
    have drift_le :
        driftNumerator.natAbs ≤ driftNumerator.natAbs * fullPower :=
      Nat.le_mul_of_pos_right _ fullPower_positive
    calc
      centerNumerator.natAbs + driftNumerator.natAbs +
          scale.natAbs * prime ^ wait ≤
        centerNumerator.natAbs * fullPower +
            driftNumerator.natAbs * fullPower +
          scale.natAbs * fullPower :=
        Nat.add_le_add (Nat.add_le_add center_le drift_le)
          (Nat.mul_le_mul_left scale.natAbs waitPower_le_fullPower)
      _ = coefficient * fullPower := by
        dsimp [coefficient]
        ring
  have nextNumerator_le :
      nextNumerator.natAbs ≤ coefficient * height := by
    have scaled_le :
        fullPower * nextNumerator.natAbs ≤
          fullPower * (coefficient * height) := by
      calc
        fullPower * nextNumerator.natAbs =
            (integralStepNumerator prime centerNumerator driftNumerator scale
              wait numerator denominator).natAbs := by
                dsimp [fullPower]
                rw [← step.1]
                simp only [Int.natAbs_mul, Int.natAbs_pow,
                  Int.natAbs_ofNat]
        _ ≤
            (centerNumerator.natAbs + driftNumerator.natAbs +
                scale.natAbs * prime ^ wait) * height :=
          integralStepNumerator_natAbs_le_height prime centerNumerator
            driftNumerator scale wait numerator denominator
        _ ≤ coefficient * fullPower * height :=
          Nat.mul_le_mul_right height coefficient_wait_le
        _ = fullPower * (coefficient * height) := by ring
    exact Nat.le_of_mul_le_mul_left scaled_le fullPower_positive
  have nextDenominator_le :
      nextDenominator.natAbs ≤ coefficient * height := by
    calc
      nextDenominator.natAbs =
          (terminalDefect centerNumerator driftNumerator scale
            numerator denominator).natAbs := by rw [step.2]
      _ ≤
          (centerNumerator - scale).natAbs * numerator.natAbs +
            driftNumerator.natAbs * denominator.natAbs := by
              simpa only [terminalDefect, Int.natAbs_mul] using
                Int.natAbs_add_le ((centerNumerator - scale) * numerator)
                  (driftNumerator * denominator)
      _ ≤
          (centerNumerator.natAbs + scale.natAbs) * height +
            driftNumerator.natAbs * height :=
        Nat.add_le_add
          (Nat.mul_le_mul (Int.natAbs_sub_le _ _) (le_max_left _ _))
          (Nat.mul_le_mul_left driftNumerator.natAbs (le_max_right _ _))
      _ = coefficient * height := by
        dsimp [coefficient]
        ring
  exact max_le nextNumerator_le nextDenominator_le

/-- Primitive reduction cannot increase height, so the same fixed Lipschitz bound holds for the
reduced orbit. -/
theorem integralStep_reduced_height_le
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator : ℤ}
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator)
    (common_ne : common ≠ 0)
    (prime_positive : 0 < prime)
    (depth_positive : 0 < depth) :
    integralPairHeight reducedNumerator reducedDenominator ≤
      (centerNumerator.natAbs + driftNumerator.natAbs +
          scale.natAbs) *
        integralPairHeight numerator denominator := by
  have common_positive : 0 < common.natAbs :=
    Int.natAbs_pos.mpr common_ne
  have reducedNumerator_le :
      reducedNumerator.natAbs ≤ nextNumerator.natAbs := by
    rw [numerator_reduced, Int.natAbs_mul]
    exact Nat.le_mul_of_pos_left _ common_positive
  have reducedDenominator_le :
      reducedDenominator.natAbs ≤ nextDenominator.natAbs := by
    rw [denominator_reduced, Int.natAbs_mul]
    exact Nat.le_mul_of_pos_left _ common_positive
  exact
    (max_le_max reducedNumerator_le reducedDenominator_le).trans
      (integralStep_next_height_le step prime_positive depth_positive)

/-- If the exponent is prime to the valuation prime, taking that power does not deepen an
existing difference. -/
theorem padicValNat_pow_sub_pow_of_exponent_coprime
    {factor left right exponent : Nat} [Fact factor.Prime]
    (right_lt_left : right < left)
    (factor_divides : factor ∣ left - right)
    (factor_not_dvd_left : ¬factor ∣ left)
    (factor_not_dvd_exponent : ¬factor ∣ exponent) :
    padicValNat factor (left ^ exponent - right ^ exponent) =
      padicValNat factor (left - right) := by
  have exponent_ne : exponent ≠ 0 := by
    intro exponent_eq
    apply factor_not_dvd_exponent
    simp [exponent_eq]
  rw [← PartENat.natCast_inj]
  iterate 2 rw [padicValNat_def, PartENat.natCast_get]
  · iterate 2 rw [← multiplicity.Int.natCast_multiplicity]
    rw [Int.ofNat_sub
      (Nat.pow_le_pow_left (Nat.le_of_lt right_lt_left) exponent),
      Int.ofNat_sub (Nat.le_of_lt right_lt_left)]
    push_cast
    apply multiplicity.pow_sub_pow_of_prime
      (Nat.prime_iff_prime_int.mp Fact.out)
    · rw [← Int.natCast_sub (Nat.le_of_lt right_lt_left)]
      exact Int.natCast_dvd_natCast.mpr factor_divides
    · exact_mod_cast factor_not_dvd_left
    · exact_mod_cast factor_not_dvd_exponent
  · exact Nat.sub_pos_of_lt right_lt_left
  · exact Nat.sub_pos_of_lt
      (Nat.pow_lt_pow_left right_lt_left exponent_ne)

/-- Odd-prime lifting of the exponent for a wait that is a multiple of one seed period. -/
theorem padicValNat_pow_mul_sub_one
    {factor base period multiplier : Nat} [Fact factor.Prime]
    (factor_odd : Odd factor)
    (period_power_gt_one : 1 < base ^ period)
    (factor_divides_period :
      factor ∣ base ^ period - 1)
    (factor_not_dvd_base : ¬factor ∣ base)
    (multiplier_ne : multiplier ≠ 0) :
    padicValNat factor (base ^ (period * multiplier) - 1) =
      padicValNat factor (base ^ period - 1) +
        padicValNat factor multiplier := by
  have factor_not_dvd_period_power : ¬factor ∣ base ^ period :=
    fun divides ↦
      factor_not_dvd_base
        ((Fact.out : factor.Prime).dvd_of_dvd_pow divides)
  simpa only [pow_mul, one_pow] using
    padicValNat.pow_sub_pow factor_odd period_power_gt_one
      factor_divides_period factor_not_dvd_period_power multiplier_ne

/-- At an odd fixed prime, the contribution of a repeated seed period grows at most
logarithmically in the wait multiplier. -/
theorem padicValNat_pow_mul_sub_one_le
    {factor base period multiplier : Nat} [Fact factor.Prime]
    (factor_odd : Odd factor)
    (period_power_gt_one : 1 < base ^ period)
    (factor_divides_period :
      factor ∣ base ^ period - 1)
    (factor_not_dvd_base : ¬factor ∣ base)
    (multiplier_ne : multiplier ≠ 0) :
    padicValNat factor (base ^ (period * multiplier) - 1) ≤
      padicValNat factor (base ^ period - 1) +
        Nat.log factor multiplier := by
  rw [padicValNat_pow_mul_sub_one factor_odd period_power_gt_one
    factor_divides_period factor_not_dvd_base multiplier_ne]
  exact Nat.add_le_add_left (padicValNat_le_nat_log multiplier) _

/-- Integer form of the logarithmic odd-prime wait bound. -/
theorem padicValInt_pow_mul_sub_one_le
    {factor base period multiplier : Nat} [Fact factor.Prime]
    (factor_odd : Odd factor)
    (period_power_gt_one : 1 < base ^ period)
    (factor_divides_period :
      factor ∣ base ^ period - 1)
    (factor_not_dvd_base : ¬factor ∣ base)
    (multiplier_ne : multiplier ≠ 0) :
    padicValInt factor
        ((base : ℤ) ^ (period * multiplier) - 1) ≤
      padicValNat factor (base ^ period - 1) +
        Nat.log factor multiplier := by
  rw [padicValInt_pow_sub_one (by
    rw [pow_mul]
    exact Nat.one_lt_pow multiplier_ne period_power_gt_one)]
  exact padicValNat_pow_mul_sub_one_le factor_odd period_power_gt_one
    factor_divides_period factor_not_dvd_base multiplier_ne

/-- The two-adic contribution of a repeated odd seed period is also logarithmic in the wait
multiplier. -/
theorem padicValNat_two_pow_mul_sub_one_le
    {base period multiplier : Nat}
    (period_power_gt_one : 1 < base ^ period)
    (period_power_odd : Odd (base ^ period))
    (multiplier_ne : multiplier ≠ 0) :
    padicValNat 2 (base ^ (period * multiplier) - 1) ≤
      padicValNat 2 (base ^ period + 1) +
        padicValNat 2 (base ^ period - 1) +
          Nat.log 2 multiplier := by
  have two_divides_period :
      2 ∣ base ^ period - 1 := by
    obtain ⟨half, half_eq⟩ := period_power_odd
    refine ⟨half, ?_⟩
    omega
  have two_not_dvd_period : ¬2 ∣ base ^ period :=
    period_power_odd.not_two_dvd_nat
  rcases Nat.even_or_odd multiplier with multiplier_even | multiplier_odd
  · have lifted :=
      padicValNat.pow_two_sub_pow period_power_gt_one
        two_divides_period two_not_dvd_period multiplier_ne
        multiplier_even
    rw [← pow_mul, one_pow] at lifted
    calc
      padicValNat 2 (base ^ (period * multiplier) - 1) ≤
          padicValNat 2 (base ^ (period * multiplier) - 1) + 1 :=
        Nat.le_succ _
      _ =
          padicValNat 2 (base ^ period + 1) +
            padicValNat 2 (base ^ period - 1) +
              padicValNat 2 multiplier := lifted
      _ ≤
          padicValNat 2 (base ^ period + 1) +
            padicValNat 2 (base ^ period - 1) +
              Nat.log 2 multiplier :=
        Nat.add_le_add_left (padicValNat_le_nat_log multiplier) _
  · have lifted :=
      padicValNat_pow_sub_pow_of_exponent_coprime period_power_gt_one
        two_divides_period two_not_dvd_period
        multiplier_odd.not_two_dvd_nat
    rw [← pow_mul, one_pow] at lifted
    rw [lifted]
    omega

/-- Integer form of the logarithmic two-adic wait bound. -/
theorem padicValInt_two_pow_mul_sub_one_le
    {base period multiplier : Nat}
    (period_power_gt_one : 1 < base ^ period)
    (period_power_odd : Odd (base ^ period))
    (multiplier_ne : multiplier ≠ 0) :
    padicValInt 2
        ((base : ℤ) ^ (period * multiplier) - 1) ≤
      padicValNat 2 (base ^ period + 1) +
        padicValNat 2 (base ^ period - 1) +
          Nat.log 2 multiplier := by
  rw [padicValInt_pow_sub_one (by
    rw [pow_mul]
    exact Nat.one_lt_pow multiplier_ne period_power_gt_one)]
  exact padicValNat_two_pow_mul_sub_one_le period_power_gt_one
    period_power_odd multiplier_ne

end
end MatrixMortality.ReturnGuard
