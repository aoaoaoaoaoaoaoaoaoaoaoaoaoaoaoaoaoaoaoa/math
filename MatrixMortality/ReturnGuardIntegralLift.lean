import MatrixMortality.ReturnGuardQuotient

/-!
# Primitive integral lifting of decoded guard dynamics

Every decoded rational step has a canonical coprime numerator-denominator presentation.
Exact branch membership forces the apparent `p^(depth * wait)` denominator scale into the
common factor of the raw rational image.  Removing that forced power therefore produces an
honest `PrimitiveIntegralStep`, not merely a projectively equivalent rational identity.

Consequently every decoded execution lifts, step for step, to primitive integral execution.
Finite quotient invariants can therefore certify physical immortality directly.
-/

namespace MatrixMortality.ReturnGuard

open MatrixMortality.PadicValuation

noncomputable section

/-- The canonical numerator and denominator of a rational are coprime over the integers. -/
theorem rat_num_den_isCoprime (value : ℚ) :
    IsCoprime value.num (value.den : ℤ) := by
  rw [Int.coprime_iff_nat_coprime]
  simpa using value.reduced

/-- A rational `p`-adic unit has denominator prime to `p` in canonical form. -/
theorem rat_denominator_not_dvd_of_isUnit
    {prime : Nat} [Fact prime.Prime] {value : ℚ}
    (unit : IsUnit prime value) :
    ¬(prime : ℤ) ∣ (value.den : ℤ) := by
  intro denominator_dvd
  have denominator_dvd_nat : prime ∣ value.den := by
    exact_mod_cast denominator_dvd
  have denominator_value_ne : padicValNat prime value.den ≠ 0 :=
    (dvd_iff_padicValNat_ne_zero value.den_ne_zero).mp denominator_dvd_nat
  have valuation_eq :
      padicValInt prime value.num = padicValNat prime value.den := by
    have valuation_zero := unit.2
    rw [padicValRat_def] at valuation_zero
    omega
  have numerator_value_ne : padicValInt prime value.num ≠ 0 := by
    rw [valuation_eq]
    exact_mod_cast denominator_value_ne
  have numerator_dvd : (prime : ℤ) ∣ value.num := by
    rw [show (prime : ℤ) = (prime : ℤ) ^ 1 by simp,
      padicValInt_dvd_iff]
    exact Or.inr (Nat.one_le_iff_ne_zero.mpr numerator_value_ne)
  obtain ⟨left, right, bezout⟩ := rat_num_den_isCoprime value
  have prime_dvd_one : (prime : ℤ) ∣ 1 := by
    rw [← bezout]
    exact dvd_add (numerator_dvd.mul_left left)
      (denominator_dvd.mul_left right)
  have prime_dvd_one_nat : prime ∣ 1 := by
    exact_mod_cast prime_dvd_one
  exact (Fact.out : prime.Prime).not_dvd_one prime_dvd_one_nat

/-- If a scaled denominator represents a rational `p`-adic unit, its full forced prime power
belongs to the common reduction factor rather than to the canonical denominator. -/
theorem primePower_dvd_common_of_unit_denominator
    {prime exponent : Nat} [Fact prime.Prime] {value : ℚ}
    (unit : IsUnit prime value) {rawDenominator common : ℤ}
    (scaled :
      (prime : ℤ) ^ exponent * rawDenominator =
        common * (value.den : ℤ)) :
    (prime : ℤ) ^ exponent ∣ common := by
  have prime_denominator_coprime :
      IsCoprime (prime : ℤ) (value.den : ℤ) := by
    rw [Int.coprime_iff_nat_coprime]
    simpa using (Fact.out : prime.Prime).coprime_iff_not_dvd.mpr
      (by
        intro divides
        exact rat_denominator_not_dvd_of_isUnit unit
          (by exact_mod_cast divides))
  have power_denominator_coprime :=
    prime_denominator_coprime.pow_left (m := exponent)
  apply power_denominator_coprime.dvd_of_dvd_mul_right
  use rawDenominator
  exact scaled.symm

/-- Clearing one decoded branch yields the raw integral numerator over the scaled terminal
defect. -/
theorem residualStep_eq_integralRatio
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    {wait : Nat} {source : ℚ}
    (branch : ResidualBranch parameters wait source) :
    residualStep parameters wait source =
      (integralStepNumerator parameters.prime centerNumerator
          driftNumerator scale wait source.num source.den : ℚ) /
        ((parameters.prime : ℤ) ^ (parameters.depth * wait) *
          terminalDefect centerNumerator driftNumerator scale
            source.num source.den) := by
  have transform_denominator_ne :=
    (centerTransform_denominator_isUnit_of_branch
      parameters wait source branch).1
  have denominator_ne : (source.den : ℚ) ≠ 0 := by
    exact_mod_cast source.den_ne_zero
  have scale_ne_rat : (scale : ℚ) ≠ 0 := by
    exact_mod_cast scale_ne
  have transform_eq :
      (parameters.center - 1) * source +
          drift parameters.center parameters.reset =
        (terminalDefect centerNumerator driftNumerator scale
          source.num source.den : ℚ) /
          (scale * source.den) := by
    rw [drift_eq, center_eq]
    conv_lhs => rw [← source.num_div_den]
    simp only [terminalDefect, Int.cast_add, Int.cast_sub, Int.cast_mul,
      Int.cast_natCast]
    field_simp [denominator_ne, scale_ne_rat]
    ring
  have numerator_eq :
      (parameters.center - parameters.prime ^ wait) * source +
          drift parameters.center parameters.reset =
        (integralStepNumerator parameters.prime centerNumerator
          driftNumerator scale wait source.num source.den : ℚ) /
          (scale * source.den) := by
    rw [drift_eq, center_eq]
    conv_lhs => rw [← source.num_div_den]
    simp only [integralStepNumerator, Int.cast_add, Int.cast_sub,
      Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    field_simp [denominator_ne, scale_ne_rat]
    ring
  have terminal_ne :
      terminalDefect centerNumerator driftNumerator scale
          source.num source.den ≠ 0 := by
    intro terminal_zero
    apply transform_denominator_ne
    rw [transform_eq, terminal_zero]
    simp
  rw [residualStep_eq parameters wait source transform_denominator_ne,
    numerator_eq, transform_eq]
  field_simp [denominator_ne, scale_ne_rat,
    primePower_ne_zero parameters.prime_prime, terminal_ne]

/-- Canonical primitive homogeneous coordinates of a rational. -/
def rationalPair (value : ℚ) : ℤ × ℤ :=
  (value.num, value.den)

@[simp]
theorem rationalPair_fst (value : ℚ) :
    (rationalPair value).1 = value.num := rfl

@[simp]
theorem rationalPair_snd (value : ℚ) :
    (rationalPair value).2 = value.den := rfl

theorem rationalPair_isCoprime (value : ℚ) :
    IsCoprime (rationalPair value).1 (rationalPair value).2 :=
  rat_num_den_isCoprime value

/-- An integral presentation whose denominator survives a prime quotient represents the same
finite projective point as the canonical rational pair. -/
theorem quotientPoint_rationalPair_eq_integral
    {factor : Nat} [Fact factor.Prime] (value : ℚ)
    {numerator denominator : ℤ}
    (denominator_ne : denominator ≠ 0)
    (value_eq : value = (numerator : ℚ) / denominator)
    (denominator_survives : (denominator : ZMod factor) ≠ 0) :
    quotientPoint factor (rationalPair value).1 (rationalPair value).2 =
      ProjectiveLine.ofPair (numerator : ZMod factor) denominator := by
  obtain ⟨common, numerator_eq, denominator_eq⟩ :=
    Rat.exists_eq_mul_div_num_and_eq_mul_div_den numerator denominator_ne
  rw [← value_eq] at numerator_eq denominator_eq
  have denominator_cast :
      (denominator : ZMod factor) =
        (common : ZMod factor) * (value.den : ZMod factor) := by
    simpa using
      congrArg (fun integer : ℤ => (integer : ZMod factor)) denominator_eq
  have common_survives : (common : ZMod factor) ≠ 0 := by
    intro common_zero
    apply denominator_survives
    rw [denominator_cast, common_zero]
    simp
  have numerator_cast :
      (numerator : ZMod factor) =
        (common : ZMod factor) * (value.num : ZMod factor) := by
    simpa using
      congrArg (fun integer : ℤ => (integer : ZMod factor)) numerator_eq
  rw [quotientPoint, rationalPair_fst, rationalPair_snd,
    numerator_cast, denominator_cast]
  simpa using
    (ProjectiveLine.ofPair_smul (common : ZMod factor) common_survives
      (value.num : ZMod factor) (value.den : ZMod factor)).symm

/-- One decoded rational step canonically lifts to one primitively reduced integral step. -/
theorem decodedStep_primitiveIntegralStep
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    {source target : ℚ}
    (decoded : DecodedStep parameters source target) :
    PrimitiveIntegralStep parameters.prime parameters.depth
      centerNumerator driftNumerator scale
      (rationalPair source) (rationalPair target) := by
  obtain ⟨wait, branch, image_eq⟩ := decoded
  let power : ℤ :=
    (parameters.prime : ℤ) ^ (parameters.depth * wait)
  let rawNumerator : ℤ :=
    integralStepNumerator parameters.prime centerNumerator
      driftNumerator scale wait source.num source.den
  let rawDenominator : ℤ :=
    terminalDefect centerNumerator driftNumerator scale source.num source.den
  have ratio_eq :
      (rawNumerator : ℚ) / (power * rawDenominator) = target := by
    rw [← image_eq]
    simpa [power, rawNumerator, rawDenominator] using
      (residualStep_eq_integralRatio parameters center_eq drift_eq
        scale_ne branch).symm
  have target_unit : IsUnit parameters.prime target :=
    image_eq ▸ residualStep_isUnit_of_branch parameters wait source branch
  have power_ne : power ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast parameters.prime_ne_zero)
  have scaledDenominator_ne : power * rawDenominator ≠ 0 := by
    intro denominator_zero
    have denominator_zero_rat :
        (power : ℚ) * rawDenominator = 0 := by
      exact_mod_cast denominator_zero
    have target_zero : target = 0 := by
      rw [← ratio_eq, denominator_zero_rat]
      simp
    exact target_unit.1 target_zero
  have ratio_eq_cast :
      (rawNumerator : ℚ) / (power * rawDenominator : ℤ) = target := by
    simpa using ratio_eq
  obtain ⟨commonScaled, numerator_eq, denominator_eq⟩ :=
    Rat.exists_eq_mul_div_num_and_eq_mul_div_den
      rawNumerator scaledDenominator_ne
  rw [ratio_eq_cast] at numerator_eq denominator_eq
  have power_dvd_commonScaled : power ∣ commonScaled := by
    apply primePower_dvd_common_of_unit_denominator target_unit
      (exponent := parameters.depth * wait)
      (rawDenominator := rawDenominator)
    simpa [power] using denominator_eq
  obtain ⟨common, commonScaled_eq⟩ := power_dvd_commonScaled
  have rawDenominator_eq :
      rawDenominator = common * target.den := by
    apply mul_left_cancel₀ power_ne
    calc
      power * rawDenominator =
          commonScaled * (target.den : ℤ) := denominator_eq
      _ = power * (common * (target.den : ℤ)) := by
        rw [commonScaled_eq]
        ring
  refine ⟨rationalPair_isCoprime source, rationalPair_isCoprime target,
    wait, common * target.num, rawDenominator, common, ?_, ?_, ?_⟩
  · refine ⟨?_, rfl⟩
    change power * (common * target.num) = rawNumerator
    rw [numerator_eq, commonScaled_eq]
    ring
  · rfl
  · exact rawDenominator_eq

/-- Exact decoded executions lift step for step to primitive integral executions. -/
theorem decodedExecution_primitiveIntegral
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    {steps : Nat} {source target : ℚ}
    (execution :
      Relation.ReachesIn (DecodedStep parameters) steps source target) :
    Relation.ReachesIn
      (PrimitiveIntegralStep parameters.prime parameters.depth
        centerNumerator driftNumerator scale)
      steps (rationalPair source) (rationalPair target) :=
  execution.map rationalPair
    (decodedStep_primitiveIntegralStep parameters center_eq drift_eq scale_ne)

/-- Blocking primitive integral execution blocks decoded rational reachability. -/
theorem not_decodedReachable_of_no_primitiveExecution
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    (blocked :
      ¬∃ steps,
        Relation.ReachesIn
          (PrimitiveIntegralStep parameters.prime parameters.depth
            centerNumerator driftNumerator scale)
          steps (rationalPair 1)
            (rationalPair (terminalResidual parameters))) :
    ¬DecodedReachable parameters := by
  intro reachable
  obtain ⟨steps, _, execution⟩ :=
    Relation.transGen_iff_exists_pos_reachesIn.mp reachable
  exact blocked ⟨steps,
    decodedExecution_primitiveIntegral parameters center_eq drift_eq
      scale_ne execution⟩

/-- A finite exact-order quotient invariant blocks the decoded rational orbit. -/
theorem not_decodedReachable_of_quotientInvariant
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    {factor period : Nat} [Fact factor.Prime]
    (primitive :
      IsPrimitivePrimeDivisor factor parameters.prime period)
    {states : Set (QuotientState (ZMod factor))}
    (closed :
      QuotientInvariant factor parameters.prime period parameters.depth
        centerNumerator driftNumerator scale states)
    (cancelled_absent : none ∉ states)
    (reset_mem :
      quotientPairState factor (rationalPair 1) ∈ states)
    (terminal_absent :
      quotientPairState factor
          (rationalPair (terminalResidual parameters)) ∉ states) :
    ¬DecodedReachable parameters := by
  apply not_decodedReachable_of_no_primitiveExecution
    parameters center_eq drift_eq scale_ne
  exact no_primitiveExecution_of_quotientInvariant
    primitive centerNumerator driftNumerator scale closed cancelled_absent
    reset_mem terminal_absent

/-- A finite exact-order quotient invariant is a certificate of physical immortality. -/
theorem not_physical_isMortal_of_quotientInvariant
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    {factor period : Nat} [Fact factor.Prime]
    (primitive :
      IsPrimitivePrimeDivisor factor parameters.prime period)
    {states : Set (QuotientState (ZMod factor))}
    (closed :
      QuotientInvariant factor parameters.prime period parameters.depth
        centerNumerator driftNumerator scale states)
    (cancelled_absent : none ∉ states)
    (reset_mem :
      quotientPairState factor (rationalPair 1) ∈ states)
    (terminal_absent :
      quotientPairState factor
          (rationalPair (terminalResidual parameters)) ∉ states) :
    ¬IsMortal
      (ReturnFamily.pairGenerator
        (ambient (parameters.prime : ℚ) parameters.depth)
        (cut parameters.center parameters.reset)) := by
  rw [physical_isMortal_iff_decodedReachable]
  exact not_decodedReachable_of_quotientInvariant parameters
    center_eq drift_eq scale_ne primitive closed cancelled_absent
    reset_mem terminal_absent

/-- A primitive divisor of the drift numerator gives a physical immortality certificate
whenever the center ratio avoids the subgroup generated by the base.  Unlike the raw integral
endpoint statement, this theorem targets the canonical reduced terminal pair and is therefore
nonvacuous without a coprimality hypothesis on the chosen coefficients. -/
theorem not_physical_isMortal_of_drift_divisor
    (parameters : Parameters)
    {centerNumerator driftNumerator scale : ℤ}
    (center_eq :
      parameters.center = (centerNumerator : ℚ) / scale)
    (drift_eq :
      drift parameters.center parameters.reset =
        (driftNumerator : ℚ) / scale)
    (scale_ne : scale ≠ 0)
    {factor period : Nat} [Fact factor.Prime]
    (primitive :
      IsPrimitivePrimeDivisor factor parameters.prime period)
    (drift_zero : (driftNumerator : ZMod factor) = 0)
    (terminal_denominator_ne :
      (centerNumerator : ZMod factor) - (scale : ZMod factor) ≠ 0)
    (residue_avoids_center :
      ∀ residue : Fin period,
        (centerNumerator : ZMod factor) -
            (scale : ZMod factor) *
              (parameters.prime : ZMod factor) ^ (residue : Nat) ≠ 0) :
    ¬IsMortal
      (ReturnFamily.pairGenerator
        (ambient (parameters.prime : ℚ) parameters.depth)
        (cut parameters.center parameters.reset)) := by
  have denominator_ne : centerNumerator - scale ≠ 0 := by
    intro denominator_zero
    apply terminal_denominator_ne
    simpa using
      congrArg (fun integer : ℤ => (integer : ZMod factor))
        denominator_zero
  have terminal_eq :
      terminalResidual parameters =
        (-driftNumerator : ℚ) / (centerNumerator - scale : ℤ) := by
    rw [terminalResidual, drift_eq, center_eq]
    have scale_ne_rat : (scale : ℚ) ≠ 0 := by
      exact_mod_cast scale_ne
    have denominator_ne_rat :
        (centerNumerator - scale : ℚ) ≠ 0 := by
      exact_mod_cast denominator_ne
    rw [show
      (centerNumerator : ℚ) / scale - 1 =
        (centerNumerator - scale : ℤ) / scale by
          field_simp [scale_ne_rat]]
    field_simp [scale_ne_rat, denominator_ne_rat]
    ring
  have terminal_state_eq :
      quotientPairState factor
          (rationalPair (terminalResidual parameters)) =
        quotientPairState factor
          (-driftNumerator, centerNumerator - scale) := by
    change
      some
          (quotientPoint factor
            (rationalPair (terminalResidual parameters)).1
            (rationalPair (terminalResidual parameters)).2) =
        some
          (quotientPoint factor (-driftNumerator)
            (centerNumerator - scale))
    congr 1
    exact quotientPoint_rationalPair_eq_integral
      (terminalResidual parameters) denominator_ne terminal_eq
      (by simpa only [Int.cast_sub] using terminal_denominator_ne)
  apply not_physical_isMortal_of_quotientInvariant parameters
    center_eq drift_eq scale_ne primitive
    (affineSurvivors_quotientInvariant drift_zero
      (by
        intro base_zero
        have factor_dvd_base : factor ∣ parameters.prime :=
          (ZMod.natCast_zmod_eq_zero_iff_dvd parameters.prime factor).mp
            base_zero
        exact primitivePrimeDivisor_not_dvd_base_int primitive
          (by exact_mod_cast factor_dvd_base))
      terminal_denominator_ne residue_avoids_center)
    (by simp [AffineSurvivors])
  · simpa [rationalPair] using
      quotientPairState_one_mem_affineSurvivors factor
  · rw [terminal_state_eq]
    exact quotientPairState_terminal_not_mem_affineSurvivors
      drift_zero terminal_denominator_ne

end
end MatrixMortality.ReturnGuard
