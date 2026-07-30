import MatrixMortality.PrimitiveDivisor
import MatrixMortality.ReturnGuardValuation

/-!
# Primitive-factor gates for guarded return dynamics

A legal integral guard step has two mutually exclusive ways to dispose of a cyclotomic prime:
primitive reduction swallows it, or the reduced projective state becomes one modulo that prime.
This file assembles those prime-local alternatives into one finite-family theorem.

The resulting gate is deliberately archimedean.  If the product of a family of swallowed,
pairwise-coprime primes is larger than the source terminal defect, divisibility forces the
terminal defect to vanish over the integers.  Otherwise at least one prime survives and gives a
finite projective reset certificate.
-/

namespace MatrixMortality.ReturnGuard

noncomputable section

/-- Prime factors of the cyclotomic value which do not divide the exponent.  Every member is a
primitive prime divisor of `base ^ exponent - 1`. -/
def primitiveCyclotomicPrimes (base exponent : Nat) : Finset Nat :=
  (cyclotomicValue base exponent).primeFactors.filter fun factor =>
    ¬factor ∣ exponent

/-- Squarefree product of the primitive prime divisors visible in the cyclotomic value. -/
def primitiveCyclotomicRadical (base exponent : Nat) : Nat :=
  ∏ factor ∈ primitiveCyclotomicPrimes base exponent, factor

theorem mem_primitiveCyclotomicPrimes
    {factor base exponent : Nat} :
    factor ∈ primitiveCyclotomicPrimes base exponent ↔
      factor ∈ (cyclotomicValue base exponent).primeFactors ∧
        ¬factor ∣ exponent := by
  simp [primitiveCyclotomicPrimes]

/-- Membership in the filtered cyclotomic support supplies the full exact-order certificate. -/
theorem primitivePrimeDivisor_of_mem_primitiveCyclotomicPrimes
    {factor base exponent : Nat}
    (base_gt_one : 1 < base) (exponent_positive : 0 < exponent)
    (member : factor ∈ primitiveCyclotomicPrimes base exponent) :
    IsPrimitivePrimeDivisor factor base exponent := by
  rw [mem_primitiveCyclotomicPrimes] at member
  exact primitivePrimeDivisor_of_prime_dvd_cyclotomicValue
    (Nat.prime_of_mem_primeFactors member.1) base_gt_one exponent_positive
    (Nat.dvd_of_mem_primeFactors member.1) member.2

/-- The terminal defect is bounded by a fixed coefficient times primitive projective height. -/
theorem terminalDefect_natAbs_le_height
    (centerNumerator driftNumerator scale numerator denominator : ℤ) :
    (terminalDefect centerNumerator driftNumerator scale
        numerator denominator).natAbs ≤
      ((centerNumerator - scale).natAbs + driftNumerator.natAbs) *
        integralPairHeight numerator denominator := by
  calc
    (terminalDefect centerNumerator driftNumerator scale
        numerator denominator).natAbs ≤
      (centerNumerator - scale).natAbs * numerator.natAbs +
        driftNumerator.natAbs * denominator.natAbs := by
          simpa only [terminalDefect, Int.natAbs_mul] using
            Int.natAbs_add_le
              ((centerNumerator - scale) * numerator)
              (driftNumerator * denominator)
    _ ≤
      (centerNumerator - scale).natAbs *
          integralPairHeight numerator denominator +
        driftNumerator.natAbs *
          integralPairHeight numerator denominator :=
      Nat.add_le_add
        (Nat.mul_le_mul_left _ (le_max_left _ _))
        (Nat.mul_le_mul_left _ (le_max_right _ _))
    _ =
      ((centerNumerator - scale).natAbs + driftNumerator.natAbs) *
        integralPairHeight numerator denominator := by ring

/-- Any swallowed divisor larger than the terminal defect certifies an actual terminal point. -/
theorem terminalDefect_eq_zero_of_large_commonDivisor
    {centerNumerator driftNumerator scale numerator denominator
      nextDenominator common reducedDenominator divisor : ℤ}
    (next_denominator :
      nextDenominator =
        terminalDefect centerNumerator driftNumerator scale numerator denominator)
    (denominator_reduced :
      nextDenominator = common * reducedDenominator)
    (divides_common : divisor ∣ common)
    (large :
      (terminalDefect centerNumerator driftNumerator scale
        numerator denominator).natAbs < divisor.natAbs) :
    terminalDefect centerNumerator driftNumerator scale numerator denominator = 0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs _ large
  rw [← next_denominator, denominator_reduced]
  exact divides_common.mul_right reducedDenominator

/-- Away from the terminal divisor, every swallowed factor is bounded by source height. -/
theorem swallowedDivisor_natAbs_le_height
    {centerNumerator driftNumerator scale numerator denominator
      nextDenominator common reducedDenominator divisor : ℤ}
    (next_denominator :
      nextDenominator =
        terminalDefect centerNumerator driftNumerator scale numerator denominator)
    (denominator_reduced :
      nextDenominator = common * reducedDenominator)
    (divides_common : divisor ∣ common)
    (nonterminal :
      terminalDefect centerNumerator driftNumerator scale numerator denominator ≠ 0) :
    divisor.natAbs ≤
      ((centerNumerator - scale).natAbs + driftNumerator.natAbs) *
        integralPairHeight numerator denominator := by
  apply (Int.natAbs_le_of_dvd_ne_zero _ nonterminal).trans
    (terminalDefect_natAbs_le_height centerNumerator driftNumerator scale
      numerator denominator)
  rw [← next_denominator, denominator_reduced]
  exact divides_common.mul_right reducedDenominator

/-- A sufficiently large finite family of cyclotomic primes either detects the true terminal
divisor or contains a surviving prime which resets the reduced projective state to one. -/
theorem terminal_or_exists_cyclotomic_reset
    {prime depth wait : Nat} {scale numerator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator : ℤ}
    {factors : Finset Nat}
    (difference :
      (prime : ℤ) ^ (depth * wait) * nextNumerator - nextDenominator =
        scale * (1 - (prime : ℤ) ^ wait) * numerator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator)
    (factor_prime : ∀ factor ∈ factors, factor.Prime)
    (factor_cyclotomic :
      ∀ factor ∈ factors, (factor : ℤ) ∣ (prime : ℤ) ^ wait - 1)
    (large :
      nextDenominator.natAbs < ∏ factor ∈ factors, factor) :
    nextDenominator = 0 ∨
      ∃ factor ∈ factors,
        ¬(factor : ℤ) ∣ common ∧
          (factor : ℤ) ∣ reducedNumerator - reducedDenominator := by
  classical
  by_cases terminal : nextDenominator = 0
  · exact Or.inl terminal
  right
  by_contra no_survivor
  push_neg at no_survivor
  have pairwise :
      (↑factors : Set Nat).Pairwise
        (IsCoprime on fun factor : Nat => (factor : ℤ)) := by
    intro left left_mem right right_mem distinct
    exact
      ((Nat.coprime_primes (factor_prime left left_mem)
        (factor_prime right right_mem)).mpr distinct).isCoprime
  have product_divides :
      (∏ factor ∈ factors, (factor : ℤ)) ∣ common :=
    Finset.prod_dvd_of_coprime pairwise fun factor factor_mem => by
      by_contra not_divides
      have no_reset := no_survivor factor factor_mem not_divides
      exact
        (cyclotomic_reset_or_cancel difference numerator_reduced
          denominator_reduced (Int.prime_iff_natAbs_prime.mpr <| by
            simpa using factor_prime factor factor_mem)
          (factor_cyclotomic factor factor_mem)).elim not_divides no_reset
  have product_divides_terminal :
      (∏ factor ∈ factors, (factor : ℤ)) ∣ nextDenominator := by
    rw [denominator_reduced]
    exact product_divides.mul_right reducedDenominator
  have product_abs :
      (∏ factor ∈ factors, (factor : ℤ)).natAbs =
        ∏ factor ∈ factors, factor := by
    calc
      (∏ factor ∈ factors, (factor : ℤ)).natAbs =
          ∏ factor ∈ factors, ((factor : ℤ).natAbs) :=
        map_prod Int.natAbsHom (fun factor : Nat => (factor : ℤ)) factors
      _ = ∏ factor ∈ factors, factor := by simp
  have terminal_zero :=
    Int.eq_zero_of_dvd_of_natAbs_lt_natAbs product_divides_terminal <| by
      rwa [product_abs]
  exact terminal terminal_zero

/-- If every prime in a cyclotomic family is prevented from resetting the reduced state, then
their squarefree product is no larger than a nonzero terminal defect.  This is the exact
arithmetic price of evading all corresponding finite quotients. -/
theorem cyclotomicProduct_le_terminalDefect_of_no_reset
    {prime depth wait : Nat} {scale numerator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator : ℤ}
    {factors : Finset Nat}
    (difference :
      (prime : ℤ) ^ (depth * wait) * nextNumerator - nextDenominator =
        scale * (1 - (prime : ℤ) ^ wait) * numerator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator)
    (factor_prime : ∀ factor ∈ factors, factor.Prime)
    (factor_cyclotomic :
      ∀ factor ∈ factors, (factor : ℤ) ∣ (prime : ℤ) ^ wait - 1)
    (nonterminal : nextDenominator ≠ 0)
    (no_reset :
      ∀ factor ∈ factors,
        ¬(factor : ℤ) ∣ reducedNumerator - reducedDenominator) :
    (∏ factor ∈ factors, factor) ≤ nextDenominator.natAbs := by
  by_contra exceeds
  have large :
      nextDenominator.natAbs < ∏ factor ∈ factors, factor :=
    Nat.lt_of_not_ge exceeds
  rcases terminal_or_exists_cyclotomic_reset difference numerator_reduced
      denominator_reduced factor_prime factor_cyclotomic large with
    terminal | ⟨factor, factor_mem, _, reset⟩
  · exact nonterminal terminal
  · exact no_reset factor factor_mem reset

/-- Height form of the finite-family gate.  A primitive factor product larger than the
archimedean terminal-defect envelope cannot disappear silently. -/
theorem terminalDefect_zero_or_exists_cyclotomic_reset_of_height_lt
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator : ℤ}
    {factors : Finset Nat}
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator)
    (factor_prime : ∀ factor ∈ factors, factor.Prime)
    (factor_cyclotomic :
      ∀ factor ∈ factors, (factor : ℤ) ∣ (prime : ℤ) ^ wait - 1)
    (large :
      ((centerNumerator - scale).natAbs + driftNumerator.natAbs) *
          integralPairHeight numerator denominator <
        ∏ factor ∈ factors, factor) :
    terminalDefect centerNumerator driftNumerator scale numerator denominator = 0 ∨
      ∃ factor ∈ factors,
        ¬(factor : ℤ) ∣ common ∧
          (factor : ℤ) ∣ reducedNumerator - reducedDenominator := by
  have terminal_bound :=
    terminalDefect_natAbs_le_height centerNumerator driftNumerator scale
      numerator denominator
  have raw_large :
      nextDenominator.natAbs < ∏ factor ∈ factors, factor := by
    rw [step.2]
    exact terminal_bound.trans_lt large
  have gate :=
    terminal_or_exists_cyclotomic_reset
      (integralStep_difference step) numerator_reduced denominator_reduced
      factor_prime factor_cyclotomic raw_large
  simpa only [step.2] using gate

/-- The canonical primitive cyclotomic radical gives the exact finite-family gate at one wait. -/
theorem terminalDefect_zero_or_exists_primitive_reset
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator : ℤ}
    (prime_gt_one : 1 < prime)
    (wait_positive : 0 < wait)
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator)
    (large :
      ((centerNumerator - scale).natAbs + driftNumerator.natAbs) *
          integralPairHeight numerator denominator <
        primitiveCyclotomicRadical prime wait) :
    terminalDefect centerNumerator driftNumerator scale numerator denominator = 0 ∨
      ∃ factor ∈ primitiveCyclotomicPrimes prime wait,
        ¬(factor : ℤ) ∣ common ∧
          (factor : ℤ) ∣ reducedNumerator - reducedDenominator := by
  apply terminalDefect_zero_or_exists_cyclotomic_reset_of_height_lt
    step numerator_reduced denominator_reduced
  · intro factor factor_mem
    exact
      (primitivePrimeDivisor_of_mem_primitiveCyclotomicPrimes
        prime_gt_one wait_positive factor_mem).prime
  · intro factor factor_mem
    have primitive :=
      primitivePrimeDivisor_of_mem_primitiveCyclotomicPrimes
        prime_gt_one wait_positive factor_mem
    have cast_dvd :
        (factor : ℤ) ∣ ((prime ^ wait - 1 : Nat) : ℤ) :=
      Int.natCast_dvd_natCast.mpr primitive.dvd
    have one_le : 1 ≤ prime ^ wait :=
      Nat.one_le_pow wait prime (Nat.zero_lt_of_lt prime_gt_one)
    rw [Int.natCast_sub one_le] at cast_dvd
    simpa using cast_dvd
  · exact large

/-- If no primitive cyclotomic quotient sees the projective reset, the entire primitive
cyclotomic radical must fit inside the terminal-defect height envelope. -/
theorem primitiveCyclotomicRadical_le_height_of_no_reset
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator : ℤ}
    (prime_gt_one : 1 < prime)
    (wait_positive : 0 < wait)
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator)
    (nonterminal :
      terminalDefect centerNumerator driftNumerator scale numerator denominator ≠ 0)
    (no_reset :
      ∀ factor ∈ primitiveCyclotomicPrimes prime wait,
        ¬(factor : ℤ) ∣ reducedNumerator - reducedDenominator) :
    primitiveCyclotomicRadical prime wait ≤
      ((centerNumerator - scale).natAbs + driftNumerator.natAbs) *
        integralPairHeight numerator denominator := by
  have radical_le_terminal :
      primitiveCyclotomicRadical prime wait ≤ nextDenominator.natAbs := by
    apply cyclotomicProduct_le_terminalDefect_of_no_reset
      (integralStep_difference step) numerator_reduced denominator_reduced
    · intro factor factor_mem
      exact
        (primitivePrimeDivisor_of_mem_primitiveCyclotomicPrimes
          prime_gt_one wait_positive factor_mem).prime
    · intro factor factor_mem
      have primitive :=
        primitivePrimeDivisor_of_mem_primitiveCyclotomicPrimes
          prime_gt_one wait_positive factor_mem
      have cast_dvd :
          (factor : ℤ) ∣ ((prime ^ wait - 1 : Nat) : ℤ) :=
        Int.natCast_dvd_natCast.mpr primitive.dvd
      have one_le : 1 ≤ prime ^ wait :=
        Nat.one_le_pow wait prime (Nat.zero_lt_of_lt prime_gt_one)
      rw [Int.natCast_sub one_le] at cast_dvd
      simpa using cast_dvd
    · simpa only [step.2] using nonterminal
    · exact no_reset
  rw [step.2] at radical_le_terminal
  exact radical_le_terminal.trans <|
    terminalDefect_natAbs_le_height centerNumerator driftNumerator scale
      numerator denominator

end
end MatrixMortality.ReturnGuard
