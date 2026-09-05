import Mathlib.Data.Int.NatAbs
import MatrixMortality.PrimitiveDivisor
import MatrixMortality.ReturnGuardValuation

/-!
# Primitive-factor gates for guarded return dynamics

A legal integral guard step has two mutually exclusive ways to dispose of a cyclotomic prime:
primitive reduction swallows it, or the reduced projective state becomes one modulo that prime.
This file assembles those prime-local alternatives into one finite-family theorem.

The squarefree gate is deliberately Archimedean. If the product of a family of swallowed,
pairwise-coprime primes exceeds the source terminal defect, divisibility forces terminality;
otherwise one prime survives as a finite projective reset witness. The complementary no-reset
gate retains every prime with its full cyclotomic multiplicity and charges that strong primitive
part to the common reduction and source height.
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

/-- Product of the full prime powers in the cyclotomic value supported on primitive primes. -/
def primitiveCyclotomicPart (base exponent : Nat) : Nat :=
  ∏ factor ∈ primitiveCyclotomicPrimes base exponent,
    factor ^ (cyclotomicValue base exponent).factorization factor

theorem mem_primitiveCyclotomicPrimes
    {factor base exponent : Nat} :
    factor ∈ primitiveCyclotomicPrimes base exponent ↔
      factor ∈ (cyclotomicValue base exponent).primeFactors ∧
        ¬factor ∣ exponent := by
  simp [primitiveCyclotomicPrimes]

theorem primitiveCyclotomicPart_pos (base exponent : Nat) :
    0 < primitiveCyclotomicPart base exponent := by
  rw [primitiveCyclotomicPart]
  apply Finset.prod_pos
  intro factor factor_mem
  exact Nat.pow_pos
    (Nat.prime_of_mem_primeFactors
      (mem_primitiveCyclotomicPrimes.mp factor_mem).1).pos

/-- Above exponent two, the cyclotomic value differs from its full primitive part by at most a
divisor of the exponent. This is the strong primitive-part interface needed for size bounds. -/
theorem cyclotomicValue_dvd_exponent_mul_primitiveCyclotomicPart
    {base exponent : Nat} (base_gt_one : 1 < base) (exponent_gt_two : 2 < exponent) :
    cyclotomicValue base exponent ∣
      exponent * primitiveCyclotomicPart base exponent := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro factor power factor_prime power_dvd_value
  by_cases power_zero : power = 0
  · subst power
    simp
  have value_positive : 0 < cyclotomicValue base exponent := by
    rw [cyclotomicValue]
    exact Int.natAbs_pos.mpr <|
      ne_of_gt (Polynomial.cyclotomic_pos' exponent (by exact_mod_cast base_gt_one))
  have factor_dvd_value : factor ∣ cyclotomicValue base exponent :=
    (dvd_pow_self factor power_zero).trans power_dvd_value
  have power_le_factorization :
      power ≤ (cyclotomicValue base exponent).factorization factor :=
    (factor_prime.pow_dvd_iff_le_factorization value_positive.ne').mp power_dvd_value
  by_cases factor_dvd_exponent : factor ∣ exponent
  · have factorization_eq_one :
        (cyclotomicValue base exponent).factorization factor = 1 := by
      rcases factor_prime.eq_two_or_odd' with factor_two | factor_odd
      · subst factor
        exact cyclotomicValue_factorization_eq_one_of_two_nonprimitive
          exponent_gt_two factor_dvd_exponent factor_dvd_value
      · exact cyclotomicValue_factorization_eq_one_of_odd_nonprimitive
          factor_prime factor_odd base_gt_one (by omega)
          factor_dvd_exponent factor_dvd_value
    have power_eq : power = 1 := by omega
    subst power
    simpa using dvd_mul_of_dvd_left factor_dvd_exponent
      (primitiveCyclotomicPart base exponent)
  · have factor_mem : factor ∈ primitiveCyclotomicPrimes base exponent :=
      mem_primitiveCyclotomicPrimes.mpr
        ⟨Nat.mem_primeFactors.mpr
          ⟨factor_prime, factor_dvd_value, value_positive.ne'⟩,
          factor_dvd_exponent⟩
    have full_power_dvd_part :
        factor ^ (cyclotomicValue base exponent).factorization factor ∣
          primitiveCyclotomicPart base exponent := by
      simpa [primitiveCyclotomicPart] using
        (Finset.dvd_prod_of_mem
          (fun candidate =>
            candidate ^ (cyclotomicValue base exponent).factorization candidate)
          factor_mem)
    exact dvd_mul_of_dvd_right
      ((pow_dvd_pow factor power_le_factorization).trans full_power_dvd_part)
      exponent

/-- Elementary strong primitive-part lower bound. It is the precise inequality supplied by the
published formula `Φ⁎ₙ(q)=Φₙ(q)` or `Φₙ(q)/r`, without introducing a second definition. -/
theorem sub_one_pow_totient_le_exponent_mul_primitiveCyclotomicPart
    {base exponent : Nat} (base_gt_one : 1 < base) (exponent_gt_two : 2 < exponent) :
    (base - 1) ^ exponent.totient ≤
      exponent * primitiveCyclotomicPart base exponent := by
  have product_positive :
      0 < exponent * primitiveCyclotomicPart base exponent :=
    Nat.mul_pos (by omega) (primitiveCyclotomicPart_pos base exponent)
  calc
    (base - 1) ^ exponent.totient ≤ cyclotomicValue base exponent :=
      sub_one_pow_totient_le_cyclotomicValue base_gt_one
    _ ≤ exponent * primitiveCyclotomicPart base exponent :=
      Nat.le_of_dvd product_positive
        (cyclotomicValue_dvd_exponent_mul_primitiveCyclotomicPart
          base_gt_one exponent_gt_two)

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

/-- If a full cyclotomic prime power divides the boundary and the reduced target does not reset
modulo its prime, the whole prime power is swallowed by primitive reduction. -/
theorem cyclotomicPrimePower_dvd_common_of_no_reset
    {prime depth : Nat} {scale : ℤ} {wait : Nat}
    {numerator nextNumerator nextDenominator common reducedNumerator
      reducedDenominator cyclotomicPrime : ℤ} {power : Nat}
    (difference :
      (prime : ℤ) ^ (depth * wait) * nextNumerator - nextDenominator =
        scale * (1 - (prime : ℤ) ^ wait) * numerator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator)
    (cyclotomic_prime : Prime cyclotomicPrime)
    (power_positive : 0 < power)
    (cyclotomic_divides :
      cyclotomicPrime ^ power ∣ (prime : ℤ) ^ wait - 1)
    (no_reset :
      ¬cyclotomicPrime ∣ reducedNumerator - reducedDenominator) :
    cyclotomicPrime ^ power ∣ common := by
  have divides_power_sub_one :
      cyclotomicPrime ^ power ∣
        (prime : ℤ) ^ (depth * wait) - 1 := by
    have power_divides :
        (prime : ℤ) ^ wait - 1 ∣
          ((prime : ℤ) ^ wait) ^ depth - 1 :=
      sub_one_dvd_pow_sub_one ((prime : ℤ) ^ wait) depth
    apply cyclotomic_divides.trans
    rw [Nat.mul_comm depth wait, pow_mul]
    exact power_divides
  have divides_scaled_difference :
      cyclotomicPrime ^ power ∣
        (prime : ℤ) ^ (depth * wait) * nextNumerator -
          nextDenominator := by
    rw [difference]
    have negative :
        cyclotomicPrime ^ power ∣ 1 - (prime : ℤ) ^ wait := by
      simpa only [neg_sub] using dvd_neg.mpr cyclotomic_divides
    exact (negative.mul_left scale).mul_right numerator
  have divides_common_product :
      cyclotomicPrime ^ power ∣
        common *
          ((prime : ℤ) ^ (depth * wait) * reducedNumerator -
            reducedDenominator) := by
    simpa [numerator_reduced, denominator_reduced, mul_sub, mul_assoc,
      mul_left_comm, mul_comm] using divides_scaled_difference
  have prime_not_dvd_residue :
      ¬cyclotomicPrime ∣
        (prime : ℤ) ^ (depth * wait) * reducedNumerator -
          reducedDenominator := by
    intro residue
    have correction :
        cyclotomicPrime ∣
          ((prime : ℤ) ^ (depth * wait) - 1) * reducedNumerator :=
      dvd_mul_of_dvd_left
        ((dvd_pow_self cyclotomicPrime power_positive.ne').trans
          divides_power_sub_one) reducedNumerator
    have decomposition :
        reducedNumerator - reducedDenominator =
          ((prime : ℤ) ^ (depth * wait) * reducedNumerator -
            reducedDenominator) -
          ((prime : ℤ) ^ (depth * wait) - 1) * reducedNumerator := by
      ring
    apply no_reset
    rw [decomposition]
    exact dvd_sub residue correction
  have coprime_residue :
      IsCoprime (cyclotomicPrime ^ power)
        ((prime : ℤ) ^ (depth * wait) * reducedNumerator -
          reducedDenominator) :=
    (cyclotomic_prime.coprime_iff_not_dvd.mpr prime_not_dvd_residue).pow_left
  exact coprime_residue.dvd_of_dvd_mul_right divides_common_product

/-- If no primitive prime sees reset, primitive reduction swallows every corresponding prime
with its full multiplicity in the cyclotomic value. -/
theorem primitiveCyclotomicPart_dvd_common_of_no_reset
    {prime depth : Nat} {scale : ℤ} {wait : Nat}
    {numerator nextNumerator nextDenominator common reducedNumerator
      reducedDenominator : ℤ}
    (prime_gt_one : 1 < prime)
    (difference :
      (prime : ℤ) ^ (depth * wait) * nextNumerator - nextDenominator =
        scale * (1 - (prime : ℤ) ^ wait) * numerator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator)
    (no_reset :
      ∀ factor ∈ primitiveCyclotomicPrimes prime wait,
        ¬(factor : ℤ) ∣ reducedNumerator - reducedDenominator) :
    (primitiveCyclotomicPart prime wait : ℤ) ∣ common := by
  classical
  let value := cyclotomicValue prime wait
  let factors := primitiveCyclotomicPrimes prime wait
  have pairwise :
      (↑factors : Set Nat).Pairwise
        (fun left right => IsCoprime
          ((left : ℤ) ^ value.factorization left)
          ((right : ℤ) ^ value.factorization right)) := by
    intro left left_mem right right_mem distinct
    have left_prime : left.Prime :=
      Nat.prime_of_mem_primeFactors (mem_primitiveCyclotomicPrimes.mp left_mem).1
    have right_prime : right.Prime :=
      Nat.prime_of_mem_primeFactors (mem_primitiveCyclotomicPrimes.mp right_mem).1
    exact
      ((Nat.coprime_primes left_prime right_prime).mpr distinct).isCoprime.pow
  have each_divides :
      ∀ factor ∈ factors,
        (factor : ℤ) ^ value.factorization factor ∣ common := by
    intro factor factor_mem
    have value_mem : factor ∈ value.primeFactors :=
      (mem_primitiveCyclotomicPrimes.mp factor_mem).1
    have factor_prime : factor.Prime := Nat.prime_of_mem_primeFactors value_mem
    have factor_dvd_value : factor ∣ value := Nat.dvd_of_mem_primeFactors value_mem
    have value_ne : value ≠ 0 := (Nat.mem_primeFactors.mp value_mem).2.2
    have power_positive : 0 < value.factorization factor :=
      factor_prime.factorization_pos_of_dvd value_ne factor_dvd_value
    have power_dvd_value : factor ^ value.factorization factor ∣ value :=
      (factor_prime.pow_dvd_iff_le_factorization value_ne).mpr le_rfl
    have power_dvd_boundary_nat :
        factor ^ value.factorization factor ∣ prime ^ wait - 1 :=
      power_dvd_value.trans (cyclotomicValue_dvd_pow_sub_one prime_gt_one)
    have power_dvd_boundary_int :
        (factor : ℤ) ^ value.factorization factor ∣
          (prime : ℤ) ^ wait - 1 := by
      have cast_dvd :
          ((factor ^ value.factorization factor : Nat) : ℤ) ∣
            ((prime ^ wait - 1 : Nat) : ℤ) :=
        Int.natCast_dvd_natCast.mpr power_dvd_boundary_nat
      have one_le : 1 ≤ prime ^ wait :=
        Nat.one_le_pow wait prime (Nat.zero_lt_of_lt prime_gt_one)
      rw [Nat.cast_pow, Int.natCast_sub one_le, Nat.cast_pow, Nat.cast_one] at cast_dvd
      exact cast_dvd
    exact cyclotomicPrimePower_dvd_common_of_no_reset difference
      numerator_reduced denominator_reduced
      (Int.prime_iff_natAbs_prime.mpr <| by simpa using factor_prime)
      power_positive power_dvd_boundary_int (no_reset factor factor_mem)
  have product_divides :
      (∏ factor ∈ factors,
        (factor : ℤ) ^ value.factorization factor) ∣ common :=
    Finset.prod_dvd_of_coprime pairwise each_divides
  simpa [primitiveCyclotomicPart, factors, value] using product_divides

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
  push Not at no_survivor
  have pairwise :
      (↑factors : Set Nat).Pairwise
        (fun left right => IsCoprime (left : ℤ) (right : ℤ)) := by
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

/-- If no primitive cyclotomic quotient sees reset, the full primitive part, including every
prime multiplicity in the cyclotomic value, fits inside the terminal-defect height envelope. -/
theorem primitiveCyclotomicPart_le_height_of_no_reset
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator : ℤ}
    (prime_gt_one : 1 < prime)
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
    primitiveCyclotomicPart prime wait ≤
      ((centerNumerator - scale).natAbs + driftNumerator.natAbs) *
        integralPairHeight numerator denominator := by
  have part_dvd_common :
      (primitiveCyclotomicPart prime wait : ℤ) ∣ common :=
    primitiveCyclotomicPart_dvd_common_of_no_reset prime_gt_one
      (integralStep_difference step) numerator_reduced denominator_reduced no_reset
  have part_le :=
    swallowedDivisor_natAbs_le_height step.2 denominator_reduced
      part_dvd_common nonterminal
  simpa using part_le

/-- If the full primitive cyclotomic part exceeds the source height envelope, the step is
terminal or its reduced target resets modulo some primitive prime. The reset prime need not
survive the raw reduction; the squarefree gate above retains that stronger quotient witness. -/
theorem terminalDefect_zero_or_exists_primitive_reset_of_part_height_lt
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {numerator denominator nextNumerator nextDenominator
      common reducedNumerator reducedDenominator : ℤ}
    (prime_gt_one : 1 < prime)
    (step :
      IntegralStep prime depth centerNumerator driftNumerator scale
        wait numerator denominator nextNumerator nextDenominator)
    (numerator_reduced : nextNumerator = common * reducedNumerator)
    (denominator_reduced : nextDenominator = common * reducedDenominator)
    (large :
      ((centerNumerator - scale).natAbs + driftNumerator.natAbs) *
          integralPairHeight numerator denominator <
        primitiveCyclotomicPart prime wait) :
    terminalDefect centerNumerator driftNumerator scale numerator denominator = 0 ∨
      ∃ factor ∈ primitiveCyclotomicPrimes prime wait,
        (factor : ℤ) ∣ reducedNumerator - reducedDenominator := by
  by_cases terminal :
      terminalDefect centerNumerator driftNumerator scale numerator denominator = 0
  · exact Or.inl terminal
  right
  by_contra no_reset
  push Not at no_reset
  exact (not_lt_of_ge <|
    primitiveCyclotomicPart_le_height_of_no_reset prime_gt_one step
      numerator_reduced denominator_reduced terminal no_reset) large

end
end MatrixMortality.ReturnGuard
