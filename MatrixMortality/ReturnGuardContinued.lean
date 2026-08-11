import Mathlib.Algebra.GeomSum
import MatrixMortality.ReturnGuardCumulative

/-!
# Fixed-cusp endpoint calculus

The cumulative endpoint recurrence admits one canonical Euclidean quotient and one fixed
forbidden cusp.  This file records those laws without introducing another dynamical state.
It also exposes reverse-content persistence and the exact two-step identity behind record-wait
height bounds.
-/

namespace MatrixMortality.ReturnGuard

open MatrixMortality.PadicValuation
open scoped Matrix

noncomputable section

/-- Geometric quotient of `base ^ depth - 1` by `base - 1`. -/
def geometricPowerSum (base : ℤ) (depth : Nat) : ℤ :=
  ∑ index ∈ Finset.range depth, base ^ index

theorem geometricPowerSum_mul_sub_one (base : ℤ) (depth : Nat) :
    geometricPowerSum base depth * (base - 1) = base ^ depth - 1 := by
  exact geom_sum_mul base depth

/-- The primitive normalization factor is the Smith gcd of the exact endpoint prequotient
and the drift-scaled source numerator. -/
theorem PrimitiveEndpointReduction.content_natAbs_eq_gcd_driftSource_prequotient
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {source target : ℤ × ℤ} {content : ℤ}
    (reduction :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        wait source target content) :
    content.natAbs =
      Nat.gcd (driftNumerator * source.1).natAbs
        (content * target.2).natAbs := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · apply Int.natAbs_dvd_natAbs.mpr
      use target.1 - (centerNumerator - scale) * target.2
      have numerator := reduction.step.numerator
      simp only [Prod.fst, Prod.snd] at numerator
      calc
        driftNumerator * source.1 =
            content * target.1 -
              (centerNumerator - scale) * (content * target.2) := by
          linarith
        _ = content *
            (target.1 - (centerNumerator - scale) * target.2) := by ring
    · exact Int.natAbs_dvd_natAbs.mpr (dvd_mul_right content target.2)
  · let common : ℤ :=
      Nat.gcd (driftNumerator * source.1).natAbs
        (content * target.2).natAbs
    have common_dvd_driftSource : common ∣ driftNumerator * source.1 :=
      Int.natAbs_dvd_natAbs.mp (Nat.gcd_dvd_left _ _)
    have common_dvd_prequotient : common ∣ content * target.2 :=
      Int.natAbs_dvd_natAbs.mp (Nat.gcd_dvd_right _ _)
    have common_dvd_rawNumerator :
        common ∣
          driftNumerator * source.1 +
            (centerNumerator - scale) * (content * target.2) :=
      dvd_add common_dvd_driftSource
        (common_dvd_prequotient.mul_left (centerNumerator - scale))
    have common_dvd_content : common ∣ content := by
      apply
        (divisor_dvd_commonFactor_iff
          (left := content * target.2)
          (right :=
            driftNumerator * source.1 +
              (centerNumerator - scale) * (content * target.2))
          (common := content) (reducedLeft := target.2)
          (reducedRight := target.1)
          (by rfl) (by
            simpa only [Prod.fst, Prod.snd, add_comm] using
              reduction.step.numerator.symm)
          reduction.target_coprime.symm).mpr
      exact ⟨common_dvd_prequotient, common_dvd_rawNumerator⟩
    exact Int.natAbs_dvd_natAbs.mpr common_dvd_content

/-- Away from the fixed base, drift, and scale support, a divisor enters forward content
exactly when it occurs simultaneously in the current endpoint numerator and branch boundary.
The equivalence retains arbitrary prime-power multiplicity. -/
theorem PrimitiveEndpointReduction.divisor_dvd_content_iff
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {source target : ℤ × ℤ} {content divisor : ℤ}
    (reduction :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        wait source target content)
    (divisor_coprime :
      IsCoprime divisor ((prime : ℤ) * driftNumerator * scale)) :
    divisor ∣ content ↔
      divisor ∣ source.1 ∧ divisor ∣ (prime : ℤ) ^ wait - 1 := by
  have coprime_prime : IsCoprime divisor (prime : ℤ) :=
    IsCoprime.of_isCoprime_of_dvd_right divisor_coprime
      ⟨driftNumerator * scale, by ring⟩
  have coprime_drift : IsCoprime divisor driftNumerator :=
    IsCoprime.of_isCoprime_of_dvd_right divisor_coprime
      ⟨(prime : ℤ) * scale, by ring⟩
  have coprime_scale : IsCoprime divisor scale :=
    IsCoprime.of_isCoprime_of_dvd_right divisor_coprime
      ⟨(prime : ℤ) * driftNumerator, by ring⟩
  constructor
  · intro divisor_dvd_content
    have content_dvd_driftSource : content ∣ driftNumerator * source.1 := by
      refine ⟨target.1 - (centerNumerator - scale) * target.2, ?_⟩
      have numerator := reduction.step.numerator
      simp only [Prod.fst, Prod.snd] at numerator
      calc
        driftNumerator * source.1 =
            content * target.1 -
              (centerNumerator - scale) * (content * target.2) := by
          linarith
        _ = content *
            (target.1 - (centerNumerator - scale) * target.2) := by ring
    have divisor_dvd_source : divisor ∣ source.1 :=
      coprime_drift.dvd_of_dvd_mul_left
        (divisor_dvd_content.trans content_dvd_driftSource)
    have content_dvd_support :
        content ∣ driftNumerator * scale * ((prime : ℤ) ^ wait - 1) := by
      apply Int.natAbs_dvd_natAbs.mp
      rw [reduction.content_natAbs_eq_gcd_support]
      exact Nat.gcd_dvd_right _ _
    have divisor_dvd_support :
        divisor ∣ driftNumerator * scale * ((prime : ℤ) ^ wait - 1) :=
      divisor_dvd_content.trans content_dvd_support
    have coprime_fixed :
        IsCoprime divisor (driftNumerator * scale) :=
      coprime_drift.mul_right coprime_scale
    exact ⟨divisor_dvd_source,
      coprime_fixed.dvd_of_dvd_mul_left divisor_dvd_support⟩
  · rintro ⟨divisor_dvd_source, divisor_dvd_boundary⟩
    have divisor_dvd_prequotient : divisor ∣ content * target.2 := by
      apply
        (coprime_prime.pow_right (n := depth * wait)).dvd_of_dvd_mul_left
      rw [reduction.step.denominator]
      exact dvd_sub divisor_dvd_source
        ((divisor_dvd_boundary.mul_left scale).mul_right source.2)
    have divisor_dvd_rawNumerator : divisor ∣ content * target.1 := by
      have numerator := reduction.step.numerator
      simp only [Prod.fst, Prod.snd] at numerator
      rw [numerator]
      exact dvd_add (divisor_dvd_source.mul_left driftNumerator)
        (divisor_dvd_prequotient.mul_left (centerNumerator - scale))
    apply
      (divisor_dvd_commonFactor_iff
        (left := content * target.2) (right := content * target.1)
        (common := content) (reducedLeft := target.2)
        (reducedRight := target.1) rfl rfl reduction.target_coprime.symm).mpr
    exact ⟨divisor_dvd_prequotient, divisor_dvd_rawNumerator⟩

/-- Exact quotient before primitive content is removed. -/
def endpointPrequotient (content : ℤ) (target : ℤ × ℤ) : ℤ :=
  content * target.2

theorem PrimitiveEndpointReduction.source_eq_power_mul_prequotient
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {source target : ℤ × ℤ} {content : ℤ}
    (reduction :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        wait source target content) :
    source.1 =
      (prime : ℤ) ^ (depth * wait) * endpointPrequotient content target +
        scale * ((prime : ℤ) ^ wait - 1) * source.2 := by
  exact (eq_sub_iff_add_eq.mp reduction.step.denominator).symm

theorem PrimitiveEndpointReduction.target_eq_drift_add_prequotient
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {source target : ℤ × ℤ} {content : ℤ}
    (reduction :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        wait source target content) :
    content * target.1 =
      driftNumerator * source.1 +
        (centerNumerator - scale) * endpointPrequotient content target := by
  exact reduction.step.numerator

/-- Forward and reverse contents determine the reset defect by one exact linear identity. -/
theorem PrimitiveEndpointReduction.resetDefect_eq_complement_mul
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {source target : ℤ × ℤ} {content complement : ℤ}
    (reduction :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        wait source target content)
    (complementary :
      content * complement =
        driftNumerator * scale * ((prime : ℤ) ^ wait - 1)) :
    scale *
        (target.1 -
          (centerNumerator + driftNumerator - scale) * target.2) =
      complement *
        (scale * source.2 +
          geometricPowerSum ((prime : ℤ) ^ wait) depth *
            endpointPrequotient content target) := by
  have power_factorization :
      (prime : ℤ) ^ (depth * wait) - 1 =
        ((prime : ℤ) ^ wait - 1) *
          geometricPowerSum ((prime : ℤ) ^ wait) depth := by
    rw [Nat.mul_comm depth wait, pow_mul]
    rw [mul_comm]
    exact (geometricPowerSum_mul_sub_one ((prime : ℤ) ^ wait) depth).symm
  have scaled_defect :
      content *
          (scale *
            (target.1 -
              (centerNumerator + driftNumerator - scale) * target.2)) =
        driftNumerator * scale *
          (source.1 - endpointPrequotient content target) := by
    change
      content *
          (scale *
            (target.1 -
              (centerNumerator + driftNumerator - scale) * target.2)) =
        driftNumerator * scale *
          (source.1 - content * target.2)
    have numerator := reduction.step.numerator
    simp only [Prod.fst, Prod.snd] at numerator
    linear_combination scale * numerator
  have source_sub_prequotient :
      source.1 - endpointPrequotient content target =
        ((prime : ℤ) ^ wait - 1) *
          (scale * source.2 +
            geometricPowerSum ((prime : ℤ) ^ wait) depth *
              endpointPrequotient content target) := by
    rw [reduction.source_eq_power_mul_prequotient]
    rw [show
      (prime : ℤ) ^ (depth * wait) =
          ((prime : ℤ) ^ (depth * wait) - 1) + 1 by ring]
    rw [power_factorization]
    ring
  apply mul_left_cancel₀ reduction.content_ne
  rw [scaled_defect, source_sub_prequotient]
  calc
    driftNumerator * scale *
          (((prime : ℤ) ^ wait - 1) *
            (scale * source.2 +
              geometricPowerSum ((prime : ℤ) ^ wait) depth *
                endpointPrequotient content target)) =
        (driftNumerator * scale * ((prime : ℤ) ^ wait - 1)) *
          (scale * source.2 +
            geometricPowerSum ((prime : ℤ) ^ wait) depth *
              endpointPrequotient content target) := by ring
    _ = (content * complement) *
          (scale * source.2 +
            geometricPowerSum ((prime : ℤ) ^ wait) depth *
              endpointPrequotient content target) := by rw [complementary]
    _ = content *
          (complement *
            (scale * source.2 +
              geometricPowerSum ((prime : ℤ) ^ wait) depth *
                endpointPrequotient content target)) := by ring

theorem PrimitiveEndpointReduction.complement_dvd_resetDefect
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {source target : ℤ × ℤ} {content complement : ℤ}
    (reduction :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        wait source target content)
    (complementary :
      content * complement =
        driftNumerator * scale * ((prime : ℤ) ^ wait - 1)) :
    complement ∣
      scale *
        (target.1 -
          (centerNumerator + driftNumerator - scale) * target.2) := by
  rw [reduction.resetDefect_eq_complement_mul complementary]
  exact dvd_mul_right _ _

/-- A boundary divisor outside the fixed scale-reset support cannot pass from reverse content
to forward content at the next occurrence.  It remains, with multiplicity, in the next reverse
content. -/
theorem PrimitiveEndpointReduction.recurrentBoundaryDivisor_persists
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait nextWait : Nat} {source middle target : ℤ × ℤ}
    {content complement nextContent nextComplement divisor : ℤ}
    (first : PrimitiveEndpointReduction prime depth centerNumerator
      driftNumerator scale wait source middle content)
    (second : PrimitiveEndpointReduction prime depth centerNumerator
      driftNumerator scale nextWait middle target nextContent)
    (firstComplementary : content * complement =
      driftNumerator * scale * ((prime : ℤ) ^ wait - 1))
    (nextComplementary : nextContent * nextComplement =
      driftNumerator * scale * ((prime : ℤ) ^ nextWait - 1))
    (divisor_dvd_complement : divisor ∣ complement)
    (divisor_dvd_nextBoundary :
      divisor ∣ scale * ((prime : ℤ) ^ nextWait - 1))
    (divisor_coprime_fixed : IsCoprime divisor
      (scale * (centerNumerator + driftNumerator - scale))) :
    IsCoprime divisor nextContent ∧ divisor ∣ nextComplement := by
  have divisor_coprime_scale : IsCoprime divisor scale :=
    divisor_coprime_fixed.of_mul_right_left
  have divisor_coprime_reset :
      IsCoprime divisor (centerNumerator + driftNumerator - scale) :=
    divisor_coprime_fixed.of_mul_right_right
  have middle_coprime_divisor : IsCoprime middle.2 divisor :=
    IsCoprime.of_isCoprime_of_dvd_right
      (first.denominator_coprime_complement firstComplementary)
      divisor_dvd_complement
  have divisor_coprime_resetMiddle :
      IsCoprime divisor
        ((centerNumerator + driftNumerator - scale) * middle.2) :=
    divisor_coprime_reset.mul_right middle_coprime_divisor.symm
  have divisor_dvd_resetDefect :
      divisor ∣
        middle.1 -
          (centerNumerator + driftNumerator - scale) * middle.2 := by
    apply divisor_coprime_scale.dvd_of_dvd_mul_right
    rw [mul_comm]
    rw [first.resetDefect_eq_complement_mul firstComplementary]
    exact divisor_dvd_complement.mul_right _
  have divisor_dvd_raw_sub_reset :
      divisor ∣
        (prime : ℤ) ^ (depth * nextWait) *
            (nextContent * target.2) -
          (centerNumerator + driftNumerator - scale) * middle.2 := by
    rw [second.step.denominator]
    convert dvd_sub divisor_dvd_resetDefect
      (divisor_dvd_nextBoundary.mul_right middle.2) using 1
    all_goals ring
  have divisor_coprime_raw :
      IsCoprime divisor
        ((prime : ℤ) ^ (depth * nextWait) *
          (nextContent * target.2)) := by
    obtain ⟨differenceFactor, difference_eq⟩ := divisor_dvd_raw_sub_reset
    obtain ⟨left, right, bezout⟩ := divisor_coprime_resetMiddle
    refine ⟨left - right * differenceFactor, right, ?_⟩
    linear_combination bezout + right * difference_eq
  have divisor_coprime_nextContent : IsCoprime divisor nextContent :=
    IsCoprime.of_isCoprime_of_dvd_right divisor_coprime_raw
      ⟨(prime : ℤ) ^ (depth * nextWait) * target.2, by ring⟩
  refine ⟨divisor_coprime_nextContent, ?_⟩
  apply divisor_coprime_nextContent.dvd_of_dvd_mul_left
  rw [nextComplementary]
  simpa only [mul_assoc] using
    divisor_dvd_nextBoundary.mul_left driftNumerator

/-- At a primitive terminal target, the reverse content divides the smaller fixed boundary
resultant; the factor `centerNumerator - scale` is absent. -/
theorem PrimitiveEndpointReduction.complement_dvd_terminalBoundary
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {source : ℤ × ℤ} {content complement : ℤ}
    (reduction :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        wait source (0, 1) content)
    (complementary :
      content * complement =
        driftNumerator * scale * ((prime : ℤ) ^ wait - 1)) :
    complement ∣
      scale * (centerNumerator + driftNumerator - scale) := by
  have divides := reduction.complement_dvd_resetDefect complementary
  simpa only [Prod.fst, Prod.snd, mul_one, zero_sub, mul_neg, dvd_neg] using divides

/-- Canonical rational predecessor ray of the terminal endpoint at any prescribed wait. -/
def terminalPredecessorPair
    (prime depth : Nat) (centerNumerator driftNumerator scale : ℤ)
    (wait : Nat) : ℤ × ℤ :=
  ((centerNumerator - scale) * scale * ((prime : ℤ) ^ wait - 1),
    centerNumerator - scale +
      driftNumerator * (prime : ℤ) ^ (depth * wait))

/-- Every wait occurs on a content-free endpoint step whose target lies on the terminal ray.
Thus a fixed boundary divisor cannot by itself bound the final wait. -/
theorem terminalPredecessorPair_step
    (prime depth : Nat) (centerNumerator driftNumerator scale : ℤ)
    (wait : Nat) :
    CumulativeEndpointStep prime depth centerNumerator driftNumerator scale wait
      (terminalPredecessorPair prime depth centerNumerator driftNumerator scale wait)
      (0, -driftNumerator * scale * ((prime : ℤ) ^ wait - 1)) := by
  constructor <;>
    simp only [terminalPredecessorPair, Prod.fst, Prod.snd] <;> ring

/-- Consecutive cumulative numerators form the canonical complete quotient. -/
def cumulativeCompleteQuotient
    (driftNumerator scale previous current : ℤ) : ℚ :=
  -(driftNumerator * scale * previous : ℚ) / current

/-- The apparent moving checkpoint is one fixed cusp: every live complete quotient differs
from `-scale` by the displayed endpoint denominator ratio. -/
theorem cumulativeCompleteQuotient_sub_forbiddenCusp
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {source target : ℤ × ℤ}
    (target_numerator_ne : target.1 ≠ 0)
    (step :
      CumulativeEndpointStep prime depth centerNumerator driftNumerator scale
        wait source target) :
    cumulativeCompleteQuotient driftNumerator scale source.1 target.1 + scale =
      (scale * (centerNumerator - scale) * target.2 : ℚ) / target.1 := by
  have target_numerator_ne_rat : (target.1 : ℚ) ≠ 0 := by
    exact_mod_cast target_numerator_ne
  have numerator_cast :
      (target.1 : ℚ) =
        driftNumerator * source.1 +
          (centerNumerator - scale) * target.2 := by
    exact_mod_cast step.numerator
  rw [cumulativeCompleteQuotient]
  field_simp [target_numerator_ne_rat]
  rw [numerator_cast]
  ring

/-- Cross-multiplied generalized continued-fraction law for three consecutive cumulative
numerators.  It is total away from the two nonterminal denominator hypotheses. -/
theorem cumulativeCompleteQuotient_recurrence
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {previous source target : ℤ × ℤ}
    (source_numerator_ne : source.1 ≠ 0)
    (target_numerator_ne : target.1 ≠ 0)
    (previous_relation :
      source.1 - driftNumerator * previous.1 =
        (centerNumerator - scale) * source.2)
    (step :
      CumulativeEndpointStep prime depth centerNumerator driftNumerator scale
        wait source target) :
    (((prime : ℚ) ^ wait - 1) *
          cumulativeCompleteQuotient driftNumerator scale previous.1 source.1 -
        centerNumerator + scale * (prime : ℚ) ^ wait) *
        cumulativeCompleteQuotient driftNumerator scale source.1 target.1 =
      driftNumerator * (prime : ℚ) ^ (depth * wait) *
        (cumulativeCompleteQuotient driftNumerator scale source.1 target.1 +
          scale) := by
  have source_numerator_ne_rat : (source.1 : ℚ) ≠ 0 := by
    exact_mod_cast source_numerator_ne
  have target_numerator_ne_rat : (target.1 : ℚ) ≠ 0 := by
    exact_mod_cast target_numerator_ne
  have recurrence :=
    cumulativeNumerator_recurrence previous_relation step
  have recurrence_cast :
      (prime : ℚ) ^ (depth * wait) * target.1 =
        (driftNumerator * (prime : ℚ) ^ (depth * wait) +
            centerNumerator - scale * (prime : ℚ) ^ wait) * source.1 +
          driftNumerator * scale * ((prime : ℚ) ^ wait - 1) * previous.1 := by
    exact_mod_cast recurrence
  have bracket_eq :
      ((prime : ℚ) ^ wait - 1) *
            cumulativeCompleteQuotient driftNumerator scale previous.1 source.1 -
          centerNumerator + scale * (prime : ℚ) ^ wait =
        driftNumerator * (prime : ℚ) ^ (depth * wait) -
          (prime : ℚ) ^ (depth * wait) * target.1 / source.1 := by
    rw [cumulativeCompleteQuotient]
    field_simp [source_numerator_ne_rat]
    ring_nf at recurrence_cast ⊢
    linear_combination recurrence_cast
  rw [bracket_eq, cumulativeCompleteQuotient]
  field_simp [source_numerator_ne_rat, target_numerator_ne_rat]
  ring

/-- On the live unit shell, the decoded wait is exactly the approximation depth to the fixed
ray `centerNumerator * current = driftNumerator * scale * previous`. -/
theorem cumulativeWaitForm_hasValue
    {prime : Nat} [Fact prime.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    {previous source : ℤ × ℤ} {wait : ℤ}
    (previous_relation :
      source.1 - driftNumerator * previous.1 =
        (centerNumerator - scale) * source.2)
    (centerDifference_unit :
      IsUnit prime ((centerNumerator - scale : ℤ) : ℚ))
    (endpoint_value :
      HasValue prime ((source.1 + scale * source.2 : ℤ) : ℚ) wait) :
    HasValue prime
      ((centerNumerator * source.1 -
        driftNumerator * scale * previous.1 : ℤ) : ℚ) wait := by
  have factorization :
      ((centerNumerator * source.1 -
          driftNumerator * scale * previous.1 : ℤ) : ℚ) =
        (centerNumerator - scale : ℤ) *
          (source.1 + scale * source.2 : ℤ) := by
    exact_mod_cast cumulativeWaitForm_eq previous_relation
  rw [factorization]
  simpa using mul_hasValue centerDifference_unit endpoint_value

/-- Two consecutive primitive reductions eliminate their intermediate numerator. -/
theorem PrimitiveEndpointReduction.twoStep_elimination
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait nextWait : Nat} {source middle target : ℤ × ℤ}
    {content nextContent : ℤ}
    (first :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        wait source middle content)
    (second :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        nextWait middle target nextContent) :
    (prime : ℤ) ^ (depth * nextWait) * content * nextContent * target.2 =
      driftNumerator * source.1 +
        (centerNumerator - scale * (prime : ℤ) ^ nextWait) *
          (content * middle.2) := by
  have first_numerator := first.step.numerator
  have second_denominator := second.step.denominator
  simp only [Prod.fst, Prod.snd] at first_numerator second_denominator ⊢
  linear_combination content * second_denominator + first_numerator

/-- The primitive pair formed by a source denominator and its endpoint prequotient is carried
through consecutive reductions by one integral generalized-continuant block.  The statement
holds at every depth; no complementary-content split or moving auxiliary state is required. -/
theorem PrimitiveEndpointReduction.twoStep_prequotient_transport
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait nextWait : Nat} {source middle target : ℤ × ℤ}
    {content nextContent : ℤ}
    (first :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        wait source middle content)
    (second :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        nextWait middle target nextContent) :
    ((prime : ℤ) ^ (depth * nextWait) * content) •
        ![middle.2, endpointPrequotient nextContent target] =
      !![
          0, (prime : ℤ) ^ (depth * nextWait);
          driftNumerator * scale * ((prime : ℤ) ^ wait - 1),
            centerNumerator +
              driftNumerator * (prime : ℤ) ^ (depth * wait) -
              scale * (prime : ℤ) ^ nextWait] *ᵥ
        ![source.2, endpointPrequotient content middle] := by
  ext i
  fin_cases i
  · simp [endpointPrequotient, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_succ, smul_eq_mul]
    ring
  · simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ,
      smul_eq_mul]
    have eliminated := first.twoStep_elimination second
    rw [first.source_eq_power_mul_prequotient] at eliminated
    dsimp [endpointPrequotient] at eliminated ⊢
    linear_combination eliminated

/-- Parameter coefficient in the depth-two record-ascent budget. -/
def twoStepContentCoefficient
    (centerNumerator driftNumerator scale : ℤ) : Nat :=
  driftNumerator.natAbs +
    (1 + scale.natAbs) * (centerNumerator.natAbs + scale.natAbs)

/-- At critical depth two, a nondecreasing second wait charges the sum of both waits to the
initial primitive height.  The intermediate height is absent. -/
theorem PrimitiveEndpointReduction.twoStep_contentBudget
    {prime : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait nextWait : Nat} {source middle target : ℤ × ℤ}
    {content nextContent : ℤ}
    (prime_positive : 0 < prime)
    (wait_le_next : wait ≤ nextWait)
    (target_denominator_ne : target.2 ≠ 0)
    (first :
      PrimitiveEndpointReduction prime 2 centerNumerator driftNumerator scale
        wait source middle content)
    (second :
      PrimitiveEndpointReduction prime 2 centerNumerator driftNumerator scale
        nextWait middle target nextContent) :
    prime ^ (wait + nextWait) * (content * nextContent).natAbs ≤
      twoStepContentCoefficient centerNumerator driftNumerator scale *
        integralPairHeight source.1 source.2 := by
  let x := prime ^ wait
  let y := prime ^ nextWait
  let height := integralPairHeight source.1 source.2
  let firstCoefficient := 1 + scale.natAbs
  let coefficient :=
    twoStepContentCoefficient centerNumerator driftNumerator scale
  have x_positive : 0 < x := Nat.pow_pos prime_positive
  have y_positive : 0 < y := Nat.pow_pos prime_positive
  have one_le_x : 1 ≤ x := x_positive
  have x_le_y : x ≤ y := by
    exact Nat.pow_le_pow_right prime_positive wait_le_next
  have sourceNumerator_le : source.1.natAbs ≤ height :=
    le_max_left _ _
  have sourceDenominator_le : source.2.natAbs ≤ height :=
    le_max_right _ _
  have cyclotomic_natAbs_le_x :
      ((prime : ℤ) ^ wait - 1).natAbs ≤ x := by
    have one_le_power : (1 : ℤ) ≤ (prime : ℤ) ^ wait := by
      exact_mod_cast one_le_x
    exact_mod_cast
      (show
        (((prime : ℤ) ^ wait - 1).natAbs : ℤ) ≤ (x : ℤ) by
        dsimp [x]
        rw [Int.natAbs_of_nonneg (sub_nonneg.mpr one_le_power)]
        simpa only [Nat.cast_pow] using
          (sub_le_self ((prime : ℤ) ^ wait)
            (show (0 : ℤ) ≤ 1 by norm_num)))
  have first_raw_abs :
      x * x * (content * middle.2).natAbs =
        (source.1 -
          scale * ((prime : ℤ) ^ wait - 1) * source.2).natAbs := by
    have denominator := first.step.denominator
    simp only [Prod.fst, Prod.snd] at denominator
    have absolute := congrArg Int.natAbs denominator
    simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_ofNat] at absolute
    rw [show 2 * wait = wait + wait by omega, pow_add] at absolute
    rw [Int.natAbs_mul]
    simpa only [x, mul_assoc] using absolute
  have first_raw_le :
      (source.1 -
          scale * ((prime : ℤ) ^ wait - 1) * source.2).natAbs ≤
        x * (firstCoefficient * height) := by
    calc
      _ ≤ source.1.natAbs +
          (scale * ((prime : ℤ) ^ wait - 1) * source.2).natAbs :=
        Int.natAbs_sub_le _ _
      _ = source.1.natAbs +
          scale.natAbs * ((prime : ℤ) ^ wait - 1).natAbs *
            source.2.natAbs := by simp only [Int.natAbs_mul]
      _ ≤ height + scale.natAbs * x * height := by
        exact Nat.add_le_add sourceNumerator_le
          (Nat.mul_le_mul
            (Nat.mul_le_mul_left scale.natAbs cyclotomic_natAbs_le_x)
            sourceDenominator_le)
      _ ≤ x * height + scale.natAbs * x * height := by
        exact Nat.add_le_add_right
          (Nat.le_mul_of_pos_left height x_positive) _
      _ = x * (firstCoefficient * height) := by
        dsimp [firstCoefficient]
        ring
  have first_budget :
      x * (content * middle.2).natAbs ≤ firstCoefficient * height := by
    apply Nat.le_of_mul_le_mul_left _ x_positive
    calc
      x * (x * (content * middle.2).natAbs) =
          x * x * (content * middle.2).natAbs := by ring
      _ =
          (source.1 -
            scale * ((prime : ℤ) ^ wait - 1) * source.2).natAbs :=
        first_raw_abs
      _ ≤ x * (firstCoefficient * height) := first_raw_le
  have targetDenominator_positive : 0 < target.2.natAbs :=
    Int.natAbs_pos.mpr target_denominator_ne
  have second_raw_abs :
      y * y *
          ((content * nextContent).natAbs * target.2.natAbs) =
        (driftNumerator * source.1 +
          (centerNumerator - scale * (prime : ℤ) ^ nextWait) *
            (content * middle.2)).natAbs := by
    have eliminated := first.twoStep_elimination second
    have absolute := congrArg Int.natAbs eliminated
    simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_ofNat] at absolute
    rw [show 2 * nextWait = nextWait + nextWait by omega, pow_add] at absolute
    rw [Int.natAbs_mul content nextContent]
    simpa only [y, mul_assoc] using absolute
  have second_left_le :
      y * y * (content * nextContent).natAbs ≤
        (driftNumerator * source.1 +
          (centerNumerator - scale * (prime : ℤ) ^ nextWait) *
            (content * middle.2)).natAbs := by
    calc
      y * y * (content * nextContent).natAbs ≤
          y * y *
            ((content * nextContent).natAbs * target.2.natAbs) := by
        apply Nat.mul_le_mul_left
        exact Nat.le_mul_of_pos_right _ targetDenominator_positive
      _ = _ := second_raw_abs
  have second_right_le :
      (driftNumerator * source.1 +
          (centerNumerator - scale * (prime : ℤ) ^ nextWait) *
            (content * middle.2)).natAbs ≤
        driftNumerator.natAbs * height +
          (centerNumerator.natAbs + scale.natAbs * y) *
            (content * middle.2).natAbs := by
    calc
      _ ≤ (driftNumerator * source.1).natAbs +
          ((centerNumerator - scale * (prime : ℤ) ^ nextWait) *
            (content * middle.2)).natAbs := Int.natAbs_add_le _ _
      _ = driftNumerator.natAbs * source.1.natAbs +
          (centerNumerator - scale * (prime : ℤ) ^ nextWait).natAbs *
            (content * middle.2).natAbs := by
        simp only [Int.natAbs_mul]
      _ ≤ driftNumerator.natAbs * height +
          (centerNumerator.natAbs + scale.natAbs * y) *
            (content * middle.2).natAbs := by
        apply Nat.add_le_add
        · exact Nat.mul_le_mul_left driftNumerator.natAbs sourceNumerator_le
        · apply Nat.mul_le_mul_right
          calc
            (centerNumerator -
                scale * (prime : ℤ) ^ nextWait).natAbs ≤
                centerNumerator.natAbs +
                  (scale * (prime : ℤ) ^ nextWait).natAbs :=
              Int.natAbs_sub_le _ _
            _ = centerNumerator.natAbs + scale.natAbs * y := by
              simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_ofNat, y]
  have scaled_right_le :
      x *
          (driftNumerator.natAbs * height +
            (centerNumerator.natAbs + scale.natAbs * y) *
              (content * middle.2).natAbs) ≤
        y * (coefficient * height) := by
    calc
      _ = x * driftNumerator.natAbs * height +
          centerNumerator.natAbs *
              (x * (content * middle.2).natAbs) +
            y * scale.natAbs *
              (x * (content * middle.2).natAbs) := by ring
      _ ≤ y * driftNumerator.natAbs * height +
          centerNumerator.natAbs * (firstCoefficient * height) +
            y * scale.natAbs * (firstCoefficient * height) := by
        exact Nat.add_le_add
          (Nat.add_le_add
            (Nat.mul_le_mul_right height
              (Nat.mul_le_mul_right driftNumerator.natAbs x_le_y))
            (Nat.mul_le_mul_left centerNumerator.natAbs first_budget))
          (Nat.mul_le_mul_left (y * scale.natAbs) first_budget)
      _ ≤ y * driftNumerator.natAbs * height +
          y * centerNumerator.natAbs * (firstCoefficient * height) +
            y * scale.natAbs * (firstCoefficient * height) := by
        simpa only [mul_assoc] using
          (Nat.add_le_add_right
            (Nat.add_le_add_left
              (Nat.le_mul_of_pos_left
                (centerNumerator.natAbs * (firstCoefficient * height))
                y_positive)
              (y * driftNumerator.natAbs * height))
            (y * scale.natAbs * (firstCoefficient * height)))
      _ = y * (coefficient * height) := by
        dsimp [coefficient, twoStepContentCoefficient]
        ring
  apply Nat.le_of_mul_le_mul_left _ y_positive
  calc
    y * (prime ^ (wait + nextWait) *
        (content * nextContent).natAbs) =
        x * (y * y * (content * nextContent).natAbs) := by
      dsimp [x, y]
      rw [pow_add]
      ring
    _ ≤ x *
        (driftNumerator * source.1 +
          (centerNumerator - scale * (prime : ℤ) ^ nextWait) *
            (content * middle.2)).natAbs :=
      Nat.mul_le_mul_left x second_left_le
    _ ≤ x *
        (driftNumerator.natAbs * height +
          (centerNumerator.natAbs + scale.natAbs * y) *
            (content * middle.2).natAbs) :=
      Nat.mul_le_mul_left x second_right_le
    _ ≤ y * (coefficient * height) := scaled_right_le

/-! ## Jacobi tail -/

/-- Rational edge quotient exposing the generalized Jacobi recurrence. It is a coordinate of
two adjacent primitive endpoint pairs, not an additional dynamical register. -/
def jacobiTail (scale content sourceDenominator targetDenominator : ℤ) : ℚ :=
  scale * sourceDenominator / (content * targetDenominator)

/-- Backward Jacobi update for the cyclotomic-normalized ready tail. -/
def jacobiBackward
    (depth : Nat) (center drift scale q nextQ tail : ℚ) : ℚ :=
  -center / drift - q ^ depth + scale / drift * nextQ +
    scale / drift * (nextQ ^ depth * (nextQ - 1) / tail)

/-- The backward Jacobi update contracts differences by its explicit reciprocal factor. -/
theorem jacobiBackward_sub
    (depth : Nat) (center drift scale q nextQ left right : ℚ)
    (drift_ne : drift ≠ 0) (left_ne : left ≠ 0) (right_ne : right ≠ 0) :
    jacobiBackward depth center drift scale q nextQ left -
        jacobiBackward depth center drift scale q nextQ right =
      -(scale / drift * nextQ ^ depth * (nextQ - 1)) *
        (left - right) / (left * right) := by
  simp only [jacobiBackward]
  field_simp
  ring

/-- Consecutive primitive endpoint reductions obey one exact generalized Jacobi shell law. -/
theorem PrimitiveEndpointReduction.jacobiTail_transition
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait nextWait : Nat} {source middle target : ℤ × ℤ}
    {content nextContent : ℤ}
    (first : PrimitiveEndpointReduction prime depth centerNumerator
      driftNumerator scale wait source middle content)
    (second : PrimitiveEndpointReduction prime depth centerNumerator
      driftNumerator scale nextWait middle target nextContent)
    (scale_ne : scale ≠ 0) (middleDenominator_ne : middle.2 ≠ 0) :
    (prime : ℚ) ^ nextWait +
        (prime : ℚ) ^ (depth * nextWait) /
          jacobiTail scale nextContent middle.2 target.2 =
      (centerNumerator : ℚ) / scale +
        (driftNumerator : ℚ) / scale *
          ((prime : ℚ) ^ (depth * wait) +
            ((prime : ℚ) ^ wait - 1) *
              jacobiTail scale content source.2 middle.2) := by
  have content_ne : (content : ℚ) ≠ 0 := by exact_mod_cast first.content_ne
  have scale_ne' : (scale : ℚ) ≠ 0 := by exact_mod_cast scale_ne
  have middleDenominator_ne' : (middle.2 : ℚ) ≠ 0 := by
    exact_mod_cast middleDenominator_ne
  have first_source :
      (source.1 : ℚ) =
        (prime : ℚ) ^ (depth * wait) * (content * middle.2) +
          scale * ((prime : ℚ) ^ wait - 1) * source.2 := by
    exact_mod_cast first.source_eq_power_mul_prequotient
  have first_target :
      (content * middle.1 : ℤ) =
        driftNumerator * source.1 +
          (centerNumerator - scale) * (content * middle.2) := by
    simpa only [endpointPrequotient] using first.target_eq_drift_add_prequotient
  have first_target' :
      (content : ℚ) * middle.1 =
        driftNumerator * source.1 +
          (centerNumerator - scale) * (content * middle.2) := by
    exact_mod_cast first_target
  have second_source :
      (middle.1 : ℚ) =
        (prime : ℚ) ^ (depth * nextWait) * (nextContent * target.2) +
          scale * ((prime : ℚ) ^ nextWait - 1) * middle.2 := by
    exact_mod_cast second.source_eq_power_mul_prequotient
  have source_ratio :
      (source.1 : ℚ) / (content * middle.2) =
        (prime : ℚ) ^ (depth * wait) +
          scale * ((prime : ℚ) ^ wait - 1) * source.2 /
            (content * middle.2) := by
    rw [first_source]
    field_simp [content_ne, middleDenominator_ne']
  have middle_ratio :
      (middle.1 : ℚ) / middle.2 =
        driftNumerator * (source.1 / (content * middle.2)) +
          (centerNumerator - scale) := by
    calc
      (middle.1 : ℚ) / middle.2 =
          (content * middle.1) / (content * middle.2) := by
        field_simp [content_ne, middleDenominator_ne']
        ring
      _ =
          (driftNumerator * source.1 +
            (centerNumerator - scale) * (content * middle.2)) /
              (content * middle.2) := by rw [first_target']
      _ =
          driftNumerator * (source.1 / (content * middle.2)) +
            (centerNumerator - scale) := by
        field_simp [content_ne, middleDenominator_ne']
  dsimp [jacobiTail]
  calc
    (prime : ℚ) ^ nextWait +
          (prime : ℚ) ^ (depth * nextWait) /
            (scale * middle.2 / (nextContent * target.2)) =
        1 + middle.1 / (scale * middle.2) := by
      rw [second_source]
      field_simp [scale_ne', middleDenominator_ne']
      ring
    _ =
        (centerNumerator : ℚ) / scale +
          (driftNumerator : ℚ) / scale *
            ((prime : ℚ) ^ (depth * wait) +
              ((prime : ℚ) ^ wait - 1) *
                (scale * source.2 / (content * middle.2))) := by
      rw [show
        (middle.1 : ℚ) / (scale * middle.2) =
          (middle.1 / middle.2) / scale by
            rw [div_div, mul_comm (scale : ℚ) middle.2]]
      rw [middle_ratio, source_ratio]
      field_simp [content_ne, scale_ne', middleDenominator_ne']
      ring

/-- Critical depth-two decoder. -/
def criticalDecoder (q : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![q, -1; 1 - q, 1]

/-- Projective order-three core of the critical decoder. -/
def criticalDecoderCore : Matrix (Fin 2) (Fin 2) ℚ :=
  !![0, -1; 1, 1]

/-- Lower-unipotent perturbation carrying the wait. -/
def criticalDecoderShear (q : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, 0; -q, 1]

theorem criticalDecoder_factor (q : ℚ) :
    criticalDecoder q = criticalDecoderCore * criticalDecoderShear q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [criticalDecoder, criticalDecoderCore, criticalDecoderShear,
      Matrix.mul_apply, Fin.sum_univ_succ, add_comm, sub_eq_add_neg]

theorem criticalDecoderCore_cube :
    criticalDecoderCore ^ 3 = -(1 : Matrix (Fin 2) (Fin 2) ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [criticalDecoderCore, pow_succ, Matrix.mul_apply,
      Fin.sum_univ_succ]

end
end MatrixMortality.ReturnGuard
