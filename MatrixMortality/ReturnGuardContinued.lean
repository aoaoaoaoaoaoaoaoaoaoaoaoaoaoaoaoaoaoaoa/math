import Mathlib.Algebra.Ring.GeomSum
import MatrixMortality.ReturnGuardCumulative

/-!
# Fixed-cusp endpoint calculus

The cumulative endpoint recurrence admits one canonical Euclidean quotient and one fixed
forbidden cusp.  This file records those laws without introducing another dynamical state.
It also exposes the exact two-step identity behind record-wait height bounds.
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
      simp only at numerator
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
    simp only at numerator
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
    simp only [terminalPredecessorPair] <;> ring

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
  simp only at first_numerator second_denominator ⊢
  linear_combination content * second_denominator + first_numerator

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
    simp only at denominator
    have absolute := congrArg Int.natAbs denominator
    simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at absolute
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
    simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at absolute
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
              simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast, y]
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
