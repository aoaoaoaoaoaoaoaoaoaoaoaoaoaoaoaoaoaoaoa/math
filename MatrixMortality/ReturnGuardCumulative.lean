import MatrixMortality.ReturnGuardEndpoint

/-!
# Cumulative endpoint recurrence

Primitive normalization is not dynamical state.  Retaining every removed scalar turns the
terminal endpoint orbit into one integral pair recurrence with exact division by the forced
base power.  The reduced denominators and their signed contents are recovered from that pair;
they are not carried independently.
-/

namespace MatrixMortality.ReturnGuard

open MatrixMortality.PadicValuation
open scoped Matrix

noncomputable section

/-- Column represented by one integral projective pair. -/
def pairVector (pair : ℤ × ℤ) : Fin 2 → ℤ :=
  ![pair.1, pair.2]

/-- Terminal endpoint pair canonically induced by one integral residual pair. -/
def endpointPair
    (centerNumerator driftNumerator scale : ℤ) (residual : ℤ × ℤ) :
    ℤ × ℤ :=
  (terminalDefect centerNumerator driftNumerator scale residual.1 residual.2,
    residual.1)

theorem pairVector_endpointPair
    (centerNumerator driftNumerator scale : ℤ) (residual : ℤ × ℤ) :
    pairVector (endpointPair centerNumerator driftNumerator scale residual) =
  endpointVector centerNumerator driftNumerator scale residual.1 residual.2 := by
  ext i
  fin_cases i <;>
    simp [pairVector, endpointPair, endpointVector, terminalDefect]

/-- Projectivizing the endpoint pair recovers the terminal-centered coordinate. -/
theorem endpointPair_ratio_eq_terminalCoordinate
    (centerNumerator driftNumerator scale : ℤ) (residual : ℤ × ℤ)
    (numerator_ne : residual.1 ≠ 0) :
    ((endpointPair centerNumerator driftNumerator scale residual).1 : ℚ) /
        (endpointPair centerNumerator driftNumerator scale residual).2 =
      terminalCoordinate centerNumerator driftNumerator scale
        ((residual.1 : ℚ) / residual.2) := by
  have numerator_ne_rat : (residual.1 : ℚ) ≠ 0 := by
    exact_mod_cast numerator_ne
  simp only [endpointPair, terminalDefect, terminalCoordinate, Prod.fst, Prod.snd,
    Int.cast_add, Int.cast_sub, Int.cast_mul]
  field_simp [numerator_ne_rat]

/-- The reset endpoint pair; all cumulative normalization is derived from this state. -/
def cumulativeResetPair
    (centerNumerator driftNumerator scale : ℤ) : ℤ × ℤ :=
  (centerNumerator + driftNumerator - scale, 1)

theorem cumulativeResetPair_eq_endpointPair
    (centerNumerator driftNumerator scale : ℤ) :
    cumulativeResetPair centerNumerator driftNumerator scale =
      endpointPair centerNumerator driftNumerator scale (1, 1) := by
  apply Prod.ext
  · simp [cumulativeResetPair, endpointPair, terminalDefect]
    ring
  · simp [cumulativeResetPair, endpointPair]

/-- One content-free integral step in terminal endpoint coordinates. -/
structure CumulativeEndpointStep
    (prime depth : Nat) (centerNumerator driftNumerator scale : ℤ)
    (wait : Nat) (source target : ℤ × ℤ) : Prop where
  denominator :
    (prime : ℤ) ^ (depth * wait) * target.2 =
      source.1 - scale * ((prime : ℤ) ^ wait - 1) * source.2
  numerator :
    target.1 =
      driftNumerator * source.1 +
        (centerNumerator - scale) * target.2

/-- Exact finite cumulative execution with its chronological wait word. -/
inductive CumulativeEndpointExecution
    (prime depth : Nat) (centerNumerator driftNumerator scale : ℤ) :
    List Nat → (ℤ × ℤ) → (ℤ × ℤ) → Prop
  | nil (state : ℤ × ℤ) :
      CumulativeEndpointExecution prime depth centerNumerator driftNumerator scale
        [] state state
  | cons {wait : Nat} {waits : List Nat} {source middle target : ℤ × ℤ} :
      CumulativeEndpointStep prime depth centerNumerator driftNumerator scale
        wait source middle →
      CumulativeEndpointExecution prime depth centerNumerator driftNumerator scale
        waits middle target →
      CumulativeEndpointExecution prime depth centerNumerator driftNumerator scale
        (wait :: waits) source target

/-- One primitive endpoint reduction, retaining its signed removed content. -/
structure PrimitiveEndpointReduction
    (prime depth : Nat) (centerNumerator driftNumerator scale : ℤ)
    (wait : Nat) (source target : ℤ × ℤ) (content : ℤ) : Prop where
  source_coprime : IsCoprime source.1 source.2
  target_coprime : IsCoprime target.1 target.2
  wait_positive : 0 < wait
  content_ne : content ≠ 0
  step :
    CumulativeEndpointStep prime depth centerNumerator driftNumerator scale
      wait source (content * target.1, content * target.2)

/-- Primitive reduction of the residual recurrence induces the content-free endpoint step.
The removed content scales the target pair but never becomes an independent state variable. -/
theorem primitiveIntegralStep_cumulativeEndpointStep
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {source target : ℤ × ℤ}
    (primitive :
      PrimitiveIntegralStep prime depth centerNumerator driftNumerator scale
        source target) :
    ∃ wait content,
      CumulativeEndpointStep prime depth centerNumerator driftNumerator scale wait
        (endpointPair centerNumerator driftNumerator scale source)
        (content *
            (endpointPair centerNumerator driftNumerator scale target).1,
          content *
            (endpointPair centerNumerator driftNumerator scale target).2) := by
  rcases primitive with
    ⟨_, _, wait, rawNumerator, rawDenominator, content,
      integral, numeratorReduced, denominatorReduced⟩
  refine ⟨wait, content, ?_⟩
  constructor
  · dsimp [endpointPair]
    rw [← numeratorReduced, integral.1]
    simp [integralStepNumerator, terminalDefect]
    ring
  · dsimp [endpointPair]
    simp only [terminalDefect]
    have rawDenominator_eq :
        rawDenominator =
          (centerNumerator - scale) * source.1 +
            driftNumerator * source.2 := by
      simpa only [terminalDefect] using integral.2
    rw [show
      content *
          ((centerNumerator - scale) * target.1 +
            driftNumerator * target.2) =
        (centerNumerator - scale) * (content * target.1) +
          driftNumerator * (content * target.2) by ring]
    rw [numeratorReduced.symm, denominatorReduced.symm, rawDenominator_eq]
    ring

/-- For a fixed source and wait, exact cumulative division determines at most one target. -/
theorem CumulativeEndpointStep.target_unique
    {prime depth : Nat} [Fact prime.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {source left right : ℤ × ℤ}
    (leftStep :
      CumulativeEndpointStep prime depth centerNumerator driftNumerator scale
        wait source left)
    (rightStep :
      CumulativeEndpointStep prime depth centerNumerator driftNumerator scale
        wait source right) :
    left = right := by
  have power_ne : (prime : ℤ) ^ (depth * wait) ≠ 0 := by
    exact pow_ne_zero _ (by
      exact_mod_cast (Fact.out : prime.Prime).ne_zero)
  have denominator_eq : left.2 = right.2 := by
    apply mul_left_cancel₀ power_ne
    rw [leftStep.denominator, rightStep.denominator]
  apply Prod.ext
  · rw [leftStep.numerator, rightStep.numerator, denominator_eq]
  · exact denominator_eq

/-- Primitive reduction commutes with any cumulative exterior scale. -/
theorem PrimitiveEndpointReduction.cumulativeStep
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {source target : ℤ × ℤ} {content cumulative : ℤ}
    (reduction :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        wait source target content) :
    CumulativeEndpointStep prime depth centerNumerator driftNumerator scale wait
      (cumulative * source.1, cumulative * source.2)
      (cumulative * content * target.1, cumulative * content * target.2) := by
  constructor
  · change
      (prime : ℤ) ^ (depth * wait) *
          (cumulative * content * target.2) =
        cumulative * source.1 -
          scale * ((prime : ℤ) ^ wait - 1) *
            (cumulative * source.2)
    calc
      _ = cumulative *
          ((prime : ℤ) ^ (depth * wait) * (content * target.2)) := by ring
      _ = cumulative *
          (source.1 - scale * ((prime : ℤ) ^ wait - 1) * source.2) := by
        rw [reduction.step.denominator]
      _ = _ := by ring
  · change
      cumulative * content * target.1 =
        driftNumerator * (cumulative * source.1) +
          (centerNumerator - scale) *
            (cumulative * content * target.2)
    have numerator := reduction.step.numerator
    simp only [Prod.fst, Prod.snd] at numerator
    calc
      cumulative * content * target.1 =
          cumulative * (content * target.1) := by ring
      _ = cumulative *
          (driftNumerator * source.1 +
            (centerNumerator - scale) * (content * target.2)) := by
        rw [numerator]
      _ = _ := by ring

/-- The prequotient of a primitive endpoint reduction is coprime to the source denominator. -/
theorem PrimitiveEndpointReduction.prequotient_coprime_denominator
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {source target : ℤ × ℤ} {content : ℤ}
    (reduction :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        wait source target content) :
    IsCoprime (content * target.2) source.2 := by
  obtain ⟨left, right, bezout⟩ := reduction.source_coprime
  refine ⟨left * (prime : ℤ) ^ (depth * wait),
    left * scale * ((prime : ℤ) ^ wait - 1) + right, ?_⟩
  have source_numerator :
      source.1 =
        (prime : ℤ) ^ (depth * wait) * (content * target.2) +
          scale * ((prime : ℤ) ^ wait - 1) * source.2 := by
    exact (eq_sub_iff_add_eq.mp reduction.step.denominator).symm
  calc
    left * (prime : ℤ) ^ (depth * wait) * (content * target.2) +
        (left * scale * ((prime : ℤ) ^ wait - 1) + right) * source.2 =
      left * source.1 + right * source.2 := by
      rw [source_numerator]
      ring
    _ = 1 := bezout

/-- The endpoint transfer carries a cumulative pair to the next pair with only the forced
base-power scalar remaining. -/
theorem CumulativeEndpointStep.transfer
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {source target : ℤ × ℤ}
    (step :
      CumulativeEndpointStep prime depth centerNumerator driftNumerator scale
        wait source target) :
    (endpointTransfer (prime : ℤ) depth centerNumerator driftNumerator scale
        wait) *ᵥ (pairVector source) =
      (prime : ℤ) ^ (depth * wait) • (pairVector target) := by
  ext i
  fin_cases i
  · simp [endpointTransfer, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_succ, pairVector, smul_eq_mul]
    rw [step.numerator]
    have main :
        (centerNumerator - scale +
                driftNumerator * (prime : ℤ) ^ (depth * wait)) * source.1 -
            (centerNumerator - scale) * scale *
                ((prime : ℤ) ^ wait - 1) * source.2 =
          (prime : ℤ) ^ (depth * wait) *
            (driftNumerator * source.1 +
              (centerNumerator - scale) * target.2) := by
      calc
        _ =
            driftNumerator * (prime : ℤ) ^ (depth * wait) * source.1 +
              (centerNumerator - scale) *
                (source.1 - scale * ((prime : ℤ) ^ wait - 1) * source.2) := by
          ring
        _ =
            driftNumerator * (prime : ℤ) ^ (depth * wait) * source.1 +
              (centerNumerator - scale) *
                ((prime : ℤ) ^ (depth * wait) * target.2) := by
          rw [← step.denominator]
        _ = _ := by ring
    convert main using 1
    all_goals ring
  · simpa [endpointTransfer, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_succ, pairVector, smul_eq_mul] using step.denominator.symm

/-- A cumulative execution transports its initial pair by the full endpoint product and strips
exactly the product of the forced base powers. -/
theorem CumulativeEndpointExecution.transfer
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {waits : List Nat} {source target : ℤ × ℤ}
    (execution :
      CumulativeEndpointExecution prime depth centerNumerator driftNumerator scale
        waits source target) :
    endpointProduct (prime : ℤ) depth centerNumerator driftNumerator scale waits *ᵥ
        pairVector source =
      (prime : ℤ) ^ (depth * waits.sum) • pairVector target := by
  induction execution with
  | nil state =>
      simp [pairVector]
  | @cons wait waits source middle target step _ induction =>
      rw [endpointProduct_cons, ← Matrix.mulVec_mulVec, step.transfer,
        Matrix.mulVec_smul, induction, smul_smul]
      rw [List.sum_cons, Nat.mul_add, pow_add]

/-- The signed primitive content is exactly the gcd of the endpoint prequotient and the full
cyclotomic determinant support. -/
theorem PrimitiveEndpointReduction.content_natAbs_eq_gcd_support
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {source target : ℤ × ℤ} {content : ℤ}
    (reduction :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        wait source target content) :
    content.natAbs =
      Nat.gcd (content * target.2).natAbs
        (driftNumerator * scale * ((prime : ℤ) ^ wait - 1)).natAbs := by
  let prequotient := content * target.2
  let support :=
    driftNumerator * scale * ((prime : ℤ) ^ wait - 1)
  have source_numerator :
      source.1 =
        (prime : ℤ) ^ (depth * wait) * prequotient +
          scale * ((prime : ℤ) ^ wait - 1) * source.2 := by
    dsimp [prequotient]
    exact (eq_sub_iff_add_eq.mp reduction.step.denominator).symm
  have content_dvd_prequotient : content ∣ prequotient := by
    exact ⟨target.2, rfl⟩
  have content_coprime_denominator : IsCoprime content source.2 :=
    IsCoprime.of_isCoprime_of_dvd_left
      reduction.prequotient_coprime_denominator content_dvd_prequotient
  have content_dvd_drift_source : content ∣ driftNumerator * source.1 := by
    use target.1 - (centerNumerator - scale) * target.2
    have target_eq := reduction.step.numerator
    simp only [Prod.fst, Prod.snd] at target_eq
    calc
      driftNumerator * source.1 =
          content * target.1 -
            (centerNumerator - scale) * (content * target.2) := by
        linarith
      _ = content *
          (target.1 - (centerNumerator - scale) * target.2) := by ring
  have content_dvd_support_mul_denominator :
      content ∣ source.2 * support := by
    obtain ⟨quotient, quotient_eq⟩ := content_dvd_drift_source
    use quotient -
      driftNumerator * (prime : ℤ) ^ (depth * wait) * target.2
    have drift_source_expanded :
        driftNumerator * source.1 =
          driftNumerator * (prime : ℤ) ^ (depth * wait) *
              (content * target.2) +
            source.2 * support := by
      rw [source_numerator]
      dsimp [support]
      ring
    rw [drift_source_expanded] at quotient_eq
    linear_combination quotient_eq
  have content_dvd_support : content ∣ support :=
    content_coprime_denominator.dvd_of_dvd_mul_left
      content_dvd_support_mul_denominator
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd
      (Int.natAbs_dvd_natAbs.mpr content_dvd_prequotient)
      (Int.natAbs_dvd_natAbs.mpr content_dvd_support)
  · let common : ℤ :=
      Nat.gcd prequotient.natAbs support.natAbs
    have common_dvd_prequotient : common ∣ prequotient := by
      exact Int.natAbs_dvd_natAbs.mp (Nat.gcd_dvd_left _ _)
    have common_dvd_support : common ∣ support := by
      exact Int.natAbs_dvd_natAbs.mp (Nat.gcd_dvd_right _ _)
    have common_dvd_rawNumerator :
        common ∣
          driftNumerator * source.1 +
            (centerNumerator - scale) * prequotient := by
      obtain ⟨prequotientFactor, prequotient_eq⟩ := common_dvd_prequotient
      obtain ⟨supportFactor, support_eq⟩ := common_dvd_support
      use
        (driftNumerator * (prime : ℤ) ^ (depth * wait) +
            centerNumerator - scale) * prequotientFactor +
          source.2 * supportFactor
      change
        driftNumerator * source.1 +
            (centerNumerator - scale) * prequotient =
          common *
            ((driftNumerator * (prime : ℤ) ^ (depth * wait) +
                centerNumerator - scale) * prequotientFactor +
              source.2 * supportFactor)
      have support_expanded := support_eq
      dsimp [support] at support_expanded
      linear_combination
        driftNumerator * source_numerator +
          (driftNumerator * (prime : ℤ) ^ (depth * wait) +
            centerNumerator - scale) * prequotient_eq +
          source.2 * support_expanded
    have common_dvd_content : common ∣ content := by
      apply
        (divisor_dvd_commonFactor_iff
          (left := prequotient)
          (right :=
            driftNumerator * source.1 +
              (centerNumerator - scale) * prequotient)
          (common := content) (reducedLeft := target.2)
          (reducedRight := target.1)
          (by rfl) (by
            dsimp [prequotient]
            simpa only [Prod.fst, Prod.snd, add_comm] using
              reduction.step.numerator.symm)
          reduction.target_coprime.symm).mpr
      exact ⟨common_dvd_prequotient, common_dvd_rawNumerator⟩
    exact Int.natAbs_dvd_natAbs.mpr common_dvd_content

/-- Consecutive primitive endpoint denominators are coprime. -/
theorem PrimitiveEndpointReduction.denominators_coprime
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {source target : ℤ × ℤ} {content : ℤ}
    (reduction :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        wait source target content) :
    IsCoprime source.2 target.2 := by
  exact
    (IsCoprime.of_isCoprime_of_dvd_left
      reduction.prequotient_coprime_denominator
      (show target.2 ∣ content * target.2 by exact dvd_mul_left _ _)).symm

/-- The next primitive denominator is coprime to the complementary determinant content. -/
theorem PrimitiveEndpointReduction.denominator_coprime_complement
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {source target : ℤ × ℤ} {content complement : ℤ}
    (reduction :
      PrimitiveEndpointReduction prime depth centerNumerator driftNumerator scale
        wait source target content)
    (complementary :
      content * complement =
        driftNumerator * scale * ((prime : ℤ) ^ wait - 1)) :
    IsCoprime target.2 complement := by
  have gcd_eq :
      Int.gcd (content * target.2) (content * complement) = content.natAbs := by
    rw [complementary, Int.gcd_eq_natAbs]
    exact reduction.content_natAbs_eq_gcd_support.symm
  apply Int.gcd_eq_one_iff_coprime.mp
  rw [Int.gcd_mul_left] at gcd_eq
  have content_positive : 0 < content.natAbs :=
    Int.natAbs_pos.mpr reduction.content_ne
  apply Nat.eq_of_mul_eq_mul_left content_positive
  calc
    content.natAbs * Int.gcd target.2 complement = content.natAbs := gcd_eq
    _ = content.natAbs * 1 := by ring

/-- The endpoint adjugate exposes one wait-independent resultant controlling every reverse
complementary content. -/
theorem reverseComplement_dvd_targetResultant
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {source target : ℤ × ℤ} {complement : ℤ}
    (reverse :
      (endpointAdjugate (prime : ℤ) depth centerNumerator driftNumerator scale
          wait) *ᵥ (pairVector target) =
        (-complement) • (pairVector source)) :
    complement ∣
      scale * ((centerNumerator - scale) * target.2 - target.1) *
        ((centerNumerator - scale) * target.2 - target.1 +
          driftNumerator * target.2) := by
  let defect := (centerNumerator - scale) * target.2 - target.1
  have first :
      scale * ((prime : ℤ) ^ wait - 1) * defect =
        -complement * source.1 := by
    have coordinate := congrFun reverse 0
    simp only [endpointAdjugate, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_succ, pairVector, smul_eq_mul] at coordinate
    convert coordinate using 1
    all_goals dsimp [defect]; ring
  have second :
      defect + driftNumerator * (prime : ℤ) ^ (depth * wait) * target.2 =
        -complement * source.2 := by
    have coordinate := congrFun reverse 1
    simp only [endpointAdjugate, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_succ, pairVector, smul_eq_mul] at coordinate
    convert coordinate using 1
    all_goals dsimp [defect]; ring
  have first_dvd :
      complement ∣ scale * ((prime : ℤ) ^ wait - 1) * defect := by
    exact ⟨-source.1, by rw [first]; ring⟩
  have second_dvd :
      complement ∣
        defect + driftNumerator * (prime : ℤ) ^ (depth * wait) * target.2 := by
    exact ⟨-source.2, by rw [second]; ring⟩
  have cyclotomic :
      (prime : ℤ) ^ wait - 1 ∣
        (prime : ℤ) ^ (depth * wait) - 1 := by
    simpa only [pow_mul, Nat.mul_comm depth wait] using
      (sub_one_dvd_pow_sub_one (x := (prime : ℤ) ^ wait) (n := depth))
  obtain ⟨factor, factor_eq⟩ := cyclotomic
  have first_scaled_dvd :
      complement ∣
        scale * ((prime : ℤ) ^ (depth * wait) - 1) * defect := by
    obtain ⟨quotient, quotient_eq⟩ := first_dvd
    refine ⟨quotient * factor, ?_⟩
    rw [factor_eq]
    calc
      scale * (((prime : ℤ) ^ wait - 1) * factor) * defect =
          (scale * ((prime : ℤ) ^ wait - 1) * defect) * factor := by ring
      _ = (complement * quotient) * factor := by rw [quotient_eq]
      _ = complement * (quotient * factor) := by ring
  have combination :=
    dvd_sub
      (second_dvd.mul_left (scale * defect))
      (first_scaled_dvd.mul_left (driftNumerator * target.2))
  convert combination using 1
  all_goals dsimp [defect]; ring

/-- The last reverse content of a terminal bridge divides one fixed parameter resultant,
independently of its wait. -/
theorem reverseComplement_dvd_terminalResultant
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {source : ℤ × ℤ} {complement : ℤ}
    (reverse :
      (endpointAdjugate (prime : ℤ) depth centerNumerator driftNumerator scale
          wait) *ᵥ (pairVector ((0 : ℤ), (1 : ℤ))) =
        (-complement) • (pairVector source)) :
    complement ∣
      scale * (centerNumerator - scale) *
        (centerNumerator - scale + driftNumerator) := by
  simpa using
    (reverseComplement_dvd_targetResultant
      (prime := prime) (depth := depth)
      (centerNumerator := centerNumerator)
      (driftNumerator := driftNumerator) (scale := scale)
      (wait := wait) (source := source) (target := ((0 : ℤ), (1 : ℤ)))
      reverse)

/-- Two consecutive cumulative steps eliminate the intermediate numerator and expose the
content-free denominator recurrence. -/
theorem cumulativeDenominator_recurrence
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait nextWait : Nat} {prior current next : ℤ × ℤ}
    (first :
      CumulativeEndpointStep prime depth centerNumerator driftNumerator scale
        wait prior current)
    (second :
      CumulativeEndpointStep prime depth centerNumerator driftNumerator scale
        nextWait current next) :
    (prime : ℤ) ^ (depth * nextWait) * next.2 =
      (centerNumerator +
          driftNumerator * (prime : ℤ) ^ (depth * wait) -
          scale * (prime : ℤ) ^ nextWait) * current.2 +
        driftNumerator * scale * ((prime : ℤ) ^ wait - 1) * prior.2 := by
  rw [second.denominator, first.numerator]
  have prior_numerator :
      prior.1 =
        (prime : ℤ) ^ (depth * wait) * current.2 +
          scale * ((prime : ℤ) ^ wait - 1) * prior.2 := by
    linarith [first.denominator]
  rw [prior_numerator]
  ring

/-- The terminal tail is exactly the ratio of consecutive cumulative denominators. -/
theorem terminalTail_eq_cumulativeDenominatorRatio
    {prime depth : Nat} [Fact prime.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {source target : ℤ × ℤ}
    (source_denominator_ne : source.2 ≠ 0)
    (step :
      CumulativeEndpointStep prime depth centerNumerator driftNumerator scale
        wait source target) :
    terminalTail prime depth scale wait ((source.1 : ℚ) / source.2) =
      (target.2 : ℚ) / source.2 := by
  have source_denominator_ne_rat : (source.2 : ℚ) ≠ 0 := by
    exact_mod_cast source_denominator_ne
  have denominator_cast :
      (prime : ℚ) ^ (depth * wait) * target.2 =
        source.1 - scale * ((prime : ℚ) ^ wait - 1) * source.2 := by
    exact_mod_cast step.denominator
  have prime_power_ne : (prime : ℚ) ^ (depth * wait) ≠ 0 :=
    primePower_ne_zero Fact.out (depth * wait)
  rw [terminalTail]
  calc
    (((source.1 : ℚ) / source.2 -
          scale * ((prime : ℚ) ^ wait - 1)) /
        (prime : ℚ) ^ (depth * wait)) =
        ((source.1 : ℚ) -
            scale * ((prime : ℚ) ^ wait - 1) * source.2) /
          ((prime : ℚ) ^ (depth * wait) * source.2) := by
      field_simp [source_denominator_ne_rat, prime_power_ne]
      ring
    _ =
        ((prime : ℚ) ^ (depth * wait) * target.2) /
          ((prime : ℚ) ^ (depth * wait) * source.2) := by
      rw [denominator_cast]
    _ = (target.2 : ℚ) / source.2 := by
      field_simp [source_denominator_ne_rat, prime_power_ne]
      ring

/-- Unit-tail coordinate carried by two consecutive cumulative denominators. -/
def cumulativeUnitTail (scale prior next : ℤ) : ℚ :=
  (scale : ℚ) * prior / next

/-- The exact unit-tail transition contains no multiplicative copy of the old tail. -/
theorem cumulativeUnitTail_transition
    {prime depth : Nat} [Fact prime.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    {wait nextWait : Nat} {prior current next : ℤ × ℤ}
    (current_denominator_ne : current.2 ≠ 0)
    (next_denominator_ne : next.2 ≠ 0)
    (first :
      CumulativeEndpointStep prime depth centerNumerator driftNumerator scale
        wait prior current)
    (second :
      CumulativeEndpointStep prime depth centerNumerator driftNumerator scale
        nextWait current next) :
    cumulativeUnitTail scale current.2 next.2 =
      (scale : ℚ) * (prime : ℚ) ^ (depth * nextWait) /
        (driftNumerator * ((prime : ℚ) ^ wait - 1) *
            cumulativeUnitTail scale prior.2 current.2 +
          centerNumerator +
            driftNumerator * (prime : ℚ) ^ (depth * wait) -
          scale * (prime : ℚ) ^ nextWait) := by
  have current_denominator_ne_rat : (current.2 : ℚ) ≠ 0 := by
    exact_mod_cast current_denominator_ne
  have next_denominator_ne_rat : (next.2 : ℚ) ≠ 0 := by
    exact_mod_cast next_denominator_ne
  have recurrence :
      (prime : ℚ) ^ (depth * nextWait) * next.2 =
        (centerNumerator +
            driftNumerator * (prime : ℚ) ^ (depth * wait) -
            scale * (prime : ℚ) ^ nextWait) * current.2 +
          driftNumerator * scale * ((prime : ℚ) ^ wait - 1) * prior.2 := by
    exact_mod_cast cumulativeDenominator_recurrence first second
  have prime_power_ne : (prime : ℚ) ^ (depth * nextWait) ≠ 0 :=
    primePower_ne_zero Fact.out (depth * nextWait)
  let divisor : ℚ :=
    driftNumerator * ((prime : ℚ) ^ wait - 1) *
        cumulativeUnitTail scale prior.2 current.2 +
      centerNumerator +
        driftNumerator * (prime : ℚ) ^ (depth * wait) -
      scale * (prime : ℚ) ^ nextWait
  have divisor_eq :
      divisor =
        (prime : ℚ) ^ (depth * nextWait) * next.2 / current.2 := by
    dsimp [divisor, cumulativeUnitTail]
    field_simp [current_denominator_ne_rat]
    simp only [Nat.mul_comm depth wait] at recurrence ⊢
    rw [recurrence]
    ring
  change
    (scale : ℚ) * current.2 / next.2 =
      (scale : ℚ) * (prime : ℚ) ^ (depth * nextWait) / divisor
  rw [divisor_eq]
  field_simp [current_denominator_ne_rat, next_denominator_ne_rat,
    prime_power_ne]
  ring

/-- The cumulative numerator alone obeys a deterministic second-order exact-division law. -/
theorem cumulativeNumerator_recurrence
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {wait : Nat} {previous source target : ℤ × ℤ}
    (previous_relation :
      source.1 - driftNumerator * previous.1 =
        (centerNumerator - scale) * source.2)
    (step :
      CumulativeEndpointStep prime depth centerNumerator driftNumerator scale
        wait source target) :
    (prime : ℤ) ^ (depth * wait) * target.1 =
      (driftNumerator * (prime : ℤ) ^ (depth * wait) +
          centerNumerator - scale * (prime : ℤ) ^ wait) * source.1 +
        driftNumerator * scale * ((prime : ℤ) ^ wait - 1) * previous.1 := by
  calc
    (prime : ℤ) ^ (depth * wait) * target.1 =
        (prime : ℤ) ^ (depth * wait) *
          (driftNumerator * source.1 +
            (centerNumerator - scale) * target.2) := by
      rw [step.numerator]
    _ = driftNumerator * (prime : ℤ) ^ (depth * wait) * source.1 +
        (centerNumerator - scale) *
          (source.1 - scale * ((prime : ℤ) ^ wait - 1) * source.2) := by
      have scaled :=
        congrArg ((centerNumerator - scale) * ·) step.denominator
      linear_combination scaled
    _ =
      (driftNumerator * (prime : ℤ) ^ (depth * wait) +
          centerNumerator - scale * (prime : ℤ) ^ wait) * source.1 +
        driftNumerator * scale * ((prime : ℤ) ^ wait - 1) * previous.1 := by
      linear_combination
        scale * ((prime : ℤ) ^ wait - 1) * previous_relation

/-- The valuation-bearing linear form factors through the current endpoint numerator and
denominator. -/
theorem cumulativeWaitForm_eq
    {centerNumerator driftNumerator scale : ℤ}
    {previous source : ℤ × ℤ}
    (previous_relation :
      source.1 - driftNumerator * previous.1 =
        (centerNumerator - scale) * source.2) :
    centerNumerator * source.1 -
        driftNumerator * scale * previous.1 =
      (centerNumerator - scale) * (source.1 + scale * source.2) := by
  linear_combination scale * previous_relation

/-- A cumulative endpoint pair is terminal exactly when its first coordinate vanishes. -/
theorem cumulativeEndpoint_eq_zero_iff
    {numerator denominator : ℤ} (denominator_ne : denominator ≠ 0) :
    (numerator : ℚ) / denominator = 0 ↔ numerator = 0 := by
  have denominator_ne_rat : (denominator : ℚ) ≠ 0 := by
    exact_mod_cast denominator_ne
  simp [denominator_ne_rat]

/-- The first row of a terminal truncant measures the cumulative numerator after removing the
entire forced base power. -/
theorem terminalTruncant_eq_cumulativeNumerator
    {prime depth : Nat} {centerNumerator driftNumerator scale : ℤ}
    {waits : List Nat} {target : ℤ × ℤ}
    (execution :
      CumulativeEndpointExecution prime depth centerNumerator driftNumerator scale
        waits (cumulativeResetPair centerNumerator driftNumerator scale) target) :
    (centerNumerator + driftNumerator - scale) *
          (endpointProduct (prime : ℤ) depth centerNumerator driftNumerator scale
            waits) 0 0 +
        (endpointProduct (prime : ℤ) depth centerNumerator driftNumerator scale
          waits) 0 1 =
      (prime : ℤ) ^ (depth * waits.sum) * target.1 := by
  have transported := congrFun execution.transfer 0
  simpa [endpointProduct, cumulativeResetPair, pairVector,
    Matrix.mulVec, Matrix.dotProduct,
    Fin.sum_univ_succ, smul_eq_mul, mul_comm] using transported

end
end MatrixMortality.ReturnGuard
