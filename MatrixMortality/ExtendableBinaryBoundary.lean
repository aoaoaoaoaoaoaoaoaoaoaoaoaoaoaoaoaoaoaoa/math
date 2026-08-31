import MatrixMortality.CyclicBinaryBoundary

/-!
# Endomorphism-extendable fixed boundaries

When one positive source morphism factors through the other by an ambient group endomorphism,
fixed-boundary equality is ordinary endomorphism-twisted conjugacy on the second positive trace.
The group solutions form a coset of one twisted stabilizer.  For free groups, computability of
endomorphism fixed subgroups and rational-set intersection therefore decides this stratum.
-/

namespace MatrixMortality.ExtendableBinaryBoundary

open CyclicBinaryBoundary PositiveFreeCancellation

/-- A witness carrying `initial` to `terminal` under endomorphism-twisted conjugacy. -/
def EndoTwistedConjugator {G : Type*} [Group G] (endomorphism : G →* G)
    (initial terminal witness : G) : Prop :=
  terminal = (endomorphism witness)⁻¹ * initial * witness

/-- The stabilizer controlling differences between endomorphism-twisted conjugators. -/
def EndoTwistedStabilizer {G : Type*} [Group G] (endomorphism : G →* G)
    (initial element : G) : Prop :=
  endomorphism element * initial = initial * element

/-- A letterwise ambient endomorphism extension transports every positive source word. -/
theorem positiveEvaluate_extension
    {S G : Type*} [Group G] (upper lower : S → G) (endomorphism : G →* G)
    (extension : ∀ letter, endomorphism (lower letter) = upper letter) (word : List S) :
    endomorphism (positiveEvaluate lower word) = positiveEvaluate upper word := by
  induction word with
  | nil => simp
  | cons letter word induction =>
      rw [positiveEvaluate_cons, map_mul, extension letter, induction,
        positiveEvaluate_cons]

/-- Four fixed boundaries reduce to the two relative boundaries adjacent to the positive trace. -/
theorem boundaryEquation_iff_normalized
    {S G : Type*} [Group G] (upper lower : S → G)
    (upperLeft upperRight lowerLeft lowerRight : G) (word : List S) :
    BoundaryEquation upper lower upperLeft upperRight lowerLeft lowerRight word ↔
      positiveEvaluate upper word * (upperRight * lowerRight⁻¹) =
        (upperLeft⁻¹ * lowerLeft) * positiveEvaluate lower word := by
  rw [BoundaryEquation]
  constructor
  · intro equation
    calc
      positiveEvaluate upper word * (upperRight * lowerRight⁻¹) =
          upperLeft⁻¹ *
            (upperLeft * positiveEvaluate upper word * upperRight) * lowerRight⁻¹ := by
        group
      _ = upperLeft⁻¹ *
            (lowerLeft * positiveEvaluate lower word * lowerRight) * lowerRight⁻¹ := by
        rw [equation]
      _ = (upperLeft⁻¹ * lowerLeft) * positiveEvaluate lower word := by group
  · intro equation
    calc
      upperLeft * positiveEvaluate upper word * upperRight =
          upperLeft *
            (positiveEvaluate upper word * (upperRight * lowerRight⁻¹)) * lowerRight := by
        group
      _ = upperLeft *
            ((upperLeft⁻¹ * lowerLeft) * positiveEvaluate lower word) * lowerRight := by
        rw [equation]
      _ = lowerLeft * positiveEvaluate lower word * lowerRight := by group

/-- Under an ambient endomorphism extension, positive fixed-boundary equality is exactly one
endomorphism-twisted conjugacy equation. -/
theorem boundaryEquation_iff_endoTwistedConjugator
    {S G : Type*} [Group G] (upper lower : S → G) (endomorphism : G →* G)
    (extension : ∀ letter, endomorphism (lower letter) = upper letter)
    (upperLeft upperRight lowerLeft lowerRight : G) (word : List S) :
    BoundaryEquation upper lower upperLeft upperRight lowerLeft lowerRight word ↔
      EndoTwistedConjugator endomorphism (upperLeft⁻¹ * lowerLeft)
        (upperRight * lowerRight⁻¹) (positiveEvaluate lower word) := by
  rw [boundaryEquation_iff_normalized,
    ← positiveEvaluate_extension upper lower endomorphism extension word]
  unfold EndoTwistedConjugator
  constructor
  · intro equation
    calc
      upperRight * lowerRight⁻¹ =
          (endomorphism (positiveEvaluate lower word))⁻¹ *
            (endomorphism (positiveEvaluate lower word) * (upperRight * lowerRight⁻¹)) := by
        group
      _ = (endomorphism (positiveEvaluate lower word))⁻¹ *
            ((upperLeft⁻¹ * lowerLeft) * positiveEvaluate lower word) := by
        rw [equation]
      _ = (endomorphism (positiveEvaluate lower word))⁻¹ *
            (upperLeft⁻¹ * lowerLeft) * positiveEvaluate lower word := by group
  · intro equation
    calc
      endomorphism (positiveEvaluate lower word) * (upperRight * lowerRight⁻¹) =
          endomorphism (positiveEvaluate lower word) *
            ((endomorphism (positiveEvaluate lower word))⁻¹ *
              (upperLeft⁻¹ * lowerLeft) * positiveEvaluate lower word) := by
        rw [equation]
      _ = (upperLeft⁻¹ * lowerLeft) * positiveEvaluate lower word := by group

/-- Left multiplication by a twisted stabilizer preserves one twisted conjugator, and every
such preservation comes from the stabilizer. -/
theorem endoTwistedConjugator_mul_iff
    {G : Type*} [Group G] (endomorphism : G →* G) (initial terminal base element : G)
    (base_conjugator : EndoTwistedConjugator endomorphism initial terminal base) :
    EndoTwistedConjugator endomorphism initial terminal (element * base) ↔
      EndoTwistedStabilizer endomorphism initial element := by
  unfold EndoTwistedConjugator at base_conjugator ⊢
  unfold EndoTwistedStabilizer
  constructor
  · intro conjugator
    have equality :
        (endomorphism base)⁻¹ * (endomorphism element)⁻¹ * initial * element * base =
          (endomorphism base)⁻¹ * initial * base := by
      simpa only [map_mul, mul_inv_rev, mul_assoc] using
        conjugator.symm.trans base_conjugator
    have core : (endomorphism element)⁻¹ * initial * element = initial := by
      calc
        (endomorphism element)⁻¹ * initial * element =
            endomorphism base *
              ((endomorphism base)⁻¹ * (endomorphism element)⁻¹ * initial * element * base) *
              base⁻¹ := by
          group
        _ = endomorphism base * ((endomorphism base)⁻¹ * initial * base) * base⁻¹ := by
          rw [equality]
        _ = initial := by group
    have reverse : initial * element = endomorphism element * initial := by
      calc
        initial * element =
            endomorphism element * ((endomorphism element)⁻¹ * initial * element) := by
          group
        _ = endomorphism element * initial := by rw [core]
    exact reverse.symm
  · intro stabilizer
    calc
      terminal = (endomorphism base)⁻¹ * initial * base := base_conjugator
      _ = (endomorphism base)⁻¹ * (endomorphism element)⁻¹ *
            (endomorphism element * initial) * base := by
        group
      _ = (endomorphism base)⁻¹ * (endomorphism element)⁻¹ *
            (initial * element) * base := by
        rw [stabilizer]
      _ = (endomorphism (element * base))⁻¹ * initial * (element * base) := by
        rw [map_mul, mul_inv_rev]
        group

/-- Once one twisted conjugator is known, every other one is uniquely its left translate by the
twisted stabilizer. -/
theorem endoTwistedConjugator_iff_stabilizer_mul
    {G : Type*} [Group G] (endomorphism : G →* G) (initial terminal base witness : G)
    (base_conjugator : EndoTwistedConjugator endomorphism initial terminal base) :
    EndoTwistedConjugator endomorphism initial terminal witness ↔
      ∃ element, EndoTwistedStabilizer endomorphism initial element ∧
        witness = element * base := by
  constructor
  · intro conjugator
    let element := witness * base⁻¹
    refine ⟨element, ?_, by simp [element]⟩
    apply (endoTwistedConjugator_mul_iff endomorphism initial terminal base element
      base_conjugator).mp
    simpa [element] using conjugator
  · rintro ⟨element, stabilizer, rfl⟩
    exact (endoTwistedConjugator_mul_iff endomorphism initial terminal base element
      base_conjugator).mpr stabilizer

/-- The existential positive fixed-boundary problem is intersection of the lower positive trace
with one endomorphism-twisted conjugacy class. -/
theorem exists_boundaryEquation_iff_trace_inter_endoTwisted_nonempty
    {S G : Type*} [Group G] (upper lower : S → G) (endomorphism : G →* G)
    (extension : ∀ letter, endomorphism (lower letter) = upper letter)
    (upperLeft upperRight lowerLeft lowerRight : G) :
    (∃ word : List S,
        BoundaryEquation upper lower upperLeft upperRight lowerLeft lowerRight word) ↔
      Set.Nonempty
        (Set.range (positiveEvaluate lower) ∩
          {witness |
            EndoTwistedConjugator endomorphism (upperLeft⁻¹ * lowerLeft)
              (upperRight * lowerRight⁻¹) witness}) := by
  constructor
  · rintro ⟨word, equation⟩
    refine ⟨positiveEvaluate lower word, ⟨⟨word, rfl⟩, ?_⟩⟩
    exact (boundaryEquation_iff_endoTwistedConjugator upper lower endomorphism extension
      upperLeft upperRight lowerLeft lowerRight word).mp equation
  · rintro ⟨witness, ⟨⟨word, rfl⟩, conjugator⟩⟩
    refine ⟨word, ?_⟩
    exact (boundaryEquation_iff_endoTwistedConjugator upper lower endomorphism extension
      upperLeft upperRight lowerLeft lowerRight word).mpr conjugator

end MatrixMortality.ExtendableBinaryBoundary
