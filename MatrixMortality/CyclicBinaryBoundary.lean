import MatrixMortality.PositiveFreeCancellation

/-!
# Cyclic-side collapse for positive fixed-boundary equality

A positive fixed-boundary equation over a binary source becomes a rational-subset intersection
in `G × ℤ` as soon as either homomorphism has cyclic image.  The algebraic reduction below is
independent of freeness; the decision consequence for free-group targets uses decidability of
rational-subset membership in a direct product of a free group and an abelian group.
-/

namespace MatrixMortality.CyclicBinaryBoundary

open PositiveFreeCancellation

/-- Additive weight of a positive source word. -/
def wordWeight {S : Type*} (weight : S → ℤ) (word : List S) : ℤ :=
  (word.map weight).sum

@[simp]
theorem wordWeight_nil {S : Type*} (weight : S → ℤ) :
    wordWeight weight [] = 0 := rfl

@[simp]
theorem wordWeight_cons {S : Type*} (weight : S → ℤ) (letter : S) (word : List S) :
    wordWeight weight (letter :: word) = weight letter + wordWeight weight word := by
  simp [wordWeight]

theorem wordWeight_append {S : Type*} (weight : S → ℤ) (left right : List S) :
    wordWeight weight (left ++ right) = wordWeight weight left + wordWeight weight right := by
  simp [wordWeight]

/-- Evaluation of a positive word whose letters are powers of one group element. -/
theorem positiveEvaluate_cyclic
    {S G : Type*} [Group G] (generator : S → G) (base : G) (weight : S → ℤ)
    (cyclic : ∀ letter, generator letter = base ^ weight letter) (word : List S) :
    positiveEvaluate generator word = base ^ wordWeight weight word := by
  induction word with
  | nil => simp
  | cons letter word induction =>
      rw [positiveEvaluate_cons, cyclic letter, induction, wordWeight_cons]
      exact (zpow_add base (weight letter) (wordWeight weight word)).symm

/-- A positive source trace, retaining both the other group value and the cyclic exponent. -/
def weightedTrace
    {S G : Type*} [Group G] (generator : S → G) (weight : S → ℤ) :
    Set (G × Multiplicative ℤ) :=
  Set.range fun word : List S =>
    (positiveEvaluate generator word, Multiplicative.ofAdd (wordWeight weight word))

/-- The two-sided cyclic corridor selected by the four fixed boundaries. -/
def cyclicCorridor {G : Type*} [Group G] (left base right : G) :
    Set (G × Multiplicative ℤ) :=
  Set.range fun exponent : ℤ =>
    (left * base ^ exponent * right, Multiplicative.ofAdd exponent)

/-- Fixed-boundary equality for two positive source morphisms. -/
def BoundaryEquation
    {S G : Type*} [Group G] (upper lower : S → G)
    (upperLeft upperRight lowerLeft lowerRight : G) (word : List S) : Prop :=
  upperLeft * positiveEvaluate upper word * upperRight =
    lowerLeft * positiveEvaluate lower word * lowerRight

/-- If the upper morphism is cyclic, its fixed-boundary equation is exactly membership of the
lower value and upper exponent in one two-sided cyclic corridor. -/
theorem boundaryEquation_iff_mem_cyclicCorridor
    {S G : Type*} [Group G] (upper lower : S → G) (base : G) (weight : S → ℤ)
    (cyclic : ∀ letter, upper letter = base ^ weight letter)
    (upperLeft upperRight lowerLeft lowerRight : G) (word : List S) :
    BoundaryEquation upper lower upperLeft upperRight lowerLeft lowerRight word ↔
      (positiveEvaluate lower word, Multiplicative.ofAdd (wordWeight weight word)) ∈
        cyclicCorridor (lowerLeft⁻¹ * upperLeft) base (upperRight * lowerRight⁻¹) := by
  rw [BoundaryEquation, positiveEvaluate_cyclic upper base weight cyclic word]
  constructor
  · intro equation
    refine ⟨wordWeight weight word, ?_⟩
    apply Prod.ext
    · simp only
      calc
        lowerLeft⁻¹ * upperLeft * base ^ wordWeight weight word *
              (upperRight * lowerRight⁻¹) =
            lowerLeft⁻¹ *
              (upperLeft * base ^ wordWeight weight word * upperRight) *
              lowerRight⁻¹ := by group
        _ = lowerLeft⁻¹ *
              (lowerLeft * positiveEvaluate lower word * lowerRight) *
              lowerRight⁻¹ := by rw [equation]
        _ = positiveEvaluate lower word := by group
    · rfl
  · rintro ⟨exponent, equality⟩
    have exponent_eq : exponent = wordWeight weight word := by
      have := congrArg Prod.snd equality
      simpa using this
    subst exponent
    have lower_eq := congrArg Prod.fst equality
    simp only at lower_eq
    calc
      upperLeft * base ^ wordWeight weight word * upperRight =
          lowerLeft *
            (lowerLeft⁻¹ * upperLeft * base ^ wordWeight weight word *
              (upperRight * lowerRight⁻¹)) *
            lowerRight := by group
      _ = lowerLeft * positiveEvaluate lower word * lowerRight := by rw [lower_eq]

/-- The existential binary problem with one cyclic side is an intersection between a finitely
generated positive trace and a two-sided cyclic corridor. -/
theorem exists_boundaryEquation_iff_trace_inter_corridor_nonempty
    {S G : Type*} [Group G] (upper lower : S → G) (base : G) (weight : S → ℤ)
    (cyclic : ∀ letter, upper letter = base ^ weight letter)
    (upperLeft upperRight lowerLeft lowerRight : G) :
    (∃ word : List S,
        BoundaryEquation upper lower upperLeft upperRight lowerLeft lowerRight word) ↔
      Set.Nonempty
        (weightedTrace lower weight ∩
          cyclicCorridor (lowerLeft⁻¹ * upperLeft) base (upperRight * lowerRight⁻¹)) := by
  constructor
  · rintro ⟨word, equation⟩
    let point :=
      (positiveEvaluate lower word, Multiplicative.ofAdd (wordWeight weight word))
    refine ⟨point, ⟨?_, ?_⟩⟩
    · exact ⟨word, rfl⟩
    · exact (boundaryEquation_iff_mem_cyclicCorridor upper lower base weight cyclic
        upperLeft upperRight lowerLeft lowerRight word).mp equation
  · rintro ⟨point, ⟨⟨word, point_eq⟩, corridor⟩⟩
    refine ⟨word, ?_⟩
    apply (boundaryEquation_iff_mem_cyclicCorridor upper lower base weight cyclic
      upperLeft upperRight lowerLeft lowerRight word).mpr
    change (positiveEvaluate lower word,
      Multiplicative.ofAdd (wordWeight weight word)) = point at point_eq
    rw [point_eq]
    exact corridor

end MatrixMortality.CyclicBinaryBoundary
