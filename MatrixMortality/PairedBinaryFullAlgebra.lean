import MatrixMortality.PairedBinaryAlgebraRank

/-!
# Full algebra of the paired-binary mortality family

The two transposed six-state controls and their canonical rank-one separator generate the full
six-dimensional matrix algebra.
-/

namespace MatrixMortality

/-- The canonical mortality family: `none` is the rank-one separator and the two Boolean
labels are the transposed paired-binary controls. -/
def pairedBinaryMortalityGenerator (β : Nat) (body : List TagLetter) :
    Option Bool → Square (Fin 6) ℚ :=
  separatedGenerator
    (Matrix.vecMulVec (pairedBinaryAlgebraColumn β) pairedBinaryAlgebraRow)
    (pairedBinaryAlgebraGenerator β body)

/-- Reachability contexts lifted into the mortality alphabet. -/
def pairedBinaryMortalityLeftWords : Fin 6 → List (Option Bool) :=
  fun index => (pairedBinaryAlgebraLeftWords index).map some

/-- Observability contexts lifted into the mortality alphabet. -/
def pairedBinaryMortalityRightWords : Fin 6 → List (Option Bool) :=
  fun index => (pairedBinaryAlgebraRightWords index).map some

theorem pairedBinaryMortality_contextColumns_eq (β : Nat) (body : List TagLetter) :
    contextColumns (pairedBinaryMortalityGenerator β body)
        (pairedBinaryAlgebraColumn β) pairedBinaryMortalityLeftWords =
      pairedBinaryAlgebraReachable β body := by
  ext row column
  simp [pairedBinaryMortalityGenerator, pairedBinaryMortalityLeftWords,
    pairedBinaryAlgebraReachable, contextColumns]

theorem pairedBinaryMortality_contextRows_eq (β : Nat) (body : List TagLetter) :
    contextRows (pairedBinaryMortalityGenerator β body)
        pairedBinaryAlgebraRow pairedBinaryMortalityRightWords =
      pairedBinaryAlgebraObservable β body := by
  ext row column
  simp [pairedBinaryMortalityGenerator, pairedBinaryMortalityRightWords,
    pairedBinaryAlgebraObservable, contextRows]

/-- Every rational six-by-six matrix is a linear combination of physical products of the
canonical three-generator paired-binary mortality family. -/
theorem pairedBinaryMortality_wordProductSpan_eq_top
    (β : Nat) (body : List TagLetter) (three_le : 3 ≤ β) :
    wordProductSpan (pairedBinaryMortalityGenerator β body) = ⊤ := by
  apply wordProductSpan_eq_top_of_rankOne_contexts
    (pairedBinaryMortalityGenerator β body)
    (pairedBinaryAlgebraColumn β) pairedBinaryAlgebraRow [none]
    (by simp [pairedBinaryMortalityGenerator, wordProduct, separatedGenerator])
    pairedBinaryMortalityLeftWords pairedBinaryMortalityRightWords
  · rw [pairedBinaryMortality_contextColumns_eq]
    exact pairedBinaryAlgebraReachable_isUnit β body three_le
  · rw [pairedBinaryMortality_contextRows_eq]
    exact pairedBinaryAlgebraObservable_isUnit β body three_le

end MatrixMortality
