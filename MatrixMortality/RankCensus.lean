import MatrixMortality.InterfaceCompression
import MatrixMortality.ReturnFamily

/-!
# Rank-census reductions

The rank profiles isolated by the mortality-table audit are direct interfaces to the compression
hub. In dimension two, unit generators cannot kill a word, so all remaining mortality is scalar
incidence between rank-one cuts. In the two-generator, four-dimensional case, rank-two and
rank-one cuts reduce respectively to a two-dimensional return family and an order-four scalar
orbit.
-/

namespace MatrixMortality.RankCensus

open scoped Matrix

/-- A family of `k` unit `2 × 2` matrices is immortal. -/
theorem finTwo_allUnit_immortal {K : Type*} [Field K] {k : Nat}
    (family : Fin k → Square (Fin 2) K)
    (family_unit : ∀ label, IsUnit (family label)) :
    ¬IsMortal family :=
  not_isMortal_of_forall_isUnit family family_unit

/-- Reindex `u` unit generators and `m` factorized rank-one generators as one
`(u + m)`-generator family. -/
def finTwoRankCensusFamily {K : Type*} [Field K] {u m : Nat}
    (units : Fin u → Square (Fin 2) K)
    (column row : Fin m → Fin 2 → K) :
    Fin (u + m) → Square (Fin 2) K :=
  InterfaceCompression.rankOneGenerator units column row ∘ finSumFinEquiv.symm

/-- With `m` factorized rank-one generators and `u` unit generators in dimension two,
mortality is exactly projective incidence `r_j X_w c_j' = 0` over the unit subfamily. -/
theorem finTwo_rankOne_isMortal_iff {K : Type*} [Field K] {u m : Nat}
    (units : Fin u → Square (Fin 2) K)
    (column row : Fin m → Fin 2 → K)
    (units_are_units : ∀ label, IsUnit (units label)) :
    IsMortal (finTwoRankCensusFamily units column row) ↔
      ∃ source word target,
        row source ⬝ᵥ wordProduct units word *ᵥ column target = 0 := by
  rw [finTwoRankCensusFamily, isMortal_comp_equiv,
    InterfaceCompression.isMortal_rankOne_iff]
  exact or_iff_right (not_isMortal_of_forall_isUnit units units_are_units)

/-- The canonical equivalence between two labels and an ambient/cut pair. -/
def finTwoPairEquiv : Fin 2 ≃ Option Unit where
  toFun label := if label = 0 then none else some ()
  invFun
    | none => 0
    | some _ => 1
  left_inv label := by fin_cases label <;> rfl
  right_inv label := by cases label <;> rfl

/-- A two-generator family consisting of an ambient matrix and a factorized rank-two cut. -/
def finFourRankTwoPair {K : Type*} [Field K]
    (ambient : Square (Fin 4) K)
    (input : Matrix (Fin 4) (Fin 2) K)
    (output : Matrix (Fin 2) (Fin 4) K) :
    Fin 2 → Square (Fin 4) K :=
  ReturnFamily.pairGenerator ambient (input * output) ∘ finTwoPairEquiv

/-- The `(4,2)` profile of `M₄(2)` is precisely a four-mode unary return family in dimension
two. No splitting hypothesis is needed. -/
theorem finFour_rankTwo_isMortal_iff {K : Type*} [Field K]
    (ambient : Square (Fin 4) K)
    (input : Matrix (Fin 4) (Fin 2) K)
    (output : Matrix (Fin 2) (Fin 4) K)
    (ambient_unit : IsUnit ambient) :
    IsMortal (finFourRankTwoPair ambient input output) ↔
      ∃ waits, ReturnFamily.returnProduct ambient input output waits = 0 := by
  rw [finFourRankTwoPair, isMortal_comp_equiv]
  exact ReturnFamily.pairGenerator_isMortal_iff
    ambient input output ambient_unit

/-- Column factor of a rank-one cut. -/
def rankOneInput {K : Type*}
    (column : Fin 4 → K) : Matrix (Fin 4) Unit K :=
  Matrix.replicateCol Unit column

/-- Row factor of a rank-one cut. -/
def rankOneOutput {K : Type*}
    (row : Fin 4 → K) : Matrix Unit (Fin 4) K :=
  Matrix.replicateRow Unit row

/-- A two-generator family consisting of an ambient matrix and a factorized rank-one cut. -/
def finFourRankOnePair {K : Type*} [Field K]
    (ambient : Square (Fin 4) K) (column row : Fin 4 → K) :
    Fin 2 → Square (Fin 4) K :=
  ReturnFamily.pairGenerator ambient
    (rankOneInput column * rankOneOutput row) ∘ finTwoPairEquiv

theorem rankOne_returnMatrix_apply {K : Type*} [Field K]
    (ambient : Square (Fin 4) K) (column row : Fin 4 → K) (wait : Nat) :
    ReturnFamily.returnMatrix ambient (rankOneInput column) (rankOneOutput row) wait () () =
      row ⬝ᵥ ambient ^ wait *ᵥ column := by
  rw [ReturnFamily.returnMatrix, Matrix.mul_assoc]
  change
    (Matrix.replicateRow Unit row *
      (ambient ^ wait * Matrix.replicateCol Unit column)) () () = _
  rw [← Matrix.replicateCol_mulVec,
    Matrix.replicateRow_mul_replicateCol_apply]

theorem rankOne_returnMatrix_eq_zero_iff {K : Type*} [Field K]
    (ambient : Square (Fin 4) K) (column row : Fin 4 → K) (wait : Nat) :
    ReturnFamily.returnMatrix ambient (rankOneInput column) (rankOneOutput row) wait = 0 ↔
      row ⬝ᵥ ambient ^ wait *ᵥ column = 0 := by
  constructor
  · intro matrix_zero
    have entry_zero := congrFun (congrFun matrix_zero ()) ()
    rw [rankOne_returnMatrix_apply] at entry_zero
    simpa using entry_zero
  · intro scalar_zero
    ext interfaceRow interfaceColumn
    cases interfaceRow
    cases interfaceColumn
    rw [rankOne_returnMatrix_apply]
    simpa using scalar_zero

/-- The `(4,1)` profile of `M₄(2)` is exactly the order-four scalar Skolem orbit
`r Aⁿ c = 0`. -/
theorem finFour_rankOne_isMortal_iff {K : Type*} [Field K]
    (ambient : Square (Fin 4) K) (column row : Fin 4 → K)
    (ambient_unit : IsUnit ambient) :
    IsMortal (finFourRankOnePair ambient column row) ↔
      ∃ wait, row ⬝ᵥ ambient ^ wait *ᵥ column = 0 := by
  rw [finFourRankOnePair, isMortal_comp_equiv,
    ReturnFamily.rankOnePair_isMortal_iff ambient
      (rankOneInput column) (rankOneOutput row) ambient_unit]
  exact exists_congr fun wait =>
    rankOne_returnMatrix_eq_zero_iff ambient column row wait

end MatrixMortality.RankCensus
