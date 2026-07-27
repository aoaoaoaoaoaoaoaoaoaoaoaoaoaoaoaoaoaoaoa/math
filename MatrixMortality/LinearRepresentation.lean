import MatrixMortality.ExactBehavior

/-!
# Finite witnesses for exact linear representations

A finite Hankel section factors through every exact matrix representation.  A nonsingular square
section therefore gives a state-cardinality lower bound without constructing an infinite Hankel
matrix.
-/

namespace MatrixMortality

open scoped Matrix

/-- Scalar coefficient emitted by a row, a matrix word, and a column. -/
def linearCoefficient {α ι R : Type*} [Semiring R] [Fintype ι] [DecidableEq ι]
    (generators : α → Matrix ι ι R) (row column : ι → R) (word : List α) : R :=
  row ⬝ᵥ wordProduct generators word *ᵥ column

/-- Exact realization of a scalar word series by a finite matrix representation. -/
def RepresentsSeries {α ι R : Type*} [Semiring R] [Fintype ι] [DecidableEq ι]
    (series : List α → R) (generators : α → Matrix ι ι R)
    (row column : ι → R) : Prop :=
  ∀ word, linearCoefficient generators row column word = series word

/-- Scalar extension commutes with exact matrix coefficients. -/
theorem linearCoefficient_map {α ι R S : Type*} [Semiring R] [Semiring S]
    [Fintype ι] [DecidableEq ι] (map : R →+* S)
    (generators : α → Matrix ι ι R) (row column : ι → R) (word : List α) :
    map (linearCoefficient generators row column word) =
      linearCoefficient
        (fun label => (generators label).map map)
        (map ∘ row) (map ∘ column) word := by
  rw [linearCoefficient, linearCoefficient, RingHom.map_dotProduct]
  congr 1
  funext state
  change map ((wordProduct generators word *ᵥ column) state) = _
  rw [RingHom.map_mulVec, wordProduct_mapMatrix]

/-- Scalar exact realization is the one-dimensional instance of exact linear behavior. -/
theorem representsSeries_iff_representsBehavior
    {α ι K : Type*} [CommSemiring K] [Fintype ι] [DecidableEq ι]
    (series : List α → K) (generators : α → Matrix ι ι K)
    (row column : ι → K) :
    RepresentsSeries series generators row column ↔
      RepresentsBehavior (scalarBehavior series)
        (fun label => Matrix.toLin' (generators label))
        (LinearMap.toSpanSingleton K (ι → K) column)
        (rowOutput row) := by
  constructor
  · intro exact word
    apply LinearMap.ext
    intro scalar
    calc
      linearBehavior
          (fun label => Matrix.toLin' (generators label))
          (LinearMap.toSpanSingleton K (ι → K) column)
          (rowOutput row) word scalar =
          scalar • linearBehavior
            (fun label => Matrix.toLin' (generators label))
            (LinearMap.toSpanSingleton K (ι → K) column)
            (rowOutput row) word 1 := by
              rw [← map_smul]
              simp
      _ = scalar • linearCoefficient generators row column word := by
        rw [linearBehavior_matrix_one]
        rfl
      _ = scalar • series word := by rw [exact word]
      _ = scalarBehavior series word scalar := by
        simp [scalarBehavior]
  · intro exact word
    have at_one := LinearMap.congr_fun (exact word) 1
    rw [linearBehavior_matrix_one] at at_one
    simpa [linearCoefficient, scalarBehavior] using at_one

/-- Finite Hankel section selected by prefix and suffix families. -/
def finiteHankel {α P S R : Type*}
    (series : List α → R) (prefixes : P → List α) (suffixes : S → List α) :
    Matrix P S R :=
  fun pidx sidx => series (prefixes pidx ++ suffixes sidx)

/-- Reachable rows selected by a finite prefix family. -/
def finitePrefixStates {α ι P R : Type*} [Semiring R] [Fintype ι]
    [DecidableEq ι]
    (generators : α → Matrix ι ι R) (row : ι → R) (prefixes : P → List α) :
    Matrix P ι R :=
  fun pidx state => (row ᵥ* wordProduct generators (prefixes pidx)) state

/-- Observable columns selected by a finite suffix family. -/
def finiteSuffixStates {α ι S R : Type*} [Semiring R] [Fintype ι]
    [DecidableEq ι]
    (generators : α → Matrix ι ι R) (column : ι → R) (suffixes : S → List α) :
    Matrix ι S R :=
  fun state sidx => (wordProduct generators (suffixes sidx) *ᵥ column) state

/-- Every finite Hankel section factors through every exact representation. -/
theorem finiteHankel_factor {α ι P S R : Type*} [CommSemiring R]
    [Fintype ι] [DecidableEq ι]
    (series : List α → R) (generators : α → Matrix ι ι R)
    (row column : ι → R) (prefixes : P → List α) (suffixes : S → List α)
    (exact : RepresentsSeries series generators row column) :
    finiteHankel series prefixes suffixes =
      finitePrefixStates generators row prefixes *
        finiteSuffixStates generators column suffixes := by
  ext pidx sidx
  rw [finiteHankel, ← exact (prefixes pidx ++ suffixes sidx)]
  rw [linearCoefficient, wordProduct_append, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  simp [finitePrefixStates, finiteSuffixStates, Matrix.mul_apply, Matrix.dotProduct]

/-- A nonsingular square product through `ι` forces at least as many states as rows. -/
theorem card_le_of_det_rectangular_product_ne_zero
    {ν ι K : Type*} [Field K] [Fintype ν] [DecidableEq ν]
    [Fintype ι]
    (left : Matrix ν ι K) (right : Matrix ι ν K)
    (det_ne_zero : (left * right).det ≠ 0) :
    Fintype.card ν ≤ Fintype.card ι := by
  have product_injective : Function.Injective (left * right).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((left * right).isUnit_iff_isUnit_det.mpr
        (isUnit_iff_ne_zero.mpr det_ne_zero))
  have right_injective : Function.Injective right.mulVec := by
    intro x y vectors_equal
    apply product_injective
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, vectors_equal]
  have dimension_bound :=
    LinearMap.finrank_le_finrank_of_injective
      (f := right.mulVecLin) right_injective
  simpa [FiniteDimensional.finrank_pi] using dimension_bound

/-- A nonsingular finite Hankel section lower-bounds every exact realization's state count. -/
theorem finiteHankel_card_le {α ν ι K : Type*} [Field K]
    [Fintype ν] [DecidableEq ν] [Fintype ι] [DecidableEq ι]
    (series : List α → K) (prefixes suffixes : ν → List α)
    (generators : α → Matrix ι ι K) (row column : ι → K)
    (exact : RepresentsSeries series generators row column)
    (det_ne_zero : (finiteHankel series prefixes suffixes).det ≠ 0) :
    Fintype.card ν ≤ Fintype.card ι := by
  apply card_le_of_det_rectangular_product_ne_zero
    (finitePrefixStates generators row prefixes)
    (finiteSuffixStates generators column suffixes)
  rw [← finiteHankel_factor series generators row column prefixes suffixes exact]
  exact det_ne_zero

end MatrixMortality
