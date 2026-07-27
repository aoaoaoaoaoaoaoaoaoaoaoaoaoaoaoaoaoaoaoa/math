import MatrixMortality.MatrixSemigroup

/-!
# Exact linear behavior

An input map, a word action, and an output map determine one linear map for every physical
word.  Scalar rational series and finite-rank matrix sandwiches are specializations of this
object.
-/

namespace MatrixMortality

open scoped Matrix

variable {K State Input Output Glyph : Type*} [CommSemiring K]
  [AddCommMonoid State] [Module K State]
  [AddCommMonoid Input] [Module K Input]
  [AddCommMonoid Output] [Module K Output]

/-- The exact input-output map emitted by one physical word. -/
def linearBehavior (generators : Glyph → Module.End K State)
    (input : Input →ₗ[K] State) (output : State →ₗ[K] Output)
    (word : List Glyph) : Input →ₗ[K] Output :=
  output.comp ((wordProduct generators word).comp input)

/-- Exact realization of a word-indexed linear behavior. -/
def RepresentsBehavior (series : List Glyph → (Input →ₗ[K] Output))
    (generators : Glyph → Module.End K State)
    (input : Input →ₗ[K] State) (output : State →ₗ[K] Output) : Prop :=
  ∀ word, linearBehavior generators input output word = series word

/-- A flattened block-Hankel column, with futures acting to the left of the fixed past. -/
def behaviorColumn (series : List Glyph → (Input →ₗ[K] Output))
    (past : List Glyph) (input : Input) : List Glyph → Output :=
  fun future => series (future ++ past) input

theorem linearBehavior_append_apply (generators : Glyph → Module.End K State)
    (input : Input →ₗ[K] State) (output : State →ₗ[K] Output)
    (future past : List Glyph) (value : Input) :
    linearBehavior generators input output (future ++ past) value =
      output (wordProduct generators future
        (wordProduct generators past (input value))) := by
  simp [linearBehavior, wordProduct_append, LinearMap.mul_apply]

/-- Matrix multiplication and linear-map composition interpret every word identically. -/
theorem wordProduct_toLin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (generators : Glyph → Square ι K) (word : List Glyph) :
    wordProduct (fun label => Matrix.toLin' (generators label)) word =
      Matrix.toLin' (wordProduct generators word) := by
  induction word with
  | nil => simp [LinearMap.one_eq_id]
  | cons label tail induction =>
      simp only [wordProduct_cons, induction, Matrix.toLin'_mul, LinearMap.mul_eq_comp]

/-! ## Scalar specialization -/

/-- A row vector as a linear output functional. -/
def rowOutput {ι : Type*} [Fintype ι] (row : ι → K) : (ι → K) →ₗ[K] K where
  toFun vector := row ⬝ᵥ vector
  map_add' left right := Matrix.dotProduct_add row left right
  map_smul' scalar vector := Matrix.dotProduct_smul scalar row vector

/-- A scalar series regarded as a one-dimensional linear behavior. -/
def scalarBehavior (series : List Glyph → K) : List Glyph → (K →ₗ[K] K) :=
  fun word => LinearMap.toSpanSingleton K K (series word)

theorem linearBehavior_matrix_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (generators : Glyph → Square ι K) (row column : ι → K)
    (word : List Glyph) :
    linearBehavior
        (fun label => Matrix.toLin' (generators label))
        (LinearMap.toSpanSingleton K (ι → K) column)
        (rowOutput row) word 1 =
      row ⬝ᵥ wordProduct generators word *ᵥ column := by
  simp [linearBehavior, wordProduct_toLin, rowOutput]

end MatrixMortality
