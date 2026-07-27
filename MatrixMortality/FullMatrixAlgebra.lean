import MatrixMortality.RankOne

/-!
# Full matrix algebras from rank-one contexts

Independent reachable columns and observable rows around one physical rank-one word generate
the entire matrix algebra.  The proof is parser-free: every matrix unit is replaced by a
physical left context, the rank-one word, and a physical right context.
-/

namespace MatrixMortality

open scoped Matrix

variable {K ι Glyph : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- Linear left-right multiplication on the matrix algebra. -/
def matrixSandwichLinear (left right : Square ι K) :
    Square ι K →ₗ[K] Square ι K :=
  (LinearMap.mulRight K right).comp (LinearMap.mulLeft K left)

omit [DecidableEq ι] in
@[simp]
theorem matrixSandwichLinear_apply (left right matrix : Square ι K) :
    matrixSandwichLinear left right matrix = left * matrix * right := rfl

theorem matrixSandwichLinear_injective
    {left right : Square ι K} (left_unit : IsUnit left) (right_unit : IsUnit right) :
    Function.Injective (matrixSandwichLinear left right) := by
  obtain ⟨left_inverse, left_inverse_mul⟩ := left_unit.exists_left_inv
  obtain ⟨right_inverse, right_mul_inverse⟩ := right_unit.exists_right_inv
  intro first second equal
  have cancelled :=
    congrArg (fun matrix : Square ι K => left_inverse * matrix * right_inverse) equal
  have right_cancelled :
      left_inverse * (left * first) = left_inverse * (left * second) := by
    simpa only [matrixSandwichLinear_apply, mul_assoc, right_mul_inverse, mul_one] using
      cancelled
  calc
    first = (left_inverse * left) * first := by rw [left_inverse_mul, one_mul]
    _ = left_inverse * (left * first) := by rw [mul_assoc]
    _ = left_inverse * (left * second) := right_cancelled
    _ = (left_inverse * left) * second := by rw [mul_assoc]
    _ = second := by rw [left_inverse_mul, one_mul]

/-- Sandwiching the standard matrix basis between two units preserves linear independence. -/
theorem sandwichMatrixUnits_linearIndependent
    {left right : Square ι K} (left_unit : IsUnit left) (right_unit : IsUnit right) :
    LinearIndependent K fun index : ι × ι =>
      left * Matrix.stdBasisMatrix index.1 index.2 1 * right := by
  have mapped :=
    (Matrix.stdBasis K ι ι).linearIndependent.map'
      (matrixSandwichLinear left right)
      (LinearMap.ker_eq_bot_of_injective
        (matrixSandwichLinear_injective left_unit right_unit))
  have family_eq :
      matrixSandwichLinear left right ∘ ⇑(Matrix.stdBasis K ι ι) =
        fun index : ι × ι =>
          left * Matrix.stdBasisMatrix index.1 index.2 1 * right := by
    funext index
    rw [Function.comp_apply, matrixSandwichLinear_apply,
      Matrix.stdBasis_eq_stdBasisMatrix]
  rw [family_eq] at mapped
  exact mapped

/-- Two invertible context matrices turn their pairwise outer products into a basis. -/
theorem sandwichMatrixUnits_span_eq_top [Nonempty ι]
    {left right : Square ι K} (left_unit : IsUnit left) (right_unit : IsUnit right) :
    Submodule.span K
        (Set.range fun index : ι × ι =>
          left * Matrix.stdBasisMatrix index.1 index.2 1 * right) =
      ⊤ := by
  apply
    (sandwichMatrixUnits_linearIndependent left_unit right_unit).span_eq_top_of_card_eq_finrank
  simp [FiniteDimensional.finrank_matrix]

/-- Pairwise outer products of the columns of `left` and rows of `right` are matrix-unit
sandwiches. -/
theorem sandwichMatrixUnit_eq_outer (left right : Square ι K) (i j : ι) :
    left * Matrix.stdBasisMatrix i j 1 * right =
      Matrix.vecMulVec (fun row => left row i) (right j) := by
  rw [Matrix.stdBasisMatrix_eq_single_vecMulVec_single, mul_outer, outer_mul]
  simp [Matrix.mulVec_single_one, Matrix.single_one_vecMul]

/-- Reachable columns selected by physical left contexts. -/
def contextColumns (generators : Glyph → Square ι K) (column : ι → K)
    (leftWords : ι → List Glyph) : Square ι K :=
  fun row index => (wordProduct generators (leftWords index) *ᵥ column) row

/-- Observable rows selected by physical right contexts. -/
def contextRows (generators : Glyph → Square ι K) (row : ι → K)
    (rightWords : ι → List Glyph) : Square ι K :=
  fun index column => (row ᵥ* wordProduct generators (rightWords index)) column

/-- The linear span of every physical word product, including the empty product. -/
def wordProductSpan (generators : Glyph → Square ι K) : Submodule K (Square ι K) :=
  Submodule.span K (Set.range (wordProduct generators))

theorem context_outer_eq_wordProduct
    (generators : Glyph → Square ι K) (column row : ι → K)
    (separatorWord : List Glyph)
    (separator : wordProduct generators separatorWord = Matrix.vecMulVec column row)
    (leftWords rightWords : ι → List Glyph) (i j : ι) :
    Matrix.vecMulVec
        (fun state => contextColumns generators column leftWords state i)
        (contextRows generators row rightWords j) =
      wordProduct generators
        (leftWords i ++ separatorWord ++ rightWords j) := by
  change
    Matrix.vecMulVec
        (wordProduct generators (leftWords i) *ᵥ column)
        (row ᵥ* wordProduct generators (rightWords j)) =
      wordProduct generators
        (leftWords i ++ separatorWord ++ rightWords j)
  rw [wordProduct_append, wordProduct_append, separator, mul_outer, outer_mul]

/-- Independent physical contexts around one rank-one word force the physical word products to
span the full matrix algebra. -/
theorem wordProductSpan_eq_top_of_rankOne_contexts [Nonempty ι]
    (generators : Glyph → Square ι K) (column row : ι → K)
    (separatorWord : List Glyph)
    (separator : wordProduct generators separatorWord = Matrix.vecMulVec column row)
    (leftWords rightWords : ι → List Glyph)
    (columns_unit : IsUnit (contextColumns generators column leftWords))
    (rows_unit : IsUnit (contextRows generators row rightWords)) :
    wordProductSpan generators = ⊤ := by
  apply top_unique
  rw [← sandwichMatrixUnits_span_eq_top columns_unit rows_unit]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨i, j⟩, rfl⟩
  change
    contextColumns generators column leftWords *
        Matrix.stdBasisMatrix i j 1 *
        contextRows generators row rightWords ∈
      wordProductSpan generators
  rw [sandwichMatrixUnit_eq_outer,
    context_outer_eq_wordProduct generators column row separatorWord separator
      leftWords rightWords i j]
  apply Submodule.subset_span
  exact ⟨leftWords i ++ separatorWord ++ rightWords j, rfl⟩

end MatrixMortality
