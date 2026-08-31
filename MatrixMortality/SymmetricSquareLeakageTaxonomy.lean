import MatrixMortality.SymmetricSquareLeakage

/-!
# Fixed symmetric-square leakage taxonomy

Rank-one leakage is governed by the dual symmetric-square action.  Its one-dimensional row space
supplies a common binary quadratic covector.  A degenerate quadratic has one rational root ray;
a nondegenerate quadratic has an algebraic root pair.  Together with the rank-two kernel theorem
and the full-rank determinant cut, this classifies every fixed leakage at the three-ray
equivariance seam.
-/

namespace MatrixMortality.SymmetricSquareLeakage

open scoped Matrix
open SymmetricSquareCollision

/-- A quadratic covector converted to the tensor convention, which stores half its middle term. -/
def covectorTensor (covector : Triple ℚ) : Triple ℚ :=
  ![covector 0, covector 1 / 2, covector 2]

/-- A quadratic covector expressed as a symmetric matrix. -/
def covectorMatrix (covector : Triple ℚ) : Square (Fin 2) ℚ :=
  !![covector 0, covector 1 / 2; covector 1 / 2, covector 2]

/-- Evaluation of a quadratic covector on one homogeneous pair. -/
def covectorValue (covector : Triple ℚ) (vector : Pair ℚ) : ℚ :=
  dotProduct covector (veronese vector)

/-- The rational ray perpendicular to a nonzero quadratic normal. -/
def normalKernelRay (normal : Pair ℚ) : Pair ℚ :=
  ![-normal 1, normal 0]

/-- The quadratic normalizer associated with a covector. -/
def covectorTwist (covector : Triple ℚ) : Square (Fin 2) ℚ :=
  alternatingMatrix * covectorMatrix covector

/-- Dual symmetric square is congruence on binary quadratic covectors. -/
theorem covectorMatrix_vecMul_symmetricSquare
    (covector : Triple ℚ) (matrix : Square (Fin 2) ℚ) :
    covectorMatrix (covector ᵥ* symmetricSquare matrix) =
      matrix.transpose * covectorMatrix covector * matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [covectorMatrix, symmetricSquare, Matrix.vecMul, dotProduct,
      Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ] <;>
    ring

/-- Quadratic covector matrices commute with scalar multiplication. -/
theorem covectorMatrix_smul (scalar : ℚ) (covector : Triple ℚ) :
    covectorMatrix (scalar • covector) = scalar • covectorMatrix covector := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [covectorMatrix] <;> ring

/-- A dual symmetric-square eigenline is a binary quadratic similitude. -/
theorem covectorMatrix_similitude_of_eigen
    (matrix : Square (Fin 2) ℚ) (covector : Triple ℚ) (scalar : ℚ)
    (eigen : covector ᵥ* symmetricSquare matrix = scalar • covector) :
    matrix.transpose * covectorMatrix covector * matrix =
      scalar • covectorMatrix covector := by
  calc
    matrix.transpose * covectorMatrix covector * matrix =
        covectorMatrix (covector ᵥ* symmetricSquare matrix) :=
      (covectorMatrix_vecMul_symmetricSquare covector matrix).symm
    _ = covectorMatrix (scalar • covector) := congrArg covectorMatrix eigen
    _ = scalar • covectorMatrix covector := covectorMatrix_smul scalar covector

/-- Quadratic evaluation is equivariant for the dual symmetric-square action. -/
theorem covectorValue_mulVec
    (covector : Triple ℚ) (matrix : Square (Fin 2) ℚ) (vector : Pair ℚ) :
    covectorValue covector (matrix *ᵥ vector) =
      covectorValue (covector ᵥ* symmetricSquare matrix) vector := by
  rw [covectorValue, covectorValue, ← symmetricSquare_mulVec_veronese,
    Matrix.dotProduct_mulVec]

/-- Quadratic evaluation is linear in its covector. -/
theorem covectorValue_smul (scalar : ℚ) (covector : Triple ℚ) (vector : Pair ℚ) :
    covectorValue (scalar • covector) vector = scalar * covectorValue covector vector := by
  rw [covectorValue, smul_dotProduct]
  rfl

/-- Halving the middle coefficient does not erase a nonzero rational covector. -/
theorem covectorTensor_ne_zero {covector : Triple ℚ} (covector_ne_zero : covector ≠ 0) :
    covectorTensor covector ≠ 0 := by
  intro tensor_zero
  apply covector_ne_zero
  funext i
  fin_cases i
  · have coordinate := congrFun tensor_zero 0
    simpa [covectorTensor] using coordinate
  · have coordinate := congrFun tensor_zero 1
    simp [covectorTensor] at coordinate
    exact coordinate
  · have coordinate := congrFun tensor_zero 2
    simpa [covectorTensor] using coordinate

/-- A scaled Veronese factorization of the tensor is the corresponding squared linear form. -/
theorem covectorValue_eq_scaled_dot_sq_of_tensor_factor
    {covector : Triple ℚ} {scalar : ℚ} {normal : Pair ℚ}
    (factor : covectorTensor covector = scalar • veronese normal)
    (vector : Pair ℚ) :
    covectorValue covector vector = scalar * dotProduct normal vector ^ 2 := by
  have first := congrFun factor 0
  have middle := congrFun factor 1
  have last := congrFun factor 2
  simp [covectorTensor, veronese] at first middle last
  have middle' : covector 1 = 2 * scalar * normal 0 * normal 1 := by
    linarith
  simp [covectorValue, veronese, dotProduct, Fin.sum_univ_succ]
  rw [first, middle', last]
  ring

/-- The perpendicular ray of a nonzero normal is nonzero. -/
theorem normalKernelRay_ne_zero {normal : Pair ℚ} (normal_ne_zero : normal ≠ 0) :
    normalKernelRay normal ≠ 0 := by
  intro ray_zero
  apply normal_ne_zero
  funext i
  fin_cases i
  · have coordinate := congrFun ray_zero 1
    simpa [normalKernelRay] using coordinate
  · have coordinate := congrFun ray_zero 0
    simpa [normalKernelRay] using congrArg Neg.neg coordinate

/-- Cross determinant from a perpendicular ray is minus the corresponding dot product. -/
theorem crossDet_normalKernelRay (normal vector : Pair ℚ) :
    crossDet (normalKernelRay normal) vector = -dotProduct normal vector := by
  simp [crossDet, normalKernelRay, dotProduct, Fin.sum_univ_succ]
  ring

/-- A quadratic normal is orthogonal to its kernel ray. -/
theorem dotProduct_normalKernelRay (normal : Pair ℚ) :
    dotProduct normal (normalKernelRay normal) = 0 := by
  simp [normalKernelRay, dotProduct, Fin.sum_univ_succ]
  ring

/-- A degenerate invariant quadratic covector gives a common rational projective fixed point. -/
theorem exists_fixed_ray_of_degenerate_covector_eigen
    {α : Type*} (generators : α → Square (Fin 2) ℚ)
    {covector : Triple ℚ} (covector_ne_zero : covector ≠ 0)
    (covector_det_zero : (covectorMatrix covector).det = 0)
    (invariant : ∀ letter, ∃ scalar : ℚ,
      covector ᵥ* symmetricSquare (generators letter) = scalar • covector) :
    ∃ ray : Pair ℚ, ray ≠ 0 ∧
      ∀ letter, crossDet ray (generators letter *ᵥ ray) = 0 := by
  have tensor_ne_zero : covectorTensor covector ≠ 0 :=
    covectorTensor_ne_zero covector_ne_zero
  have tensor_det_zero : (tensorMatrix (covectorTensor covector)).det = 0 := by
    simpa [covectorMatrix, covectorTensor, tensorMatrix] using covector_det_zero
  obtain ⟨form_scalar, normal, form_scalar_ne_zero, normal_ne_zero, factor⟩ :=
    exists_smul_veronese_of_tensor_det_eq_zero tensor_ne_zero tensor_det_zero
  refine ⟨normalKernelRay normal, normalKernelRay_ne_zero normal_ne_zero, ?_⟩
  intro letter
  obtain ⟨eigen_scalar, eigen⟩ := invariant letter
  have source_value_zero : covectorValue covector (normalKernelRay normal) = 0 := by
    rw [covectorValue_eq_scaled_dot_sq_of_tensor_factor factor,
      dotProduct_normalKernelRay, zero_pow, mul_zero]
    norm_num
  have target_value_zero :
      covectorValue covector (generators letter *ᵥ normalKernelRay normal) = 0 := by
    calc
      covectorValue covector (generators letter *ᵥ normalKernelRay normal) =
          covectorValue
            (covector ᵥ* symmetricSquare (generators letter))
            (normalKernelRay normal) :=
        covectorValue_mulVec covector (generators letter) (normalKernelRay normal)
      _ = covectorValue (eigen_scalar • covector) (normalKernelRay normal) := by
        rw [eigen]
      _ = eigen_scalar * covectorValue covector (normalKernelRay normal) :=
        covectorValue_smul eigen_scalar covector (normalKernelRay normal)
      _ = 0 := by rw [source_value_zero, mul_zero]
  rw [covectorValue_eq_scaled_dot_sq_of_tensor_factor factor] at target_value_zero
  have target_dot_zero :
      dotProduct normal (generators letter *ᵥ normalKernelRay normal) = 0 := by
    rcases mul_eq_zero.mp target_value_zero with scalar_zero | square_zero
    · exact False.elim (form_scalar_ne_zero scalar_zero)
    · exact sq_eq_zero_iff.mp square_zero
  rw [crossDet_normalKernelRay, target_dot_zero, neg_zero]

/-- The dual quadratic twist squares to minus the covector determinant. -/
theorem covectorTwist_sq (covector : Triple ℚ) :
    covectorTwist covector * covectorTwist covector =
      (-(covectorMatrix covector).det) • (1 : Square (Fin 2) ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [covectorTwist, covectorMatrix, alternatingMatrix, Matrix.mul_apply,
      Matrix.det_fin_two, Fin.sum_univ_succ] <;>
    ring

/-- The dual quadratic twist is traceless. -/
theorem covectorTwist_trace (covector : Triple ℚ) :
    covectorTwist covector 0 0 + covectorTwist covector 1 1 = 0 := by
  simp [covectorTwist, covectorMatrix, alternatingMatrix, Matrix.mul_apply,
    Fin.sum_univ_succ]

/-- The alternating form also scales under the opposite binary congruence. -/
theorem mul_alternating_mul_transpose {R : Type*} [CommRing R]
    (matrix : Square (Fin 2) R) :
    matrix * alternatingMatrix * matrix.transpose = matrix.det • alternatingMatrix := by
  simpa using transpose_mul_alternating_mul matrix.transpose

/-- A dual quadratic similitude intertwines its twist up to determinant and eigenvalue. -/
theorem covectorTwist_intertwining_of_similitude
    (matrix : Square (Fin 2) ℚ) (covector : Triple ℚ) (scalar : ℚ)
    (similitude : matrix.transpose * covectorMatrix covector * matrix =
      scalar • covectorMatrix covector) :
    matrix.det • (covectorTwist covector * matrix) =
      scalar • (matrix * covectorTwist covector) := by
  rw [covectorTwist]
  calc
    matrix.det • ((alternatingMatrix * covectorMatrix covector) * matrix) =
        (matrix.det • alternatingMatrix) * covectorMatrix covector * matrix := by
      simp [Matrix.mul_assoc]
    _ = (matrix * alternatingMatrix * matrix.transpose) *
        covectorMatrix covector * matrix := by
      rw [mul_alternating_mul_transpose]
    _ = matrix * alternatingMatrix *
        (matrix.transpose * covectorMatrix covector * matrix) := by
      simp [Matrix.mul_assoc]
    _ = matrix * alternatingMatrix * (scalar • covectorMatrix covector) := by
      rw [similitude]
    _ = scalar • (matrix * (alternatingMatrix * covectorMatrix covector)) := by
      simp [Matrix.mul_assoc]

/-- A nondegenerate dual quadratic similitude has eigenvalue `±det(matrix)`. -/
theorem covectorEigenScalar_sq_eq_det_sq_of_det_ne_zero
    {matrix : Square (Fin 2) ℚ} {covector : Triple ℚ} {scalar : ℚ}
    (covector_det_ne_zero : (covectorMatrix covector).det ≠ 0)
    (similitude : matrix.transpose * covectorMatrix covector * matrix =
      scalar • covectorMatrix covector) :
    scalar ^ 2 = matrix.det ^ 2 := by
  have tensor_det_ne_zero : (tensorMatrix (covectorTensor covector)).det ≠ 0 := by
    simpa [tensorMatrix, covectorTensor, covectorMatrix] using covector_det_ne_zero
  have tensor_similitude :
      matrix.transpose * tensorMatrix (covectorTensor covector) *
          matrix.transpose.transpose =
        scalar • tensorMatrix (covectorTensor covector) := by
    simpa [tensorMatrix, covectorTensor, covectorMatrix] using similitude
  have squares := eigenScalar_sq_eq_det_sq_of_tensor_det_ne_zero
    tensor_det_ne_zero tensor_similitude
  simpa using squares

/-- A nondegenerate invariant quadratic covector gives one common algebraic pair normalizer. -/
theorem exists_quadratic_normalizer_of_nondegenerate_covector_eigen
    {α : Type*} (generators : α → Square (Fin 2) ℚ)
    (generators_det_ne_zero : ∀ letter, (generators letter).det ≠ 0)
    {covector : Triple ℚ} (covector_det_ne_zero : (covectorMatrix covector).det ≠ 0)
    (invariant : ∀ letter, ∃ scalar : ℚ,
      covector ᵥ* symmetricSquare (generators letter) = scalar • covector) :
    ∃ twist : Square (Fin 2) ℚ, ∃ discriminant : ℚ,
      twist 0 0 + twist 1 1 = 0 ∧ discriminant ≠ 0 ∧
        twist * twist = discriminant • 1 ∧
          ∀ letter,
            generators letter * twist = twist * generators letter ∨
              generators letter * twist = -(twist * generators letter) := by
  refine ⟨covectorTwist covector, -(covectorMatrix covector).det,
    covectorTwist_trace covector, neg_ne_zero.mpr covector_det_ne_zero,
    covectorTwist_sq covector, ?_⟩
  intro letter
  obtain ⟨scalar, eigen⟩ := invariant letter
  have similitude := covectorMatrix_similitude_of_eigen
    (generators letter) covector scalar eigen
  have scalar_sq := covectorEigenScalar_sq_eq_det_sq_of_det_ne_zero
    covector_det_ne_zero similitude
  have intertwining := covectorTwist_intertwining_of_similitude
    (generators letter) covector scalar similitude
  rcases eq_or_eq_neg_of_sq_eq_sq scalar_sq with scalar_eq | scalar_eq
  · left
    rw [scalar_eq] at intertwining
    exact (smul_right_injective (Square (Fin 2) ℚ)
      (generators_det_ne_zero letter) intertwining).symm
  · right
    rw [scalar_eq] at intertwining
    have swapped :
        covectorTwist covector * generators letter =
          -(generators letter * covectorTwist covector) := by
      apply smul_right_injective (Square (Fin 2) ℚ)
        (generators_det_ne_zero letter)
      simpa using intertwining
    rw [swapped]
    simp

/-- A common nonzero dual symmetric-square eigenline forces an elementary binary action. -/
theorem isTensorElementary_of_invariant_covector
    {α : Type*} (generators : α → Square (Fin 2) ℚ)
    (generators_det_ne_zero : ∀ letter, (generators letter).det ≠ 0)
    {covector : Triple ℚ} (covector_ne_zero : covector ≠ 0)
    (invariant : ∀ letter, ∃ scalar : ℚ,
      covector ᵥ* symmetricSquare (generators letter) = scalar • covector) :
    IsTensorElementary generators := by
  by_cases covector_det_zero : (covectorMatrix covector).det = 0
  · exact Or.inl (exists_fixed_ray_of_degenerate_covector_eigen generators
      covector_ne_zero covector_det_zero invariant)
  · exact Or.inr (exists_quadratic_normalizer_of_nondegenerate_covector_eigen generators
      generators_det_ne_zero covector_det_zero invariant)

/-- A rank-one fixed leakage intertwiner supplies a common dual symmetric-square eigenline. -/
theorem exists_common_covector_eigen_of_rankOne_leakage
    {α : Type*} (generators : α → Square (Fin 2) ℚ)
    (leakage : Square (Fin 3) ℚ) (leakage_rank_one : leakage.rank = 1)
    (quotient : α → Square (Fin 3) ℚ)
    (intertwines : ∀ letter,
      leakage * symmetricSquare (generators letter) = quotient letter * leakage) :
    ∃ covector : Triple ℚ, covector ≠ 0 ∧
      ∀ letter, ∃ scalar : ℚ,
        covector ᵥ* symmetricSquare (generators letter) = scalar • covector := by
  have transpose_rank : leakage.transpose.rank = 1 := by
    rw [Matrix.rank_transpose, leakage_rank_one]
  have range_rank :
      Module.finrank ℚ (LinearMap.range leakage.transpose.mulVecLin) = 1 := by
    simpa only [Matrix.rank] using transpose_rank
  have range_ne_bot : LinearMap.range leakage.transpose.mulVecLin ≠ ⊥ := by
    intro range_bot
    rw [range_bot, finrank_bot] at range_rank
    omega
  obtain ⟨covector, covector_mem, covector_ne_zero⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot range_ne_bot
  have range_eq_span : LinearMap.range leakage.transpose.mulVecLin = ℚ ∙ covector :=
    eq_span_singleton_of_mem_of_finrank_eq_one range_rank covector_mem covector_ne_zero
  obtain ⟨source, source_eq⟩ := covector_mem
  have source_mulVec : leakage.transpose *ᵥ source = covector := source_eq
  refine ⟨covector, covector_ne_zero, ?_⟩
  intro letter
  have transposed_intertwiner :
      (symmetricSquare (generators letter)).transpose * leakage.transpose =
        leakage.transpose * (quotient letter).transpose := by
    have transposed := congrArg Matrix.transpose (intertwines letter)
    simpa only [Matrix.transpose_mul] using transposed
  have forward_mem :
      (symmetricSquare (generators letter)).transpose *ᵥ covector ∈
        LinearMap.range leakage.transpose.mulVecLin := by
    refine ⟨(quotient letter).transpose *ᵥ source, ?_⟩
    calc
      leakage.transpose *ᵥ ((quotient letter).transpose *ᵥ source) =
          (leakage.transpose * (quotient letter).transpose) *ᵥ source :=
        Matrix.mulVec_mulVec source leakage.transpose (quotient letter).transpose
      _ = ((symmetricSquare (generators letter)).transpose * leakage.transpose) *ᵥ
          source := by rw [transposed_intertwiner]
      _ = (symmetricSquare (generators letter)).transpose *ᵥ
          (leakage.transpose *ᵥ source) :=
        (Matrix.mulVec_mulVec source
          (symmetricSquare (generators letter)).transpose leakage.transpose).symm
      _ = (symmetricSquare (generators letter)).transpose *ᵥ covector := by
        rw [source_mulVec]
  rw [range_eq_span, Submodule.mem_span_singleton] at forward_mem
  obtain ⟨scalar, scalar_eq⟩ := forward_mem
  refine ⟨scalar, ?_⟩
  have transpose_eigen :
      (symmetricSquare (generators letter)).transpose *ᵥ covector =
        scalar • covector := scalar_eq.symm
  simpa only [Matrix.mulVec_transpose] using transpose_eigen

/-- A rank-one fixed leakage intertwiner forces elementary binary dynamics. -/
theorem isTensorElementary_of_rankOne_leakage
    {α : Type*} (generators : α → Square (Fin 2) ℚ)
    (generators_det_ne_zero : ∀ letter, (generators letter).det ≠ 0)
    (leakage : Square (Fin 3) ℚ) (leakage_rank_one : leakage.rank = 1)
    (quotient : α → Square (Fin 3) ℚ)
    (intertwines : ∀ letter,
      leakage * symmetricSquare (generators letter) = quotient letter * leakage) :
    IsTensorElementary generators := by
  obtain ⟨covector, covector_ne_zero, invariant⟩ :=
    exists_common_covector_eigen_of_rankOne_leakage generators leakage leakage_rank_one
      quotient intertwines
  exact isTensorElementary_of_invariant_covector generators generators_det_ne_zero
    covector_ne_zero invariant

/-- A rational matrix of rank zero is the zero matrix. -/
theorem matrix_eq_zero_of_rank_eq_zero
    (matrix : Square (Fin 3) ℚ) (matrix_rank_zero : matrix.rank = 0) :
    matrix = 0 := by
  have range_rank : Module.finrank ℚ (LinearMap.range matrix.mulVecLin) = 0 := by
    simpa only [Matrix.rank] using matrix_rank_zero
  have range_bot : LinearMap.range matrix.mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp range_rank
  ext i j
  have image_mem : matrix *ᵥ Pi.single j 1 ∈ LinearMap.range matrix.mulVecLin :=
    ⟨Pi.single j 1, rfl⟩
  rw [range_bot] at image_mem
  have image_zero : matrix *ᵥ Pi.single j 1 = 0 := by
    simpa using image_mem
  have coordinate := congrFun image_zero i
  simpa using coordinate

/-- Fixed leakage of rank at most one is either zero or forces elementary binary dynamics. -/
theorem leakage_eq_zero_or_isTensorElementary_of_rank_le_one
    {α : Type*} (generators : α → Square (Fin 2) ℚ)
    (generators_det_ne_zero : ∀ letter, (generators letter).det ≠ 0)
    (leakage : Square (Fin 3) ℚ) (leakage_rank_le_one : leakage.rank ≤ 1)
    (quotient : α → Square (Fin 3) ℚ)
    (intertwines : ∀ letter,
      leakage * symmetricSquare (generators letter) = quotient letter * leakage) :
    leakage = 0 ∨ IsTensorElementary generators := by
  by_cases leakage_rank_zero : leakage.rank = 0
  · exact Or.inl (matrix_eq_zero_of_rank_eq_zero leakage leakage_rank_zero)
  · right
    have leakage_rank_one : leakage.rank = 1 := by omega
    exact isTensorElementary_of_rankOne_leakage generators generators_det_ne_zero
      leakage leakage_rank_one quotient intertwines

/-- A singular rational three-state matrix has rank at most two. -/
theorem rank_le_two_of_det_eq_zero
    (matrix : Square (Fin 3) ℚ) (matrix_det_zero : matrix.det = 0) :
    matrix.rank ≤ 2 := by
  obtain ⟨vector, vector_ne_zero, vector_mem_kernel⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr matrix_det_zero
  have kernel_ne_bot : LinearMap.ker matrix.mulVecLin ≠ ⊥ := by
    intro kernel_bot
    have vector_mem : vector ∈ LinearMap.ker matrix.mulVecLin :=
      LinearMap.mem_ker.mpr vector_mem_kernel
    rw [kernel_bot] at vector_mem
    have vector_zero : vector = 0 := by simpa using vector_mem
    exact vector_ne_zero vector_zero
  have kernel_rank_pos : 1 ≤ Module.finrank ℚ (LinearMap.ker matrix.mulVecLin) :=
    Submodule.one_le_finrank_iff.mpr kernel_ne_bot
  have rank_nullity := matrix.mulVecLin.finrank_range_add_finrank_ker
  have ambient_rank : Module.finrank ℚ (Fin 3 → ℚ) = 3 := by simp
  change matrix.rank + Module.finrank ℚ (LinearMap.ker matrix.mulVecLin) =
    Module.finrank ℚ (Fin 3 → ℚ) at rank_nullity
  rw [ambient_rank] at rank_nullity
  omega

/-- Every singular fixed symmetric-square leakage is zero or forces elementary binary dynamics. -/
theorem leakage_eq_zero_or_isTensorElementary_of_singular_intertwiner
    {α : Type*} (generators : α → Square (Fin 2) ℚ)
    (generators_det_ne_zero : ∀ letter, (generators letter).det ≠ 0)
    (leakage : Square (Fin 3) ℚ) (leakage_det_zero : leakage.det = 0)
    (quotient : α → Square (Fin 3) ℚ)
    (intertwines : ∀ letter,
      leakage * symmetricSquare (generators letter) = quotient letter * leakage) :
    leakage = 0 ∨ IsTensorElementary generators := by
  have leakage_rank_le_two := rank_le_two_of_det_eq_zero leakage leakage_det_zero
  by_cases leakage_rank_two : leakage.rank = 2
  · right
    obtain ⟨tensor, tensor_ne_zero, tensor_mem_kernel, kernel_line⟩ :=
      exists_kernel_line_of_rank_eq_two leakage leakage_rank_two
    exact isTensorElementary_of_fixed_rankTwo_leakage generators generators_det_ne_zero
      leakage quotient tensor tensor_ne_zero tensor_mem_kernel kernel_line intertwines
  · have leakage_rank_le_one : leakage.rank ≤ 1 := by omega
    exact leakage_eq_zero_or_isTensorElementary_of_rank_le_one generators
      generators_det_ne_zero leakage leakage_rank_le_one quotient intertwines

/-- A dependent image of three distinct equivariant Veronese rays makes fixed leakage zero or
forces elementary binary dynamics. -/
theorem leakage_eq_zero_or_isTensorElementary_of_three_veronese_carrier
    {α : Type*} (generators : α → Square (Fin 2) ℚ)
    (generators_det_ne_zero : ∀ letter, (generators letter).det ≠ 0)
    (leakage : Square (Fin 3) ℚ) (quotient : α → Square (Fin 3) ℚ)
    {first second third : Pair ℚ}
    (first_second_distinct : crossDet first second ≠ 0)
    (first_third_distinct : crossDet first third ≠ 0)
    (second_third_distinct : crossDet second third ≠ 0)
    (carrier_singular :
      (leakage * veroneseColumns first second third).det = 0)
    (first_eq : ∀ letter,
      leakage *ᵥ (symmetricSquare (generators letter) *ᵥ veronese first) =
        quotient letter *ᵥ (leakage *ᵥ veronese first))
    (second_eq : ∀ letter,
      leakage *ᵥ (symmetricSquare (generators letter) *ᵥ veronese second) =
        quotient letter *ᵥ (leakage *ᵥ veronese second))
    (third_eq : ∀ letter,
      leakage *ᵥ (symmetricSquare (generators letter) *ᵥ veronese third) =
        quotient letter *ᵥ (leakage *ᵥ veronese third)) :
    leakage = 0 ∨ IsTensorElementary generators := by
  have ray_det_ne_zero :
      (veroneseColumns first second third).det ≠ 0 := by
    rw [veroneseColumns_det]
    exact mul_ne_zero (mul_ne_zero first_second_distinct first_third_distinct)
      second_third_distinct
  have leakage_det_zero : leakage.det = 0 := by
    rw [Matrix.det_mul] at carrier_singular
    exact (mul_eq_zero.mp carrier_singular).resolve_right ray_det_ne_zero
  apply leakage_eq_zero_or_isTensorElementary_of_singular_intertwiner generators
    generators_det_ne_zero leakage leakage_det_zero quotient
  intro letter
  exact leakage_intertwines_of_three_veronese first_second_distinct
    first_third_distinct second_third_distinct (first_eq letter) (second_eq letter)
    (third_eq letter)

/-- The middle-coordinate projector witnesses that two distinct Veronese rays do not determine a
three-state linear map. -/
def middleCoordinateProjector : Square (Fin 3) ℚ :=
  !![0, 0, 0; 0, 1, 0; 0, 0, 0]

/-- Two distinct Veronese test rays leave one nonzero three-state direction invisible. -/
theorem two_veronese_rays_do_not_detect_matrix_equality :
    ∃ left right : Square (Fin 3) ℚ, ∃ first second : Pair ℚ,
      crossDet first second ≠ 0 ∧ left ≠ right ∧
        left *ᵥ veronese first = right *ᵥ veronese first ∧
          left *ᵥ veronese second = right *ᵥ veronese second := by
  refine ⟨0, middleCoordinateProjector, ![1, 0], ![0, 1], ?_, ?_, ?_, ?_⟩
  · norm_num [crossDet]
  · intro matrices_equal
    have coordinate := congrArg (fun matrix => matrix 1 1) matrices_equal
    norm_num [middleCoordinateProjector] at coordinate
  · ext i
    fin_cases i <;>
      norm_num [middleCoordinateProjector, veronese, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ]
  · ext i
    fin_cases i <;>
      norm_num [middleCoordinateProjector, veronese, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ]

end MatrixMortality.SymmetricSquareLeakage
