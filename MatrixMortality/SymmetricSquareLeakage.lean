import MatrixMortality.SymmetricSquareCollision

/-!
# Fixed symmetric-square leakage

A fixed rank-two quotient of a spanning symmetric-square orbit must have an invariant kernel
line.  Identifying a symmetric tensor `(X,Y,Z)` with `[[X,Y],[Y,Z]]` turns that kernel line into
a common binary quadratic similitude.  A degenerate tensor gives a common rational ray.  A
nondegenerate tensor gives a traceless quadratic twist which every generator commutes or
anticommutes with, the exact algebraic certificate for an invariant algebraic pair.
-/

namespace MatrixMortality.SymmetricSquareLeakage

open scoped Matrix
open SymmetricSquareCollision

/-- A symmetric tensor written as its binary symmetric matrix. -/
def tensorMatrix {R : Type*} (tensor : Triple R) : Square (Fin 2) R :=
  !![tensor 0, tensor 1; tensor 1, tensor 2]

/-- The standard alternating binary form. -/
def alternatingMatrix {R : Type*} [CommRing R] : Square (Fin 2) R :=
  !![0, -1; 1, 0]

/-- The traceless quadratic twist associated with a symmetric tensor. -/
def tensorTwist {R : Type*} [CommRing R] (tensor : Triple R) : Square (Fin 2) R :=
  tensorMatrix tensor * alternatingMatrix

/-- An exact elementary certificate: either a common rational ray, or a common quadratic
normalizer whose two algebraic eigendirections are preserved as an unordered pair. -/
def IsTensorElementary {α : Type*}
    (generators : α → Square (Fin 2) ℚ) : Prop :=
  (∃ ray : Pair ℚ, ray ≠ 0 ∧
      ∀ letter, crossDet ray (generators letter *ᵥ ray) = 0) ∨
    ∃ twist : Square (Fin 2) ℚ, ∃ discriminant : ℚ,
      twist 0 0 + twist 1 1 = 0 ∧ discriminant ≠ 0 ∧
        twist * twist = discriminant • 1 ∧
          ∀ letter,
            generators letter * twist = twist * generators letter ∨
              generators letter * twist = -(twist * generators letter)

/-- Commuting with a twist preserves each of its eigenspaces. -/
theorem twist_eigenvector_forward_of_commute {K : Type*} [Field K]
    (matrix twist : Square (Fin 2) K) (vector : Pair K) (root : K)
    (commutes : matrix * twist = twist * matrix)
    (eigenvector : twist *ᵥ vector = root • vector) :
    twist *ᵥ (matrix *ᵥ vector) = root • (matrix *ᵥ vector) := by
  calc
    twist *ᵥ (matrix *ᵥ vector) = (twist * matrix) *ᵥ vector :=
      Matrix.mulVec_mulVec vector twist matrix
    _ = (matrix * twist) *ᵥ vector := congrArg (fun product => product *ᵥ vector) commutes.symm
    _ = matrix *ᵥ (twist *ᵥ vector) :=
      (Matrix.mulVec_mulVec vector matrix twist).symm
    _ = matrix *ᵥ (root • vector) := congrArg (fun image => matrix *ᵥ image) eigenvector
    _ = root • (matrix *ᵥ vector) := Matrix.mulVec_smul matrix root vector

/-- Anticommuting with a twist swaps its opposite eigenspaces. -/
theorem twist_eigenvector_forward_of_anticommute {K : Type*} [Field K]
    (matrix twist : Square (Fin 2) K) (vector : Pair K) (root : K)
    (anticommutes : matrix * twist = -(twist * matrix))
    (eigenvector : twist *ᵥ vector = root • vector) :
    twist *ᵥ (matrix *ᵥ vector) = (-root) • (matrix *ᵥ vector) := by
  have twist_matrix : twist * matrix = -(matrix * twist) := by
    rw [anticommutes]
    simp
  calc
    twist *ᵥ (matrix *ᵥ vector) = (twist * matrix) *ᵥ vector :=
      Matrix.mulVec_mulVec vector twist matrix
    _ = (-(matrix * twist)) *ᵥ vector :=
      congrArg (fun product => product *ᵥ vector) twist_matrix
    _ = -(matrix *ᵥ (twist *ᵥ vector)) := by
      rw [Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
    _ = -(matrix *ᵥ (root • vector)) := by rw [eigenvector]
    _ = (-root) • (matrix *ᵥ vector) := by
      rw [Matrix.mulVec_smul, neg_smul]

/-- Covariant symmetric square is matrix congruence on symmetric tensors. -/
theorem tensorMatrix_symmetricSquare_mulVec {R : Type*} [CommRing R]
    (matrix : Square (Fin 2) R) (tensor : Triple R) :
    tensorMatrix (symmetricSquare matrix *ᵥ tensor) =
      matrix * tensorMatrix tensor * matrix.transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tensorMatrix, symmetricSquare, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ] <;>
    ring

/-- Tensor matrices commute with scalar multiplication. -/
theorem tensorMatrix_smul {R : Type*} [CommRing R]
    (scalar : R) (tensor : Triple R) :
    tensorMatrix (scalar • tensor) = scalar • tensorMatrix tensor := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tensorMatrix]

/-- The tensor determinant is the binary discriminant `XZ-Y²`. -/
theorem tensorMatrix_det {R : Type*} [CommRing R] (tensor : Triple R) :
    (tensorMatrix tensor).det = tensor 0 * tensor 2 - tensor 1 ^ 2 := by
  rw [Matrix.det_fin_two]
  simp [tensorMatrix]
  ring

/-- The quadratic twist squares to minus the tensor determinant. -/
theorem tensorTwist_sq {R : Type*} [CommRing R] (tensor : Triple R) :
    tensorTwist tensor * tensorTwist tensor =
      (-(tensorMatrix tensor).det) • (1 : Square (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tensorTwist, tensorMatrix, alternatingMatrix, Matrix.mul_apply,
      Matrix.det_fin_two, Fin.sum_univ_succ] <;>
    ring

/-- The quadratic twist is traceless. -/
theorem tensorTwist_trace (tensor : Triple ℚ) :
    tensorTwist tensor 0 0 + tensorTwist tensor 1 1 = 0 := by
  simp [tensorTwist, tensorMatrix, alternatingMatrix, Matrix.mul_apply,
    Fin.sum_univ_succ]

/-- Binary changes of coordinates scale the standard alternating form by their determinant. -/
theorem transpose_mul_alternating_mul {R : Type*} [CommRing R]
    (matrix : Square (Fin 2) R) :
    matrix.transpose * alternatingMatrix * matrix = matrix.det • alternatingMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alternatingMatrix, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.det_fin_two, Fin.sum_univ_succ] <;>
    ring

/-- A symmetric-square eigenline is exactly a binary quadratic similitude. -/
theorem tensorMatrix_similitude_of_eigen {K : Type*} [Field K]
    (matrix : Square (Fin 2) K) (tensor : Triple K) (scalar : K)
    (eigen : symmetricSquare matrix *ᵥ tensor = scalar • tensor) :
    matrix * tensorMatrix tensor * matrix.transpose =
      scalar • tensorMatrix tensor := by
  calc
    matrix * tensorMatrix tensor * matrix.transpose =
        tensorMatrix (symmetricSquare matrix *ᵥ tensor) :=
      (tensorMatrix_symmetricSquare_mulVec matrix tensor).symm
    _ = tensorMatrix (scalar • tensor) := congrArg tensorMatrix eigen
    _ = scalar • tensorMatrix tensor := tensorMatrix_smul scalar tensor

/-- A nondegenerate tensor similitude has scalar `±det(matrix)`. -/
theorem eigenScalar_sq_eq_det_sq_of_tensor_det_ne_zero
    {K : Type*} [Field K] {matrix : Square (Fin 2) K}
    {tensor : Triple K} {scalar : K}
    (tensor_det_ne_zero : (tensorMatrix tensor).det ≠ 0)
    (similitude : matrix * tensorMatrix tensor * matrix.transpose =
      scalar • tensorMatrix tensor) :
    scalar ^ 2 = matrix.det ^ 2 := by
  have determinant_eq := congrArg Matrix.det similitude
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul]
    at determinant_eq
  simp only [Fintype.card_fin] at determinant_eq
  apply mul_right_cancel₀ tensor_det_ne_zero
  calc
    scalar ^ 2 * (tensorMatrix tensor).det =
        matrix.det * (tensorMatrix tensor).det * matrix.det := determinant_eq.symm
    _ = matrix.det ^ 2 * (tensorMatrix tensor).det := by ring

/-- Equal squares in a field differ by at most a sign. -/
theorem eq_or_eq_neg_of_sq_eq_sq {K : Type*} [Field K] {left right : K}
    (squares : left ^ 2 = right ^ 2) : left = right ∨ left = -right := by
  have factor : (left - right) * (left + right) = 0 := by
    calc
      (left - right) * (left + right) = left ^ 2 - right ^ 2 := by ring
      _ = 0 := by rw [squares, sub_self]
  rcases mul_eq_zero.mp factor with equal | opposite
  · exact Or.inl (sub_eq_zero.mp equal)
  · right
    calc
      left = left + right - right := by ring
      _ = -right := by rw [opposite]; simp

/-- A tensor similitude intertwines its quadratic twist up to determinant and eigenvalue. -/
theorem tensorTwist_intertwining_of_similitude {K : Type*} [Field K]
    (matrix : Square (Fin 2) K) (tensor : Triple K) (scalar : K)
    (similitude : matrix * tensorMatrix tensor * matrix.transpose =
      scalar • tensorMatrix tensor) :
    matrix.det • (matrix * tensorTwist tensor) =
      scalar • (tensorTwist tensor * matrix) := by
  rw [tensorTwist]
  calc
    matrix.det • (matrix * (tensorMatrix tensor * alternatingMatrix)) =
        matrix * tensorMatrix tensor * (matrix.det • alternatingMatrix) := by
      simp [Matrix.mul_assoc]
    _ = matrix * tensorMatrix tensor *
        (matrix.transpose * alternatingMatrix * matrix) := by
      rw [transpose_mul_alternating_mul]
    _ = (matrix * tensorMatrix tensor * matrix.transpose) *
        alternatingMatrix * matrix := by
      simp [Matrix.mul_assoc]
    _ = (scalar • tensorMatrix tensor) * alternatingMatrix * matrix := by
      rw [similitude]
    _ = scalar • ((tensorMatrix tensor * alternatingMatrix) * matrix) := by
      simp [Matrix.mul_assoc]

/-- Every nonzero degenerate rational symmetric tensor is a scaled Veronese vector. -/
theorem exists_smul_veronese_of_tensor_det_eq_zero
    {tensor : Triple ℚ} (tensor_ne_zero : tensor ≠ 0)
    (tensor_det_zero : (tensorMatrix tensor).det = 0) :
    ∃ scalar : ℚ, ∃ ray : Pair ℚ,
      scalar ≠ 0 ∧ ray ≠ 0 ∧ tensor = scalar • veronese ray := by
  rw [tensorMatrix_det] at tensor_det_zero
  by_cases first_zero : tensor 0 = 0
  · have middle_zero : tensor 1 = 0 := by
      rw [first_zero, zero_mul, zero_sub, neg_eq_zero, sq_eq_zero_iff] at tensor_det_zero
      exact tensor_det_zero
    have last_ne_zero : tensor 2 ≠ 0 := by
      intro last_zero
      apply tensor_ne_zero
      funext i
      fin_cases i <;> assumption
    refine ⟨tensor 2, ![0, 1], last_ne_zero, ?_, ?_⟩
    · intro ray_zero
      have coordinate := congrFun ray_zero 1
      norm_num at coordinate
    · ext i
      fin_cases i <;> simp [veronese, first_zero, middle_zero]
  · refine ⟨(tensor 0)⁻¹, ![tensor 0, tensor 1], inv_ne_zero first_zero, ?_, ?_⟩
    · intro ray_zero
      have coordinate := congrFun ray_zero 0
      simp [first_zero] at coordinate
    · ext i
      fin_cases i
      · simp [veronese]
        field_simp
      · simp [veronese, first_zero]
      · simp [veronese]
        field_simp
        nlinarith [tensor_det_zero]

/-- Proportional Veronese vectors represent the same projective ray. -/
theorem crossDet_eq_zero_of_veronese_eq_smul
    {left right : Pair ℚ} {scalar : ℚ}
    (proportional : veronese right = scalar • veronese left) :
    crossDet left right = 0 := by
  have tangent_zero : tangentValue left right = 0 := by
    calc
      tangentValue left right =
          dotProduct (tangentRow left) (scalar • veronese left) := by
        rw [tangentValue, proportional]
      _ = scalar * tangentValue left left := by
        rw [dotProduct_smul]
        rfl
      _ = 0 := by rw [tangentValue_self, mul_zero]
  rw [tangentValue_eq_crossDet_sq, sq_eq_zero_iff] at tangent_zero
  exact tangent_zero

/-- A degenerate invariant tensor line gives a common rational projective fixed point. -/
theorem exists_fixed_ray_of_degenerate_tensor_eigen
    {α : Type*} (generators : α → Square (Fin 2) ℚ)
    {tensor : Triple ℚ} (tensor_ne_zero : tensor ≠ 0)
    (tensor_det_zero : (tensorMatrix tensor).det = 0)
    (invariant : ∀ letter, ∃ scalar : ℚ,
      symmetricSquare (generators letter) *ᵥ tensor = scalar • tensor) :
    ∃ ray : Pair ℚ, ray ≠ 0 ∧
      ∀ letter, crossDet ray (generators letter *ᵥ ray) = 0 := by
  obtain ⟨tensor_scalar, ray, tensor_scalar_ne_zero, ray_ne_zero, tensor_eq⟩ :=
    exists_smul_veronese_of_tensor_det_eq_zero tensor_ne_zero tensor_det_zero
  refine ⟨ray, ray_ne_zero, ?_⟩
  intro letter
  obtain ⟨eigen_scalar, eigen⟩ := invariant letter
  have scaled_eigen :
      tensor_scalar • veronese (generators letter *ᵥ ray) =
        tensor_scalar • (eigen_scalar • veronese ray) := by
    calc
      tensor_scalar • veronese (generators letter *ᵥ ray) =
          symmetricSquare (generators letter) *ᵥ tensor := by
        rw [tensor_eq, Matrix.mulVec_smul, symmetricSquare_mulVec_veronese]
      _ = eigen_scalar • tensor := eigen
      _ = tensor_scalar • (eigen_scalar • veronese ray) := by
        rw [tensor_eq]
        simp [smul_smul, mul_comm]
  have ray_eigen :
      veronese (generators letter *ᵥ ray) = eigen_scalar • veronese ray :=
    smul_right_injective (Triple ℚ) tensor_scalar_ne_zero scaled_eigen
  exact crossDet_eq_zero_of_veronese_eq_smul ray_eigen

/-- A nondegenerate invariant tensor line gives one common quadratic normalizer. -/
theorem exists_quadratic_normalizer_of_nondegenerate_tensor_eigen
    {α : Type*} (generators : α → Square (Fin 2) ℚ)
    (generators_det_ne_zero : ∀ letter, (generators letter).det ≠ 0)
    {tensor : Triple ℚ} (tensor_det_ne_zero : (tensorMatrix tensor).det ≠ 0)
    (invariant : ∀ letter, ∃ scalar : ℚ,
      symmetricSquare (generators letter) *ᵥ tensor = scalar • tensor) :
    ∃ twist : Square (Fin 2) ℚ, ∃ discriminant : ℚ,
      twist 0 0 + twist 1 1 = 0 ∧ discriminant ≠ 0 ∧
        twist * twist = discriminant • 1 ∧
          ∀ letter,
            generators letter * twist = twist * generators letter ∨
              generators letter * twist = -(twist * generators letter) := by
  refine ⟨tensorTwist tensor, -(tensorMatrix tensor).det,
    tensorTwist_trace tensor, neg_ne_zero.mpr tensor_det_ne_zero,
    tensorTwist_sq tensor, ?_⟩
  intro letter
  obtain ⟨scalar, eigen⟩ := invariant letter
  have similitude := tensorMatrix_similitude_of_eigen
    (generators letter) tensor scalar eigen
  have scalar_sq := eigenScalar_sq_eq_det_sq_of_tensor_det_ne_zero
    tensor_det_ne_zero similitude
  have intertwining := tensorTwist_intertwining_of_similitude
    (generators letter) tensor scalar similitude
  rcases eq_or_eq_neg_of_sq_eq_sq scalar_sq with scalar_eq | scalar_eq
  · left
    rw [scalar_eq] at intertwining
    exact smul_right_injective (Square (Fin 2) ℚ)
      (generators_det_ne_zero letter) intertwining
  · right
    rw [scalar_eq] at intertwining
    apply smul_right_injective (Square (Fin 2) ℚ)
      (generators_det_ne_zero letter)
    simpa using intertwining

/-- A common nonzero symmetric-square eigenline forces an elementary binary action. -/
theorem isTensorElementary_of_invariant_tensor
    {α : Type*} (generators : α → Square (Fin 2) ℚ)
    (generators_det_ne_zero : ∀ letter, (generators letter).det ≠ 0)
    {tensor : Triple ℚ} (tensor_ne_zero : tensor ≠ 0)
    (invariant : ∀ letter, ∃ scalar : ℚ,
      symmetricSquare (generators letter) *ᵥ tensor = scalar • tensor) :
    IsTensorElementary generators := by
  by_cases tensor_det_zero : (tensorMatrix tensor).det = 0
  · exact Or.inl (exists_fixed_ray_of_degenerate_tensor_eigen generators tensor_ne_zero
      tensor_det_zero invariant)
  · exact Or.inr (exists_quadratic_normalizer_of_nondegenerate_tensor_eigen generators
      generators_det_ne_zero tensor_det_zero invariant)

/-- Three pairwise-distinct Veronese rays detect equality of three-state linear maps. -/
theorem matrix_eq_of_mulVec_eq_on_three_veronese
    {left right : Square (Fin 3) ℚ} {first second third : Pair ℚ}
    (first_second_distinct : crossDet first second ≠ 0)
    (first_third_distinct : crossDet first third ≠ 0)
    (second_third_distinct : crossDet second third ≠ 0)
    (first_eq : left *ᵥ veronese first = right *ᵥ veronese first)
    (second_eq : left *ᵥ veronese second = right *ᵥ veronese second)
    (third_eq : left *ᵥ veronese third = right *ᵥ veronese third) :
    left = right := by
  let columns := veroneseColumns first second third
  have columns_unit : IsUnit columns := by
    dsimp [columns]
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, veroneseColumns_det]
    exact mul_ne_zero (mul_ne_zero first_second_distinct first_third_distinct)
      second_third_distinct
  apply columns_unit.mul_right_cancel
  ext i j
  fin_cases j
  · exact congrFun first_eq i
  · exact congrFun second_eq i
  · exact congrFun third_eq i

/-- Agreement of fixed leakage dynamics on a spanning Veronese triple is a global intertwiner. -/
theorem leakage_intertwines_of_three_veronese
    {binary : Square (Fin 2) ℚ} {leakage quotient : Square (Fin 3) ℚ}
    {first second third : Pair ℚ}
    (first_second_distinct : crossDet first second ≠ 0)
    (first_third_distinct : crossDet first third ≠ 0)
    (second_third_distinct : crossDet second third ≠ 0)
    (first_eq : leakage *ᵥ (symmetricSquare binary *ᵥ veronese first) =
      quotient *ᵥ (leakage *ᵥ veronese first))
    (second_eq : leakage *ᵥ (symmetricSquare binary *ᵥ veronese second) =
      quotient *ᵥ (leakage *ᵥ veronese second))
    (third_eq : leakage *ᵥ (symmetricSquare binary *ᵥ veronese third) =
      quotient *ᵥ (leakage *ᵥ veronese third)) :
    leakage * symmetricSquare binary = quotient * leakage := by
  apply matrix_eq_of_mulVec_eq_on_three_veronese first_second_distinct
    first_third_distinct second_third_distinct
  · simpa only [Matrix.mulVec_mulVec] using first_eq
  · simpa only [Matrix.mulVec_mulVec] using second_eq
  · simpa only [Matrix.mulVec_mulVec] using third_eq

/-- An intertwining leakage carries its kernel forward under the symmetric-square action. -/
theorem leakage_kernel_forward
    (binary : Square (Fin 2) ℚ) (leakage quotient : Square (Fin 3) ℚ)
    (tensor : Triple ℚ)
    (intertwines : leakage * symmetricSquare binary = quotient * leakage)
    (tensor_mem_kernel : leakage *ᵥ tensor = 0) :
    leakage *ᵥ (symmetricSquare binary *ᵥ tensor) = 0 := by
  calc
    leakage *ᵥ (symmetricSquare binary *ᵥ tensor) =
        (leakage * symmetricSquare binary) *ᵥ tensor :=
      Matrix.mulVec_mulVec tensor leakage (symmetricSquare binary)
    _ = (quotient * leakage) *ᵥ tensor := congrArg (fun matrix => matrix *ᵥ tensor) intertwines
    _ = quotient *ᵥ (leakage *ᵥ tensor) :=
      (Matrix.mulVec_mulVec tensor quotient leakage).symm
    _ = 0 := by rw [tensor_mem_kernel]; simp

/-- A rank-two three-state leakage has a witnessed one-dimensional kernel. -/
theorem exists_kernel_line_of_rank_eq_two
    (leakage : Square (Fin 3) ℚ) (rank_two : leakage.rank = 2) :
    ∃ tensor : Triple ℚ, tensor ≠ 0 ∧ leakage *ᵥ tensor = 0 ∧
      ∀ candidate : Triple ℚ, leakage *ᵥ candidate = 0 →
        ∃ scalar : ℚ, candidate = scalar • tensor := by
  have rank_nullity := leakage.mulVecLin.finrank_range_add_finrank_ker
  have kernel_rank : Module.finrank ℚ (LinearMap.ker leakage.mulVecLin) = 1 := by
    have range_rank : Module.finrank ℚ (LinearMap.range leakage.mulVecLin) = 2 := by
      simpa only [Matrix.rank] using rank_two
    have ambient_rank : Module.finrank ℚ (Fin 3 → ℚ) = 3 := by
      simp
    rw [range_rank, ambient_rank] at rank_nullity
    omega
  have kernel_ne_bot : LinearMap.ker leakage.mulVecLin ≠ ⊥ := by
    intro kernel_bot
    rw [kernel_bot, finrank_bot] at kernel_rank
    omega
  obtain ⟨tensor, tensor_mem, tensor_ne_zero⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot kernel_ne_bot
  have kernel_eq_span : LinearMap.ker leakage.mulVecLin = ℚ ∙ tensor :=
    eq_span_singleton_of_mem_of_finrank_eq_one kernel_rank tensor_mem tensor_ne_zero
  refine ⟨tensor, tensor_ne_zero, LinearMap.mem_ker.mp tensor_mem, ?_⟩
  intro candidate candidate_mem
  have candidate_in_kernel : candidate ∈ LinearMap.ker leakage.mulVecLin :=
    LinearMap.mem_ker.mpr candidate_mem
  rw [kernel_eq_span, Submodule.mem_span_singleton] at candidate_in_kernel
  obtain ⟨scalar, scalar_eq⟩ := candidate_in_kernel
  exact ⟨scalar, scalar_eq.symm⟩

/-- A one-dimensional leakage kernel becomes a symmetric-square eigenline. -/
theorem exists_eigen_of_intertwining_and_kernel_line
    (binary : Square (Fin 2) ℚ) (leakage quotient : Square (Fin 3) ℚ)
    (tensor : Triple ℚ)
    (intertwines : leakage * symmetricSquare binary = quotient * leakage)
    (tensor_mem_kernel : leakage *ᵥ tensor = 0)
    (kernel_line : ∀ candidate : Triple ℚ, leakage *ᵥ candidate = 0 →
      ∃ scalar : ℚ, candidate = scalar • tensor) :
    ∃ scalar : ℚ, symmetricSquare binary *ᵥ tensor = scalar • tensor := by
  exact kernel_line (symmetricSquare binary *ᵥ tensor)
    (leakage_kernel_forward binary leakage quotient tensor intertwines tensor_mem_kernel)

/-- Fixed rank-two leakage on a spanning Sym² orbit forces an elementary binary action. -/
theorem isTensorElementary_of_fixed_rankTwo_leakage
    {α : Type*} (generators : α → Square (Fin 2) ℚ)
    (generators_det_ne_zero : ∀ letter, (generators letter).det ≠ 0)
    (leakage : Square (Fin 3) ℚ) (quotient : α → Square (Fin 3) ℚ)
    (tensor : Triple ℚ) (tensor_ne_zero : tensor ≠ 0)
    (tensor_mem_kernel : leakage *ᵥ tensor = 0)
    (kernel_line : ∀ candidate : Triple ℚ, leakage *ᵥ candidate = 0 →
      ∃ scalar : ℚ, candidate = scalar • tensor)
    (intertwines : ∀ letter,
      leakage * symmetricSquare (generators letter) = quotient letter * leakage) :
    IsTensorElementary generators := by
  apply isTensorElementary_of_invariant_tensor generators generators_det_ne_zero
    tensor_ne_zero
  intro letter
  exact exists_eigen_of_intertwining_and_kernel_line (generators letter) leakage
    (quotient letter) tensor (intertwines letter) tensor_mem_kernel kernel_line

/-- Rank-two fixed leakage agreeing on three spanning Sym² rays forces elementary dynamics. -/
theorem isTensorElementary_of_rankTwo_leakage_on_three_veronese
    {α : Type*} (generators : α → Square (Fin 2) ℚ)
    (generators_det_ne_zero : ∀ letter, (generators letter).det ≠ 0)
    (leakage : Square (Fin 3) ℚ) (rank_two : leakage.rank = 2)
    (quotient : α → Square (Fin 3) ℚ) {first second third : Pair ℚ}
    (first_second_distinct : crossDet first second ≠ 0)
    (first_third_distinct : crossDet first third ≠ 0)
    (second_third_distinct : crossDet second third ≠ 0)
    (first_eq : ∀ letter,
      leakage *ᵥ (symmetricSquare (generators letter) *ᵥ veronese first) =
        quotient letter *ᵥ (leakage *ᵥ veronese first))
    (second_eq : ∀ letter,
      leakage *ᵥ (symmetricSquare (generators letter) *ᵥ veronese second) =
        quotient letter *ᵥ (leakage *ᵥ veronese second))
    (third_eq : ∀ letter,
      leakage *ᵥ (symmetricSquare (generators letter) *ᵥ veronese third) =
        quotient letter *ᵥ (leakage *ᵥ veronese third)) :
    IsTensorElementary generators := by
  obtain ⟨tensor, tensor_ne_zero, tensor_mem_kernel, kernel_line⟩ :=
    exists_kernel_line_of_rank_eq_two leakage rank_two
  apply isTensorElementary_of_fixed_rankTwo_leakage generators generators_det_ne_zero
    leakage quotient tensor tensor_ne_zero tensor_mem_kernel kernel_line
  intro letter
  exact leakage_intertwines_of_three_veronese first_second_distinct
    first_third_distinct second_third_distinct (first_eq letter) (second_eq letter)
    (third_eq letter)

end MatrixMortality.SymmetricSquareLeakage
