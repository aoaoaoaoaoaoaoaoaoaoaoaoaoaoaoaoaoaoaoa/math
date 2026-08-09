import MatrixMortality.ProjectiveLine
import MatrixMortality.ReverseEdge

namespace MatrixMortality.ProjectiveIncidence

open scoped Matrix

noncomputable section

/-- The two-dimensional incidence carrier. -/
abbrev Interface := ReverseEdge.Interface

/-- Rational projective source ray. -/
abbrev Point := ProjectiveLine.Point ℚ

/-- Projectivization of a nonzero incidence column. -/
def sourcePoint (vector : Interface → ℚ) : Point :=
  ProjectiveLine.ofPair (vector 0) (vector 1)

/-- Canonical nonzero column spanning the kernel of a nonzero incidence row. -/
def kernelColumn (row : Interface → ℚ) : Interface → ℚ :=
  ![-row 1, row 0]

private def cross (left right : Interface → ℚ) : ℚ :=
  left 0 * right 1 - left 1 * right 0

private theorem kernelColumn_ne_zero {row : Interface → ℚ} (row_ne : row ≠ 0) :
    kernelColumn row ≠ 0 := by
  intro kernel_zero
  apply row_ne
  funext i
  fin_cases i
  · have := congrFun kernel_zero 1
    simpa [kernelColumn] using this
  · have := congrFun kernel_zero 0
    simpa [kernelColumn] using neg_eq_zero.mp this

private theorem sourcePoint_eq_iff_cross_eq_zero
    {left right : Interface → ℚ} (left_ne : left ≠ 0) (right_ne : right ≠ 0) :
    sourcePoint left = sourcePoint right ↔ cross left right = 0 := by
  by_cases left_bottom : left 1 = 0
  · have left_top : left 0 ≠ 0 := by
      intro left_top
      apply left_ne
      funext i
      fin_cases i <;> assumption
    by_cases right_bottom : right 1 = 0
    · simp [sourcePoint, ProjectiveLine.ofPair, cross, left_bottom, right_bottom]
    · simp [sourcePoint, ProjectiveLine.ofPair, cross, left_bottom, right_bottom,
        left_top]
  · by_cases right_bottom : right 1 = 0
    · have right_top : right 0 ≠ 0 := by
        intro right_top
        apply right_ne
        funext i
        fin_cases i <;> assumption
      simp [sourcePoint, ProjectiveLine.ofPair, cross, left_bottom, right_bottom,
        right_top]
    · simp only [sourcePoint, ProjectiveLine.ofPair, left_bottom, right_bottom,
        ↓reduceIte, Option.some.injEq]
      constructor
      · intro quotient_eq
        dsimp [cross]
        field_simp at quotient_eq
        linarith
      · intro cross_zero
        dsimp [cross] at cross_zero
        field_simp
        linarith

private theorem cross_mulVec (matrix : Square Interface ℚ) (left right : Interface → ℚ) :
    cross (matrix *ᵥ left) (matrix *ᵥ right) = matrix.det * cross left right := by
  simp [cross, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ,
    Matrix.det_fin_two]
  ring

private theorem dotProduct_eq_cross_kernelColumn (row vector : Interface → ℚ) :
    row ⬝ᵥ vector = cross vector (kernelColumn row) := by
  simp [cross, kernelColumn, Matrix.dotProduct, Fin.sum_univ_succ]
  ring

private theorem image_ne_zero
    {matrix : Square Interface ℚ} (matrix_unit : IsUnit matrix)
    {vector : Interface → ℚ} (vector_ne : vector ≠ 0) :
    matrix *ᵥ vector ≠ 0 := by
  intro image_zero
  apply vector_ne
  apply Matrix.mulVec_injective_iff_isUnit.mpr matrix_unit
  simpa using image_zero

private theorem cut_eq_zero_iff_sourcePoint_eq_image
    {matrix : Square Interface ℚ} (matrix_unit : IsUnit matrix)
    {row vector target : Interface → ℚ}
    (row_ne : row ≠ 0) (vector_ne : vector ≠ 0)
    (action : matrix *ᵥ vector = target) :
    row ⬝ᵥ vector = 0 ↔
      sourcePoint target = sourcePoint (matrix *ᵥ kernelColumn row) := by
  have target_ne : target ≠ 0 := by
    rw [← action]
    exact image_ne_zero matrix_unit vector_ne
  have kernel_ne := kernelColumn_ne_zero row_ne
  have image_kernel_ne := image_ne_zero matrix_unit kernel_ne
  rw [sourcePoint_eq_iff_cross_eq_zero target_ne image_kernel_ne]
  rw [← action, cross_mulVec, dotProduct_eq_cross_kernelColumn]
  constructor
  · intro cut_zero
    rw [cut_zero, mul_zero]
  · intro product_zero
    exact (mul_eq_zero.mp product_zero).resolve_left
      ((Matrix.isUnit_iff_isUnit_det matrix).mp matrix_unit).ne_zero

/-- The two source rays at which one ordered incidence instance violates an exceptional-scalar
condition. `false` is the `alpha` ray and `true` is the `beta` ray. -/
def badSource (G H : Square Interface ℚ) (row : Interface → ℚ) : Bool → Point
  | false => sourcePoint (H *ᵥ kernelColumn row)
  | true => sourcePoint ((H * G⁻¹ * H) *ᵥ kernelColumn row)

/-- Exceptional source set for the ordered incidence pair `(G,H)`. -/
def badSources (G H : Square Interface ℚ) (row : Interface → ℚ) : Finset Point :=
  {badSource G H row false, badSource G H row true}

/-- The first reverse-compiler scalar vanishes exactly on its first exceptional source ray. -/
theorem alpha_eq_zero_iff_sourcePoint_eq_badSource
    (G H : Square Interface ℚ) (row column : Interface → ℚ)
    (H_unit : IsUnit H) (row_ne : row ≠ 0) (column_ne : column ≠ 0) :
    ReverseEdge.alpha H row column = 0 ↔
      sourcePoint column = badSource G H row false := by
  rw [ReverseEdge.alpha]
  apply cut_eq_zero_iff_sourcePoint_eq_image H_unit row_ne
  · exact image_ne_zero (nonsingInv_isUnit H H_unit) column_ne
  · exact ReverseEdge.mulVec_pulledColumn H column H_unit

private theorem bridgeInverse_mulVec_firstVector
    (G H : Square Interface ℚ) (column : Interface → ℚ)
    (G_unit : IsUnit G) (H_unit : IsUnit H) :
    (H * G⁻¹ * H) *ᵥ ReverseEdge.firstVector G H column = column := by
  calc
    (H * G⁻¹ * H) *ᵥ ReverseEdge.firstVector G H column =
        (H * G⁻¹) *ᵥ (H *ᵥ ReverseEdge.firstVector G H column) :=
      (Matrix.mulVec_mulVec _ (H * G⁻¹) H).symm
    _ = H *ᵥ (G⁻¹ *ᵥ (H *ᵥ ReverseEdge.firstVector G H column)) :=
      (Matrix.mulVec_mulVec _ H G⁻¹).symm
    _ = H *ᵥ (G⁻¹ *ᵥ (G *ᵥ ReverseEdge.pulledColumn H column)) := by
      rw [ReverseEdge.mulVec_firstVector G H column H_unit]
    _ = H *ᵥ ((G⁻¹ * G) *ᵥ ReverseEdge.pulledColumn H column) := by
      exact congrArg (fun vector => H *ᵥ vector)
        (Matrix.mulVec_mulVec _ G⁻¹ G)
    _ = H *ᵥ ReverseEdge.pulledColumn H column := by
      rw [Matrix.nonsing_inv_mul G (G.isUnit_iff_isUnit_det.mp G_unit),
        Matrix.one_mulVec]
    _ = column := ReverseEdge.mulVec_pulledColumn H column H_unit

/-- The second reverse-compiler scalar vanishes exactly on its second exceptional source ray. -/
theorem beta_eq_zero_iff_sourcePoint_eq_badSource
    (G H : Square Interface ℚ) (row column : Interface → ℚ)
    (G_unit : IsUnit G) (H_unit : IsUnit H)
    (row_ne : row ≠ 0) (column_ne : column ≠ 0) :
    ReverseEdge.beta G H row column = 0 ↔
      sourcePoint column = badSource G H row true := by
  rw [ReverseEdge.beta]
  have bridge_unit : IsUnit (H * G⁻¹ * H) :=
    (H_unit.mul (nonsingInv_isUnit G G_unit)).mul H_unit
  apply cut_eq_zero_iff_sourcePoint_eq_image bridge_unit row_ne
  · rw [ReverseEdge.firstVector]
    exact image_ne_zero (nonsingInv_isUnit H H_unit) <|
      image_ne_zero G_unit <|
        image_ne_zero (nonsingInv_isUnit H H_unit) column_ne
  · exact bridgeInverse_mulVec_firstVector G H column G_unit H_unit

/-- An ordered incidence instance is generic exactly off its two exceptional source rays. -/
theorem generic_iff_sourcePoint_not_mem_badSources
    (G H : Square Interface ℚ) (row column : Interface → ℚ)
    (G_unit : IsUnit G) (H_unit : IsUnit H)
    (row_ne : row ≠ 0) (column_ne : column ≠ 0) :
    ReverseEdge.alpha H row column ≠ 0 ∧
        ReverseEdge.beta G H row column ≠ 0 ↔
      sourcePoint column ∉ badSources G H row := by
  rw [badSources, Finset.mem_insert, Finset.mem_singleton]
  have alpha_zero := alpha_eq_zero_iff_sourcePoint_eq_badSource G H row column
    H_unit row_ne column_ne
  have beta_zero := beta_eq_zero_iff_sourcePoint_eq_badSource G H row column
    G_unit H_unit row_ne column_ne
  constructor
  · rintro ⟨alpha_ne, beta_ne⟩ (alpha_bad | beta_bad)
    · exact alpha_ne (alpha_zero.mpr alpha_bad)
    · exact beta_ne (beta_zero.mpr beta_bad)
  · intro neither
    constructor
    · intro alpha_is_zero
      exact neither (Or.inl (alpha_zero.mp alpha_is_zero))
    · intro beta_is_zero
      exact neither (Or.inr (beta_zero.mp beta_is_zero))

private theorem smulMatrix_isUnit
    {matrix : Square Interface ℚ} (matrix_unit : IsUnit matrix)
    {scalar : ℚ} (scalar_ne : scalar ≠ 0) :
    IsUnit (scalar • matrix) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, isUnit_iff_ne_zero]
  exact mul_ne_zero (pow_ne_zero _ scalar_ne)
    ((Matrix.isUnit_iff_isUnit_det matrix).mp matrix_unit).ne_zero

/-- Independent nonzero scaling of the two generators makes both exceptional scalars one while
preserving the complete incidence zero language, including the empty word. -/
theorem exists_unitNormalized
    (G H : Square Interface ℚ) (row column : Interface → ℚ)
    (G_unit : IsUnit G) (H_unit : IsUnit H)
    (alpha_ne : ReverseEdge.alpha H row column ≠ 0)
    (beta_ne : ReverseEdge.beta G H row column ≠ 0) :
    ∃ G' H', IsUnit G' ∧ IsUnit H' ∧
      ReverseEdge.alpha H' row column = 1 ∧
      ReverseEdge.beta G' H' row column = 1 ∧
      ∀ word, ReverseEdge.incidence G' H' row column word = 0 ↔
        ReverseEdge.incidence G H row column word = 0 := by
  let alpha := ReverseEdge.alpha H row column
  let beta := ReverseEdge.beta G H row column
  let gScale := alpha ^ 2 / beta
  let G' := gScale • G
  let H' := alpha • H
  have alpha_ne' : alpha ≠ 0 := alpha_ne
  have beta_ne' : beta ≠ 0 := beta_ne
  have gScale_ne : gScale ≠ 0 := div_ne_zero (pow_ne_zero _ alpha_ne') beta_ne'
  have G'_unit : IsUnit G' := smulMatrix_isUnit G_unit gScale_ne
  have H'_unit : IsUnit H' := smulMatrix_isUnit H_unit alpha_ne'
  let pulled := ReverseEdge.pulledColumn H column
  let first := ReverseEdge.firstVector G H column
  have pulled_action : H' *ᵥ (alpha⁻¹ • pulled) = column := by
    rw [show H' = alpha • H by rfl, Matrix.smul_mulVec_assoc,
      Matrix.mulVec_smul, smul_smul]
    rw [mul_inv_cancel₀ alpha_ne', one_smul]
    exact ReverseEdge.mulVec_pulledColumn H column H_unit
  have pulled_eq :
      ReverseEdge.pulledColumn H' column = alpha⁻¹ • pulled := by
    exact nonsingInv_mulVec_eq_of_mulVec_eq H'_unit pulled_action
  have normalized_alpha : ReverseEdge.alpha H' row column = 1 := by
    rw [ReverseEdge.alpha, pulled_eq, Matrix.dotProduct_smul]
    change alpha⁻¹ * alpha = 1
    exact inv_mul_cancel₀ alpha_ne'
  have first_action : H' *ᵥ (beta⁻¹ • first) = G' *ᵥ (alpha⁻¹ • pulled) := by
    rw [show H' = alpha • H by rfl, show G' = gScale • G by rfl,
      Matrix.smul_mulVec_assoc, Matrix.smul_mulVec_assoc,
      Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul, smul_smul]
    rw [show H *ᵥ first = G *ᵥ pulled by
      exact ReverseEdge.mulVec_firstVector G H column H_unit]
    congr 1
    dsimp [gScale]
    field_simp
    ring
  have first_eq :
      ReverseEdge.firstVector G' H' column = beta⁻¹ • first := by
    rw [ReverseEdge.firstVector, pulled_eq]
    exact nonsingInv_mulVec_eq_of_mulVec_eq H'_unit first_action
  have normalized_beta : ReverseEdge.beta G' H' row column = 1 := by
    rw [ReverseEdge.beta, first_eq, Matrix.dotProduct_smul]
    change beta⁻¹ * beta = 1
    exact inv_mul_cancel₀ beta_ne'
  refine ⟨G', H', G'_unit, H'_unit, normalized_alpha, normalized_beta, ?_⟩
  intro word
  let scales : Bool → ℚ
    | false => gScale
    | true => alpha
  have generator_eq :
      ReverseEdge.incidenceGenerator G' H' =
        fun label => scales label • ReverseEdge.incidenceGenerator G H label := by
    funext label
    cases label <;> rfl
  rw [ReverseEdge.incidence, ReverseEdge.incidence, generator_eq,
    wordProduct_smulMatrix, Matrix.smul_mulVec_assoc, Matrix.dotProduct_smul]
  have scales_ne : ∀ label, scales label ≠ 0 := by
    intro label
    cases label
    · exact gScale_ne
    · exact alpha_ne'
  have product_ne : (word.map scales).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro zero_mem
    obtain ⟨label, _, scale_zero⟩ := List.mem_map.mp zero_mem
    exact scales_ne label scale_zero
  constructor
  · intro scaled_zero
    exact (mul_eq_zero.mp scaled_zero).resolve_left product_ne
  · intro original_zero
    simp [original_zero]

end

end MatrixMortality.ProjectiveIncidence
