import MatrixMortality.TransverseLineAtlas
import MatrixMortality.TwoPlaneEdges

/-!
# The one-chart hard core of the transverse line atlas

Every two-generator rational projective-line incidence instance embeds exactly into the
singular-data, involutive-toggle architecture of `TransverseLineAtlas`. Both lifted data controls
have one common invariant image plane, and the identity toggle erases from every raw word. Thus
the finite-atlas survivor already contains the complete `M₂(3)` projective hard core before any
chart switching occurs.
-/

namespace MatrixMortality
namespace TransverseLineHardCore

open scoped Matrix

/-- Two-dimensional projective interface. -/
abbrev Interface := Fin 2
/-- Rational states on the projective interface. -/
abbrev SmallState := Interface → ℚ
/-- Rational matrices acting on the projective interface. -/
abbrev SmallMatrix := Matrix Interface Interface ℚ
/-- Three-dimensional rational carrier state. -/
abbrev State := Fin 3 → ℚ
/-- Rational control matrices acting on the carrier. -/
abbrev ControlMatrix := Matrix (Fin 3) (Fin 3) ℚ

/-- Inclusion of the first coordinate plane. -/
def planeInput : Matrix (Fin 3) Interface ℚ :=
  TwoPlaneEdges.input false

/-- Projection splitting `planeInput`. -/
def planeProjection : Matrix Interface (Fin 3) ℚ :=
  TwoPlaneEdges.inputLeftInverse false

theorem planeProjection_mul_planeInput : planeProjection * planeInput = 1 :=
  TwoPlaneEdges.inputLeftInverse_mul_input false

/-- Embed a two-state matrix as a three-state map with common image plane and zero transverse
coordinate. -/
def liftMatrix (matrix : SmallMatrix) : ControlMatrix :=
  planeInput * (matrix * planeProjection)

/-- Embed a two-state column in the common invariant plane. -/
def liftColumn (column : SmallState) : State :=
  planeInput *ᵥ column

/-- Extend a two-state row by zero on the transverse coordinate. -/
def liftRow (row : SmallState) : State :=
  row ᵥ* planeProjection

theorem planeProjection_mulVec_liftColumn (column : SmallState) :
    planeProjection *ᵥ liftColumn column = column := by
  rw [liftColumn, Matrix.mulVec_mulVec, planeProjection_mul_planeInput, Matrix.one_mulVec]

theorem liftColumn_eq_zero_iff (column : SmallState) : liftColumn column = 0 ↔ column = 0 := by
  constructor
  · intro liftedZero
    calc
      column = planeProjection *ᵥ liftColumn column :=
        (planeProjection_mulVec_liftColumn column).symm
      _ = 0 := by rw [liftedZero, Matrix.mulVec_zero]
  · rintro rfl
    simp [liftColumn]

theorem liftRow_vecMul_planeInput (row : SmallState) :
    liftRow row ᵥ* planeInput = row := by
  rw [liftRow, Matrix.vecMul_vecMul, planeProjection_mul_planeInput, Matrix.vecMul_one]

theorem liftRow_eq_zero_iff (row : SmallState) : liftRow row = 0 ↔ row = 0 := by
  constructor
  · intro liftedZero
    calc
      row = liftRow row ᵥ* planeInput := (liftRow_vecMul_planeInput row).symm
      _ = 0 := by rw [liftedZero, Matrix.zero_vecMul]
  · rintro rfl
    simp [liftRow]

/-- The common invariant plane of every lifted data map. -/
def plane : Submodule ℚ State :=
  LinearMap.range (Matrix.toLin' planeInput)

theorem liftColumn_mem_plane (column : SmallState) : liftColumn column ∈ plane :=
  ⟨column, rfl⟩

theorem liftMatrix_mulVec_liftColumn (matrix : SmallMatrix) (column : SmallState) :
    liftMatrix matrix *ᵥ liftColumn column = liftColumn (matrix *ᵥ column) := by
  simp only [liftMatrix, liftColumn, ← Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_mulVec column planeProjection planeInput,
    planeProjection_mul_planeInput, Matrix.one_mulVec]

theorem liftRow_dotProduct_liftColumn (row column : SmallState) :
    liftRow row ⬝ᵥ liftColumn column = row ⬝ᵥ column := by
  rw [liftRow, liftColumn, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec column planeProjection planeInput,
    planeProjection_mul_planeInput, Matrix.one_mulVec]

/-- Every lifted data map is singular. -/
theorem liftMatrix_det (matrix : SmallMatrix) : (liftMatrix matrix).det = 0 := by
  have transverse_ne : (![0, 0, 1] : State) ≠ 0 := by
    intro transverse_zero
    have one_zero : (1 : ℚ) = 0 := by
      simpa [Matrix.cons_val_two] using congrFun transverse_zero 2
    exact one_ne_zero one_zero
  have transverse_kernel : liftMatrix matrix *ᵥ ![0, 0, 1] = 0 := by
    ext i
    fin_cases i <;>
      simp [liftMatrix, planeInput, planeProjection, TwoPlaneEdges.input,
        TwoPlaneEdges.inputLeftInverse, Matrix.mulVec, Matrix.mul_apply,
        dotProduct, Fin.sum_univ_succ]
  by_contra det_ne
  have matrixUnit : IsUnit (liftMatrix matrix) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact det_ne
  have injective := Matrix.mulVec_injective_iff_isUnit.mpr matrixUnit
  apply transverse_ne
  apply injective
  simpa using transverse_kernel

/-- An invertible two-state matrix lifts to a matrix of rank exactly two. -/
theorem liftMatrix_rank_eq_two (matrix : SmallMatrix) (matrixUnit : IsUnit matrix) :
    (liftMatrix matrix).rank = 2 := by
  apply le_antisymm
  · calc
      (liftMatrix matrix).rank ≤ planeInput.rank := by
        exact Matrix.rank_mul_le_left planeInput (matrix * planeProjection)
      _ ≤ Fintype.card Interface := Matrix.rank_le_width planeInput
      _ = 2 := by norm_num
  · have smallRank : matrix.rank = 2 := by
      apply Matrix.rank_of_isUnit
      exact matrixUnit
    have corner :
        (liftMatrix matrix).submatrix Fin.castSucc Fin.castSucc = matrix := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [liftMatrix, planeInput, planeProjection, TwoPlaneEdges.input,
          TwoPlaneEdges.inputLeftInverse, Matrix.mul_apply, Matrix.vecMul,
          dotProduct, Fin.sum_univ_succ]
    calc
      2 = matrix.rank := smallRank.symm
      _ = ((liftMatrix matrix).submatrix Fin.castSucc Fin.castSucc).rank := by rw [corner]
      _ ≤ (liftMatrix matrix).rank := Matrix.rank_submatrix_le _ _ _

theorem liftMatrix_mulVec_mem_plane (matrix : SmallMatrix) (state : State) :
    liftMatrix matrix *ᵥ state ∈ plane := by
  refine ⟨matrix *ᵥ (planeProjection *ᵥ state), ?_⟩
  simp [liftMatrix, ← Matrix.mulVec_mulVec]

/-- For an invertible two-state matrix, the lifted image is exactly the common plane. -/
theorem liftMatrix_range_eq_plane (matrix : SmallMatrix) (matrixUnit : IsUnit matrix) :
    LinearMap.range (Matrix.toLin' (liftMatrix matrix)) = plane := by
  apply le_antisymm
  · rintro state ⟨preimage, rfl⟩
    exact liftMatrix_mulVec_mem_plane matrix preimage
  · rintro state ⟨vector, rfl⟩
    obtain ⟨preimage, image_eq⟩ :=
      Matrix.mulVec_surjective_iff_isUnit.mpr matrixUnit vector
    refine ⟨liftColumn preimage, ?_⟩
    change liftMatrix matrix *ᵥ liftColumn preimage = planeInput *ᵥ vector
    rw [liftMatrix_mulVec_liftColumn, image_eq, liftColumn]

/-- Lift both projective generators into the common plane. -/
def data (generators : TagLetter → SmallMatrix) (letter : TagLetter) : ControlMatrix :=
  liftMatrix (generators letter)

/-- The transverse generator with identity toggle. -/
def generator (generators : TagLetter → SmallMatrix) : PairedControl → ControlMatrix :=
  TransverseLineAtlas.generator (data generators) 1

/-- Delete every identity-toggle control. -/
def eraseToggles : List PairedControl → List TagLetter
  | [] => []
  | .data letter :: word => letter :: eraseToggles word
  | .toggle :: word => eraseToggles word

/-- Embed a two-letter word without inserting toggles. -/
def dataWord (word : List TagLetter) : List PairedControl :=
  word.map PairedControl.data

theorem eraseToggles_dataWord (word : List TagLetter) :
    eraseToggles (dataWord word) = word := by
  induction word with
  | nil => rfl
  | cons letter word induction =>
      change letter :: eraseToggles (dataWord word) = letter :: word
      rw [induction]

/-- Exact state transport on every raw control word. Toggle erasure preserves multiplication
order. -/
theorem wordProduct_mulVec_liftColumn
    (generators : TagLetter → SmallMatrix) (column : SmallState)
    (word : List PairedControl) :
    wordProduct (generator generators) word *ᵥ liftColumn column =
      liftColumn (wordProduct generators (eraseToggles word) *ᵥ column) := by
  induction word with
  | nil =>
      simp only [wordProduct, List.map_nil, List.prod_nil, Matrix.one_mulVec, eraseToggles]
  | cons control word induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec, induction]
      cases control with
      | data letter =>
          rw [eraseToggles, wordProduct_cons, generator,
            TransverseLineAtlas.generator, data, liftMatrix_mulVec_liftColumn,
            ← Matrix.mulVec_mulVec]
      | toggle =>
          simp [eraseToggles, generator, TransverseLineAtlas.generator]

/-- The lifted scalar coefficient is exactly the two-state coefficient after deleting toggles. -/
theorem linearCoefficient_eq
    (generators : TagLetter → SmallMatrix) (row column : SmallState)
    (word : List PairedControl) :
    linearCoefficient (generator generators) (liftRow row) (liftColumn column) word =
      linearCoefficient generators row column (eraseToggles word) := by
  rw [linearCoefficient, linearCoefficient, wordProduct_mulVec_liftColumn,
    liftRow_dotProduct_liftColumn]

theorem coefficient_zero_iff
    (generators : TagLetter → SmallMatrix) (row column : SmallState)
    (word : List PairedControl) :
    linearCoefficient (generator generators) (liftRow row) (liftColumn column) word = 0 ↔
      linearCoefficient generators row column (eraseToggles word) = 0 := by
  rw [linearCoefficient_eq]

/-- Exact many-one embedding of two-generator projective incidence into the one-chart transverse
atlas. Raw toggles introduce no extra zeros, and every two-letter witness embeds without a
toggle. -/
theorem exists_zero_iff
    (generators : TagLetter → SmallMatrix) (row column : SmallState) :
    (∃ word : List PairedControl,
      linearCoefficient (generator generators) (liftRow row) (liftColumn column) word = 0) ↔
      ∃ word : List TagLetter, linearCoefficient generators row column word = 0 := by
  constructor
  · rintro ⟨word, wordZero⟩
    exact ⟨eraseToggles word, (coefficient_zero_iff generators row column word).mp wordZero⟩
  · rintro ⟨word, wordZero⟩
    refine ⟨dataWord word, ?_⟩
    rw [linearCoefficient_eq, eraseToggles_dataWord]
    exact wordZero

theorem data_det (generators : TagLetter → SmallMatrix) (letter : TagLetter) :
    (data generators letter).det = 0 :=
  liftMatrix_det (generators letter)

theorem data_rank_eq_two (generators : TagLetter → SmallMatrix)
    (generatorsUnit : ∀ letter, IsUnit (generators letter)) (letter : TagLetter) :
    (data generators letter).rank = 2 :=
  liftMatrix_rank_eq_two (generators letter) (generatorsUnit letter)

theorem data_range_eq_plane (generators : TagLetter → SmallMatrix)
    (generatorsUnit : ∀ letter, IsUnit (generators letter)) (letter : TagLetter) :
    LinearMap.range (Matrix.toLin' (data generators letter)) = plane :=
  liftMatrix_range_eq_plane (generators letter) (generatorsUnit letter)

/-- Both the untoggled and toggled data carriers are the same plane. -/
theorem data_carrier_eq_plane (generators : TagLetter → SmallMatrix)
    (generatorsUnit : ∀ letter, IsUnit (generators letter)) (column : SmallState)
    (toggled : Bool) (letter : TagLetter) :
    TransverseLineAtlas.carrier (data generators) 1 (liftColumn column)
      (.data toggled letter) = plane := by
  cases toggled with
  | false => exact data_range_eq_plane generators generatorsUnit letter
  | true =>
      rw [TransverseLineAtlas.carrier, data_range_eq_plane generators generatorsUnit letter]
      simp

theorem toggle_involutive :
    (1 : ControlMatrix) * 1 = 1 := by simp

end TransverseLineHardCore
end MatrixMortality
