import MatrixMortality.ReverseEdge

/-!
# The unique hard rank-two edge stratum

A compatible two-vertex edge square with one rank-one loop and three units is already the raw
generic projective-incidence compiler, after one source-plane coordinate change.  The graph
constraint therefore contributes no additional hard core in this stratum.
-/

namespace MatrixMortality.RankTwoPunctuation

open scoped Matrix

/-- The two-dimensional compressed interface. -/
abbrev Interface := ReverseEdge.Interface

/-- Edge square with one distinguished loop.  Indices are target, source. -/
def oneLoopEdge (loop crossIn crossOut control : Square Interface ℚ) :
    Bool → Bool → Square Interface ℚ
  | false, false => loop
  | false, true => crossIn
  | true, false => crossOut
  | true, true => control

/-- The intrinsic incidence row. -/
def intrinsicRow (row : Interface → ℚ) (crossIn : Square Interface ℚ) : Interface → ℚ :=
  row ᵥ* crossIn

/-- The intrinsic incidence column. -/
def intrinsicColumn (crossOut : Square Interface ℚ) (column : Interface → ℚ) :
    Interface → ℚ :=
  crossOut *ᵥ column

/-- Move the source-zero interface through its unit cross-edge. -/
def sourceChange (crossIn : Square Interface ℚ) : Bool → Square Interface ℚ
  | false => crossIn
  | true => 1

/-- Inverse source-plane change. -/
noncomputable def sourceInverse (crossIn : Square Interface ℚ) : Bool → Square Interface ℚ
  | false => crossIn⁻¹
  | true => 1

private theorem compatible_firstColumn
    (loop crossIn crossOut control : Square Interface ℚ)
    (compatible : TwoPlaneEdges.Compatible (oneLoopEdge loop crossIn crossOut control)) :
    loop *ᵥ ![1, 0] = crossIn *ᵥ ![1, 0] ∧
      crossOut *ᵥ ![1, 0] = control *ᵥ ![1, 0] := by
  constructor
  · ext i
    simpa [oneLoopEdge, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using
      compatible false i
  · ext i
    simpa [oneLoopEdge, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using
      compatible true i

private theorem intrinsic_pulledColumn
    (crossIn crossOut : Square Interface ℚ) (column : Interface → ℚ)
    (crossIn_unit : IsUnit crossIn) (crossOut_unit : IsUnit crossOut) :
    ReverseEdge.pulledColumn (crossOut * crossIn) (intrinsicColumn crossOut column) =
      crossIn⁻¹ *ᵥ column := by
  apply Matrix.mulVec_injective_iff_isUnit.mpr (crossOut_unit.mul crossIn_unit)
  rw [ReverseEdge.mulVec_pulledColumn _ _ (crossOut_unit.mul crossIn_unit)]
  simp only [intrinsicColumn, Matrix.mulVec_mulVec]
  rw [Matrix.mul_assoc,
    Matrix.mul_nonsing_inv crossIn (crossIn.isUnit_iff_isUnit_det.mp crossIn_unit),
    Matrix.mul_one]

private theorem intrinsic_alpha_eq_selfBridge
    (crossIn crossOut : Square Interface ℚ) (column row : Interface → ℚ)
    (crossIn_unit : IsUnit crossIn) (crossOut_unit : IsUnit crossOut) :
    ReverseEdge.alpha (crossOut * crossIn) (intrinsicRow row crossIn)
        (intrinsicColumn crossOut column) = row ⬝ᵥ column := by
  rw [ReverseEdge.alpha, intrinsicRow,
    intrinsic_pulledColumn crossIn crossOut column crossIn_unit crossOut_unit,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv crossIn (crossIn.isUnit_iff_isUnit_det.mp crossIn_unit),
    Matrix.one_mulVec]

private theorem sourceChange_mul_sourceInverse
    (crossIn : Square Interface ℚ) (crossIn_unit : IsUnit crossIn) :
    ∀ source, sourceChange crossIn source * sourceInverse crossIn source = 1 := by
  intro source
  cases source
  · exact Matrix.mul_nonsing_inv crossIn
      (crossIn.isUnit_iff_isUnit_det.mp crossIn_unit)
  · simp [sourceChange, sourceInverse]

private theorem sourceInverse_mul_sourceChange
    (crossIn : Square Interface ℚ) (crossIn_unit : IsUnit crossIn) :
    ∀ source, sourceInverse crossIn source * sourceChange crossIn source = 1 := by
  intro source
  cases source
  · exact Matrix.nonsing_inv_mul crossIn
      (crossIn.isUnit_iff_isUnit_det.mp crossIn_unit)
  · simp [sourceChange, sourceInverse]

private theorem sourceChange_isUnit
    (crossIn : Square Interface ℚ) (crossIn_unit : IsUnit crossIn) :
    ∀ source, IsUnit (sourceChange crossIn source) := by
  intro source
  cases source
  · exact crossIn_unit
  · simp [sourceChange]

private theorem sourceInverse_isUnit
    (crossIn : Square Interface ℚ) (crossIn_unit : IsUnit crossIn) :
    ∀ source, IsUnit (sourceInverse crossIn source) := by
  intro source
  cases source
  · exact nonsingInv_isUnit crossIn crossIn_unit
  · simp [sourceInverse]

private theorem intrinsic_beta_eq_one
    (column row : Interface → ℚ)
    (crossIn crossOut control : Square Interface ℚ)
    (compatible :
      TwoPlaneEdges.Compatible
        (oneLoopEdge (Matrix.vecMulVec column row) crossIn crossOut control))
    (crossIn_unit : IsUnit crossIn) (crossOut_unit : IsUnit crossOut) :
    ReverseEdge.beta control (crossOut * crossIn)
        (intrinsicRow row crossIn) (intrinsicColumn crossOut column) = 1 := by
  let first : Interface → ℚ := ![1, 0]
  let pivot := row 0
  have compatible_columns :=
    compatible_firstColumn (Matrix.vecMulVec column row) crossIn crossOut control compatible
  have crossIn_first : crossIn *ᵥ first = pivot • column := by
    rw [← compatible_columns.1]
    ext i
    fin_cases i <;>
      simp [pivot, Matrix.mulVec, dotProduct,
        Matrix.vecMulVec_apply, Fin.sum_univ_succ] <;> ring
  have first_ne : first ≠ 0 := by
    intro first_zero
    have := congr_fun first_zero 0
    simp [first] at this
  have pivot_ne : pivot ≠ 0 := by
    intro pivot_zero
    have crossIn_first_ne := unit_mulVec_ne_zero crossIn_unit first_ne
    rw [crossIn_first, pivot_zero, zero_smul] at crossIn_first_ne
    exact crossIn_first_ne rfl
  have pulled_scaled :
      pivot • ReverseEdge.pulledColumn (crossOut * crossIn)
          (intrinsicColumn crossOut column) = first := by
    rw [intrinsic_pulledColumn crossIn crossOut column crossIn_unit crossOut_unit]
    calc
      pivot • (crossIn⁻¹ *ᵥ column) =
          crossIn⁻¹ *ᵥ (pivot • column) := by rw [Matrix.mulVec_smul]
      _ = crossIn⁻¹ *ᵥ (crossIn *ᵥ first) := by rw [crossIn_first]
      _ = (crossIn⁻¹ * crossIn) *ᵥ first := by rw [Matrix.mulVec_mulVec]
      _ = first := by
        rw [Matrix.nonsing_inv_mul crossIn
          (crossIn.isUnit_iff_isUnit_det.mp crossIn_unit), Matrix.one_mulVec]
  have firstVector_scaled :
      pivot • ReverseEdge.firstVector control (crossOut * crossIn)
          (intrinsicColumn crossOut column) = crossIn⁻¹ *ᵥ first := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr (crossOut_unit.mul crossIn_unit)
    rw [Matrix.mulVec_smul,
      ReverseEdge.mulVec_firstVector control (crossOut * crossIn)
        (intrinsicColumn crossOut column) (crossOut_unit.mul crossIn_unit),
      ← Matrix.mulVec_smul, pulled_scaled]
    simp only [Matrix.mulVec_mulVec]
    rw [Matrix.mul_assoc,
      Matrix.mul_nonsing_inv crossIn
        (crossIn.isUnit_iff_isUnit_det.mp crossIn_unit), Matrix.mul_one]
    simpa [first] using compatible_columns.2.symm
  have crossIn_firstVector_scaled :
      pivot • (crossIn *ᵥ ReverseEdge.firstVector control (crossOut * crossIn)
          (intrinsicColumn crossOut column)) = first := by
    rw [← Matrix.mulVec_smul, firstVector_scaled, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv crossIn
        (crossIn.isUnit_iff_isUnit_det.mp crossIn_unit), Matrix.one_mulVec]
  apply mul_left_cancel₀ pivot_ne
  calc
    pivot * ReverseEdge.beta control (crossOut * crossIn)
          (intrinsicRow row crossIn) (intrinsicColumn crossOut column) =
        row ⬝ᵥ (pivot • (crossIn *ᵥ
          ReverseEdge.firstVector control (crossOut * crossIn)
            (intrinsicColumn crossOut column))) := by
      rw [ReverseEdge.beta, intrinsicRow, ← Matrix.dotProduct_mulVec,
        dotProduct_smul]
      simp [smul_eq_mul]
    _ = row ⬝ᵥ first := by rw [crossIn_firstVector_scaled]
    _ = pivot * 1 := by
      simp [first, pivot, dotProduct, Fin.sum_univ_succ]

/-- Normalizing a compatible one-loop edge square produces the existing raw reverse edge
exactly.  In particular, its second exceptional scalar is forced to one. -/
theorem transport_eq_rawEdge
    (column row : Interface → ℚ)
    (crossIn crossOut control : Square Interface ℚ)
    (compatible :
      TwoPlaneEdges.Compatible
        (oneLoopEdge (Matrix.vecMulVec column row) crossIn crossOut control))
    (crossIn_unit : IsUnit crossIn) (crossOut_unit : IsUnit crossOut) :
    TwoPlaneEdges.transport
        (oneLoopEdge (Matrix.vecMulVec column row) crossIn crossOut control)
        (sourceChange crossIn) (sourceInverse crossIn) =
      ReverseEdge.rawEdge control (crossOut * crossIn)
        (intrinsicRow row crossIn) (intrinsicColumn crossOut column) := by
  funext target source
  cases target <;> cases source
  · simp only [TwoPlaneEdges.transport, oneLoopEdge, sourceChange, sourceInverse,
      ReverseEdge.rawEdge, ReverseEdge.testLoop]
    rw [show ReverseEdge.beta control (crossOut * crossIn)
        (intrinsicRow row crossIn) (intrinsicColumn crossOut column) = 1 by
      exact intrinsic_beta_eq_one column row crossIn crossOut control compatible
        crossIn_unit crossOut_unit]
    simp only [inv_one, one_smul]
    rw [mul_outer, outer_mul,
      intrinsic_pulledColumn crossIn crossOut column crossIn_unit crossOut_unit]
    rfl
  · simp only [TwoPlaneEdges.transport, oneLoopEdge, sourceChange, sourceInverse,
      ReverseEdge.rawEdge, Matrix.mul_one]
    exact Matrix.nonsing_inv_mul crossIn
      (crossIn.isUnit_iff_isUnit_det.mp crossIn_unit)
  · simp [TwoPlaneEdges.transport, oneLoopEdge, sourceChange, sourceInverse,
      ReverseEdge.rawEdge]
  · simp [TwoPlaneEdges.transport, oneLoopEdge, sourceChange, sourceInverse,
      ReverseEdge.rawEdge]

/-- The one-loop/three-unit stratum is one generic projective-incidence instance.  The empty
incidence word is retained and is exactly the nilpotent-loop case. -/
theorem exists_pathProduct_eq_zero_iff_incidence
    (column row : Interface → ℚ)
    (crossIn crossOut control : Square Interface ℚ)
    (compatible :
      TwoPlaneEdges.Compatible
        (oneLoopEdge (Matrix.vecMulVec column row) crossIn crossOut control))
    (crossIn_unit : IsUnit crossIn) (crossOut_unit : IsUnit crossOut)
    (control_unit : IsUnit control)
    (selfBridge_nonzero : row ⬝ᵥ column ≠ 0) :
    (∃ start tail,
        EdgeCompression.pathProduct
            (oneLoopEdge (Matrix.vecMulVec column row) crossIn crossOut control)
            start tail = 0) ↔
      ∃ word,
        ReverseEdge.incidence control (crossOut * crossIn)
          (intrinsicRow row crossIn) (intrinsicColumn crossOut column) word = 0 := by
  let edge := oneLoopEdge (Matrix.vecMulVec column row) crossIn crossOut control
  let normalized :=
    TwoPlaneEdges.transport edge (sourceChange crossIn) (sourceInverse crossIn)
  have normalized_eq :
      normalized = ReverseEdge.rawEdge control (crossOut * crossIn)
        (intrinsicRow row crossIn) (intrinsicColumn crossOut column) := by
    simpa [edge, normalized] using
      transport_eq_rawEdge column row crossIn crossOut control compatible
        crossIn_unit crossOut_unit
  have normalized_zero_iff (start : Bool) (tail : List Bool) :
      EdgeCompression.pathProduct normalized start tail = 0 ↔
        EdgeCompression.pathProduct edge start tail = 0 := by
    exact TwoPlaneEdges.transport_edgeProduct_eq_zero_iff
      edge (sourceChange crossIn) (sourceInverse crossIn)
      (sourceChange_mul_sourceInverse crossIn crossIn_unit)
      (sourceInverse_mul_sourceChange crossIn crossIn_unit)
      (sourceChange_isUnit crossIn crossIn_unit)
      (sourceInverse_isUnit crossIn crossIn_unit) start tail
  have return_unit : IsUnit (crossOut * crossIn) := crossOut_unit.mul crossIn_unit
  have alpha_nonzero :
      ReverseEdge.alpha (crossOut * crossIn) (intrinsicRow row crossIn)
          (intrinsicColumn crossOut column) ≠ 0 := by
    rw [intrinsic_alpha_eq_selfBridge crossIn crossOut column row
      crossIn_unit crossOut_unit]
    exact selfBridge_nonzero
  have beta_nonzero :
      ReverseEdge.beta control (crossOut * crossIn) (intrinsicRow row crossIn)
          (intrinsicColumn crossOut column) ≠ 0 := by
    rw [intrinsic_beta_eq_one column row crossIn crossOut control compatible
      crossIn_unit crossOut_unit]
    norm_num
  constructor
  · rintro ⟨start, tail, edge_zero⟩
    have normalized_zero : EdgeCompression.pathProduct normalized start tail = 0 :=
      (normalized_zero_iff start tail).mpr (by simpa [edge] using edge_zero)
    have raw_zero :
        EdgeCompression.pathProduct
            (ReverseEdge.rawEdge control (crossOut * crossIn)
              (intrinsicRow row crossIn) (intrinsicColumn crossOut column))
            start tail = 0 := by
      simpa [normalized_eq] using normalized_zero
    by_contra no_incidence
    have incidence_nonzero :
        ∀ word,
          ReverseEdge.incidence control (crossOut * crossIn)
              (intrinsicRow row crossIn) (intrinsicColumn crossOut column) word ≠ 0 := by
      intro word word_zero
      exact no_incidence ⟨word, word_zero⟩
    exact ReverseEdge.rawEdge_pathProduct_ne_zero control (crossOut * crossIn)
      (intrinsicRow row crossIn) (intrinsicColumn crossOut column)
      control_unit return_unit alpha_nonzero beta_nonzero incidence_nonzero
      start tail raw_zero
  · rintro ⟨word, incidence_zero⟩
    obtain ⟨start, tail, raw_zero⟩ :=
      ReverseEdge.exists_rawEdge_pathProduct_eq_zero_of_incidence
        control (crossOut * crossIn) (intrinsicRow row crossIn)
        (intrinsicColumn crossOut column) return_unit incidence_zero
    have normalized_zero : EdgeCompression.pathProduct normalized start tail = 0 := by
      rw [normalized_eq]
      exact raw_zero
    refine ⟨start, tail, ?_⟩
    simpa [edge] using (normalized_zero_iff start tail).mp normalized_zero

/-- Complete one-loop classification: a nilpotent test loop is immediately mortal; otherwise
the edge square is mortal exactly when its single intrinsic projective-incidence instance has a
zero. -/
theorem exists_pathProduct_eq_zero_iff_selfBridge_or_incidence
    (column row : Interface → ℚ)
    (crossIn crossOut control : Square Interface ℚ)
    (compatible :
      TwoPlaneEdges.Compatible
        (oneLoopEdge (Matrix.vecMulVec column row) crossIn crossOut control))
    (crossIn_unit : IsUnit crossIn) (crossOut_unit : IsUnit crossOut)
    (control_unit : IsUnit control) :
    (∃ start tail,
        EdgeCompression.pathProduct
            (oneLoopEdge (Matrix.vecMulVec column row) crossIn crossOut control)
            start tail = 0) ↔
      row ⬝ᵥ column = 0 ∨
        ∃ word,
          ReverseEdge.incidence control (crossOut * crossIn)
            (intrinsicRow row crossIn) (intrinsicColumn crossOut column) word = 0 := by
  by_cases selfBridge_zero : row ⬝ᵥ column = 0
  · constructor
    · exact fun _ => Or.inl selfBridge_zero
    · intro _
      refine ⟨false, [false, false], ?_⟩
      simp [EdgeCompression.pathProduct, oneLoopEdge, outer_mul_outer,
        selfBridge_zero]
  · rw [or_iff_right selfBridge_zero]
    exact exists_pathProduct_eq_zero_iff_incidence column row crossIn crossOut control
      compatible crossIn_unit crossOut_unit control_unit selfBridge_zero

end MatrixMortality.RankTwoPunctuation
