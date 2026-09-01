import MatrixMortality.CubicContinuantPunctuation

/-!
# Endpoint chart for the fixed cubic continuant family

An exact basis sends the separator source and covector to coordinate axes. In this chart the
positive scalar-bridge problem is precisely reachability of the accepting axis from the source
vector, while the two known length-seven cores already exhibit the inevitable accepting-fibre
collision.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

/-- Basis whose first column is the singular separator source. -/
def falseWaitEndpointBasis : Square (Fin 2) ℚ :=
  !![-79, 1; -90, 0]

/-- Exact inverse of `falseWaitEndpointBasis`. -/
def falseWaitEndpointBasisInverse : Square (Fin 2) ℚ :=
  !![0, -1 / 90; 1, -79 / 90]

/-- Source representative `e₀` in the endpoint chart. -/
def falseWaitEndpointSourceVector : Fin 2 → ℚ := ![1, 0]

/-- Accepting representative `e₁` in the endpoint chart. -/
def falseWaitEndpointAcceptingVector : Fin 2 → ℚ := ![0, 1]

/-- Closed endpoint-chart return attached to one cubic recurrence state. -/
def falseWaitEndpointReturnOfState
    (state : CubicDefectState) : Square (Fin 2) ℚ :=
  !![-79 * state.first - 30 * state.second - 90 * state.third,
      state.first;
    -3424 * state.first - 2376 * state.second,
      16 * state.first + 24 * state.second]

/-- Fixed false-wait return conjugated into separator endpoint coordinates. -/
def falseWaitEndpointReturn (wait : ℕ) : Square (Fin 2) ℚ :=
  falseWaitEndpointBasisInverse * falseWaitReturn wait * falseWaitEndpointBasis

/-- Relabelled positive endpoint return. -/
def positiveFalseWaitEndpointReturn (wait : ℕ) : Square (Fin 2) ℚ :=
  falseWaitEndpointReturn (wait + 1)

/-- The displayed inverse is a left inverse of the endpoint basis. -/
theorem falseWaitEndpointBasis_inverse_left :
    falseWaitEndpointBasisInverse * falseWaitEndpointBasis = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [falseWaitEndpointBasisInverse, falseWaitEndpointBasis,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

/-- The displayed inverse is a right inverse of the endpoint basis. -/
theorem falseWaitEndpointBasis_inverse_right :
    falseWaitEndpointBasis * falseWaitEndpointBasisInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [falseWaitEndpointBasisInverse, falseWaitEndpointBasis,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

/-- The singular source and covector become the two endpoint coordinate functionals. -/
theorem falseWaitEndpoint_separator_coordinates :
    falseWaitEndpointBasis *ᵥ falseWaitEndpointSourceVector =
        falseWaitSeparatorColumn ∧
      falseWaitSeparatorRow ᵥ* falseWaitEndpointBasis =
        (-90 : ℚ) • falseWaitEndpointSourceVector := by
  constructor <;>
    ext coordinate <;>
    fin_cases coordinate <;>
      norm_num [falseWaitEndpointBasis, falseWaitEndpointSourceVector,
        falseWaitSeparatorColumn, falseWaitSeparatorRow, Matrix.mulVec,
        Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

/-- Each conjugated return has the displayed integral endpoint-chart formula. -/
theorem falseWaitEndpointReturn_eq_state (wait : ℕ) :
    falseWaitEndpointReturn wait =
      falseWaitEndpointReturnOfState (cubicDefectState wait) := by
  rw [falseWaitEndpointReturn, falseWaitReturn_eq_state]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [falseWaitEndpointBasisInverse, falseWaitEndpointBasis,
      falseWaitEndpointReturnOfState, falseWaitReturnOfState,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

/-- Every endpoint word product is conjugate to the original physical return product. -/
theorem falseWaitEndpoint_wordProduct_conjugate (waits : List ℕ) :
    wordProduct falseWaitEndpointReturn waits =
      falseWaitEndpointBasisInverse *
        wordProduct falseWaitReturn waits * falseWaitEndpointBasis := by
  induction waits with
  | nil =>
      simp [wordProduct_nil, falseWaitEndpointBasis_inverse_left]
  | cons wait waits induction =>
      rw [wordProduct_cons, falseWaitEndpointReturn, induction]
      calc
        (falseWaitEndpointBasisInverse * falseWaitReturn wait *
              falseWaitEndpointBasis) *
            (falseWaitEndpointBasisInverse *
              wordProduct falseWaitReturn waits * falseWaitEndpointBasis) =
            falseWaitEndpointBasisInverse * falseWaitReturn wait *
              (falseWaitEndpointBasis * falseWaitEndpointBasisInverse) *
                wordProduct falseWaitReturn waits * falseWaitEndpointBasis := by
          simp only [Matrix.mul_assoc]
        _ = falseWaitEndpointBasisInverse * falseWaitReturn wait *
              wordProduct falseWaitReturn waits * falseWaitEndpointBasis := by
          rw [falseWaitEndpointBasis_inverse_right, Matrix.mul_one]
        _ = falseWaitEndpointBasisInverse *
              (falseWaitReturn wait * wordProduct falseWaitReturn waits) *
                falseWaitEndpointBasis := by
          simp only [Matrix.mul_assoc]

/-- Relabelled positive endpoint products are conjugate to relabelled positive physical
products. -/
theorem positiveFalseWaitEndpoint_wordProduct_conjugate (waits : List ℕ) :
    wordProduct positiveFalseWaitEndpointReturn waits =
      falseWaitEndpointBasisInverse *
        wordProduct positiveFalseWaitReturn waits * falseWaitEndpointBasis := by
  change wordProduct (falseWaitEndpointReturn ∘ fun wait => wait + 1) waits =
    falseWaitEndpointBasisInverse *
      wordProduct (falseWaitReturn ∘ fun wait => wait + 1) waits *
        falseWaitEndpointBasis
  rw [wordProduct_comp, wordProduct_comp]
  exact falseWaitEndpoint_wordProduct_conjugate (waits.map fun wait => wait + 1)

/-- Endpoint conjugation preserves the determinant of every physical word product. -/
theorem falseWaitEndpoint_wordProduct_det (waits : List ℕ) :
    (wordProduct falseWaitEndpointReturn waits).det =
      (wordProduct falseWaitReturn waits).det := by
  rw [falseWaitEndpoint_wordProduct_conjugate, Matrix.det_mul, Matrix.det_mul]
  norm_num [falseWaitEndpointBasisInverse, falseWaitEndpointBasis,
    Matrix.det_fin_two]
  ring

/-- Endpoint conjugation preserves each physical return determinant. -/
theorem falseWaitEndpointReturn_det (wait : ℕ) :
    (falseWaitEndpointReturn wait).det = (falseWaitReturn wait).det := by
  simpa [wordProduct_cons, wordProduct_nil] using
    falseWaitEndpoint_wordProduct_det [wait]

/-- Every relabelled positive endpoint return is a unit. -/
theorem positiveFalseWaitEndpointReturn_isUnit (wait : ℕ) :
    IsUnit (positiveFalseWaitEndpointReturn wait) := by
  rw [Matrix.isUnit_iff_isUnit_det, positiveFalseWaitEndpointReturn,
    falseWaitEndpointReturn_det]
  have physical_unit :=
    falseWaitReturn_positive_isUnit (by omega : 0 < wait + 1)
  rw [Matrix.isUnit_iff_isUnit_det] at physical_unit
  exact physical_unit

/-- Every relabelled positive endpoint word product is a unit. -/
theorem positiveFalseWaitEndpoint_wordProduct_isUnit (waits : List ℕ) :
    IsUnit (wordProduct positiveFalseWaitEndpointReturn waits) := by
  induction waits with
  | nil => exact isUnit_one
  | cons wait waits induction =>
      rw [wordProduct_cons]
      exact (positiveFalseWaitEndpointReturn_isUnit wait).mul induction

/-- The original bridge scalar is `-90` times the upper-left endpoint-product entry. -/
theorem falseWaitEndpoint_bridgeScalar_eq (waits : List ℕ) :
    bridgeScalar falseWaitSeparatorColumn falseWaitSeparatorRow
        (wordProduct falseWaitReturn waits) =
      -90 * (wordProduct falseWaitEndpointReturn waits) 0 0 := by
  rw [falseWaitEndpoint_wordProduct_conjugate]
  norm_num [bridgeScalar, falseWaitSeparatorColumn, falseWaitSeparatorRow,
    falseWaitEndpointBasisInverse, falseWaitEndpointBasis,
    Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct,
    Fin.sum_univ_succ]
  ring

/-- A raw physical bridge vanishes exactly when the endpoint product has zero upper-left
entry. -/
theorem falseWaitEndpoint_bridgeScalar_zero_iff (waits : List ℕ) :
    bridgeScalar falseWaitSeparatorColumn falseWaitSeparatorRow
        (wordProduct falseWaitReturn waits) = 0 ↔
      (wordProduct falseWaitEndpointReturn waits) 0 0 = 0 := by
  rw [falseWaitEndpoint_bridgeScalar_eq]
  constructor
  · intro product_zero
    linarith
  · intro entry_zero
    simp [entry_zero]

/-- A relabelled positive bridge scalar is `-90` times the upper-left endpoint-product entry. -/
theorem falseWaitPositiveBridge_eq_endpoint_entry (waits : List ℕ) :
    falseWaitPositiveBridge waits =
      -90 * (wordProduct positiveFalseWaitEndpointReturn waits) 0 0 := by
  rw [falseWaitPositiveBridge, positiveFalseWaitEndpoint_wordProduct_conjugate]
  norm_num [bridgeScalar, falseWaitSeparatorColumn, falseWaitSeparatorRow,
    falseWaitEndpointBasisInverse, falseWaitEndpointBasis,
    Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct,
    Fin.sum_univ_succ]
  ring

/-- A relabelled positive bridge vanishes exactly when its endpoint source lies on the
accepting `e₁` ray. -/
theorem falseWaitPositiveBridge_zero_iff_endpoint_accepting (waits : List ℕ) :
    falseWaitPositiveBridge waits = 0 ↔
      ∃ scale : ℚ, scale ≠ 0 ∧
        wordProduct positiveFalseWaitEndpointReturn waits *ᵥ
            falseWaitEndpointSourceVector =
          scale • falseWaitEndpointAcceptingVector := by
  rw [falseWaitPositiveBridge_eq_endpoint_entry]
  let product := wordProduct positiveFalseWaitEndpointReturn waits
  have product_unit : IsUnit product :=
    positiveFalseWaitEndpoint_wordProduct_isUnit waits
  constructor
  · intro product_zero
    have entry_zero : product 0 0 = 0 := by
      linarith
    refine ⟨product 1 0, ?_, ?_⟩
    · intro lower_zero
      have determinant_zero : product.det = 0 := by
        rw [Matrix.det_fin_two]
        simp [entry_zero, lower_zero]
      have determinant_unit : IsUnit product.det := by
        rw [← Matrix.isUnit_iff_isUnit_det]
        exact product_unit
      exact (isUnit_iff_ne_zero.mp determinant_unit) determinant_zero
    · ext coordinate
      fin_cases coordinate <;>
        simp [product, falseWaitEndpointSourceVector,
          falseWaitEndpointAcceptingVector, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ, entry_zero]
  · rintro ⟨scale, scale_ne, accepting⟩
    have first_coordinate := congrFun accepting 0
    have entry_zero : product 0 0 = 0 := by
      simpa [product, falseWaitEndpointSourceVector,
        falseWaitEndpointAcceptingVector, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ] using first_coordinate
    simpa [product] using entry_zero

/-- Mortality of the complete fixed family is exactly endpoint-source reachability of the
accepting ray by a positive word. -/
theorem falseWaitReturn_isMortal_iff_endpoint_accepting :
    IsMortal falseWaitReturn ↔
      ∃ waits : List ℕ, ∃ scale : ℚ, scale ≠ 0 ∧
        wordProduct positiveFalseWaitEndpointReturn waits *ᵥ
            falseWaitEndpointSourceVector =
          scale • falseWaitEndpointAcceptingVector := by
  rw [falseWaitReturn_isMortal_iff_positiveBridge]
  constructor
  · rintro ⟨waits, bridge_zero⟩
    exact ⟨waits,
      (falseWaitPositiveBridge_zero_iff_endpoint_accepting waits).mp bridge_zero⟩
  · rintro ⟨waits, accepting⟩
    exact ⟨waits,
      (falseWaitPositiveBridge_zero_iff_endpoint_accepting waits).mpr accepting⟩

/-- The two length-seven cores reach the accepting endpoint ray with explicit nonzero scales. -/
theorem falseWaitEndpoint_lengthSevenBridgeCore_accepting :
    wordProduct falseWaitEndpointReturn (falseWaitLengthSevenBridgeCore 0) *ᵥ
        falseWaitEndpointSourceVector =
          (29617088832000000 : ℚ) • falseWaitEndpointAcceptingVector ∧
      wordProduct falseWaitEndpointReturn (falseWaitLengthSevenBridgeCore 1) *ᵥ
          falseWaitEndpointSourceVector =
            (13080043192320000 : ℚ) • falseWaitEndpointAcceptingVector := by
  constructor <;>
    ext coordinate <;>
    fin_cases coordinate <;>
      norm_num [falseWaitLengthSevenBridgeCore, falseWaitEndpointSourceVector,
        falseWaitEndpointAcceptingVector, wordProduct_cons, wordProduct_nil,
        falseWaitEndpointReturn_eq_state, falseWaitEndpointReturnOfState,
        cubicDefectState, CubicDefectState.next, Matrix.mul_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Distinct equal-length words already collide projectively at the accepting endpoint ray. -/
theorem falseWaitEndpoint_lengthSevenBridgeCore_collision :
    wordProduct falseWaitEndpointReturn (falseWaitLengthSevenBridgeCore 0) *ᵥ
        falseWaitEndpointSourceVector =
      (195925 / 86528 : ℚ) •
        (wordProduct falseWaitEndpointReturn (falseWaitLengthSevenBridgeCore 1) *ᵥ
          falseWaitEndpointSourceVector) := by
  rw [falseWaitEndpoint_lengthSevenBridgeCore_accepting.1,
    falseWaitEndpoint_lengthSevenBridgeCore_accepting.2]
  ext coordinate
  fin_cases coordinate <;> norm_num [falseWaitEndpointAcceptingVector]

end MatrixMortality.CubicReturn.NonPure
