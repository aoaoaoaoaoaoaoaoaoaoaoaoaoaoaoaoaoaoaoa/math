import MatrixMortality.GeometricTailHankel
import MatrixMortality.ChangedSeparatorMortality
import Mathlib.Tactic

/-!
# Tilted geometric-tail obstruction

At deletion width three and body `bb`, no exact transfer realization of the toggle and two data
roles followed by a geometric tilted-separator tail has fewer than nine states. Four sparse
Hankel minors cover every tail scale in the injective same-zero chamber.
-/

namespace MatrixMortality

open scoped Matrix

namespace TiltedGeometricHankel

private def separator (q : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  Matrix.vecMulVec (![67, 0, 81, -1] : Fin 4 → ℚ) (![1, q, q, q] : Fin 4 → ℚ)

/-- Benchmark toggle and data roles followed by a geometric tilted-separator tail. -/
def moment (q tailScale tailRatio : ℚ) : Nat → Matrix (Fin 4) (Fin 4) ℚ
  | 0 => RunLengthHankel.benchmarkToggle
  | 1 => RunLengthHankel.benchmarkDataB
  | 2 => RunLengthHankel.benchmarkDataC
  | offset + 3 => (tailScale * tailRatio ^ offset) • separator q

/-- The checked rank-nine compiler's width-three benchmark has the tilted geometric moments. -/
theorem benchmark_return_eq_moment (n : Nat) :
    ReturnFamily.returnMatrix
        (ChangedSeparatorRealization.transition 3 [.b, .b])
        (ChangedSeparatorRealization.input 3 [.b, .b])
        (ChangedSeparatorRealization.output 3 [.b, .b]) n =
      moment (ChangedSeparatorTail.nearyTailRatio 3 [.b, .b])
        (ChangedSeparatorRealization.separatorScale 3 [.b, .b])
        (ChangedSeparatorRealization.tailEigenvalue 3 [.b, .b]) n := by
  have column_eq :
      pairedTrailingToggleColumn ℚ 3 = (![67, 0, 81, -1] : Fin 4 → ℚ) := by
    rw [← ChangedSeparatorRealization.chainTailColumn_eq_pairedTrailingToggleColumn]
    funext i
    fin_cases i <;>
      norm_num [ChangedSeparatorRealization.chainTailColumn,
        ChangedSeparatorRealization.widthScale]
  rw [ChangedSeparatorRealization.returnMatrix_eq_scaled_tiltedFamily 3 (by norm_num)
    [.b, .b] (by simp) n]
  cases n with
  | zero =>
      simp [moment, ChangedSeparatorRealization.returnScale,
        ChangedSeparatorRealization.tiltedFamily,
        ChangedSeparatorRealization.returnLabel, separatedGenerator, pairedGenerator,
        RunLengthHankel.benchmarkToggle_eq_paired]
  | succ n =>
      cases n with
      | zero =>
          simp [moment, ChangedSeparatorRealization.returnScale,
            ChangedSeparatorRealization.tiltedFamily,
            ChangedSeparatorRealization.returnLabel, separatedGenerator, pairedGenerator,
            RunLengthHankel.benchmarkDataB_eq_paired]
      | succ n =>
          cases n with
          | zero =>
              simp [moment, ChangedSeparatorRealization.returnScale,
                ChangedSeparatorRealization.tiltedFamily,
                ChangedSeparatorRealization.returnLabel, separatedGenerator, pairedGenerator,
                RunLengthHankel.benchmarkDataC_eq_paired]
          | succ n =>
              simp [moment, mul_comm, ChangedSeparatorRealization.returnScale,
                ChangedSeparatorRealization.tiltedFamily,
                ChangedSeparatorRealization.returnLabel, separatedGenerator,
                ChangedSeparatorRealization.tiltedSeparator, separator,
                ChangedSeparatorTail.uniformTailRow, column_eq, Matrix.vecMulVec]

private def column : Fin 9 → Nat × Fin 4 :=
  ![(0, 0), (0, 1), (0, 2), (0, 3),
    (1, 0), (1, 1), (1, 2), (1, 3), (2, 0)]

private def row (extra₀ extra₁ : Nat × Fin 4) : Fin 9 → Nat × Fin 4 :=
  ![(0, 0), (0, 1), (0, 2), (0, 3),
    (1, 0), (1, 2), (1, 3), extra₀, extra₁]

private def minor (extra₀ extra₁ : Nat × Fin 4) (q tailScale tailRatio : ℚ) :
    Matrix (Fin 9) (Fin 9) ℚ :=
  fun i j =>
    moment q tailScale tailRatio ((row extra₀ extra₁ i).1 + (column j).1)
      (row extra₀ extra₁ i).2 (column j).2

private structure CommonKernel (tailScale : ℚ) (v : Fin 9 → ℚ) : Prop where
  x3 : v 3 = 0
  x6 : 19682 * v 6 = 27 * tailScale * v 8
  x2 : 19682 * v 2 = -6561 * tailScale * v 8
  x1 : 72672 * v 1 = (183194 - 81 * tailScale) * v 8
  x5 : 478763136 * v 5 = (309 * tailScale - 19682) * v 8
  x7 : 17731968 * v 7 = (6485 * tailScale - 14893218) * v 8
  x04 : 1555980192 * (v 0 + v 4) =
    -(433900101 * tailScale + 247501150) * v 8

private structure CommonCoordinates (tailScale : ℚ) (v : Fin 9 → ℚ) : Prop where
  x6 : v 6 = 27 * tailScale / 19682 * v 8
  x2 : v 2 = -6561 * tailScale / 19682 * v 8
  x1 : v 1 = (183194 - 81 * tailScale) / 72672 * v 8
  x5 : v 5 = (309 * tailScale - 19682) / 478763136 * v 8
  x7 : v 7 = (6485 * tailScale - 14893218) / 17731968 * v 8
  x0 : v 0 = -v 4 -
    (433900101 * tailScale + 247501150) / 1555980192 * v 8

private theorem commonKernel_of_mulVec_eq_zero
    (extra₀ extra₁ : Nat × Fin 4) (q tailScale tailRatio : ℚ)
    (v : Fin 9 → ℚ)
    (h : minor extra₀ extra₁ q tailScale tailRatio *ᵥ v = 0) :
    CommonKernel tailScale v := by
  have hz (i : Fin 9) :
      (minor extra₀ extra₁ q tailScale tailRatio *ᵥ v) i = 0 :=
    congrFun h i
  have h0 := hz 0
  have h1 := hz 1
  have h2 := hz 2
  have h3 := hz 3
  have h4 := hz 4
  have h5 := hz 5
  have h6 := hz 6
  simp [minor, row, column, moment, separator, RunLengthHankel.benchmarkToggle,
    RunLengthHankel.benchmarkDataB, RunLengthHankel.benchmarkDataC,
    Matrix.vecMulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6
  have hx6 : 19682 * v 6 = 27 * tailScale * v 8 := by
    linear_combination 81 * h2 - (1 / 3) * h5
  have hx2 : 19682 * v 2 = -6561 * tailScale * v 8 := by
    linear_combination 19682 * h2 - 243 * hx6
  refine ⟨h1, hx6, hx2, ?_, ?_, ?_, ?_⟩
  · linarith [h0, h2, h3, h4, h5, h6]
  · linarith [h0, h2, h3, h4, h5, h6]
  · linarith [h0, h2, h3, h4, h5, h6]
  · linarith [h0, h2, h3, h4, h5, h6]

private theorem CommonKernel.coordinates {tailScale : ℚ} {v : Fin 9 → ℚ}
    (common : CommonKernel tailScale v) : CommonCoordinates tailScale v := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith [common.x6]
  · linarith [common.x2]
  · linarith [common.x1]
  · linarith [common.x5]
  · linarith [common.x7]
  · linarith [common.x04]

private theorem CommonKernel.vector_eq_zero {tailScale : ℚ} {v : Fin 9 → ℚ}
    (common : CommonKernel tailScale v) (x4 : v 4 = 0) (x8 : v 8 = 0) :
    v = 0 := by
  funext i
  fin_cases i
  · change v 0 = 0
    have equation := common.x04
    rw [x4, x8] at equation
    norm_num at equation
    exact equation
  · change v 1 = 0
    have equation := common.x1
    rw [x8] at equation
    norm_num at equation
    exact equation
  · change v 2 = 0
    have equation := common.x2
    rw [x8] at equation
    norm_num at equation
    exact equation
  · change v 3 = 0
    exact common.x3
  · change v 4 = 0
    exact x4
  · change v 5 = 0
    have equation := common.x5
    rw [x8] at equation
    norm_num at equation
    exact equation
  · change v 6 = 0
    have equation := common.x6
    rw [x8] at equation
    norm_num at equation
    exact equation
  · change v 7 = 0
    have equation := common.x7
    rw [x8] at equation
    norm_num at equation
    exact equation
  · change v 8 = 0
    exact x8

private def primaryPivot (q tailScale tailRatio : ℚ) : ℚ :=
  2704575 * q * tailScale - 1306943846 * q + 1555980192 * tailRatio -
    2616669105204 * tailScale + 5917584210439160

private theorem primaryMinor_mulVec_eq_zero_iff (q tailScale tailRatio : ℚ)
    (tailScale_ne : tailScale ≠ 0) (pivot_ne : primaryPivot q tailScale tailRatio ≠ 0)
    (v : Fin 9 → ℚ) :
    minor (2, 0) (2, 2) q tailScale tailRatio *ᵥ v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have common := commonKernel_of_mulVec_eq_zero (2, 0) (2, 2)
      q tailScale tailRatio v h
    have hz (i : Fin 9) :
        (minor (2, 0) (2, 2) q tailScale tailRatio *ᵥ v) i = 0 :=
      congrFun h i
    have h7 := hz 7
    have h8 := hz 8
    simp [minor, row, column, moment, separator, RunLengthHankel.benchmarkToggle,
      RunLengthHankel.benchmarkDataB, RunLengthHankel.benchmarkDataC,
      Matrix.vecMulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h7 h8
    have coordinates := common.coordinates
    rw [common.x3, coordinates.x6, coordinates.x2, coordinates.x1,
      coordinates.x5, coordinates.x7, coordinates.x0] at h7
    rw [coordinates.x6, coordinates.x2, coordinates.x5, coordinates.x7] at h8
    ring_nf at h7 h8
    have pivot_zero : tailScale * primaryPivot q tailScale tailRatio * v 8 = 0 := by
      unfold primaryPivot
      linear_combination
        19209632 * (81 * tailScale * h7 - (67 * tailScale - 1) * h8)
    have x8_zero : v 8 = 0 := by
      exact (mul_eq_zero.mp pivot_zero).resolve_left (mul_ne_zero tailScale_ne pivot_ne)
    have x4_zero : v 4 = 0 := by
      rw [x8_zero] at h8
      have split : v 4 = 0 ∨ tailScale = 0 := by simpa using h8
      exact split.resolve_right tailScale_ne
    exact common.vector_eq_zero x4_zero x8_zero
  · rintro rfl
    exact Matrix.mulVec_zero _

private theorem zeroTailMinor_mulVec_eq_zero_iff (q tailRatio : ℚ) (v : Fin 9 → ℚ) :
    minor (2, 0) (2, 3) q 0 tailRatio *ᵥ v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have common := commonKernel_of_mulVec_eq_zero (2, 0) (2, 3) q 0 tailRatio v h
    have hz (i : Fin 9) :
        (minor (2, 0) (2, 3) q 0 tailRatio *ᵥ v) i = 0 := congrFun h i
    have h7 := hz 7
    have h8 := hz 8
    simp [minor, row, column, moment, separator, RunLengthHankel.benchmarkToggle,
      RunLengthHankel.benchmarkDataB, RunLengthHankel.benchmarkDataC,
      Matrix.vecMulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h7 h8
    have coordinates := common.coordinates
    rw [coordinates.x0, coordinates.x1, coordinates.x2, common.x3] at h7
    rw [coordinates.x1, common.x3] at h8
    ring_nf at h7 h8
    have x8_zero : v 8 = 0 := by linarith [h8]
    have x4_zero : v 4 = 0 := by linarith [h7, x8_zero]
    exact common.vector_eq_zero x4_zero x8_zero
  · rintro rfl
    exact Matrix.mulVec_zero _

private def tailScaleGap (tailScale : ℚ) : ℚ := 209357 * tailScale - 473489874

private def exceptionalTailScale : ℚ := 473489874 / 209357

private def exceptionalPivot (q tailScale tailRatio : ℚ) : ℚ :=
  2704575 * q * tailRatio * tailScale - 1306943846 * q * tailRatio +
    34686980844 * q * tailScale ^ 2 - 175753754203 * q * tailScale +
    3922366734 * q + 1555980192 * tailRatio ^ 2 -
    2722206888804 * tailRatio * tailScale + 5917584229649768 * tailRatio +
    29071306767 * tailScale ^ 2 + 2634104892889 * tailScale - 5917584477150918

private theorem exceptionalPivot_lt_zero (q tailRatio : ℚ) (q_lt : q < -3 / 2)
    (pivot_zero : primaryPivot q exceptionalTailScale tailRatio = 0) :
    exceptionalPivot q exceptionalTailScale tailRatio < 0 := by
  have tailRatio_eq :
      tailRatio = (4915461113967761 - 62935689575408 * q) / 20359709066034 := by
    norm_num [primaryPivot, exceptionalTailScale] at pivot_zero ⊢
    linarith
  rw [tailRatio_eq]
  unfold exceptionalPivot exceptionalTailScale
  ring_nf
  linarith

private theorem genericScaleMinor_mulVec_eq_zero_iff (q tailScale tailRatio : ℚ)
    (tailScale_ne : tailScale ≠ 0) (gap_ne : tailScaleGap tailScale ≠ 0)
    (v : Fin 9 → ℚ) :
    minor (2, 2) (2, 3) q tailScale tailRatio *ᵥ v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have common := commonKernel_of_mulVec_eq_zero (2, 2) (2, 3)
      q tailScale tailRatio v h
    have hz (i : Fin 9) :
        (minor (2, 2) (2, 3) q tailScale tailRatio *ᵥ v) i = 0 := congrFun h i
    have h7 := hz 7
    have h8 := hz 8
    simp [minor, row, column, moment, separator, RunLengthHankel.benchmarkToggle,
      RunLengthHankel.benchmarkDataB, RunLengthHankel.benchmarkDataC,
      Matrix.vecMulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h7 h8
    have coordinates := common.coordinates
    rw [coordinates.x6, coordinates.x2, coordinates.x5, coordinates.x7] at h7
    rw [common.x3, coordinates.x6, coordinates.x1, coordinates.x5,
      coordinates.x7] at h8
    ring_nf at h7 h8
    have pivot_zero : tailScale * tailScaleGap tailScale * v 8 = 0 := by
      unfold tailScaleGap
      linear_combination (-314912 / 216513) *
        (81 * tailScale * h8 + tailScale * h7)
    have x8_zero : v 8 = 0 := by
      exact (mul_eq_zero.mp pivot_zero).resolve_left (mul_ne_zero tailScale_ne gap_ne)
    have x4_zero : v 4 = 0 := by
      rw [x8_zero] at h7
      have split : tailScale = 0 ∨ v 4 = 0 := by simpa using h7
      exact split.resolve_left tailScale_ne
    exact common.vector_eq_zero x4_zero x8_zero
  · rintro rfl
    exact Matrix.mulVec_zero _

private theorem exceptionalScaleMinor_mulVec_eq_zero_iff (q tailRatio : ℚ)
    (q_lt : q < -3 / 2) (pivot_zero : primaryPivot q exceptionalTailScale tailRatio = 0)
    (v : Fin 9 → ℚ) :
    minor (2, 0) (3, 0) q exceptionalTailScale tailRatio *ᵥ v = 0 ↔ v = 0 := by
  have tailScale_ne : exceptionalTailScale ≠ 0 := by
    norm_num [exceptionalTailScale]
  have pivot_ne : exceptionalPivot q exceptionalTailScale tailRatio ≠ 0 :=
    ne_of_lt (exceptionalPivot_lt_zero q tailRatio q_lt pivot_zero)
  constructor
  · intro h
    have common := commonKernel_of_mulVec_eq_zero (2, 0) (3, 0)
      q exceptionalTailScale tailRatio v h
    have hz (i : Fin 9) :
        (minor (2, 0) (3, 0) q exceptionalTailScale tailRatio *ᵥ v) i = 0 :=
      congrFun h i
    have h7 := hz 7
    have h8 := hz 8
    simp [minor, row, column, moment, separator, RunLengthHankel.benchmarkToggle,
      RunLengthHankel.benchmarkDataB, RunLengthHankel.benchmarkDataC,
      Matrix.vecMulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h7 h8
    have coordinates := common.coordinates
    rw [common.x3, coordinates.x6, coordinates.x2, coordinates.x1,
      coordinates.x5, coordinates.x7, coordinates.x0] at h7 h8
    ring_nf at h7 h8
    have pivot_product_zero :
        exceptionalTailScale * exceptionalPivot q exceptionalTailScale tailRatio * v 8 = 0 := by
      unfold exceptionalPivot
      linear_combination (-1555980192 / 67) *
        ((67 * exceptionalTailScale - 1) * h8 -
          67 * exceptionalTailScale * (tailRatio - 1) * h7)
    have x8_zero : v 8 = 0 := by
      exact (mul_eq_zero.mp pivot_product_zero).resolve_left
        (mul_ne_zero tailScale_ne pivot_ne)
    have x4_zero : v 4 = 0 := by
      rw [x8_zero] at h7
      norm_num [exceptionalTailScale] at h7
      linarith
    exact common.vector_eq_zero x4_zero x8_zero
  · rintro rfl
    exact Matrix.mulVec_zero _

private theorem det_ne_zero_of_mulVec_eq_zero_iff (matrix : Matrix (Fin 9) (Fin 9) ℚ)
    (kernel : ∀ v, matrix *ᵥ v = 0 ↔ v = 0) : matrix.det ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro left right product_eq
  have difference_zero : matrix *ᵥ (left - right) = 0 := by
    rw [Matrix.mulVec_sub, product_eq, sub_self]
  exact sub_eq_zero.mp ((kernel (left - right)).mp difference_zero)

private theorem exists_tiltedGeometricMinor_det_ne_zero
    (q tailScale tailRatio : ℚ) (q_lt : q < -3 / 2) :
    ∃ extra₀ extra₁ : Nat × Fin 4,
      (minor extra₀ extra₁ q tailScale tailRatio).det ≠ 0 := by
  by_cases tailScale_zero : tailScale = 0
  · subst tailScale
    refine ⟨(2, 0), (2, 3), ?_⟩
    exact det_ne_zero_of_mulVec_eq_zero_iff _
      (zeroTailMinor_mulVec_eq_zero_iff q tailRatio)
  · by_cases gap_zero : tailScaleGap tailScale = 0
    · have tailScale_eq : tailScale = exceptionalTailScale := by
        unfold tailScaleGap at gap_zero
        unfold exceptionalTailScale
        linarith
      by_cases pivot_zero : primaryPivot q tailScale tailRatio = 0
      · subst tailScale
        refine ⟨(2, 0), (3, 0), ?_⟩
        exact det_ne_zero_of_mulVec_eq_zero_iff _
          (exceptionalScaleMinor_mulVec_eq_zero_iff q tailRatio q_lt pivot_zero)
      · refine ⟨(2, 0), (2, 2), ?_⟩
        exact det_ne_zero_of_mulVec_eq_zero_iff _
          (primaryMinor_mulVec_eq_zero_iff q tailScale tailRatio tailScale_zero pivot_zero)
    · refine ⟨(2, 2), (2, 3), ?_⟩
      exact det_ne_zero_of_mulVec_eq_zero_iff _
        (genericScaleMinor_mulVec_eq_zero_iff q tailScale tailRatio tailScale_zero gap_zero)

/-- Every exact realization of the benchmark toggle and data roles followed by a geometric
tilted-separator tail has at least nine states throughout the same-zero chamber. -/
theorem nine_le_card_of_tilted_geometric_transfer_moments
    {State : Type*} [Fintype State] [DecidableEq State]
    (transition : Matrix State State ℚ)
    (input : Matrix State (Fin 4) ℚ) (output : Matrix (Fin 4) State ℚ)
    (q tailScale tailRatio : ℚ) (q_lt : q < -3 / 2)
    (moments : ∀ exponent,
      output * transition ^ exponent * input = moment q tailScale tailRatio exponent) :
    9 ≤ Fintype.card State := by
  obtain ⟨extra₀, extra₁, minor_det_ne⟩ :=
    exists_tiltedGeometricMinor_det_ne_zero q tailScale tailRatio q_lt
  have product_eq :
      RunLengthHankel.transferFutureFactor transition output (row extra₀ extra₁) *
          RunLengthHankel.transferPastFactor transition input column =
        minor extra₀ extra₁ q tailScale tailRatio := by
    rw [← RunLengthHankel.transferHankel_factor]
    ext i j
    rw [moments]
    rfl
  have product_det_ne :
      (RunLengthHankel.transferFutureFactor transition output (row extra₀ extra₁) *
        RunLengthHankel.transferPastFactor transition input column).det ≠ 0 := by
    rw [product_eq]
    exact minor_det_ne
  simpa using card_le_of_det_rectangular_product_ne_zero
    (RunLengthHankel.transferFutureFactor transition output (row extra₀ extra₁))
    (RunLengthHankel.transferPastFactor transition input column) product_det_ne

end TiltedGeometricHankel

end MatrixMortality
