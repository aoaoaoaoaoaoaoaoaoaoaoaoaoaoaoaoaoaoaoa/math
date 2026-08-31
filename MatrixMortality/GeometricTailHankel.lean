import MatrixMortality.MovingTailHankel

/-!
# Geometric separator-tail obstruction

The consecutive transfer-moment obstruction survives when the absorbed separator tail is
multiplied by successive powers of any nonzero scalar. An explicit ten-dimensional Hankel
minor remains nonsingular, closing the one-state moving-tail seam left by the general
moving-tail dimension tax.
-/

namespace MatrixMortality

open scoped Matrix

namespace GeometricTailHankel

/-- Consecutive toggle and data roles followed by a nonzero geometric separator tail. -/
def tbcMoment
    (toggleScale dataBScale dataCScale tailScale : ℚ) :
    Nat → Matrix (Fin 4) (Fin 4) ℚ
  | 0 => toggleScale • RunLengthHankel.benchmarkToggle
  | 1 => dataBScale • RunLengthHankel.benchmarkDataB
  | 2 => dataCScale • RunLengthHankel.benchmarkDataC
  | offset + 3 => tailScale ^ (offset + 1) • RunLengthHankel.benchmarkSeparator

/-- Selected block rows of the geometric-tail certificate. -/
def tbcRow : Fin 10 → Nat × Fin 4 :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (1, 0),
    (1, 2), (1, 3), (2, 0), (2, 3), (3, 2)]

/-- Selected block columns of the geometric-tail certificate. -/
def tbcColumn : Fin 10 → Nat × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 0), (1, 1),
    (1, 3), (2, 0), (2, 1), (2, 2), (2, 3)]

/-- The selected geometric-tail block-Hankel minor. -/
def tbcMinor
    (toggleScale dataBScale dataCScale tailScale : ℚ) :
    Matrix (Fin 10) (Fin 10) ℚ :=
  fun row column =>
    tbcMoment toggleScale dataBScale dataCScale tailScale
      ((tbcRow row).1 + (tbcColumn column).1)
      (tbcRow row).2 (tbcColumn column).2

/-- Sparse normal form of the selected geometric-tail minor. -/
def tbcCertificate
    (toggleScale dataBScale dataCScale tailScale : ℚ) :
    Matrix (Fin 10) (Fin 10) ℚ :=
  !![0, 0, 0, dataBScale, 25 * dataBScale, dataBScale,
      dataCScale, 1508677 * dataCScale, 2 * dataCScale, dataCScale;
     0, 0, toggleScale, 0, 0, 0, 0, 0, 0, 0;
     0, toggleScale, 0, 0, 0, 0, 0, 0, 3 * dataCScale, 0;
     toggleScale, 0, 0, 0, 27 * dataBScale, 3 * dataBScale,
      0, 1594323 * dataCScale, 0, 3 * dataCScale;
     25 * dataBScale, 203 * dataBScale, dataBScale, dataCScale,
      1508677 * dataCScale, dataCScale, 67 * tailScale, 0, 0, 0;
     0, 243 * dataBScale, 0, 0, 0, 0, 81 * tailScale, 0, 0, 0;
     27 * dataBScale, 0, 3 * dataBScale, 0,
      1594323 * dataCScale, 3 * dataCScale, -tailScale, 0, 0, 0;
     1508677 * dataCScale, 2 * dataCScale, dataCScale, 67 * tailScale,
      0, 0, 67 * tailScale ^ 2, 0, 0, 0;
     1594323 * dataCScale, 0, 3 * dataCScale, -tailScale,
      0, 0, -tailScale ^ 2, 0, 0, 0;
     0, 0, 0, 81 * tailScale ^ 2, 0, 0,
      81 * tailScale ^ 3, 0, 0, 0]

theorem tbcMinor_eq_certificate
    (toggleScale dataBScale dataCScale tailScale : ℚ) :
    tbcMinor toggleScale dataBScale dataCScale tailScale =
      tbcCertificate toggleScale dataBScale dataCScale tailScale := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [tbcMinor, tbcCertificate, tbcMoment, tbcRow, tbcColumn,
      RunLengthHankel.benchmarkToggle, RunLengthHankel.benchmarkSeparator,
      RunLengthHankel.benchmarkDataB, RunLengthHankel.benchmarkDataC] <;> ring

/-- The geometric-tail certificate has trivial kernel whenever the toggle, data-`c`, and tail
scales are nonzero. The data-`b` scale remains unrestricted. -/
theorem tbcMinor_mulVec_eq_zero_iff
    (toggleScale dataBScale dataCScale tailScale : ℚ)
    (toggleScale_ne_zero : toggleScale ≠ 0)
    (dataCScale_ne_zero : dataCScale ≠ 0)
    (tailScale_ne_zero : tailScale ≠ 0)
    (vector : Fin 10 → ℚ) :
    tbcMinor toggleScale dataBScale dataCScale tailScale *ᵥ vector = 0 ↔
      vector = 0 := by
  constructor
  · intro product_zero
    have row_zero (row : Fin 10) :
        (tbcMinor toggleScale dataBScale dataCScale tailScale *ᵥ vector) row = 0 := by
      exact congrFun product_zero row
    have row0 := row_zero 0
    have row1 := row_zero 1
    have row2 := row_zero 2
    have row3 := row_zero 3
    have row4 := row_zero 4
    have row5 := row_zero 5
    have row6 := row_zero 6
    have row7 := row_zero 7
    have row8 := row_zero 8
    have row9 := row_zero 9
    rw [tbcMinor_eq_certificate] at row0 row1 row2 row3 row4 row5 row6 row7 row8 row9
    simp [tbcCertificate, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      at row0 row1 row2 row3 row4 row5 row6 row7 row8 row9
    have vector2_zero : vector 2 = 0 :=
      row1.resolve_left toggleScale_ne_zero
    have vector3_eq : vector 3 = -tailScale * vector 6 := by
      have reduced_row9 :
          81 * tailScale ^ 2 * (vector 3 + tailScale * vector 6) = 0 := by
        calc
          81 * tailScale ^ 2 * (vector 3 + tailScale * vector 6) =
              81 * tailScale ^ 2 * vector 3 +
                81 * tailScale ^ 3 * vector 6 := by ring
          _ = 0 := row9
      have coefficient_ne : 81 * tailScale ^ 2 ≠ 0 :=
        mul_ne_zero (by norm_num) (pow_ne_zero 2 tailScale_ne_zero)
      have sum_zero : vector 3 + tailScale * vector 6 = 0 :=
        (mul_eq_zero.mp reduced_row9).resolve_left coefficient_ne
      linarith
    have vector0_zero : vector 0 = 0 := by
      have reduced_row8 : 1594323 * dataCScale * vector 0 = 0 := by
        calc
          1594323 * dataCScale * vector 0 =
              1594323 * dataCScale * vector 0 +
                (3 * dataCScale * vector 2 +
                  (-(tailScale * vector 3) + -(tailScale ^ 2 * vector 6))) := by
                rw [vector2_zero, vector3_eq]
                ring
          _ = 0 := row8
      have coefficient_ne : 1594323 * dataCScale ≠ 0 :=
        mul_ne_zero (by norm_num) dataCScale_ne_zero
      exact (mul_eq_zero.mp reduced_row8).resolve_left coefficient_ne
    have vector1_zero : vector 1 = 0 := by
      have reduced_row7 : 2 * dataCScale * vector 1 = 0 := by
        calc
          2 * dataCScale * vector 1 =
              1508677 * dataCScale * vector 0 +
                (2 * dataCScale * vector 1 +
                  (dataCScale * vector 2 +
                    (67 * tailScale * vector 3 +
                      67 * tailScale ^ 2 * vector 6))) := by
                rw [vector0_zero, vector2_zero, vector3_eq]
                ring
          _ = 0 := row7
      have coefficient_ne : 2 * dataCScale ≠ 0 :=
        mul_ne_zero (by norm_num) dataCScale_ne_zero
      exact (mul_eq_zero.mp reduced_row7).resolve_left coefficient_ne
    have vector8_zero : vector 8 = 0 := by
      have reduced_row2 : 3 * dataCScale * vector 8 = 0 := by
        calc
          3 * dataCScale * vector 8 =
              toggleScale * vector 1 + 3 * dataCScale * vector 8 := by
                rw [vector1_zero]
                ring
          _ = 0 := row2
      have coefficient_ne : 3 * dataCScale ≠ 0 :=
        mul_ne_zero (by norm_num) dataCScale_ne_zero
      exact (mul_eq_zero.mp reduced_row2).resolve_left coefficient_ne
    have vector6_zero : vector 6 = 0 := by
      have reduced_row5 : 81 * tailScale * vector 6 = 0 := by
        calc
          81 * tailScale * vector 6 =
              243 * dataBScale * vector 1 + 81 * tailScale * vector 6 := by
                rw [vector1_zero]
                ring
          _ = 0 := row5
      have coefficient_ne : 81 * tailScale ≠ 0 :=
        mul_ne_zero (by norm_num) tailScale_ne_zero
      exact (mul_eq_zero.mp reduced_row5).resolve_left coefficient_ne
    have vector3_zero : vector 3 = 0 := by
      rw [vector3_eq, vector6_zero]
      ring
    have reduced_row4 :
        1508677 * dataCScale * vector 4 + dataCScale * vector 5 = 0 := by
      calc
        1508677 * dataCScale * vector 4 + dataCScale * vector 5 =
            25 * dataBScale * vector 0 +
              (203 * dataBScale * vector 1 +
                (dataBScale * vector 2 +
                  (dataCScale * vector 3 +
                    (1508677 * dataCScale * vector 4 +
                      (dataCScale * vector 5 + 67 * tailScale * vector 6))))) := by
              rw [vector0_zero, vector1_zero, vector2_zero, vector3_zero, vector6_zero]
              ring
        _ = 0 := row4
    have reduced_row6 :
        1594323 * dataCScale * vector 4 + 3 * dataCScale * vector 5 = 0 := by
      calc
        1594323 * dataCScale * vector 4 + 3 * dataCScale * vector 5 =
            27 * dataBScale * vector 0 +
              (3 * dataBScale * vector 2 +
                (1594323 * dataCScale * vector 4 +
                  (3 * dataCScale * vector 5 + -(tailScale * vector 6)))) := by
              rw [vector0_zero, vector2_zero, vector6_zero]
              ring
        _ = 0 := row6
    have vector4_zero : vector 4 = 0 := by
      have eliminated : 2931708 * dataCScale * vector 4 = 0 := by
        linear_combination 3 * reduced_row4 - reduced_row6
      have coefficient_ne : 2931708 * dataCScale ≠ 0 :=
        mul_ne_zero (by norm_num) dataCScale_ne_zero
      exact (mul_eq_zero.mp eliminated).resolve_left coefficient_ne
    have vector5_zero : vector 5 = 0 := by
      have eliminated : dataCScale * vector 5 = 0 := by
        calc
          dataCScale * vector 5 =
              1508677 * dataCScale * vector 4 + dataCScale * vector 5 := by
                rw [vector4_zero]
                ring
          _ = 0 := reduced_row4
      exact (mul_eq_zero.mp eliminated).resolve_left dataCScale_ne_zero
    have reduced_row0 :
        1508677 * dataCScale * vector 7 + dataCScale * vector 9 = 0 := by
      calc
        1508677 * dataCScale * vector 7 + dataCScale * vector 9 =
            dataBScale * vector 3 +
              (25 * dataBScale * vector 4 +
                (dataBScale * vector 5 +
                  (dataCScale * vector 6 +
                    (1508677 * dataCScale * vector 7 +
                      (2 * dataCScale * vector 8 + dataCScale * vector 9))))) := by
              rw [vector3_zero, vector4_zero, vector5_zero, vector6_zero, vector8_zero]
              ring
        _ = 0 := row0
    have reduced_row3 :
        1594323 * dataCScale * vector 7 + 3 * dataCScale * vector 9 = 0 := by
      calc
        1594323 * dataCScale * vector 7 + 3 * dataCScale * vector 9 =
            toggleScale * vector 0 +
              (27 * dataBScale * vector 4 +
                (3 * dataBScale * vector 5 +
                  (1594323 * dataCScale * vector 7 + 3 * dataCScale * vector 9))) := by
              rw [vector0_zero, vector4_zero, vector5_zero]
              ring
        _ = 0 := row3
    have vector7_zero : vector 7 = 0 := by
      have eliminated : 2931708 * dataCScale * vector 7 = 0 := by
        linear_combination 3 * reduced_row0 - reduced_row3
      have coefficient_ne : 2931708 * dataCScale ≠ 0 :=
        mul_ne_zero (by norm_num) dataCScale_ne_zero
      exact (mul_eq_zero.mp eliminated).resolve_left coefficient_ne
    have vector9_zero : vector 9 = 0 := by
      have eliminated : dataCScale * vector 9 = 0 := by
        calc
          dataCScale * vector 9 =
              1508677 * dataCScale * vector 7 + dataCScale * vector 9 := by
                rw [vector7_zero]
                ring
          _ = 0 := reduced_row0
      exact (mul_eq_zero.mp eliminated).resolve_left dataCScale_ne_zero
    funext index
    fin_cases index <;> assumption
  · rintro rfl
    exact Matrix.mulVec_zero _

/-- The selected geometric-tail minor is nonsingular. -/
theorem tbcMinor_det_ne_zero
    (toggleScale dataBScale dataCScale tailScale : ℚ)
    (toggleScale_ne_zero : toggleScale ≠ 0)
    (dataCScale_ne_zero : dataCScale ≠ 0)
    (tailScale_ne_zero : tailScale ≠ 0) :
    (tbcMinor toggleScale dataBScale dataCScale tailScale).det ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro left right product_eq
  have difference_zero :
      tbcMinor toggleScale dataBScale dataCScale tailScale *ᵥ (left - right) = 0 := by
    rw [Matrix.mulVec_sub, product_eq, sub_self]
  have vectors_difference_zero :=
    (tbcMinor_mulVec_eq_zero_iff toggleScale dataBScale dataCScale tailScale
      toggleScale_ne_zero dataCScale_ne_zero tailScale_ne_zero (left - right)).mp
      difference_zero
  exact sub_eq_zero.mp vectors_difference_zero

/-- Exact consecutive moments `T,D_b,D_c` followed by a nonzero geometric separator tail need
at least ten ambient states. This is the consecutive moving-tail seam not covered by the late
exception theorem. -/
theorem ten_le_card_of_tbc_geometric_transfer_moments
    {State : Type*} [Fintype State] [DecidableEq State]
    (transition : Matrix State State ℚ)
    (input : Matrix State (Fin 4) ℚ) (output : Matrix (Fin 4) State ℚ)
    (toggleScale dataBScale dataCScale tailScale : ℚ)
    (toggleScale_ne_zero : toggleScale ≠ 0)
    (dataCScale_ne_zero : dataCScale ≠ 0)
    (tailScale_ne_zero : tailScale ≠ 0)
    (moments : ∀ exponent,
      output * transition ^ exponent * input =
        tbcMoment toggleScale dataBScale dataCScale tailScale exponent) :
    10 ≤ Fintype.card State := by
  have product_eq :
      RunLengthHankel.transferFutureFactor transition output tbcRow *
          RunLengthHankel.transferPastFactor transition input tbcColumn =
        tbcMinor toggleScale dataBScale dataCScale tailScale := by
    rw [← RunLengthHankel.transferHankel_factor]
    ext row column
    rw [moments]
    rfl
  have product_det_ne_zero :
      (RunLengthHankel.transferFutureFactor transition output tbcRow *
        RunLengthHankel.transferPastFactor transition input tbcColumn).det ≠ 0 := by
    rw [product_eq]
    exact tbcMinor_det_ne_zero toggleScale dataBScale dataCScale tailScale
      toggleScale_ne_zero dataCScale_ne_zero tailScale_ne_zero
  simpa using
    card_le_of_det_rectangular_product_ne_zero
      (RunLengthHankel.transferFutureFactor transition output tbcRow)
      (RunLengthHankel.transferPastFactor transition input tbcColumn)
      product_det_ne_zero

end GeometricTailHankel

end MatrixMortality
