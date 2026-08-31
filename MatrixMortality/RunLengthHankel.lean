import MatrixMortality.PairedBinaryPrefixTax
import MatrixMortality.LinearRepresentation

/-!
# Run-length transfer Hankel obstruction

A rank-four cut and one arbitrary transition replace parser fibres by the transfer moments
`V Aⁿ U`.  This permits unrestricted cross-path interference inside the ambient state space.
A finite block-Hankel minor nevertheless factors through that space.

For the paired benchmark at deletion width three and body `bb`, consider the run-length moment
sequence whose first three values are nonzero rescalings of the toggle, data-`b`, and data-`c`
roles, and whose later values are the absorbed separator.  One explicit ten-dimensional minor
is injective for every nonzero rescaling.  Hence this exact architecture cannot use nine states.
-/

namespace MatrixMortality

open scoped Matrix

namespace RunLengthHankel

/-- The paired toggle in the benchmark coordinates. -/
def benchmarkToggle : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0;
     0, 1, 0, 0]

/-- The paired rank-one separator after trailing-toggle absorption. -/
def benchmarkSeparator : Matrix (Fin 4) (Fin 4) ℚ :=
  !![67, 0, 0, 0;
     0, 0, 0, 0;
     81, 0, 0, 0;
     -1, 0, 0, 0]

/-- The paired data-`b` role at deletion width three and body `bb`. -/
def benchmarkDataB : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 25, 203, 1;
     0, 0, 0, 0;
     0, 0, 243, 0;
     0, 27, 0, 3]

/-- The paired data-`c` role at deletion width three and body `bb`. -/
def benchmarkDataC : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 1508677, 2, 1;
     0, 0, 0, 0;
     0, 0, 3, 0;
     0, 1594323, 0, 3]

theorem benchmarkToggle_eq_paired : benchmarkToggle = pairedToggleMatrix ℚ := by
  rw [pairedToggleMatrix_eq_explicit]
  rfl

theorem benchmarkDataB_eq_paired :
    benchmarkDataB = pairedDataMatrix ℚ 3 [.b, .b] .b := by
  rw [pairedDataMatrix_eq_explicit]
  norm_num [benchmarkDataB, nearyLower, nearyUpper, tagCode, ternaryCode,
    ternaryDigit, Nat.ofDigits, List.replicate]

theorem benchmarkDataC_eq_paired :
    benchmarkDataC = pairedDataMatrix ℚ 3 [.b, .b] .c := by
  rw [pairedDataMatrix_eq_explicit]
  norm_num [benchmarkDataC, nearyLower, nearyUpper, tagCode, tagEncode, spell,
    ternaryCode, ternaryDigit, Nat.ofDigits, List.replicate]

/-- The consecutive `toggle,data-b,data-c`, then constant-separator moment sequence. -/
def tbcMoment (toggleScale dataBScale dataCScale : ℚ) :
    Nat → Matrix (Fin 4) (Fin 4) ℚ
  | 0 => toggleScale • benchmarkToggle
  | 1 => dataBScale • benchmarkDataB
  | 2 => dataCScale • benchmarkDataC
  | _ => benchmarkSeparator

/-- Selected future-block/output-coordinate rows of the ten-dimensional certificate. -/
def tbcRow : Fin 10 → Nat × Fin 4 :=
  ![(1, 0), (0, 3), (3, 2), (0, 1), (1, 2),
    (1, 3), (0, 2), (2, 3), (2, 0), (0, 0)]

/-- Selected past-block/input-coordinate columns of the ten-dimensional certificate. -/
def tbcColumn : Fin 10 → Nat × Fin 4 :=
  ![(2, 0), (2, 2), (1, 3), (1, 1), (0, 1),
    (0, 3), (0, 2), (1, 0), (2, 3), (2, 1)]

/-- The selected `10 × 10` block-Hankel minor. -/
def tbcMinor (toggleScale dataBScale dataCScale : ℚ) :
    Matrix (Fin 10) (Fin 10) ℚ :=
  fun row column =>
    tbcMoment toggleScale dataBScale dataCScale
      ((tbcRow row).1 + (tbcColumn column).1)
      (tbcRow row).2 (tbcColumn column).2

/-- The expanded selected minor.  Keeping this sparse normal form makes the certificate's
elimination proof independent of determinant normalization. -/
def tbcCertificate (toggleScale dataBScale dataCScale : ℚ) :
    Matrix (Fin 10) (Fin 10) ℚ :=
  !![67, 0, dataCScale, 1508677 * dataCScale, 25 * dataBScale,
      dataBScale, 203 * dataBScale, dataCScale, 0, 0;
     0, 0, 3 * dataBScale, 27 * dataBScale, toggleScale,
      0, 0, 0, 3 * dataCScale, 1594323 * dataCScale;
     81, 0, 0, 0, 0, 0, 0, 81, 0, 0;
     0, 0, 0, 0, 0, toggleScale, 0, 0, 0, 0;
     81, 0, 0, 0, 0, 0, 243 * dataBScale, 0, 0, 0;
     -1, 0, 3 * dataCScale, 1594323 * dataCScale, 27 * dataBScale,
      3 * dataBScale, 0, 0, 0, 0;
     0, 3 * dataCScale, 0, 0, 0, 0, toggleScale, 0, 0, 0;
     -1, 0, 0, 0, 1594323 * dataCScale, 3 * dataCScale, 0, -1, 0, 0;
     67, 0, 0, 0, 1508677 * dataCScale, dataCScale, 2 * dataCScale, 67, 0, 0;
     dataCScale, 2 * dataCScale, dataBScale, 25 * dataBScale, 0,
      0, 0, dataBScale, dataCScale, 1508677 * dataCScale]

theorem tbcMinor_eq_certificate (toggleScale dataBScale dataCScale : ℚ) :
    tbcMinor toggleScale dataBScale dataCScale =
      tbcCertificate toggleScale dataBScale dataCScale := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [tbcMinor, tbcCertificate, tbcMoment, tbcRow, tbcColumn,
      benchmarkToggle, benchmarkSeparator, benchmarkDataB, benchmarkDataC] <;> ring

/-- Future block rows selected from an arbitrary transfer system. -/
def transferFutureFactor
    {R Interface State Row : Type*} [Semiring R]
    [Fintype State] [DecidableEq State]
    (transition : Matrix State State R) (output : Matrix Interface State R)
    (left : Row → Nat × Interface) : Matrix Row State R :=
  fun row state =>
    (output * transition ^ (left row).1) (left row).2 state

/-- Past block columns selected from an arbitrary transfer system. -/
def transferPastFactor
    {R Interface State Column : Type*} [Semiring R]
    [Fintype State] [DecidableEq State]
    (transition : Matrix State State R) (input : Matrix State Interface R)
    (right : Column → Nat × Interface) : Matrix State Column R :=
  fun state column =>
    (transition ^ (right column).1 * input) state (right column).2

/-- Every finite block-Hankel section of the transfer moments `V Aⁿ U` factors through the
ambient state space.  The interface, row selectors, and column selectors are arbitrary. -/
theorem transferHankel_factor
    {R Interface State Row Column : Type*} [Semiring R]
    [Fintype State] [DecidableEq State]
    (transition : Matrix State State R)
    (input : Matrix State Interface R) (output : Matrix Interface State R)
    (left : Row → Nat × Interface) (right : Column → Nat × Interface) :
    (fun row column =>
      (output * transition ^ ((left row).1 + (right column).1) * input)
        (left row).2 (right column).2) =
      transferFutureFactor transition output left *
        transferPastFactor transition input right := by
  ext row column
  change
    (output * transition ^ ((left row).1 + (right column).1) * input)
        (left row).2 (right column).2 =
      ((output * transition ^ (left row).1) *
          (transition ^ (right column).1 * input))
        (left row).2 (right column).2
  rw [pow_add]
  simp only [Matrix.mul_assoc]

/-- An arbitrary transition's selected future factor. -/
def futureFactor {State : Type*} [Fintype State] [DecidableEq State]
    (transition : Matrix State State ℚ) (output : Matrix (Fin 4) State ℚ) :
    Matrix (Fin 10) State ℚ :=
  fun row state =>
    (output * transition ^ (tbcRow row).1) (tbcRow row).2 state

/-- An arbitrary transition's selected past factor. -/
def pastFactor {State : Type*} [Fintype State] [DecidableEq State]
    (transition : Matrix State State ℚ) (input : Matrix State (Fin 4) ℚ) :
    Matrix State (Fin 10) ℚ :=
  fun state column =>
    (transition ^ (tbcColumn column).1 * input) state (tbcColumn column).2

/-- Every selected transfer Hankel minor factors through the ambient state space. -/
theorem transferMinor_factor {State : Type*} [Fintype State] [DecidableEq State]
    (transition : Matrix State State ℚ)
    (input : Matrix State (Fin 4) ℚ) (output : Matrix (Fin 4) State ℚ) :
    (fun row column =>
      (output * transition ^ ((tbcRow row).1 + (tbcColumn column).1) * input)
        (tbcRow row).2 (tbcColumn column).2) =
      futureFactor transition output * pastFactor transition input := by
  exact transferHankel_factor transition input output tbcRow tbcColumn

/-- The explicit benchmark minor has trivial kernel for every nonzero toggle and data-`c`
rescaling.  The data-`b` rescaling is unrestricted; the retained certificate is stronger than
the nonzero-rescaling application needs. -/
theorem tbcMinor_mulVec_eq_zero_iff (toggleScale dataBScale dataCScale : ℚ)
    (toggleScale_ne : toggleScale ≠ 0) (dataCScale_ne : dataCScale ≠ 0)
    (vector : Fin 10 → ℚ) :
    tbcMinor toggleScale dataBScale dataCScale *ᵥ vector = 0 ↔ vector = 0 := by
  constructor
  · intro product_zero
    have row_zero (row : Fin 10) :
        (tbcMinor toggleScale dataBScale dataCScale *ᵥ vector) row = 0 := by
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
    have vector5_zero : vector 5 = 0 :=
      row3.resolve_left toggleScale_ne
    have vector7_eq : vector 7 = -vector 0 := by
      linarith [row2]
    have reduced_row7 : 1594323 * dataCScale * vector 4 = 0 := by
      calc
        1594323 * dataCScale * vector 4 =
            -vector 0 +
              (1594323 * dataCScale * vector 4 +
                (3 * dataCScale * vector 5 + -vector 7)) := by
              rw [vector5_zero, vector7_eq]
              ring
        _ = 0 := row7
    have vector4_zero : vector 4 = 0 := by
      have coefficient_ne : 1594323 * dataCScale ≠ 0 :=
        mul_ne_zero (by norm_num) dataCScale_ne
      exact (mul_eq_zero.mp reduced_row7).resolve_left coefficient_ne
    have reduced_row8 : 2 * dataCScale * vector 6 = 0 := by
      calc
        2 * dataCScale * vector 6 =
            67 * vector 0 +
              (1508677 * dataCScale * vector 4 +
                (dataCScale * vector 5 +
                  (2 * dataCScale * vector 6 + 67 * vector 7))) := by
              rw [vector4_zero, vector5_zero, vector7_eq]
              ring
        _ = 0 := row8
    have vector6_zero : vector 6 = 0 := by
      have coefficient_ne : 2 * dataCScale ≠ 0 :=
        mul_ne_zero (by norm_num) dataCScale_ne
      exact (mul_eq_zero.mp reduced_row8).resolve_left coefficient_ne
    have vector0_zero : vector 0 = 0 := by
      have reduced_row4 : 81 * vector 0 = 0 := by
        calc
          81 * vector 0 = 81 * vector 0 + 243 * dataBScale * vector 6 := by
            rw [vector6_zero]
            ring
          _ = 0 := row4
      exact (mul_eq_zero.mp reduced_row4).resolve_left (by norm_num)
    have vector7_zero : vector 7 = 0 := by
      rw [vector7_eq, vector0_zero]
      norm_num
    have vector1_zero : vector 1 = 0 := by
      have reduced_row6 : 3 * dataCScale * vector 1 = 0 := by
        calc
          3 * dataCScale * vector 1 =
              3 * dataCScale * vector 1 + toggleScale * vector 6 := by
                rw [vector6_zero]
                ring
          _ = 0 := row6
      have coefficient_ne : 3 * dataCScale ≠ 0 :=
        mul_ne_zero (by norm_num) dataCScale_ne
      exact (mul_eq_zero.mp reduced_row6).resolve_left coefficient_ne
    have reduced_row0 :
        dataCScale * vector 2 + 1508677 * dataCScale * vector 3 = 0 := by
      calc
        dataCScale * vector 2 + 1508677 * dataCScale * vector 3 =
            67 * vector 0 +
              (dataCScale * vector 2 +
                (1508677 * dataCScale * vector 3 +
                  (25 * dataBScale * vector 4 +
                    (dataBScale * vector 5 +
                      (203 * dataBScale * vector 6 + dataCScale * vector 7))))) := by
              rw [vector0_zero, vector4_zero, vector5_zero, vector6_zero, vector7_zero]
              ring
        _ = 0 := row0
    have reduced_row5 :
        3 * dataCScale * vector 2 + 1594323 * dataCScale * vector 3 = 0 := by
      calc
        3 * dataCScale * vector 2 + 1594323 * dataCScale * vector 3 =
            -vector 0 +
              (3 * dataCScale * vector 2 +
                (1594323 * dataCScale * vector 3 +
                  (27 * dataBScale * vector 4 + 3 * dataBScale * vector 5))) := by
              rw [vector0_zero, vector4_zero, vector5_zero]
              ring
        _ = 0 := row5
    have vector3_zero : vector 3 = 0 := by
      have eliminated : 2931708 * dataCScale * vector 3 = 0 := by
        linear_combination 3 * reduced_row0 - reduced_row5
      have coefficient_ne : 2931708 * dataCScale ≠ 0 :=
        mul_ne_zero (by norm_num) dataCScale_ne
      exact (mul_eq_zero.mp eliminated).resolve_left coefficient_ne
    have vector2_zero : vector 2 = 0 := by
      have eliminated : dataCScale * vector 2 = 0 := by
        calc
          dataCScale * vector 2 =
              dataCScale * vector 2 + 1508677 * dataCScale * vector 3 := by
                rw [vector3_zero]
                ring
          _ = 0 := reduced_row0
      exact (mul_eq_zero.mp eliminated).resolve_left dataCScale_ne
    have reduced_row1 :
        3 * dataCScale * vector 8 + 1594323 * dataCScale * vector 9 = 0 := by
      calc
        3 * dataCScale * vector 8 + 1594323 * dataCScale * vector 9 =
            3 * dataBScale * vector 2 +
              (27 * dataBScale * vector 3 +
                (toggleScale * vector 4 +
                  (3 * dataCScale * vector 8 + 1594323 * dataCScale * vector 9))) := by
              rw [vector2_zero, vector3_zero, vector4_zero]
              ring
        _ = 0 := row1
    have reduced_row9 :
        dataCScale * vector 8 + 1508677 * dataCScale * vector 9 = 0 := by
      calc
        dataCScale * vector 8 + 1508677 * dataCScale * vector 9 =
            dataCScale * vector 0 +
              (2 * dataCScale * vector 1 +
                (dataBScale * vector 2 +
                  (25 * dataBScale * vector 3 +
                    (dataBScale * vector 7 +
                      (dataCScale * vector 8 + 1508677 * dataCScale * vector 9))))) := by
              rw [vector0_zero, vector1_zero, vector2_zero, vector3_zero, vector7_zero]
              ring
        _ = 0 := row9
    have vector9_zero : vector 9 = 0 := by
      have eliminated : 2931708 * dataCScale * vector 9 = 0 := by
        linear_combination 3 * reduced_row9 - reduced_row1
      have coefficient_ne : 2931708 * dataCScale ≠ 0 :=
        mul_ne_zero (by norm_num) dataCScale_ne
      exact (mul_eq_zero.mp eliminated).resolve_left coefficient_ne
    have vector8_zero : vector 8 = 0 := by
      have eliminated : dataCScale * vector 8 = 0 := by
        calc
          dataCScale * vector 8 =
              dataCScale * vector 8 + 1508677 * dataCScale * vector 9 := by
                rw [vector9_zero]
                ring
          _ = 0 := reduced_row9
      exact (mul_eq_zero.mp eliminated).resolve_left dataCScale_ne
    funext index
    fin_cases index <;> assumption
  · rintro rfl
    exact Matrix.mulVec_zero _

/-- The selected benchmark minor is nonsingular. -/
theorem tbcMinor_det_ne_zero (toggleScale dataBScale dataCScale : ℚ)
    (toggleScale_ne : toggleScale ≠ 0) (dataCScale_ne : dataCScale ≠ 0) :
    (tbcMinor toggleScale dataBScale dataCScale).det ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro left right product_eq
  have difference_zero :
      tbcMinor toggleScale dataBScale dataCScale *ᵥ (left - right) = 0 := by
    rw [Matrix.mulVec_sub, product_eq, sub_self]
  have vectors_difference_zero :=
    (tbcMinor_mulVec_eq_zero_iff toggleScale dataBScale dataCScale
      toggleScale_ne dataCScale_ne (left - right)).mp difference_zero
  exact sub_eq_zero.mp vectors_difference_zero

/-- Exact consecutive transfer moments `T, D_b, D_c, P′, P′, ...` require at least ten ambient
states.  No factorial, direct-sum, common-image, or deterministic-parser hypothesis is used. -/
theorem ten_le_card_of_tbc_transfer_moments
    {State : Type*} [Fintype State] [DecidableEq State]
    (transition : Matrix State State ℚ)
    (input : Matrix State (Fin 4) ℚ) (output : Matrix (Fin 4) State ℚ)
    (toggleScale dataBScale dataCScale : ℚ)
    (toggleScale_ne : toggleScale ≠ 0) (dataCScale_ne : dataCScale ≠ 0)
    (moments : ∀ exponent,
      output * transition ^ exponent * input =
        tbcMoment toggleScale dataBScale dataCScale exponent) :
    10 ≤ Fintype.card State := by
  have product_eq :
      futureFactor transition output * pastFactor transition input =
        tbcMinor toggleScale dataBScale dataCScale := by
    rw [← transferMinor_factor]
    ext row column
    rw [moments]
    rfl
  have product_det_ne_zero :
      (futureFactor transition output * pastFactor transition input).det ≠ 0 := by
    rw [product_eq]
    exact tbcMinor_det_ne_zero toggleScale dataBScale dataCScale
      toggleScale_ne dataCScale_ne
  simpa using
    card_le_of_det_rectangular_product_ne_zero
      (futureFactor transition output) (pastFactor transition input)
      product_det_ne_zero

end RunLengthHankel

end MatrixMortality
