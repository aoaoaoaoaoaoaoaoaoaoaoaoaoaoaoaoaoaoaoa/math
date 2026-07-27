import MatrixMortality.CHHNPackingRank
import MatrixMortality.FullMatrixAlgebra
import MatrixMortality.PairedBinary

/-!
# Full algebra of the paired-binary mortality family

The two transposed six-state controls and their canonical rank-one separator generate the full
six-dimensional matrix algebra.  Sparse reachable and observable context matrices reduce
nonsingularity to two integer factors, each congruent to three modulo nine.
-/

namespace MatrixMortality

open scoped Matrix

@[simp] private theorem vecCons_val_five {α : Type*} (head : α) (tail : Fin 5 → α) :
    Matrix.vecCons head tail (5 : Fin 6) = tail 4 := rfl

@[simp] private theorem fin_succ_two_eq_three {n : Nat} :
    Fin.succ (2 : Fin (n + 3)) = (3 : Fin (n + 4)) := by
  apply Fin.ext
  rfl

@[simp] private theorem fin_succ_three_eq_four {n : Nat} :
    Fin.succ (3 : Fin (n + 4)) = (4 : Fin (n + 5)) := by
  apply Fin.ext
  rfl

@[simp] private theorem fin_succ_four_eq_five {n : Nat} :
    Fin.succ (4 : Fin (n + 5)) = (5 : Fin (n + 6)) := by
  apply Fin.ext
  rfl

/-- Column-acting form of the two paired-binary controls. -/
def pairedBinaryAlgebraGenerator (β : Nat) (body : List TagLetter) (bit : Bool) :
    Square (Fin 6) ℚ :=
  (pairedBinaryGenerator ℚ β body bit)ᵀ

/-- Canonical separator column after transposing the row-acting representation. -/
def pairedBinaryAlgebraColumn (β : Nat) : Fin 6 → ℚ :=
  pairedBinaryBoundaryRow ℚ β

/-- Canonical separator row after transposing the row-acting representation. -/
def pairedBinaryAlgebraRow : Fin 6 → ℚ :=
  pairedBinaryBoundaryColumn ℚ

/-- Closed form of the transposed controls. -/
def pairedBinaryAlgebraGeneratorClosed (β : Nat) (body : List TagLetter) :
    Bool → Square (Fin 6) ℚ
  | false =>
      let ρ := (3 : ℚ) ^ β
      let u := (15 * ρ + 1) / 2
      !![1, 0, 0, 25, u, 1;
         0, 0, 0, 27, 0, 3;
         0, 0, 0, 0, 9 * ρ, 0;
         0, 1, 0, 0, 0, 0;
         0, 0, 1, 0, 0, 0;
         0, 0, 0, 0, 0, 0]
  | true =>
      let V := chhnNearyLowerC β body
      let B := chhnNearyLowerCScale β body
      !![1, 0, 0, V, 2, 1;
         0, 0, 0, B, 0, 3;
         0, 0, 0, 0, 3, 0;
         0, 0, 0, 0, 0, 0;
         0, 0, 1, 0, 0, 0;
         0, 1, 0, 0, 0, 0]

/-- Action of the closed `b`-control on a column. -/
theorem pairedBinaryAlgebraGeneratorClosed_false_mulVec
    (β : Nat) (body : List TagLetter) (vector : Fin 6 → ℚ) :
    pairedBinaryAlgebraGeneratorClosed β body false *ᵥ vector =
      ![vector 0 + 25 * vector 3 + (15 * (3 : ℚ) ^ β + 1) / 2 * vector 4 + vector 5,
        27 * vector 3 + 3 * vector 5,
        9 * (3 : ℚ) ^ β * vector 4,
        vector 1,
        vector 2,
        0] := by
  ext coordinate
  fin_cases coordinate <;>
    simp [pairedBinaryAlgebraGeneratorClosed, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_succ]
  all_goals ring

/-- Action of the closed `c`-control on a column. -/
theorem pairedBinaryAlgebraGeneratorClosed_true_mulVec
    (β : Nat) (body : List TagLetter) (vector : Fin 6 → ℚ) :
    pairedBinaryAlgebraGeneratorClosed β body true *ᵥ vector =
      ![vector 0 + chhnNearyLowerC β body * vector 3 + 2 * vector 4 + vector 5,
        chhnNearyLowerCScale β body * vector 3 + 3 * vector 5,
        3 * vector 4,
        0,
        vector 2,
        vector 1] := by
  ext coordinate
  fin_cases coordinate <;>
    simp [pairedBinaryAlgebraGeneratorClosed, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_succ]
  all_goals ring

/-- Action of a row on the closed `b`-control. -/
theorem pairedBinaryAlgebraGeneratorClosed_vecMul_false
    (β : Nat) (body : List TagLetter) (vector : Fin 6 → ℚ) :
    vector ᵥ* pairedBinaryAlgebraGeneratorClosed β body false =
      ![vector 0,
        vector 3,
        vector 4,
        25 * vector 0 + 27 * vector 1,
        (15 * (3 : ℚ) ^ β + 1) / 2 * vector 0 + 9 * (3 : ℚ) ^ β * vector 2,
        vector 0 + 3 * vector 1] := by
  ext coordinate
  fin_cases coordinate <;>
    simp [pairedBinaryAlgebraGeneratorClosed, Matrix.vecMul, Matrix.dotProduct,
      Fin.sum_univ_succ]
  all_goals ring

/-- Action of a row on the closed `c`-control. -/
theorem pairedBinaryAlgebraGeneratorClosed_vecMul_true
    (β : Nat) (body : List TagLetter) (vector : Fin 6 → ℚ) :
    vector ᵥ* pairedBinaryAlgebraGeneratorClosed β body true =
      ![vector 0,
        vector 5,
        vector 4,
        chhnNearyLowerC β body * vector 0 +
          chhnNearyLowerCScale β body * vector 1,
        2 * vector 0 + 3 * vector 2,
        vector 0 + 3 * vector 1] := by
  ext coordinate
  fin_cases coordinate <;>
    simp [pairedBinaryAlgebraGeneratorClosed, Matrix.vecMul, Matrix.dotProduct,
      Fin.sum_univ_succ]
  all_goals ring

/-- Closed form of the separator column. -/
def pairedBinaryAlgebraColumnClosed (β : Nat) : Fin 6 → ℚ :=
  let ρ := (3 : ℚ) ^ β
  ![(5 * ρ - 1) / 2, -1, 3 * ρ, 0, 0, 0]

theorem pairedBinaryAlgebraGenerator_eq_closed (β : Nat) (body : List TagLetter)
    (bit : Bool) :
    pairedBinaryAlgebraGenerator β body bit =
      pairedBinaryAlgebraGeneratorClosed β body bit := by
  have upper_b :
      (ternaryCode (tagCode β .b) : ℚ) = (15 * (3 : ℚ) ^ β + 1) / 2 := by
    simpa [chhnNearyUpperB] using chhnNearyUpperB_eq β
  have upper_b_scale :
      ((3 : ℚ) ^ (tagCode β .b).length) = 9 * (3 : ℚ) ^ β := by
    simpa [chhnNearyUpperBScale] using chhnNearyUpperBScale_eq β
  have upper_c : (ternaryCode (tagCode β .c) : ℚ) = 2 := by
    exact_mod_cast ternaryCode_tagCode_c β
  have upper_c_scale : ((3 : ℚ) ^ (tagCode β .c).length) = 3 := by
    norm_num [tagCode]
  have rule_upper_b :
      (ternaryCode (nearyUpper β (.rule .b)) : ℚ) =
        (15 * (3 : ℚ) ^ β + 1) / 2 := by
    simpa [nearyUpper] using upper_b
  have rule_upper_b_scale :
      ((3 : ℚ) ^ (nearyUpper β (.rule .b)).length) =
        9 * (3 : ℚ) ^ β := by
    simpa [nearyUpper] using upper_b_scale
  have rule_upper_c :
      (ternaryCode (nearyUpper β (.rule .c)) : ℚ) = 2 := by
    exact upper_c
  have rule_upper_c_scale :
      ((3 : ℚ) ^ (nearyUpper β (.rule .c)).length) = 3 := by
    simpa [nearyUpper] using upper_c_scale
  have rule_b_scale :
      ((3 : ℚ) ^ (nearyLower β body (.rule .b)).length) = 27 := by
    norm_num [nearyLower]
  have rule_c :
      (ternaryCode (nearyLower β body (.rule .c)) : ℚ) =
        chhnNearyLowerC β body := rfl
  have rule_c_scale :
      ((3 : ℚ) ^ (nearyLower β body (.rule .c)).length) =
        chhnNearyLowerCScale β body := rfl
  have erase_scale (letter : TagLetter) :
      ((3 : ℚ) ^ (nearyLower β body (.erase letter)).length) = 3 := by
    cases letter <;> norm_num [nearyLower]
  cases bit <;>
    ext row column <;>
    fin_cases row <;> fin_cases column <;>
    simp [pairedBinaryAlgebraGenerator, pairedBinaryAlgebraGeneratorClosed,
      pairedBinaryGenerator, upper_b, upper_b_scale, upper_c, upper_c_scale,
      rule_upper_b, rule_upper_b_scale, rule_upper_c, rule_upper_c_scale,
      rule_b_scale, rule_c, rule_c_scale, erase_scale,
      Matrix.transpose_apply] <;>
    simp only [Matrix.vecHead, Matrix.vecTail]
  all_goals rfl

theorem pairedBinaryAlgebraGenerator_eq_closed_fun (β : Nat) (body : List TagLetter) :
    pairedBinaryAlgebraGenerator β body =
      pairedBinaryAlgebraGeneratorClosed β body := by
  funext bit
  exact pairedBinaryAlgebraGenerator_eq_closed β body bit

theorem pairedBinaryAlgebraColumn_eq_closed (β : Nat) :
    pairedBinaryAlgebraColumn β = pairedBinaryAlgebraColumnClosed β := by
  have marker :
      (ternaryCode (nearyMarker β) : ℚ) = (5 * (3 : ℚ) ^ β - 1) / 2 := by
    simpa [chhnNearyMarkerValue] using chhnNearyMarkerValue_eq β
  ext coordinate
  fin_cases coordinate <;>
    simp [pairedBinaryAlgebraColumn, pairedBinaryAlgebraColumnClosed,
      pairedBinaryBoundaryRow, pairedBinaryRow, sideTerminalColumn, sidePcpMatrix,
      sideTailBasis, marker, chhnNearyMarkerScale_eq,
      Matrix.mulVec, Matrix.dotProduct, Matrix.vecHead, Matrix.vecTail,
      Fin.sum_univ_succ]
  all_goals ring

theorem pairedBinaryAlgebraRow_eq :
    pairedBinaryAlgebraRow = ![1, 0, 0, 0, 0, 0] := by
  rfl

/-- Physical left contexts selecting six reachable columns. -/
def pairedBinaryAlgebraLeftWords : Fin 6 → List Bool :=
  ![[], [false], [true], [false, false], [true, false], [false, false, false]]

/-- Physical right contexts selecting six observable rows. -/
def pairedBinaryAlgebraRightWords : Fin 6 → List Bool :=
  ![[], [false], [true], [false, false], [false, true], [false, false, false]]

/-- Reachable context matrix around the canonical separator column. -/
def pairedBinaryAlgebraReachable (β : Nat) (body : List TagLetter) :
    Square (Fin 6) ℚ :=
  contextColumns (pairedBinaryAlgebraGenerator β body)
    (pairedBinaryAlgebraColumn β) pairedBinaryAlgebraLeftWords

/-- Observable context matrix around the canonical separator row. -/
def pairedBinaryAlgebraObservable (β : Nat) (body : List TagLetter) :
    Square (Fin 6) ℚ :=
  contextRows (pairedBinaryAlgebraGenerator β body)
    pairedBinaryAlgebraRow pairedBinaryAlgebraRightWords

/-- Closed sparse form of the reachable context matrix. -/
def pairedBinaryAlgebraReachableClosed (β : Nat) (body : List TagLetter) :
    Square (Fin 6) ℚ :=
  let ρ := (3 : ℚ) ^ β
  let m := (5 * ρ - 1) / 2
  let u := (15 * ρ + 1) / 2
  let V := chhnNearyLowerC β body
  let B := chhnNearyLowerCScale β body
  !![m, m, m, 3 * ρ * u + m - 25, -V + (17 * ρ - 1) / 2,
       3 * ρ * u + m - 25;
     -1, 0, 0, -27, -B, 0;
     3 * ρ, 0, 0, 27 * ρ ^ 2, 9 * ρ, 0;
     0, -1, 0, 0, 0, -27;
     0, 3 * ρ, 3 * ρ, 0, 0, 27 * ρ ^ 2;
     0, 0, -1, 0, 0, 0]

/-- Closed sparse form of the observable context matrix. -/
def pairedBinaryAlgebraObservableClosed (β : Nat) (body : List TagLetter) :
    Square (Fin 6) ℚ :=
  let ρ := (3 : ℚ) ^ β
  let u := (15 * ρ + 1) / 2
  let V := chhnNearyLowerC β body
  !![1, 0, 0, 0, 0, 0;
     1, 0, 0, 25, u, 1;
     1, 0, 0, V, 2, 1;
     1, 25, u, 25, u, 1;
     1, 1, u, V, 2, 1;
     1, 25, u, 700, (135 * ρ ^ 2 + 24 * ρ + 1) / 2, 76]

/-- The terminal `10` of the rule-`c` lower word fixes its two least significant ternary
digits. -/
theorem chhnNearyLowerC_eq_nine_mul_add_seven (β : Nat) (body : List TagLetter) :
    chhnNearyLowerC β body =
      9 * ternaryCode (true :: tagEncode β body) + 7 := by
  simp [chhnNearyLowerC, nearyLower, ternaryCode_append, ternaryCode_cons,
    ternaryDigit]
  ring

/-- The rule-`c` lower scale contains the same terminal two-digit factor. -/
theorem chhnNearyLowerCScale_eq_nine_mul (β : Nat) (body : List TagLetter) :
    chhnNearyLowerCScale β body =
      9 * (3 : ℚ) ^ (tagEncode β body).length.succ := by
  simp [chhnNearyLowerCScale, nearyLower, pow_add]
  ring
end MatrixMortality
