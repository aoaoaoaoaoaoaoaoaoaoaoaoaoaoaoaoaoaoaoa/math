import MatrixMortality.PrefixAlgebraContexts

/-!
# Nonsingularity of the ten-state prefix contexts

The adapted reachable matrix has a `3+3+3+1` filtration.  Its two large polynomial factors
are nonzero for the source family for the elementary reasons `P(ρ) ≡ 8 (mod 9)` and
`Q(ρ,x) ≡ 3 (mod 9)`.  The observable matrix repeats one nonsingular three-dimensional
block and ends with one pivot.
-/

namespace MatrixMortality

open scoped Matrix
open PrefixAlgebra.Certificate

attribute [local simp]
  vecCons_val_three vecCons_val_four vecCons_val_five vecCons_val_six
  vecCons_val_seven vecCons_val_eight vecCons_val_nine
  fin_succ_two_eq_three fin_succ_three_eq_four fin_succ_four_eq_five
  fin_succ_five_eq_six fin_succ_six_eq_seven fin_succ_seven_eq_eight
  fin_succ_eight_eq_nine

/-- The body-independent polynomial controlling the middle reachable block. -/
def prefixAlgebraReachabilityPolynomial (ρ : ℚ) : ℚ :=
  158203125 * ρ ^ 11 -
  158203125 * ρ ^ 10 +
  59062500 * ρ ^ 9 -
  8812500 * ρ ^ 8 -
  39071250 * ρ ^ 7 +
  30457250 * ρ ^ 6 -
  9526500 * ρ ^ 5 +
  4428948 * ρ ^ 4 -
  664283 * ρ ^ 3 +
  40587 * ρ ^ 2 -
  1032 * ρ +
  8

/-- The body-dependent polynomial controlling the last reachable three-block. -/
def prefixAlgebraBodyPolynomial (ρ x : ℚ) : ℚ :=
  46875 * ρ ^ 6 -
  56250 * ρ ^ 5 +
  28125 * ρ ^ 4 -
  18000 * ρ ^ 3 * x -
  457500 * ρ ^ 3 +
  10800 * ρ ^ 2 * x +
  271125 * ρ ^ 2 -
  2160 * ρ * x -
  54090 * ρ +
  512 * x ^ 3 +
  39168 * x ^ 2 +
  998928 * x +
  8493267

private theorem nine_mul_integer_add_three_ne_zero (integer : ℤ) :
    (9 * (integer : ℚ) + 3) ≠ 0 := by
  intro equal_zero
  have integer_zero : 9 * integer + 3 = 0 := by
    exact_mod_cast equal_zero
  omega

private theorem nine_mul_integer_add_eight_ne_zero (integer : ℤ) :
    (9 * (integer : ℚ) + 8) ≠ 0 := by
  intro equal_zero
  have integer_zero : 9 * integer + 8 = 0 := by
    exact_mod_cast equal_zero
  omega

/-- The lower-code displacement is a multiple of nine. -/
theorem prefixAlgebraLowerGap_eq_nine_mul (β : Nat) (body : List TagLetter) :
    prefixAlgebraLowerGap β body =
      9 * ((ternaryCode (true :: tagEncode β body) : ℚ) - 2) := by
  rw [prefixAlgebraLowerGap, chhnNearyLowerC_eq_nine_mul_add_seven]
  ring

theorem prefixAlgebraReachabilityPolynomial_ne_zero
    (β : Nat) (three_le : 3 ≤ β) :
    prefixAlgebraReachabilityPolynomial ((3 : ℚ) ^ β) ≠ 0 := by
  obtain ⟨offset, β_eq⟩ := Nat.exists_eq_add_of_le three_le
  subst β
  let ninth : ℤ := 3 * 3 ^ offset
  let ρ : ℤ := 9 * ninth
  let integer : ℤ :=
    ninth * (
      158203125 * ρ ^ 10 -
      158203125 * ρ ^ 9 +
      59062500 * ρ ^ 8 -
      8812500 * ρ ^ 7 -
      39071250 * ρ ^ 6 +
      30457250 * ρ ^ 5 -
      9526500 * ρ ^ 4 +
      4428948 * ρ ^ 3 -
      664283 * ρ ^ 2 +
      40587 * ρ -
      1032)
  have polynomial_eq :
      prefixAlgebraReachabilityPolynomial ((3 : ℚ) ^ (3 + offset)) =
        9 * (integer : ℚ) + 8 := by
    simp [prefixAlgebraReachabilityPolynomial, pow_add, ninth, ρ, integer]
    ring
  rw [polynomial_eq]
  exact nine_mul_integer_add_eight_ne_zero integer

theorem prefixAlgebraBodyPolynomial_ne_zero
    (β : Nat) (body : List TagLetter) (three_le : 3 ≤ β) :
    prefixAlgebraBodyPolynomial ((3 : ℚ) ^ β)
        (prefixAlgebraLowerGap β body) ≠ 0 := by
  obtain ⟨offset, β_eq⟩ := Nat.exists_eq_add_of_le three_le
  subst β
  let ninth : ℤ := 3 * 3 ^ offset
  let ρ : ℤ := 9 * ninth
  let digitGap : ℤ :=
    (ternaryCode (true :: tagEncode (3 + offset) body) : ℤ) - 2
  let x : ℤ := 9 * digitGap
  let integer : ℤ :=
    ninth * (
      46875 * ρ ^ 5 -
      56250 * ρ ^ 4 +
      28125 * ρ ^ 3 -
      18000 * ρ ^ 2 * x -
      457500 * ρ ^ 2 +
      10800 * ρ * x +
      271125 * ρ -
      2160 * x -
      54090) +
    digitGap * (512 * x ^ 2 + 39168 * x + 998928) +
    943696
  have polynomial_eq :
      prefixAlgebraBodyPolynomial ((3 : ℚ) ^ (3 + offset))
          (prefixAlgebraLowerGap (3 + offset) body) =
        9 * (integer : ℚ) + 3 := by
    rw [prefixAlgebraLowerGap_eq_nine_mul]
    simp [prefixAlgebraBodyPolynomial, pow_add, ninth, ρ, digitGap, x, integer]
    ring
  rw [polynomial_eq]
  exact nine_mul_integer_add_three_ne_zero integer

/-- First three-dimensional diagonal block of the adapted reachable matrix. -/
def prefixAlgebraReachableBlockA (β : Nat) : Square (Fin 3) ℚ :=
  let ρ := (3 : ℚ) ^ β
  let m := (5 * ρ - 1) / 2
  !![m ^ 2, 1, m;
     m, m ^ 2, 1;
     1, m, m ^ 2]

/-- Middle three-dimensional diagonal block of the adapted reachable matrix. -/
def prefixAlgebraReachableBlockC (β : Nat) : Square (Fin 3) ℚ :=
  let ρ := (3 : ℚ) ^ β
  let m := (5 * ρ - 1) / 2
  let u := (15 * ρ + 1) / 2
  let c := 3 * (17 * ρ - 1) / 2
  !![m ^ 2 * u, c, m * c;
     m * c, 9 * ρ * m ^ 2 * u, 9 * ρ * c;
     c, m * c, 9 * ρ * m ^ 2 * u]

/-- Last three-dimensional diagonal block of the adapted reachable matrix. -/
def prefixAlgebraReachableBlockB
    (β : Nat) (body : List TagLetter) : Square (Fin 3) ℚ :=
  let ρ := (3 : ℚ) ^ β
  let m := (5 * ρ - 1) / 2
  let x := prefixAlgebraLowerGap β body
  let factor := 3 - 9 * ρ
  !![factor * m ^ 2, factor * (2 * x + 51), factor * 3 * m;
     factor * 3 * m, 3 * factor * m ^ 2, 3 * factor * (2 * x + 51);
     factor * (2 * x + 51), factor * 3 * m, 3 * factor * m ^ 2]

/-- Repeated three-dimensional observable block. -/
def prefixAlgebraObservableBlock (β : Nat) : Square (Fin 3) ℚ :=
  let ρ := (3 : ℚ) ^ β
  let m := (5 * ρ - 1) / 2
  !![m, -1, 3 * ρ;
     (45 * ρ ^ 2 + 8 * ρ - 51) / 2, -27, 27 * ρ ^ 2;
     (17 * ρ - 3) / 2, -3, 9 * ρ]

theorem prefixAlgebraReachableBlockA_det (β : Nat) :
    (prefixAlgebraReachableBlockA β).det =
      ((5 * (3 : ℚ) ^ β - 3) ^ 2 *
        (25 * ((3 : ℚ) ^ β) ^ 2 + 3) ^ 2) / 64 := by
  rw [Matrix.det_fin_three]
  simp [prefixAlgebraReachableBlockA]
  ring

theorem prefixAlgebraReachableBlockC_det (β : Nat) :
    (prefixAlgebraReachableBlockC β).det =
      27 * prefixAlgebraReachabilityPolynomial ((3 : ℚ) ^ β) / 512 := by
  rw [Matrix.det_fin_three]
  simp [prefixAlgebraReachableBlockC, prefixAlgebraReachabilityPolynomial]
  ring

theorem prefixAlgebraReachableBlockB_det (β : Nat) (body : List TagLetter) :
    (prefixAlgebraReachableBlockB β body).det =
      -81 * (3 * (3 : ℚ) ^ β - 1) ^ 3 *
        prefixAlgebraBodyPolynomial ((3 : ℚ) ^ β)
          (prefixAlgebraLowerGap β body) / 64 := by
  rw [Matrix.det_fin_three]
  simp [prefixAlgebraReachableBlockB, prefixAlgebraBodyPolynomial]
  ring

theorem prefixAlgebraObservableBlock_det (β : Nat) :
    (prefixAlgebraObservableBlock β).det =
      -27 * ((3 : ℚ) ^ β) ^ 2 * ((3 : ℚ) ^ β - 3) := by
  rw [Matrix.det_fin_three]
  simp [prefixAlgebraObservableBlock]
  ring

private theorem prefixAlgebraReachableBlockA_isUnit
    (β : Nat) (three_le : 3 ≤ β) :
    IsUnit (prefixAlgebraReachableBlockA β) := by
  rw [Matrix.isUnit_iff_isUnit_det, prefixAlgebraReachableBlockA_det]
  apply isUnit_iff_ne_zero.mpr
  have ρ_large_nat : 27 ≤ 3 ^ β := by
    change 3 ^ 3 ≤ 3 ^ β
    exact Nat.pow_le_pow_right (by norm_num) three_le
  have ρ_large : (27 : ℚ) ≤ (3 : ℚ) ^ β := by
    exact_mod_cast ρ_large_nat
  have first_positive : 0 < 5 * (3 : ℚ) ^ β - 3 := by linarith
  have second_positive : 0 < 25 * ((3 : ℚ) ^ β) ^ 2 + 3 := by positivity
  exact div_ne_zero
    (mul_ne_zero (pow_ne_zero 2 (ne_of_gt first_positive))
      (pow_ne_zero 2 (ne_of_gt second_positive)))
    (by norm_num)

private theorem prefixAlgebraReachableBlockC_isUnit
    (β : Nat) (three_le : 3 ≤ β) :
    IsUnit (prefixAlgebraReachableBlockC β) := by
  rw [Matrix.isUnit_iff_isUnit_det, prefixAlgebraReachableBlockC_det]
  exact isUnit_iff_ne_zero.mpr <|
    div_ne_zero
      (mul_ne_zero (by norm_num)
        (prefixAlgebraReachabilityPolynomial_ne_zero β three_le))
      (by norm_num)

private theorem prefixAlgebraReachableBlockB_isUnit
    (β : Nat) (body : List TagLetter) (three_le : 3 ≤ β) :
    IsUnit (prefixAlgebraReachableBlockB β body) := by
  rw [Matrix.isUnit_iff_isUnit_det, prefixAlgebraReachableBlockB_det]
  apply isUnit_iff_ne_zero.mpr
  have ρ_positive : (0 : ℚ) < (3 : ℚ) ^ β := by positivity
  have ρ_one : (1 : ℚ) ≤ (3 : ℚ) ^ β :=
    one_le_pow_of_one_le (by norm_num) β
  exact div_ne_zero
    (mul_ne_zero
      (mul_ne_zero (by norm_num)
        (pow_ne_zero 3 (sub_ne_zero.mpr (by linarith))))
      (prefixAlgebraBodyPolynomial_ne_zero β body three_le))
    (by norm_num)

private theorem prefixAlgebraObservableBlock_isUnit
    (β : Nat) (three_le : 3 ≤ β) :
    IsUnit (prefixAlgebraObservableBlock β) := by
  rw [Matrix.isUnit_iff_isUnit_det, prefixAlgebraObservableBlock_det]
  apply isUnit_iff_ne_zero.mpr
  have ρ_large_nat : 27 ≤ 3 ^ β := by
    change 3 ^ 3 ≤ 3 ^ β
    exact Nat.pow_le_pow_right (by norm_num) three_le
  have ρ_large : (27 : ℚ) ≤ (3 : ℚ) ^ β := by
    exact_mod_cast ρ_large_nat
  have ρ_positive : (0 : ℚ) < (3 : ℚ) ^ β := by positivity
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 (ne_of_gt ρ_positive)))
    (sub_ne_zero.mpr (by linarith))

private theorem prefixAlgebraAdaptedClosed_mulVec_eq_zero
    (β : Nat) (body : List TagLetter) (three_le : 3 ≤ β)
    (body_nonempty : body ≠ [])
    (vector : Fin 10 → ℚ)
    (product_zero : prefixAlgebraAdaptedClosed β body *ᵥ vector = 0) :
    vector = 0 := by
  let ρ := (3 : ℚ) ^ β
  let m := (5 * ρ - 1) / 2
  let x := prefixAlgebraLowerGap β body
  have row₀ := congrFun product_zero (0 : Fin 10)
  have row₁ := congrFun product_zero (1 : Fin 10)
  have row₂ := congrFun product_zero (2 : Fin 10)
  have row₃ := congrFun product_zero (3 : Fin 10)
  have row₄ := congrFun product_zero (4 : Fin 10)
  have row₅ := congrFun product_zero (5 : Fin 10)
  have row₆ := congrFun product_zero (6 : Fin 10)
  have row₇ := congrFun product_zero (7 : Fin 10)
  have row₈ := congrFun product_zero (8 : Fin 10)
  have row₉ := congrFun product_zero (9 : Fin 10)
  simp [prefixAlgebraAdaptedClosed, Matrix.mulVec, Matrix.dotProduct,
    Fin.sum_univ_succ, ρ, m, x] at row₀ row₁ row₂ row₃ row₄ row₅ row₆ row₇ row₈ row₉
  let first : Fin 3 → ℚ := ![vector 0, vector 1, vector 2]
  have first_product : prefixAlgebraReachableBlockA β *ᵥ first = 0 := by
    funext coordinate
    fin_cases coordinate
    · simpa [prefixAlgebraReachableBlockA, first, ρ, m, Matrix.mulVec,
        Matrix.dotProduct, Fin.sum_univ_succ] using row₀
    · simpa [prefixAlgebraReachableBlockA, first, ρ, m, Matrix.mulVec,
        Matrix.dotProduct, Fin.sum_univ_succ] using row₆
    · simpa [prefixAlgebraReachableBlockA, first, ρ, m, Matrix.mulVec,
        Matrix.dotProduct, Fin.sum_univ_succ] using row₃
  have first_zero : first = 0 := by
    apply (Matrix.mulVec_injective_iff_isUnit.mpr
      (prefixAlgebraReachableBlockA_isUnit β three_le))
    simpa using first_product
  have coordinate₀ : vector 0 = 0 := congrFun first_zero 0
  have coordinate₁ : vector 1 = 0 := congrFun first_zero 1
  have coordinate₂ : vector 2 = 0 := congrFun first_zero 2
  let middle : Fin 3 → ℚ := ![vector 3, vector 4, vector 5]
  have middle_product : prefixAlgebraReachableBlockC β *ᵥ middle = 0 := by
    funext coordinate
    fin_cases coordinate
    · simp [coordinate₀, coordinate₁, coordinate₂] at row₂
      simp [prefixAlgebraReachableBlockC, middle, ρ, m, Matrix.mulVec,
        Matrix.dotProduct, Fin.sum_univ_succ]
      linear_combination row₂
    · simp [coordinate₀, coordinate₁, coordinate₂] at row₈
      simp [prefixAlgebraReachableBlockC, middle, ρ, m, Matrix.mulVec,
        Matrix.dotProduct, Fin.sum_univ_succ]
      linear_combination row₈
    · simp [coordinate₀, coordinate₁, coordinate₂] at row₅
      simp [prefixAlgebraReachableBlockC, middle, ρ, m, Matrix.mulVec,
        Matrix.dotProduct, Fin.sum_univ_succ]
      linear_combination row₅
  have middle_zero : middle = 0 := by
    apply (Matrix.mulVec_injective_iff_isUnit.mpr
      (prefixAlgebraReachableBlockC_isUnit β three_le))
    simpa using middle_product
  have coordinate₃ : vector 3 = 0 := congrFun middle_zero 0
  have coordinate₄ : vector 4 = 0 := congrFun middle_zero 1
  have coordinate₅ : vector 5 = 0 := congrFun middle_zero 2
  let last : Fin 3 → ℚ := ![vector 6, vector 7, vector 8]
  have last_product : prefixAlgebraReachableBlockB β body *ᵥ last = 0 := by
    funext coordinate
    fin_cases coordinate
    · simp [coordinate₀, coordinate₁, coordinate₂, coordinate₃, coordinate₄,
        coordinate₅, prefixAlgebraLowerGap] at row₁
      simp [prefixAlgebraReachableBlockB, last, ρ, m, x,
        prefixAlgebraLowerGap, Matrix.mulVec, Matrix.dotProduct,
        Fin.sum_univ_succ]
      linear_combination row₁
    · simp [coordinate₀, coordinate₁, coordinate₂, coordinate₃, coordinate₄,
        coordinate₅, prefixAlgebraLowerGap] at row₉
      simp [prefixAlgebraReachableBlockB, last, ρ, m, x,
        prefixAlgebraLowerGap, Matrix.mulVec, Matrix.dotProduct,
        Fin.sum_univ_succ]
      linear_combination row₉
    · simp [coordinate₀, coordinate₁, coordinate₂, coordinate₃, coordinate₄,
        coordinate₅, prefixAlgebraLowerGap] at row₄
      simp [prefixAlgebraReachableBlockB, last, ρ, m, x,
        prefixAlgebraLowerGap, Matrix.mulVec, Matrix.dotProduct,
        Fin.sum_univ_succ]
      linear_combination row₄
  have last_zero : last = 0 := by
    apply (Matrix.mulVec_injective_iff_isUnit.mpr
      (prefixAlgebraReachableBlockB_isUnit β body three_le))
    simpa using last_product
  have coordinate₆ : vector 6 = 0 := congrFun last_zero 0
  have coordinate₇ : vector 7 = 0 := congrFun last_zero 1
  have coordinate₈ : vector 8 = 0 := congrFun last_zero 2
  have lower_code_large :
      (25 : ℚ) < chhnNearyLowerC β body := by
    simpa [chhnNearyLowerC] using
      (show (25 : ℚ) < ternaryCode (nearyLower β body (.rule .c)) by
        exact_mod_cast
          ternaryCode_neary_rule_c_gt_twenty_five β body body_nonempty)
  have x_positive : 0 < x := by
    dsimp [x, prefixAlgebraLowerGap]
    linarith
  have ρ_positive : 0 < ρ := by positivity
  have m_positive : 0 < m := by
    dsimp [m]
    have ρ_one : (1 : ℚ) ≤ ρ :=
      one_le_pow_of_one_le (by norm_num) β
    linarith
  have coordinate₉ : vector 9 = 0 := by
    simp [coordinate₀, coordinate₁, coordinate₂, coordinate₃, coordinate₄,
      coordinate₅, coordinate₆, coordinate₇, coordinate₈] at row₇
    rcases row₇ with (x_zero | m_zero) | coordinate₉
    · change x = 0 at x_zero
      exact (ne_of_gt x_positive x_zero).elim
    · have m_zero' : m = 0 := by
        dsimp [m]
        rw [m_zero]
        norm_num
      exact (ne_of_gt m_positive m_zero').elim
    · exact coordinate₉
  funext coordinate
  fin_cases coordinate <;>
    simp [coordinate₀, coordinate₁, coordinate₂, coordinate₃, coordinate₄,
      coordinate₅, coordinate₆, coordinate₇, coordinate₈, coordinate₉]

theorem prefixAlgebraAdapted_isUnit
    (β : Nat) (body : List TagLetter) (three_le : 3 ≤ β)
    (body_nonempty : body ≠ []) :
    IsUnit (prefixAlgebraAdapted β body) := by
  rw [prefixAlgebraAdapted_eq_closed]
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro first second products_equal
  apply sub_eq_zero.mp
  apply prefixAlgebraAdaptedClosed_mulVec_eq_zero β body three_le body_nonempty
  rw [Matrix.mulVec_sub, products_equal, sub_self]

theorem prefixAlgebraReachable_isUnit
    (β : Nat) (body : List TagLetter) (three_le : 3 ≤ β)
    (body_nonempty : body ≠ []) :
    IsUnit (prefixAlgebraReachable β body) := by
  have product_unit : IsUnit
      (prefixAlgebraReachable β body * prefixAlgebraReachabilityChange β) := by
    rw [prefixAlgebraReachable_mul_change]
    exact prefixAlgebraAdapted_isUnit β body three_le body_nonempty
  obtain ⟨repair, product_mul_repair⟩ := product_unit.exists_right_inv
  have right_inverse :
      prefixAlgebraReachable β body *
          (prefixAlgebraReachabilityChange β * repair) = 1 := by
    rw [← Matrix.mul_assoc, product_mul_repair]
  exact Matrix.isUnit_of_right_inverse right_inverse

private theorem prefixAlgebraObservableClosed_mulVec_eq_zero
    (β : Nat) (three_le : 3 ≤ β)
    (vector : Fin 10 → ℚ)
    (product_zero : prefixAlgebraObservableClosed β *ᵥ vector = 0) :
    vector = 0 := by
  have row₀ := congrFun product_zero (0 : Fin 10)
  have row₁ := congrFun product_zero (1 : Fin 10)
  have row₂ := congrFun product_zero (2 : Fin 10)
  have row₃ := congrFun product_zero (3 : Fin 10)
  have row₄ := congrFun product_zero (4 : Fin 10)
  have row₅ := congrFun product_zero (5 : Fin 10)
  have row₆ := congrFun product_zero (6 : Fin 10)
  have row₇ := congrFun product_zero (7 : Fin 10)
  have row₈ := congrFun product_zero (8 : Fin 10)
  have row₉ := congrFun product_zero (9 : Fin 10)
  simp [prefixAlgebraObservableClosed, prefixAlgebraObservableClosedRow,
    Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ] at row₀ row₁ row₂ row₃ row₄
  simp [prefixAlgebraObservableClosed, prefixAlgebraObservableClosedRow,
    Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ] at row₅ row₆ row₇ row₈ row₉
  let first : Fin 3 → ℚ := ![vector 0, vector 1, vector 2]
  have first_product : prefixAlgebraObservableBlock β *ᵥ first = 0 := by
    funext coordinate
    fin_cases coordinate
    · simpa [prefixAlgebraObservableBlock, first, Matrix.mulVec,
        Matrix.dotProduct, Fin.sum_univ_succ] using row₀
    · simpa [prefixAlgebraObservableBlock, first, Matrix.mulVec,
        Matrix.dotProduct, Fin.sum_univ_succ] using row₄
    · simpa [prefixAlgebraObservableBlock, first, Matrix.mulVec,
        Matrix.dotProduct, Fin.sum_univ_succ] using row₅
  have first_zero : first = 0 := by
    apply (Matrix.mulVec_injective_iff_isUnit.mpr
      (prefixAlgebraObservableBlock_isUnit β three_le))
    simpa using first_product
  have coordinate₀ : vector 0 = 0 := congrFun first_zero 0
  have coordinate₁ : vector 1 = 0 := congrFun first_zero 1
  have coordinate₂ : vector 2 = 0 := congrFun first_zero 2
  let middle : Fin 3 → ℚ := ![vector 3, vector 4, vector 5]
  have middle_product : prefixAlgebraObservableBlock β *ᵥ middle = 0 := by
    funext coordinate
    fin_cases coordinate
    · simpa [prefixAlgebraObservableBlock, middle, Matrix.mulVec,
        Matrix.dotProduct, Fin.sum_univ_succ] using row₁
    · simpa [prefixAlgebraObservableBlock, middle, Matrix.mulVec,
        Matrix.dotProduct, Fin.sum_univ_succ] using row₆
    · simpa [prefixAlgebraObservableBlock, middle, Matrix.mulVec,
        Matrix.dotProduct, Fin.sum_univ_succ] using row₇
  have middle_zero : middle = 0 := by
    apply (Matrix.mulVec_injective_iff_isUnit.mpr
      (prefixAlgebraObservableBlock_isUnit β three_le))
    simpa using middle_product
  have coordinate₃ : vector 3 = 0 := congrFun middle_zero 0
  have coordinate₄ : vector 4 = 0 := congrFun middle_zero 1
  have coordinate₅ : vector 5 = 0 := congrFun middle_zero 2
  let last : Fin 3 → ℚ := ![vector 6, vector 7, vector 8]
  have last_product : prefixAlgebraObservableBlock β *ᵥ last = 0 := by
    funext coordinate
    fin_cases coordinate
    · simpa [prefixAlgebraObservableBlock, last, Matrix.mulVec,
        Matrix.dotProduct, Fin.sum_univ_succ] using row₂
    · simpa [prefixAlgebraObservableBlock, last, Matrix.mulVec,
        Matrix.dotProduct, Fin.sum_univ_succ] using row₈
    · simpa [prefixAlgebraObservableBlock, last, Matrix.mulVec,
        Matrix.dotProduct, Fin.sum_univ_succ] using row₉
  have last_zero : last = 0 := by
    apply (Matrix.mulVec_injective_iff_isUnit.mpr
      (prefixAlgebraObservableBlock_isUnit β three_le))
    simpa using last_product
  have coordinate₆ : vector 6 = 0 := congrFun last_zero 0
  have coordinate₇ : vector 7 = 0 := congrFun last_zero 1
  have coordinate₈ : vector 8 = 0 := congrFun last_zero 2
  have coordinate₉ : vector 9 = 0 := by
    rw [coordinate₆, coordinate₈] at row₃
    simpa using row₃
  funext coordinate
  fin_cases coordinate <;>
    simp [coordinate₀, coordinate₁, coordinate₂, coordinate₃, coordinate₄,
      coordinate₅, coordinate₆, coordinate₇, coordinate₈, coordinate₉]

theorem prefixAlgebraObservable_isUnit
    (β : Nat) (body : List TagLetter) (three_le : 3 ≤ β) :
    IsUnit (prefixAlgebraObservable β body) := by
  rw [prefixAlgebraObservable_eq_closed]
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro first second products_equal
  apply sub_eq_zero.mp
  apply prefixAlgebraObservableClosed_mulVec_eq_zero β three_le
  rw [Matrix.mulVec_sub, products_equal, sub_self]

end MatrixMortality
