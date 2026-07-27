import MatrixMortality.PairedBinaryAlgebraContexts

/-!
# Nonsingularity of the paired-binary contexts

The sparse reachable and observable context matrices are nonsingular.  Each kernel calculation
reduces to an integer factor congruent to three modulo nine.
-/

namespace MatrixMortality

open scoped Matrix
open PairedBinaryAlgebra.Certificate

/-- The last factor controlling reachability of the paired-binary separator contexts. -/
private def pairedBinaryAlgebraReachabilityGap (β : Nat) (body : List TagLetter) : ℚ :=
  let ρ := (3 : ℚ) ^ β
  let V := nearySideLowerC β body
  let B := nearySideLowerCScale β body
  17 * B - 18 * V + 18 * ρ - 33

/-- The last factor controlling observability of the paired-binary separator contexts. -/
private def pairedBinaryAlgebraObservabilityGap (β : Nat) (body : List TagLetter) : ℚ :=
  let ρ := (3 : ℚ) ^ β
  let V := nearySideLowerC β body
  45 * V * ρ ^ 2 - 372 * V * ρ - 25 * V -
    1125 * ρ ^ 2 + 3300 * ρ + 1825

private theorem nine_mul_integer_add_three_ne_zero (integer : ℤ) :
    (9 * (integer : ℚ) + 3) ≠ 0 := by
  intro equal_zero
  have integer_zero : 9 * integer + 3 = 0 := by
    exact_mod_cast equal_zero
  omega

private theorem pairedBinaryAlgebraReachabilityGap_ne_zero
    (β : Nat) (body : List TagLetter) (two_le : 2 ≤ β) :
    pairedBinaryAlgebraReachabilityGap β body ≠ 0 := by
  obtain ⟨offset, β_eq⟩ := Nat.exists_eq_add_of_le two_le
  subst β
  let encodedPrefix := ternaryCode (true :: tagEncode (2 + offset) body)
  let lowerScale := (3 : ℤ) ^ (tagEncode (2 + offset) body).length.succ
  let widthScale := (3 : ℤ) ^ offset
  have gap_eq :
      pairedBinaryAlgebraReachabilityGap (2 + offset) body =
        9 * ((17 * lowerScale - 18 * encodedPrefix + 18 * widthScale - 18 : ℤ) : ℚ) +
          3 := by
    rw [pairedBinaryAlgebraReachabilityGap,
      nearySideLowerC_eq_nine_mul_add_seven,
      nearySideLowerCScale_eq_nine_mul]
    push_cast
    simp [pow_add, pow_succ, encodedPrefix, lowerScale, widthScale]
    ring
  rw [gap_eq]
  exact nine_mul_integer_add_three_ne_zero _

private theorem pairedBinaryAlgebraObservabilityGap_ne_zero
    (β : Nat) (body : List TagLetter) (two_le : 2 ≤ β) :
    pairedBinaryAlgebraObservabilityGap β body ≠ 0 := by
  obtain ⟨offset, β_eq⟩ := Nat.exists_eq_add_of_le two_le
  subst β
  let encodedPrefix := ternaryCode (true :: tagEncode (2 + offset) body)
  let widthScale := (3 : ℤ) ^ offset
  have gap_eq :
      pairedBinaryAlgebraObservabilityGap (2 + offset) body =
        9 * ((3645 * widthScale ^ 2 * encodedPrefix - 7290 * widthScale ^ 2 -
          3348 * widthScale * encodedPrefix + 696 * widthScale -
          25 * encodedPrefix + 183 : ℤ) : ℚ) +
          3 := by
    rw [pairedBinaryAlgebraObservabilityGap,
      nearySideLowerC_eq_nine_mul_add_seven]
    push_cast
    simp [pow_add, pow_mul, encodedPrefix, widthScale]
    ring
  rw [gap_eq]
  exact nine_mul_integer_add_three_ne_zero _

private theorem pairedBinaryAlgebraReachableClosed_mulVec_eq_zero
    (β : Nat) (body : List TagLetter) (three_le : 3 ≤ β)
    (vector : Fin 6 → ℚ)
    (product_zero : pairedBinaryAlgebraReachableClosed β body *ᵥ vector = 0) :
    vector = 0 := by
  let ρ := (3 : ℚ) ^ β
  let m := (5 * ρ - 1) / 2
  let u := (15 * ρ + 1) / 2
  let V := nearySideLowerC β body
  let B := nearySideLowerCScale β body
  let H := 3 * ρ * u + m - 25
  let J := -V + (17 * ρ - 1) / 2
  have row₀ := congrFun product_zero (0 : Fin 6)
  have row₁ := congrFun product_zero (1 : Fin 6)
  have row₂ := congrFun product_zero (2 : Fin 6)
  have row₃ := congrFun product_zero (3 : Fin 6)
  have row₄ := congrFun product_zero (4 : Fin 6)
  have row₅ := congrFun product_zero (5 : Fin 6)
  simp [pairedBinaryAlgebraReachableClosed, Matrix.mulVec, Matrix.dotProduct,
    Fin.sum_univ_succ, ρ, m, u, V, B, H, J] at row₀ row₁ row₂ row₃ row₄ row₅
  have ρ_large_nat : 27 ≤ 3 ^ β := by
    change 3 ^ 3 ≤ 3 ^ β
    exact Nat.pow_le_pow_right (by norm_num) three_le
  have ρ_large : (27 : ℚ) ≤ ρ := by
    change (27 : ℚ) ≤ (3 : ℚ) ^ β
    exact_mod_cast ρ_large_nat
  have ρ_positive : 0 < ρ := by
    dsimp [ρ]
    positivity
  have B_large : (9 : ℚ) ≤ B := by
    dsimp [B]
    rw [nearySideLowerCScale_eq_nine_mul]
    nlinarith [one_le_pow_of_one_le (by norm_num : (1 : ℚ) ≤ 3)
      (tagEncode β body).length.succ]
  have gap_ne :
      pairedBinaryAlgebraReachabilityGap β body ≠ 0 :=
    pairedBinaryAlgebraReachabilityGap_ne_zero β body (by omega)
  have determinant_ne :
      9 * (ρ - 3) * (J - B * m) - (3 - B) * (H - 27 * m) ≠ 0 := by
    have factor :
        9 * (ρ - 3) * (J - B * m) - (3 - B) * (H - 27 * m) =
          (ρ - 3) * pairedBinaryAlgebraReachabilityGap β body / 2 := by
      simp [ρ, m, u, V, B, H, J, pairedBinaryAlgebraReachabilityGap]
      ring
    rw [factor]
    exact div_ne_zero
      (mul_ne_zero (sub_ne_zero.mpr (by linarith)) gap_ne)
      (by norm_num)
  have coordinate₂ : vector 2 = 0 := by linarith
  have coordinate₅ : vector 5 = 0 := by
    have factor_zero : 27 * ρ * (ρ - 3) * vector 5 = 0 := by
      linear_combination 3 * ρ * row₃ + row₄ - 3 * ρ * coordinate₂
    have coefficient_ne : 27 * ρ * (ρ - 3) ≠ 0 :=
      mul_ne_zero
        (mul_ne_zero (by norm_num) (ne_of_gt ρ_positive))
        (sub_ne_zero.mpr (by linarith))
    exact (mul_eq_zero.mp factor_zero).resolve_left coefficient_ne
  have coordinate₁ : vector 1 = 0 := by linarith
  have first_equation :
      9 * (ρ - 3) * vector 3 + (3 - B) * vector 4 = 0 := by
    have scaled :
        3 * ρ * (9 * (ρ - 3) * vector 3 + (3 - B) * vector 4) = 0 := by
      linear_combination row₂ + 3 * ρ * row₁
    exact (mul_eq_zero.mp scaled).resolve_left
      (mul_ne_zero (by norm_num) (ne_of_gt ρ_positive))
  have second_equation :
      (H - 27 * m) * vector 3 + (J - B * m) * vector 4 = 0 := by
    linear_combination row₀ + m * row₁ - m * coordinate₁ -
      m * coordinate₂ - H * coordinate₅
  have coordinate₃_factor :
      (9 * (ρ - 3) * (J - B * m) - (3 - B) * (H - 27 * m)) *
        vector 3 = 0 := by
    linear_combination (J - B * m) * first_equation -
      (3 - B) * second_equation
  have coordinate₃ : vector 3 = 0 :=
    (mul_eq_zero.mp coordinate₃_factor).resolve_left determinant_ne
  have coordinate₄ : vector 4 = 0 := by
    have B_ne : 3 - B ≠ 0 := by linarith
    have factor_zero : (3 - B) * vector 4 = 0 := by
      linear_combination first_equation - 9 * (ρ - 3) * coordinate₃
    exact (mul_eq_zero.mp factor_zero).resolve_left B_ne
  have coordinate₀ : vector 0 = 0 := by
    linear_combination -row₁ - 27 * coordinate₃ - B * coordinate₄
  funext coordinate
  fin_cases coordinate <;>
    simp [coordinate₀, coordinate₁, coordinate₂, coordinate₃, coordinate₄, coordinate₅]

theorem pairedBinaryAlgebraReachable_isUnit
    (β : Nat) (body : List TagLetter) (three_le : 3 ≤ β) :
    IsUnit (pairedBinaryAlgebraReachable β body) := by
  rw [pairedBinaryAlgebraReachable_eq_closed]
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro first second products_equal
  apply sub_eq_zero.mp
  apply pairedBinaryAlgebraReachableClosed_mulVec_eq_zero β body three_le
  rw [Matrix.mulVec_sub, products_equal, sub_self]

private theorem pairedBinaryAlgebraObservableClosed_mulVec_eq_zero
    (β : Nat) (body : List TagLetter) (three_le : 3 ≤ β)
    (vector : Fin 6 → ℚ)
    (product_zero : pairedBinaryAlgebraObservableClosed β body *ᵥ vector = 0) :
    vector = 0 := by
  let ρ := (3 : ℚ) ^ β
  let u := (15 * ρ + 1) / 2
  let V := nearySideLowerC β body
  let K := (135 * ρ ^ 2 + 24 * ρ + 1) / 2
  have row₀ := congrFun product_zero (0 : Fin 6)
  have row₁ := congrFun product_zero (1 : Fin 6)
  have row₂ := congrFun product_zero (2 : Fin 6)
  have row₃ := congrFun product_zero (3 : Fin 6)
  have row₄ := congrFun product_zero (4 : Fin 6)
  have row₅ := congrFun product_zero (5 : Fin 6)
  simp [pairedBinaryAlgebraObservableClosed, Matrix.mulVec, Matrix.dotProduct,
    Fin.sum_univ_succ, ρ, u, V, K] at row₀ row₁ row₂ row₃ row₄ row₅
  have u_ne : u ≠ 0 := by
    dsimp [u]
    positivity
  have gap_ne :
      pairedBinaryAlgebraObservabilityGap β body ≠ 0 :=
    pairedBinaryAlgebraObservabilityGap_ne_zero β body (by omega)
  have determinant_ne :
      (25 - V) * (76 * u - K) - 1200 * (u - 2) ≠ 0 := by
    have factor :
        (25 - V) * (76 * u - K) - 1200 * (u - 2) =
          3 * pairedBinaryAlgebraObservabilityGap β body / 2 := by
      simp [ρ, u, V, K, pairedBinaryAlgebraObservabilityGap]
      ring
    rw [factor]
    exact div_ne_zero (mul_ne_zero (by norm_num) gap_ne) (by norm_num)
  have coordinate₀ : vector 0 = 0 := by linarith
  have phase_first : 25 * vector 1 + u * vector 2 = 0 := by
    linear_combination row₃ - row₁
  have phase_second : vector 1 + u * vector 2 = 0 := by
    linear_combination row₄ - row₂
  have coordinate₁ : vector 1 = 0 := by
    linarith [phase_first, phase_second]
  have coordinate₂ : vector 2 = 0 := by
    have factor_zero := phase_second
    rw [coordinate₁, zero_add] at factor_zero
    exact (mul_eq_zero.mp factor_zero).resolve_left u_ne
  have first_equation :
      (25 - V) * vector 3 + (u - 2) * vector 4 = 0 := by
    linear_combination row₁ - row₂
  have second_equation :
      1200 * vector 3 + (76 * u - K) * vector 4 = 0 := by
    have raw :
        75 * vector 0 - 25 * vector 1 - u * vector 2 +
          1200 * vector 3 + (76 * u - K) * vector 4 = 0 := by
      linear_combination 76 * row₁ - row₅
    rw [coordinate₀, coordinate₁, coordinate₂] at raw
    simpa using raw
  have coordinate₃_factor :
      ((25 - V) * (76 * u - K) - 1200 * (u - 2)) * vector 3 = 0 := by
    linear_combination (76 * u - K) * first_equation -
      (u - 2) * second_equation
  have coordinate₃ : vector 3 = 0 :=
    (mul_eq_zero.mp coordinate₃_factor).resolve_left determinant_ne
  have coordinate₄ : vector 4 = 0 := by
    have coordinate₄_factor :
        ((25 - V) * (76 * u - K) - 1200 * (u - 2)) * vector 4 = 0 := by
      linear_combination (25 - V) * second_equation -
        1200 * first_equation
    exact (mul_eq_zero.mp coordinate₄_factor).resolve_left determinant_ne
  have coordinate₅ : vector 5 = 0 := by
    have reduced := row₁
    rw [coordinate₀, coordinate₃, coordinate₄] at reduced
    simpa using reduced
  funext coordinate
  fin_cases coordinate <;>
    simp [coordinate₀, coordinate₁, coordinate₂, coordinate₃, coordinate₄, coordinate₅]

theorem pairedBinaryAlgebraObservable_isUnit
    (β : Nat) (body : List TagLetter) (three_le : 3 ≤ β) :
    IsUnit (pairedBinaryAlgebraObservable β body) := by
  rw [pairedBinaryAlgebraObservable_eq_closed]
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro first second products_equal
  apply sub_eq_zero.mp
  apply pairedBinaryAlgebraObservableClosed_mulVec_eq_zero β body three_le
  rw [Matrix.mulVec_sub, products_equal, sub_self]

end MatrixMortality
