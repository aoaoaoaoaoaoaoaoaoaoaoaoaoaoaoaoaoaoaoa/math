import MatrixMortality.ReturnFamily

/-!
# The parity-Jordan return branch

A single `-1` Jordan block carries the mode `n(-1)ⁿ` unavailable to split quadratic pencils.
The resulting exact parity-Collatz rail is unique within its rank-compatible normal form, but
its physical pair has a common eigenline modulo seven and is therefore immortal.
-/

namespace MatrixMortality.ReturnJordan

open scoped Matrix

/-- Constant mode of the integral parity return. -/
def constant : Square (Fin 2) ℤ :=
  !![35, 14;
     35, 14]

/-- Alternating mode of the integral parity return. -/
def alternating : Square (Fin 2) ℤ :=
  !![-23, -14;
     49, -14]

/-- Jordan drift mode of the integral parity return. -/
def drift : Square (Fin 2) ℤ :=
  !![42, -12;
     0, 0]

/-- Exact return sequence `C₀+(-1)ⁿC₁+n(-1)ⁿC₂`. -/
def parityReturn (n : Nat) : Square (Fin 2) ℤ :=
  constant + (-1 : ℤ) ^ n • alternating +
    ((n : ℤ) * (-1 : ℤ) ^ n) • drift

/-- Even returns implement the halving rail. -/
theorem parityReturn_of_even (n : Nat) (even : Even n) :
    parityReturn n =
      6 • !![7 * (n : ℤ) + 2, -2 * (n : ℤ);
             14, 0] := by
  rw [parityReturn, even.neg_one_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [constant, alternating, drift, Matrix.add_apply,
      Matrix.smul_apply]
  all_goals ring

/-- Odd returns implement the `3n+1` rail. -/
theorem parityReturn_of_odd (n : Nat) (odd : Odd n) :
    parityReturn n =
      2 • !![29 - 21 * (n : ℤ), 6 * (n : ℤ) + 14;
             -7, 14] := by
  rw [parityReturn, odd.neg_one_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [constant, alternating, drift, Matrix.add_apply,
      Matrix.smul_apply]
  all_goals ring

/-- Cross-multiplied exactness of the even halving rail. -/
theorem even_rail (n : Nat) (even : Even n) :
    2 * (parityReturn n *ᵥ ![(n : ℤ), 1]) 0 =
      (n : ℤ) * (parityReturn n *ᵥ ![(n : ℤ), 1]) 1 := by
  rw [parityReturn_of_even n even]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- Cross-multiplied exactness of the odd `3n+1` rail. -/
theorem odd_rail (n : Nat) (odd : Odd n) :
    (parityReturn n *ᵥ ![(n : ℤ), 1]) 0 =
      (3 * (n : ℤ) + 1) * (parityReturn n *ᵥ ![(n : ℤ), 1]) 1 := by
  rw [parityReturn_of_odd n odd]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- Zero wait is a nonzero rank-one separator. -/
theorem parityReturn_zero :
    parityReturn 0 = Matrix.vecMulVec ![12, 84] ![1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [parityReturn, constant, alternating, drift,
      Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply]

/-- Determinant on the even branch. -/
theorem parityReturn_det_of_even (n : Nat) (even : Even n) :
    (parityReturn n).det = 1008 * (n : ℤ) := by
  rw [parityReturn_of_even n even, Matrix.det_fin_two]
  norm_num [Matrix.smul_apply]
  ring

/-- Determinant on the odd branch. -/
theorem parityReturn_det_of_odd (n : Nat) (odd : Odd n) :
    (parityReturn n).det = 1008 * (2 - (n : ℤ)) := by
  rw [parityReturn_of_odd n odd, Matrix.det_fin_two]
  norm_num [Matrix.smul_apply]
  ring

/-- Every positive parity return is invertible over `ℚ`. -/
theorem cast_parityReturn_isUnit (n : Nat) (positive : 0 < n) :
    IsUnit (castMatrix (parityReturn n)) := by
  apply (castMatrix (parityReturn n)).isUnit_iff_isUnit_det.mpr
  rw [castMatrix_det]
  apply isUnit_iff_ne_zero.mpr
  have det_ne : (parityReturn n).det ≠ 0 := by
    rcases Nat.even_or_odd n with even | odd
    · rw [parityReturn_det_of_even n even]
      exact mul_ne_zero (by norm_num : (1008 : ℤ) ≠ 0)
        (Int.ofNat_ne_zero.mpr positive.ne')
    · rw [parityReturn_det_of_odd n odd]
      apply mul_ne_zero
      · norm_num
      · intro two_eq
        have n_eq_two : n = 2 := by omega
        subst n
        rcases odd with ⟨k, odd_eq⟩
        omega
  exact_mod_cast det_ne

/-- Physical Jordan ambient matrix. -/
def physicalAmbient : Square (Fin 3) ℤ :=
  !![1, 0, 0;
     0, -1, 1;
     0, 0, -1]

/-- Physical rank-two cut realizing the parity return sequence. -/
def physicalCut : Square (Fin 3) ℤ :=
  !![147, 105, -49;
     -111, -69, 49;
     -90, -126, -42]

/-- Rational split input of the physical cut. -/
def input : Matrix (Fin 3) (Fin 2) ℚ :=
  !![-105, -42;
     69, 42;
     126, -36]

/-- Rational split output of the physical cut. -/
def output : Matrix (Fin 2) (Fin 3) ℚ :=
  !![-1, -1, 0;
     -1, 0, 7 / 6]

/-- Closed form of the Jordan ambient power. -/
def ambientPower (n : Nat) : Square (Fin 3) ℚ :=
  !![1, 0, 0;
     0, (-1 : ℚ) ^ n, -(n : ℚ) * (-1 : ℚ) ^ n;
     0, 0, (-1 : ℚ) ^ n]

theorem physicalAmbient_pow (n : Nat) :
    castMatrix physicalAmbient ^ n = ambientPower n := by
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [ambientPower, Matrix.one_apply, Matrix.vecHead, Matrix.vecTail]
  | succ n induction =>
      rw [pow_succ, induction]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [ambientPower, physicalAmbient, castMatrix, Matrix.mul_apply,
          Fin.sum_univ_succ, pow_succ]
      all_goals ring

theorem input_mul_output :
    input * output = castMatrix physicalCut := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [input, output, physicalCut, castMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ]

/-- The physical returns are exactly three times the parity pencil. -/
theorem returnMatrix_eq (n : Nat) :
    ReturnFamily.returnMatrix (castMatrix physicalAmbient) input output n =
      3 • castMatrix (parityReturn n) := by
  rw [ReturnFamily.returnMatrix, physicalAmbient_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [input, output, ambientPower, parityReturn, constant, alternating,
      drift, castMatrix, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
      Fin.sum_univ_succ]
  all_goals ring

/-! ## Rigidity of the rank-compatible rail -/

/-- Constant coefficient forced by the two parity rail identities. -/
def normalConstant (f h i : ℚ) : Square (Fin 2) ℚ :=
  !![-7 * f / 2 + h / 2 - i / 6, -f;
     5 * i / 6, -2 * f + h]

/-- Alternating coefficient forced by the two parity rail identities. -/
def normalAlternating (f h i j l : ℚ) : Square (Fin 2) ℚ :=
  !![5 * f / 2 + h / 2 + i / 6 - j, f;
     7 * i / 6 - l, h]

/-- Jordan coefficient forced by the two parity rail identities. -/
def normalDrift (i j l : ℚ) : Square (Fin 2) ℚ :=
  !![i, j;
     0, l]

/-- Even branch of the five-parameter rail normal form. -/
def normalEven (f h i j l n : ℚ) : Square (Fin 2) ℚ :=
  normalConstant f h i + normalAlternating f h i j l +
    n • normalDrift i j l

/-- Odd branch of the five-parameter rail normal form. -/
def normalOdd (f h i j l n : ℚ) : Square (Fin 2) ℚ :=
  normalConstant f h i - normalAlternating f h i j l -
    n • normalDrift i j l

/-- The two projective rail identities on every even and odd natural input force the
five-parameter coefficient normal form. -/
theorem rail_normal_form
    (C₀ C₁ C₂ : Square (Fin 2) ℚ)
    (even : ∀ n : Nat, Even n →
      2 * ((C₀ + C₁ + (n : ℚ) • C₂) *ᵥ ![(n : ℚ), 1]) 0 =
        (n : ℚ) * ((C₀ + C₁ + (n : ℚ) • C₂) *ᵥ ![(n : ℚ), 1]) 1)
    (odd : ∀ n : Nat, Odd n →
      ((C₀ - C₁ - (n : ℚ) • C₂) *ᵥ ![(n : ℚ), 1]) 0 =
        (3 * (n : ℚ) + 1) *
          ((C₀ - C₁ - (n : ℚ) • C₂) *ᵥ ![(n : ℚ), 1]) 1) :
    C₀ = normalConstant (C₁ 0 1) (C₁ 1 1) (C₂ 0 0) ∧
      C₁ = normalAlternating
        (C₁ 0 1) (C₁ 1 1) (C₂ 0 0) (C₂ 0 1) (C₂ 1 1) ∧
      C₂ = normalDrift (C₂ 0 0) (C₂ 0 1) (C₂ 1 1) := by
  have evenTwo := even 2 (by decide)
  have evenFour := even 4 (by decide)
  have evenSix := even 6 (by decide)
  have evenEight := even 8 (by decide)
  have oddOne := odd 1 (by decide)
  have oddThree := odd 3 (by decide)
  have oddFive := odd 5 (by decide)
  simp [Matrix.mulVec, dotProduct, Matrix.add_apply,
    Matrix.smul_apply, Fin.sum_univ_succ] at evenTwo evenFour evenSix evenEight
  simp [Matrix.mulVec, dotProduct, Matrix.sub_apply,
    Matrix.smul_apply, Fin.sum_univ_succ] at oddOne oddThree oddFive
  ring_nf at evenTwo evenFour evenSix evenEight oddOne oddThree oddFive
  constructor
  · ext row column
    fin_cases row <;> fin_cases column <;>
      simp [normalConstant]
    all_goals linarith
  constructor
  · ext row column
    fin_cases row <;> fin_cases column <;>
      simp [normalAlternating]
    all_goals linarith
  · ext row column
    fin_cases row <;> fin_cases column <;>
      simp [normalDrift]
    all_goals linarith

/-- Tangency equation saying that the alternating mode lies in the tangent space to the
rank-one determinantal variety at the Jordan mode. -/
def tangentDefect (f h i j l : ℚ) : ℚ :=
  15 * f * l + 6 * h * i + 3 * h * l - 7 * i * j + i * l

theorem normalConstant_det (f h i : ℚ) :
    (normalConstant f h i).det =
      (7 * f - h) * (6 * f - 3 * h + i) / 6 := by
  rw [Matrix.det_fin_two]
  simp [normalConstant]
  ring

theorem normalDrift_det (i j l : ℚ) :
    (normalDrift i j l).det = i * l := by
  rw [Matrix.det_fin_two]
  simp [normalDrift]

theorem normalEven_zero_det (f h i j l : ℚ) :
    (normalEven f h i j l 0).det =
      2 * (f - h) * (f - h + j) := by
  rw [Matrix.det_fin_two]
  simp [normalEven, normalConstant, normalAlternating, normalDrift,
    Matrix.add_apply]
  ring

theorem normalEven_det (f h i j l n : ℚ) :
    (normalEven f h i j l n).det =
      (f - h - i * n) * (2 * f - 2 * h + 2 * j - l * n) := by
  rw [Matrix.det_fin_two]
  simp [normalEven, normalConstant, normalAlternating, normalDrift,
    Matrix.add_apply]
  ring

theorem normalOdd_det (f h i j l n : ℚ) :
    (normalOdd f h i j l n).det =
      (6 * f + i * n) * (6 * f - j + 3 * l * n + l) / 3 := by
  rw [Matrix.det_fin_two]
  simp [normalOdd, normalConstant, normalAlternating, normalDrift,
    Matrix.sub_apply]
  ring

/-- The rank constraints, separator, and the first positive return in each parity leave only
the displayed parity-Collatz branch. -/
theorem normalForm_unique
    (f h i j l : ℚ)
    (constant_singular : (normalConstant f h i).det = 0)
    (drift_singular : (normalDrift i j l).det = 0)
    (tangent : tangentDefect f h i j l = 0)
    (separator_singular : (normalEven f h i j l 0).det = 0)
    (even_two_unit : (normalEven f h i j l 2).det ≠ 0)
    (odd_one_unit : (normalOdd f h i j l 1).det ≠ 0) :
    f ≠ 0 ∧ h = f ∧ i = -3 * f ∧ j = 6 * f / 7 ∧ l = 0 := by
  unfold tangentDefect at tangent
  rw [normalConstant_det] at constant_singular
  rw [normalDrift_det] at drift_singular
  rw [normalEven_zero_det] at separator_singular
  rw [normalEven_det] at even_two_unit
  rw [normalOdd_det] at odd_one_unit
  have constant_factors :
      (7 * f - h) * (6 * f - 3 * h + i) = 0 := by
    nlinarith
  have separator_factors :
      (f - h) * (f - h + j) = 0 := by
    nlinarith
  have even_first : f - h - 2 * i ≠ 0 := by
    intro factor_zero
    apply even_two_unit
    rw [show f - h - i * 2 = f - h - 2 * i by ring, factor_zero, zero_mul]
  have even_second : 2 * f - 2 * h + 2 * j - 2 * l ≠ 0 := by
    intro factor_zero
    apply even_two_unit
    rw [show 2 * f - 2 * h + 2 * j - l * 2 =
        2 * f - 2 * h + 2 * j - 2 * l by ring, factor_zero, mul_zero]
  have odd_first : 6 * f + i ≠ 0 := by
    intro factor_zero
    apply odd_one_unit
    rw [show 6 * f + i * 1 = 6 * f + i by ring, factor_zero, zero_mul,
      zero_div]
  rcases mul_eq_zero.mp constant_factors with constant_left | constant_right
  · exfalso
    have h_value : h = 7 * f := by linarith
    rw [h_value] at tangent separator_factors even_first even_second
    rcases mul_eq_zero.mp drift_singular with i_zero | l_zero
    · rw [i_zero] at tangent even_first odd_first
      rcases mul_eq_zero.mp separator_factors with first_zero | second_zero
      · exact even_first (by linarith)
      · have j_value : j = 6 * f := by linarith
        rw [j_value] at tangent even_second
        have f_nonzero : f ≠ 0 := by
          intro f_zero
          exact odd_first (by linarith)
        have l_value : l = 0 := by
          have product_zero : f * l = 0 := by nlinarith [tangent]
          exact (mul_eq_zero.mp product_zero).resolve_left f_nonzero
        rw [l_value] at even_second
        exact even_second (by ring)
    · rw [l_zero] at tangent even_second
      rcases mul_eq_zero.mp separator_factors with first_zero | second_zero
      · have f_zero : f = 0 := by linarith
        have i_nonzero : i ≠ 0 := by
          intro i_zero
          exact odd_first (by linarith)
        have j_zero : j = 0 := by
          have product_zero : i * j = 0 := by
            rw [f_zero] at tangent
            nlinarith [tangent]
          exact (mul_eq_zero.mp product_zero).resolve_left i_nonzero
        exact even_second (by rw [f_zero, j_zero]; ring)
      · have j_value : j = 6 * f := by linarith
        exact even_second (by rw [j_value]; ring)
  · have i_eq : i = -6 * f + 3 * h := by linarith
    rw [i_eq] at tangent drift_singular even_first odd_first
    rcases mul_eq_zero.mp drift_singular with i_zero | l_zero
    · exfalso
      have h_value : h = 2 * f := by linarith
      rw [h_value] at tangent separator_factors even_first even_second
      rcases mul_eq_zero.mp separator_factors with first_zero | second_zero
      · exact odd_first (by linarith)
      · have j_value : j = f := by linarith
        rw [j_value] at tangent even_second
        have f_nonzero : f ≠ 0 := by
          intro f_zero
          exact odd_first (by linarith)
        have l_value : l = 0 := by
          have product_zero : f * l = 0 := by nlinarith [tangent]
          exact (mul_eq_zero.mp product_zero).resolve_left f_nonzero
        rw [l_value] at even_second
        exact even_second (by ring)
    · rw [l_zero] at tangent even_second
      rcases mul_eq_zero.mp separator_factors with first_zero | second_zero
      · have h_value : h = f := by linarith
        have i_value : i = -3 * f := by linarith
        have f_nonzero : f ≠ 0 := by
          intro f_zero
          apply even_first
          rw [h_value, f_zero]
          norm_num
        have j_value : j = 6 * f / 7 := by
          have factored : 3 * f * (7 * j - 6 * f) = 0 := by
            rw [h_value] at tangent
            nlinarith [tangent]
          have final_factor : 7 * j - 6 * f = 0 := by
            rcases mul_eq_zero.mp factored with three_f_zero | final_factor
            · have : f = 0 := by nlinarith
              exact (f_nonzero this).elim
            · exact final_factor
          linarith
        exact ⟨f_nonzero, h_value, i_value, j_value, l_zero⟩
      · have j_value : j = h - f := by linarith
        apply (even_second (by rw [j_value]; ring)).elim

/-- The physical binary family, with `false` ambient and `true` cut. -/
def generator : Bool → Square (Fin 3) ℤ
  | false => physicalAmbient
  | true => physicalCut

/-- Common eigenline modulo seven. -/
def witness : Fin 3 → ZMod 7 :=
  ![0, 1, 0]

/-- Ambient and cut eigenvalues on the modular witness. -/
def eigenvalue : Bool → ZMod 7
  | false => -1
  | true => 1

theorem mapped_generator_mulVec (label : Bool) :
    Matrix.mulVec ((generator label).map (Int.castRingHom (ZMod 7))) witness =
      eigenvalue label • witness := by
  let : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  cases label <;> decide

/-- The exact parity-Collatz Jordan branch is immortal, certified in `ZMod 7`. -/
theorem not_isMortal_generator :
    ¬IsMortal generator := by
  let : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let quotient :=
    ((Int.castRingHom (ZMod 7)).mapMatrix (m := Fin 3)).toMonoidWithZeroHom
  apply not_isMortal_of_map_not_isMortal quotient generator
  apply not_isMortal_of_common_eigenvector
    (quotient ∘ generator) witness eigenvalue
  · intro witness_zero
    have := congrFun witness_zero 1
    norm_num [witness] at this
  · intro label
    cases label <;> norm_num [eigenvalue]
  · intro label
    simpa [quotient, Function.comp_def] using mapped_generator_mulVec label

end MatrixMortality.ReturnJordan
