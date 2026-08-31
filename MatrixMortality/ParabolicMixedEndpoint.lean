import MatrixMortality.ParabolicDefect

/-!
# Mixed `c` endpoint exclusions

Exact characteristic-zero bridge certificates for shortest bad skeletons whose body dependence
occurs at more than one endpoint.
-/

namespace MatrixMortality.ParabolicBlade

/-- Positive coefficient core for the shortest `1 | 2 | 0` bridge with `c` endpoints and a
`b` defect at deletion width three. -/
def cOneBDefectCZeroCore (D q x y z : ℚ) : ℚ :=
  384 * D * (84797 * D - 2991 * q - 143568) * x * y * z +
    (1998567888 * D ^ 2 + 68192928 * D * q + 3466305792 * D) * x * y +
    1152 * (84797 * D - 2991 * q - 143568) * x * z +
    (5995703664 * D + 204578784 * q + 10398917376) * x +
    (810465320 * D ^ 2 + 59128288 * D * q + 2838157824 * D -
      2871240 * q ^ 2 - 275639040 * q - 6615336960) * y * z +
    (46638900919 * D ^ 2 + 6565013951 * D * q + 319777380960 * D +
      170211402 * q ^ 2 + 16835549616 * q + 415939311360) * y +
    (1841488208 * D - 55334064 * q - 2656035072) * z +
    104349113518 * D + 3260309508 * q + 166998205152

theorem cOneBDefectCZeroCore_pos
    (D q x y z : ℚ) (twenty_four_lt_D : 24 < D) (q_positive : 0 < q)
    (q_small : q < 16 * D) (x_nonnegative : 0 ≤ x)
    (y_nonnegative : 0 ≤ y) (z_nonnegative : 0 ≤ z) :
    0 < cOneBDefectCZeroCore D q x y z := by
  have D_positive : 0 < D := by linarith
  have throat_positive : 0 < 84797 * D - 2991 * q - 143568 := by
    nlinarith
  have q_sq_lt : q ^ 2 < 16 * D * q := by
    nlinarith [mul_lt_mul_of_pos_right q_small q_positive]
  have yz_coefficient_positive :
      0 < 810465320 * D ^ 2 + 59128288 * D * q + 2838157824 * D -
        2871240 * q ^ 2 - 275639040 * q - 6615336960 := by
    have Dq_positive : 0 < D * q := mul_pos D_positive q_positive
    have D_sq_positive : 0 < D ^ 2 := sq_pos_of_pos D_positive
    have twenty_four_q_lt_Dq : 24 * q < D * q :=
      mul_lt_mul_of_pos_right twenty_four_lt_D q_positive
    nlinarith
  have z_coefficient_positive :
      0 < 1841488208 * D - 55334064 * q - 2656035072 := by
    nlinarith
  unfold cOneBDefectCZeroCore
  positivity

/-- Exact shortest `1 | 2 | 0` bridge determinant with `c` endpoints and a `b` defect at
deletion width three. -/
theorem bridge_cOne_bTwo_cZero_det
    (body : List TagLetter) (x y z : Nat) :
    (bridge 27
      (cAtom 27 (nearySideLowerC 3 body) (nearySideLowerCScale 3 body) (3 * z + 1) *
        bAtom 27 (3 * x + 2) *
        cAtom 27 (nearySideLowerC 3 body) (nearySideLowerCScale 3 body) (3 * y))).det =
      729 / 704 *
        cOneBDefectCZeroCore
          (nearySideLowerCScale 3 body - 3)
          (11 * nearySideLowerC 3 body - 9 * nearySideLowerCScale 3 body - 32)
          x y z := by
  rw [cAtom_three_mul_add_one_matrix, bAtom_three_mul_add_two_matrix,
    cAtom_three_mul_matrix, Matrix.det_fin_two]
  norm_num [bridge, coreInput, coreOutput, Matrix.mul_apply, Fin.sum_univ_succ,
    cOneBDefectCZeroCore]
  ring

/-- No shortest `1 | 2 | 0` bad bridge with `c` endpoints and a `b` defect closes at deletion
width three. -/
theorem bridge_cOne_bTwo_cZero_det_ne_zero
    (body : List TagLetter) (body_nonempty : body ≠ []) (x y z : Nat) :
    (bridge 27
      (cAtom 27 (nearySideLowerC 3 body) (nearySideLowerCScale 3 body) (3 * z + 1) *
        bAtom 27 (3 * x + 2) *
        cAtom 27 (nearySideLowerC 3 body) (nearySideLowerCScale 3 body) (3 * y))).det ≠ 0 := by
  rw [bridge_cOne_bTwo_cZero_det]
  let L : ℚ := nearySideLowerC 3 body
  let M : ℚ := nearySideLowerCScale 3 body
  let D := M - 3
  let q := 11 * L - 9 * M - 32
  obtain ⟨q_positive, q_small⟩ :=
    neary_rule_c_residue_one_bounds 3 body body_nonempty
  change 0 < q at q_positive
  change q < 16 * D at q_small
  have encoded_nonempty : tagEncode 3 body ≠ [] :=
    (tagEncode_eq_nil_iff 3 body).not.mpr body_nonempty
  have four_le : 4 ≤ (nearyLower 3 body (.rule .c)).length := by
    simp only [nearyLower, List.length_append, List.length_cons, List.length_nil]
    have encoded_length := List.length_pos_of_ne_nil encoded_nonempty
    omega
  have M_gt : 27 < M := by
    have power_lt : 27 < 3 ^ (nearyLower 3 body (.rule .c)).length := by
      have := Nat.pow_le_pow_right (by norm_num : 0 < 3) four_le
      norm_num at this ⊢
      omega
    dsimp [M]
    simp only [nearySideLowerCScale]
    exact_mod_cast power_lt
  have twenty_four_lt_D : 24 < D := by
    dsimp [D]
    linarith
  change 729 / 704 * cOneBDefectCZeroCore D q x y z ≠ 0
  have core_positive : 0 < cOneBDefectCZeroCore D q x y z :=
    cOneBDefectCZeroCore_pos D q x y z twenty_four_lt_D q_positive q_small
      (by positivity) (by positivity) (by positivity)
  positivity

/-! ## Transposed double-`c` endpoint incidence -/

/-- Integral coefficient core of the remaining shortest `0 | 2 | 1` bridge with a `b` defect
and `c` endpoints. -/
def cZeroBDefectCOneCore (L M x y z : ℚ) : ℚ :=
  -4608 * (M - 3) * (486 * L + 43 * M - 615) * x * y * z -
    5073408 * (M - 3) * x * y +
    72 * (6825141 * L ^ 2 - 6090991 * L * M + 4529379 * L -
      729918 * M ^ 2 + 10462243 * M - 17899014) * x * z +
    864 * (1320089 * L - 1319355 * M + 2620360) * x +
    8 * (60367761 * L ^ 2 + 6238674 * L * M - 139451544 * L -
      351196 * M ^ 2 - 4131498 * M + 75923019) * y * z +
    22368 * (50085 * L - 527 * M - 48504) * y +
    (328665276 * L ^ 2 - 353028863 * L * M + 1845263517 * L -
      41891652 * M ^ 2 + 750997031 * M - 2990808429) * z +
    5592 * (129436 * L - 154215 * M + 927905)

/-- Exact determinant of the transposed double-`c` endpoint bridge. -/
theorem bridge_cZero_bTwo_cOne_det
    (body : List TagLetter) (x y z : Nat) :
    (bridge 27
      (cAtom 27 (nearySideLowerC 3 body) (nearySideLowerCScale 3 body) (3 * z) *
        bAtom 27 (3 * x + 2) *
        cAtom 27 (nearySideLowerC 3 body) (nearySideLowerCScale 3 body)
          (3 * y + 1))).det =
      243 / 128 *
        cZeroBDefectCOneCore
          (nearySideLowerC 3 body) (nearySideLowerCScale 3 body) x y z := by
  rw [cAtom_three_mul_matrix, bAtom_three_mul_add_two_matrix,
    cAtom_three_mul_add_one_matrix, Matrix.det_fin_two]
  norm_num [bridge, coreInput, coreOutput, Matrix.mul_apply, Fin.sum_univ_succ,
    cZeroBDefectCOneCore]
  ring

/-- On the all-`c` body ray `L=M-2`, the transposed double-`c` incidence separates into two
linear wait pencils. -/
theorem cZeroBDefectCOneCore_allC_factor (M x y z : ℚ) :
    cZeroBDefectCOneCore (M - 2) M x y z =
      -(8 * (M - 3) * y - (M - 27)) *
        (304704 * (M - 3) * x * z + 634176 * x -
          66255239 * (M - 3) * z - 138564168) := by
  unfold cZeroBDefectCOneCore
  ring

/-- The transposed double-`c` incidence is nonzero on the all-`c` code ray. -/
theorem cZeroBDefectCOneCore_allC_ne_zero
    (M : ℚ) (twenty_seven_lt_M : 27 < M) (x y z : Nat) :
    cZeroBDefectCOneCore (M - 2) M x y z ≠ 0 := by
  rw [cZeroBDefectCOneCore_allC_factor]
  apply mul_ne_zero
  · by_cases y_zero : y = 0
    · subst y
      norm_num
      linarith
    · have y_one : (1 : ℚ) ≤ y := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr y_zero
      have factor_positive :
          0 < 8 * (M - 3) * (y : ℚ) - (M - 27) := by
        have scale_positive : 0 < M - 3 := by linarith
        have scaled_lower : M - 3 ≤ (M - 3) * (y : ℚ) :=
          (le_mul_iff_one_le_right scale_positive).mpr y_one
        nlinarith
      exact neg_ne_zero.mpr (ne_of_gt factor_positive)
  · intro pencil_zero
    by_cases z_zero : z = 0
    · subst z
      norm_num at pencil_zero
      have x_lower : (218 : ℚ) < x := by nlinarith
      have x_upper : (x : ℚ) < 219 := by nlinarith
      have x_lower_nat : 218 < x := by exact_mod_cast x_lower
      have x_upper_nat : x < 219 := by exact_mod_cast x_upper
      omega
    · have z_one : (1 : ℚ) ≤ z := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr z_zero
      let D := M - 3
      let denominator : ℚ := 304704 * D * z + 634176
      let numerator : ℚ := 66255239 * D * z + 138564168
      have D_positive : 0 < D := by dsimp [D]; linarith
      have Dz_lower : 24 < D * (z : ℚ) := by
        have D_le_Dz : D ≤ D * (z : ℚ) :=
          (le_mul_iff_one_le_right D_positive).mpr z_one
        dsimp [D] at D_positive ⊢
        linarith
      have denominator_positive : 0 < denominator := by
        dsimp [denominator]
        positivity
      have lower_numerator : 217 * denominator < numerator := by
        dsimp [denominator, numerator]
        nlinarith
      have upper_numerator : numerator < 218 * denominator := by
        dsimp [denominator, numerator]
        nlinarith
      have pencil_eq : denominator * (x : ℚ) = numerator := by
        dsimp [denominator, numerator, D]
        nlinarith
      have x_lower : (217 : ℚ) < x := by
        by_contra lower_not
        have x_le : (x : ℚ) ≤ 217 := le_of_not_gt lower_not
        have scaled_le : denominator * (x : ℚ) ≤ denominator * 217 :=
          mul_le_mul_of_nonneg_left x_le denominator_positive.le
        nlinarith
      have x_upper : (x : ℚ) < 218 := by
        by_contra upper_not
        have x_ge : (218 : ℚ) ≤ x := le_of_not_gt upper_not
        have scaled_ge : denominator * 218 ≤ denominator * (x : ℚ) :=
          mul_le_mul_of_nonneg_left x_ge denominator_positive.le
        nlinarith
      have x_lower_nat : 217 < x := by exact_mod_cast x_lower
      have x_upper_nat : x < 218 := by exact_mod_cast x_upper
      omega

/-! ## Simultaneous `c` endpoint and defect -/

/-- Positive coefficient core for the shortest `0 | 2 | 1` bridge with a residue-zero `c`
endpoint, a `c` defect, and a residue-one `b` endpoint at deletion width three. -/
def cZeroCDefectBOneCore (L M x z : ℚ) : ℚ :=
  864 * (M - 3) * (1805 * L + 486 * M - 3263) * x * z +
    864 * (1805 * L + 3263 * M - 11594) * x +
    (21400527 * L * M - 59523021 * L + 13711802 * M ^ 2 -
      102411627 * M + 179150103) * z -
    3 * (19537767 * L - 34180949 * M + 80295864)

theorem cZeroCDefectBOneCore_pos
    (L M x z : ℚ) (twenty_seven_lt_M : 27 < M)
    (L_nonnegative : 0 ≤ L) (L_lt_M : L < M)
    (x_nonnegative : 0 ≤ x) (z_nonnegative : 0 ≤ z) :
    0 < cZeroCDefectBOneCore L M x z := by
  have M_positive : 0 < M := by linarith
  have scale_gap_positive : 0 < M - 3 := by linarith
  have xz_throat_positive : 0 < 1805 * L + 486 * M - 3263 := by
    nlinarith
  have x_coefficient_positive : 0 < 1805 * L + 3263 * M - 11594 := by
    nlinarith
  have Lz_nonnegative :
      0 ≤ L * (21400527 * M - 59523021) := by
    have factor_positive : 0 < 21400527 * M - 59523021 := by
      nlinarith
    positivity
  have M_sq_growth : 27 * M < M ^ 2 := by
    nlinarith [mul_pos M_positive (sub_pos.mpr twenty_seven_lt_M)]
  have scale_z_positive :
      0 < 13711802 * M ^ 2 - 102411627 * M + 179150103 := by
    nlinarith
  have z_coefficient_positive :
      0 < 21400527 * L * M - 59523021 * L + 13711802 * M ^ 2 -
        102411627 * M + 179150103 := by
    nlinarith
  have constant_throat_negative :
      19537767 * L - 34180949 * M + 80295864 < 0 := by
    nlinarith
  have xz_term_nonnegative :
      0 ≤ 864 * (M - 3) * (1805 * L + 486 * M - 3263) * x * z := by
    positivity
  have x_term_nonnegative :
      0 ≤ 864 * (1805 * L + 3263 * M - 11594) * x := by
    positivity
  have z_term_nonnegative :
      0 ≤ (21400527 * L * M - 59523021 * L + 13711802 * M ^ 2 -
        102411627 * M + 179150103) * z := by
    positivity
  unfold cZeroCDefectBOneCore
  nlinarith

/-- Exact determinant of the shortest `0 | 2 | 1` bridge with letters `c | c | b` at deletion
width three. -/
theorem bridge_cZero_cTwo_bOne_det
    (body : List TagLetter) (x y z : Nat) :
    (bridge 27
      (cAtom 27 (nearySideLowerC 3 body) (nearySideLowerCScale 3 body) (3 * z) *
        cAtom 27 (nearySideLowerC 3 body) (nearySideLowerCScale 3 body) (3 * x + 2) *
        bAtom 27 (3 * y + 1))).det =
      243 * y / 16 *
        cZeroCDefectBOneCore
          (nearySideLowerC 3 body) (nearySideLowerCScale 3 body) x z := by
  rw [cAtom_three_mul_matrix, cAtom_three_mul_add_two_matrix,
    bAtom_three_mul_add_one_matrix, Matrix.det_fin_two]
  norm_num [bridge, coreInput, coreOutput, Matrix.mul_apply, Fin.sum_univ_succ,
    cZeroCDefectBOneCore]
  ring

/-- No regular shortest `0 | 2 | 1` bad bridge with letters `c | c | b` closes at deletion
width three. -/
theorem bridge_cZero_cTwo_bOne_det_ne_zero
    (body : List TagLetter) (body_nonempty : body ≠ [])
    (x y z : Nat) (y_positive : 0 < y) :
    (bridge 27
      (cAtom 27 (nearySideLowerC 3 body) (nearySideLowerCScale 3 body) (3 * z) *
        cAtom 27 (nearySideLowerC 3 body) (nearySideLowerCScale 3 body) (3 * x + 2) *
        bAtom 27 (3 * y + 1))).det ≠ 0 := by
  rw [bridge_cZero_cTwo_bOne_det]
  let L : ℚ := nearySideLowerC 3 body
  let M : ℚ := nearySideLowerCScale 3 body
  have encoded_nonempty : tagEncode 3 body ≠ [] :=
    (tagEncode_eq_nil_iff 3 body).not.mpr body_nonempty
  have four_le : 4 ≤ (nearyLower 3 body (.rule .c)).length := by
    simp only [nearyLower, List.length_append, List.length_cons, List.length_nil]
    have encoded_length := List.length_pos_of_ne_nil encoded_nonempty
    omega
  have M_gt : 27 < M := by
    have power_lt : 27 < 3 ^ (nearyLower 3 body (.rule .c)).length := by
      have := Nat.pow_le_pow_right (by norm_num : 0 < 3) four_le
      norm_num at this ⊢
      omega
    dsimp [M]
    simp only [nearySideLowerCScale]
    exact_mod_cast power_lt
  have L_nonnegative : 0 ≤ L := by
    dsimp [L, nearySideLowerC]
    positivity
  have L_lt_M : L < M := by
    dsimp [L, M]
    simp only [nearySideLowerC, nearySideLowerCScale]
    exact_mod_cast ternaryCode_lt_pow_length (nearyLower 3 body (.rule .c))
  change 243 * y / 16 * cZeroCDefectBOneCore L M x z ≠ 0
  have core_positive : 0 < cZeroCDefectBOneCore L M x z :=
    cZeroCDefectBOneCore_pos L M x z M_gt L_nonnegative L_lt_M
      (by positivity) (by positivity)
  positivity

end MatrixMortality.ParabolicBlade
