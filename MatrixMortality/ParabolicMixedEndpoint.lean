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

end MatrixMortality.ParabolicBlade
