import MatrixMortality.ParabolicEvenBody

/-!
# The exceptional second-first-`b` cylinder

The first-`b` density attack on the residual phase-zero right-`c` bridge leaves one integral
endpoint on the body prefix `ccbccb`, at waits `(x, y, z) = (213, 465, 38)`.  Its required
suffix density lies strictly between the first-`b` cylinders beginning before and after the
second position.  This file records that final grammar gap.
-/

namespace MatrixMortality.ParabolicBlade

/-- Every physical tag word lies on one side of the open density gap between a first `b` in
its first two positions and a first `b` after them. -/
private theorem tagComplementCode_second_position_density_gap (body : List TagLetter) :
    13 * 3 ^ (tagEncode 3 body).length ≤ 243 * tagComplementCode body ∨
      2178 * tagComplementCode body < 39 * 3 ^ (tagEncode 3 body).length := by
  cases body with
  | nil =>
      right
      norm_num [tagComplementCode, tagEncode, spell, ternaryCode]
  | cons first tail =>
      cases first with
      | b =>
          left
          have density :
              13 * 3 ^ (tagEncode 3 (.b :: tail)).length ≤
                81 * tagComplementCode (.b :: tail) := by
            simpa using (tagComplementCode_first_b_density 0 tail).1
          omega
      | c =>
          cases tail with
          | nil =>
              right
              norm_num [tagComplementCode, tagEncode, spell, tagCode, ternaryCode,
                ternaryDigit]
          | cons second rest =>
              cases second with
              | b =>
                  left
                  simpa using (tagComplementCode_first_b_density 1 rest).1
              | c =>
                  right
                  let R : Nat := 3 ^ (tagEncode 3 rest).length
                  let D : Nat := tagComplementCode rest
                  have scale_positive : 1 ≤ R := by
                    dsimp [R]
                    exact one_le_pow₀ (by norm_num)
                  have density : 242 * D ≤ 39 * (R - 1) := by
                    dsimp [R, D]
                    exact tagComplementCode_global_bound rest
                  have complement_eq :
                      tagComplementCode (.c :: .c :: rest) = D := by
                    rw [tagComplementCode_cons_c, tagComplementCode_cons_c]
                  have scale_eq :
                      3 ^ (tagEncode 3 (.c :: .c :: rest)).length = 9 * R := by
                    dsimp [R]
                    simp only [List.length_append]
                    norm_num [tagCode, pow_add]
                    ring
                  rw [complement_eq, scale_eq]
                  omega

private theorem ccbccb_scale (rest : List TagLetter) :
    3 ^ (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)).length =
      4782969 * 3 ^ (tagEncode 3 rest).length := by
  rw [tagEncode_append, List.length_append, pow_add]
  norm_num [tagEncode, spell, tagCode]

private theorem ccbccb_complement (rest : List TagLetter) :
    tagComplementCode ([.c, .c, .b, .c, .c, .b] ++ rest) =
      85332 * 3 ^ (tagEncode 3 rest).length + tagComplementCode rest := by
  rw [tagComplementCode_append]
  have stem_complement :
      tagComplementCode [.c, .c, .b, .c, .c, .b] = 85332 := by decide
  rw [stem_complement]

/-- The lone integral endpoint of the second-first-`b` cylinder cannot close the primitive
core, independently of the remaining physical suffix. -/
theorem bZeroBDefectCOneCodeCore_ccbccb_ne_zero (rest : List TagLetter) :
    bZeroBDefectCOneCodeCore
        ((3 : ℤ) ^ (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)).length)
        (ternaryCode (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)))
        213 465 38 ≠ 0 := by
  let R : Nat := 3 ^ (tagEncode 3 rest).length
  let G : Nat := tagComplementCode rest
  let S : Nat := 3 ^ (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)).length
  let C : Nat := ternaryCode (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest))
  let D : Nat := tagComplementCode ([.c, .c, .b, .c, .c, .b] ++ rest)
  have scale_positive : 1 ≤ R := by
    dsimp [R]
    exact one_le_pow₀ (by norm_num)
  have scale_eq : S = 4782969 * R := by
    dsimp [S, R]
    exact ccbccb_scale rest
  have complement_eq : D = 85332 * R + G := by
    dsimp [D, R, G]
    exact ccbccb_complement rest
  have code_lt : C < S := by
    dsimp [C, S]
    exact ternaryCode_lt_pow_length
      (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest))
  have complement_nat : D = S - C - 1 := by
    rfl
  have coordinate_sum : C + D + 1 = S := by omega
  have code_eq : (C : ℤ) = (S : ℤ) - 1 - D := by
    have coordinate_sum_int : (C : ℤ) + D + 1 = S := by
      exact_mod_cast coordinate_sum
    omega
  intro core_zero
  have affine_zero :
      (-378928275417207 : ℤ) * R + 16135907225190852 * G +
          31917593029119 = 0 := by
    change bZeroBDefectCOneCodeCore (S : ℤ) (C : ℤ) 213 465 38 = 0 at core_zero
    rw [code_eq, bZeroBDefectCOneCodeCore_thin_decomposition] at core_zero
    unfold bZeroBDefectCOneWaitFactor bZeroBDefectCOneRootPencil
      bZeroBDefectCOneComplementCore at core_zero
    rw [scale_eq, complement_eq] at core_zero
    push_cast at core_zero
    norm_num at core_zero ⊢
    linear_combination core_zero
  have forced_lower : (39 : ℤ) * R < 2178 * G := by
    have R_positive : (0 : ℤ) < R := by exact_mod_cast scale_positive
    linarith [affine_zero]
  have forced_upper : (243 : ℤ) * G < 13 * R := by
    have R_positive : (0 : ℤ) < R := by exact_mod_cast scale_positive
    linarith [affine_zero]
  rcases tagComplementCode_second_position_density_gap rest with high | low
  · have high_int : (13 : ℤ) * R ≤ 243 * G := by
      exact_mod_cast high
    linarith
  · have low_int : (2178 : ℤ) * G < 39 * R := by
      exact_mod_cast low
    linarith

/-- The exceptional waits do not close the `b | b | c` bridge on any body with prefix
`ccbccb`. -/
theorem bridge_bZero_bTwo_cOne_det_ne_zero_of_ccbccb
    (rest : List TagLetter) :
    (bridge 27
      (bAtom 27 (3 * 38) * bAtom 27 (3 * 213 + 2) *
        cAtom 27 (nearySideLowerC 3 ([.c, .c, .b, .c, .c, .b] ++ rest))
          (nearySideLowerCScale 3 ([.c, .c, .b, .c, .c, .b] ++ rest))
          (3 * 465 + 1))).det ≠ 0 := by
  rw [bridge_bZero_bTwo_cOne_det]
  apply mul_ne_zero (by norm_num)
  intro rational_core_zero
  have power_cast :
      (((3 : Nat) ^ (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)).length : Nat) : ℚ) =
        (3 : ℚ) ^ (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)).length := by
    norm_num
  rw [← power_cast] at rational_core_zero
  have cast_integer_core :
      ((bZeroBDefectCOneCodeCore
        ((3 : ℤ) ^ (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)).length)
        (ternaryCode (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)))
        213 465 38 : ℤ) : ℚ) =
        bZeroBDefectCOneCodeCore
          (((3 : Nat) ^
            (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)).length : Nat) : ℚ)
          (ternaryCode (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)))
          213 465 38 := by
    norm_num [bZeroBDefectCOneCodeCore]
  have integer_core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℤ) ^ (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)).length)
        (ternaryCode (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)))
        213 465 38 = 0 := by
    have cast_zero :
        ((bZeroBDefectCOneCodeCore
          ((3 : ℤ) ^ (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)).length)
          (ternaryCode (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)))
          213 465 38 : ℤ) : ℚ) = 0 := by
      rw [cast_integer_core]
      exact rational_core_zero
    exact_mod_cast cast_zero
  exact bZeroBDefectCOneCodeCore_ccbccb_ne_zero rest integer_core_zero

end MatrixMortality.ParabolicBlade
