import MatrixMortality.ParabolicFirstBOnePhysical

/-!
# Analytic large-inner reduction at outer wait 211

The physical suffix balance contracts the unbounded inner-wait cylinder to two affine
inequalities. Exact grammar bounds then reduce every surviving zero to a short finite list of
first-`b` positions and middle waits. The generated certificate in
`ParabolicFirstBOneInnerCertificate` extinguishes that list.
-/

namespace MatrixMortality.ParabolicBlade

/-- Exact suffix equation after the first `b` is removed from an x=211 `cb` body. -/
def FirstBOneX211SuffixCore (body : List TagLetter) (H J B : ℤ) : Prop :=
  (tagComplementCode body : ℤ) * J =
    (3 : ℤ) ^ (tagEncode 3 body).length * H - B

/-- Removing a leading `c` triples the suffix coefficient. -/
theorem firstBOneX211SuffixCore_cons_c
    (body : List TagLetter) (H J B : ℤ)
    (core : FirstBOneX211SuffixCore (.c :: body) H J B) :
    FirstBOneX211SuffixCore body (3 * H) J B := by
  unfold FirstBOneX211SuffixCore at core ⊢
  rw [tagComplementCode_cons_c] at core
  have scale_eq :
      (3 : ℤ) ^ (tagEncode 3 (.c :: body)).length =
        3 * (3 : ℤ) ^ (tagEncode 3 body).length := by
    simp [tagEncode_cons, tagCode, pow_add, mul_comm]
  rw [scale_eq] at core
  linear_combination core

/-- Removing a leading `b` applies the exact affine coefficient transition. -/
theorem firstBOneX211SuffixCore_cons_b
    (body : List TagLetter) (H J B : ℤ)
    (core : FirstBOneX211SuffixCore (.b :: body) H J B) :
    FirstBOneX211SuffixCore body (243 * H - 39 * J) J B := by
  unfold FirstBOneX211SuffixCore at core ⊢
  rw [tagComplementCode_cons_b] at core
  have scale_eq :
      (3 : ℤ) ^ (tagEncode 3 (.b :: body)).length =
        243 * (3 : ℤ) ^ (tagEncode 3 body).length := by
    simp [tagEncode_cons, tagCode, pow_add]
    ring
  rw [scale_eq] at core
  push_cast at core ⊢
  linear_combination core

/-- A nonpositive suffix coefficient cannot balance positive finite correction. -/
theorem firstBOneX211SuffixCore_false_of_nonpositive
    (body : List TagLetter) (H J B : ℤ) (J_positive : 0 < J)
    (B_positive : 0 < B) (H_nonpositive : H ≤ 0)
    (core : FirstBOneX211SuffixCore body H J B) : False := by
  unfold FirstBOneX211SuffixCore at core
  have complement_nonnegative : (0 : ℤ) ≤ tagComplementCode body := by positivity
  have scale_positive : (0 : ℤ) < (3 : ℤ) ^ (tagEncode 3 body).length := by positivity
  have left_nonnegative : (0 : ℤ) ≤ (tagComplementCode body : ℤ) * J :=
    mul_nonneg complement_nonnegative J_positive.le
  have scale_term_nonpositive :
      (3 : ℤ) ^ (tagEncode 3 body).length * H ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos scale_positive.le H_nonpositive
  nlinarith

/-- The global complement bound excludes coefficients above its closed density wall. -/
theorem firstBOneX211SuffixCore_false_of_global
    (body : List TagLetter) (H J B : ℤ) (J_positive : 0 < J)
    (B_positive : 0 < B)
    (coefficient_large : 242 * H - 39 * J > 242 * B)
    (core : FirstBOneX211SuffixCore body H J B) : False := by
  unfold FirstBOneX211SuffixCore at core
  have bound := tagComplementCode_global_bound body
  have bound_int :
      (242 : ℤ) * tagComplementCode body ≤
        39 * ((3 : ℤ) ^ (tagEncode 3 body).length - 1) := by
    have scale_positive : 1 ≤ 3 ^ (tagEncode 3 body).length := one_le_pow₀ (by norm_num)
    exact_mod_cast bound
  have scaled_bound := mul_le_mul_of_nonneg_right bound_int J_positive.le
  have scale_one : (1 : ℤ) ≤ (3 : ℤ) ^ (tagEncode 3 body).length :=
    one_le_pow₀ (by norm_num)
  have coefficient_gap : 0 < 242 * H - 39 * J - 242 * B := by linarith
  have coefficient_positive : 0 < 242 * H - 39 * J := by nlinarith
  have amplification :
      242 * B < (3 : ℤ) ^ (tagEncode 3 body).length * (242 * H - 39 * J) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr scale_one) coefficient_positive.le]
  nlinarith [scaled_bound]

/-- Either side of the first-`b` position separator contradicts the displayed open gap. -/
theorem firstBOneX211SuffixCore_false_of_gap
    (k : Nat) (body : List TagLetter) (H J B : ℤ) (J_positive : 0 < J)
    (B_positive : 0 < B)
    (low_impossible : 242 * (3 : ℤ) ^ (k + 1) * H - 39 * J >
      242 * (3 : ℤ) ^ (k + 1) * B)
    (high_impossible : 81 * (3 : ℤ) ^ k * H - 13 * J < 0)
    (core : FirstBOneX211SuffixCore body H J B) : False := by
  unfold FirstBOneX211SuffixCore at core
  rcases tagComplementCode_first_b_position_gap k body with high | low
  · have high_int :
        (13 : ℤ) * (3 : ℤ) ^ (tagEncode 3 body).length ≤
          81 * (3 : ℤ) ^ k * tagComplementCode body := by
      exact_mod_cast high
    have scaled := mul_le_mul_of_nonneg_right high_int J_positive.le
    have scale_positive : (0 : ℤ) < (3 : ℤ) ^ (tagEncode 3 body).length := by
      positivity
    nlinarith [mul_pos scale_positive (neg_pos.mpr high_impossible)]
  · have low_int :
        (242 : ℤ) * (3 : ℤ) ^ (k + 1) * tagComplementCode body <
          39 * (3 : ℤ) ^ (tagEncode 3 body).length := by
      exact_mod_cast low
    have scaled := mul_lt_mul_of_pos_right low_int J_positive
    have scale_one : (1 : ℤ) ≤ (3 : ℤ) ^ (tagEncode 3 body).length :=
      one_le_pow₀ (by norm_num)
    have coefficient_gap :
        0 < 242 * (3 : ℤ) ^ (k + 1) * H - 39 * J -
          242 * (3 : ℤ) ^ (k + 1) * B := by
      linarith
    have coefficient_positive :
        0 < 242 * (3 : ℤ) ^ (k + 1) * H - 39 * J := by
      have power_positive : (0 : ℤ) < (3 : ℤ) ^ (k + 1) := pow_pos (by norm_num) _
      have right_positive :
          (0 : ℤ) < 242 * (3 : ℤ) ^ (k + 1) * B := by
        positivity
      linarith
    have amplification :
        242 * (3 : ℤ) ^ (k + 1) * B <
          (3 : ℤ) ^ (tagEncode 3 body).length *
            (242 * (3 : ℤ) ^ (k + 1) * H - 39 * J) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr scale_one) coefficient_positive.le]
    have core_scaled :
        242 * (3 : ℤ) ^ (k + 1) * tagComplementCode body * J =
          242 * (3 : ℤ) ^ (k + 1) *
            ((3 : ℤ) ^ (tagEncode 3 body).length * H - B) := by
      linear_combination (242 * (3 : ℤ) ^ (k + 1)) * core
    nlinarith

/-- The empty suffix is impossible whenever its coefficient differs from the correction. -/
theorem firstBOneX211SuffixCore_false_of_nil
    (H J B : ℤ) (different : H ≠ B)
    (core : FirstBOneX211SuffixCore [] H J B) : False := by
  norm_num [FirstBOneX211SuffixCore, tagComplementCode, tagEncode, spell, tagCode,
    ternaryCode, ternaryDigit] at core
  apply different
  nlinarith

/-- Root suffix coefficient after `j` leading `c` letters and the first `b`. -/
def firstBOneX211SuffixH (j y z : Nat) : ℤ :=
  243 * (3 : ℤ) ^ j *
      (firstBOneX211A y z - 39 * firstBOneX211J y z) -
    39 * firstBOneX211J y z

private theorem inner_replicate_c_length (j : Nat) :
    (tagEncode 3 (List.replicate j .c)).length = j := by
  induction j with
  | zero => rfl
  | succ j induction =>
      rw [List.replicate_succ, tagEncode_cons, List.length_append]
      simp only [tagCode, List.length_singleton, induction]
      omega

/-- A physical x=211 core zero and first-`b` decomposition force the exact suffix equation. -/
theorem firstBOneX211SuffixCore_of_core_zero
    (j : Nat) (tail rest : List TagLetter) (y z : Nat)
    (first_b : tail = List.replicate j .c ++ .b :: rest)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
        (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) 211 y z = 0) :
    FirstBOneX211SuffixCore rest (firstBOneX211SuffixH j y z)
      (firstBOneX211J y z) (firstBOneX211B y z) := by
  let R : Nat := 3 ^ (tagEncode 3 rest).length
  let G : Nat := tagComplementCode rest
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E : Nat := tagComplementCode tail
  have scale_eq : T = 3 ^ j * 243 * R := by
    dsimp [T, R]
    rw [first_b, tagEncode_append, List.length_append, inner_replicate_c_length,
      tagEncode_cons, List.length_append, pow_add, pow_add]
    norm_num [tagCode]
    ring
  have complement_eq : E = 39 * R + G := by
    dsimp [E, R, G]
    rw [first_b, tagComplementCode_replicate_c_append, tagComplementCode_cons_b]
  have balance := firstBOneX211_core_balance tail y z core_zero
  change ((39 * T + E : Nat) : ℤ) * firstBOneX211J y z =
    (T : ℤ) * firstBOneX211A y z - firstBOneX211B y z at balance
  rw [scale_eq, complement_eq] at balance
  dsimp [R, G] at balance
  unfold FirstBOneX211SuffixCore firstBOneX211SuffixH
  linear_combination balance

/-- Two affine inequalities forced by a physical suffix core. -/
def FirstBOneX211LargeInnerEnvelope (j y z : Nat) : Prop :=
  let p : ℤ := 3 ^ j
  let K : ℤ :=
    242 * p * (firstBOneX211A y z - 39 * firstBOneX211J y z) -
      39 * firstBOneX211J y z
  0 < firstBOneX211SuffixH j y z ∧ 243 * K ≤ 242 * firstBOneX211B y z

/-- Positivity and the global complement wall contract every physical suffix equation to the
large-inner envelope. -/
theorem firstBOneX211LargeInnerEnvelope_of_suffix_core
    (j : Nat) (body : List TagLetter) (y z : Nat) (y_positive : 2 ≤ y)
    (core : FirstBOneX211SuffixCore body (firstBOneX211SuffixH j y z)
      (firstBOneX211J y z) (firstBOneX211B y z)) :
    FirstBOneX211LargeInnerEnvelope j y z := by
  let p : ℤ := 3 ^ j
  let R : ℤ := (3 : ℤ) ^ (tagEncode 3 body).length
  let G : ℤ := tagComplementCode body
  let J : ℤ := firstBOneX211J y z
  let B : ℤ := firstBOneX211B y z
  let H : ℤ := firstBOneX211SuffixH j y z
  let K : ℤ := 242 * p * (firstBOneX211A y z - 39 * firstBOneX211J y z) - 39 * J
  have R_positive : 0 < R := by dsimp [R]; positivity
  have R_one : 1 ≤ R := by dsimp [R]; exact one_le_pow₀ (by norm_num)
  have G_nonnegative : 0 ≤ G := by dsimp [G]; positivity
  have J_positive : 0 < J := by
    dsimp [J]
    unfold firstBOneX211J
    positivity
  have B_positive : 0 < B := by
    have y_positive_int : (2 : ℤ) ≤ y := by exact_mod_cast y_positive
    have wait_positive : (0 : ℤ) < 8 * y - 9 := by omega
    dsimp [B]
    unfold firstBOneX211B firstBOneX211Q
    positivity
  unfold FirstBOneX211SuffixCore at core
  change G * J = R * H - B at core
  have left_nonnegative : 0 ≤ G * J := mul_nonneg G_nonnegative J_positive.le
  have RH_positive : 0 < R * H := by nlinarith
  have H_positive : 0 < H := by
    by_contra H_not_positive
    have H_nonpositive : H ≤ 0 := le_of_not_gt H_not_positive
    have product_nonpositive : R * H ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos R_positive.le H_nonpositive
    linarith
  have bound := tagComplementCode_global_bound body
  have bound_int : 242 * G ≤ 39 * (R - 1) := by
    have scale_nat_one : 1 ≤ 3 ^ (tagEncode 3 body).length := one_le_pow₀ (by norm_num)
    have cast_bound :
        ((242 * tagComplementCode body : Nat) : ℤ) ≤
          ((39 * (3 ^ (tagEncode 3 body).length - 1) : Nat) : ℤ) := by
      exact_mod_cast bound
    norm_num only [Nat.cast_mul] at cast_bound
    rw [Nat.cast_sub scale_nat_one] at cast_bound
    simpa [G, R] using cast_bound
  have scaled_bound := mul_le_mul_of_nonneg_right bound_int J_positive.le
  have core_scaled : 242 * G * J = 242 * (R * H - B) := by
    linear_combination 242 * core
  have raw_upper : R * (242 * H - 39 * J) ≤ 242 * B - 39 * J := by
    nlinarith
  have coefficient_identity : 242 * H - 39 * J = 243 * K := by
    dsimp [H, J, K, p]
    unfold firstBOneX211SuffixH
    ring
  rw [coefficient_identity] at raw_upper
  have base_upper : 243 * K ≤ 242 * B := by
    by_cases K_nonnegative : 0 ≤ K
    · have amplified := mul_le_mul_of_nonneg_right R_one (by positivity : 0 ≤ 243 * K)
      nlinarith
    · nlinarith
  unfold FirstBOneX211LargeInnerEnvelope
  change 0 < H ∧ 243 * K ≤ 242 * B
  exact ⟨H_positive, base_upper⟩

/-- Above the inner-wait threshold, the large-inner envelope forces the first suffix `b` to
occur before position thirteen. -/
theorem firstBOneX211_position_lt_thirteen_of_large_inner_envelope
    (j y z : Nat) (y_lower : 22529 ≤ y) (y_upper : y ≤ 51767)
    (z_large : 3 ^ 13 ≤ z)
    (envelope : FirstBOneX211LargeInnerEnvelope j y z) :
    j < 13 := by
  by_contra position_not_bounded
  have position_large : 13 ≤ j := by omega
  let p : ℤ := 3 ^ j
  let F : ℤ := firstBOneX211A y z - 39 * firstBOneX211J y z
  have p_lower : (3 : ℤ) ^ 13 ≤ p := by
    dsimp [p]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 3) position_large
  have J_positive : (0 : ℤ) < firstBOneX211J y z := by
    unfold firstBOneX211J
    positivity
  have B_positive : (0 : ℤ) < firstBOneX211B y z := by
    have y_positive : 2 ≤ y := by omega
    have y_positive_int : (2 : ℤ) ≤ y := by exact_mod_cast y_positive
    have wait_positive : (0 : ℤ) < 8 * y - 9 := by omega
    unfold firstBOneX211B firstBOneX211Q
    positivity
  unfold FirstBOneX211LargeInnerEnvelope at envelope
  rcases envelope with ⟨H_positive, K_upper⟩
  change 0 < 243 * p * F - 39 * firstBOneX211J y z at H_positive
  change
    243 * (242 * p * F - 39 * firstBOneX211J y z) ≤
      242 * firstBOneX211B y z at K_upper
  have F_positive : 0 < F := by
    by_contra F_not_positive
    have F_nonpositive : F ≤ 0 := le_of_not_gt F_not_positive
    have product_nonpositive : 243 * p * F ≤ 0 := by
      have coefficient_nonnegative : (0 : ℤ) ≤ 243 * p := by positivity
      exact mul_nonpos_of_nonneg_of_nonpos coefficient_nonnegative F_nonpositive
    nlinarith
  have pF_lower : (3 : ℤ) ^ 13 * F ≤ p * F :=
    mul_le_mul_of_nonneg_right p_lower F_positive.le
  have f_upper :
      242 * (3 : ℤ) ^ 13 * F ≤
        firstBOneX211B y z + 39 * firstBOneX211J y z := by
    nlinarith
  have y_cases :=
    firstBOneX211_large_position_y_cases y z y_lower y_upper F_positive f_upper
  dsimp [F] at f_upper
  rcases y_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J] at f_upper <;>
    nlinarith

/-- Every large-inner envelope lies above the global middle-wait floor. -/
theorem firstBOneX211_y_lower_of_large_inner_envelope
    (j y z : Nat) (envelope : FirstBOneX211LargeInnerEnvelope j y z) :
    22529 ≤ y := by
  let p : ℤ := 3 ^ j
  have p_positive : 0 < p := by dsimp [p]; positivity
  have J_positive : (0 : ℤ) < firstBOneX211J y z := by
    unfold firstBOneX211J
    positivity
  have H_positive := envelope.1
  change 0 < 243 * p *
    (firstBOneX211A y z - 39 * firstBOneX211J y z) -
      39 * firstBOneX211J y z at H_positive
  have scaled_positive :
      0 < p * (81 * firstBOneX211A y z - 3159 * firstBOneX211J y z) := by
    nlinarith
  have root_positive :
      0 < 81 * firstBOneX211A y z - 3159 * firstBOneX211J y z := by
    by_contra root_not_positive
    have root_nonpositive :
        81 * firstBOneX211A y z - 3159 * firstBOneX211J y z ≤ 0 :=
      le_of_not_gt root_not_positive
    have product_nonpositive :
        p * (81 * firstBOneX211A y z - 3159 * firstBOneX211J y z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos p_positive.le root_nonpositive
    linarith
  by_contra wait_not_bounded
  have wait_upper_int : (y : ℤ) ≤ 22528 := by omega
  have z_nonnegative : (0 : ℤ) ≤ z := by positivity
  have coefficient_nonpositive :
      (18757162068480 : ℤ) * y - 422575327245605580 ≤ 0 := by
    nlinarith
  have coefficient_product_nonpositive :
      ((18757162068480 : ℤ) * y - 422575327245605580) * z ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg coefficient_nonpositive z_nonnegative
  have polynomial_identity :
      81 * firstBOneX211A y z - 3159 * firstBOneX211J y z =
        ((18757162068480 : ℤ) * y - 422575327245605580) * z -
          934481760336 * y - 39500761802903613 := by
    unfold firstBOneX211A firstBOneX211Q firstBOneX211J
    ring
  rw [polynomial_identity] at root_positive
  nlinarith

end MatrixMortality.ParabolicBlade
