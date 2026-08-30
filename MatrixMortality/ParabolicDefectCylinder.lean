import MatrixMortality.ParabolicDefect

/-!
# Opposite c-defect cylinder exclusion

The remaining shortest `1 | 2 | 0` bridge determinant is an affine weighted average of two
nearby roots. The leading `c`-run of the tag body places both roots in one of five rational
cylinders, none of which contains a compatible pair of natural waits.
-/

namespace MatrixMortality.ParabolicBlade

private theorem tagEncode_c_run (k : Nat) :
    tagEncode 3 (List.replicate k .c) = List.replicate k true := by
  induction k with
  | zero => rfl
  | succ k induction =>
      rw [List.replicate_succ, tagEncode_cons, induction]
      simp [tagCode, List.replicate_succ]

private theorem tagEncode_c_run_b (k : Nat) (tail : List TagLetter) :
    tagEncode 3 (List.replicate k .c ++ .b :: tail) =
      List.replicate k true ++ [true, false, false, false, true] ++ tagEncode 3 tail := by
  rw [tagEncode_append, tagEncode_c_run]
  simp [tagCode]

private theorem ternaryCode_true_run (k : Nat) :
    ternaryCode (List.replicate k true) = 3 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, ternaryCode_cons, ih]
      simp only [List.length_replicate, ternaryDigit]
      omega

private theorem c_run_code (k : Nat) :
    (ternaryCode (tagEncode 3 (List.replicate k .c)) : ℚ) = (3 : ℚ) ^ k - 1 := by
  rw [tagEncode_c_run, ternaryCode_true_run]
  have power_positive : 1 ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  rw [Nat.cast_sub power_positive]
  push_cast
  rfl

private theorem ternaryCode_c_run_b (k : Nat) (tail : List TagLetter) :
    ternaryCode (tagEncode 3 (List.replicate k .c ++ .b :: tail)) =
      3 ^ (tagEncode 3 tail).length * (243 * 3 ^ k - 40) +
        ternaryCode (tagEncode 3 tail) := by
  rw [tagEncode_c_run_b, ternaryCode_append, ternaryCode_append,
    ternaryCode_true_run]
  simp only [List.length_cons, List.length_nil]
  have b_code : ternaryCode [true, false, false, false, true] = 203 := by decide
  rw [b_code]
  have power_positive : 1 ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have prefix_code : 243 * (3 ^ k - 1) + 203 = 243 * 3 ^ k - 40 := by omega
  norm_num only [Nat.zero_add, Nat.reduceAdd, Nat.reducePow]
  rw [prefix_code]

private theorem tagEncode_c_run_b_length (k : Nat) (tail : List TagLetter) :
    (tagEncode 3 (List.replicate k .c ++ .b :: tail)).length =
      k + 5 + (tagEncode 3 tail).length := by
  rw [tagEncode_c_run_b]
  simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]

private theorem c_run_b_coordinates (k : Nat) (tail : List TagLetter) :
    let R : ℚ := 3 ^ (tagEncode 3 tail).length
    let T : ℚ := ternaryCode (tagEncode 3 tail)
    let S : ℚ := 3 ^ (tagEncode 3 (List.replicate k .c ++ .b :: tail)).length
    let C : ℚ := ternaryCode (tagEncode 3 (List.replicate k .c ++ .b :: tail))
    C = R * (243 * 3 ^ k - 40) + T ∧
      S = 243 * 3 ^ k * R ∧ 0 ≤ T ∧ T + 1 ≤ R := by
  dsimp only
  constructor
  · have power_positive : 1 ≤ 3 ^ k := one_le_pow₀ (by norm_num)
    have forty_le : 40 ≤ 243 * 3 ^ k := by omega
    have cast_code := congrArg (fun n : Nat => (n : ℚ)) (ternaryCode_c_run_b k tail)
    norm_num [Nat.cast_sub forty_le] at cast_code ⊢
    exact cast_code
  constructor
  · rw [tagEncode_c_run_b_length, pow_add, pow_add]
    norm_num
    ring
  constructor
  · positivity
  · exact_mod_cast Nat.succ_le_iff.mpr (ternaryCode_lt_pow_length (tagEncode 3 tail))

private def oppositeCScale (M : ℚ) : ℚ := 1699776 * (M - 3)

private def oppositeCBase (L M : ℚ) : ℚ :=
  164500347 * L - 55585393 * M - 2843496

private def oppositeCCrest (L M : ℚ) : ℚ :=
  oppositeCBase L M + 247806 * (M - 3)

private theorem side_coordinates (body : List TagLetter) :
    let S : ℚ := 3 ^ (tagEncode 3 body).length
    let C : ℚ := ternaryCode (tagEncode 3 body)
    nearySideLowerC 3 body = 18 * S + 9 * C + 7 ∧
      nearySideLowerCScale 3 body = 27 * S := by
  dsimp only
  constructor
  · rw [nearySideLowerC_eq_nine_mul_add_seven]
    simp [ternaryCode_cons, ternaryDigit]
    ring
  · rw [nearySideLowerCScale_eq_nine_mul, pow_succ]
    ring

private theorem c_run_b_side_coordinates (k : Nat) (tail : List TagLetter) :
    let R : ℚ := 3 ^ (tagEncode 3 tail).length
    let T : ℚ := ternaryCode (tagEncode 3 tail)
    let body := List.replicate k .c ++ .b :: tail
    nearySideLowerC 3 body =
        18 * (243 * 3 ^ k * R) + 9 * (R * (243 * 3 ^ k - 40) + T) + 7 ∧
      nearySideLowerCScale 3 body = 27 * (243 * 3 ^ k * R) ∧
      0 ≤ T ∧ T + 1 ≤ R := by
  dsimp only
  rcases c_run_b_coordinates k tail with
    ⟨code_eq, scale_eq, code_nonnegative, code_succ_le_scale⟩
  rcases side_coordinates (List.replicate k .c ++ .b :: tail) with
    ⟨lower_eq, lower_scale_eq⟩
  rw [code_eq, scale_eq] at lower_eq
  rw [scale_eq] at lower_scale_eq
  exact ⟨lower_eq, lower_scale_eq, code_nonnegative, code_succ_le_scale⟩

private theorem b_zero_crosses_every_suffix (body : List TagLetter) :
    388498986 * (3 : ℚ) ^ (tagEncode 3 body).length <
      493501041 * ternaryCode (tagEncode 3 body) + 482952823 := by
  induction body with
  | nil => norm_num
  | cons head tail induction =>
      cases head with
      | b =>
          rcases c_run_b_coordinates 0 tail with
            ⟨code_eq, scale_eq, code_nonnegative, code_succ_le_scale⟩
          norm_num at code_eq scale_eq
          have whole_code_eq :
              (ternaryCode (tagEncode 3 (.b :: tail)) : ℚ) =
                3 ^ (tagEncode 3 tail).length * 203 + ternaryCode (tagEncode 3 tail) := by
            simpa [tagEncode_cons] using code_eq
          have whole_scale_eq :
              (3 : ℚ) ^ (tagEncode 3 (.b :: tail)).length =
                243 * 3 ^ (tagEncode 3 tail).length := by
            rw [show (tagEncode 3 (.b :: tail)).length =
              5 + (tagEncode 3 tail).length by
                simp [tagEncode_cons, tagCode]
                omega]
            exact scale_eq
          nlinarith
      | c =>
          have code_eq :
              (ternaryCode (tagEncode 3 (.c :: tail)) : ℚ) =
                2 * (3 : ℚ) ^ (tagEncode 3 tail).length +
                  ternaryCode (tagEncode 3 tail) := by
            simp only [tagEncode_cons, tagCode, List.singleton_append]
            rw [ternaryCode_cons]
            simp only [ternaryDigit]
            push_cast
            ring
          have scale_eq :
              (3 : ℚ) ^ (tagEncode 3 (.c :: tail)).length =
                3 * 3 ^ (tagEncode 3 tail).length := by
            simp only [tagEncode_cons, tagCode, List.singleton_append, List.length_cons,
              pow_succ]
            ring
          nlinarith

private theorem c_run_b_zero_bounds (tail : List TagLetter) :
    let body := .b :: tail
    let L := nearySideLowerC 3 body
    let M := nearySideLowerCScale 3 body
    let A := oppositeCScale M
    let B₀ := oppositeCBase L M
    let B₁ := oppositeCCrest L M
    58 * A < B₀ ∧ 58 * A < B₁ ∧ B₀ < 60 * A ∧ B₁ < 60 * A ∧
      B₀ < 59 * A ∧ 59 * A < B₁ ∧ 9 * 59 * A < B₀ + 8 * B₁ := by
  dsimp only
  rcases c_run_b_side_coordinates 0 tail with
    ⟨lower_eq, lower_scale_eq, code_nonnegative, code_succ_le_scale⟩
  norm_num at lower_eq lower_scale_eq
  have crosses := b_zero_crosses_every_suffix tail
  simp only [oppositeCScale, oppositeCBase, oppositeCCrest]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem c_run_b_one_bounds (tail : List TagLetter) :
    let body := List.replicate 1 .c ++ .b :: tail
    let L := nearySideLowerC 3 body
    let M := nearySideLowerCScale 3 body
    let A := oppositeCScale M
    let B₀ := oppositeCBase L M
    let B₁ := oppositeCCrest L M
    62 * A < B₀ ∧ 62 * A < B₁ ∧ B₀ < 63 * A ∧ B₁ < 63 * A := by
  dsimp only
  rcases c_run_b_side_coordinates 1 tail with
    ⟨lower_eq, lower_scale_eq, code_nonnegative, code_succ_le_scale⟩
  norm_num at lower_eq lower_scale_eq
  simp only [List.replicate_succ, List.replicate_zero, List.nil_append,
    List.cons_append] at lower_eq lower_scale_eq ⊢
  simp only [oppositeCScale, oppositeCBase, oppositeCCrest]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem c_run_b_two_bounds (tail : List TagLetter) :
    let body := List.replicate 2 .c ++ .b :: tail
    let L := nearySideLowerC 3 body
    let M := nearySideLowerCScale 3 body
    let A := oppositeCScale M
    let B₀ := oppositeCBase L M
    let B₁ := oppositeCCrest L M
    63 * A < B₀ ∧ 63 * A < B₁ ∧ B₀ < 64 * A ∧ B₁ < 64 * A := by
  dsimp only
  rcases c_run_b_side_coordinates 2 tail with
    ⟨lower_eq, lower_scale_eq, code_nonnegative, code_succ_le_scale⟩
  norm_num at lower_eq lower_scale_eq
  simp only [oppositeCScale, oppositeCBase, oppositeCCrest]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem c_run_b_three_bounds (tail : List TagLetter) :
    let body := List.replicate 3 .c ++ .b :: tail
    let L := nearySideLowerC 3 body
    let M := nearySideLowerCScale 3 body
    let A := oppositeCScale M
    let B₀ := oppositeCBase L M
    let B₁ := oppositeCCrest L M
    63 * A < B₀ ∧ 63 * A < B₁ ∧ B₀ < 65 * A ∧ B₁ < 65 * A ∧
      B₀ < 64 * A ∧ 64 * A < B₁ ∧ 9 * 64 * A < B₀ + 8 * B₁ := by
  dsimp only
  rcases c_run_b_side_coordinates 3 tail with
    ⟨lower_eq, lower_scale_eq, code_nonnegative, code_succ_le_scale⟩
  norm_num at lower_eq lower_scale_eq
  simp only [oppositeCScale, oppositeCBase, oppositeCCrest]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem c_run_b_long_bounds (k : Nat) (tail : List TagLetter) (four_le : 4 ≤ k) :
    let body := List.replicate k .c ++ .b :: tail
    let L := nearySideLowerC 3 body
    let M := nearySideLowerCScale 3 body
    let A := oppositeCScale M
    let B₀ := oppositeCBase L M
    let B₁ := oppositeCCrest L M
    64 * A < B₀ ∧ 64 * A < B₁ ∧ B₀ < 65 * A ∧ B₁ < 65 * A := by
  dsimp only
  rcases c_run_b_side_coordinates k tail with
    ⟨lower_eq, lower_scale_eq, code_nonnegative, code_succ_le_scale⟩
  have power_ge : (81 : ℚ) ≤ 3 ^ k := by
    have power_ge_nat : 3 ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) four_le
    exact_mod_cast power_ge_nat
  have power_excess_nonnegative :
      0 ≤ ((3 : ℚ) ^ k - 81) * 3 ^ (tagEncode 3 tail).length := by positivity
  simp only [oppositeCScale, oppositeCBase, oppositeCCrest]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem c_run_bounds (k : Nat) (k_positive : 0 < k) :
    let body := List.replicate k .c
    let L := nearySideLowerC 3 body
    let M := nearySideLowerCScale 3 body
    let A := oppositeCScale M
    let B₀ := oppositeCBase L M
    let B₁ := oppositeCCrest L M
    64 * A < B₀ ∧ 64 * A < B₁ ∧ B₀ < 65 * A ∧ B₁ < 65 * A := by
  dsimp only
  have code_eq := c_run_code k
  have scale_eq :
      (3 : ℚ) ^ (tagEncode 3 (List.replicate k .c)).length = 3 ^ k := by
    rw [tagEncode_c_run]
    simp
  rcases side_coordinates (List.replicate k .c) with ⟨lower_eq, lower_scale_eq⟩
  rw [code_eq, scale_eq] at lower_eq
  rw [scale_eq] at lower_scale_eq
  have power_ge : (3 : ℚ) ≤ 3 ^ k := by
    have power_ge_nat : 3 ^ 1 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) k_positive
    exact_mod_cast power_ge_nat
  simp only [oppositeCScale, oppositeCBase, oppositeCCrest]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem oppositeCScale_positive (body : List TagLetter) (body_nonempty : body ≠ []) :
    0 < oppositeCScale (nearySideLowerCScale 3 body) := by
  rcases side_coordinates body with ⟨_, scale_eq⟩
  have encoded_nonempty : tagEncode 3 body ≠ [] :=
    (tagEncode_eq_nil_iff 3 body).not.mpr body_nonempty
  have encoded_length_positive : 0 < (tagEncode 3 body).length :=
    List.length_pos_of_ne_nil encoded_nonempty
  have power_gt_one : (1 : ℚ) < 3 ^ (tagEncode 3 body).length :=
    one_lt_pow₀ (by norm_num) encoded_length_positive.ne'
  simp only [oppositeCScale]
  nlinarith

private theorem tagWord_c_run_or_c_run_b (body : List TagLetter) :
    (∃ k, body = List.replicate k .c) ∨
      ∃ k tail, body = List.replicate k .c ++ .b :: tail := by
  induction body with
  | nil => exact Or.inl ⟨0, rfl⟩
  | cons head tail induction =>
      cases head with
      | b => exact Or.inr ⟨0, tail, rfl⟩
      | c =>
          rcases induction with ⟨k, rfl⟩ | ⟨k, rest, rfl⟩
          · exact Or.inl ⟨k + 1, by simp [List.replicate_succ]⟩
          · exact Or.inr ⟨k + 1, rest, by simp [List.replicate_succ]⟩

private theorem oppositeC_incidence_eq (L M : ℚ) (x y : Nat) :
    1699776 * (M - 3) * (8 * y + 1) * x -
        (1316002776 * L - 442700696 * M - 28695312) * y -
        (164500347 * L - 55585393 * M - 2843496) =
      oppositeCScale M * (8 * y + 1) * x -
        8 * oppositeCCrest L M * y - oppositeCBase L M := by
  simp only [oppositeCScale, oppositeCCrest, oppositeCBase]
  ring

private theorem weighted_root_between_consecutive_ne_zero
    (A B₀ B₁ : ℚ) (x y n : Nat) (A_positive : 0 < A)
    (lower_base : n * A < B₀) (lower_crest : n * A < B₁)
    (base_upper : B₀ < (n + 1) * A) (crest_upper : B₁ < (n + 1) * A) :
    A * (8 * y + 1) * x - 8 * B₁ * y - B₀ ≠ 0 := by
  intro zero
  have y_nonnegative : (0 : ℚ) ≤ y := by positivity
  have lower_tail : 0 ≤ 8 * (y : ℚ) * (B₁ - n * A) := by positivity
  have upper_tail : 0 ≤ 8 * (y : ℚ) * ((n + 1) * A - B₁) := by positivity
  have lower_lt : (n : ℚ) < x := by nlinarith
  have upper_lt : (x : ℚ) < n + 1 := by nlinarith
  have lower_lt_nat : n < x := by exact_mod_cast lower_lt
  have upper_lt_nat : x < n + 1 := by exact_mod_cast upper_lt
  omega

private theorem weighted_root_single_candidate_ne_zero
    (A B₀ B₁ : ℚ) (x y n : Nat) (A_positive : 0 < A)
    (lower_base : n * A < B₀) (lower_crest : n * A < B₁)
    (crest_upper : B₁ < (n + 2) * A)
    (base_below_candidate : B₀ < (n + 1) * A)
    (candidate_below_crest : (n + 1) * A < B₁)
    (candidate_shallow : 9 * (n + 1) * A < B₀ + 8 * B₁) :
    A * (8 * y + 1) * x - 8 * B₁ * y - B₀ ≠ 0 := by
  intro zero
  have y_nonnegative : (0 : ℚ) ≤ y := by positivity
  have lower_tail : 0 ≤ 8 * (y : ℚ) * (B₁ - n * A) := by positivity
  have upper_tail : 0 ≤ 8 * (y : ℚ) * ((n + 2) * A - B₁) := by positivity
  have lower_lt : (n : ℚ) < x := by nlinarith
  have upper_lt : (x : ℚ) < n + 2 := by nlinarith
  have lower_lt_nat : n < x := by exact_mod_cast lower_lt
  have upper_lt_nat : x < n + 2 := by exact_mod_cast upper_lt
  have x_eq : x = n + 1 := by omega
  subst x
  norm_num [Nat.cast_add, Nat.cast_one] at zero
  have base_gap_positive : 0 < (n + 1) * A - B₀ := by nlinarith
  have crest_gap_positive : 0 < B₁ - (n + 1) * A := by nlinarith
  by_cases y_zero : y = 0
  · subst y
    norm_num at zero
    nlinarith
  · have y_at_least_one : (1 : ℚ) ≤ y := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr y_zero)
    have delta_eq :
        (n + 1) * A - B₀ = 8 * (y : ℚ) * (B₁ - (n + 1) * A) := by
      linear_combination zero
    have shallow : (n + 1) * A - B₀ < 8 * (B₁ - (n + 1) * A) := by
      nlinarith
    have excess_nonnegative :
        0 ≤ 8 * ((y : ℚ) - 1) * (B₁ - (n + 1) * A) := by positivity
    nlinarith [delta_eq]

/-- No regular shortest bad run of orientation `1 | 2 | 0` with a `c` defect and `b`
endpoints closes the bridge at deletion width three. -/
theorem bridge_bOne_cTwo_bZero_det_ne_zero
    (body : List TagLetter) (body_nonempty : body ≠ [])
    (x y z : Nat) (z_positive : 0 < z) :
    (bridge 27
      (bAtom 27 (3 * z + 1) *
        cAtom 27 (nearySideLowerC 3 body) (nearySideLowerCScale 3 body) (3 * x + 2) *
        bAtom 27 (3 * y))).det ≠ 0 := by
  rw [bridge_bOne_cTwo_bZero_det]
  rw [oppositeC_incidence_eq]
  have scale_positive := oppositeCScale_positive body body_nonempty
  apply mul_ne_zero
  · positivity
  rcases tagWord_c_run_or_c_run_b body with ⟨k, body_eq⟩ | ⟨k, tail, body_eq⟩
  · subst body
    have k_positive : 0 < k := by
      by_contra k_not_positive
      have k_zero : k = 0 := by omega
      subst k
      simp at body_nonempty
    rcases c_run_bounds k k_positive with
      ⟨lower_base, lower_crest, base_upper, crest_upper⟩
    refine weighted_root_between_consecutive_ne_zero
      _ _ _ x y 64 scale_positive lower_base lower_crest ?_ ?_
    · norm_num
      exact base_upper
    · norm_num
      exact crest_upper
  · subst body
    by_cases short : k < 4
    · have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      · simp only [List.replicate_zero, List.nil_append] at scale_positive ⊢
        rcases c_run_b_zero_bounds tail with
          ⟨lower_base, lower_crest, _, crest_upper, base_below_candidate,
            candidate_below_crest, candidate_shallow⟩
        refine weighted_root_single_candidate_ne_zero
          _ _ _ x y 58 scale_positive lower_base lower_crest ?_ ?_ ?_ ?_
        · norm_num
          exact crest_upper
        · norm_num
          exact base_below_candidate
        · norm_num
          exact candidate_below_crest
        · norm_num at candidate_shallow ⊢
          exact candidate_shallow
      · rcases c_run_b_one_bounds tail with
          ⟨lower_base, lower_crest, base_upper, crest_upper⟩
        refine weighted_root_between_consecutive_ne_zero
          _ _ _ x y 62 scale_positive lower_base lower_crest ?_ ?_
        · norm_num
          exact base_upper
        · norm_num
          exact crest_upper
      · rcases c_run_b_two_bounds tail with
          ⟨lower_base, lower_crest, base_upper, crest_upper⟩
        refine weighted_root_between_consecutive_ne_zero
          _ _ _ x y 63 scale_positive lower_base lower_crest ?_ ?_
        · norm_num
          exact base_upper
        · norm_num
          exact crest_upper
      · rcases c_run_b_three_bounds tail with
          ⟨lower_base, lower_crest, _, crest_upper, base_below_candidate,
            candidate_below_crest, candidate_shallow⟩
        refine weighted_root_single_candidate_ne_zero
          _ _ _ x y 63 scale_positive lower_base lower_crest ?_ ?_ ?_ ?_
        · norm_num
          exact crest_upper
        · norm_num
          exact base_below_candidate
        · norm_num
          exact candidate_below_crest
        · norm_num at candidate_shallow ⊢
          exact candidate_shallow
    · have four_le : 4 ≤ k := by omega
      rcases c_run_b_long_bounds k tail four_le with
        ⟨lower_base, lower_crest, base_upper, crest_upper⟩
      refine weighted_root_between_consecutive_ne_zero
        _ _ _ x y 64 scale_positive lower_base lower_crest ?_ ?_
      · norm_num
        exact base_upper
      · norm_num
        exact crest_upper

end MatrixMortality.ParabolicBlade
