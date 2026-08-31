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

/-! ## Opposite right-`c` endpoint cylinder -/

private def rightCScale (M : ℚ) : ℚ := 166944 * (M - 3)

private def rightCCrest (L M : ℚ) : ℚ :=
  16274467 * L - 5515409 * M - 229072

private def rightCBase (L M : ℚ) : ℚ :=
  48637017 * L - 16433267 * M - 839712

private def rightCIncidence (L M x y : ℚ) : ℚ :=
  (M - 3) * rightCCrest L M * y + rightCBase L M -
    rightCScale M * ((M - 3) * y + 3) * x

/-- Exact shortest `1 | 2 | 0` bridge determinant with a `c` defect and a residue-zero `c`
right endpoint. -/
theorem bridge_bOne_cTwo_cZero_det (body : List TagLetter) (x y z : Nat) :
    (bridge 27
      (bAtom 27 (3 * z + 1) *
        cAtom 27 (nearySideLowerC 3 body) (nearySideLowerCScale 3 body) (3 * x + 2) *
        cAtom 27 (nearySideLowerC 3 body) (nearySideLowerCScale 3 body) (3 * y))).det =
      729 * z / 4 *
        rightCIncidence
          (nearySideLowerC 3 body) (nearySideLowerCScale 3 body) x y := by
  rw [bAtom_three_mul_add_one_matrix, cAtom_three_mul_add_two_matrix,
    cAtom_three_mul_matrix, Matrix.det_fin_two]
  norm_num [bridge, coreInput, coreOutput, Matrix.mul_apply, Fin.sum_univ_succ,
    rightCIncidence, rightCScale, rightCCrest, rightCBase]
  ring

private theorem rightC_root_between_consecutive_ne_zero
    (D A B : ℚ) (x y n m : Nat) (adjacent : m = n + 1) (D_positive : 0 < D)
    (crest_lower : n * (166944 * D) < A)
    (crest_upper : A < m * (166944 * D))
    (base_lower : n * (3 * (166944 * D)) < B)
    (base_upper : B < m * (3 * (166944 * D))) :
    D * A * y + B - 166944 * D * (D * y + 3) * x ≠ 0 := by
  intro zero
  have y_nonnegative : (0 : ℚ) ≤ y := by positivity
  have denominator_positive : 0 < 166944 * D * (D * (y : ℚ) + 3) := by positivity
  have lower_margin_positive :
      0 < D * (y : ℚ) * (A - n * (166944 * D)) +
        (B - n * (3 * (166944 * D))) := by positivity
  have upper_margin_positive :
      0 < D * (y : ℚ) * (m * (166944 * D) - A) +
        (m * (3 * (166944 * D)) - B) := by positivity
  have x_lower : (n : ℚ) < x := by nlinarith
  have x_upper : (x : ℚ) < m := by nlinarith
  have x_lower_nat : n < x := by exact_mod_cast x_lower
  have x_upper_nat : x < m := by exact_mod_cast x_upper
  omega

private theorem rightC_run_b_zero_bounds (tail : List TagLetter) :
    let body := .b :: tail
    let L := nearySideLowerC 3 body
    let M := nearySideLowerCScale 3 body
    let A := rightCCrest L M
    let B := rightCBase L M
    let S := rightCScale M
    59 * S < A ∧ A < 60 * S ∧ 59 * (3 * S) < B ∧ B < 60 * (3 * S) := by
  dsimp only
  rcases c_run_b_side_coordinates 0 tail with
    ⟨lower_eq, lower_scale_eq, code_nonnegative, code_succ_le_scale⟩
  norm_num at lower_eq lower_scale_eq
  have crosses := b_zero_crosses_every_suffix tail
  simp only [rightCCrest, rightCBase, rightCScale]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem rightC_run_b_one_bounds (tail : List TagLetter) :
    let body := List.replicate 1 .c ++ .b :: tail
    let L := nearySideLowerC 3 body
    let M := nearySideLowerCScale 3 body
    let A := rightCCrest L M
    let B := rightCBase L M
    let S := rightCScale M
    62 * S < A ∧ A < 63 * S ∧ 62 * (3 * S) < B ∧ B < 63 * (3 * S) := by
  dsimp only
  rcases c_run_b_side_coordinates 1 tail with
    ⟨lower_eq, lower_scale_eq, code_nonnegative, code_succ_le_scale⟩
  norm_num at lower_eq lower_scale_eq
  simp only [List.replicate_succ, List.replicate_zero, List.nil_append,
    List.cons_append] at lower_eq lower_scale_eq ⊢
  simp only [rightCCrest, rightCBase, rightCScale]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem rightC_run_b_two_bounds (tail : List TagLetter) :
    let body := List.replicate 2 .c ++ .b :: tail
    let L := nearySideLowerC 3 body
    let M := nearySideLowerCScale 3 body
    let A := rightCCrest L M
    let B := rightCBase L M
    let S := rightCScale M
    63 * S < A ∧ A < 64 * S ∧ 63 * (3 * S) < B ∧ B < 64 * (3 * S) := by
  dsimp only
  rcases c_run_b_side_coordinates 2 tail with
    ⟨lower_eq, lower_scale_eq, code_nonnegative, code_succ_le_scale⟩
  norm_num at lower_eq lower_scale_eq
  simp only [rightCCrest, rightCBase, rightCScale]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem rightC_run_b_long_bounds
    (k : Nat) (tail : List TagLetter) (three_le : 3 ≤ k) :
    let body := List.replicate k .c ++ .b :: tail
    let L := nearySideLowerC 3 body
    let M := nearySideLowerCScale 3 body
    let A := rightCCrest L M
    let B := rightCBase L M
    let S := rightCScale M
    64 * S < A ∧ A < 65 * S ∧ 64 * (3 * S) < B ∧ B < 65 * (3 * S) := by
  dsimp only
  rcases c_run_b_side_coordinates k tail with
    ⟨lower_eq, lower_scale_eq, code_nonnegative, code_succ_le_scale⟩
  have power_ge_nat : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) three_le
  have power_ge : (27 : ℚ) ≤ 3 ^ k := by exact_mod_cast power_ge_nat
  have power_excess_nonnegative :
      0 ≤ ((3 : ℚ) ^ k - 27) * 3 ^ (tagEncode 3 tail).length := by positivity
  simp only [rightCCrest, rightCBase, rightCScale]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem rightC_run_bounds (k : Nat) (k_positive : 0 < k) :
    let body := List.replicate k .c
    let L := nearySideLowerC 3 body
    let M := nearySideLowerCScale 3 body
    let A := rightCCrest L M
    let B := rightCBase L M
    let S := rightCScale M
    64 * S < A ∧ A < 65 * S ∧ 64 * (3 * S) < B ∧ B < 65 * (3 * S) := by
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
  simp only [rightCCrest, rightCBase, rightCScale]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- No regular shortest bad run of orientation `1 | 2 | 0` with a `c` defect and a residue-zero
`c` right endpoint closes the bridge at deletion width three. -/
theorem bridge_bOne_cTwo_cZero_det_ne_zero
    (body : List TagLetter) (body_nonempty : body ≠ [])
    (x y z : Nat) (z_positive : 0 < z) :
    (bridge 27
      (bAtom 27 (3 * z + 1) *
        cAtom 27 (nearySideLowerC 3 body) (nearySideLowerCScale 3 body) (3 * x + 2) *
        cAtom 27 (nearySideLowerC 3 body) (nearySideLowerCScale 3 body) (3 * y))).det ≠ 0 := by
  rw [bridge_bOne_cTwo_cZero_det]
  let L : ℚ := nearySideLowerC 3 body
  let M : ℚ := nearySideLowerCScale 3 body
  let D := M - 3
  let A := rightCCrest L M
  let B := rightCBase L M
  have D_positive : 0 < D := by
    have scale_positive := oppositeCScale_positive body body_nonempty
    dsimp [oppositeCScale, D, M] at scale_positive ⊢
    nlinarith
  apply mul_ne_zero
  · positivity
  change rightCIncidence L M x y ≠ 0
  change D * A * y + B - 166944 * D * (D * y + 3) * x ≠ 0
  rcases tagWord_c_run_or_c_run_b body with ⟨k, body_eq⟩ | ⟨k, tail, body_eq⟩
  · subst body
    have k_positive : 0 < k := by
      by_contra k_not_positive
      have k_zero : k = 0 := by omega
      subst k
      simp at body_nonempty
    rcases rightC_run_bounds k k_positive with
      ⟨crest_lower, crest_upper, base_lower, base_upper⟩
    norm_num [rightCScale, D, A, B, M, L] at crest_lower crest_upper base_lower base_upper ⊢
    exact rightC_root_between_consecutive_ne_zero D A B x y 64 65 (by omega) D_positive
      crest_lower crest_upper base_lower base_upper
  · subst body
    by_cases short : k < 3
    · have cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases cases with rfl | rfl | rfl
      · rcases rightC_run_b_zero_bounds tail with
          ⟨crest_lower, crest_upper, base_lower, base_upper⟩
        norm_num [rightCScale, D, A, B, M, L] at crest_lower crest_upper base_lower base_upper ⊢
        exact rightC_root_between_consecutive_ne_zero D A B x y 59 60 (by omega) D_positive
          crest_lower crest_upper base_lower base_upper
      · rcases rightC_run_b_one_bounds tail with
          ⟨crest_lower, crest_upper, base_lower, base_upper⟩
        norm_num [rightCScale, D, A, B, M, L] at crest_lower crest_upper base_lower base_upper ⊢
        exact rightC_root_between_consecutive_ne_zero D A B x y 62 63 (by omega) D_positive
          crest_lower crest_upper base_lower base_upper
      · rcases rightC_run_b_two_bounds tail with
          ⟨crest_lower, crest_upper, base_lower, base_upper⟩
        norm_num [rightCScale, D, A, B, M, L] at crest_lower crest_upper base_lower base_upper ⊢
        exact rightC_root_between_consecutive_ne_zero D A B x y 63 64 (by omega) D_positive
          crest_lower crest_upper base_lower base_upper
    · have three_le : 3 ≤ k := by omega
      rcases rightC_run_b_long_bounds k tail three_le with
        ⟨crest_lower, crest_upper, base_lower, base_upper⟩
      norm_num [rightCScale, D, A, B, M, L] at crest_lower crest_upper base_lower base_upper ⊢
      exact rightC_root_between_consecutive_ne_zero D A B x y 64 65 (by omega) D_positive
        crest_lower crest_upper base_lower base_upper

/-! ## Phase-zero double-`c` parity cylinder -/

/-- Primitive code-coordinate determinant core for the shortest `0 | 2 | 1` bridge with a `b`
left endpoint and `c` defect and right endpoint. -/
def bZeroCDefectCOneCodeCore {R : Type*} [CommRing R] (S C x y z : R) : R :=
  -23334912 * (9 * S - 1) ^ 2 * x * y * z -
    13824 * (9 * S - 1) * (162 * C + 1251 * S + 5) * x * y +
    5184 * (9 * S - 1) * (3005309 * C - 3000245 * S + 3000245) * x * z +
    648 * (2275047 * C ^ 2 + 15676434 * C * S + 2299246 * C -
      17917569 * S ^ 2 + 17889602 * S + 27967) * x +
    64 * (9 * S - 1) * (237746619 * C + 474797736 * S + 158210416) * y * z +
    8 * (181103283 * C ^ 2 + 1775833389 * C * S + 124016715 * C +
      2831071824 * S ^ 2 + 946249992 * S + 2443688) * y +
    24 * (2780613 * C ^ 2 + 3181640607 * C * S + 296595377 * C -
      5322054285 * S ^ 2 + 5266848130 * S + 55206155) * z +
    3 * (270019620 * C ^ 2 + 1664902161 * C * S + 827900783 * C -
      3530924613 * S ^ 2 + 3151634218 * S + 379290395)

/-- Exact code-coordinate determinant of the shortest `0 | 2 | 1` bridge with letters
`b | c | c`. -/
theorem bridge_bZero_cTwo_cOne_det (body : List TagLetter) (x y z : Nat) :
    (bridge 27
      (bAtom 27 (3 * z) *
        cAtom 27 (nearySideLowerC 3 body) (nearySideLowerCScale 3 body) (3 * x + 2) *
        cAtom 27 (nearySideLowerC 3 body) (nearySideLowerCScale 3 body)
          (3 * y + 1))).det =
      2187 / 1024 *
        bZeroCDefectCOneCodeCore
          ((3 : ℚ) ^ (tagEncode 3 body).length)
          (ternaryCode (tagEncode 3 body)) x y z := by
  rcases side_coordinates body with ⟨lower_eq, scale_eq⟩
  rw [bAtom_three_mul_matrix, cAtom_three_mul_add_two_matrix,
    cAtom_three_mul_add_one_matrix, Matrix.det_fin_two, lower_eq, scale_eq]
  norm_num [bridge, coreInput, coreOutput, Matrix.mul_apply, Fin.sum_univ_succ,
    bZeroCDefectCOneCodeCore]
  ring

private theorem three_pow_mod_two (n : Nat) : 3 ^ n % 2 = 1 := by
  induction n with
  | zero => simp
  | succ n induction => simp [pow_succ, Nat.mul_mod, induction]

private theorem three_pow_mod_four_of_odd_exponent (n : Nat) (n_odd : n % 2 = 1) :
    3 ^ n % 4 = 3 := by
  obtain ⟨k, n_eq⟩ : ∃ k, n = 2 * k + 1 := by
    refine ⟨n / 2, ?_⟩
    omega
  rw [n_eq, pow_add, pow_mul]
  norm_num [Nat.pow_mod, Nat.mul_mod]

private theorem tagEncode_length_mod_two (body : List TagLetter) :
    (tagEncode 3 body).length % 2 = body.length % 2 := by
  induction body with
  | nil => simp
  | cons head tail induction =>
      rw [tagEncode_cons]
      cases head <;> simp [tagCode] <;> omega

private theorem tagEncode_code_mod_two (body : List TagLetter) :
    ternaryCode (tagEncode 3 body) % 2 = body.count .b % 2 := by
  induction body with
  | nil => simp [ternaryCode]
  | cons head tail induction =>
      rw [tagEncode_cons, ternaryCode_append]
      have scale_mod := three_pow_mod_two (tagEncode 3 tail).length
      cases head with
      | b =>
          have prefix_code : ternaryCode (tagCode 3 .b) = 203 := by decide
          rw [prefix_code, Nat.add_mod, Nat.mul_mod, scale_mod, induction]
          norm_num
          simp [Nat.add_comm]
      | c =>
          have prefix_code : ternaryCode (tagCode 3 .c) = 2 := by decide
          rw [prefix_code, Nat.add_mod, Nat.mul_mod, scale_mod, induction]
          norm_num
          simp

private def bZeroCDefectCOneParityQuotient (s c x y z : ℤ) : ℤ :=
  -23334912 * (18 * s + 13) ^ 2 * x * y * z -
    27648 * (18 * s + 13) * (1251 * s + 81 * c + 980) * x * y -
    2592 * (18 * s + 13) * (12000980 * s - 6010618 * c + 2995181) * x * z -
    162 * (286681104 * s ^ 2 - 125411472 * s * c + 295757512 * s -
      9100188 * c ^ 2 - 107757284 * c + 55957753) * x +
    32 * (18 * s + 13) * (1899190944 * s + 475493238 * c + 1820350243) * y * z +
    2 * (45297149184 * s ^ 2 + 14206667112 * s * c + 78834057300 * s +
      724413132 * c ^ 2 + 11627446896 * c + 33953460245) * y -
    6 * (85152868560 * s ^ 2 - 25453124856 * s * c + 93935347892 * s -
      11122452 * c ^ 2 - 19694156848 * c + 22198440209) * z -
    42371095356 * s ^ 2 + 9989412966 * s * c - 49107033897 * s +
    810058860 * c ^ 2 + 9543969759 * c - 11888626187

private theorem bZeroCDefectCOneCodeCore_parity_factor
    (s c x y z : ℤ) :
    bZeroCDefectCOneCodeCore (4 * s + 3) (2 * c + 1) x y z =
      4 * bZeroCDefectCOneParityQuotient s c x y z + 2 := by
  unfold bZeroCDefectCOneCodeCore bZeroCDefectCOneParityQuotient
  ring

private theorem codeCore_ne_zero_of_odd_coordinates
    (S C x y z : Nat) (S_mod_four : S % 4 = 3) (C_odd : C % 2 = 1) :
    bZeroCDefectCOneCodeCore (S : ℤ) C x y z ≠ 0 := by
  intro core_zero
  obtain ⟨s, S_eq⟩ : ∃ s, S = 4 * s + 3 := by
    refine ⟨S / 4, ?_⟩
    omega
  obtain ⟨c, C_eq⟩ : ∃ c, C = 2 * c + 1 := by
    refine ⟨C / 2, ?_⟩
    omega
  rw [S_eq, C_eq] at core_zero
  push_cast at core_zero
  rw [bZeroCDefectCOneCodeCore_parity_factor] at core_zero
  omega

/-- Odd body length and an odd number of `b` letters form a uniform parity cylinder excluding
the shortest `0 | 2 | 1` bridge with letters `b | c | c`. -/
theorem bridge_bZero_cTwo_cOne_det_ne_zero_of_odd_body
    (body : List TagLetter) (body_length_odd : body.length % 2 = 1)
    (b_count_odd : body.count .b % 2 = 1) (x y z : Nat) :
    (bridge 27
      (bAtom 27 (3 * z) *
        cAtom 27 (nearySideLowerC 3 body) (nearySideLowerCScale 3 body) (3 * x + 2) *
        cAtom 27 (nearySideLowerC 3 body) (nearySideLowerCScale 3 body)
          (3 * y + 1))).det ≠ 0 := by
  rw [bridge_bZero_cTwo_cOne_det]
  apply mul_ne_zero (by norm_num)
  have encoded_length_odd : (tagEncode 3 body).length % 2 = 1 := by
    rw [tagEncode_length_mod_two]
    exact body_length_odd
  have encoded_code_odd : ternaryCode (tagEncode 3 body) % 2 = 1 := by
    rw [tagEncode_code_mod_two]
    exact b_count_odd
  have scale_mod_four : 3 ^ (tagEncode 3 body).length % 4 = 3 :=
    three_pow_mod_four_of_odd_exponent (tagEncode 3 body).length encoded_length_odd
  intro core_zero
  have power_cast :
      ((3 ^ (tagEncode 3 body).length : Nat) : ℚ) =
        (3 : ℚ) ^ (tagEncode 3 body).length := by norm_num
  rw [← power_cast] at core_zero
  have cast_integer_core :
      ((bZeroCDefectCOneCodeCore
        ((3 ^ (tagEncode 3 body).length : Nat) : ℤ)
        (ternaryCode (tagEncode 3 body)) x y z : ℤ) : ℚ) =
        bZeroCDefectCOneCodeCore
          ((3 ^ (tagEncode 3 body).length : Nat) : ℚ)
          (ternaryCode (tagEncode 3 body)) x y z := by
    norm_num [bZeroCDefectCOneCodeCore]
  have integer_core_zero :
      bZeroCDefectCOneCodeCore
        ((3 ^ (tagEncode 3 body).length : Nat) : ℤ)
        (ternaryCode (tagEncode 3 body)) x y z = 0 := by
    have cast_zero :
        ((bZeroCDefectCOneCodeCore
          ((3 ^ (tagEncode 3 body).length : Nat) : ℤ)
          (ternaryCode (tagEncode 3 body)) x y z : ℤ) : ℚ) = 0 := by
      exact cast_integer_core.trans core_zero
    exact_mod_cast cast_zero
  exact (codeCore_ne_zero_of_odd_coordinates
    (3 ^ (tagEncode 3 body).length) (ternaryCode (tagEncode 3 body)) x y z
      scale_mod_four encoded_code_odd) integer_core_zero

end MatrixMortality.ParabolicBlade
