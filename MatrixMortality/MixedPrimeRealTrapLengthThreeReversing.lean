import MatrixMortality.MixedPrimeRealTrapLengthThreeChambers

/-!
# Negative-positive-negative length-three classifier

The real trap forces the tail transfer to one and leaves an explicit finite/ray cell table.
The prefix and target guards then isolate `q=1`, `A=2`, and `p∈{1,2}`. Exact carry transport
reduces the remaining gap to 250 residues and the terminal wait to ten residues; forty pairs
survive, giving a complete semilinear acceptance language for the final strict sign chamber.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation
open PeriodicShell

private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Left schedule in the strict negative-positive-negative chamber. -/
def lengthThreeReversingLeft (p q t B : ℕ) : List ℕ :=
  [p, q + B, t]

/-- Right schedule in the strict negative-positive-negative chamber. -/
def lengthThreeReversingRight (p q t A k : ℕ) : List ℕ :=
  [p + A, q, t + k]

/-- Exact collision source in the strict negative-positive-negative chamber. -/
def lengthThreeReversingSource (p q A B k : ℕ) : ℚ :=
  (9 * (2 / 3 : ℚ) ^ q * ((2 / 3 : ℚ) ^ B - (2 / 3 : ℚ) ^ k) +
      15 * (1 - (2 / 3 : ℚ) ^ k)) /
    (27 * (2 / 3 : ℚ) ^ (p + q) *
      ((2 / 3 : ℚ) ^ (A + k) - (2 / 3 : ℚ) ^ B))

private theorem reversingShellOffset_nil' : shellOffset [] = 0 := by
  have run_nil : shellRun [] (0 : ℚ) = 0 := rfl
  rw [shellOffset, shellIntercept, run_nil]
  norm_num

private theorem reversingShellOffset_triple' (a b c : ℕ) :
    shellOffset [a, b, c] =
      9 * (2 / 3 : ℚ) ^ (b + c) + 15 * (2 / 3 : ℚ) ^ c + 25 := by
  rw [shellOffset_cons, shellOffset_cons, shellOffset_cons, reversingShellOffset_nil']
  simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, pow_succ, pow_zero]
  ring

theorem lengthThreeReversing_collisionSource
    (p q t A B k : ℕ) (total_positive : A + k < B) :
    collisionSource (lengthThreeReversingLeft p q t B)
        (lengthThreeReversingRight p q t A k) =
      lengthThreeReversingSource p q A B k := by
  have length_eq :
      (lengthThreeReversingLeft p q t B).length =
        (lengthThreeReversingRight p q t A k).length := by
    rfl
  have sum_ne :
      (lengthThreeReversingLeft p q t B).sum ≠
        (lengthThreeReversingRight p q t A k).sum := by
    simp only [lengthThreeReversingLeft, lengthThreeReversingRight,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  have base_ne : (2 / 3 : ℚ) ≠ 0 := by norm_num
  have gap_positive :
      (2 / 3 : ℚ) ^ B < (2 / 3 : ℚ) ^ (A + k) :=
    pow_right_strictAnti₀ (by norm_num) (by norm_num) total_positive
  have gap_ne : (2 / 3 : ℚ) ^ (A + k) - (2 / 3 : ℚ) ^ B ≠ 0 := by
    linarith
  have offset_difference :
      shellOffset (lengthThreeReversingLeft p q t B) -
          shellOffset (lengthThreeReversingRight p q t A k) =
        (2 / 3 : ℚ) ^ t *
          (9 * (2 / 3 : ℚ) ^ q *
              ((2 / 3 : ℚ) ^ B - (2 / 3 : ℚ) ^ k) +
            15 * (1 - (2 / 3 : ℚ) ^ k)) := by
    rw [lengthThreeReversingLeft, lengthThreeReversingRight,
      reversingShellOffset_triple', reversingShellOffset_triple']
    simp only [pow_add]
    ring
  have gain_difference :
      shellGain (lengthThreeReversingRight p q t A k) -
          shellGain (lengthThreeReversingLeft p q t B) =
        27 * (2 / 3 : ℚ) ^ (p + q + t) *
          ((2 / 3 : ℚ) ^ (A + k) - (2 / 3 : ℚ) ^ B) := by
    simp only [lengthThreeReversingLeft, lengthThreeReversingRight,
      shellGain, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, pow_add]
    ring
  rw [collisionSource_eq_clearedBalance length_eq sum_ne,
    offset_difference, gain_difference, lengthThreeReversingSource,
    show p + q + t = (p + q) + t by omega, pow_add]
  field_simp [base_ne, gap_ne]

/-- After the real trap freezes `k=1`, normalize the remaining total gap as `offset+1`. -/
def lengthThreeReversingNormalizedSource
    (p q A offset : ℕ) : ℚ :=
  (5 - 6 * (2 / 3 : ℚ) ^ q +
      9 * (2 / 3 : ℚ) ^ (q + A + 2 + offset)) /
    (27 * (2 / 3 : ℚ) ^ (p + q + A + 1) *
      (1 - (2 / 3 : ℚ) ^ (offset + 1)))

theorem lengthThreeReversingSource_normalized
    (p q A offset : ℕ) :
    lengthThreeReversingSource p q A (A + 2 + offset) 1 =
      lengthThreeReversingNormalizedSource p q A offset := by
  have base_ne : (2 / 3 : ℚ) ≠ 0 := by norm_num
  have gap_positive : 0 < offset + 1 := by omega
  have gap_ne : 1 - (2 / 3 : ℚ) ^ (offset + 1) ≠ 0 := by
    have power_lt : (2 / 3 : ℚ) ^ (offset + 1) < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) gap_positive.ne'
    linarith
  have gap_factor :
      (2 / 3 : ℚ) ^ (A + 1) - (2 / 3 : ℚ) ^ (A + 2 + offset) =
        (2 / 3 : ℚ) ^ (A + 1) *
          (1 - (2 / 3 : ℚ) ^ (offset + 1)) := by
    rw [show A + 2 + offset = (A + 1) + (offset + 1) by omega, pow_add]
    ring
  have tail_power :
      (2 / 3 : ℚ) ^ (A + 2 + offset) =
        (2 / 3 : ℚ) ^ (A + 1) * (2 / 3 : ℚ) ^ (offset + 1) := by
    rw [show A + 2 + offset = (A + 1) + (offset + 1) by omega, pow_add]
  have numerator_power :
      (2 / 3 : ℚ) ^ (q + A + 2 + offset) =
        (2 / 3 : ℚ) ^ q * (2 / 3 : ℚ) ^ (A + 2 + offset) := by
    rw [show q + A + 2 + offset = q + (A + 2 + offset) by omega, pow_add]
  have baseline_power :
      (2 / 3 : ℚ) ^ (p + q + A + 1) =
        (2 / 3 : ℚ) ^ (p + q) * (2 / 3 : ℚ) ^ (A + 1) := by
    rw [show p + q + A + 1 = (p + q) + (A + 1) by omega, pow_add]
  rw [lengthThreeReversingSource, lengthThreeReversingNormalizedSource,
    gap_factor, tail_power, numerator_power, baseline_power]
  simp only [pow_one]
  field_simp [base_ne, gap_ne]
  ring

/-- Exact normalized common target in the negative-positive-negative chamber. -/
def lengthThreeReversingTarget (q A offset t : ℕ) : ℚ :=
  (25 * (1 - (2 / 3 : ℚ) ^ (offset + 1)) +
      (2 / 3 : ℚ) ^ t *
        (15 + (2 / 3 : ℚ) ^ (offset + 1) *
          (9 * (2 / 3 : ℚ) ^ (q + A + 1) -
            6 * (2 / 3 : ℚ) ^ q - 10))) /
    (125 * (1 - (2 / 3 : ℚ) ^ (offset + 1)))

/-- The right schedule reaches the exact normalized target. -/
theorem lengthThreeReversingRight_commonTarget
    (p q A offset t : ℕ) :
    shellRun (lengthThreeReversingRight p q t A 1)
        (lengthThreeReversingNormalizedSource p q A offset) =
      lengthThreeReversingTarget q A offset t := by
  have base_ne : (2 / 3 : ℚ) ≠ 0 := by norm_num
  have gap_positive : 0 < offset + 1 := by omega
  have gap_ne : 1 - (2 / 3 : ℚ) ^ (offset + 1) ≠ 0 := by
    have power_lt : (2 / 3 : ℚ) ^ (offset + 1) < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) gap_positive.ne'
    linarith
  have offset_power_le_one : (2 / 3 : ℚ) ^ offset ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have scaled_gap_ne : 3 - (2 / 3 : ℚ) ^ offset * 2 ≠ 0 := by
    have : 0 < 3 - (2 / 3 : ℚ) ^ offset * 2 := by nlinarith
    exact ne_of_gt this
  have six_scaled_gap_ne : 18 - (2 / 3 : ℚ) ^ offset * 12 ≠ 0 := by
    intro equality
    apply scaled_gap_ne
    nlinarith
  have oneTwentyFive_scaled_gap_ne :
      375 - (2 / 3 : ℚ) ^ offset * 250 ≠ 0 := by
    intro equality
    apply scaled_gap_ne
    nlinarith
  rw [lengthThreeReversingRight, shellRun_cons, shellRun_cons,
    shellRun_singleton, lengthThreeReversingNormalizedSource,
    lengthThreeReversingTarget]
  simp only [shellStep, pow_one, pow_add]
  ring_nf
  field_simp [base_ne, gap_ne, scaled_gap_ne, six_scaled_gap_ne,
    oneTwentyFive_scaled_gap_ne]
  ring_nf
  field_simp [oneTwentyFive_scaled_gap_ne]
  ring

/-- Both schedules reach the exact normalized target. -/
theorem lengthThreeReversing_commonTarget
    (p q A offset t : ℕ) :
    shellRun (lengthThreeReversingLeft p q t (A + 2 + offset))
          (lengthThreeReversingNormalizedSource p q A offset) =
        lengthThreeReversingTarget q A offset t ∧
      shellRun (lengthThreeReversingRight p q t A 1)
          (lengthThreeReversingNormalizedSource p q A offset) =
        lengthThreeReversingTarget q A offset t := by
  have total_positive : A + 1 < A + 2 + offset := by omega
  have source_eq := lengthThreeReversing_collisionSource
    p q t A (A + 2 + offset) 1 total_positive
  rw [lengthThreeReversingSource_normalized] at source_eq
  have slope_ne :
      shellSlope (lengthThreeReversingLeft p q t (A + 2 + offset)) ≠
        shellSlope (lengthThreeReversingRight p q t A 1) := by
    intro slope_eq
    have sums_eq :=
      (shellSlope_eq_iff_length_sum
        (lengthThreeReversingLeft p q t (A + 2 + offset))
        (lengthThreeReversingRight p q t A 1)).1 slope_eq
    simp only [lengthThreeReversingLeft, lengthThreeReversingRight,
      List.sum_cons, List.sum_nil, Nat.add_zero] at sums_eq
    omega
  have endpoint_collision := shellRun_collisionSource
    (lengthThreeReversingLeft p q t (A + 2 + offset))
    (lengthThreeReversingRight p q t A 1) slope_ne
  rw [source_eq] at endpoint_collision
  have right_target := lengthThreeReversingRight_commonTarget p q A offset t
  exact ⟨endpoint_collision.trans right_target, right_target⟩

/-- Every reversing source with tail transfer at least two lies above the real trap. -/
theorem lengthThreeReversingSource_gt_half_of_two_le_k
    (p q A B k : ℕ) (A_positive : 0 < A) (two_le_k : 2 ≤ k)
    (total_positive : A + k < B) :
    1 / 2 < lengthThreeReversingSource p q A B k := by
  have q_power_nonnegative : 0 ≤ (2 / 3 : ℚ) ^ q := by positivity
  have q_power_le_one : (2 / 3 : ℚ) ^ q ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have k_power_nonnegative : 0 ≤ (2 / 3 : ℚ) ^ k := by positivity
  have k_power_upper : (2 / 3 : ℚ) ^ k ≤ 4 / 9 := by
    have power_order := pow_le_pow_of_le_one
      (show 0 ≤ (2 / 3 : ℚ) by norm_num)
      (show (2 / 3 : ℚ) ≤ 1 by norm_num) two_le_k
    norm_num at power_order ⊢
    exact power_order
  have B_power_nonnegative : 0 ≤ (2 / 3 : ℚ) ^ B := by positivity
  have negative_gap_le :
      (2 / 3 : ℚ) ^ k - (2 / 3 : ℚ) ^ B ≤ (2 / 3 : ℚ) ^ k := by
    linarith
  have weighted_gap_le :
      (2 / 3 : ℚ) ^ q *
          ((2 / 3 : ℚ) ^ k - (2 / 3 : ℚ) ^ B) ≤ 4 / 9 := by
    calc
      (2 / 3 : ℚ) ^ q *
            ((2 / 3 : ℚ) ^ k - (2 / 3 : ℚ) ^ B) ≤
          (2 / 3 : ℚ) ^ q * (2 / 3 : ℚ) ^ k :=
        mul_le_mul_of_nonneg_left negative_gap_le q_power_nonnegative
      _ ≤ 1 * (4 / 9 : ℚ) :=
        mul_le_mul q_power_le_one k_power_upper (by positivity) (by norm_num)
      _ = 4 / 9 := by norm_num
  have numerator_lower :
      13 / 3 ≤
        9 * (2 / 3 : ℚ) ^ q *
            ((2 / 3 : ℚ) ^ B - (2 / 3 : ℚ) ^ k) +
          15 * (1 - (2 / 3 : ℚ) ^ k) := by
    nlinarith
  have baseline_upper :
      (2 / 3 : ℚ) ^ (p + q) ≤ (2 / 3 : ℚ) ^ q := by
    rw [pow_add]
    have p_power_le_one : (2 / 3 : ℚ) ^ p ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have total_power_lt : (2 / 3 : ℚ) ^ B < (2 / 3 : ℚ) ^ (A + k) :=
    pow_right_strictAnti₀ (by norm_num) (by norm_num) total_positive
  have denominator_positive :
      0 < 27 * (2 / 3 : ℚ) ^ (p + q) *
        ((2 / 3 : ℚ) ^ (A + k) - (2 / 3 : ℚ) ^ B) := by
    positivity
  have three_le_total : 3 ≤ A + k := by omega
  have total_power_upper : (2 / 3 : ℚ) ^ (A + k) ≤ 8 / 27 := by
    have power_order := pow_le_pow_of_le_one
      (show 0 ≤ (2 / 3 : ℚ) by norm_num)
      (show (2 / 3 : ℚ) ≤ 1 by norm_num) three_le_total
    norm_num at power_order ⊢
    exact power_order
  have denominator_upper :
      27 * (2 / 3 : ℚ) ^ (p + q) *
          ((2 / 3 : ℚ) ^ (A + k) - (2 / 3 : ℚ) ^ B) <
        8 * (2 / 3 : ℚ) ^ q := by
    have difference_lt :
        (2 / 3 : ℚ) ^ (A + k) - (2 / 3 : ℚ) ^ B <
          (2 / 3 : ℚ) ^ (A + k) := by
      have B_power_positive : 0 < (2 / 3 : ℚ) ^ B := by positivity
      linarith
    calc
      27 * (2 / 3 : ℚ) ^ (p + q) *
            ((2 / 3 : ℚ) ^ (A + k) - (2 / 3 : ℚ) ^ B) <
          27 * (2 / 3 : ℚ) ^ (p + q) * (2 / 3 : ℚ) ^ (A + k) := by
        exact mul_lt_mul_of_pos_left difference_lt (by positivity)
      _ ≤ 27 * (2 / 3 : ℚ) ^ q * (8 / 27) :=
        mul_le_mul (mul_le_mul_of_nonneg_left baseline_upper (by norm_num))
          total_power_upper (by positivity) (by positivity)
      _ = 8 * (2 / 3 : ℚ) ^ q := by ring
  rw [lengthThreeReversingSource]
  apply (lt_div_iff₀ denominator_positive).2
  nlinarith

/-- The real trap freezes the reversing tail transfer to one. -/
theorem lengthThreeReversingSource_realTrap_forces_k_eq_one
    (p q A B k : ℕ) (A_positive : 0 < A) (k_positive : 0 < k)
    (total_positive : A + k < B)
    (source_mem :
      lengthThreeReversingSource p q A B k ∈ Set.Icc (1 / 5) (1 / 2)) :
    k = 1 := by
  by_contra k_ne
  have two_le_k : 2 ≤ k := by omega
  have source_gt := lengthThreeReversingSource_gt_half_of_two_le_k
    p q A B k A_positive two_le_k total_positive
  exact (not_lt_of_ge source_mem.2) source_gt

/-- The real trap bounds the middle gauge by two after tail normalization. -/
theorem lengthThreeReversingNormalizedSource_realTrap_forces_q_le_two
    (p q A offset : ℕ) (A_positive : 0 < A)
    (source_mem :
      lengthThreeReversingNormalizedSource p q A offset ∈
        Set.Icc (1 / 5) (1 / 2)) :
    q ≤ 2 := by
  by_contra q_large
  have three_le_q : 3 ≤ q := by omega
  have gap_power_lt : (2 / 3 : ℚ) ^ (offset + 1) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have denominator_positive :
      0 < 27 * (2 / 3 : ℚ) ^ (p + q + A + 1) *
        (1 - (2 / 3 : ℚ) ^ (offset + 1)) := by
    positivity
  have q_power_upper : (2 / 3 : ℚ) ^ q ≤ 8 / 27 := by
    have power_order := pow_le_pow_of_le_one
      (show 0 ≤ (2 / 3 : ℚ) by norm_num)
      (show (2 / 3 : ℚ) ≤ 1 by norm_num) three_le_q
    norm_num at power_order ⊢
    exact power_order
  have numerator_lower :
      29 / 9 ≤
        5 - 6 * (2 / 3 : ℚ) ^ q +
          9 * (2 / 3 : ℚ) ^ (q + A + 2 + offset) := by
    have tail_power_nonnegative :
        0 ≤ (2 / 3 : ℚ) ^ (q + A + 2 + offset) := by positivity
    nlinarith
  have total_exponent : 5 ≤ p + q + A + 1 := by omega
  have baseline_upper :
      (2 / 3 : ℚ) ^ (p + q + A + 1) ≤ (2 / 3 : ℚ) ^ 5 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) total_exponent
  have denominator_upper :
      27 * (2 / 3 : ℚ) ^ (p + q + A + 1) *
          (1 - (2 / 3 : ℚ) ^ (offset + 1)) < 32 / 9 := by
    have gap_power_positive : 0 < (2 / 3 : ℚ) ^ (offset + 1) := by positivity
    norm_num at baseline_upper ⊢
    nlinarith
  have source_gt_half :
      1 / 2 < lengthThreeReversingNormalizedSource p q A offset := by
    rw [lengthThreeReversingNormalizedSource]
    apply (lt_div_iff₀ denominator_positive).2
    nlinarith
  exact (not_lt_of_ge source_mem.2) source_gt_half

/-- The real trap bounds the first reversing gap by four. -/
theorem lengthThreeReversingNormalizedSource_realTrap_forces_A_le_four
    (p q A offset : ℕ) (_A_positive : 0 < A)
    (source_mem :
      lengthThreeReversingNormalizedSource p q A offset ∈
        Set.Icc (1 / 5) (1 / 2)) :
    A ≤ 4 := by
  by_contra A_large
  have five_le_A : 5 ≤ A := by omega
  have gap_power_lt : (2 / 3 : ℚ) ^ (offset + 1) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have denominator_positive :
      0 < 27 * (2 / 3 : ℚ) ^ (p + q + A + 1) *
        (1 - (2 / 3 : ℚ) ^ (offset + 1)) := by
    positivity
  by_cases q_zero : q = 0
  · subst q
    have source_positive :
        0 < lengthThreeReversingNormalizedSource p 0 A offset :=
      lt_of_lt_of_le (by norm_num) source_mem.1
    have numerator_positive :
        0 < 5 - 6 * (2 / 3 : ℚ) ^ 0 +
          9 * (2 / 3 : ℚ) ^ (0 + A + 2 + offset) := by
      rw [lengthThreeReversingNormalizedSource] at source_positive
      exact (div_pos_iff_of_pos_right denominator_positive).1 source_positive
    have six_le_exponent : 6 ≤ A + 2 + offset := by omega
    have power_upper :
        (2 / 3 : ℚ) ^ (A + 2 + offset) ≤ (2 / 3 : ℚ) ^ 6 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) six_le_exponent
    norm_num at numerator_positive power_upper
    nlinarith
  · have one_le_q : 1 ≤ q := by omega
    have q_power_upper : (2 / 3 : ℚ) ^ q ≤ 2 / 3 := by
      have power_order := pow_le_pow_of_le_one
        (show 0 ≤ (2 / 3 : ℚ) by norm_num)
        (show (2 / 3 : ℚ) ≤ 1 by norm_num) one_le_q
      norm_num at power_order ⊢
      exact power_order
    have numerator_lower :
        1 ≤ 5 - 6 * (2 / 3 : ℚ) ^ q +
          9 * (2 / 3 : ℚ) ^ (q + A + 2 + offset) := by
      have tail_power_nonnegative :
          0 ≤ (2 / 3 : ℚ) ^ (q + A + 2 + offset) := by positivity
      nlinarith
    have seven_le_exponent : 7 ≤ p + q + A + 1 := by omega
    have baseline_upper :
        (2 / 3 : ℚ) ^ (p + q + A + 1) ≤ (2 / 3 : ℚ) ^ 7 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) seven_le_exponent
    have denominator_upper :
        27 * (2 / 3 : ℚ) ^ (p + q + A + 1) *
            (1 - (2 / 3 : ℚ) ^ (offset + 1)) < 128 / 81 := by
      have gap_power_positive : 0 < (2 / 3 : ℚ) ^ (offset + 1) := by positivity
      norm_num at baseline_upper ⊢
      nlinarith
    have source_gt_half :
        1 / 2 < lengthThreeReversingNormalizedSource p q A offset := by
      rw [lengthThreeReversingNormalizedSource]
      apply (lt_div_iff₀ denominator_positive).2
      nlinarith
    exact (not_lt_of_ge source_mem.2) source_gt_half

/-- The real trap bounds the first gauge by seven. -/
theorem lengthThreeReversingNormalizedSource_realTrap_forces_p_le_seven
    (p q A offset : ℕ) (A_positive : 0 < A)
    (source_mem :
      lengthThreeReversingNormalizedSource p q A offset ∈
        Set.Icc (1 / 5) (1 / 2)) :
    p ≤ 7 := by
  by_contra p_large
  have eight_le_p : 8 ≤ p := by omega
  have gap_power_lt : (2 / 3 : ℚ) ^ (offset + 1) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have denominator_positive :
      0 < 27 * (2 / 3 : ℚ) ^ (p + q + A + 1) *
        (1 - (2 / 3 : ℚ) ^ (offset + 1)) := by
    positivity
  by_cases q_zero : q = 0
  · subst q
    have source_positive :
        0 < lengthThreeReversingNormalizedSource p 0 A offset :=
      lt_of_lt_of_le (by norm_num) source_mem.1
    have numerator_positive :
        0 < -1 + 9 * (2 / 3 : ℚ) ^ (A + 2 + offset) := by
      rw [lengthThreeReversingNormalizedSource] at source_positive
      have raw_numerator_positive :=
        (div_pos_iff_of_pos_right denominator_positive).1 source_positive
      norm_num at raw_numerator_positive
      linarith
    have exponent_le_five : A + 2 + offset ≤ 5 := by
      by_contra exponent_large
      have six_le : 6 ≤ A + 2 + offset := by omega
      have power_upper :
          (2 / 3 : ℚ) ^ (A + 2 + offset) ≤ (2 / 3 : ℚ) ^ 6 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) six_le
      norm_num at numerator_positive power_upper
      nlinarith
    have A_le_three : A ≤ 3 := by omega
    have offset_le_two : offset ≤ 2 := by omega
    have p_power_upper : (2 / 3 : ℚ) ^ p ≤ (2 / 3 : ℚ) ^ 8 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) eight_le_p
    have source_upper := (div_le_iff₀ denominator_positive).1 source_mem.2
    have baseline_factor :
        (2 / 3 : ℚ) ^ (p + 0 + A + 1) =
          (2 / 3 : ℚ) ^ p * (2 / 3 : ℚ) ^ (A + 1) := by
      rw [show p + 0 + A + 1 = p + (A + 1) by omega, pow_add]
    rw [baseline_factor] at source_upper
    interval_cases A <;> interval_cases offset <;>
      norm_num at source_upper p_power_upper <;>
      nlinarith
  · have one_le_q : 1 ≤ q := by omega
    have q_power_upper : (2 / 3 : ℚ) ^ q ≤ 2 / 3 := by
      have power_order := pow_le_pow_of_le_one
        (show 0 ≤ (2 / 3 : ℚ) by norm_num)
        (show (2 / 3 : ℚ) ≤ 1 by norm_num) one_le_q
      norm_num at power_order ⊢
      exact power_order
    have numerator_lower :
        1 ≤ 5 - 6 * (2 / 3 : ℚ) ^ q +
          9 * (2 / 3 : ℚ) ^ (q + A + 2 + offset) := by
      have tail_power_nonnegative :
          0 ≤ (2 / 3 : ℚ) ^ (q + A + 2 + offset) := by positivity
      nlinarith
    have eleven_le_exponent : 11 ≤ p + q + A + 1 := by omega
    have baseline_upper :
        (2 / 3 : ℚ) ^ (p + q + A + 1) ≤ (2 / 3 : ℚ) ^ 11 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) eleven_le_exponent
    have denominator_upper :
        27 * (2 / 3 : ℚ) ^ (p + q + A + 1) *
            (1 - (2 / 3 : ℚ) ^ (offset + 1)) < 2048 / 2187 := by
      have gap_power_positive : 0 < (2 / 3 : ℚ) ^ (offset + 1) := by positivity
      norm_num at baseline_upper ⊢
      nlinarith
    have source_gt_half :
        1 / 2 < lengthThreeReversingNormalizedSource p q A offset := by
      rw [lengthThreeReversingNormalizedSource]
      apply (lt_div_iff₀ denominator_positive).2
      nlinarith
    exact (not_lt_of_ge source_mem.2) source_gt_half

private theorem lengthThreeReversingNormalizedSource_expanded
    (p q A offset : ℕ) :
    lengthThreeReversingNormalizedSource p q A offset =
      (5 - 6 * (2 / 3 : ℚ) ^ q +
          9 * (2 / 3 : ℚ) ^ (q + A + 1) *
            (2 / 3 : ℚ) ^ (offset + 1)) /
        (27 * (2 / 3 : ℚ) ^ (p + q + A + 1) *
          (1 - (2 / 3 : ℚ) ^ (offset + 1))) := by
  rw [lengthThreeReversingNormalizedSource,
    show q + A + 2 + offset = (q + A + 1) + (offset + 1) by omega, pow_add]
  ring

/-- For positive middle gauge, the normalized source decreases with the residual total gap. -/
theorem lengthThreeReversingNormalizedSource_antitone
    (p q A : ℕ) {first second : ℕ} (q_positive : 0 < q)
    (offset_order : first ≤ second) :
    lengthThreeReversingNormalizedSource p q A second ≤
      lengthThreeReversingNormalizedSource p q A first := by
  have first_power_positive : 0 < (2 / 3 : ℚ) ^ (first + 1) := by positivity
  have second_power_positive : 0 < (2 / 3 : ℚ) ^ (second + 1) := by positivity
  have first_power_lt_one : (2 / 3 : ℚ) ^ (first + 1) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have second_power_lt_one : (2 / 3 : ℚ) ^ (second + 1) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have first_denominator_positive :
      0 < 27 * (2 / 3 : ℚ) ^ (p + q + A + 1) *
        (1 - (2 / 3 : ℚ) ^ (first + 1)) := by positivity
  have second_denominator_positive :
      0 < 27 * (2 / 3 : ℚ) ^ (p + q + A + 1) *
        (1 - (2 / 3 : ℚ) ^ (second + 1)) := by positivity
  have power_order :
      (2 / 3 : ℚ) ^ (second + 1) ≤ (2 / 3 : ℚ) ^ (first + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have q_power_upper : (2 / 3 : ℚ) ^ q ≤ 2 / 3 := by
    have order := pow_le_pow_of_le_one
      (show 0 ≤ (2 / 3 : ℚ) by norm_num)
      (show (2 / 3 : ℚ) ≤ 1 by norm_num) q_positive
    norm_num at order ⊢
    exact order
  rw [lengthThreeReversingNormalizedSource_expanded,
    lengthThreeReversingNormalizedSource_expanded]
  apply (div_le_div_iff₀ second_denominator_positive first_denominator_positive).2
  have baseline_positive :
      0 < 27 * (2 / 3 : ℚ) ^ (p + q + A + 1) := by positivity
  have tail_coefficient_positive :
      0 < 9 * (2 / 3 : ℚ) ^ (q + A + 1) := by positivity
  have base_term_positive : 0 < 5 - 6 * (2 / 3 : ℚ) ^ q := by
    nlinarith
  have power_gap_nonnegative :
      0 ≤ (2 / 3 : ℚ) ^ (first + 1) - (2 / 3 : ℚ) ^ (second + 1) := by
    linarith
  have product_nonnegative :
      0 ≤ 27 * (2 / 3 : ℚ) ^ (p + q + A + 1) *
        ((5 - 6 * (2 / 3 : ℚ) ^ q) +
          9 * (2 / 3 : ℚ) ^ (q + A + 1)) *
        ((2 / 3 : ℚ) ^ (first + 1) - (2 / 3 : ℚ) ^ (second + 1)) :=
    mul_nonneg
      (mul_nonneg (le_of_lt baseline_positive)
        (by linarith :
          0 ≤ (5 - 6 * (2 / 3 : ℚ) ^ q) +
            9 * (2 / 3 : ℚ) ^ (q + A + 1)))
      power_gap_nonnegative
  have cross_difference :
      (5 - 6 * (2 / 3 : ℚ) ^ q +
          9 * (2 / 3 : ℚ) ^ (q + A + 1) * (2 / 3 : ℚ) ^ (first + 1)) *
            (27 * (2 / 3 : ℚ) ^ (p + q + A + 1) *
              (1 - (2 / 3 : ℚ) ^ (second + 1))) -
        (5 - 6 * (2 / 3 : ℚ) ^ q +
          9 * (2 / 3 : ℚ) ^ (q + A + 1) * (2 / 3 : ℚ) ^ (second + 1)) *
            (27 * (2 / 3 : ℚ) ^ (p + q + A + 1) *
              (1 - (2 / 3 : ℚ) ^ (first + 1))) =
      27 * (2 / 3 : ℚ) ^ (p + q + A + 1) *
        ((5 - 6 * (2 / 3 : ℚ) ^ q) +
          9 * (2 / 3 : ℚ) ^ (q + A + 1)) *
        ((2 / 3 : ℚ) ^ (first + 1) - (2 / 3 : ℚ) ^ (second + 1)) := by
    ring
  nlinarith

/-- A positive-middle-gauge source lies strictly above its infinite-gap limit. -/
theorem lengthThreeReversingNormalizedSource_gt_limit
    (p q A offset : ℕ) (q_positive : 0 < q) :
    (5 - 6 * (2 / 3 : ℚ) ^ q) /
        (27 * (2 / 3 : ℚ) ^ (p + q + A + 1)) <
      lengthThreeReversingNormalizedSource p q A offset := by
  have gap_power_positive : 0 < (2 / 3 : ℚ) ^ (offset + 1) := by positivity
  have gap_power_lt_one : (2 / 3 : ℚ) ^ (offset + 1) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have baseline_positive :
      0 < 27 * (2 / 3 : ℚ) ^ (p + q + A + 1) := by positivity
  have source_denominator_positive :
      0 < 27 * (2 / 3 : ℚ) ^ (p + q + A + 1) *
        (1 - (2 / 3 : ℚ) ^ (offset + 1)) := by positivity
  have q_power_upper : (2 / 3 : ℚ) ^ q ≤ 2 / 3 := by
    have order := pow_le_pow_of_le_one
      (show 0 ≤ (2 / 3 : ℚ) by norm_num)
      (show (2 / 3 : ℚ) ≤ 1 by norm_num) q_positive
    norm_num at order ⊢
    exact order
  rw [lengthThreeReversingNormalizedSource_expanded]
  apply (div_lt_div_iff₀ baseline_positive source_denominator_positive).2
  have tail_coefficient_positive :
      0 < 9 * (2 / 3 : ℚ) ^ (q + A + 1) := by positivity
  have base_term_positive : 0 < 5 - 6 * (2 / 3 : ℚ) ^ q := by
    nlinarith
  have product_positive :
      0 < 27 * (2 / 3 : ℚ) ^ (p + q + A + 1) *
        (2 / 3 : ℚ) ^ (offset + 1) *
        ((5 - 6 * (2 / 3 : ℚ) ^ q) +
          9 * (2 / 3 : ℚ) ^ (q + A + 1)) := by positivity
  have cross_difference :
      (5 - 6 * (2 / 3 : ℚ) ^ q +
          9 * (2 / 3 : ℚ) ^ (q + A + 1) * (2 / 3 : ℚ) ^ (offset + 1)) *
            (27 * (2 / 3 : ℚ) ^ (p + q + A + 1)) -
        (5 - 6 * (2 / 3 : ℚ) ^ q) *
            (27 * (2 / 3 : ℚ) ^ (p + q + A + 1) *
              (1 - (2 / 3 : ℚ) ^ (offset + 1))) =
      27 * (2 / 3 : ℚ) ^ (p + q + A + 1) *
        (2 / 3 : ℚ) ^ (offset + 1) *
        ((5 - 6 * (2 / 3 : ℚ) ^ q) +
          9 * (2 / 3 : ℚ) ^ (q + A + 1)) := by
    ring
  nlinarith

private theorem lengthThreeReversingNormalizedSource_mem_iff_interval
    (p q A lower upper : ℕ) (q_positive : 0 < q) (lower_positive : 0 < lower)
    (before_high :
      1 / 2 < lengthThreeReversingNormalizedSource p q A (lower - 1))
    (lower_upper :
      lengthThreeReversingNormalizedSource p q A lower ≤ 1 / 2)
    (upper_lower :
      1 / 5 ≤ lengthThreeReversingNormalizedSource p q A upper)
    (after_low :
      lengthThreeReversingNormalizedSource p q A (upper + 1) < 1 / 5)
    (offset : ℕ) :
    lengthThreeReversingNormalizedSource p q A offset ∈
        Set.Icc (1 / 5) (1 / 2) ↔
      lower ≤ offset ∧ offset ≤ upper := by
  constructor
  · intro source_mem
    constructor
    · by_contra offset_small
      have offset_le : offset ≤ lower - 1 := by omega
      have source_order := lengthThreeReversingNormalizedSource_antitone
        p q A q_positive offset_le
      exact (not_lt_of_ge source_mem.2) (before_high.trans_le source_order)
    · by_contra offset_large
      have after_le : upper + 1 ≤ offset := by omega
      have source_order := lengthThreeReversingNormalizedSource_antitone
        p q A q_positive after_le
      exact (not_lt_of_ge source_mem.1) (source_order.trans_lt after_low)
  · rintro ⟨lower_le, le_upper⟩
    have upper_order := lengthThreeReversingNormalizedSource_antitone
      p q A q_positive lower_le
    have lower_order := lengthThreeReversingNormalizedSource_antitone
      p q A q_positive le_upper
    exact ⟨upper_lower.trans lower_order, upper_order.trans lower_upper⟩

private theorem lengthThreeReversingNormalizedSource_mem_iff_ray
    (p q A lower : ℕ) (q_positive : 0 < q) (lower_positive : 0 < lower)
    (before_high :
      1 / 2 < lengthThreeReversingNormalizedSource p q A (lower - 1))
    (lower_upper :
      lengthThreeReversingNormalizedSource p q A lower ≤ 1 / 2)
    (limit_lower :
      1 / 5 ≤
        (5 - 6 * (2 / 3 : ℚ) ^ q) /
          (27 * (2 / 3 : ℚ) ^ (p + q + A + 1)))
    (offset : ℕ) :
    lengthThreeReversingNormalizedSource p q A offset ∈
        Set.Icc (1 / 5) (1 / 2) ↔
      lower ≤ offset := by
  constructor
  · intro source_mem
    by_contra offset_small
    have offset_le : offset ≤ lower - 1 := by omega
    have source_order := lengthThreeReversingNormalizedSource_antitone
      p q A q_positive offset_le
    exact (not_lt_of_ge source_mem.2) (before_high.trans_le source_order)
  · intro lower_le
    have upper_order := lengthThreeReversingNormalizedSource_antitone
      p q A q_positive lower_le
    have limit_lt := lengthThreeReversingNormalizedSource_gt_limit
      p q A offset q_positive
    exact ⟨limit_lower.trans limit_lt.le, upper_order.trans lower_upper⟩

private theorem reversing_q1_A1_p0 (offset : ℕ) :
    lengthThreeReversingNormalizedSource 0 1 1 offset ∈
        Set.Icc (1 / 5) (1 / 2) ↔
      1 ≤ offset ∧ offset ≤ 3 := by
  apply lengthThreeReversingNormalizedSource_mem_iff_interval
      0 1 1 1 3 (by norm_num) (by norm_num) <;>
    norm_num [lengthThreeReversingNormalizedSource]

private theorem reversing_q1_A1_p1 (offset : ℕ) :
    lengthThreeReversingNormalizedSource 1 1 1 offset ∈
        Set.Icc (1 / 5) (1 / 2) ↔
      2 ≤ offset ∧ offset ≤ 8 := by
  apply lengthThreeReversingNormalizedSource_mem_iff_interval
      1 1 1 2 8 (by norm_num) (by norm_num) <;>
    norm_num [lengthThreeReversingNormalizedSource]

private theorem reversing_q1_A1_p2 (offset : ℕ) :
    lengthThreeReversingNormalizedSource 2 1 1 offset ∈
        Set.Icc (1 / 5) (1 / 2) ↔
      4 ≤ offset := by
  apply lengthThreeReversingNormalizedSource_mem_iff_ray
      2 1 1 4 (by norm_num) (by norm_num) <;>
    norm_num [lengthThreeReversingNormalizedSource]

private theorem reversing_q1_A1_p3 (offset : ℕ) :
    lengthThreeReversingNormalizedSource 3 1 1 offset ∈
        Set.Icc (1 / 5) (1 / 2) ↔
      7 ≤ offset := by
  apply lengthThreeReversingNormalizedSource_mem_iff_ray
      3 1 1 7 (by norm_num) (by norm_num) <;>
    norm_num [lengthThreeReversingNormalizedSource]

private theorem reversing_q1_A2_p0 (offset : ℕ) :
    lengthThreeReversingNormalizedSource 0 1 2 offset ∈
        Set.Icc (1 / 5) (1 / 2) ↔
      2 ≤ offset ∧ offset ≤ 8 := by
  apply lengthThreeReversingNormalizedSource_mem_iff_interval
      0 1 2 2 8 (by norm_num) (by norm_num) <;>
    norm_num [lengthThreeReversingNormalizedSource]

/-- Exact real-trap ray for `q=1`, `A=2`, and head gauge one. -/
theorem lengthThreeReversing_q1_A2_p_one_mem_realTrap_iff (offset : ℕ) :
    lengthThreeReversingNormalizedSource 1 1 2 offset ∈
        Set.Icc (1 / 5) (1 / 2) ↔
      3 ≤ offset := by
  apply lengthThreeReversingNormalizedSource_mem_iff_ray
      1 1 2 3 (by norm_num) (by norm_num) <;>
    norm_num [lengthThreeReversingNormalizedSource]

/-- Exact real-trap ray for `q=1`, `A=2`, and head gauge two. -/
theorem lengthThreeReversing_q1_A2_p_two_mem_realTrap_iff (offset : ℕ) :
    lengthThreeReversingNormalizedSource 2 1 2 offset ∈
        Set.Icc (1 / 5) (1 / 2) ↔
      6 ≤ offset := by
  apply lengthThreeReversingNormalizedSource_mem_iff_ray
      2 1 2 6 (by norm_num) (by norm_num) <;>
    norm_num [lengthThreeReversingNormalizedSource]

private theorem reversing_q1_A3_p0 (offset : ℕ) :
    lengthThreeReversingNormalizedSource 0 1 3 offset ∈
        Set.Icc (1 / 5) (1 / 2) ↔
      3 ≤ offset := by
  apply lengthThreeReversingNormalizedSource_mem_iff_ray
      0 1 3 3 (by norm_num) (by norm_num) <;>
    norm_num [lengthThreeReversingNormalizedSource]

private theorem reversing_q1_A3_p1 (offset : ℕ) :
    lengthThreeReversingNormalizedSource 1 1 3 offset ∈
        Set.Icc (1 / 5) (1 / 2) ↔
      6 ≤ offset := by
  apply lengthThreeReversingNormalizedSource_mem_iff_ray
      1 1 3 6 (by norm_num) (by norm_num) <;>
    norm_num [lengthThreeReversingNormalizedSource]

private theorem reversing_q1_A4_p0 (offset : ℕ) :
    lengthThreeReversingNormalizedSource 0 1 4 offset ∈
        Set.Icc (1 / 5) (1 / 2) ↔
      5 ≤ offset := by
  apply lengthThreeReversingNormalizedSource_mem_iff_ray
      0 1 4 5 (by norm_num) (by norm_num) <;>
    norm_num [lengthThreeReversingNormalizedSource]

private theorem reversing_q2_A1_p0 (offset : ℕ) :
    lengthThreeReversingNormalizedSource 0 2 1 offset ∈
        Set.Icc (1 / 5) (1 / 2) ↔
      6 ≤ offset := by
  apply lengthThreeReversingNormalizedSource_mem_iff_ray
      0 2 1 6 (by norm_num) (by norm_num) <;>
    norm_num [lengthThreeReversingNormalizedSource]

/-- Exact Archimedean cells in the normalized reversing chamber. -/
def lengthThreeReversingRealCell (p q A offset : ℕ) : Prop :=
  (q = 0 ∧
    ((A = 1 ∧ offset = 0 ∧ p = 0) ∨
      (A = 1 ∧ offset = 1 ∧ (p = 2 ∨ p = 3)) ∨
      (A = 1 ∧ offset = 2 ∧ (p = 6 ∨ p = 7)) ∨
      (A = 2 ∧ offset = 0 ∧ (p = 0 ∨ p = 1)) ∨
      (A = 2 ∧ offset = 1 ∧ (p = 4 ∨ p = 5 ∨ p = 6)) ∨
      (A = 3 ∧ offset = 0 ∧ (p = 2 ∨ p = 3)))) ∨
  (q = 1 ∧
    ((A = 1 ∧ p = 0 ∧ 1 ≤ offset ∧ offset ≤ 3) ∨
      (A = 1 ∧ p = 1 ∧ 2 ≤ offset ∧ offset ≤ 8) ∨
      (A = 1 ∧ p = 2 ∧ 4 ≤ offset) ∨
      (A = 1 ∧ p = 3 ∧ 7 ≤ offset) ∨
      (A = 2 ∧ p = 0 ∧ 2 ≤ offset ∧ offset ≤ 8) ∨
      (A = 2 ∧ p = 1 ∧ 3 ≤ offset) ∨
      (A = 2 ∧ p = 2 ∧ 6 ≤ offset) ∨
      (A = 3 ∧ p = 0 ∧ 3 ≤ offset) ∨
      (A = 3 ∧ p = 1 ∧ 6 ≤ offset) ∨
      (A = 4 ∧ p = 0 ∧ 5 ≤ offset))) ∨
  (q = 2 ∧ A = 1 ∧ p = 0 ∧ 6 ≤ offset)

/-- Complete real-trap classifier for the normalized reversing chamber. -/
theorem lengthThreeReversingNormalizedSource_mem_realTrap_iff
    (p q A offset : ℕ) (A_positive : 0 < A) :
    lengthThreeReversingNormalizedSource p q A offset ∈
        Set.Icc (1 / 5) (1 / 2) ↔
      lengthThreeReversingRealCell p q A offset := by
  have q_cases : q = 0 ∨ q = 1 ∨ q = 2 ∨ 3 ≤ q := by omega
  rcases q_cases with q_zero | q_one | q_two | q_large
  · subst q
    constructor
    · intro source_mem
      have p_le := lengthThreeReversingNormalizedSource_realTrap_forces_p_le_seven
        p 0 A offset A_positive source_mem
      have source_positive :
          0 < lengthThreeReversingNormalizedSource p 0 A offset :=
        lt_of_lt_of_le (by norm_num) source_mem.1
      have gap_power_lt : (2 / 3 : ℚ) ^ (offset + 1) < 1 :=
        pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
      have denominator_positive :
          0 < 27 * (2 / 3 : ℚ) ^ (p + 0 + A + 1) *
            (1 - (2 / 3 : ℚ) ^ (offset + 1)) := by positivity
      have numerator_positive :
          0 < -1 + 9 * (2 / 3 : ℚ) ^ (A + 2 + offset) := by
        rw [lengthThreeReversingNormalizedSource] at source_positive
        have raw := (div_pos_iff_of_pos_right denominator_positive).1 source_positive
        norm_num at raw
        linarith
      have exponent_le_five : A + 2 + offset ≤ 5 := by
        by_contra exponent_large
        have six_le : 6 ≤ A + 2 + offset := by omega
        have power_upper :
            (2 / 3 : ℚ) ^ (A + 2 + offset) ≤ (2 / 3 : ℚ) ^ 6 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) six_le
        norm_num at numerator_positive power_upper
        nlinarith
      have A_le : A ≤ 3 := by omega
      have offset_le : offset ≤ 2 := by omega
      interval_cases A <;> interval_cases offset <;> interval_cases p <;>
        norm_num [lengthThreeReversingNormalizedSource] at source_mem <;>
        norm_num [lengthThreeReversingRealCell]
    · intro cell
      rcases cell with ⟨_, row⟩ | ⟨q_one, _⟩ | ⟨q_two, _⟩
      · rcases row with
          ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl | rfl⟩ |
          ⟨rfl, rfl, rfl | rfl⟩ | ⟨rfl, rfl, rfl | rfl⟩ |
          ⟨rfl, rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl, rfl | rfl⟩ <;>
          norm_num [lengthThreeReversingNormalizedSource]
      · omega
      · omega
  · subst q
    constructor
    · intro source_mem
      have A_le := lengthThreeReversingNormalizedSource_realTrap_forces_A_le_four
        p 1 A offset A_positive source_mem
      have limit_lt := lengthThreeReversingNormalizedSource_gt_limit
        p 1 A offset (by norm_num)
      have p_add_A_le : p + A ≤ 4 := by
        by_contra sum_large
        have five_le : 5 ≤ p + A := by omega
        have seven_le : 7 ≤ p + 1 + A + 1 := by omega
        have power_upper :
            (2 / 3 : ℚ) ^ (p + 1 + A + 1) ≤ (2 / 3 : ℚ) ^ 7 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) seven_le
        have limit_gt :
            1 / 2 <
              (5 - 6 * (2 / 3 : ℚ) ^ 1) /
                (27 * (2 / 3 : ℚ) ^ (p + 1 + A + 1)) := by
          have denominator_positive :
              0 < 27 * (2 / 3 : ℚ) ^ (p + 1 + A + 1) := by positivity
          apply (lt_div_iff₀ denominator_positive).2
          norm_num at power_upper ⊢
          nlinarith
        exact (not_lt_of_ge source_mem.2) (limit_gt.trans limit_lt)
      have A_cases : A = 1 ∨ A = 2 ∨ A = 3 ∨ A = 4 := by omega
      rcases A_cases with rfl | rfl | rfl | rfl
      · have p_cases : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by omega
        rcases p_cases with rfl | rfl | rfl | rfl
        · exact Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, rfl,
            (reversing_q1_A1_p0 offset).1 source_mem⟩⟩)
        · exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl,
            (reversing_q1_A1_p1 offset).1 source_mem⟩)⟩)
        · exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl,
            (reversing_q1_A1_p2 offset).1 source_mem⟩))⟩)
        · exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl,
            (reversing_q1_A1_p3 offset).1 source_mem⟩)))⟩)
      · have p_cases : p = 0 ∨ p = 1 ∨ p = 2 := by omega
        rcases p_cases with rfl | rfl | rfl
        · exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨rfl, rfl, (reversing_q1_A2_p0 offset).1 source_mem⟩))))⟩)
        · exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨rfl, rfl,
              (lengthThreeReversing_q1_A2_p_one_mem_realTrap_iff offset).1 source_mem⟩)))))⟩)
        · exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl ⟨rfl, rfl,
              (lengthThreeReversing_q1_A2_p_two_mem_realTrap_iff offset).1 source_mem⟩))))))⟩)
      · have p_cases : p = 0 ∨ p = 1 := by omega
        rcases p_cases with rfl | rfl
        · exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inl ⟨rfl, rfl,
              (reversing_q1_A3_p0 offset).1 source_mem⟩)))))))⟩)
        · exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr (Or.inl ⟨rfl, rfl,
              (reversing_q1_A3_p1 offset).1 source_mem⟩))))))))⟩)
      · have p_zero : p = 0 := by omega
        subst p
        exact Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr ⟨rfl, rfl,
            (reversing_q1_A4_p0 offset).1 source_mem⟩))))))))⟩)
    · intro cell
      rcases cell with _ | ⟨_, row⟩ | _
      · omega
      · rcases row with first | tail
        · rcases first with ⟨rfl, rfl, lower, upper⟩
          exact (reversing_q1_A1_p0 offset).2 ⟨lower, upper⟩
        · rcases tail with second | tail
          · rcases second with ⟨rfl, rfl, lower, upper⟩
            exact (reversing_q1_A1_p1 offset).2 ⟨lower, upper⟩
          · rcases tail with third | tail
            · rcases third with ⟨rfl, rfl, lower⟩
              exact (reversing_q1_A1_p2 offset).2 lower
            · rcases tail with fourth | tail
              · rcases fourth with ⟨rfl, rfl, lower⟩
                exact (reversing_q1_A1_p3 offset).2 lower
              · rcases tail with fifth | tail
                · rcases fifth with ⟨rfl, rfl, lower, upper⟩
                  exact (reversing_q1_A2_p0 offset).2 ⟨lower, upper⟩
                · rcases tail with sixth | tail
                  · rcases sixth with ⟨rfl, rfl, lower⟩
                    exact (lengthThreeReversing_q1_A2_p_one_mem_realTrap_iff offset).2 lower
                  · rcases tail with seventh | tail
                    · rcases seventh with ⟨rfl, rfl, lower⟩
                      exact (lengthThreeReversing_q1_A2_p_two_mem_realTrap_iff offset).2 lower
                    · rcases tail with eighth | tail
                      · rcases eighth with ⟨rfl, rfl, lower⟩
                        exact (reversing_q1_A3_p0 offset).2 lower
                      · rcases tail with ninth | tenth
                        · rcases ninth with ⟨rfl, rfl, lower⟩
                          exact (reversing_q1_A3_p1 offset).2 lower
                        · rcases tenth with ⟨rfl, rfl, lower⟩
                          exact (reversing_q1_A4_p0 offset).2 lower
      · omega
  · subst q
    constructor
    · intro source_mem
      have limit_lt := lengthThreeReversingNormalizedSource_gt_limit
        p 2 A offset (by norm_num)
      have p_add_A_le : p + A ≤ 1 := by
        by_contra sum_large
        have two_le : 2 ≤ p + A := by omega
        have five_le : 5 ≤ p + 2 + A + 1 := by omega
        have power_upper :
            (2 / 3 : ℚ) ^ (p + 2 + A + 1) ≤ (2 / 3 : ℚ) ^ 5 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) five_le
        have limit_gt :
            1 / 2 <
              (5 - 6 * (2 / 3 : ℚ) ^ 2) /
                (27 * (2 / 3 : ℚ) ^ (p + 2 + A + 1)) := by
          have denominator_positive :
              0 < 27 * (2 / 3 : ℚ) ^ (p + 2 + A + 1) := by positivity
          apply (lt_div_iff₀ denominator_positive).2
          norm_num at power_upper ⊢
          nlinarith
        exact (not_lt_of_ge source_mem.2) (limit_gt.trans limit_lt)
      have A_one : A = 1 := by omega
      have p_zero : p = 0 := by omega
      subst A
      subst p
      exact Or.inr (Or.inr ⟨rfl, rfl, rfl,
        (reversing_q2_A1_p0 offset).1 source_mem⟩)
    · intro cell
      rcases cell with _ | _ | ⟨_, A_one, p_zero, lower⟩
      · omega
      · omega
      · subst A
        subst p
        exact (reversing_q2_A1_p0 offset).2 lower
  · constructor
    · intro source_mem
      have q_le := lengthThreeReversingNormalizedSource_realTrap_forces_q_le_two
        p q A offset A_positive source_mem
      omega
    · intro cell
      rcases cell with ⟨q_zero, _⟩ | ⟨q_one, _⟩ | ⟨q_two, _⟩ <;> omega


end MatrixMortality.MixedPrimeDebt
