import MatrixMortality.MixedPrimeRealTrapLengthThree

/-!
# Remaining length-three sign chambers

After orienting a cross-grade pair by total wait and stripping common initial and terminal
coordinates, the suffix antichain leaves four endpoint-strict coordinate-sign chambers. The
first is closed along its middle-zero wall and is treated in `MixedPrimeRealTrapLengthThree`.
This module and its two residue-classifier companions classify the other three strict chambers.

The positive-negative-negative chamber dies over the reals: its collision source is always
strictly above `1/2`. The two alternating chambers require exact residue classifiers.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation
open PeriodicShell

private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private theorem rebounding_unit_pow
    {value : ℚ} (value_unit : IsUnit 5 value) (exponent : ℕ) :
    IsUnit 5 (value ^ exponent) := by
  refine ⟨pow_ne_zero exponent value_unit.1, ?_⟩
  rw [padicValRat.pow, value_unit.2]
  simp

private theorem one_sub_shellRatio_pow_hasValue
    {exponent : ℕ} (exponent_positive : 0 < exponent) :
    HasValue 5 (1 - (2 / 3 : ℚ) ^ exponent)
      (shellSlopeGapFiveDepth exponent) := by
  have negative_value := neg_hasValue
    (shellRatio_pow_sub_one_hasValue exponent_positive)
  convert negative_value using 1
  ring

private theorem hasValue_of_sub_higher_iff
    {later earlier : ℚ} {lower higher : ℤ} (lower_lt_higher : lower < higher)
    (difference_value : HasValue 5 (later - earlier) higher) :
    HasValue 5 later lower ↔ HasValue 5 earlier lower := by
  have reverse_value : HasValue 5 (earlier - later) higher := by
    convert neg_hasValue difference_value using 1
    ring
  constructor
  · intro later_value
    have earlier_value := add_hasValue_right reverse_value later_value lower_lt_higher
    convert earlier_value using 1
    ring
  · intro earlier_value
    have later_value := add_hasValue_right difference_value earlier_value lower_lt_higher
    convert later_value using 1
    ring

private theorem shellOffset_nil' : shellOffset [] = 0 := by
  have run_nil : shellRun [] (0 : ℚ) = 0 := rfl
  rw [shellOffset, shellIntercept, run_nil]
  norm_num

private theorem shellOffset_triple' (a b c : ℕ) :
    shellOffset [a, b, c] =
      9 * (2 / 3 : ℚ) ^ (b + c) + 15 * (2 / 3 : ℚ) ^ c + 25 := by
  rw [shellOffset_cons, shellOffset_cons, shellOffset_cons, shellOffset_nil']
  simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, pow_succ, pow_zero]
  ring

/-- Left schedule in the strict positive-negative-negative chamber. -/
def lengthThreeDoublyFallingLeft (p q t A : ℕ) : List ℕ :=
  [p + A, q, t]

/-- Right schedule in the strict positive-negative-negative chamber. -/
def lengthThreeDoublyFallingRight (p q t B k : ℕ) : List ℕ :=
  [p, q + B, t + k]

/-- Exact collision source in the strict positive-negative-negative chamber. -/
def lengthThreeDoublyFallingSource (p q A B k : ℕ) : ℚ :=
  (9 * (2 / 3 : ℚ) ^ q * (1 - (2 / 3 : ℚ) ^ (B + k)) +
      15 * (1 - (2 / 3 : ℚ) ^ k)) /
    (27 * (2 / 3 : ℚ) ^ (p + q) *
      ((2 / 3 : ℚ) ^ (B + k) - (2 / 3 : ℚ) ^ A))

theorem lengthThreeDoublyFalling_collisionSource
    (p q t A B k : ℕ) (total_positive : B + k < A) :
    collisionSource (lengthThreeDoublyFallingLeft p q t A)
        (lengthThreeDoublyFallingRight p q t B k) =
      lengthThreeDoublyFallingSource p q A B k := by
  have length_eq :
      (lengthThreeDoublyFallingLeft p q t A).length =
        (lengthThreeDoublyFallingRight p q t B k).length := by
    rfl
  have sum_ne :
      (lengthThreeDoublyFallingLeft p q t A).sum ≠
        (lengthThreeDoublyFallingRight p q t B k).sum := by
    simp only [lengthThreeDoublyFallingLeft, lengthThreeDoublyFallingRight,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  have base_ne : (2 / 3 : ℚ) ≠ 0 := by norm_num
  have gap_positive :
      (2 / 3 : ℚ) ^ A < (2 / 3 : ℚ) ^ (B + k) :=
    pow_right_strictAnti₀ (by norm_num) (by norm_num) total_positive
  have gap_ne : (2 / 3 : ℚ) ^ (B + k) - (2 / 3 : ℚ) ^ A ≠ 0 := by
    linarith
  have offset_difference :
      shellOffset (lengthThreeDoublyFallingLeft p q t A) -
          shellOffset (lengthThreeDoublyFallingRight p q t B k) =
        (2 / 3 : ℚ) ^ t *
          (9 * (2 / 3 : ℚ) ^ q * (1 - (2 / 3 : ℚ) ^ (B + k)) +
            15 * (1 - (2 / 3 : ℚ) ^ k)) := by
    rw [lengthThreeDoublyFallingLeft, lengthThreeDoublyFallingRight,
      shellOffset_triple', shellOffset_triple']
    simp only [pow_add]
    ring
  have gain_difference :
      shellGain (lengthThreeDoublyFallingRight p q t B k) -
          shellGain (lengthThreeDoublyFallingLeft p q t A) =
        27 * (2 / 3 : ℚ) ^ (p + q + t) *
          ((2 / 3 : ℚ) ^ (B + k) - (2 / 3 : ℚ) ^ A) := by
    simp only [lengthThreeDoublyFallingLeft, lengthThreeDoublyFallingRight,
      shellGain, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, pow_add]
    ring
  rw [collisionSource_eq_clearedBalance length_eq sum_ne,
    offset_difference, gain_difference, lengthThreeDoublyFallingSource,
    show p + q + t = (p + q) + t by omega, pow_add]
  field_simp [base_ne, gap_ne]
  ring

/-- The positive-negative-negative chamber lies strictly above the real trap. -/
theorem lengthThreeDoublyFallingSource_gt_half
    (p q A B k : ℕ) (B_pos : 0 < B) (k_pos : 0 < k)
    (total_positive : B + k < A) :
    1 / 2 < lengthThreeDoublyFallingSource p q A B k := by
  have q_power_nonnegative : 0 ≤ (2 / 3 : ℚ) ^ q := by positivity
  have q_power_le_one : (2 / 3 : ℚ) ^ q ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have p_power_le_one : (2 / 3 : ℚ) ^ p ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have k_power_upper : (2 / 3 : ℚ) ^ k ≤ 2 / 3 := by
    have power_order := pow_le_pow_of_le_one
      (show 0 ≤ (2 / 3 : ℚ) by norm_num) (show (2 / 3 : ℚ) ≤ 1 by norm_num)
      k_pos
    norm_num at power_order ⊢
    exact power_order
  have combined_power_upper : (2 / 3 : ℚ) ^ (B + k) ≤ 4 / 9 := by
    have two_le : 2 ≤ B + k := by omega
    have power_order := pow_le_pow_of_le_one
      (show 0 ≤ (2 / 3 : ℚ) by norm_num) (show (2 / 3 : ℚ) ≤ 1 by norm_num)
      two_le
    norm_num at power_order ⊢
    exact power_order
  have total_power_lt :
      (2 / 3 : ℚ) ^ A < (2 / 3 : ℚ) ^ (B + k) :=
    pow_right_strictAnti₀ (by norm_num) (by norm_num) total_positive
  have denominator_positive :
      0 < 27 * (2 / 3 : ℚ) ^ (p + q) *
        ((2 / 3 : ℚ) ^ (B + k) - (2 / 3 : ℚ) ^ A) := by
    positivity
  have numerator_lower :
      5 * (2 / 3 : ℚ) ^ q + 5 ≤
        9 * (2 / 3 : ℚ) ^ q * (1 - (2 / 3 : ℚ) ^ (B + k)) +
          15 * (1 - (2 / 3 : ℚ) ^ k) := by
    nlinarith
  have baseline_upper :
      (2 / 3 : ℚ) ^ (p + q) ≤ (2 / 3 : ℚ) ^ q := by
    rw [pow_add]
    nlinarith
  have difference_positive :
      0 < (2 / 3 : ℚ) ^ (B + k) - (2 / 3 : ℚ) ^ A := by
    linarith
  have denominator_upper :
      27 * (2 / 3 : ℚ) ^ (p + q) *
          ((2 / 3 : ℚ) ^ (B + k) - (2 / 3 : ℚ) ^ A) <
        12 * (2 / 3 : ℚ) ^ q := by
    calc
      27 * (2 / 3 : ℚ) ^ (p + q) *
          ((2 / 3 : ℚ) ^ (B + k) - (2 / 3 : ℚ) ^ A) <
          27 * (2 / 3 : ℚ) ^ (p + q) * (2 / 3 : ℚ) ^ (B + k) := by
            have baseline_positive : 0 < 27 * (2 / 3 : ℚ) ^ (p + q) := by positivity
            nlinarith [show 0 < (2 / 3 : ℚ) ^ A by positivity]
      _ ≤ 27 * (2 / 3 : ℚ) ^ q * (4 / 9) := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left baseline_upper (by norm_num))
              combined_power_upper (by positivity) (by positivity)
      _ = 12 * (2 / 3 : ℚ) ^ q := by ring
  rw [lengthThreeDoublyFallingSource]
  apply (lt_div_iff₀ denominator_positive).2
  nlinarith

/-- No strict positive-negative-negative collision source lies in the real trap. -/
theorem lengthThreeDoublyFallingSource_not_mem_realTrap
    (p q A B k : ℕ) (B_pos : 0 < B) (k_pos : 0 < k)
    (total_positive : B + k < A) :
    lengthThreeDoublyFallingSource p q A B k ∉ Set.Icc (1 / 5) (1 / 2) := by
  intro source_mem
  exact (not_lt_of_ge source_mem.2)
    (lengthThreeDoublyFallingSource_gt_half p q A B k B_pos k_pos total_positive)

/-- No strict positive-negative-negative collision lies in the real trap. -/
theorem lengthThreeDoublyFalling_collision_not_mem_realTrap
    (p q t A B k : ℕ) (B_pos : 0 < B) (k_pos : 0 < k)
    (total_positive : B + k < A) :
    collisionSource (lengthThreeDoublyFallingLeft p q t A)
      (lengthThreeDoublyFallingRight p q t B k) ∉ Set.Icc (1 / 5) (1 / 2) := by
  rw [lengthThreeDoublyFalling_collisionSource p q t A B k total_positive]
  exact lengthThreeDoublyFallingSource_not_mem_realTrap
    p q A B k B_pos k_pos total_positive

/-- Left schedule in the strict positive-negative-positive chamber. -/
def lengthThreeReboundingLeft (p q t A k : ℕ) : List ℕ :=
  [p + A, q, t + k]

/-- Right schedule in the strict positive-negative-positive chamber. -/
def lengthThreeReboundingRight (p q t B : ℕ) : List ℕ :=
  [p, q + B, t]

/-- Exact collision source in the strict positive-negative-positive chamber. -/
def lengthThreeReboundingSource (p q A B k : ℕ) : ℚ :=
  (9 * (2 / 3 : ℚ) ^ q * ((2 / 3 : ℚ) ^ k - (2 / 3 : ℚ) ^ B) -
      15 * (1 - (2 / 3 : ℚ) ^ k)) /
    (27 * (2 / 3 : ℚ) ^ (p + q) *
      ((2 / 3 : ℚ) ^ B - (2 / 3 : ℚ) ^ (A + k)))

theorem lengthThreeRebounding_collisionSource
    (p q t A B k : ℕ) (total_positive : B < A + k) :
    collisionSource (lengthThreeReboundingLeft p q t A k)
        (lengthThreeReboundingRight p q t B) =
      lengthThreeReboundingSource p q A B k := by
  have length_eq :
      (lengthThreeReboundingLeft p q t A k).length =
        (lengthThreeReboundingRight p q t B).length := by
    rfl
  have sum_ne :
      (lengthThreeReboundingLeft p q t A k).sum ≠
        (lengthThreeReboundingRight p q t B).sum := by
    simp only [lengthThreeReboundingLeft, lengthThreeReboundingRight,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  have base_ne : (2 / 3 : ℚ) ≠ 0 := by norm_num
  have gap_positive :
      (2 / 3 : ℚ) ^ (A + k) < (2 / 3 : ℚ) ^ B :=
    pow_right_strictAnti₀ (by norm_num) (by norm_num) total_positive
  have gap_ne : (2 / 3 : ℚ) ^ B - (2 / 3 : ℚ) ^ (A + k) ≠ 0 := by
    linarith
  have offset_difference :
      shellOffset (lengthThreeReboundingLeft p q t A k) -
          shellOffset (lengthThreeReboundingRight p q t B) =
        (2 / 3 : ℚ) ^ t *
          (9 * (2 / 3 : ℚ) ^ q *
              ((2 / 3 : ℚ) ^ k - (2 / 3 : ℚ) ^ B) -
            15 * (1 - (2 / 3 : ℚ) ^ k)) := by
    rw [lengthThreeReboundingLeft, lengthThreeReboundingRight,
      shellOffset_triple', shellOffset_triple']
    simp only [pow_add]
    ring
  have gain_difference :
      shellGain (lengthThreeReboundingRight p q t B) -
          shellGain (lengthThreeReboundingLeft p q t A k) =
        27 * (2 / 3 : ℚ) ^ (p + q + t) *
          ((2 / 3 : ℚ) ^ B - (2 / 3 : ℚ) ^ (A + k)) := by
    simp only [lengthThreeReboundingLeft, lengthThreeReboundingRight,
      shellGain, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, pow_add]
    ring
  rw [collisionSource_eq_clearedBalance length_eq sum_ne,
    offset_difference, gain_difference, lengthThreeReboundingSource,
    show p + q + t = (p + q) + t by omega, pow_add]
  field_simp [base_ne, gap_ne]

private theorem lengthThreeReboundingNumerator_pos_iff
    (q B k : ℕ) (k_pos : 0 < k) (rise_before_fall : k < B) :
    0 <
        9 * (2 / 3 : ℚ) ^ q * ((2 / 3 : ℚ) ^ k - (2 / 3 : ℚ) ^ B) -
          15 * (1 - (2 / 3 : ℚ) ^ k) ↔
      k = 1 ∧ q = 0 ∧ 6 ≤ B := by
  constructor
  · intro numerator_pos
    have q_power_nonnegative : 0 ≤ (2 / 3 : ℚ) ^ q := by positivity
    have q_power_le_one : (2 / 3 : ℚ) ^ q ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have B_power_nonnegative : 0 ≤ (2 / 3 : ℚ) ^ B := by positivity
    have k_lt_two : k < 2 := by
      by_contra k_not_lt
      have two_le : 2 ≤ k := by omega
      have k_power_upper : (2 / 3 : ℚ) ^ k ≤ 4 / 9 := by
        have power_order := pow_le_pow_of_le_one
          (show 0 ≤ (2 / 3 : ℚ) by norm_num)
          (show (2 / 3 : ℚ) ≤ 1 by norm_num) two_le
        norm_num at power_order ⊢
        exact power_order
      nlinarith
    have k_one : k = 1 := by omega
    subst k
    have q_zero : q = 0 := by
      by_contra q_ne_zero
      have q_pos : 0 < q := Nat.pos_of_ne_zero q_ne_zero
      have q_power_upper : (2 / 3 : ℚ) ^ q ≤ 2 / 3 := by
        have power_order := pow_le_pow_of_le_one
          (show 0 ≤ (2 / 3 : ℚ) by norm_num)
          (show (2 / 3 : ℚ) ≤ 1 by norm_num) q_pos
        norm_num at power_order ⊢
        exact power_order
      nlinarith
    subst q
    have six_le : 6 ≤ B := by
      by_contra six_not_le
      have B_le_five : B ≤ 5 := by omega
      have power_lower : (2 / 3 : ℚ) ^ 5 ≤ (2 / 3 : ℚ) ^ B := by
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) B_le_five
      norm_num at numerator_pos power_lower
      nlinarith
    exact ⟨rfl, rfl, six_le⟩
  · rintro ⟨rfl, rfl, six_le⟩
    have power_upper : (2 / 3 : ℚ) ^ B ≤ (2 / 3 : ℚ) ^ 6 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) six_le
    norm_num at power_upper ⊢
    nlinarith

/-- Positivity rigidifies the alternating chamber to one tail rise and no middle gauge. -/
theorem lengthThreeReboundingSource_pos_iff
    (p q A B k : ℕ) (k_pos : 0 < k) (rise_before_fall : k < B)
    (total_positive : B < A + k) :
    0 < lengthThreeReboundingSource p q A B k ↔
      k = 1 ∧ q = 0 ∧ 6 ≤ B := by
  have total_power_lt :
      (2 / 3 : ℚ) ^ (A + k) < (2 / 3 : ℚ) ^ B :=
    pow_right_strictAnti₀ (by norm_num) (by norm_num) total_positive
  have denominator_positive :
      0 < 27 * (2 / 3 : ℚ) ^ (p + q) *
        ((2 / 3 : ℚ) ^ B - (2 / 3 : ℚ) ^ (A + k)) := by
    positivity
  rw [lengthThreeReboundingSource]
  exact (div_pos_iff_of_pos_right denominator_positive).trans
    (lengthThreeReboundingNumerator_pos_iff q B k k_pos rise_before_fall)

/-- Exact normalized source after positivity fixes the middle gauge and tail rise. -/
theorem lengthThreeReboundingSource_normalized
    (p B offset : ℕ) :
    lengthThreeReboundingSource p 0 (B + offset) B 1 =
      (1 - 9 * (2 / 3 : ℚ) ^ B) /
        (27 * (2 / 3 : ℚ) ^ (p + B) *
          (1 - (2 / 3 : ℚ) ^ (offset + 1))) := by
  have base_ne : (2 / 3 : ℚ) ≠ 0 := by norm_num
  have gap_positive : 0 < offset + 1 := by omega
  have gap_ne : 1 - (2 / 3 : ℚ) ^ (offset + 1) ≠ 0 := by
    have power_lt : (2 / 3 : ℚ) ^ (offset + 1) < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) gap_positive.ne'
    linarith
  rw [lengthThreeReboundingSource]
  simp only [pow_zero]
  rw [show B + offset + 1 = B + (offset + 1) by omega,
    show p + 0 = p by omega, pow_add, show p + B = p + B by rfl]
  field_simp [base_ne, gap_ne]
  ring

/-- The real upper trap cuts every positive normalized rebounding source to `B ≤ 7`. -/
theorem lengthThreeReboundingSource_realTrap_forces_B_le_seven
    (p B offset : ℕ)
    (source_mem :
      lengthThreeReboundingSource p 0 (B + offset) B 1 ∈
        Set.Icc (1 / 5) (1 / 2)) :
    B ≤ 7 := by
  by_contra B_large
  have eight_le : 8 ≤ B := by omega
  have B_power_positive : 0 < (2 / 3 : ℚ) ^ B := by positivity
  have B_power_upper : (2 / 3 : ℚ) ^ B ≤ (2 / 3 : ℚ) ^ 8 := by
    exact pow_le_pow_of_le_one
      (show 0 ≤ (2 / 3 : ℚ) by norm_num)
      (show (2 / 3 : ℚ) ≤ 1 by norm_num) eight_le
  have p_power_positive : 0 < (2 / 3 : ℚ) ^ p := by positivity
  have p_power_le_one : (2 / 3 : ℚ) ^ p ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have gap_power_positive : 0 < (2 / 3 : ℚ) ^ (offset + 1) := by positivity
  have gap_power_lt_one : (2 / 3 : ℚ) ^ (offset + 1) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have denominator_positive :
      0 < 27 * (2 / 3 : ℚ) ^ (p + B) *
        (1 - (2 / 3 : ℚ) ^ (offset + 1)) := by
    positivity
  have baseline_upper :
      (2 / 3 : ℚ) ^ (p + B) ≤ (2 / 3 : ℚ) ^ B := by
    rw [pow_add]
    nlinarith
  have denominator_upper :
      27 * (2 / 3 : ℚ) ^ (p + B) *
          (1 - (2 / 3 : ℚ) ^ (offset + 1)) <
        27 * (2 / 3 : ℚ) ^ B := by
    have gap_factor_positive :
        0 < 1 - (2 / 3 : ℚ) ^ (offset + 1) := by linarith
    have gap_factor_lt_one :
        1 - (2 / 3 : ℚ) ^ (offset + 1) < 1 := by linarith
    nlinarith
  have numerator_large :
      (27 * (2 / 3 : ℚ) ^ B) / 2 <
        1 - 9 * (2 / 3 : ℚ) ^ B := by
    norm_num at B_power_upper ⊢
    nlinarith
  have source_gt_half :
      1 / 2 < lengthThreeReboundingSource p 0 (B + offset) B 1 := by
    rw [lengthThreeReboundingSource_normalized]
    apply (lt_div_iff₀ denominator_positive).2
    nlinarith
  exact (not_lt_of_ge source_mem.2) source_gt_half

/-- Positivity and the real trap leave only the two middle gaps six and seven. -/
theorem lengthThreeReboundingSource_positive_realTrap_parameter_cut
    (p q A B k : ℕ) (k_pos : 0 < k) (rise_before_fall : k < B)
    (total_positive : B < A + k)
    (source_mem :
      lengthThreeReboundingSource p q A B k ∈ Set.Icc (1 / 5) (1 / 2)) :
    k = 1 ∧ q = 0 ∧ (B = 6 ∨ B = 7) := by
  have source_pos : 0 < lengthThreeReboundingSource p q A B k := by
    linarith [source_mem.1]
  obtain ⟨k_one, q_zero, six_le⟩ :=
    (lengthThreeReboundingSource_pos_iff
      p q A B k k_pos rise_before_fall total_positive).1 source_pos
  subst k
  subst q
  have B_le_A : B ≤ A := by omega
  let offset := A - B
  have A_eq : A = B + offset := by
    simp only [offset]
    omega
  rw [A_eq] at source_mem
  have B_le_seven :=
    lengthThreeReboundingSource_realTrap_forces_B_le_seven p B offset source_mem
  exact ⟨rfl, rfl, by omega⟩

/-- Exact normalized source in the `B=6` positive-negative-positive fibre. -/
theorem lengthThreeReboundingSource_six
    (p offset : ℕ) :
    lengthThreeReboundingSource p 0 (6 + offset) 6 1 =
      (17 / 192 : ℚ) * (3 / 2 : ℚ) ^ p /
        (1 - (2 / 3 : ℚ) ^ (offset + 1)) := by
  rw [lengthThreeReboundingSource]
  have base_ne : (2 / 3 : ℚ) ≠ 0 := by norm_num
  have gap_positive : 0 < offset + 1 := by omega
  have gap_ne : 1 - (2 / 3 : ℚ) ^ (offset + 1) ≠ 0 := by
    have power_lt : (2 / 3 : ℚ) ^ (offset + 1) < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) gap_positive.ne'
    linarith
  simp only [pow_zero]
  rw [show 6 + offset + 1 = 6 + (offset + 1) by omega]
  have gap_factor :
      (2 / 3 : ℚ) ^ 6 - (2 / 3 : ℚ) ^ (6 + (offset + 1)) =
        (2 / 3 : ℚ) ^ 6 * (1 - (2 / 3 : ℚ) ^ (offset + 1)) := by
    rw [pow_add]
    ring
  have offset_power_le_one : (2 / 3 : ℚ) ^ offset ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have scaled_gap_ne : 3 - 2 * (2 / 3 : ℚ) ^ offset ≠ 0 := by
    have : 0 < 3 - 2 * (2 / 3 : ℚ) ^ offset := by nlinarith
    exact ne_of_gt this
  have scaled_gap_ne' : 3 - (2 / 3 : ℚ) ^ offset * 2 ≠ 0 := by
    nlinarith
  rw [gap_factor]
  have reciprocal_power :
      (3 / 2 : ℚ) ^ p = ((2 / 3 : ℚ) ^ p)⁻¹ := by
    rw [← inv_pow]
    congr 2
    norm_num
  rw [reciprocal_power]
  field_simp [base_ne, gap_ne, scaled_gap_ne, scaled_gap_ne']
  ring

/-- Exact normalized source in the `B=7` positive-negative-positive fibre. -/
theorem lengthThreeReboundingSource_seven
    (p offset : ℕ) :
    lengthThreeReboundingSource p 0 (7 + offset) 7 1 =
      (115 / 384 : ℚ) * (3 / 2 : ℚ) ^ p /
        (1 - (2 / 3 : ℚ) ^ (offset + 1)) := by
  rw [lengthThreeReboundingSource]
  have base_ne : (2 / 3 : ℚ) ≠ 0 := by norm_num
  have gap_positive : 0 < offset + 1 := by omega
  have gap_ne : 1 - (2 / 3 : ℚ) ^ (offset + 1) ≠ 0 := by
    have power_lt : (2 / 3 : ℚ) ^ (offset + 1) < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) gap_positive.ne'
    linarith
  simp only [pow_zero]
  rw [show 7 + offset + 1 = 7 + (offset + 1) by omega]
  have gap_factor :
      (2 / 3 : ℚ) ^ 7 - (2 / 3 : ℚ) ^ (7 + (offset + 1)) =
        (2 / 3 : ℚ) ^ 7 * (1 - (2 / 3 : ℚ) ^ (offset + 1)) := by
    rw [pow_add]
    ring
  rw [gap_factor]
  have reciprocal_power :
      (3 / 2 : ℚ) ^ p = ((2 / 3 : ℚ) ^ p)⁻¹ := by
    rw [← inv_pow]
    congr 2
    norm_num
  rw [reciprocal_power]
  field_simp [base_ne, gap_ne]
  ring

/-- Exact source valuation in the `B=6` fibre. -/
theorem lengthThreeReboundingSource_six_hasValue
    (p offset : ℕ) :
    HasValue 5 (lengthThreeReboundingSource p 0 (6 + offset) 6 1)
      (-(shellSlopeGapFiveDepth (offset + 1) : ℤ)) := by
  rw [lengthThreeReboundingSource_six]
  have constant_unit : IsUnit 5 (17 / 192 : ℚ) := by
    exact div_hasValue
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (17 : ℤ)))
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (192 : ℤ)))
  have inverse_ratio_unit : IsUnit 5 (3 / 2 : ℚ) :=
    div_hasValue
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (3 : ℤ)))
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (2 : ℤ)))
  have power_unit := rebounding_unit_pow inverse_ratio_unit p
  have gap_value := one_sub_shellRatio_pow_hasValue
    (show 0 < offset + 1 by omega)
  have result := div_hasValue (mul_hasValue constant_unit power_unit) gap_value
  convert result using 1
  ring

/-- Source acceptance in the `B=6` fibre is exactly odd total gap depth zero. -/
theorem lengthThreeReboundingSource_six_fiveUnit_iff
    (p offset : ℕ) :
    IsUnit 5 (lengthThreeReboundingSource p 0 (6 + offset) 6 1) ↔
      shellSlopeGapFiveDepth (offset + 1) = 0 := by
  have value := lengthThreeReboundingSource_six_hasValue p offset
  constructor
  · intro source_unit
    have valuation_eq :
        -(shellSlopeGapFiveDepth (offset + 1) : ℤ) = 0 :=
      value.2.symm.trans source_unit.2
    omega
  · intro depth_zero
    refine ⟨value.1, ?_⟩
    rw [value.2, depth_zero]
    norm_num

/-- Exact source valuation in the `B=7` fibre. -/
theorem lengthThreeReboundingSource_seven_hasValue
    (p offset : ℕ) :
    HasValue 5 (lengthThreeReboundingSource p 0 (7 + offset) 7 1)
      (1 - (shellSlopeGapFiveDepth (offset + 1) : ℤ)) := by
  rw [lengthThreeReboundingSource_seven]
  have constant_value : HasValue 5 (115 / 384 : ℚ) 1 := by
    have five_value : HasValue 5 (5 : ℚ) 1 := by
      convert primePower_hasValue (prime := 5) 1 using 1 <;> norm_num
    have twentyThree_unit : IsUnit 5 (23 : ℚ) :=
      intCast_isUnit_of_not_dvd (by norm_num)
    have numerator_value : HasValue 5 (115 : ℚ) 1 := by
      convert mul_hasValue five_value twentyThree_unit using 1 <;> norm_num
    have denominator_unit : IsUnit 5 (384 : ℚ) :=
      intCast_isUnit_of_not_dvd (by norm_num)
    simpa using div_hasValue numerator_value denominator_unit
  have inverse_ratio_unit : IsUnit 5 (3 / 2 : ℚ) :=
    div_hasValue
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (3 : ℤ)))
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (2 : ℤ)))
  have power_unit := rebounding_unit_pow inverse_ratio_unit p
  have gap_value := one_sub_shellRatio_pow_hasValue
    (show 0 < offset + 1 by omega)
  have result := div_hasValue (mul_hasValue constant_value power_unit) gap_value
  convert result using 1
  ring

/-- Source acceptance in the `B=7` fibre is exactly total gap depth one. -/
theorem lengthThreeReboundingSource_seven_fiveUnit_iff
    (p offset : ℕ) :
    IsUnit 5 (lengthThreeReboundingSource p 0 (7 + offset) 7 1) ↔
      shellSlopeGapFiveDepth (offset + 1) = 1 := by
  have value := lengthThreeReboundingSource_seven_hasValue p offset
  constructor
  · intro source_unit
    have valuation_eq :
        1 - (shellSlopeGapFiveDepth (offset + 1) : ℤ) = 0 :=
      value.2.symm.trans source_unit.2
    omega
  · intro depth_one
    refine ⟨value.1, ?_⟩
    rw [value.2, depth_one]
    norm_num

/-- The `B=6` real-trap gauges and total gaps are exactly the five displayed cells. -/
theorem lengthThreeReboundingSource_six_mem_realTrap_iff
    (p offset : ℕ) :
    lengthThreeReboundingSource p 0 (6 + offset) 6 1 ∈ Set.Icc (1 / 5) (1 / 2) ↔
      (p = 0 ∧ offset = 0) ∨
      (p = 1 ∧ offset ≤ 1) ∨
      (p = 2 ∧ 1 ≤ offset ∧ offset ≤ 12) ∨
      (p = 3 ∧ 2 ≤ offset) ∨
      (p = 4 ∧ 5 ≤ offset) := by
  rw [lengthThreeReboundingSource_six]
  have power_positive : 0 < (2 / 3 : ℚ) ^ (offset + 1) := by positivity
  have power_lt_one : (2 / 3 : ℚ) ^ (offset + 1) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have denominator_positive : 0 < 1 - (2 / 3 : ℚ) ^ (offset + 1) := by
    linarith
  constructor
  · intro source_mem
    have p_lt_five : p < 5 := by
      by_contra p_large
      have five_le : 5 ≤ p := by omega
      have gauge_power_lower : (3 / 2 : ℚ) ^ 5 ≤ (3 / 2 : ℚ) ^ p :=
        pow_right_mono₀ (by norm_num) five_le
      have coefficient_large :
          1 / 2 < (17 / 192 : ℚ) * (3 / 2 : ℚ) ^ p := by
        norm_num at gauge_power_lower ⊢
        nlinarith
      have source_gt_coefficient :
          (17 / 192 : ℚ) * (3 / 2 : ℚ) ^ p <
            (17 / 192 : ℚ) * (3 / 2 : ℚ) ^ p /
              (1 - (2 / 3 : ℚ) ^ (offset + 1)) := by
        apply (lt_div_iff₀ denominator_positive).2
        have coefficient_positive :
            0 < (17 / 192 : ℚ) * (3 / 2 : ℚ) ^ p := by positivity
        nlinarith
      exact (not_lt_of_ge source_mem.2) (coefficient_large.trans source_gt_coefficient)
    interval_cases p
    · left
      refine ⟨rfl, ?_⟩
      by_contra offset_ne
      have two_le : 2 ≤ offset + 1 := by omega
      have power_upper :
          (2 / 3 : ℚ) ^ (offset + 1) ≤ (2 / 3 : ℚ) ^ 2 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) two_le
      have source_lower := (le_div_iff₀ denominator_positive).1 source_mem.1
      norm_num at source_lower power_upper
      nlinarith
    · right; left
      refine ⟨rfl, ?_⟩
      by_contra offset_large
      have three_le : 3 ≤ offset + 1 := by omega
      have power_upper :
          (2 / 3 : ℚ) ^ (offset + 1) ≤ (2 / 3 : ℚ) ^ 3 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) three_le
      have source_lower := (le_div_iff₀ denominator_positive).1 source_mem.1
      norm_num at source_lower power_upper
      nlinarith
    · right; right; left
      refine ⟨rfl, ?_, ?_⟩
      · by_contra offset_zero
        have offset_eq : offset = 0 := by omega
        subst offset
        norm_num at source_mem
      · by_contra offset_large
        have fourteen_le : 14 ≤ offset + 1 := by omega
        have power_upper :
            (2 / 3 : ℚ) ^ (offset + 1) ≤ (2 / 3 : ℚ) ^ 14 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) fourteen_le
        have source_lower := (le_div_iff₀ denominator_positive).1 source_mem.1
        norm_num at source_lower power_upper
        nlinarith
    · right; right; right; left
      refine ⟨rfl, ?_⟩
      by_contra offset_small
      have offset_cases : offset = 0 ∨ offset = 1 := by omega
      rcases offset_cases with rfl | rfl <;> norm_num at source_mem
    · right; right; right; right
      refine ⟨rfl, ?_⟩
      by_contra offset_small
      have offset_le : offset ≤ 4 := by omega
      interval_cases offset <;> norm_num at source_mem
  · intro cells
    rcases cells with ⟨rfl, rfl⟩ | ⟨rfl, offset_le⟩ |
        ⟨rfl, offset_lower, offset_upper⟩ | ⟨rfl, offset_lower⟩ |
        ⟨rfl, offset_lower⟩
    · norm_num
    · have offset_cases : offset = 0 ∨ offset = 1 := by omega
      rcases offset_cases with rfl | rfl <;> norm_num
    · interval_cases offset <;> norm_num
    · have power_upper :
          (2 / 3 : ℚ) ^ (offset + 1) ≤ (2 / 3 : ℚ) ^ 3 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      constructor
      · apply (le_div_iff₀ denominator_positive).2
        norm_num
        nlinarith
      · apply (div_le_iff₀ denominator_positive).2
        norm_num at power_upper ⊢
        nlinarith
    · have power_upper :
          (2 / 3 : ℚ) ^ (offset + 1) ≤ (2 / 3 : ℚ) ^ 6 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      constructor
      · apply (le_div_iff₀ denominator_positive).2
        norm_num
        nlinarith
      · apply (div_le_iff₀ denominator_positive).2
        norm_num at power_upper ⊢
        nlinarith

/-- The `B=7` real-trap gauges and total gaps are exactly the two displayed rays. -/
theorem lengthThreeReboundingSource_seven_mem_realTrap_iff
    (p offset : ℕ) :
    lengthThreeReboundingSource p 0 (7 + offset) 7 1 ∈ Set.Icc (1 / 5) (1 / 2) ↔
      (p = 0 ∧ 2 ≤ offset) ∨ (p = 1 ∧ 5 ≤ offset) := by
  rw [lengthThreeReboundingSource_seven]
  have power_positive : 0 < (2 / 3 : ℚ) ^ (offset + 1) := by positivity
  have power_lt_one : (2 / 3 : ℚ) ^ (offset + 1) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have denominator_positive : 0 < 1 - (2 / 3 : ℚ) ^ (offset + 1) := by
    linarith
  constructor
  · intro source_mem
    have p_lt_two : p < 2 := by
      by_contra p_large
      have two_le : 2 ≤ p := by omega
      have gauge_power_lower : (3 / 2 : ℚ) ^ 2 ≤ (3 / 2 : ℚ) ^ p :=
        pow_right_mono₀ (by norm_num) two_le
      have coefficient_large :
          1 / 2 < (115 / 384 : ℚ) * (3 / 2 : ℚ) ^ p := by
        norm_num at gauge_power_lower ⊢
        nlinarith
      have source_gt_coefficient :
          (115 / 384 : ℚ) * (3 / 2 : ℚ) ^ p <
            (115 / 384 : ℚ) * (3 / 2 : ℚ) ^ p /
              (1 - (2 / 3 : ℚ) ^ (offset + 1)) := by
        apply (lt_div_iff₀ denominator_positive).2
        have coefficient_positive :
            0 < (115 / 384 : ℚ) * (3 / 2 : ℚ) ^ p := by positivity
        nlinarith
      exact (not_lt_of_ge source_mem.2) (coefficient_large.trans source_gt_coefficient)
    interval_cases p
    · left
      refine ⟨rfl, ?_⟩
      by_contra offset_small
      have offset_cases : offset = 0 ∨ offset = 1 := by omega
      rcases offset_cases with rfl | rfl <;> norm_num at source_mem
    · right
      refine ⟨rfl, ?_⟩
      by_contra offset_small
      have offset_le : offset ≤ 4 := by omega
      interval_cases offset <;> norm_num at source_mem
  · rintro (⟨rfl, offset_lower⟩ | ⟨rfl, offset_lower⟩)
    · have power_upper :
          (2 / 3 : ℚ) ^ (offset + 1) ≤ (2 / 3 : ℚ) ^ 3 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      constructor
      · apply (le_div_iff₀ denominator_positive).2
        norm_num
        nlinarith
      · apply (div_le_iff₀ denominator_positive).2
        norm_num at power_upper ⊢
        nlinarith
    · have power_upper :
          (2 / 3 : ℚ) ^ (offset + 1) ≤ (2 / 3 : ℚ) ^ 6 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      constructor
      · apply (le_div_iff₀ denominator_positive).2
        norm_num
        nlinarith
      · apply (div_le_iff₀ denominator_positive).2
        norm_num at power_upper ⊢
        nlinarith

/-- Common target in the positive-negative-positive chamber after normalizing the total gap as
`offset+1`. The source is independent of `t`; the target retains it through one ratio power. -/
def lengthThreeReboundingTarget (B offset t : ℕ) : ℚ :=
  (75 * (1 - (2 / 3 : ℚ) ^ (offset + 1)) +
      (2 / 3 : ℚ) ^ t *
        (48 - (45 + 27 * (2 / 3 : ℚ) ^ B) *
          (2 / 3 : ℚ) ^ (offset + 1))) /
    (375 * (1 - (2 / 3 : ℚ) ^ (offset + 1)))

/-- Depth-two carry coordinate of the normalized rebounding target. -/
def lengthThreeReboundingTargetCarry (B offset : ℕ) : ℚ :=
  (16 - (15 + 9 * (2 / 3 : ℚ) ^ B) *
      (2 / 3 : ℚ) ^ (offset + 1)) /
    (1 - (2 / 3 : ℚ) ^ (offset + 1))

private theorem mobiusCarry_sub
    (constant z scale : ℚ) (base_ne : 1 - z ≠ 0)
    (scaled_ne : 1 - z * scale ≠ 0) :
    (16 - constant * (z * scale)) / (1 - z * scale) -
        (16 - constant * z) / (1 - z) =
      z * (constant - 16) * (1 - scale) /
        ((1 - z * scale) * (1 - z)) := by
  field_simp [base_ne, scaled_ne]
  ring

/-- Exact carry displacement under a shift of the total-gap coordinate. -/
theorem lengthThreeReboundingTargetCarry_offset_add_sub
    (B offset shift : ℕ) :
    lengthThreeReboundingTargetCarry B (offset + shift) -
        lengthThreeReboundingTargetCarry B offset =
      ((2 / 3 : ℚ) ^ (offset + 1) *
          (9 * (2 / 3 : ℚ) ^ B - 1) *
          (1 - (2 / 3 : ℚ) ^ shift)) /
        ((1 - (2 / 3 : ℚ) ^ (offset + shift + 1)) *
          (1 - (2 / 3 : ℚ) ^ (offset + 1))) := by
  have base_gap_positive : 0 < offset + 1 := by omega
  have shifted_gap_positive : 0 < offset + shift + 1 := by omega
  have base_gap_ne : 1 - (2 / 3 : ℚ) ^ (offset + 1) ≠ 0 := by
    have power_lt : (2 / 3 : ℚ) ^ (offset + 1) < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) base_gap_positive.ne'
    linarith
  have shifted_gap_ne : 1 - (2 / 3 : ℚ) ^ (offset + shift + 1) ≠ 0 := by
    have power_lt : (2 / 3 : ℚ) ^ (offset + shift + 1) < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) shifted_gap_positive.ne'
    linarith
  have scaled_gap_ne :
      1 - (2 / 3 : ℚ) ^ (offset + 1) * (2 / 3 : ℚ) ^ shift ≠ 0 := by
    rw [← pow_add]
    simpa only [show offset + shift + 1 = offset + 1 + shift by omega] using
      shifted_gap_ne
  have algebra := mobiusCarry_sub
    (15 + 9 * (2 / 3 : ℚ) ^ B)
    ((2 / 3 : ℚ) ^ (offset + 1))
    ((2 / 3 : ℚ) ^ shift) base_gap_ne scaled_gap_ne
  rw [lengthThreeReboundingTargetCarry, lengthThreeReboundingTargetCarry,
    show offset + shift + 1 = offset + 1 + shift by omega, pow_add]
  convert algebra using 1
  · ring

/-- Exact valuation of the carry displacement under a positive total-gap shift. -/
theorem lengthThreeReboundingTargetCarry_offset_add_sub_hasValue
    (B offset : ℕ) {shift : ℕ} (shift_positive : 0 < shift)
    {constantValue : ℤ}
    (constant_value :
      HasValue 5 (9 * (2 / 3 : ℚ) ^ B - 1) constantValue) :
    HasValue 5
      (lengthThreeReboundingTargetCarry B (offset + shift) -
        lengthThreeReboundingTargetCarry B offset)
      (constantValue + shellSlopeGapFiveDepth shift -
        shellSlopeGapFiveDepth (offset + shift + 1) -
        shellSlopeGapFiveDepth (offset + 1)) := by
  have ratio_unit : IsUnit 5 (2 / 3 : ℚ) :=
    div_hasValue
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (2 : ℤ)))
      (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (3 : ℤ)))
  have power_unit := rebounding_unit_pow ratio_unit (offset + 1)
  have shift_value := one_sub_shellRatio_pow_hasValue shift_positive
  have shifted_gap_value := one_sub_shellRatio_pow_hasValue
    (show 0 < offset + shift + 1 by omega)
  have base_gap_value := one_sub_shellRatio_pow_hasValue
    (show 0 < offset + 1 by omega)
  have numerator_value :=
    mul_hasValue (mul_hasValue power_unit constant_value) shift_value
  have denominator_value := mul_hasValue shifted_gap_value base_gap_value
  rw [lengthThreeReboundingTargetCarry_offset_add_sub]
  have result := div_hasValue numerator_value denominator_value
  convert result using 1
  ring

private theorem shellSlopeGapFiveDepth_add_even_eq_zero
    {gap shift : ℕ} (gap_depth : shellSlopeGapFiveDepth gap = 0)
    (shift_even : Even shift) :
    shellSlopeGapFiveDepth (gap + shift) = 0 := by
  have gap_odd : Odd gap := by
    by_contra gap_not_odd
    rw [shellSlopeGapFiveDepth, if_neg gap_not_odd] at gap_depth
    omega
  obtain ⟨gapHalf, gap_eq⟩ := gap_odd
  obtain ⟨shiftHalf, shift_eq⟩ := shift_even
  have shifted_odd : Odd (gap + shift) :=
    ⟨gapHalf + shiftHalf, by omega⟩
  rw [shellSlopeGapFiveDepth, if_pos shifted_odd]

private theorem shellSlopeGapFiveDepth_add_ten_mul_eq_one
    {gap multiplier : ℕ} (gap_positive : 0 < gap)
    (gap_depth : shellSlopeGapFiveDepth gap = 1) :
    shellSlopeGapFiveDepth (gap + 10 * multiplier) = 1 := by
  have gap_not_odd : ¬Odd gap := by
    intro gap_odd
    rw [shellSlopeGapFiveDepth, if_pos gap_odd] at gap_depth
    omega
  obtain ⟨gapHalf, gap_eq⟩ := Nat.not_odd_iff_even.mp gap_not_odd
  have gap_half_eq : gap / 2 = gapHalf := by omega
  have gap_half_value : padicValNat 5 gapHalf = 0 := by
    rw [shellSlopeGapFiveDepth, if_neg gap_not_odd, gap_half_eq] at gap_depth
    omega
  have gap_half_ne : gapHalf ≠ 0 := by omega
  have gap_half_not_dvd : ¬5 ∣ gapHalf := by
    intro gap_half_dvd
    have value_ne :=
      (dvd_iff_padicValNat_ne_zero gap_half_ne).1 gap_half_dvd
    exact value_ne gap_half_value
  have shifted_even : Even (gap + 10 * multiplier) :=
    ⟨gapHalf + 5 * multiplier, by omega⟩
  have shifted_not_odd : ¬Odd (gap + 10 * multiplier) :=
    Nat.not_odd_iff_even.mpr shifted_even
  have shifted_half_eq :
      (gap + 10 * multiplier) / 2 = gapHalf + 5 * multiplier := by
    omega
  have shifted_half_not_dvd : ¬5 ∣ gapHalf + 5 * multiplier := by
    rw [Nat.dvd_iff_mod_eq_zero] at gap_half_not_dvd ⊢
    omega
  rw [shellSlopeGapFiveDepth, if_neg shifted_not_odd, shifted_half_eq,
    padicValNat.eq_zero_of_not_dvd shifted_half_not_dvd]

private theorem rebounding_six_constant_unit :
    IsUnit 5 (9 * (2 / 3 : ℚ) ^ 6 - 1) := by
  have constant_eq : 9 * (2 / 3 : ℚ) ^ 6 - 1 = -17 / 81 := by norm_num
  rw [constant_eq]
  exact div_hasValue
    (neg_hasValue (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (17 : ℤ))))
    (intCast_isUnit_of_not_dvd (by norm_num : ¬5 ∣ (81 : ℤ)))

private theorem rebounding_seven_constant_hasValue :
    HasValue 5 (9 * (2 / 3 : ℚ) ^ 7 - 1) 1 := by
  have constant_eq : 9 * (2 / 3 : ℚ) ^ 7 - 1 = -115 / 243 := by norm_num
  have five_value : HasValue 5 (5 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 5) 1)
  have twentyThree_unit : IsUnit 5 (23 : ℚ) :=
    intCast_isUnit_of_not_dvd (by norm_num)
  have numerator_value : HasValue 5 (-115 : ℚ) 1 := by
    convert neg_hasValue (mul_hasValue five_value twentyThree_unit) using 1 <;> norm_num
  have denominator_unit : IsUnit 5 (243 : ℚ) :=
    intCast_isUnit_of_not_dvd (by norm_num)
  rw [constant_eq]
  exact div_hasValue numerator_value denominator_unit

private theorem shellSlopeGapFiveDepth_fifty : shellSlopeGapFiveDepth 50 = 3 := by
  rw [shellSlopeGapFiveDepth, if_neg (by norm_num : ¬Odd 50)]
  norm_num
  rw [show (25 : ℕ) = 5 ^ 2 by norm_num, padicValNat.prime_pow]

private theorem shellSlopeGapFiveDepth_twoFifty :
    shellSlopeGapFiveDepth 250 = 4 := by
  rw [shellSlopeGapFiveDepth, if_neg (by norm_num : ¬Odd 250)]
  norm_num
  rw [show (125 : ℕ) = 5 ^ 3 by norm_num, padicValNat.prime_pow]

private theorem shellSlopeGapFiveDepth_twelveFifty :
    shellSlopeGapFiveDepth 1250 = 5 := by
  rw [shellSlopeGapFiveDepth, if_neg (by norm_num : ¬Odd 1250)]
  norm_num
  rw [show (625 : ℕ) = 5 ^ 4 by norm_num, padicValNat.prime_pow]

/-- On the `B=6` source-unit fibre, a fifty-step total-gap shift changes the target carry at
exact value three. -/
theorem lengthThreeReboundingTargetCarry_six_offset_add_fifty_sub_hasValue
    (offset : ℕ) (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 0) :
    HasValue 5
      (lengthThreeReboundingTargetCarry 6 (offset + 50) -
        lengthThreeReboundingTargetCarry 6 offset) 3 := by
  have shifted_depth : shellSlopeGapFiveDepth (offset + 50 + 1) = 0 := by
    convert shellSlopeGapFiveDepth_add_even_eq_zero gap_depth
      (show Even 50 by norm_num) using 1
  have difference_value :=
    lengthThreeReboundingTargetCarry_offset_add_sub_hasValue
      6 offset (show 0 < 50 by norm_num) rebounding_six_constant_unit
  rw [shellSlopeGapFiveDepth_fifty, shifted_depth, gap_depth] at difference_value
  norm_num at difference_value ⊢
  exact difference_value

/-- On the `B=6` source-unit fibre, a 250-step total-gap shift changes the target carry at
exact value four. -/
theorem lengthThreeReboundingTargetCarry_six_offset_add_twoFifty_sub_hasValue
    (offset : ℕ) (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 0) :
    HasValue 5
      (lengthThreeReboundingTargetCarry 6 (offset + 250) -
        lengthThreeReboundingTargetCarry 6 offset) 4 := by
  have shifted_depth : shellSlopeGapFiveDepth (offset + 250 + 1) = 0 := by
    convert shellSlopeGapFiveDepth_add_even_eq_zero gap_depth
      (show Even 250 by norm_num) using 1
  have difference_value :=
    lengthThreeReboundingTargetCarry_offset_add_sub_hasValue
      6 offset (show 0 < 250 by norm_num) rebounding_six_constant_unit
  rw [shellSlopeGapFiveDepth_twoFifty, shifted_depth, gap_depth] at difference_value
  norm_num at difference_value ⊢
  exact difference_value

/-- On the `B=7` source-unit fibre, a 250-step total-gap shift changes the target carry at
exact value three. -/
theorem lengthThreeReboundingTargetCarry_seven_offset_add_twoFifty_sub_hasValue
    (offset : ℕ) (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 1) :
    HasValue 5
      (lengthThreeReboundingTargetCarry 7 (offset + 250) -
        lengthThreeReboundingTargetCarry 7 offset) 3 := by
  have shifted_depth : shellSlopeGapFiveDepth (offset + 250 + 1) = 1 := by
    convert shellSlopeGapFiveDepth_add_ten_mul_eq_one
      (show 0 < offset + 1 by omega) gap_depth (multiplier := 25) using 1
  have difference_value :=
    lengthThreeReboundingTargetCarry_offset_add_sub_hasValue
      7 offset (show 0 < 250 by norm_num) rebounding_seven_constant_hasValue
  rw [shellSlopeGapFiveDepth_twoFifty, shifted_depth, gap_depth] at difference_value
  norm_num at difference_value ⊢
  exact difference_value

/-- On the `B=7` source-unit fibre, a 1250-step total-gap shift changes the target carry at
exact value four. -/
theorem lengthThreeReboundingTargetCarry_seven_offset_add_twelveFifty_sub_hasValue
    (offset : ℕ) (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 1) :
    HasValue 5
      (lengthThreeReboundingTargetCarry 7 (offset + 1250) -
        lengthThreeReboundingTargetCarry 7 offset) 4 := by
  have shifted_depth : shellSlopeGapFiveDepth (offset + 1250 + 1) = 1 := by
    convert shellSlopeGapFiveDepth_add_ten_mul_eq_one
      (show 0 < offset + 1 by omega) gap_depth (multiplier := 125) using 1
  have difference_value :=
    lengthThreeReboundingTargetCarry_offset_add_sub_hasValue
      7 offset (show 0 < 1250 by norm_num) rebounding_seven_constant_hasValue
  rw [shellSlopeGapFiveDepth_twelveFifty, shifted_depth, gap_depth] at difference_value
  norm_num at difference_value ⊢
  exact difference_value

/-- Exact depth-two carry is fifty-periodic on the `B=6` source-unit fibre. -/
theorem lengthThreeReboundingTargetCarry_six_add_fifty_hasValue_two_iff
    (offset : ℕ) (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 0) :
    HasValue 5 (lengthThreeReboundingTargetCarry 6 (offset + 50)) 2 ↔
      HasValue 5 (lengthThreeReboundingTargetCarry 6 offset) 2 := by
  exact hasValue_of_sub_higher_iff (by norm_num)
    (lengthThreeReboundingTargetCarry_six_offset_add_fifty_sub_hasValue
      offset gap_depth)

/-- Exact depth-two carry is 250-periodic on the `B=7` source-unit fibre. -/
theorem lengthThreeReboundingTargetCarry_seven_add_twoFifty_hasValue_two_iff
    (offset : ℕ) (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 1) :
    HasValue 5 (lengthThreeReboundingTargetCarry 7 (offset + 250)) 2 ↔
      HasValue 5 (lengthThreeReboundingTargetCarry 7 offset) 2 := by
  exact hasValue_of_sub_higher_iff (by norm_num)
    (lengthThreeReboundingTargetCarry_seven_offset_add_twoFifty_sub_hasValue
      offset gap_depth)

/-- The rebounding target is the universal terminal coordinate at wait `t`. -/
theorem lengthThreeReboundingTarget_eq_terminalCarryTarget
    (B offset t : ℕ) :
    lengthThreeReboundingTarget B offset t =
      terminalCarryTarget t (lengthThreeReboundingTargetCarry B offset) := by
  have gap_positive : 0 < offset + 1 := by omega
  have gap_ne : 1 - (2 / 3 : ℚ) ^ (offset + 1) ≠ 0 := by
    have power_lt : (2 / 3 : ℚ) ^ (offset + 1) < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) gap_positive.ne'
    linarith
  rw [lengthThreeReboundingTarget, terminalCarryTarget,
    lengthThreeReboundingTargetCarry]
  field_simp [gap_ne]
  ring

/-- A guarded rebounding target forces its incoming carry to exact depth two. -/
theorem lengthThreeReboundingTarget_fiveUnit_forces_carry
    (B offset t : ℕ)
    (target_unit : IsUnit 5 (lengthThreeReboundingTarget B offset t)) :
    HasValue 5 (lengthThreeReboundingTargetCarry B offset) 2 := by
  rw [lengthThreeReboundingTarget_eq_terminalCarryTarget] at target_unit
  exact terminalCarryTarget_fiveUnit_forces_carry t target_unit

/-- Ten terminal residues classify a rebounding target on its forced carry fibre. -/
theorem lengthThreeReboundingTarget_fiveUnit_iff_mod_ten
    (B offset t : ℕ)
    (carry_value : HasValue 5 (lengthThreeReboundingTargetCarry B offset) 2) :
    IsUnit 5 (lengthThreeReboundingTarget B offset t) ↔
      IsUnit 5 (lengthThreeReboundingTarget B offset (t % 10)) := by
  rw [lengthThreeReboundingTarget_eq_terminalCarryTarget,
    lengthThreeReboundingTarget_eq_terminalCarryTarget]
  exact terminalCarryTarget_fiveUnit_iff_mod_ten t carry_value

/-- Every positive odd terminal shift from an accepted rebounding target is rejected at
value minus one. -/
theorem lengthThreeReboundingTarget_oddShift_hasValue_negOne
    (B offset t : ℕ) {shift : ℕ} (shift_positive : 0 < shift)
    (shift_odd : Odd shift)
    (target_unit : IsUnit 5 (lengthThreeReboundingTarget B offset t)) :
    HasValue 5 (lengthThreeReboundingTarget B offset (t + shift)) (-1) := by
  rw [lengthThreeReboundingTarget_eq_terminalCarryTarget] at target_unit ⊢
  exact terminalCarryTarget_oddShift_hasValue_negOne
    t shift_positive shift_odd target_unit

/-- Target acceptance is 250-periodic in the `B=6` total-gap coordinate on its source-unit
fibre. -/
theorem lengthThreeReboundingTarget_six_offset_add_twoFifty_fiveUnit_iff
    (offset t : ℕ) (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 0) :
    IsUnit 5 (lengthThreeReboundingTarget 6 (offset + 250) t) ↔
      IsUnit 5 (lengthThreeReboundingTarget 6 offset t) := by
  rw [lengthThreeReboundingTarget_eq_terminalCarryTarget,
    lengthThreeReboundingTarget_eq_terminalCarryTarget]
  exact terminalCarryTarget_carry_sub_fiveUnit_iff t (by norm_num)
    (lengthThreeReboundingTargetCarry_six_offset_add_twoFifty_sub_hasValue
      offset gap_depth)

/-- Target acceptance is 1250-periodic in the `B=7` total-gap coordinate on its source-unit
fibre. -/
theorem lengthThreeReboundingTarget_seven_offset_add_twelveFifty_fiveUnit_iff
    (offset t : ℕ) (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 1) :
    IsUnit 5 (lengthThreeReboundingTarget 7 (offset + 1250) t) ↔
      IsUnit 5 (lengthThreeReboundingTarget 7 offset t) := by
  rw [lengthThreeReboundingTarget_eq_terminalCarryTarget,
    lengthThreeReboundingTarget_eq_terminalCarryTarget]
  exact terminalCarryTarget_carry_sub_fiveUnit_iff t (by norm_num)
    (lengthThreeReboundingTargetCarry_seven_offset_add_twelveFifty_sub_hasValue
      offset gap_depth)

/-- The right schedule reaches the exact normalized target; notably both head gauges cancel. -/
theorem lengthThreeReboundingRight_commonTarget
    (p B offset t : ℕ) :
    shellRun (lengthThreeReboundingRight p 0 t B)
        (lengthThreeReboundingSource p 0 (B + offset) B 1) =
      lengthThreeReboundingTarget B offset t := by
  have base_ne : (2 / 3 : ℚ) ≠ 0 := by norm_num
  have gap_positive : 0 < offset + 1 := by omega
  have gap_ne : 1 - (2 / 3 : ℚ) ^ (offset + 1) ≠ 0 := by
    have power_lt : (2 / 3 : ℚ) ^ (offset + 1) < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) gap_positive.ne'
    linarith
  have gap_factor :
      (2 / 3 : ℚ) ^ B - (2 / 3 : ℚ) ^ (B + (offset + 1)) =
        (2 / 3 : ℚ) ^ B * (1 - (2 / 3 : ℚ) ^ (offset + 1)) := by
    rw [pow_add]
    ring
  have offset_power_le_one : (2 / 3 : ℚ) ^ offset ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have scaled_gap_ne : 3 - (2 / 3 : ℚ) ^ offset * 2 ≠ 0 := by
    have : 0 < 3 - (2 / 3 : ℚ) ^ offset * 2 := by nlinarith
    exact ne_of_gt this
  have nine_scaled_gap_ne : 27 - (2 / 3 : ℚ) ^ offset * 18 ≠ 0 := by
    intro equality
    apply scaled_gap_ne
    nlinarith
  have oneTwentyFive_scaled_gap_ne :
      375 - (2 / 3 : ℚ) ^ offset * 250 ≠ 0 := by
    intro equality
    apply scaled_gap_ne
    nlinarith
  rw [lengthThreeReboundingRight, shellRun_cons, shellRun_cons,
    shellRun_singleton, lengthThreeReboundingSource,
    show B + offset + 1 = B + (offset + 1) by omega, gap_factor,
    lengthThreeReboundingTarget]
  simp only [shellStep, pow_zero, mul_one, pow_add]
  ring_nf
  field_simp [base_ne, gap_ne, scaled_gap_ne, nine_scaled_gap_ne,
    oneTwentyFive_scaled_gap_ne]
  ring

/-- Both schedules reach the exact normalized target. -/
theorem lengthThreeRebounding_commonTarget
    (p B offset t : ℕ) :
    shellRun (lengthThreeReboundingLeft p 0 t (B + offset) 1)
          (lengthThreeReboundingSource p 0 (B + offset) B 1) =
        lengthThreeReboundingTarget B offset t ∧
      shellRun (lengthThreeReboundingRight p 0 t B)
          (lengthThreeReboundingSource p 0 (B + offset) B 1) =
        lengthThreeReboundingTarget B offset t := by
  have total_positive : B < B + offset + 1 := by omega
  have collision := lengthThreeRebounding_collisionSource
    p 0 t (B + offset) B 1 total_positive
  have slope_ne :
      shellSlope (lengthThreeReboundingLeft p 0 t (B + offset) 1) ≠
        shellSlope (lengthThreeReboundingRight p 0 t B) := by
    intro slope_eq
    have sums_eq :=
      (shellSlope_eq_iff_length_sum
        (lengthThreeReboundingLeft p 0 t (B + offset) 1)
        (lengthThreeReboundingRight p 0 t B)).1 slope_eq
    simp only [lengthThreeReboundingLeft, lengthThreeReboundingRight,
      List.sum_cons, List.sum_nil, Nat.add_zero] at sums_eq
    omega
  have endpoint_collision := shellRun_collisionSource
    (lengthThreeReboundingLeft p 0 t (B + offset) 1)
    (lengthThreeReboundingRight p 0 t B) slope_ne
  rw [collision] at endpoint_collision
  have right_target := lengthThreeReboundingRight_commonTarget p B offset t
  exact ⟨endpoint_collision.trans right_target, right_target⟩

/-- A guarded rebounding target forces its collision source to be a five-unit. -/
theorem lengthThreeReboundingTarget_fiveUnit_forces_source_fiveUnit
    (p B offset t : ℕ)
    (target_unit : IsUnit 5 (lengthThreeReboundingTarget B offset t)) :
    IsUnit 5 (lengthThreeReboundingSource p 0 (B + offset) B 1) := by
  have right_target := (lengthThreeRebounding_commonTarget p B offset t).2
  have output_unit :
      IsUnit 5
        (shellRun (lengthThreeReboundingRight p 0 t B)
          (lengthThreeReboundingSource p 0 (B + offset) B 1)) := by
    rw [right_target]
    exact target_unit
  have prefixes :=
    (shellPrefixesUnit_iff (lengthThreeReboundingRight p 0 t B)
      (lengthThreeReboundingSource p 0 (B + offset) B 1)).2 output_unit
  exact prefixes [] (lengthThreeReboundingRight p 0 t B) (by simp)

/-- Pure arithmetic partition of a strict length-three suffix crossing after orienting the total
gap positively. The first chamber includes a zero middle coordinate gap. -/
theorem lengthThree_strictCrossing_chambers
    (a b c d e f : ℕ) (total_positive : d + e + f < a + b + c)
    (first_ne : a ≠ d) (last_ne : c ≠ f)
    (proper_suffix_cross : c < f ∨ b + c < e + f) :
    (∃ A B k, 0 < A ∧ 0 < k ∧
      a = d + A ∧ b = e + B ∧ f = c + k ∧ k < A + B) ∨
    (∃ A B k, 0 < A ∧ 0 < B ∧ 0 < k ∧
      a = d + A ∧ e = b + B ∧ f = c + k ∧ B + k < A) ∨
    (∃ A B k, 0 < A ∧ 0 < B ∧ 0 < k ∧
      a = d + A ∧ e = b + B ∧ c = f + k ∧ k < B ∧ B < A + k) ∨
    ∃ A B k, 0 < A ∧ 0 < B ∧ 0 < k ∧
      d = a + A ∧ b = e + B ∧ f = c + k ∧ A + k < B := by
  rcases lt_or_gt_of_ne first_ne with a_lt | a_gt
  · rcases lt_trichotomy b e with b_lt | b_eq | b_gt
    · rcases lt_or_gt_of_ne last_ne with c_lt | c_gt <;> omega
    · subst e
      rcases lt_or_gt_of_ne last_ne with c_lt | c_gt <;> omega
    · rcases lt_or_gt_of_ne last_ne with c_lt | c_gt
      · right; right; right
        refine ⟨d - a, b - e, f - c, by omega, by omega, by omega,
          by omega, by omega, by omega, by omega⟩
      · omega
  · rcases lt_trichotomy b e with b_lt | b_eq | b_gt
    · rcases lt_or_gt_of_ne last_ne with c_lt | c_gt
      · right; left
        refine ⟨a - d, e - b, f - c, by omega, by omega, by omega,
          by omega, by omega, by omega, by omega⟩
      · right; right; left
        refine ⟨a - d, e - b, c - f, by omega, by omega, by omega,
          by omega, by omega, by omega, by omega, by omega⟩
    · subst e
      rcases lt_or_gt_of_ne last_ne with c_lt | c_gt
      · left
        refine ⟨a - d, 0, f - c, by omega, by omega,
          by omega, by omega, by omega, by omega⟩
      · omega
    · rcases lt_or_gt_of_ne last_ne with c_lt | c_gt
      · left
        refine ⟨a - d, b - e, f - c, by omega, by omega,
          by omega, by omega, by omega, by omega⟩
      · omega

/-- Every positive-source, cross-grade, strict-end length-three collision enters exactly one of
the four coordinate-sign chambers after orienting the larger total wait to the left. -/
theorem lengthThree_positiveCollision_chambers
    (a b c d e f : ℕ) (total_positive : d + e + f < a + b + c)
    (first_ne : a ≠ d) (last_ne : c ≠ f)
    (source_positive : 0 < collisionSource [a, b, c] [d, e, f]) :
    (∃ A B k, 0 < A ∧ 0 < k ∧
      a = d + A ∧ b = e + B ∧ f = c + k ∧ k < A + B) ∨
    (∃ A B k, 0 < A ∧ 0 < B ∧ 0 < k ∧
      a = d + A ∧ e = b + B ∧ f = c + k ∧ B + k < A) ∨
    (∃ A B k, 0 < A ∧ 0 < B ∧ 0 < k ∧
      a = d + A ∧ e = b + B ∧ c = f + k ∧ k < B ∧ B < A + k) ∨
    ∃ A B k, 0 < A ∧ 0 < B ∧ 0 < k ∧
      d = a + A ∧ b = e + B ∧ f = c + k ∧ A + k < B := by
  have sum_ne : [a, b, c].sum ≠ [d, e, f].sum := by
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  have distinct : [a, b, c] ≠ [d, e, f] := by
    intro schedules_eq
    exact sum_ne (congrArg List.sum schedules_eq)
  have slope_ne : shellSlope [a, b, c] ≠ shellSlope [d, e, f] := by
    intro slope_eq
    exact sum_ne ((shellSlope_eq_iff_length_sum [a, b, c] [d, e, f]).1 slope_eq).2
  have collision := shellRun_collisionSource [a, b, c] [d, e, f] slope_ne
  have crossings := sameLength_positiveSource_collision_suffixSums_cross
    (show [a, b, c].length = [d, e, f].length by rfl)
    distinct source_positive collision
  obtain ⟨cut, proper_gap⟩ := crossings.2
  have proper_suffix_cross : c < f ∨ b + c < e + f := by
    cases cut with
    | zero =>
        simp only [List.drop_zero, List.sum_cons, List.sum_nil, Nat.add_zero] at proper_gap
        omega
    | succ cut =>
        cases cut with
        | zero =>
            right
            simpa only [List.drop_succ_cons, List.drop_zero, List.sum_cons,
              List.sum_nil, Nat.add_zero] using proper_gap
        | succ cut =>
            cases cut with
            | zero =>
                left
                simpa only [List.drop_succ_cons, List.drop_zero, List.sum_cons,
                  List.sum_nil, Nat.add_zero] using proper_gap
            | succ cut =>
                simp only [List.drop_succ_cons] at proper_gap
                exact (lt_irrefl _ proper_gap).elim
  exact lengthThree_strictCrossing_chambers
    a b c d e f total_positive first_ne last_ne proper_suffix_cross

end MatrixMortality.MixedPrimeDebt
