import MatrixMortality.MixedPrimeRealTrapLengthTwo

/-!
# Falling-tail length-three crossings

This module opens the first genuine three-term carry chamber left by the complete length-two
classifier. Write the schedules as

```text
[p + A, q + B, t]   and   [p, q, t + k],
```

with `k < A + B`. This is the closed `(+,+,−)` chamber: `A`, `B`, and `k` may lie on
coordinate walls, while the strict chamber adds their positivity. The collision source has an
exact rational expression independent of the final gauge `t`. Membership in the real trap
`[1/5, 1/2]` then excludes `k = 0` and forces `k ≤ 2`, uniformly in the four remaining
parameters. Thus precisely `k = 1` and `k = 2` survive.

The result isolates the next arithmetic seam. It leaves the `k = 1` and `k = 2` five-adic
carry trees open, and makes no claim about the other length-three sign chambers.
-/

namespace MatrixMortality.MixedPrimeDebt

open PeriodicShell

/-- Left schedule in the closed positive-positive-negative length-three chamber. -/
def lengthThreeFallingLeft (p q t A B : ℕ) : List ℕ :=
  [p + A, q + B, t]

/-- Right schedule in the closed positive-positive-negative length-three chamber. -/
def lengthThreeFallingRight (p q t k : ℕ) : List ℕ :=
  [p, q, t + k]

/-- Exact collision source in the closed positive-positive-negative length-three chamber. -/
def lengthThreeFallingSource (p q A B k : ℕ) : ℚ :=
  (9 * (2 / 3 : ℚ) ^ q * ((2 / 3 : ℚ) ^ B - (2 / 3 : ℚ) ^ k) +
      15 * (1 - (2 / 3 : ℚ) ^ k)) /
    (27 * (2 / 3 : ℚ) ^ (p + q) *
      ((2 / 3 : ℚ) ^ k - (2 / 3 : ℚ) ^ (A + B)))

private theorem shellOffset_nil : shellOffset [] = 0 := by
  have run_nil : shellRun [] (0 : ℚ) = 0 := rfl
  rw [shellOffset, shellIntercept, run_nil]
  norm_num

private theorem shellOffset_triple (a b c : ℕ) :
    shellOffset [a, b, c] =
      9 * (2 / 3 : ℚ) ^ (b + c) + 15 * (2 / 3 : ℚ) ^ c + 25 := by
  rw [shellOffset_cons, shellOffset_cons, shellOffset_cons, shellOffset_nil]
  simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, pow_succ, pow_zero]
  ring

theorem lengthThreeFalling_collisionSource
    (p q t A B : ℕ) {k : ℕ} (total_positive : k < A + B) :
    collisionSource (lengthThreeFallingLeft p q t A B)
        (lengthThreeFallingRight p q t k) =
      lengthThreeFallingSource p q A B k := by
  have length_eq :
      (lengthThreeFallingLeft p q t A B).length =
        (lengthThreeFallingRight p q t k).length := by
    rfl
  have sum_ne :
      (lengthThreeFallingLeft p q t A B).sum ≠
        (lengthThreeFallingRight p q t k).sum := by
    simp only [lengthThreeFallingLeft, lengthThreeFallingRight, List.sum_cons,
      List.sum_nil, Nat.add_zero]
    omega
  have base_ne : (2 / 3 : ℚ) ≠ 0 := by norm_num
  have gap_positive :
      (2 / 3 : ℚ) ^ (A + B) < (2 / 3 : ℚ) ^ k :=
    pow_right_strictAnti₀ (by norm_num) (by norm_num) total_positive
  have gap_ne : (2 / 3 : ℚ) ^ k - (2 / 3 : ℚ) ^ (A + B) ≠ 0 := by
    linarith
  have offset_difference :
      shellOffset (lengthThreeFallingLeft p q t A B) -
          shellOffset (lengthThreeFallingRight p q t k) =
        (2 / 3 : ℚ) ^ t *
          (9 * (2 / 3 : ℚ) ^ q *
              ((2 / 3 : ℚ) ^ B - (2 / 3 : ℚ) ^ k) +
            15 * (1 - (2 / 3 : ℚ) ^ k)) := by
    rw [lengthThreeFallingLeft, lengthThreeFallingRight,
      shellOffset_triple, shellOffset_triple]
    simp only [pow_add]
    ring
  have gain_difference :
      shellGain (lengthThreeFallingRight p q t k) -
          shellGain (lengthThreeFallingLeft p q t A B) =
        27 * (2 / 3 : ℚ) ^ (p + q + t) *
          ((2 / 3 : ℚ) ^ k - (2 / 3 : ℚ) ^ (A + B)) := by
    simp only [lengthThreeFallingLeft, lengthThreeFallingRight, shellGain,
      List.length_cons, List.length_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, pow_add]
    ring
  rw [collisionSource_eq_clearedBalance length_eq sum_ne,
    offset_difference, gain_difference, lengthThreeFallingSource,
    show p + q + t = (p + q) + t by omega, pow_add]
  field_simp [base_ne, gap_ne]

/-- The real trap cuts the falling-tail transfer to one or two. -/
theorem lengthThreeFallingSource_realTrap_forces_k_le_two
    (p q A B : ℕ) {k : ℕ} (total_positive : k < A + B)
    (source_mem : lengthThreeFallingSource p q A B k ∈ Set.Icc (1 / 5) (1 / 2)) :
    k ≤ 2 := by
  by_contra k_large
  have three_le : 3 ≤ k := by omega
  have k_power_positive : 0 < (2 / 3 : ℚ) ^ k := by positivity
  have k_power_upper : (2 / 3 : ℚ) ^ k ≤ 8 / 27 := by
    have power_order := pow_le_pow_of_le_one
      (show 0 ≤ (2 / 3 : ℚ) by norm_num) (show (2 / 3 : ℚ) ≤ 1 by norm_num) three_le
    norm_num at power_order ⊢
    exact power_order
  have q_power_nonnegative : 0 ≤ (2 / 3 : ℚ) ^ q := by positivity
  have q_power_le_one : (2 / 3 : ℚ) ^ q ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have B_power_nonnegative : 0 ≤ (2 / 3 : ℚ) ^ B := by positivity
  have baseline_power_positive : 0 < (2 / 3 : ℚ) ^ (p + q) := by positivity
  have total_power_lt :
      (2 / 3 : ℚ) ^ (A + B) < (2 / 3 : ℚ) ^ k :=
    pow_right_strictAnti₀ (by norm_num) (by norm_num) total_positive
  have denominator_positive :
      0 < 27 * (2 / 3 : ℚ) ^ (p + q) *
        ((2 / 3 : ℚ) ^ k - (2 / 3 : ℚ) ^ (A + B)) := by
    positivity
  have numerator_lower :
      71 / 9 ≤
        9 * (2 / 3 : ℚ) ^ q *
            ((2 / 3 : ℚ) ^ B - (2 / 3 : ℚ) ^ k) +
          15 * (1 - (2 / 3 : ℚ) ^ k) := by
    have negative_product_bound :
        -(9 * (2 / 3 : ℚ) ^ q * (2 / 3 : ℚ) ^ k) ≥
          -(9 * (2 / 3 : ℚ) ^ k) := by
      nlinarith
    nlinarith
  have denominator_upper :
      27 * (2 / 3 : ℚ) ^ (p + q) *
          ((2 / 3 : ℚ) ^ k - (2 / 3 : ℚ) ^ (A + B)) < 8 := by
    have baseline_le_one : (2 / 3 : ℚ) ^ (p + q) ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have difference_lt :
        (2 / 3 : ℚ) ^ k - (2 / 3 : ℚ) ^ (A + B) <
          (2 / 3 : ℚ) ^ k := by
      have total_power_positive : 0 < (2 / 3 : ℚ) ^ (A + B) := by positivity
      linarith
    nlinarith
  have source_gt_half : 1 / 2 < lengthThreeFallingSource p q A B k := by
    rw [lengthThreeFallingSource]
    apply (lt_div_iff₀ denominator_positive).2
    nlinarith
  exact (not_lt_of_ge source_mem.2) source_gt_half

/-- A real-trap source excludes the zero-transfer wall. -/
theorem lengthThreeFallingSource_realTrap_forces_k_pos
    (p q A B : ℕ) {k : ℕ} (total_positive : k < A + B)
    (source_mem : lengthThreeFallingSource p q A B k ∈ Set.Icc (1 / 5) (1 / 2)) :
    0 < k := by
  by_contra k_not_positive
  have k_zero : k = 0 := by omega
  subst k
  have total_power_lt : (2 / 3 : ℚ) ^ (A + B) < 1 := by
    have power_lt :
        (2 / 3 : ℚ) ^ (A + B) < (2 / 3 : ℚ) ^ 0 :=
      pow_right_strictAnti₀ (by norm_num) (by norm_num) total_positive
    simpa using power_lt
  have denominator_positive :
      0 < 27 * (2 / 3 : ℚ) ^ (p + q) *
        (1 - (2 / 3 : ℚ) ^ (A + B)) := by
    positivity
  have B_power_le_one : (2 / 3 : ℚ) ^ B ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have numerator_nonpositive :
      9 * (2 / 3 : ℚ) ^ q * ((2 / 3 : ℚ) ^ B - 1) ≤ 0 := by
    have q_power_nonnegative : 0 ≤ (2 / 3 : ℚ) ^ q := by positivity
    nlinarith
  have source_nonpositive : lengthThreeFallingSource p q A B 0 ≤ 0 := by
    rw [lengthThreeFallingSource, pow_zero]
    norm_num only [sub_self, mul_zero, add_zero]
    exact div_nonpos_of_nonpos_of_nonneg numerator_nonpositive
      (le_of_lt denominator_positive)
  linarith [source_mem.1]

/-- The strict falling-tail chamber leaves exactly transfers one and two. -/
theorem lengthThreeFallingSource_realTrap_forces_k_eq_one_or_two
    (p q A B : ℕ) {k : ℕ} (total_positive : k < A + B)
    (source_mem : lengthThreeFallingSource p q A B k ∈ Set.Icc (1 / 5) (1 / 2)) :
    k = 1 ∨ k = 2 := by
  have k_pos := lengthThreeFallingSource_realTrap_forces_k_pos
    p q A B total_positive source_mem
  have k_le_two := lengthThreeFallingSource_realTrap_forces_k_le_two
    p q A B total_positive source_mem
  omega

/-- Every real-trap collision in the falling-tail chamber has transfer at most two. -/
theorem lengthThreeFalling_collision_realTrap_forces_k_le_two
    (p q t A B : ℕ) {k : ℕ} (total_positive : k < A + B)
    (source_mem :
      collisionSource (lengthThreeFallingLeft p q t A B)
        (lengthThreeFallingRight p q t k) ∈ Set.Icc (1 / 5) (1 / 2)) :
    k ≤ 2 := by
  rw [lengthThreeFalling_collisionSource p q t A B total_positive] at source_mem
  exact lengthThreeFallingSource_realTrap_forces_k_le_two
    p q A B total_positive source_mem

/-- Every real-trap collision in the falling-tail chamber has transfer one or two. -/
theorem lengthThreeFalling_collision_realTrap_forces_k_eq_one_or_two
    (p q t A B : ℕ) {k : ℕ} (total_positive : k < A + B)
    (source_mem :
      collisionSource (lengthThreeFallingLeft p q t A B)
        (lengthThreeFallingRight p q t k) ∈ Set.Icc (1 / 5) (1 / 2)) :
    k = 1 ∨ k = 2 := by
  rw [lengthThreeFalling_collisionSource p q t A B total_positive] at source_mem
  exact lengthThreeFallingSource_realTrap_forces_k_eq_one_or_two
    p q A B total_positive source_mem

end MatrixMortality.MixedPrimeDebt
