import MatrixMortality.MixedPrimeRealTrapLengthTwo
import MatrixMortality.MixedPrimeTerminalCarry

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

open PadicValuation
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

private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The nonzero total-grade gain gap, with all five-adic depth retained. -/
def lengthThreeFallingGainGap (A B k : ℕ) : ℚ :=
  (2 / 3 : ℚ) ^ k - (2 / 3 : ℚ) ^ (A + B)

/-- Collision-source unit after stripping its slope unit and total-grade gain gap. -/
def lengthThreeFallingSourceCarry (q A B k : ℕ) : ℚ :=
  (9 * (2 / 3 : ℚ) ^ q *
      ((2 / 3 : ℚ) ^ B - (2 / 3 : ℚ) ^ k) +
    15 * (1 - (2 / 3 : ℚ) ^ k)) /
      lengthThreeFallingGainGap A B k

/-- The unique intermediate carry whose depth two is forced by target acceptance. -/
def lengthThreeFallingTargetCarry (q A B k : ℕ) : ℚ :=
  lengthThreeFallingSourceCarry q A B k +
    9 * (2 / 3 : ℚ) ^ q + 15

/-- Common target in source-carry coordinates. -/
def lengthThreeFallingTarget (q t A B k : ℕ) : ℚ :=
  (25 + (2 / 3 : ℚ) ^ (t + k) *
      lengthThreeFallingTargetCarry q A B k) / 125

private theorem lengthThreeFallingGainGap_ne
    (A B : ℕ) {k : ℕ} (total_positive : k < A + B) :
    lengthThreeFallingGainGap A B k ≠ 0 := by
  rw [lengthThreeFallingGainGap]
  have gap_positive :
      (2 / 3 : ℚ) ^ (A + B) < (2 / 3 : ℚ) ^ k :=
    pow_right_strictAnti₀ (by norm_num) (by norm_num) total_positive
  linarith

private theorem lengthThree_unit_pow
    {value : ℚ} (value_unit : IsUnit 5 value) (exponent : ℕ) :
    IsUnit 5 (value ^ exponent) := by
  refine ⟨pow_ne_zero exponent value_unit.1, ?_⟩
  rw [padicValRat.pow, value_unit.2]
  simp

private theorem shellRatio_power_unit (exponent : ℕ) :
    IsUnit 5 ((2 / 3 : ℚ) ^ exponent) := by
  have two_unit : IsUnit 5 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have three_unit : IsUnit 5 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  exact lengthThree_unit_pow (div_hasValue two_unit three_unit) exponent

theorem lengthThreeFallingSource_eq_sourceCarry
    (p q A B : ℕ) {k : ℕ} (total_positive : k < A + B) :
    lengthThreeFallingSource p q A B k =
      lengthThreeFallingSourceCarry q A B k /
        (27 * (2 / 3 : ℚ) ^ (p + q)) := by
  have gap_ne := lengthThreeFallingGainGap_ne A B total_positive
  rw [lengthThreeFallingSource, lengthThreeFallingSourceCarry,
    lengthThreeFallingGainGap]
  field_simp [gap_ne]

theorem lengthThreeFallingSource_fiveUnit_iff_sourceCarry
    (p q A B : ℕ) {k : ℕ} (total_positive : k < A + B) :
    IsUnit 5 (lengthThreeFallingSource p q A B k) ↔
      IsUnit 5 (lengthThreeFallingSourceCarry q A B k) := by
  have twentySeven_unit : IsUnit 5 (27 : ℚ) :=
    intCast_isUnit_of_not_dvd (by norm_num)
  have denominator_unit :
      IsUnit 5 (27 * (2 / 3 : ℚ) ^ (p + q)) :=
    mul_hasValue twentySeven_unit (shellRatio_power_unit (p + q))
  rw [lengthThreeFallingSource_eq_sourceCarry p q A B total_positive]
  constructor
  · intro quotient_unit
    have product_unit := mul_hasValue quotient_unit denominator_unit
    have product_eq :
        lengthThreeFallingSourceCarry q A B k /
              (27 * (2 / 3 : ℚ) ^ (p + q)) *
            (27 * (2 / 3 : ℚ) ^ (p + q)) =
          lengthThreeFallingSourceCarry q A B k :=
      div_mul_cancel₀ _ denominator_unit.1
    rwa [product_eq] at product_unit
  · intro sourceCarry_unit
    exact div_hasValue sourceCarry_unit denominator_unit

theorem lengthThreeFalling_commonTarget
    (p q t A B : ℕ) {k : ℕ} (total_positive : k < A + B) :
    shellRun (lengthThreeFallingLeft p q t A B)
        (lengthThreeFallingSource p q A B k) =
        lengthThreeFallingTarget q t A B k ∧
      shellRun (lengthThreeFallingRight p q t k)
        (lengthThreeFallingSource p q A B k) =
        lengthThreeFallingTarget q t A B k := by
  have source_eq := lengthThreeFalling_collisionSource p q t A B total_positive
  have sum_ne :
      (lengthThreeFallingLeft p q t A B).sum ≠
        (lengthThreeFallingRight p q t k).sum := by
    simp only [lengthThreeFallingLeft, lengthThreeFallingRight, List.sum_cons,
      List.sum_nil, Nat.add_zero]
    omega
  have slope_ne :
      shellSlope (lengthThreeFallingLeft p q t A B) ≠
        shellSlope (lengthThreeFallingRight p q t k) := by
    intro slope_eq
    exact sum_ne
      ((shellSlope_eq_iff_length_sum
        (lengthThreeFallingLeft p q t A B)
        (lengthThreeFallingRight p q t k)).1 slope_eq).2
  have collision := shellRun_collisionSource
    (lengthThreeFallingLeft p q t A B)
    (lengthThreeFallingRight p q t k) slope_ne
  rw [source_eq] at collision
  have right_target :
      shellRun (lengthThreeFallingRight p q t k)
          (lengthThreeFallingSource p q A B k) =
        lengthThreeFallingTarget q t A B k := by
    rw [lengthThreeFallingRight, shellRun_cons, shellRun_cons, shellRun_singleton,
      lengthThreeFallingSource_eq_sourceCarry p q A B total_positive]
    simp only [shellStep, lengthThreeFallingTarget,
      lengthThreeFallingTargetCarry]
    have power_ne : (2 / 3 : ℚ) ^ (p + q) ≠ 0 := by positivity
    have q_power_ne : (2 / 3 : ℚ) ^ q ≠ 0 := by positivity
    field_simp [power_ne, q_power_ne]
    rw [show p + q = p + q by rfl, pow_add]
    ring
  exact ⟨collision.trans right_target, right_target⟩

/-- The falling-tail target is the universal coordinate at wait `t+k`. -/
theorem lengthThreeFallingTarget_eq_terminalCarryTarget
    (q t A B k : ℕ) :
    lengthThreeFallingTarget q t A B k =
      terminalCarryTarget (t + k) (lengthThreeFallingTargetCarry q A B k) := by
  rfl

/-- A guarded common target already forces the collision source to be a five-unit. -/
theorem lengthThreeFallingTarget_fiveUnit_forces_source_fiveUnit
    (p q t A B : ℕ) {k : ℕ} (total_positive : k < A + B)
    (target_unit : IsUnit 5 (lengthThreeFallingTarget q t A B k)) :
    IsUnit 5 (lengthThreeFallingSource p q A B k) := by
  have right_target :=
    (lengthThreeFalling_commonTarget p q t A B total_positive).2
  have output_unit :
      IsUnit 5
        (shellRun (lengthThreeFallingRight p q t k)
          (lengthThreeFallingSource p q A B k)) := by
    rw [right_target]
    exact target_unit
  have prefixes :=
    (shellPrefixesUnit_iff (lengthThreeFallingRight p q t k)
      (lengthThreeFallingSource p q A B k)).2 output_unit
  exact prefixes [] (lengthThreeFallingRight p q t k) (by simp)
private theorem lengthThreeFalling_two_realTrap_forces_q_zero
    (p q A B : ℕ) (total_positive : 2 < A + B)
    (source_mem :
      lengthThreeFallingSource p q A B 2 ∈ Set.Icc (1 / 5) (1 / 2)) :
    q = 0 := by
  by_contra q_ne
  have q_positive : 0 < q := Nat.pos_of_ne_zero q_ne
  have q_power_upper : (2 / 3 : ℚ) ^ q ≤ 2 / 3 := by
    have order := pow_le_pow_of_le_one
      (show 0 ≤ (2 / 3 : ℚ) by norm_num)
      (show (2 / 3 : ℚ) ≤ 1 by norm_num) q_positive
    norm_num at order ⊢
    exact order
  have baseline_power_upper :
      (2 / 3 : ℚ) ^ (p + q) ≤ (2 / 3 : ℚ) ^ q := by
    exact pow_le_pow_of_le_one
      (show 0 ≤ (2 / 3 : ℚ) by norm_num)
      (show (2 / 3 : ℚ) ≤ 1 by norm_num) (by omega)
  have B_power_nonnegative : 0 ≤ (2 / 3 : ℚ) ^ B := by positivity
  have qB_product_nonnegative :
      0 ≤ (2 / 3 : ℚ) ^ q * (2 / 3 : ℚ) ^ B := by positivity
  have total_power_positive : 0 < (2 / 3 : ℚ) ^ (A + B) := by positivity
  have total_power_lt :
      (2 / 3 : ℚ) ^ (A + B) < (2 / 3 : ℚ) ^ 2 :=
    pow_right_strictAnti₀ (by norm_num) (by norm_num) total_positive
  have denominator_positive :
      0 < 27 * (2 / 3 : ℚ) ^ (p + q) *
        ((2 / 3 : ℚ) ^ 2 - (2 / 3 : ℚ) ^ (A + B)) := by
    positivity
  have denominator_upper :
      27 * (2 / 3 : ℚ) ^ (p + q) *
          ((2 / 3 : ℚ) ^ 2 - (2 / 3 : ℚ) ^ (A + B)) < 8 := by
    have difference_lt :
        (2 / 3 : ℚ) ^ 2 - (2 / 3 : ℚ) ^ (A + B) <
          (2 / 3 : ℚ) ^ 2 := by
      linarith
    norm_num at difference_lt ⊢
    nlinarith
  have numerator_lower :
      17 / 3 ≤
        9 * (2 / 3 : ℚ) ^ q *
            ((2 / 3 : ℚ) ^ B - (2 / 3 : ℚ) ^ 2) +
          15 * (1 - (2 / 3 : ℚ) ^ 2) := by
    norm_num
    nlinarith
  have source_gt_half : 1 / 2 < lengthThreeFallingSource p q A B 2 := by
    rw [lengthThreeFallingSource]
    apply (lt_div_iff₀ denominator_positive).2
    nlinarith
  exact (not_lt_of_ge source_mem.2) source_gt_half

theorem lengthThreeFalling_two_realTrap_forces_pq_zero
    (p q A B : ℕ) (total_positive : 2 < A + B)
    (source_mem :
      lengthThreeFallingSource p q A B 2 ∈ Set.Icc (1 / 5) (1 / 2)) :
    p = 0 ∧ q = 0 := by
  have q_zero := lengthThreeFalling_two_realTrap_forces_q_zero
    p q A B total_positive source_mem
  subst q
  refine ⟨?_, rfl⟩
  by_contra p_ne
  have p_positive : 0 < p := Nat.pos_of_ne_zero p_ne
  have p_power_upper : (2 / 3 : ℚ) ^ p ≤ 2 / 3 := by
    have order := pow_le_pow_of_le_one
      (show 0 ≤ (2 / 3 : ℚ) by norm_num)
      (show (2 / 3 : ℚ) ≤ 1 by norm_num) p_positive
    norm_num at order ⊢
    exact order
  have B_power_positive : 0 < (2 / 3 : ℚ) ^ B := by positivity
  have total_power_positive : 0 < (2 / 3 : ℚ) ^ (A + B) := by positivity
  have total_power_lt :
      (2 / 3 : ℚ) ^ (A + B) < (2 / 3 : ℚ) ^ 2 :=
    pow_right_strictAnti₀ (by norm_num) (by norm_num) total_positive
  have denominator_positive :
      0 < 27 * (2 / 3 : ℚ) ^ (p + 0) *
        ((2 / 3 : ℚ) ^ 2 - (2 / 3 : ℚ) ^ (A + B)) := by
    positivity
  have denominator_upper :
      27 * (2 / 3 : ℚ) ^ (p + 0) *
          ((2 / 3 : ℚ) ^ 2 - (2 / 3 : ℚ) ^ (A + B)) < 8 := by
    have difference_lt :
        (2 / 3 : ℚ) ^ 2 - (2 / 3 : ℚ) ^ (A + B) <
          (2 / 3 : ℚ) ^ 2 := by
      linarith
    norm_num at difference_lt ⊢
    nlinarith
  have numerator_lower :
      13 / 3 <
        9 * (2 / 3 : ℚ) ^ 0 *
            ((2 / 3 : ℚ) ^ B - (2 / 3 : ℚ) ^ 2) +
          15 * (1 - (2 / 3 : ℚ) ^ 2) := by
    norm_num
    linarith
  have source_gt_half : 1 / 2 < lengthThreeFallingSource p 0 A B 2 := by
    rw [lengthThreeFallingSource]
    apply (lt_div_iff₀ denominator_positive).2
    nlinarith
  exact (not_lt_of_ge source_mem.2) source_gt_half

theorem lengthThreeFalling_one_realTrap_forces_q_le_two
    (p q A B : ℕ) (total_positive : 1 < A + B)
    (source_mem :
      lengthThreeFallingSource p q A B 1 ∈ Set.Icc (1 / 5) (1 / 2)) :
    q ≤ 2 := by
  by_contra q_large
  have three_le : 3 ≤ q := by omega
  have q_power_upper : (2 / 3 : ℚ) ^ q ≤ 8 / 27 := by
    have order := pow_le_pow_of_le_one
      (show 0 ≤ (2 / 3 : ℚ) by norm_num)
      (show (2 / 3 : ℚ) ≤ 1 by norm_num) three_le
    norm_num at order ⊢
    exact order
  have baseline_power_upper :
      (2 / 3 : ℚ) ^ (p + q) ≤ (2 / 3 : ℚ) ^ q := by
    exact pow_le_pow_of_le_one
      (show 0 ≤ (2 / 3 : ℚ) by norm_num)
      (show (2 / 3 : ℚ) ≤ 1 by norm_num) (by omega)
  have B_power_nonnegative : 0 ≤ (2 / 3 : ℚ) ^ B := by positivity
  have qB_product_nonnegative :
      0 ≤ (2 / 3 : ℚ) ^ q * (2 / 3 : ℚ) ^ B := by positivity
  have total_power_positive : 0 < (2 / 3 : ℚ) ^ (A + B) := by positivity
  have total_power_lt :
      (2 / 3 : ℚ) ^ (A + B) < (2 / 3 : ℚ) := by
    simpa only [pow_one] using
      pow_right_strictAnti₀ (show 0 < (2 / 3 : ℚ) by norm_num)
        (show (2 / 3 : ℚ) < 1 by norm_num) total_positive
  have denominator_positive :
      0 < 27 * (2 / 3 : ℚ) ^ (p + q) *
        ((2 / 3 : ℚ) - (2 / 3 : ℚ) ^ (A + B)) := by
    positivity
  have denominator_upper :
      27 * (2 / 3 : ℚ) ^ (p + q) *
          ((2 / 3 : ℚ) - (2 / 3 : ℚ) ^ (A + B)) < 16 / 3 := by
    have difference_lt :
        (2 / 3 : ℚ) - (2 / 3 : ℚ) ^ (A + B) < 2 / 3 := by
      linarith
    nlinarith
  have numerator_lower :
      29 / 9 ≤
        9 * (2 / 3 : ℚ) ^ q *
            ((2 / 3 : ℚ) ^ B - (2 / 3 : ℚ)) +
          15 * (1 - (2 / 3 : ℚ)) := by
    norm_num
    nlinarith
  have source_gt_half : 1 / 2 < lengthThreeFallingSource p q A B 1 := by
    rw [lengthThreeFallingSource, pow_one]
    apply (lt_div_iff₀ denominator_positive).2
    nlinarith
  exact (not_lt_of_ge source_mem.2) source_gt_half

theorem lengthThreeFalling_one_realTrap_q_two_forces_p_le_one
    (p A B : ℕ) (total_positive : 1 < A + B)
    (source_mem :
      lengthThreeFallingSource p 2 A B 1 ∈ Set.Icc (1 / 5) (1 / 2)) :
    p ≤ 1 := by
  by_contra p_large
  have two_le : 2 ≤ p := by omega
  have baseline_power_upper :
      (2 / 3 : ℚ) ^ (p + 2) ≤ (2 / 3 : ℚ) ^ 4 := by
    exact pow_le_pow_of_le_one
      (show 0 ≤ (2 / 3 : ℚ) by norm_num)
      (show (2 / 3 : ℚ) ≤ 1 by norm_num) (by omega)
  have B_power_nonnegative : 0 ≤ (2 / 3 : ℚ) ^ B := by positivity
  have total_power_positive : 0 < (2 / 3 : ℚ) ^ (A + B) := by positivity
  have total_power_lt :
      (2 / 3 : ℚ) ^ (A + B) < (2 / 3 : ℚ) := by
    simpa only [pow_one] using
      pow_right_strictAnti₀ (show 0 < (2 / 3 : ℚ) by norm_num)
        (show (2 / 3 : ℚ) < 1 by norm_num) total_positive
  have denominator_positive :
      0 < 27 * (2 / 3 : ℚ) ^ (p + 2) *
        ((2 / 3 : ℚ) - (2 / 3 : ℚ) ^ (A + B)) := by
    positivity
  have denominator_upper :
      27 * (2 / 3 : ℚ) ^ (p + 2) *
          ((2 / 3 : ℚ) - (2 / 3 : ℚ) ^ (A + B)) < 32 / 9 := by
    have difference_lt :
        (2 / 3 : ℚ) - (2 / 3 : ℚ) ^ (A + B) < 2 / 3 := by
      linarith
    norm_num at baseline_power_upper ⊢
    nlinarith
  have numerator_lower :
      7 / 3 ≤
        9 * (2 / 3 : ℚ) ^ 2 *
            ((2 / 3 : ℚ) ^ B - (2 / 3 : ℚ)) +
          15 * (1 - (2 / 3 : ℚ)) := by
    norm_num
    linarith
  have source_gt_half : 1 / 2 < lengthThreeFallingSource p 2 A B 1 := by
    rw [lengthThreeFallingSource, pow_one]
    apply (lt_div_iff₀ denominator_positive).2
    nlinarith
  exact (not_lt_of_ge source_mem.2) source_gt_half

theorem lengthThreeFalling_one_realTrap_q_one_forces_p_le_four
    (p A B : ℕ) (total_positive : 1 < A + B)
    (source_mem :
      lengthThreeFallingSource p 1 A B 1 ∈ Set.Icc (1 / 5) (1 / 2)) :
    p ≤ 4 := by
  by_contra p_large
  have five_le : 5 ≤ p := by omega
  have baseline_power_upper :
      (2 / 3 : ℚ) ^ (p + 1) ≤ (2 / 3 : ℚ) ^ 6 := by
    exact pow_le_pow_of_le_one
      (show 0 ≤ (2 / 3 : ℚ) by norm_num)
      (show (2 / 3 : ℚ) ≤ 1 by norm_num) (by omega)
  have B_power_nonnegative : 0 ≤ (2 / 3 : ℚ) ^ B := by positivity
  have total_power_positive : 0 < (2 / 3 : ℚ) ^ (A + B) := by positivity
  have total_power_lt :
      (2 / 3 : ℚ) ^ (A + B) < (2 / 3 : ℚ) := by
    simpa only [pow_one] using
      pow_right_strictAnti₀ (show 0 < (2 / 3 : ℚ) by norm_num)
        (show (2 / 3 : ℚ) < 1 by norm_num) total_positive
  have denominator_positive :
      0 < 27 * (2 / 3 : ℚ) ^ (p + 1) *
        ((2 / 3 : ℚ) - (2 / 3 : ℚ) ^ (A + B)) := by
    positivity
  have denominator_upper :
      27 * (2 / 3 : ℚ) ^ (p + 1) *
          ((2 / 3 : ℚ) - (2 / 3 : ℚ) ^ (A + B)) < 128 / 81 := by
    have difference_lt :
        (2 / 3 : ℚ) - (2 / 3 : ℚ) ^ (A + B) < 2 / 3 := by
      linarith
    norm_num at baseline_power_upper ⊢
    nlinarith
  have numerator_lower :
      1 ≤
        9 * (2 / 3 : ℚ) *
            ((2 / 3 : ℚ) ^ B - (2 / 3 : ℚ)) +
          15 * (1 - (2 / 3 : ℚ)) := by
    norm_num
    linarith
  have source_gt_half : 1 / 2 < lengthThreeFallingSource p 1 A B 1 := by
    rw [lengthThreeFallingSource, pow_one]
    apply (lt_div_iff₀ denominator_positive).2
    nlinarith
  exact (not_lt_of_ge source_mem.2) source_gt_half

theorem lengthThreeFalling_one_realTrap_q_zero_forces_B_le_five
    (p A B : ℕ) (total_positive : 1 < A + B)
    (source_mem :
      lengthThreeFallingSource p 0 A B 1 ∈ Set.Icc (1 / 5) (1 / 2)) :
    B ≤ 5 := by
  by_contra B_large
  have six_le : 6 ≤ B := by omega
  have B_power_upper : (2 / 3 : ℚ) ^ B ≤ (2 / 3 : ℚ) ^ 6 := by
    exact pow_le_pow_of_le_one
      (show 0 ≤ (2 / 3 : ℚ) by norm_num)
      (show (2 / 3 : ℚ) ≤ 1 by norm_num) six_le
  have total_power_lt :
      (2 / 3 : ℚ) ^ (A + B) < (2 / 3 : ℚ) := by
    simpa only [pow_one] using
      pow_right_strictAnti₀ (show 0 < (2 / 3 : ℚ) by norm_num)
        (show (2 / 3 : ℚ) < 1 by norm_num) total_positive
  have denominator_positive :
      0 < 27 * (2 / 3 : ℚ) ^ (p + 0) *
        ((2 / 3 : ℚ) - (2 / 3 : ℚ) ^ (A + B)) := by
    positivity
  have numerator_nonpositive :
      9 * (2 / 3 : ℚ) ^ 0 *
            ((2 / 3 : ℚ) ^ B - (2 / 3 : ℚ)) +
          15 * (1 - (2 / 3 : ℚ)) ≤ 0 := by
    norm_num at B_power_upper ⊢
    linarith
  have source_nonpositive : lengthThreeFallingSource p 0 A B 1 ≤ 0 := by
    rw [lengthThreeFallingSource, pow_one]
    exact div_nonpos_of_nonpos_of_nonneg numerator_nonpositive
      (le_of_lt denominator_positive)
  linarith [source_mem.1]

theorem lengthThreeFalling_one_realTrap_q_zero_forces_p_le_nine
    (p A B : ℕ) (total_positive : 1 < A + B)
    (source_mem :
      lengthThreeFallingSource p 0 A B 1 ∈ Set.Icc (1 / 5) (1 / 2)) :
    p ≤ 9 := by
  have B_le := lengthThreeFalling_one_realTrap_q_zero_forces_B_le_five
    p A B total_positive source_mem
  by_contra p_large
  have ten_le : 10 ≤ p := by omega
  have p_power_upper : (2 / 3 : ℚ) ^ p ≤ (2 / 3 : ℚ) ^ 10 := by
    exact pow_le_pow_of_le_one
      (show 0 ≤ (2 / 3 : ℚ) by norm_num)
      (show (2 / 3 : ℚ) ≤ 1 by norm_num) ten_le
  have B_power_lower : (2 / 3 : ℚ) ^ 5 ≤ (2 / 3 : ℚ) ^ B := by
    exact pow_le_pow_of_le_one
      (show 0 ≤ (2 / 3 : ℚ) by norm_num)
      (show (2 / 3 : ℚ) ≤ 1 by norm_num) B_le
  have total_power_positive : 0 < (2 / 3 : ℚ) ^ (A + B) := by positivity
  have total_power_lt :
      (2 / 3 : ℚ) ^ (A + B) < (2 / 3 : ℚ) := by
    simpa only [pow_one] using
      pow_right_strictAnti₀ (show 0 < (2 / 3 : ℚ) by norm_num)
        (show (2 / 3 : ℚ) < 1 by norm_num) total_positive
  have denominator_positive :
      0 < 27 * (2 / 3 : ℚ) ^ (p + 0) *
        ((2 / 3 : ℚ) - (2 / 3 : ℚ) ^ (A + B)) := by
    positivity
  have denominator_upper :
      27 * (2 / 3 : ℚ) ^ (p + 0) *
          ((2 / 3 : ℚ) - (2 / 3 : ℚ) ^ (A + B)) <
        18432 / 59049 := by
    have difference_lt :
        (2 / 3 : ℚ) - (2 / 3 : ℚ) ^ (A + B) < 2 / 3 := by
      linarith
    norm_num at p_power_upper ⊢
    nlinarith
  have numerator_lower :
      5 / 27 ≤
        9 * (2 / 3 : ℚ) ^ 0 *
            ((2 / 3 : ℚ) ^ B - (2 / 3 : ℚ)) +
          15 * (1 - (2 / 3 : ℚ)) := by
    norm_num at B_power_lower ⊢
    linarith
  have source_gt_half : 1 / 2 < lengthThreeFallingSource p 0 A B 1 := by
    rw [lengthThreeFallingSource, pow_one]
    apply (lt_div_iff₀ denominator_positive).2
    nlinarith
  exact (not_lt_of_ge source_mem.2) source_gt_half

theorem lengthThreeFalling_one_realTrap_parameter_cut
    (p q A B : ℕ) (total_positive : 1 < A + B)
    (source_mem :
      lengthThreeFallingSource p q A B 1 ∈ Set.Icc (1 / 5) (1 / 2)) :
    (q = 0 ∧ B ≤ 5 ∧ p ≤ 9) ∨
      (q = 1 ∧ p ≤ 4) ∨
      (q = 2 ∧ p ≤ 1) := by
  have q_le := lengthThreeFalling_one_realTrap_forces_q_le_two
    p q A B total_positive source_mem
  interval_cases q
  · exact Or.inl ⟨rfl,
      lengthThreeFalling_one_realTrap_q_zero_forces_B_le_five
        p A B total_positive source_mem,
      lengthThreeFalling_one_realTrap_q_zero_forces_p_le_nine
        p A B total_positive source_mem⟩
  · exact Or.inr (Or.inl ⟨rfl,
      lengthThreeFalling_one_realTrap_q_one_forces_p_le_four
        p A B total_positive source_mem⟩)
  · exact Or.inr (Or.inr ⟨rfl,
      lengthThreeFalling_one_realTrap_q_two_forces_p_le_one
        p A B total_positive source_mem⟩)

/-- In the strict falling chamber, target acceptance forces the first positive displacement
to be even. -/
theorem lengthThreeFallingTarget_fiveUnit_forces_A_even
    (p q t : ℕ) {A : ℕ} (B k : ℕ) (A_positive : 0 < A)
    (total_positive : k < A + B)
    (target_unit : IsUnit 5 (lengthThreeFallingTarget q t A B k)) :
    Even A := by
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
  have collision_source :=
    lengthThreeFalling_collisionSource p q t A B total_positive
  have common_target :=
    (lengthThreeFalling_commonTarget p q t A B total_positive).1
  have collision_target_unit :
      IsUnit 5
        (shellRun (lengthThreeFallingLeft p q t A B)
          (collisionSource (lengthThreeFallingLeft p q t A B)
            (lengthThreeFallingRight p q t k))) := by
    rw [collision_source, common_target]
    exact target_unit
  have first_gap :
      shellPrefixSumGap
          (lengthThreeFallingLeft p q t A B)
          (lengthThreeFallingRight p q t k) 0 = A := by
    simp only [shellPrefixSumGap, lengthThreeFallingLeft,
      lengthThreeFallingRight, List.take, shellSlopeSumGap, List.sum_cons,
      List.sum_nil, Nat.add_zero]
    omega
  have first_even := acceptedCollision_firstNonzeroPrefixGap_even
    length_eq sum_ne collision_target_unit (first := 0)
    (by simp [lengthThreeFallingLeft])
    (by rw [first_gap]; omega) (by omega)
  rwa [first_gap] at first_even

end MatrixMortality.MixedPrimeDebt
