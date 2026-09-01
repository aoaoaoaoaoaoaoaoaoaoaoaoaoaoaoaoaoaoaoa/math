import MatrixMortality.ReturnSquarePureDenominator

/-!
# Real descent for pure-denominator ReturnSquare tails

At a positive denominator `B`, the affine inverse branch has an invariant interval `[-1,1]`.
Outside that trap, every viable inverse step decreases its target by at least the selected scale
minus one. This bounds the complete common-base tail independently of p-adic common content.
-/

namespace MatrixMortality.ReturnSquare

/-- Denominator of one pure-denominator affine predecessor. -/
def pureDenominatorPredecessorDenominator (B t s : ℚ) : ℚ :=
  s * t + (B - 1) * t ^ 2 - B

/-- Execute pure-denominator affine predecessors from the right end of a scale word. -/
def fractionPredecessorRun (q B : ℚ) : List Nat → ℚ → ℚ
  | [], target => target
  | wait :: tail, target =>
      fractionPredecessor 1 B (q ^ (wait + 1))
        (fractionPredecessorRun q B tail target)

/-- Additive descent cost of a common-base tail. -/
def fractionPredecessorCost (q : ℚ) : List Nat → ℚ
  | [] => 0
  | wait :: tail => q ^ (wait + 1) - 1 + fractionPredecessorCost q tail

private theorem pureDenominatorPredecessorDenominator_pos
    (B t s : ℚ) (B_at_least_two : 2 ≤ B) (t_at_least_four : 4 ≤ t)
    (s_at_least_neg_one : -1 ≤ s) :
    0 < pureDenominatorPredecessorDenominator B t s := by
  have B_term_nonnegative : 0 ≤ (B - 2) * (t ^ 2 - 1) :=
    mul_nonneg (by linarith) (by nlinarith)
  have t_term_positive : 0 < t ^ 2 - t - 2 := by nlinarith
  have base_positive : 0 < (B - 1) * t ^ 2 - B - t := by
    nlinarith
  have target_bound : -t ≤ s * t := by
    have product_nonnegative : 0 ≤ (s + 1) * t :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  dsimp [pureDenominatorPredecessorDenominator]
  linarith

private theorem fractionPredecessor_pure_ge_neg_one
    (B t s : ℚ) (B_at_least_two : 2 ≤ B) (t_at_least_four : 4 ≤ t)
    (s_at_least_neg_one : -1 ≤ s) :
    -1 ≤ fractionPredecessor 1 B t s := by
  have denominator_pos := pureDenominatorPredecessorDenominator_pos
    B t s B_at_least_two t_at_least_four s_at_least_neg_one
  rw [fractionPredecessor]
  apply (le_div_iff₀ denominator_pos).2
  have B_term_nonnegative :
      0 ≤ (B - 2) * (t ^ 2 - t - 2) :=
    mul_nonneg (by linarith) (by nlinarith)
  have t_term_nonnegative : 0 ≤ t ^ 2 - 3 * t - 4 := by
    have product_nonnegative : 0 ≤ (t - 4) * (t + 1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have endpoint_nonnegative :
      0 ≤ (B - 1) * t ^ 2 - (B + 1) * t - 2 * B := by
    nlinarith
  have target_term_nonnegative : 0 ≤ (B + 1) * t * (s + 1) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  dsimp [pureDenominatorPredecessorDenominator] at denominator_pos ⊢
  nlinarith

private theorem fractionPredecessor_pure_gt_one_iff
    (B t s : ℚ) (B_at_least_two : 2 ≤ B) (t_at_least_four : 4 ≤ t)
    (s_at_least_neg_one : -1 ≤ s) :
    1 < fractionPredecessor 1 B t s ↔ t < s := by
  have denominator_pos := pureDenominatorPredecessorDenominator_pos
    B t s B_at_least_two t_at_least_four s_at_least_neg_one
  have denominator_pos' : 0 < s * t + (B - 1) * t ^ 2 - B := by
    simpa [pureDenominatorPredecessorDenominator] using denominator_pos
  rw [fractionPredecessor, lt_div_iff₀ denominator_pos']
  dsimp [pureDenominatorPredecessorDenominator] at denominator_pos ⊢
  constructor <;> intro inequality
  · by_contra not_lt
    have product_nonpositive : (B - 1) * t * (s - t) ≤ 0 := by
      have coefficient_nonnegative : 0 ≤ (B - 1) * t :=
        mul_nonneg (by linarith) (by linarith)
      exact mul_nonpos_of_nonneg_of_nonpos coefficient_nonnegative
        (sub_nonpos.mpr (le_of_not_gt not_lt))
    nlinarith
  · have product_positive : 0 < (B - 1) * t * (s - t) :=
      mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    nlinarith

private theorem fractionPredecessor_pure_le_sub_add_one
    (B t s : ℚ) (B_at_least_two : 2 ≤ B) (t_at_least_four : 4 ≤ t)
    (target_above_scale : t < s) :
    fractionPredecessor 1 B t s ≤ s - t + 1 := by
  have s_at_least_neg_one : -1 ≤ s := by linarith
  have denominator_pos := pureDenominatorPredecessorDenominator_pos
    B t s B_at_least_two t_at_least_four s_at_least_neg_one
  rw [fractionPredecessor]
  apply (div_le_iff₀ denominator_pos).2
  have scale_product_ge_two : 2 ≤ t * (t - 1) := by nlinarith
  have denominator_term_nonnegative :
      0 ≤ (B - 1) * (t * (t - 1)) - B := by
    have product_nonnegative :
        0 ≤ (B - 2) * (t * (t - 1) - 1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have bracket_positive :
      0 < t * s + (B - 1) * t * (t - 1) - B := by
    nlinarith
  have factor_nonnegative :
      0 ≤ (s - t) * (t * s + (B - 1) * t * (t - 1) - B) := by
    exact mul_nonneg (by linarith) bracket_positive.le
  dsimp [pureDenominatorPredecessorDenominator] at denominator_pos ⊢
  nlinarith

private theorem fractionPredecessorRun_ge_neg_one
    (q B target : ℚ) (B_at_least_two : 2 ≤ B) (q_at_least_four : 4 ≤ q)
    (target_at_least_neg_one : -1 ≤ target) (tail : List Nat) :
    -1 ≤ fractionPredecessorRun q B tail target := by
  induction tail with
  | nil => simpa [fractionPredecessorRun] using target_at_least_neg_one
  | cons wait tail induction =>
      have scale_at_least_four : 4 ≤ q ^ (wait + 1) := by
        have q_positive : 0 ≤ q := by positivity
        have one_le_power : 1 ≤ q ^ wait := one_le_pow₀ (by linarith)
        rw [pow_succ]
        nlinarith
      exact fractionPredecessor_pure_ge_neg_one
        B (q ^ (wait + 1)) (fractionPredecessorRun q B tail target)
          B_at_least_two scale_at_least_four induction

/-- Any inverse word which ends above one pays at least the sum of its scale decrements. -/
theorem fractionPredecessorRun_add_cost_le
    (q B target : ℚ) (B_at_least_two : 2 ≤ B) (q_at_least_four : 4 ≤ q)
    (target_at_least_neg_one : -1 ≤ target) (tail : List Nat)
    (run_above_one : 1 < fractionPredecessorRun q B tail target) :
    fractionPredecessorRun q B tail target + fractionPredecessorCost q tail ≤ target := by
  induction tail with
  | nil => simp [fractionPredecessorRun, fractionPredecessorCost]
  | cons wait tail induction =>
      let scale := q ^ (wait + 1)
      let middle := fractionPredecessorRun q B tail target
      have middle_at_least_neg_one : -1 ≤ middle :=
        fractionPredecessorRun_ge_neg_one
          q B target B_at_least_two q_at_least_four target_at_least_neg_one tail
      have scale_at_least_four : 4 ≤ scale := by
        have q_positive : 0 ≤ q := by positivity
        have one_le_power : 1 ≤ q ^ wait := one_le_pow₀ (by linarith)
        dsimp [scale]
        rw [pow_succ]
        nlinarith
      have scale_lt_middle : scale < middle :=
        (fractionPredecessor_pure_gt_one_iff
          B scale middle B_at_least_two scale_at_least_four
            middle_at_least_neg_one).mp run_above_one
      have middle_above_one : 1 < middle := by linarith
      have tail_descent := induction middle_above_one
      have step_descent := fractionPredecessor_pure_le_sub_add_one
        B scale middle B_at_least_two scale_at_least_four scale_lt_middle
      simp only [fractionPredecessorRun, fractionPredecessorCost]
      dsimp [scale, middle] at step_descent tail_descent ⊢
      linarith

/-- The affine predecessor run is the exact projective coordinate of the homogeneous adjugate
tail, whose lower coordinate stays strictly positive. -/
theorem fractionTailPredecessorState_pure_lower_pos_and_ratio
    (q B : ℚ) (q_at_least_four : 4 ≤ q) (B_at_least_two : 2 ≤ B)
    (tail : List Nat) :
    0 < fractionTailPredecessorState q 1 B tail 1 ∧
      fractionTailPredecessorState q 1 B tail 0 =
        fractionPredecessorRun q B tail B *
          fractionTailPredecessorState q 1 B tail 1 := by
  induction tail with
  | nil => simp [fractionTailPredecessorState, fractionPredecessorRun, wordProduct]
  | cons wait tail induction =>
      let scale := q ^ (wait + 1)
      let middle := fractionPredecessorRun q B tail B
      have scale_at_least_four : 4 ≤ scale := by
        have q_nonnegative : 0 ≤ q := by linarith
        have one_le_power : 1 ≤ q ^ wait := one_le_pow₀ (by linarith)
        dsimp [scale]
        rw [pow_succ]
        nlinarith
      have terminal_at_least_neg_one : -1 ≤ B := by linarith
      have middle_at_least_neg_one : -1 ≤ middle := by
        exact fractionPredecessorRun_ge_neg_one q B B B_at_least_two q_at_least_four
          terminal_at_least_neg_one tail
      have denominator_pos :
          0 < pureDenominatorPredecessorDenominator B scale middle :=
        pureDenominatorPredecessorDenominator_pos B scale middle B_at_least_two
          scale_at_least_four middle_at_least_neg_one
      have tail_lower_pos := induction.1
      have tail_ratio := induction.2
      change
        fractionTailPredecessorState q 1 B tail 0 =
          middle * fractionTailPredecessorState q 1 B tail 1 at tail_ratio
      have state_cons :
          fractionTailPredecessorState q 1 B (wait :: tail) =
            Matrix.mulVec (fractionPullbackAdjugate 1 B scale)
              (fractionTailPredecessorState q 1 B tail) := by
        dsimp [scale]
        rw [fractionTailPredecessorState, wordProduct_cons, ← Matrix.mulVec_mulVec]
        rw [fractionTailPredecessorState]
      rw [state_cons]
      change
        0 < Matrix.mulVec (fractionPullbackAdjugate 1 B scale)
              (fractionTailPredecessorState q 1 B tail) 1 ∧
          Matrix.mulVec (fractionPullbackAdjugate 1 B scale)
              (fractionTailPredecessorState q 1 B tail) 0 =
            fractionPredecessor 1 B scale middle *
              Matrix.mulVec (fractionPullbackAdjugate 1 B scale)
                (fractionTailPredecessorState q 1 B tail) 1
      have lower_formula :
          Matrix.mulVec (fractionPullbackAdjugate 1 B scale)
              (fractionTailPredecessorState q 1 B tail) 1 =
            pureDenominatorPredecessorDenominator B scale middle *
              fractionTailPredecessorState q 1 B tail 1 := by
        simp [fractionPullbackAdjugate, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ]
        rw [tail_ratio]
        simp [pureDenominatorPredecessorDenominator]
        ring
      have upper_formula :
          Matrix.mulVec (fractionPullbackAdjugate 1 B scale)
              (fractionTailPredecessorState q 1 B tail) 0 =
            B * (middle * scale - 1) *
              fractionTailPredecessorState q 1 B tail 1 := by
        simp [fractionPullbackAdjugate, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ]
        rw [tail_ratio]
        ring
      constructor
      · rw [lower_formula]
        exact mul_pos denominator_pos tail_lower_pos
      · rw [upper_formula, lower_formula, fractionPredecessor]
        change
          B * (middle * scale - 1) * fractionTailPredecessorState q 1 B tail 1 =
            (B * (middle * scale - 1) /
                pureDenominatorPredecessorDenominator B scale middle) *
              (pureDenominatorPredecessorDenominator B scale middle *
                fractionTailPredecessorState q 1 B tail 1)
        rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt denominator_pos)]

/-- A pure-denominator bridge zero identifies the affine predecessor run with its separated
source scale. -/
theorem positiveBridge_pureDenominator_zero_run_eq
    (q B : ℚ) (q_at_least_four : 4 ≤ q) (B_at_least_two : 2 ≤ B)
    (head : Nat) (tail : List Nat)
    (bridge_zero : positiveBridge q (-(1 / B)) (head :: tail) = 0) :
    fractionPredecessorRun q B tail B = q ^ (head + 1) := by
  have B_ne : B ≠ 0 := by linarith
  have B_sub_one_ne : B - 1 ≠ 0 := by linarith
  have q_ne : q ≠ 0 := by linarith
  have incidence :=
    (positiveBridge_fraction_cons_zero_iff_tailAdjugate
      q 1 B head tail B_ne B_sub_one_ne q_ne).mp bridge_zero
  obtain ⟨lower_pos, ratio⟩ :=
    fractionTailPredecessorState_pure_lower_pos_and_ratio
      q B q_at_least_four B_at_least_two tail
  apply mul_right_cancel₀ (ne_of_gt lower_pos)
  calc
    fractionPredecessorRun q B tail B *
          fractionTailPredecessorState q 1 B tail 1 =
        fractionTailPredecessorState q 1 B tail 0 := ratio.symm
    _ = q ^ (head + 1) * fractionTailPredecessorState q 1 B tail 1 := by
      simpa using incidence

/-- A pure-denominator bridge zero pays its complete inverse-word cost from the terminal
denominator. -/
theorem positiveBridge_pureDenominator_zero_add_cost_le
    (q B : ℚ) (q_at_least_four : 4 ≤ q) (B_at_least_two : 2 ≤ B)
    (head : Nat) (tail : List Nat)
    (bridge_zero : positiveBridge q (-(1 / B)) (head :: tail) = 0) :
    q ^ (head + 1) + fractionPredecessorCost q tail ≤ B := by
  have run_eq := positiveBridge_pureDenominator_zero_run_eq
    q B q_at_least_four B_at_least_two head tail bridge_zero
  have source_above_one : 1 < q ^ (head + 1) :=
    one_lt_pow₀ (by linarith) (Nat.succ_ne_zero head)
  have run_above_one : 1 < fractionPredecessorRun q B tail B := by
    rw [run_eq]
    exact source_above_one
  have terminal_at_least_neg_one : -1 ≤ B := by linarith
  have descent := fractionPredecessorRun_add_cost_le
    q B B B_at_least_two q_at_least_four terminal_at_least_neg_one tail
      run_above_one
  simpa [run_eq] using descent

/-- The additive cost of every common-base tail is nonnegative. -/
theorem fractionPredecessorCost_nonnegative
    (q : ℚ) (q_at_least_one : 1 ≤ q) (tail : List Nat) :
    0 ≤ fractionPredecessorCost q tail := by
  induction tail with
  | nil => simp [fractionPredecessorCost]
  | cons wait tail induction =>
      have scale_at_least_one : 1 ≤ q ^ (wait + 1) :=
        one_le_pow₀ q_at_least_one
      simp only [fractionPredecessorCost]
      linarith

/-- Every selected scale contributes its scale decrement to the total inverse-word cost. -/
theorem fractionPredecessor_scale_sub_one_le_cost_of_mem
    (q : ℚ) (q_at_least_one : 1 ≤ q) (wait : Nat) (tail : List Nat)
    (wait_mem : wait ∈ tail) :
    q ^ (wait + 1) - 1 ≤ fractionPredecessorCost q tail := by
  induction tail with
  | nil => simp at wait_mem
  | cons first tail induction =>
      rcases List.mem_cons.mp wait_mem with wait_eq | wait_mem_tail
      · subst first
        have tail_cost_nonnegative :=
          fractionPredecessorCost_nonnegative q q_at_least_one tail
        simp only [fractionPredecessorCost]
        linarith
      · have first_scale_at_least_one : 1 ≤ q ^ (first + 1) :=
          one_le_pow₀ q_at_least_one
        have tail_bound := induction wait_mem_tail
        simp only [fractionPredecessorCost]
        linarith

/-- Tail length times the least possible scale decrement is a lower bound for total cost. -/
theorem fractionPredecessor_length_mul_base_sub_one_le_cost
    (q : ℚ) (q_at_least_one : 1 ≤ q) (tail : List Nat) :
    (tail.length : ℚ) * (q - 1) ≤ fractionPredecessorCost q tail := by
  induction tail with
  | nil => simp [fractionPredecessorCost]
  | cons wait tail induction =>
      have q_nonnegative : 0 ≤ q := by linarith
      have wait_power_at_least_one : 1 ≤ q ^ wait := one_le_pow₀ q_at_least_one
      have scale_at_least_base : q ≤ q ^ (wait + 1) := by
        rw [pow_succ]
        nlinarith
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one,
        fractionPredecessorCost]
      nlinarith

/-- Every tail exponent in a pure-denominator bridge zero selects a scale strictly below the
terminal denominator. -/
theorem positiveBridge_pureDenominator_zero_tail_scale_lt
    (q B : ℚ) (q_at_least_four : 4 ≤ q) (B_at_least_two : 2 ≤ B)
    (head wait : Nat) (tail : List Nat)
    (bridge_zero : positiveBridge q (-(1 / B)) (head :: tail) = 0)
    (wait_mem : wait ∈ tail) :
    q ^ (wait + 1) < B := by
  have cost_bound := positiveBridge_pureDenominator_zero_add_cost_le
    q B q_at_least_four B_at_least_two head tail bridge_zero
  have scale_cost_bound := fractionPredecessor_scale_sub_one_le_cost_of_mem
    q (by linarith) wait tail wait_mem
  have source_above_one : 1 < q ^ (head + 1) :=
    one_lt_pow₀ (by linarith) (Nat.succ_ne_zero head)
  linarith

/-- Pure-denominator mortality has a linear tail-length bound in addition to the individual
scale bound. -/
theorem positiveBridge_pureDenominator_zero_length_bound
    (q B : ℚ) (q_at_least_four : 4 ≤ q) (B_at_least_two : 2 ≤ B)
    (head : Nat) (tail : List Nat)
    (bridge_zero : positiveBridge q (-(1 / B)) (head :: tail) = 0) :
    q ^ (head + 1) + (tail.length : ℚ) * (q - 1) ≤ B := by
  have cost_bound := positiveBridge_pureDenominator_zero_add_cost_le
    q B q_at_least_four B_at_least_two head tail bridge_zero
  have length_cost_bound := fractionPredecessor_length_mul_base_sub_one_le_cost
    q (by linarith) tail
  linarith

end MatrixMortality.ReturnSquare
