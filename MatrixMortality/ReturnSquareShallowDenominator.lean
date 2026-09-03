import MatrixMortality.ReturnSquarePureDenominatorDescent

/-!
# Shallow pure-denominator ReturnSquare classification

The rightmost inverse step contracts the terminal denominator by more than its selected scale.
Combined with two-return extinction, this classifies every denominator through the first
possible terminal-weighted three-return budget.  In this chamber mortality is exactly a
one-return resonance.
-/

namespace MatrixMortality.ReturnSquare

private theorem base_le_succ_power
    (q head : Nat) (q_positive : 0 < q) :
    q ≤ q ^ (head + 1) := by
  rw [pow_succ]
  exact Nat.le_mul_of_pos_left q (pow_pos q_positive head)

private theorem fractionPredecessorRun_append
    (q B : ℚ) (left right : List Nat) (target : ℚ) :
    fractionPredecessorRun q B (left ++ right) target =
      fractionPredecessorRun q B left (fractionPredecessorRun q B right target) := by
  induction left with
  | nil => simp [fractionPredecessorRun]
  | cons wait left induction =>
      simp only [List.cons_append, fractionPredecessorRun]
      rw [induction]

private theorem fractionPredecessor_pure_terminal_lt_div
    (B t : ℚ) (B_at_least_two : 2 ≤ B) (t_at_least_four : 4 ≤ t)
    (scale_lt_denominator : t < B) :
    fractionPredecessor 1 B t B < B / t := by
  have B_positive : 0 < B := by linarith
  have t_positive : 0 < t := by linarith
  have denominator_positive : 0 < B * t + (B - 1) * t ^ 2 - B := by
    have square_nonnegative : 0 ≤ (t - 1) ^ 2 := sq_nonneg (t - 1)
    nlinarith
  have gap_positive : 0 < B * (B - t) * (t - 1) :=
    mul_pos (mul_pos B_positive (by linarith)) (by linarith)
  rw [fractionPredecessor]
  apply (div_lt_div_iff₀ denominator_positive t_positive).2
  nlinarith only [gap_positive]

/-- Isolating the rightmost tail letter strengthens additive descent to a multiplicative
terminal budget. -/
theorem positiveBridge_pureDenominator_zero_terminal_budget
    (q B : ℚ) (q_at_least_four : 4 ≤ q) (B_at_least_two : 2 ≤ B)
    (head last : Nat) (properTail : List Nat)
    (bridge_zero :
      positiveBridge q (-(1 / B)) (head :: (properTail ++ [last])) = 0) :
    q ^ (last + 1) *
        (q ^ (head + 1) + fractionPredecessorCost q properTail) < B := by
  let scale := q ^ (last + 1)
  let terminalPredecessor := fractionPredecessor 1 B scale B
  have scale_at_least_four : 4 ≤ scale := by
    have one_le_power : 1 ≤ q ^ last := one_le_pow₀ (by linarith)
    dsimp [scale]
    rw [pow_succ]
    nlinarith
  have scale_lt_B : scale < B := by
    dsimp [scale]
    exact positiveBridge_pureDenominator_zero_tail_scale_lt
      q B q_at_least_four B_at_least_two head last (properTail ++ [last]) bridge_zero
        (by simp)
  have denominator_positive : 0 < B * scale + (B - 1) * scale ^ 2 - B := by
    have square_nonnegative : 0 ≤ (scale - 1) ^ 2 := sq_nonneg (scale - 1)
    nlinarith
  have numerator_positive : 0 < B * (B * scale - 1) := by
    exact mul_pos (by linarith) (by nlinarith)
  have terminal_positive : 0 < terminalPredecessor := by
    dsimp [terminalPredecessor]
    rw [fractionPredecessor]
    exact div_pos numerator_positive denominator_positive
  have run_eq := positiveBridge_pureDenominator_zero_run_eq
    q B q_at_least_four B_at_least_two head (properTail ++ [last]) bridge_zero
  rw [fractionPredecessorRun_append] at run_eq
  change
    fractionPredecessorRun q B properTail terminalPredecessor = q ^ (head + 1) at run_eq
  have run_above_one :
      1 < fractionPredecessorRun q B properTail terminalPredecessor := by
    rw [run_eq]
    exact one_lt_pow₀ (by linarith) (Nat.succ_ne_zero head)
  have prefix_descent := fractionPredecessorRun_add_cost_le
    q B terminalPredecessor B_at_least_two q_at_least_four (by linarith)
      properTail run_above_one
  rw [run_eq] at prefix_descent
  have terminal_lt : terminalPredecessor < B / scale := by
    exact fractionPredecessor_pure_terminal_lt_div
      B scale B_at_least_two scale_at_least_four scale_lt_B
  have budget_lt_div :
      q ^ (head + 1) + fractionPredecessorCost q properTail < B / scale :=
    lt_of_le_of_lt prefix_descent terminal_lt
  have scale_positive : 0 < scale := by positivity
  simpa [scale, mul_comm] using (lt_div_iff₀ scale_positive).mp budget_lt_div

/-- Below the first possible terminal-weighted three-return budget, a pure-denominator bridge
zero is exactly a singleton resonance. -/
theorem positiveBridge_pureDenominator_shallow_iff
    (q B : Nat) (q_at_least_four : 4 ≤ q) (B_at_least_two : 1 < B)
    (within_terminal_three_return_floor : B + q ≤ 2 * q ^ 2) (waits : List Nat) :
    positiveBridge (q : ℚ) (-(1 / (B : ℚ))) waits = 0 ↔
      ∃ head : Nat, waits = [head] ∧ B = q ^ (head + 1) := by
  have q_at_least_two_int : 2 ≤ (q : ℤ) := by
    exact_mod_cast show 2 ≤ q by omega
  have B_ne_zero_rat : (B : ℚ) ≠ 0 := by positivity
  have parameter_ne_neg_one : -(1 / (B : ℚ)) + 1 ≠ 0 := by
    intro equality
    have reciprocal_one : (1 : ℚ) / B = 1 := by linarith only [equality]
    have B_eq_one_rat : (B : ℚ) = 1 :=
      ((div_eq_one_iff_eq B_ne_zero_rat).mp reciprocal_one).symm
    have B_eq_one : B = 1 := by exact_mod_cast B_eq_one_rat
    omega
  constructor
  · intro bridge_zero
    obtain ⟨head, waits_eq, resonance⟩ | at_least_three :=
      positiveBridge_zero_shape (q : ℤ) (-(1 / (B : ℚ))) waits
        q_at_least_two_int parameter_ne_neg_one bridge_zero
    · refine ⟨head, waits_eq, ?_⟩
      have denominator_eq_rat : (B : ℚ) = (q : ℚ) ^ (head + 1) := by
        field_simp [B_ne_zero_rat] at resonance
        norm_num at resonance
        linear_combination resonance
      exact_mod_cast denominator_eq_rat
    · rcases waits with _ | ⟨head, tail⟩
      · simp at at_least_three
      have tail_at_least_two : 2 ≤ tail.length := by
        simpa using at_least_three
      have tail_ne : tail ≠ [] := by
        exact List.ne_nil_of_length_pos (by omega)
      let last := tail.getLast tail_ne
      let properTail := tail.dropLast
      have decomposition : properTail ++ [last] = tail := by
        exact List.dropLast_append_getLast tail_ne
      have properTail_ne : properTail ≠ [] := by
        intro properTail_empty
        have tail_singleton : tail = [last] := by
          calc
            tail = properTail ++ [last] := decomposition.symm
            _ = [last] := by rw [properTail_empty]; simp
        rw [tail_singleton] at tail_at_least_two
        simp at tail_at_least_two
      have bridge_zero' :
          positiveBridge (q : ℚ) (-(1 / (B : ℚ)))
            (head :: (properTail ++ [last])) = 0 := by
        rw [decomposition]
        exact bridge_zero
      have terminal_budget := positiveBridge_pureDenominator_zero_terminal_budget
        (q : ℚ) B (by exact_mod_cast q_at_least_four)
          (by exact_mod_cast B_at_least_two) head last properTail bridge_zero'
      have source_at_least_base : q ≤ q ^ (head + 1) :=
        base_le_succ_power q head (by omega)
      have source_at_least_base_rat :
          (q : ℚ) ≤ (q : ℚ) ^ (head + 1) := by
        exact_mod_cast source_at_least_base
      have scale_at_least_base : q ≤ q ^ (last + 1) :=
        base_le_succ_power q last (by omega)
      have scale_at_least_base_rat :
          (q : ℚ) ≤ (q : ℚ) ^ (last + 1) := by
        exact_mod_cast scale_at_least_base
      have properTail_length_positive : 0 < properTail.length :=
        List.length_pos_of_ne_nil properTail_ne
      have properTail_cost_bound := fractionPredecessor_length_mul_base_sub_one_le_cost
        (q : ℚ) (by exact_mod_cast show 1 ≤ q by omega) properTail
      have properTail_cost_at_least_base_sub_one :
          (q : ℚ) - 1 ≤ fractionPredecessorCost q properTail := by
        have properTail_length_at_least_one_rat : (1 : ℚ) ≤ properTail.length := by
          exact_mod_cast properTail_length_positive
        have q_at_least_one_rat : (1 : ℚ) ≤ q := by
          exact_mod_cast show 1 ≤ q by omega
        nlinarith only [properTail_cost_bound, properTail_length_at_least_one_rat,
          q_at_least_one_rat]
      have inner_at_least_two_base_sub_one :
          (2 : ℚ) * q - 1 ≤
            (q : ℚ) ^ (head + 1) + fractionPredecessorCost q properTail := by
        linarith only [source_at_least_base_rat,
          properTail_cost_at_least_base_sub_one]
      have two_base_sub_one_nonnegative : (0 : ℚ) ≤ 2 * q - 1 := by
        have q_at_least_four_rat : (4 : ℚ) ≤ q := by
          exact_mod_cast q_at_least_four
        linarith
      have scale_nonnegative : (0 : ℚ) ≤ (q : ℚ) ^ (last + 1) := by positivity
      have weighted_lower :
          (q : ℚ) * (2 * q - 1) ≤
            (q : ℚ) ^ (last + 1) *
              ((q : ℚ) ^ (head + 1) + fractionPredecessorCost q properTail) := by
        calc
          (q : ℚ) * (2 * q - 1) ≤
              (q : ℚ) ^ (last + 1) * (2 * q - 1) :=
            mul_le_mul_of_nonneg_right scale_at_least_base_rat
              two_base_sub_one_nonnegative
          _ ≤ (q : ℚ) ^ (last + 1) *
                ((q : ℚ) ^ (head + 1) + fractionPredecessorCost q properTail) :=
            mul_le_mul_of_nonneg_left inner_at_least_two_base_sub_one scale_nonnegative
      have first_three_return_budget_lt :
          (2 : ℚ) * q ^ 2 < B + q := by
        nlinarith only [weighted_lower, terminal_budget]
      have first_three_return_budget_lt_nat : 2 * q ^ 2 < B + q := by
        exact_mod_cast first_three_return_budget_lt
      exact ((Nat.not_lt_of_ge within_terminal_three_return_floor)
        first_three_return_budget_lt_nat).elim
  · rintro ⟨head, rfl, B_eq⟩
    rw [positiveBridge_singleton, B_eq]
    have q_power_ne : ((q : ℚ) ^ (head + 1)) ≠ 0 := by positivity
    norm_num only [Nat.cast_pow]
    rw [neg_mul]
    rw [div_mul_cancel₀ 1 q_power_ne]
    ring

/-- In the shallow chamber, physical mortality is exactly a positive-power reciprocal
resonance. -/
theorem physical_isMortal_pureDenominator_shallow_iff
    (q B : Nat) (q_at_least_four : 4 ≤ q) (B_at_least_two : 1 < B)
    (within_terminal_three_return_floor : B + q ≤ 2 * q ^ 2) :
    IsMortal
        (ReturnFamily.pairGenerator (ambient (q : ℚ))
          (cut (-(1 / (B : ℚ))))) ↔
      ∃ head : Nat, B = q ^ (head + 1) := by
  have q_ne_int : (q : ℤ) ≠ 0 := by
    exact_mod_cast show q ≠ 0 by omega
  have B_ne_zero_rat : (B : ℚ) ≠ 0 := by positivity
  have parameter_ne_neg_one : -(1 / (B : ℚ)) + 1 ≠ 0 := by
    intro equality
    have reciprocal_one : (1 : ℚ) / B = 1 := by linarith only [equality]
    have B_eq_one_rat : (B : ℚ) = 1 :=
      ((div_eq_one_iff_eq B_ne_zero_rat).mp reciprocal_one).symm
    have B_eq_one : B = 1 := by exact_mod_cast B_eq_one_rat
    omega
  change
    IsMortal
        (ReturnFamily.pairGenerator (ambient (((q : ℤ) : ℚ)))
          (cut (-(1 / (B : ℚ))))) ↔ _
  rw [physical_isMortal_iff_positiveBridge
    (q : ℤ) (-(1 / (B : ℚ))) q_ne_int]
  constructor
  · rintro ⟨waits, bridge_zero⟩
    obtain ⟨head, _, denominator_eq⟩ :=
      (positiveBridge_pureDenominator_shallow_iff
        q B q_at_least_four B_at_least_two within_terminal_three_return_floor waits).mp
          bridge_zero
    exact ⟨head, denominator_eq⟩
  · rintro ⟨head, denominator_eq⟩
    refine ⟨[head], ?_⟩
    exact (positiveBridge_pureDenominator_shallow_iff
      q B q_at_least_four B_at_least_two within_terminal_three_return_floor [head]).mpr
        ⟨head, rfl, denominator_eq⟩

end MatrixMortality.ReturnSquare
