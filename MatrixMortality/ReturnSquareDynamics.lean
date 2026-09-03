import MatrixMortality.ReturnSquare

/-!
# ReturnSquareDynamics

This file owns the word-level projective dynamics of negative-parameter ReturnSquare families.
`ReturnSquare` supplies the exact return algebra; this layer lifts its one-step cone invariant to
arbitrary words and discharges the resulting immortality wall.
-/

namespace MatrixMortality.ReturnSquare

private theorem self_le_pow_succ (q : ℤ) (hq : 2 ≤ q) (n : Nat) :
    q ≤ q ^ (n + 1) := by
  rw [pow_succ]
  have one_le_power : 1 ≤ q ^ n := by
    have : 0 < q ^ n := pow_pos (by omega) n
    omega
  have q_nonneg : 0 ≤ q := by omega
  nlinarith [mul_le_mul_of_nonneg_right one_le_power q_nonneg]

/-- A word of negative-parameter positive returns cannot enter the signed trap unless its input
was already trapped. -/
theorem positiveTransferWord_preimage_signedTrap
    (q : ℤ) (d : ℚ) (waits : List Nat) (v : Fin 2 → ℚ)
    (q_at_least_two : 2 ≤ q)
    (beyond_wall : 1 + ((q : ℚ) - 1) / (q : ℚ) ^ 2 < d)
    (image_trapped :
      signedTrap (trapBound d (q : ℚ))
        (Matrix.mulVec
          (wordProduct (positiveTransfer (q : ℚ) (-d)) waits) v 0)
        (Matrix.mulVec
          (wordProduct (positiveTransfer (q : ℚ) (-d)) waits) v 1)) :
    signedTrap (trapBound d (q : ℚ)) (v 0) (v 1) := by
  induction waits with
  | nil =>
      simpa [wordProduct] using image_trapped
  | cons wait waits induction =>
      rw [wordProduct_cons] at image_trapped
      rw [← Matrix.mulVec_mulVec] at image_trapped
      apply induction
      apply transfer_neg_preimage_signedTrap_mulVec
        d (q : ℚ) ((q : ℚ) ^ (wait + 1)) _ (by exact_mod_cast q_at_least_two)
      · exact_mod_cast self_le_pow_succ q q_at_least_two wait
      · exact beyond_wall
      · exact image_trapped

/-- Any nonzero representative of the pulled-back target line lies in the signed trap. -/
theorem targetRay_signedTrap (d q t x y : ℚ)
    (q_at_least_two : 2 ≤ q) (scale_at_least_base : q ≤ t)
    (beyond_wall : 1 + (q - 1) / q ^ 2 < d)
    (representative_nonzero : (x, y) ≠ (0, 0))
    (target_line : y = d * t * x) :
    signedTrap (trapBound d q) x y := by
  obtain ⟨_, _, _, _, _, bound_dt_gt_one⟩ :=
    trapBound_spec d q t q_at_least_two scale_at_least_base beyond_wall
  have x_ne_zero : x ≠ 0 := by
    intro x_zero
    apply representative_nonzero
    simp [x_zero, target_line]
  have d_pos : 0 < d := by
    have ratio_nonneg : 0 ≤ (q - 1) / q ^ 2 :=
      div_nonneg (by linarith) (sq_nonneg q)
    nlinarith
  have t_pos : 0 < t := by linarith
  rcases lt_or_gt_of_ne x_ne_zero with x_neg | x_pos
  · right
    have y_neg : y < 0 := by
      rw [target_line]
      exact mul_neg_of_pos_of_neg (mul_pos d_pos t_pos) x_neg
    refine ⟨x_neg, y_neg, ?_⟩
    rw [target_line]
    have := mul_le_mul_of_nonpos_right bound_dt_gt_one.le x_neg.le
    nlinarith
  · left
    have y_pos : 0 < y := by
      rw [target_line]
      exact mul_pos (mul_pos d_pos t_pos) x_pos
    refine ⟨x_pos, y_pos, ?_⟩
    rw [target_line]
    have := mul_le_mul_of_nonneg_right bound_dt_gt_one.le x_pos.le
    nlinarith

/-- Beyond the uniform projective wall, every negative-parameter bridge is nonzero. -/
theorem positiveBridge_ne_zero_of_beyond_negative_wall
    (q : ℤ) (d : ℚ) (waits : List Nat) (hq : 2 ≤ q)
    (beyond_wall : 1 + ((q : ℚ) - 1) / (q : ℚ) ^ 2 < d) :
    positiveBridge (q : ℚ) (-d) waits ≠ 0 := by
  have d_gt_one : 1 < d := by
    have numerator_nonneg : (0 : ℚ) ≤ (q : ℚ) - 1 := by
      have : (1 : ℚ) ≤ (q : ℚ) := by
        exact_mod_cast (show (1 : ℤ) ≤ q by omega)
      linarith
    have ratio_nonneg : 0 ≤ ((q : ℚ) - 1) / (q : ℚ) ^ 2 :=
      div_nonneg numerator_nonneg (sq_nonneg (q : ℚ))
    linarith
  rcases waits with _ | ⟨wait, waits⟩
  · rw [positiveBridge_nil]
    nlinarith
  · rw [positiveBridge_cons]
    intro bridge_zero
    have prefix_ne : (-d + 1) * (q : ℚ) ^ (wait + 1) ≠ 0 :=
      mul_ne_zero (by nlinarith) (by positivity)
    have scalar_zero :
        dotProduct ![-d * (q : ℚ) ^ (wait + 1), 1]
            (Matrix.mulVec
              (wordProduct (positiveTransfer (q : ℚ) (-d)) waits) ![1, 1]) = 0 :=
      (mul_eq_zero.mp bridge_zero).resolve_left prefix_ne
    let residual :=
      Matrix.mulVec
        (wordProduct (positiveTransfer (q : ℚ) (-d)) waits) ![1, 1]
    have target_line :
        residual 1 = d * (q : ℚ) ^ (wait + 1) * residual 0 := by
      have identity :
          dotProduct ![-d * (q : ℚ) ^ (wait + 1), 1] residual = 0 := scalar_zero
      simp (config := { zeta := false }) [dotProduct, Fin.sum_univ_succ] at identity
      linarith
    have residual_ne_zero : residual ≠ 0 := by
      apply unit_mulVec_ne_zero
      · apply wordProduct_isUnit
        intro label
        exact positiveTransfer_isUnit q (-d) hq (by nlinarith) label
      · simp
    have pair_ne_zero : (residual 0, residual 1) ≠ (0, 0) := by
      intro pair_zero
      have first_zero : residual 0 = 0 := by
        simpa using congrArg Prod.fst pair_zero
      have second_zero : residual 1 = 0 := by
        simpa using congrArg Prod.snd pair_zero
      apply residual_ne_zero
      funext i
      fin_cases i
      · exact first_zero
      · exact second_zero
    have scale_at_least_base :
        (q : ℚ) ≤ (q : ℚ) ^ (wait + 1) := by
      exact_mod_cast self_le_pow_succ q hq wait
    have residual_trapped :
        signedTrap (trapBound d (q : ℚ)) (residual 0) (residual 1) :=
      targetRay_signedTrap d (q : ℚ) ((q : ℚ) ^ (wait + 1))
        (residual 0) (residual 1) (by exact_mod_cast hq) scale_at_least_base
        beyond_wall pair_ne_zero target_line
    have initial_trapped :
        signedTrap (trapBound d (q : ℚ)) (1 : ℚ) 1 := by
      simpa [residual] using
        positiveTransferWord_preimage_signedTrap q d waits ![1, 1] hq beyond_wall
          residual_trapped
    obtain ⟨_, bound_lt_one, _, _, _, _⟩ :=
      trapBound_spec d (q : ℚ) (q : ℚ) (by exact_mod_cast hq) le_rfl beyond_wall
    rcases initial_trapped with positive | negative
    · norm_num at positive
      linarith
    · norm_num at negative

/-- ReturnSquare is immortal throughout the negative half-line beyond the uniform wall. -/
theorem not_physical_isMortal_of_beyond_negative_wall
    (q : ℤ) (d : ℚ) (hq : 2 ≤ q)
    (beyond_wall : 1 + ((q : ℚ) - 1) / (q : ℚ) ^ 2 < d) :
    ¬IsMortal (ReturnFamily.pairGenerator (ambient (q : ℚ)) (cut (-d))) := by
  have d_gt_one : 1 < d := by
    have numerator_nonneg : (0 : ℚ) ≤ (q : ℚ) - 1 := by
      have : (1 : ℚ) ≤ (q : ℚ) := by
        exact_mod_cast (show (1 : ℤ) ≤ q by omega)
      linarith
    have ratio_nonneg : 0 ≤ ((q : ℚ) - 1) / (q : ℚ) ^ 2 :=
      div_nonneg numerator_nonneg (sq_nonneg (q : ℚ))
    linarith
  rw [physical_isMortal_iff_positiveBridge q (-d) (by omega)]
  rintro ⟨waits, bridge_zero⟩
  exact positiveBridge_ne_zero_of_beyond_negative_wall q d waits hq beyond_wall
    bridge_zero

end MatrixMortality.ReturnSquare
