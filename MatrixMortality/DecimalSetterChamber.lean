import MatrixMortality.DecimalSetterCarry
import MatrixMortality.Undecidability.NearyExecution
import Mathlib.Tactic

/-!
# Pole-free chambers for the decimal setter

This file combines decimal digit bounds with the negative J-fraction chart. It proves that the
two length-two `c`-erasure transfers cannot hit any admissible pole after an ordinary-reset
transfer. The rule/erasure branch uses the stronger prefix forced by compiler-emitted bodies.
-/

namespace MatrixMortality.DecimalSetterChamber

open MatrixMortality.DecimalSetterCarry
open MatrixMortality.Undecidability

/-- Coefficient converting a normalized lower spelling into its J-fraction weight. -/
def lowerScale (ρ : ℚ) : ℚ :=
  lift ρ / ((2 * ρ - 7) * (52 * ρ - 7))

/-- Upper coefficient `P/(μA)` of one decimal setter block. -/
def jUpper (ρ upper scale : ℚ) : ℚ :=
  (marker ρ + 10 * ρ * upper) / (marker ρ * scale)

/-- Lower coefficient `LV/(μA)` of one decimal setter block. -/
def jLower (ρ lower scale : ℚ) : ℚ :=
  lowerScale ρ * lower / scale

/-- Negative J-fraction transfer in the pole chamber coordinate. -/
def jStep (u v t : ℚ) : ℚ := u + v - v / t

/-- Pole of a negative J-fraction transfer. -/
def jPole (u v : ℚ) : ℚ := v / (u + v)

/-- Upper coefficient of the two-`c` deletion block. -/
def doubleDeletionUpper (ρ : ℚ) : ℚ := jUpper ρ 55 100

/-- Lower coefficient of the two-`c` deletion block. -/
def doubleDeletionLower (ρ : ℚ) : ℚ := jLower ρ 77 100

theorem nine_mul_code_add_seven_le_seven_mul_pow (word : List Bool) :
    9 * code word + 7 ≤ 7 * 10 ^ word.length := by
  induction word with
  | nil => norm_num
  | cons bit tail ih =>
      have digit_upper : digit bit ≤ 7 := by cases bit <;> norm_num [digit]
      rw [code_cons, List.length_cons, pow_succ]
      nlinarith [Nat.mul_le_mul_right (10 ^ tail.length) digit_upper]

theorem leadingOne_code_bounds (tail : List Bool) :
    5 * 10 ^ tail.length ≤ code (true :: tail) ∧
      90 * code (true :: tail) + 70 ≤ 52 * 10 ^ (true :: tail).length := by
  constructor
  · exact five_mul_pow_length_le_code true tail
  · have tail_bound := nine_mul_code_add_seven_le_seven_mul_pow tail
    rw [code_cons, digit_true, List.length_cons, pow_succ]
    omega

theorem lowerPrefix_code_bound_false (tail : List Bool) :
    11 * 10 ^ (false :: tail).length ≤ 20 * code (false :: tail) := by
  rw [code_cons, digit_false, List.length_cons, pow_succ]
  omega

theorem lowerPrefix_code_bound_true_true (tail : List Bool) :
    11 * 10 ^ (true :: true :: tail).length ≤
      20 * code (true :: true :: tail) := by
  rw [code_cons, digit_true, List.length_cons, pow_succ,
    code_cons, digit_true, List.length_cons, pow_succ]
  nlinarith [Nat.zero_le (code tail)]

theorem replicateFalse_code_identity (width : Nat) :
    9 * code (List.replicate width false) + 7 = 7 * 10 ^ width := by
  induction width with
  | zero => norm_num
  | succ width ih =>
      rw [List.replicate_succ, code_cons, digit_false, List.length_replicate,
        pow_succ]
      omega

/-- Binary marker `10^β`. -/
def markerWord (β : Nat) : List Bool := true :: List.replicate β false

/-- Neary's long tag for `b`, namely `10^β1`. -/
def bTag (β : Nat) : List Bool := markerWord β ++ [true]

theorem markerWord_code_identity (β : Nat) :
    9 * code (markerWord β) + 7 = 52 * 10 ^ β := by
  rw [markerWord, code_cons, digit_true, List.length_replicate]
  have zeros := replicateFalse_code_identity β
  omega

theorem bTag_code (β : Nat) : code (bTag β) = 10 * code (markerWord β) + 5 := by
  simp [bTag, code_append]
  ring

theorem leadingTrueTrue_code_bound (tail : List Bool) :
    9 * code (true :: true :: tail) + 7 ≤ 502 * 10 ^ tail.length := by
  have tail_bound := nine_mul_code_add_seven_le_seven_mul_pow tail
  simp only [code_cons, digit_true, List.length_cons, pow_succ]
  omega

/-- Lower decimal code divided by the upper decimal place scale. -/
def normalizedLower (upper lower : List Bool) : ℚ :=
  code lower / (10 : ℚ) ^ upper.length

theorem normalizedLower_pos {upper lower : List Bool} (lower_ne : lower ≠ []) :
    0 < normalizedLower upper lower := by
  unfold normalizedLower
  positivity [code_pos_of_ne_nil lower_ne]

theorem normalizedLower_lt_lowShell {upper lower : List Bool} {β : Nat}
    (length_low : lower.length ≤ upper.length + β) :
    normalizedLower upper lower < 7 / 9 * (10 : ℚ) ^ β := by
  have code_bound := nine_mul_code_add_seven_le_seven_mul_pow lower
  have code_lt_nat : 9 * code lower < 7 * 10 ^ lower.length := by omega
  have code_lt : (code lower : ℚ) < 7 / 9 * (10 : ℚ) ^ lower.length := by
    have cast_bound :
        (((9 * code lower : ℕ) : ℚ)) < ((7 * 10 ^ lower.length : ℕ) : ℚ) := by
      exact_mod_cast code_lt_nat
    norm_num at cast_bound
    nlinarith
  have power_le_nat : 10 ^ lower.length ≤ 10 ^ (upper.length + β) :=
    Nat.pow_le_pow_right (by norm_num) length_low
  have power_le : (10 : ℚ) ^ lower.length ≤
      (10 : ℚ) ^ upper.length * (10 : ℚ) ^ β := by
    have cast_bound : (10 : ℚ) ^ lower.length ≤
        (10 : ℚ) ^ (upper.length + β) := by exact_mod_cast power_le_nat
    simpa [pow_add] using cast_bound
  have scaled_power_le :
      7 / 9 * (10 : ℚ) ^ lower.length ≤
        7 / 9 * ((10 : ℚ) ^ upper.length * (10 : ℚ) ^ β) :=
    mul_le_mul_of_nonneg_left power_le (by norm_num)
  unfold normalizedLower
  rw [div_lt_iff₀ (by positivity : 0 < (10 : ℚ) ^ upper.length)]
  calc
    (code lower : ℚ) < 7 / 9 * (10 : ℚ) ^ lower.length := code_lt
    _ ≤ 7 / 9 * ((10 : ℚ) ^ upper.length * (10 : ℚ) ^ β) := scaled_power_le
    _ = 7 / 9 * (10 : ℚ) ^ β * (10 : ℚ) ^ upper.length := by ring

theorem normalizedLower_highShell_false {upper tail : List Bool} {β : Nat}
    (length_high : upper.length + β + 1 ≤ (false :: tail).length) :
    11 / 2 * (10 : ℚ) ^ β ≤ normalizedLower upper (false :: tail) := by
  have prefix_bound := lowerPrefix_code_bound_false tail
  have power_le_nat :
      10 ^ (upper.length + β + 1) ≤ 10 ^ (false :: tail).length :=
    Nat.pow_le_pow_right (by norm_num) length_high
  have prefix_bound_rat :
      11 / 20 * (10 : ℚ) ^ (false :: tail).length ≤ code (false :: tail) := by
    have cast_bound :
        ((11 * 10 ^ (false :: tail).length : ℕ) : ℚ) ≤
          ((20 * code (false :: tail) : ℕ) : ℚ) := by exact_mod_cast prefix_bound
    norm_num at cast_bound
    simp only [List.length_cons] at cast_bound ⊢
    nlinarith
  have power_le :
      (10 : ℚ) ^ (upper.length + β + 1) ≤
        (10 : ℚ) ^ (false :: tail).length := by exact_mod_cast power_le_nat
  unfold normalizedLower
  rw [le_div_iff₀ (by positivity : 0 < (10 : ℚ) ^ upper.length)]
  calc
    11 / 2 * (10 : ℚ) ^ β * (10 : ℚ) ^ upper.length =
        11 / 20 * (10 : ℚ) ^ (upper.length + β + 1) := by
          rw [pow_add, pow_succ]
          ring
    _ ≤ 11 / 20 * (10 : ℚ) ^ (false :: tail).length :=
      mul_le_mul_of_nonneg_left power_le (by norm_num)
    _ ≤ code (false :: tail) := prefix_bound_rat

theorem normalizedLower_highShell_true_true {upper tail : List Bool} {β : Nat}
    (length_high : upper.length + β + 1 ≤ (true :: true :: tail).length) :
    11 / 2 * (10 : ℚ) ^ β ≤ normalizedLower upper (true :: true :: tail) := by
  have prefix_bound := lowerPrefix_code_bound_true_true tail
  have power_le_nat :
      10 ^ (upper.length + β + 1) ≤ 10 ^ (true :: true :: tail).length :=
    Nat.pow_le_pow_right (by norm_num) length_high
  have prefix_bound_rat :
      11 / 20 * (10 : ℚ) ^ (true :: true :: tail).length ≤
        code (true :: true :: tail) := by
    have cast_bound :
        ((11 * 10 ^ (true :: true :: tail).length : ℕ) : ℚ) ≤
          ((20 * code (true :: true :: tail) : ℕ) : ℚ) := by
      exact_mod_cast prefix_bound
    norm_num at cast_bound
    simp only [List.length_cons] at cast_bound ⊢
    nlinarith
  have power_le :
      (10 : ℚ) ^ (upper.length + β + 1) ≤
        (10 : ℚ) ^ (true :: true :: tail).length := by exact_mod_cast power_le_nat
  unfold normalizedLower
  rw [le_div_iff₀ (by positivity : 0 < (10 : ℚ) ^ upper.length)]
  calc
    11 / 2 * (10 : ℚ) ^ β * (10 : ℚ) ^ upper.length =
        11 / 20 * (10 : ℚ) ^ (upper.length + β + 1) := by
          rw [pow_add, pow_succ]
          ring
    _ ≤ 11 / 20 * (10 : ℚ) ^ (true :: true :: tail).length :=
      mul_le_mul_of_nonneg_left power_le (by norm_num)
    _ ≤ code (true :: true :: tail) := prefix_bound_rat

theorem normalizedLower_huge_true_true {tail : List Bool} {β : Nat}
    (length_huge : 2 * β + 4 ≤ (true :: true :: tail).length) :
    55 * ((10 : ℚ) ^ β) ^ 2 ≤
      normalizedLower [true, true] (true :: true :: tail) := by
  have shell := normalizedLower_highShell_true_true
    (upper := [true, true]) (β := 2 * β + 1) (tail := tail) (by
      simp only [List.length_cons, List.length_nil] at length_huge ⊢
      omega)
  calc
    55 * ((10 : ℚ) ^ β) ^ 2 = 11 / 2 * (10 : ℚ) ^ (2 * β + 1) := by
      rw [show 2 * β + 1 = β + β + 1 by omega, pow_succ, pow_add]
      ring
    _ ≤ normalizedLower [true, true] (true :: true :: tail) := shell

private theorem denominator_bounds {ρ : ℚ} (rho_bound : 1000 ≤ ρ) :
    0 < marker ρ ∧ 0 < 2 * ρ - 7 ∧ 0 < 52 * ρ - 7 ∧ 0 < lift ρ := by
  simp [marker, lift]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem jUpper_in_window {ρ upper scale : ℚ}
    (rho_bound : 1000 ≤ ρ) (scale_pos : 0 < scale)
    (upper_lower : scale / 2 ≤ upper)
    (upper_upper : 90 * upper + 70 ≤ 52 * scale) :
    4 / 5 < jUpper ρ upper scale ∧ jUpper ρ upper scale < 101 / 100 := by
  obtain ⟨marker_pos, _, _, _⟩ := denominator_bounds rho_bound
  have rho_pos : 0 < ρ := lt_of_lt_of_le (by norm_num) rho_bound
  have denominator_pos : 0 < marker ρ * scale := mul_pos marker_pos scale_pos
  have scaled_lower : 0 ≤ ρ * (2 * upper - scale) := by
    apply mul_nonneg rho_pos.le
    linarith
  have scaled_upper : 0 ≤ ρ * (52 * scale - 90 * upper - 70) := by
    apply mul_nonneg rho_pos.le
    linarith
  constructor
  · unfold jUpper
    rw [lt_div_iff₀ denominator_pos]
    simp [marker]
    nlinarith
  · unfold jUpper
    rw [div_lt_iff₀ denominator_pos]
    simp [marker]
    nlinarith

private theorem thousand_le_ten_pow {β : Nat} (beta_large : 3 ≤ β) :
    (1000 : ℚ) ≤ 10 ^ β := by
  have natural_bound : 10 ^ 3 ≤ 10 ^ β :=
    Nat.pow_le_pow_right (by norm_num) beta_large
  norm_num at natural_bound ⊢
  exact_mod_cast natural_bound

theorem encodedJUpper_in_window {ρ : ℚ} (tail : List Bool) (rho_bound : 1000 ≤ ρ) :
    4 / 5 < jUpper ρ (code (true :: tail)) (10 ^ (true :: tail).length) ∧
      jUpper ρ (code (true :: tail)) (10 ^ (true :: tail).length) < 101 / 100 := by
  obtain ⟨lower_bound, upper_bound⟩ := leadingOne_code_bounds tail
  have scale_pos : 0 < ((10 : ℚ) ^ (true :: tail).length) := by positivity
  apply jUpper_in_window rho_bound scale_pos
  · calc
      (10 : ℚ) ^ (true :: tail).length / 2 =
          ((5 * 10 ^ tail.length : ℕ) : ℚ) := by
            norm_num [List.length_cons, pow_succ]
            ring
      _ ≤ code (true :: tail) := by exact_mod_cast lower_bound
  · exact_mod_cast upper_bound

theorem markerWord_code_eq_marker (β : Nat) :
    (code (markerWord β) : ℚ) = marker ((10 : ℚ) ^ β) := by
  have identity := markerWord_code_identity β
  have cast_identity :
      ((9 * code (markerWord β) + 7 : ℕ) : ℚ) =
        ((52 * 10 ^ β : ℕ) : ℚ) := by exact_mod_cast identity
  norm_num at cast_identity
  simp [marker]
  linarith

theorem bLeading_jUpper_lower {β : Nat} (tail : List Bool) (beta_large : 3 ≤ β) :
    1 + 1 / (2 * marker ((10 : ℚ) ^ β)) <
      jUpper ((10 : ℚ) ^ β) (code (bTag β ++ tail))
        (10 ^ (bTag β ++ tail).length) := by
  let ρ : ℚ := 10 ^ β
  have rho_bound : 1000 ≤ ρ := thousand_le_ten_pow beta_large
  obtain ⟨marker_pos, _, _, _⟩ := denominator_bounds rho_bound
  have rho_pos : 0 < ρ := lt_of_lt_of_le (by norm_num) rho_bound
  have tail_scale_pos : 0 < (10 : ℚ) ^ tail.length := by positivity
  have tag_code : (code (bTag β) : ℚ) = 10 * marker ρ + 5 := by
    rw [bTag_code]
    norm_num
    rw [markerWord_code_eq_marker]
  have upper_code :
      (code (bTag β ++ tail) : ℚ) =
        (10 * marker ρ + 5) * (10 : ℚ) ^ tail.length + code tail := by
    rw [code_append]
    norm_num
    rw [tag_code]
  have scale_eq :
      (10 : ℚ) ^ (bTag β ++ tail).length =
        100 * ρ * (10 : ℚ) ^ tail.length := by
    simp [bTag, markerWord, ρ, pow_add, pow_succ]
    ring
  have difference :
      jUpper ρ (code (bTag β ++ tail)) (10 ^ (bTag β ++ tail).length) -
          (1 + 1 / (2 * marker ρ)) =
        (marker ρ + 10 * ρ * code tail) /
          (100 * ρ * marker ρ * (10 : ℚ) ^ tail.length) := by
    unfold jUpper
    rw [upper_code, scale_eq]
    field_simp [ne_of_gt marker_pos, ne_of_gt rho_pos, ne_of_gt tail_scale_pos]
    ring
  rw [← sub_pos, difference]
  positivity

theorem cLeadingMulti_jUpper_upper {β : Nat} (tail : List Bool)
    (beta_large : 3 ≤ β) :
    jUpper ((10 : ℚ) ^ β) (code (true :: true :: tail))
        (10 ^ (true :: true :: tail).length) < 97 / 100 := by
  let ρ : ℚ := 10 ^ β
  have rho_bound : 1000 ≤ ρ := thousand_le_ten_pow beta_large
  obtain ⟨marker_pos, _, _, _⟩ := denominator_bounds rho_bound
  have rho_pos : 0 < ρ := lt_of_lt_of_le (by norm_num) rho_bound
  have tail_scale_pos : 0 < (10 : ℚ) ^ tail.length := by positivity
  have code_bound_nat := leadingTrueTrue_code_bound tail
  have code_bound :
      (9 : ℚ) * code (true :: true :: tail) + 7 ≤
        502 * (10 : ℚ) ^ tail.length := by exact_mod_cast code_bound_nat
  have scaled_code_bound :
      0 ≤ ρ * (502 * (10 : ℚ) ^ tail.length -
        9 * code (true :: true :: tail) - 7) :=
    mul_nonneg rho_pos.le (by linarith)
  have scale_eq :
      (10 : ℚ) ^ (true :: true :: tail).length =
        100 * (10 : ℚ) ^ tail.length := by
    simp [pow_succ]
    ring
  unfold jUpper
  rw [scale_eq, div_lt_iff₀ (mul_pos marker_pos (mul_pos (by norm_num) tail_scale_pos))]
  simp [marker, ρ]
  nlinarith

theorem lowNormalizedLower_lt_four {ρ normalized : ℚ}
    (rho_bound : 1000 ≤ ρ) (normalized_upper : normalized < 7 / 9 * ρ) :
    jLower ρ normalized 1 < 4 := by
  obtain ⟨_, two_pos, fiftyTwo_pos, lift_pos⟩ := denominator_bounds rho_bound
  have denominator_pos : 0 < (2 * ρ - 7) * (52 * ρ - 7) :=
    mul_pos two_pos fiftyTwo_pos
  unfold jLower lowerScale lift
  simp only [div_one]
  rw [div_mul_eq_mul_div, div_lt_iff₀ denominator_pos]
  nlinarith [mul_pos (sub_pos.mpr normalized_upper) lift_pos]

theorem highNormalizedLower_gt {ρ normalized : ℚ}
    (rho_bound : 1000 ≤ ρ) (normalized_lower : 11 / 2 * ρ ≤ normalized) :
    53 / 2 < jLower ρ normalized 1 := by
  obtain ⟨_, two_pos, fiftyTwo_pos, lift_pos⟩ := denominator_bounds rho_bound
  have denominator_pos : 0 < (2 * ρ - 7) * (52 * ρ - 7) :=
    mul_pos two_pos fiftyTwo_pos
  unfold jLower lowerScale lift
  simp only [div_one]
  rw [div_mul_eq_mul_div, lt_div_iff₀ denominator_pos]
  have rho_pos : 0 < ρ := lt_of_lt_of_le (by norm_num) rho_bound
  have lifted_difference : 0 ≤ lift ρ * (normalized - 11 / 2 * ρ) := by
    exact mul_nonneg lift_pos.le (sub_nonneg.mpr normalized_lower)
  nlinarith [sq_nonneg (ρ - 1000)]

theorem hugeNormalizedLower_gt {ρ normalized : ℚ}
    (rho_bound : 1000 ≤ ρ) (normalized_lower : 55 * ρ ^ 2 ≤ normalized) :
    265 * ρ < jLower ρ normalized 1 := by
  obtain ⟨_, two_pos, fiftyTwo_pos, lift_pos⟩ := denominator_bounds rho_bound
  have rho_pos : 0 < ρ := lt_of_lt_of_le (by norm_num) rho_bound
  have denominator_pos : 0 < (2 * ρ - 7) * (52 * ρ - 7) :=
    mul_pos two_pos fiftyTwo_pos
  have expanded_denominator_pos : 0 < 49 - 378 * ρ + 104 * ρ ^ 2 := by
    calc
      49 - 378 * ρ + 104 * ρ ^ 2 = (2 * ρ - 7) * (52 * ρ - 7) := by ring
      _ > 0 := denominator_pos
  have scale_pos : 0 < lowerScale ρ := by
    unfold lowerScale
    positivity
  have baseline_difference :
      jLower ρ (55 * ρ ^ 2) 1 - 265 * ρ =
        5 * ρ * (10 * ρ ^ 2 + 19957 * ρ - 2597) /
          ((2 * ρ - 7) * (52 * ρ - 7)) := by
    unfold jLower lowerScale lift
    simp only [div_one]
    field_simp [ne_of_gt two_pos, ne_of_gt fiftyTwo_pos,
      show -7 + ρ * 2 ≠ 0 by linarith]
    ring_nf
    field_simp [show -7 + ρ * 2 ≠ 0 by linarith,
      ne_of_gt expanded_denominator_pos,
      show 49 - ρ * 378 + ρ ^ 2 * 104 ≠ 0 by
        have : 49 - ρ * 378 + ρ ^ 2 * 104 =
            49 - 378 * ρ + 104 * ρ ^ 2 := by ring
        rw [this]
        exact ne_of_gt expanded_denominator_pos]
    ring
  have polynomial_pos : 0 < 10 * ρ ^ 2 + 19957 * ρ - 2597 := by
    nlinarith [sq_nonneg (ρ - 1000)]
  have baseline_pos : 0 < jLower ρ (55 * ρ ^ 2) 1 - 265 * ρ := by
    rw [baseline_difference]
    positivity
  have monotone : jLower ρ (55 * ρ ^ 2) 1 ≤ jLower ρ normalized 1 := by
    unfold jLower
    simp only [div_one]
    exact mul_le_mul_of_nonneg_left normalized_lower scale_pos.le
  linarith

theorem jLower_pos {ρ normalized : ℚ}
    (rho_bound : 1000 ≤ ρ) (normalized_pos : 0 < normalized) :
    0 < jLower ρ normalized 1 := by
  obtain ⟨_, two_pos, fiftyTwo_pos, lift_pos⟩ := denominator_bounds rho_bound
  unfold jLower lowerScale
  simp only [div_one]
  positivity

theorem ruleDeletionLower_gt {β : Nat} (tail : List Bool) (beta_large : 3 ≤ β)
    (length_huge : 2 * β + 4 ≤ (true :: true :: tail).length) :
    265 * (10 : ℚ) ^ β <
      jLower ((10 : ℚ) ^ β)
        (normalizedLower [true, true] (true :: true :: tail)) 1 :=
  hugeNormalizedLower_gt (thousand_le_ten_pow beta_large)
    (normalizedLower_huge_true_true length_huge)

theorem jStep_strictMono {u v s t : ℚ}
    (v_pos : 0 < v) (s_pos : 0 < s) (s_lt_t : s < t) :
    jStep u v s < jStep u v t := by
  have t_pos : 0 < t := s_pos.trans s_lt_t
  have quotient_lt : v / t < v / s := by
    rw [div_lt_div_iff₀ t_pos s_pos]
    nlinarith
  simp only [jStep]
  linarith

theorem jStep_negative_of_hugeLower {ρ u v t : ℚ}
    (rho_bound : 1000 ≤ ρ) (u_upper : u < 101 / 100)
    (v_lower : 265 * ρ < v) (t_pos : 0 < t) (t_upper : t < 97 / 100) :
    jStep u v t < 0 := by
  have rho_pos : 0 < ρ := lt_of_lt_of_le (by norm_num) rho_bound
  unfold jStep
  rw [sub_lt_zero, lt_div_iff₀ t_pos]
  nlinarith [mul_pos (sub_pos.mpr t_upper) (sub_pos.mpr v_lower)]

theorem jStep_above_one_of_hugeLower {ρ u v t : ℚ}
    (rho_bound : 1000 ≤ ρ)
    (u_lower : 4 / 5 < u) (v_lower : 265 * ρ < v)
    (t_lower : 1 + 1 / (2 * marker ρ) < t) (t_upper : t < 101 / 100) :
    1 < jStep u v t := by
  obtain ⟨marker_pos, _, _, _⟩ := denominator_bounds rho_bound
  have rho_pos : 0 < ρ := lt_of_lt_of_le (by norm_num) rho_bound
  have marker_upper : marker ρ < 6 * ρ := by
    simp [marker]
    linarith
  have t_pos : 0 < t := by
    have reciprocal_pos : 0 < 1 / (2 * marker ρ) := by positivity
    linarith
  have epsilon_pos : 0 < t - 1 := by
    have reciprocal_pos : 0 < 1 / (2 * marker ρ) := by positivity
    linarith
  have reciprocal_lower : 1 / (12 * ρ) < 1 / (2 * marker ρ) := by
    rw [div_lt_div_iff₀ (by positivity : 0 < 12 * ρ)
      (by positivity : 0 < 2 * marker ρ)]
    nlinarith
  have epsilon_lower : 1 / (12 * ρ) < t - 1 := by linarith
  have first_product :
      265 * ρ * (1 / (12 * ρ)) < 265 * ρ * (t - 1) :=
    mul_lt_mul_of_pos_left epsilon_lower (mul_pos (by norm_num) rho_pos)
  have second_product : 265 * ρ * (t - 1) < v * (t - 1) :=
    mul_lt_mul_of_pos_right v_lower epsilon_pos
  have product_lower : 265 / 12 < v * (t - 1) := by
    have cancel : 265 * ρ * (1 / (12 * ρ)) = 265 / 12 := by
      field_simp [ne_of_gt rho_pos]
    rw [cancel] at first_product
    exact first_product.trans second_product
  have scaled : t < (u + v) * t - v := by
    nlinarith [mul_pos (sub_pos.mpr t_upper) (sub_pos.mpr u_lower)]
  unfold jStep
  rw [show u + v - v / t = ((u + v) * t - v) / t by
    field_simp [ne_of_gt t_pos]]
  exact (lt_div_iff₀ t_pos).2 (by simpa using scaled)

private theorem doubleDeletionLower_pos {ρ : ℚ} (rho_bound : 1000 ≤ ρ) :
    0 < doubleDeletionLower ρ := by
  obtain ⟨_, two_pos, fiftyTwo_pos, lift_pos⟩ := denominator_bounds rho_bound
  simp [doubleDeletionLower, jLower, lowerScale]
  positivity

private theorem lower_endpoint {ρ : ℚ} (rho_bound : 1000 ≤ ρ) :
    961 / 1000 < jStep (doubleDeletionUpper ρ) (doubleDeletionLower ρ) (4 / 5) := by
  obtain ⟨marker_pos, two_pos, fiftyTwo_pos, lift_pos⟩ := denominator_bounds rho_bound
  have denominator_pos : 0 < (2 * ρ - 7) * (52 * ρ - 7) := mul_pos two_pos fiftyTwo_pos
  have difference :
      jStep (doubleDeletionUpper ρ) (doubleDeletionLower ρ) (4 / 5) - 961 / 1000 =
        (192 * ρ ^ 2 - 167314 * ρ - 90503) /
          (2000 * (2 * ρ - 7) * (52 * ρ - 7)) := by
    unfold jStep doubleDeletionUpper doubleDeletionLower jUpper jLower lowerScale marker lift
    field_simp [ne_of_gt marker_pos, ne_of_gt two_pos, ne_of_gt fiftyTwo_pos,
      show -7 + ρ * 2 ≠ 0 by linarith]
    ring_nf
    field_simp [show -7 + ρ * 2 ≠ 0 by linarith]
    ring
  rw [← sub_pos, difference]
  apply div_pos
  · nlinarith [sq_nonneg (ρ - 1000)]
  · positivity

private theorem upper_endpoint {ρ : ℚ} (rho_bound : 1000 ≤ ρ) :
    jStep (doubleDeletionUpper ρ) (doubleDeletionLower ρ) (101 / 100) < 963 / 1000 := by
  obtain ⟨marker_pos, two_pos, fiftyTwo_pos, lift_pos⟩ := denominator_bounds rho_bound
  have denominator_pos : 0 < (2 * ρ - 7) * (52 * ρ - 7) := mul_pos two_pos fiftyTwo_pos
  have difference :
      963 / 1000 -
          jStep (doubleDeletionUpper ρ) (doubleDeletionLower ρ) (101 / 100) =
        7 * (1616 * ρ ^ 2 - 253382 * ρ + 674541) /
          (101000 * (2 * ρ - 7) * (52 * ρ - 7)) := by
    unfold jStep doubleDeletionUpper doubleDeletionLower jUpper jLower lowerScale marker lift
    field_simp [ne_of_gt marker_pos, ne_of_gt two_pos, ne_of_gt fiftyTwo_pos,
      show -7 + ρ * 2 ≠ 0 by linarith]
    ring_nf
    field_simp [show -7 + ρ * 2 ≠ 0 by linarith]
    ring
  rw [← sub_pos, difference]
  apply div_pos
  · have polynomial_pos : 0 < 1616 * ρ ^ 2 - 253382 * ρ + 674541 := by
      nlinarith [sq_nonneg (ρ - 1000)]
    positivity
  · positivity

theorem doubleDeletion_step_in_gap {ρ t : ℚ}
    (rho_bound : 1000 ≤ ρ) (t_lower : 4 / 5 < t) (t_upper : t < 101 / 100) :
    961 / 1000 < jStep (doubleDeletionUpper ρ) (doubleDeletionLower ρ) t ∧
      jStep (doubleDeletionUpper ρ) (doubleDeletionLower ρ) t < 963 / 1000 := by
  have v_pos := doubleDeletionLower_pos rho_bound
  have t_pos : 0 < t := lt_trans (by norm_num) t_lower
  constructor
  · exact (lower_endpoint rho_bound).trans
      (jStep_strictMono v_pos (by norm_num) t_lower)
  · exact (jStep_strictMono v_pos t_pos t_upper).trans
      (upper_endpoint rho_bound)

theorem lowShell_pole_below {u v : ℚ}
    (u_lower : 4 / 5 < u) (v_pos : 0 < v) (v_upper : v < 4) :
    jPole u v < 9 / 10 := by
  have sum_pos : 0 < u + v := add_pos (lt_trans (by norm_num) u_lower) v_pos
  unfold jPole
  rw [div_lt_iff₀ sum_pos]
  nlinarith

theorem highShell_pole_above {u v : ℚ}
    (u_pos : 0 < u) (u_upper : u < 101 / 100) (v_lower : 53 / 2 < v) :
    963 / 1000 < jPole u v := by
  have v_pos : 0 < v := lt_trans (by norm_num) v_lower
  have sum_pos : 0 < u + v := add_pos u_pos v_pos
  unfold jPole
  rw [lt_div_iff₀ sum_pos]
  nlinarith

theorem jPole_mem_unit {u v : ℚ} (u_pos : 0 < u) (v_pos : 0 < v) :
    0 < jPole u v ∧ jPole u v < 1 := by
  have sum_pos : 0 < u + v := add_pos u_pos v_pos
  unfold jPole
  constructor
  · positivity
  · rw [div_lt_one sum_pos]
    linarith

theorem encodedShellPole_outside_gap {ρ normalized : ℚ}
    (tail : List Bool) (rho_bound : 1000 ≤ ρ) (normalized_pos : 0 < normalized)
    (length_shell : normalized < 7 / 9 * ρ ∨ 11 / 2 * ρ ≤ normalized) :
    jPole
        (jUpper ρ (code (true :: tail)) (10 ^ (true :: tail).length))
        (jLower ρ normalized 1) < 9 / 10 ∨
      963 / 1000 <
        jPole
          (jUpper ρ (code (true :: tail)) (10 ^ (true :: tail).length))
          (jLower ρ normalized 1) := by
  obtain ⟨upper_lower, upper_upper⟩ := encodedJUpper_in_window tail rho_bound
  have upper_pos :
      0 < jUpper ρ (code (true :: tail)) (10 ^ (true :: tail).length) :=
    lt_trans (by norm_num) upper_lower
  have lower_pos := jLower_pos rho_bound normalized_pos
  rcases length_shell with low | high
  · exact Or.inl <| lowShell_pole_below upper_lower lower_pos
      (lowNormalizedLower_lt_four rho_bound low)
  · exact Or.inr <| highShell_pole_above upper_pos upper_upper
      (highNormalizedLower_gt rho_bound high)

theorem encodedTargetPole_false_outside_gap {β : Nat}
    (upperTail lowerTail : List Bool) (beta_large : 3 ≤ β) :
    jPole
        (jUpper (10 ^ β) (code (true :: upperTail)) (10 ^ (true :: upperTail).length))
        (jLower (10 ^ β) (normalizedLower (true :: upperTail) (false :: lowerTail)) 1) <
        9 / 10 ∨
      963 / 1000 <
        jPole
          (jUpper (10 ^ β) (code (true :: upperTail)) (10 ^ (true :: upperTail).length))
          (jLower (10 ^ β) (normalizedLower (true :: upperTail) (false :: lowerTail)) 1) := by
  have rho_bound := thousand_le_ten_pow beta_large
  apply encodedShellPole_outside_gap upperTail rho_bound
    (normalizedLower_pos (by simp))
  by_cases low : (false :: lowerTail).length ≤ (true :: upperTail).length + β
  · exact Or.inl (normalizedLower_lt_lowShell low)
  · exact Or.inr (normalizedLower_highShell_false (by omega))

theorem encodedTargetPole_true_true_outside_gap {β : Nat}
    (upperTail lowerTail : List Bool) (beta_large : 3 ≤ β) :
    jPole
        (jUpper (10 ^ β) (code (true :: upperTail)) (10 ^ (true :: upperTail).length))
        (jLower (10 ^ β)
          (normalizedLower (true :: upperTail) (true :: true :: lowerTail)) 1) <
        9 / 10 ∨
      963 / 1000 <
        jPole
          (jUpper (10 ^ β) (code (true :: upperTail)) (10 ^ (true :: upperTail).length))
          (jLower (10 ^ β)
            (normalizedLower (true :: upperTail) (true :: true :: lowerTail)) 1) := by
  have rho_bound := thousand_le_ten_pow beta_large
  apply encodedShellPole_outside_gap upperTail rho_bound
    (normalizedLower_pos (by simp))
  by_cases low : (true :: true :: lowerTail).length ≤ (true :: upperTail).length + β
  · exact Or.inl (normalizedLower_lt_lowShell low)
  · exact Or.inr (normalizedLower_highShell_true_true (by omega))

theorem doubleDeletion_step_ne_pole {ρ t u v : ℚ}
    (rho_bound : 1000 ≤ ρ) (t_lower : 4 / 5 < t) (t_upper : t < 101 / 100)
    (pole_low : jPole u v < 9 / 10 ∨ 963 / 1000 < jPole u v) :
    jStep (doubleDeletionUpper ρ) (doubleDeletionLower ρ) t ≠ jPole u v := by
  obtain ⟨step_lower, step_upper⟩ :=
    doubleDeletion_step_in_gap rho_bound t_lower t_upper
  rcases pole_low with pole_low | pole_high
  · linarith
  · linarith

theorem doubleDeletion_avoids_encodedShellPole {ρ normalized : ℚ}
    (sourceTail targetTail : List Bool) (rho_bound : 1000 ≤ ρ)
    (normalized_pos : 0 < normalized)
    (length_shell : normalized < 7 / 9 * ρ ∨ 11 / 2 * ρ ≤ normalized) :
    jStep (doubleDeletionUpper ρ) (doubleDeletionLower ρ)
        (jUpper ρ (code (true :: sourceTail)) (10 ^ (true :: sourceTail).length)) ≠
      jPole
        (jUpper ρ (code (true :: targetTail)) (10 ^ (true :: targetTail).length))
        (jLower ρ normalized 1) := by
  obtain ⟨source_lower, source_upper⟩ :=
    encodedJUpper_in_window sourceTail rho_bound
  apply doubleDeletion_step_ne_pole rho_bound source_lower source_upper
  exact encodedShellPole_outside_gap targetTail rho_bound normalized_pos length_shell

theorem doubleDeletion_avoids_falsePrefixPole {β : Nat}
    (sourceTail targetUpperTail targetLowerTail : List Bool) (beta_large : 3 ≤ β) :
    jStep (doubleDeletionUpper (10 ^ β)) (doubleDeletionLower (10 ^ β))
        (jUpper (10 ^ β) (code (true :: sourceTail)) (10 ^ (true :: sourceTail).length)) ≠
      jPole
        (jUpper (10 ^ β) (code (true :: targetUpperTail))
          (10 ^ (true :: targetUpperTail).length))
        (jLower (10 ^ β)
          (normalizedLower (true :: targetUpperTail) (false :: targetLowerTail)) 1) := by
  obtain ⟨source_lower, source_upper⟩ :=
    encodedJUpper_in_window sourceTail (thousand_le_ten_pow beta_large)
  apply doubleDeletion_step_ne_pole (thousand_le_ten_pow beta_large)
    source_lower source_upper
  exact encodedTargetPole_false_outside_gap targetUpperTail targetLowerTail beta_large

theorem doubleDeletion_avoids_trueTruePrefixPole {β : Nat}
    (sourceTail targetUpperTail targetLowerTail : List Bool) (beta_large : 3 ≤ β) :
    jStep (doubleDeletionUpper (10 ^ β)) (doubleDeletionLower (10 ^ β))
        (jUpper (10 ^ β) (code (true :: sourceTail)) (10 ^ (true :: sourceTail).length)) ≠
      jPole
        (jUpper (10 ^ β) (code (true :: targetUpperTail))
          (10 ^ (true :: targetUpperTail).length))
        (jLower (10 ^ β)
          (normalizedLower (true :: targetUpperTail) (true :: true :: targetLowerTail)) 1) := by
  obtain ⟨source_lower, source_upper⟩ :=
    encodedJUpper_in_window sourceTail (thousand_le_ten_pow beta_large)
  apply doubleDeletion_step_ne_pole (thousand_le_ten_pow beta_large)
    source_lower source_upper
  exact encodedTargetPole_true_true_outside_gap targetUpperTail targetLowerTail beta_large

private theorem doubleDeletionUpper_eq_encoded (ρ : ℚ) :
    doubleDeletionUpper ρ = jUpper ρ (code [true, true]) (10 ^ [true, true].length) := by
  norm_num [doubleDeletionUpper, code, digit, Nat.ofDigits]

theorem ruleDeletion_cLeading_step_outside {β : Nat}
    (sourceTail middleLowerTail : List Bool) (beta_large : 3 ≤ β)
    (middle_length : 2 * β + 4 ≤ (true :: true :: middleLowerTail).length) :
    jStep (doubleDeletionUpper ((10 : ℚ) ^ β))
        (jLower ((10 : ℚ) ^ β)
          (normalizedLower [true, true] (true :: true :: middleLowerTail)) 1)
        (jUpper ((10 : ℚ) ^ β) (code (true :: true :: sourceTail))
          (10 ^ (true :: true :: sourceTail).length)) < 0 := by
  let ρ : ℚ := 10 ^ β
  have rho_bound := thousand_le_ten_pow beta_large
  have middle_upper_window := encodedJUpper_in_window (ρ := ρ) [true] rho_bound
  have middle_upper : doubleDeletionUpper ρ < 101 / 100 := by
    rw [doubleDeletionUpper_eq_encoded]
    exact middle_upper_window.2
  have middle_lower :
      265 * ρ <
        jLower ρ (normalizedLower [true, true] (true :: true :: middleLowerTail)) 1 :=
    ruleDeletionLower_gt middleLowerTail beta_large middle_length
  have source_pos :
      0 < jUpper ρ (code (true :: true :: sourceTail))
        (10 ^ (true :: true :: sourceTail).length) := by
    have window := encodedJUpper_in_window (ρ := ρ) (true :: sourceTail) rho_bound
    linarith [window.1]
  have source_upper :
      jUpper ρ (code (true :: true :: sourceTail))
          (10 ^ (true :: true :: sourceTail).length) < 97 / 100 :=
    cLeadingMulti_jUpper_upper sourceTail beta_large
  exact jStep_negative_of_hugeLower rho_bound middle_upper middle_lower
    source_pos source_upper

theorem ruleDeletion_bLeading_step_outside {β : Nat}
    (sourceTail middleLowerTail : List Bool) (beta_large : 3 ≤ β)
    (middle_length : 2 * β + 4 ≤ (true :: true :: middleLowerTail).length) :
    1 < jStep (doubleDeletionUpper ((10 : ℚ) ^ β))
        (jLower ((10 : ℚ) ^ β)
          (normalizedLower [true, true] (true :: true :: middleLowerTail)) 1)
        (jUpper ((10 : ℚ) ^ β) (code (bTag β ++ sourceTail))
          (10 ^ (bTag β ++ sourceTail).length)) := by
  let ρ : ℚ := 10 ^ β
  have rho_bound := thousand_le_ten_pow beta_large
  have middle_upper_window := encodedJUpper_in_window (ρ := ρ) [true] rho_bound
  have middle_lower_bound : 4 / 5 < doubleDeletionUpper ρ := by
    rw [doubleDeletionUpper_eq_encoded]
    exact middle_upper_window.1
  have middle_lower :
      265 * ρ <
        jLower ρ (normalizedLower [true, true] (true :: true :: middleLowerTail)) 1 :=
    ruleDeletionLower_gt middleLowerTail beta_large middle_length
  have source_lower :
      1 + 1 / (2 * marker ρ) <
        jUpper ρ (code (bTag β ++ sourceTail))
          (10 ^ (bTag β ++ sourceTail).length) :=
    bLeading_jUpper_lower sourceTail beta_large
  let sourceRest := List.replicate β false ++ true :: sourceTail
  have source_window := encodedJUpper_in_window (ρ := ρ) sourceRest rho_bound
  have source_upper :
      jUpper ρ (code (bTag β ++ sourceTail))
          (10 ^ (bTag β ++ sourceTail).length) < 101 / 100 := by
    simpa [bTag, markerWord, sourceRest, List.append_assoc] using source_window.2
  exact jStep_above_one_of_hugeLower rho_bound middle_lower_bound middle_lower
    source_lower source_upper

theorem ruleDeletion_cLeading_avoids_positivePole {β : Nat}
    (sourceTail middleLowerTail : List Bool) {targetU targetV : ℚ}
    (beta_large : 3 ≤ β)
    (middle_length : 2 * β + 4 ≤ (true :: true :: middleLowerTail).length)
    (targetU_pos : 0 < targetU) (targetV_pos : 0 < targetV) :
    jStep (doubleDeletionUpper ((10 : ℚ) ^ β))
        (jLower ((10 : ℚ) ^ β)
          (normalizedLower [true, true] (true :: true :: middleLowerTail)) 1)
        (jUpper ((10 : ℚ) ^ β) (code (true :: true :: sourceTail))
          (10 ^ (true :: true :: sourceTail).length)) ≠ jPole targetU targetV := by
  have outside := ruleDeletion_cLeading_step_outside sourceTail middleLowerTail
    beta_large middle_length
  have target := jPole_mem_unit targetU_pos targetV_pos
  linarith

theorem ruleDeletion_bLeading_avoids_positivePole {β : Nat}
    (sourceTail middleLowerTail : List Bool) {targetU targetV : ℚ}
    (beta_large : 3 ≤ β)
    (middle_length : 2 * β + 4 ≤ (true :: true :: middleLowerTail).length)
    (targetU_pos : 0 < targetU) (targetV_pos : 0 < targetV) :
    jStep (doubleDeletionUpper ((10 : ℚ) ^ β))
        (jLower ((10 : ℚ) ^ β)
          (normalizedLower [true, true] (true :: true :: middleLowerTail)) 1)
        (jUpper ((10 : ℚ) ^ β) (code (bTag β ++ sourceTail))
          (10 ^ (bTag β ++ sourceTail).length)) ≠ jPole targetU targetV := by
  have outside := ruleDeletion_bLeading_step_outside sourceTail middleLowerTail
    beta_large middle_length
  have target := jPole_mem_unit targetU_pos targetV_pos
  linarith

/-! ## Emitted-body grammar -/

theorem length_le_tagEncode (β : Nat) (word : List TagLetter) :
    word.length ≤ (tagEncode β word).length := by
  induction word with
  | nil => simp
  | cons letter word ih =>
      rw [tagEncode_cons, List.length_cons, List.length_append]
      have code_pos : 0 < (tagCode β letter).length := by
        cases letter <;> simp [tagCode]
      omega

theorem tagEncode_length_of_head_b {β : Nat} {body : List TagLetter}
    (body_long : β - 1 ≤ body.length)
    (body_head : body.head? = some .b) :
    2 * β ≤ (tagEncode β body).length := by
  cases body with
  | nil => simp at body_head
  | cons letter tail =>
      simp only [List.head?_cons, Option.some.injEq] at body_head
      subst letter
      rw [tagEncode_cons, List.length_append]
      have tail_bound := length_le_tagEncode β tail
      simp [tagCode] at body_long ⊢
      omega

/-- Lower spelling of the length-two block `R_c D_c`. -/
def ruleDeletionLowerWord (β : Nat) (body : List TagLetter) : List Bool :=
  nearyLower β body (.rule .c) ++ nearyLower β body (.erase .c)

theorem ruleDeletionLowerWord_shape {β : Nat} {body : List TagLetter}
    (body_long : β - 1 ≤ body.length)
    (body_head : body.head? = some .b) :
    ∃ tail, ruleDeletionLowerWord β body = true :: true :: tail ∧
      2 * β + 4 ≤ (true :: true :: tail).length := by
  cases body with
  | nil => simp at body_head
  | cons letter tail =>
      simp only [List.head?_cons, Option.some.injEq] at body_head
      subst letter
      let lowerTail := List.replicate β false ++
        true :: tagEncode β tail ++ [true, false, false]
      refine ⟨lowerTail, ?_, ?_⟩
      · simp [ruleDeletionLowerWord, nearyLower, tagEncode_cons, tagCode, lowerTail,
          List.append_assoc]
      · have encoded_bound := tagEncode_length_of_head_b body_long (by simp)
        simp [lowerTail, tagEncode_cons, tagCode] at encoded_bound ⊢
        omega

theorem compiler_body_head_b {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) :
    (NearyCompiler.body system input haltPhase period_pos).head? = some .b := by
  have whole_head :
      (NearyCompiler.wholeAppendant system input haltPhase period_pos).head? = some .b := by
    have not_last : 0 ≠ 10 * period - 1 := by
      simp
      omega
    unfold NearyCompiler.wholeAppendant weave
    simp [List.head?_eq_getElem?, NearyCompiler.tableTrack, NearyCompiler.tableTrackVal,
      NearyCompiler.deletionWidth, period_pos, NearyCompiler.trackWidth_pos, not_last]
    change
      (List.replicate (NearyCompiler.trackWidth system input) TagLetter.b)[0]'_ = TagLetter.b
    simp
  have body_ne : NearyCompiler.body system input haltPhase period_pos ≠ [] := by
    intro body_empty
    have lengths := congrArg List.length body_empty
    rw [NearyCompiler.body_length] at lengths
    have beta_large := NearyCompiler.deletionWidth_large period_pos
    simp [NearyCompiler.deletionWidth] at lengths
    omega
  rw [NearyCompiler.wholeAppendant_eq_body_append,
    List.head?_append_of_ne_nil _ body_ne] at whole_head
  exact whole_head

/-- The truncated compiler body also ends in `b`; its final position is the penultimate, hence
even, position of the woven appendant. -/
theorem compiler_body_getLast?_b {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) :
    (NearyCompiler.body system input haltPhase period_pos).getLast? = some .b := by
  let body := NearyCompiler.body system input haltPhase period_pos
  let whole := NearyCompiler.wholeAppendant system input haltPhase period_pos
  have body_ne : body ≠ [] := by
    intro body_empty
    have lengths := congrArg List.length body_empty
    rw [NearyCompiler.body_length] at lengths
    have beta_large := NearyCompiler.deletionWidth_large period_pos
    simp [NearyCompiler.deletionWidth] at lengths
    omega
  have whole_eq : whole = body ++ [.b] :=
    NearyCompiler.wholeAppendant_eq_body_append system input haltPhase period_pos
  have whole_even : 2 ∣ whole.length := by
    exact dvd_trans (by norm_num)
      (NearyCompiler.wholeAppendant_aligned system input haltPhase period_pos)
  have body_length : body.length + 1 = whole.length := by
    rw [whole_eq]
    simp
  have index_lt_body : body.length - 1 < body.length := by omega
  have index_even : (body.length - 1) % 2 = 0 := by
    have whole_mod : whole.length % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp whole_even
    omega
  have index_lt_whole : body.length - 1 < whole.length := by omega
  have whole_at_last : whole[body.length - 1] = .b := by
    apply NearyCompiler.wholeAppendant_get_of_even_index system input haltPhase period_pos
      (body.length - 1) index_lt_whole index_even
  have body_at_last : body[body.length - 1] = .b := by
    simpa only [whole_eq, List.getElem_append_left index_lt_body] using whole_at_last
  rw [List.getLast?_eq_getLast_of_ne_nil body_ne]
  apply congrArg some
  simpa [List.getLast_eq_getElem] using body_at_last

theorem compiler_ruleDeletionLowerWord_shape {period : Nat}
    (system : CyclicTag period) (input : List Bool) (haltPhase : Fin period)
    (period_pos : 0 < period) :
    ∃ tail,
      ruleDeletionLowerWord (NearyCompiler.deletionWidth period)
          (NearyCompiler.body system input haltPhase period_pos) = true :: true :: tail ∧
        2 * NearyCompiler.deletionWidth period + 4 ≤ (true :: true :: tail).length := by
  have body_long :
      NearyCompiler.deletionWidth period - 1 ≤
        (NearyCompiler.body system input haltPhase period_pos).length := by
    simpa using
      (NearyArithmeticEnvelope.body_long
        (NearyCompiler.arithmeticEnvelope system input haltPhase period_pos))
  exact ruleDeletionLowerWord_shape body_long
    (compiler_body_head_b system input haltPhase period_pos)

end MatrixMortality.DecimalSetterChamber
