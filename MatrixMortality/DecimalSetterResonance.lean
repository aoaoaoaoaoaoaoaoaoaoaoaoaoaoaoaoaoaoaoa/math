import MatrixMortality.DecimalSetterChamber

/-!
# Extinction of the remaining ordinary decimal resonances

The joint shell forest leaves two ordinary depth-two families after the length-two A/A branch:
an all-`c` middle block before a singleton target, and an all-`c` source of length `β` followed
by `D_b`. This file supplies their exact Archimedean cuts in the negative J-fraction chart.
-/

namespace MatrixMortality.DecimalSetterResonance

open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterChamber
open MatrixMortality.Undecidability

/-- J-coordinate of an all-`c` upper spelling of length `β` after the ordinary reset. -/
def repeatedCSource (ρ : ℚ) : ℚ :=
  (50 * ρ ^ 2 + 2 * ρ - 7) / (ρ * (52 * ρ - 7))

/-- Upper J-fraction coefficient of the singleton `D_b` block. -/
def singleBUpper (ρ : ℚ) : ℚ :=
  jUpper ρ (10 * marker ρ + 5) (100 * ρ)

/-- Lower J-fraction coefficient of the singleton `D_b` block. -/
def singleBLower (ρ : ℚ) : ℚ :=
  jLower ρ (7 / (100 * ρ)) 1

theorem repeatedTrue_code_identity (width : Nat) :
    9 * code (List.replicate width true) + 5 = 5 * 10 ^ width := by
  induction width with
  | zero => norm_num
  | succ width ih =>
      rw [List.replicate_succ, code_cons, digit_true, List.length_replicate,
        pow_succ]
      omega

theorem repeatedCSource_eq_encoded (β : Nat) :
    repeatedCSource ((10 : ℚ) ^ β) =
      jUpper ((10 : ℚ) ^ β) (code (List.replicate β true)) (10 ^ β) := by
  let ρ : ℚ := 10 ^ β
  have code_identity := repeatedTrue_code_identity β
  have code_eq : (code (List.replicate β true) : ℚ) = (5 * ρ - 5) / 9 := by
    have cast_identity :
        ((9 * code (List.replicate β true) + 5 : Nat) : ℚ) =
          ((5 * 10 ^ β : Nat) : ℚ) := by
      exact_mod_cast code_identity
    norm_num at cast_identity
    dsimp [ρ]
    linarith
  change repeatedCSource ρ = jUpper ρ (code (List.replicate β true)) ρ
  rw [code_eq]
  unfold repeatedCSource jUpper marker
  ring_nf
  have rho_pos : 0 < ρ := by
    dsimp [ρ]
    positivity
  have marker_factor_pos : 0 < 52 * ρ - 7 := by
    nlinarith
  have first_denominator_pos : 0 < -(ρ * 7) + ρ ^ 2 * 52 := by
    rw [show -(ρ * 7) + ρ ^ 2 * 52 = ρ * (52 * ρ - 7) by ring]
    exact mul_pos rho_pos marker_factor_pos
  have second_denominator_pos :
      0 < ρ * (-7 / 9) + ρ ^ 2 * (52 / 9) := by
    rw [show ρ * (-7 / 9) + ρ ^ 2 * (52 / 9) =
      ρ * (52 * ρ - 7) / 9 by ring]
    exact div_pos (mul_pos rho_pos marker_factor_pos) (by norm_num)
  field_simp [ne_of_gt first_denominator_pos, ne_of_gt second_denominator_pos]
  ring

theorem singleBUpper_eq_encoded (β : Nat) :
    singleBUpper ((10 : ℚ) ^ β) =
      jUpper ((10 : ℚ) ^ β) (code (bTag β)) (10 ^ (bTag β).length) := by
  let ρ : ℚ := 10 ^ β
  have code_eq : (code (bTag β) : ℚ) = 10 * marker ρ + 5 := by
    rw [bTag_code]
    norm_num
    rw [markerWord_code_eq_marker]
  have scale_eq : (10 : ℚ) ^ (bTag β).length = 100 * ρ := by
    simp [bTag, markerWord, ρ, pow_succ]
    ring
  change singleBUpper ρ =
    jUpper ρ (code (bTag β)) ((10 : ℚ) ^ (bTag β).length)
  rw [code_eq, scale_eq]
  rfl

theorem singleBLower_eq_encoded (β : Nat) :
    singleBLower ((10 : ℚ) ^ β) =
      jLower ((10 : ℚ) ^ β) (normalizedLower (bTag β) [false]) 1 := by
  let ρ : ℚ := 10 ^ β
  have scale_eq : (10 : ℚ) ^ (bTag β).length = 100 * ρ := by
    simp [bTag, markerWord, ρ, pow_succ]
    ring
  change singleBLower ρ = jLower ρ (normalizedLower (bTag β) [false]) 1
  simp [singleBLower, normalizedLower, code, digit, scale_eq]

private theorem singleBUpper_eq_closed {ρ : ℚ}
    (rho_ne : ρ ≠ 0) (marker_factor_ne : 52 * ρ - 7 ≠ 0) :
    singleBUpper ρ =
      (5200 * ρ ^ 2 - 198 * ρ - 7) / (100 * ρ * (52 * ρ - 7)) := by
  unfold singleBUpper jUpper marker
  field_simp [rho_ne, marker_factor_ne]
  ring

private theorem singleBLower_eq_closed {ρ : ℚ} (rho_ne : ρ ≠ 0) :
    singleBLower ρ =
      7 * (502 * ρ - 7) /
        (100 * ρ * (2 * ρ - 7) * (52 * ρ - 7)) := by
  unfold singleBLower jLower lowerScale lift
  field_simp [rho_ne]

/-- The surviving B/A shell family crosses one strictly: an all-`c` source of length `β`
followed by `D_b` cannot be the next pole of any positive block. -/
theorem singleB_after_repeatedC_gt_one {ρ : ℚ} (rho_bound : 1000 ≤ ρ) :
    1 < jStep (singleBUpper ρ) (singleBLower ρ) (repeatedCSource ρ) := by
  have rho_pos : 0 < ρ := lt_of_lt_of_le (by norm_num) rho_bound
  have marker_factor_pos : 0 < 52 * ρ - 7 := by linarith
  have lift_factor_pos : 0 < 502 * ρ - 7 := by linarith
  have gap_factor_pos : 0 < 2 * ρ - 7 := by linarith
  have source_factor_pos : 0 < 50 * ρ ^ 2 + 2 * ρ - 7 := by
    nlinarith [sq_nonneg (ρ - 1000)]
  have ten_factor_pos : 0 < 10 * ρ - 1 := by linarith
  have difference :
      jStep (singleBUpper ρ) (singleBLower ρ) (repeatedCSource ρ) - 1 =
        (10 * ρ - 1) * (502 * ρ - 7) /
          (20 * (52 * ρ - 7) * (50 * ρ ^ 2 + 2 * ρ - 7)) := by
    rw [singleBUpper_eq_closed (ne_of_gt rho_pos) (ne_of_gt marker_factor_pos),
      singleBLower_eq_closed (ne_of_gt rho_pos)]
    unfold jStep repeatedCSource
    field_simp [ne_of_gt rho_pos, ne_of_gt marker_factor_pos,
      ne_of_gt gap_factor_pos, ne_of_gt source_factor_pos]
    field_simp [show ρ * 2 - 7 ≠ 0 by linarith,
      show ρ * 52 - 7 ≠ 0 by linarith,
      show ρ * (ρ * 50 + 2) - 7 ≠ 0 by nlinarith]
    ring
  rw [← sub_pos, difference]
  exact div_pos (mul_pos ten_factor_pos lift_factor_pos)
    (mul_pos (mul_pos (by norm_num) marker_factor_pos) source_factor_pos)

theorem singleB_after_repeatedC_ne_pole {ρ targetU targetV : ℚ}
    (rho_bound : 1000 ≤ ρ) (targetU_pos : 0 < targetU) (targetV_pos : 0 < targetV) :
    jStep (singleBUpper ρ) (singleBLower ρ) (repeatedCSource ρ) ≠
      jPole targetU targetV := by
  have step_high := singleB_after_repeatedC_gt_one rho_bound
  have pole_unit := jPole_mem_unit targetU_pos targetV_pos
  linarith

theorem thousand_le_ten_pow {β : Nat} (beta_large : 3 ≤ β) :
    (1000 : ℚ) ≤ 10 ^ β := by
  have natural_bound : 10 ^ 3 ≤ 10 ^ β :=
    Nat.pow_le_pow_right (by norm_num) beta_large
  norm_num at natural_bound ⊢
  exact_mod_cast natural_bound

/-- Encoded form of the B/A extinction: `β` all-`c` roles followed by `D_b` crosses above one. -/
theorem encodedSingleB_after_repeatedC_ne_pole {β : Nat} {targetU targetV : ℚ}
    (beta_large : 3 ≤ β) (targetU_pos : 0 < targetU) (targetV_pos : 0 < targetV) :
    jStep
        (jUpper (10 ^ β) (code (bTag β)) (10 ^ (bTag β).length))
        (jLower (10 ^ β) (normalizedLower (bTag β) [false]) 1)
        (jUpper (10 ^ β) (code (List.replicate β true)) (10 ^ β)) ≠
      jPole targetU targetV := by
  rw [← singleBUpper_eq_encoded, ← singleBLower_eq_encoded,
    ← repeatedCSource_eq_encoded]
  exact singleB_after_repeatedC_ne_pole (thousand_le_ten_pow beta_large)
    targetU_pos targetV_pos

theorem encodedSingleB_after_repeatedC_avoids_encodedPole {β : Nat}
    (targetUpperTail targetLower : List Bool) (beta_large : 3 ≤ β)
    (targetLower_ne : targetLower ≠ []) :
    jStep
        (jUpper (10 ^ β) (code (bTag β)) (10 ^ (bTag β).length))
        (jLower (10 ^ β) (normalizedLower (bTag β) [false]) 1)
        (jUpper (10 ^ β) (code (List.replicate β true)) (10 ^ β)) ≠
      jPole
        (jUpper (10 ^ β) (code (true :: targetUpperTail))
          (10 ^ (true :: targetUpperTail).length))
        (jLower (10 ^ β)
          (normalizedLower (true :: targetUpperTail) targetLower) 1) := by
  have rho_bound := thousand_le_ten_pow beta_large
  have target_window := encodedJUpper_in_window targetUpperTail rho_bound
  have target_normalized_pos :=
    normalizedLower_pos (upper := true :: targetUpperTail) targetLower_ne
  have target_lower_pos := jLower_pos rho_bound target_normalized_pos
  exact encodedSingleB_after_repeatedC_ne_pole beta_large
    (lt_trans (by norm_num) target_window.1) target_lower_pos

/-! ## A-to-B chambers -/

theorem tinyNormalizedLower_lt {ρ normalized : ℚ}
    (rho_bound : 1000 ≤ ρ) (normalized_upper : normalized < 7 / 9) :
    jLower ρ normalized 1 < 1 / 200 := by
  have rho_pos : 0 < ρ := lt_of_lt_of_le (by norm_num) rho_bound
  have gap_pos : 0 < 2 * ρ - 7 := by linarith
  have marker_factor_pos : 0 < 52 * ρ - 7 := by linarith
  have lift_pos : 0 < 502 * ρ - 7 := by linarith
  have denominator_pos : 0 < (2 * ρ - 7) * (52 * ρ - 7) :=
    mul_pos gap_pos marker_factor_pos
  have upper_gap : 0 ≤ (502 * ρ - 7) * (7 / 9 - normalized) :=
    mul_nonneg lift_pos.le (sub_nonneg.mpr normalized_upper.le)
  unfold jLower lowerScale lift
  simp only [div_one]
  rw [div_mul_eq_mul_div, div_lt_iff₀ denominator_pos]
  nlinarith [sq_nonneg (ρ - 1000)]

theorem tinyLower_step_above_three_quarters {u v t : ℚ}
    (u_lower : 4 / 5 < u) (v_pos : 0 < v) (v_upper : v < 1 / 200)
    (t_lower : 4 / 5 < t) :
    3 / 4 < jStep u v t := by
  have t_pos : 0 < t := lt_trans (by norm_num) t_lower
  have quotient_upper : v / t < 1 / 160 := by
    rw [div_lt_iff₀ t_pos]
    nlinarith
  unfold jStep
  linarith

theorem tinyLower_pole_below_one_hundredth {u v : ℚ}
    (u_lower : 4 / 5 < u) (v_pos : 0 < v) (v_upper : v < 1 / 200) :
    jPole u v < 1 / 100 := by
  have sum_pos : 0 < u + v := add_pos (lt_trans (by norm_num) u_lower) v_pos
  unfold jPole
  rw [div_lt_iff₀ sum_pos]
  nlinarith

/-- A low-weight all-deletion middle block stays above `3/4`, whereas either singleton target
pole lies below `1/100`. -/
theorem encodedTinyLower_avoids_singletonPole {ρ middleNormalized : ℚ}
    (sourceTail middleTail targetTail : List Bool)
    (rho_bound : 1000 ≤ ρ) (middle_pos : 0 < middleNormalized)
    (middle_upper : middleNormalized < 7 / 9) :
    jStep
        (jUpper ρ (code (true :: middleTail)) (10 ^ (true :: middleTail).length))
        (jLower ρ middleNormalized 1)
        (jUpper ρ (code (true :: sourceTail)) (10 ^ (true :: sourceTail).length)) ≠
      jPole
        (jUpper ρ (code (true :: targetTail)) (10 ^ (true :: targetTail).length))
        (jLower ρ (normalizedLower (true :: targetTail) [false]) 1) := by
  have source_window := encodedJUpper_in_window sourceTail rho_bound
  have middle_window := encodedJUpper_in_window middleTail rho_bound
  have target_window := encodedJUpper_in_window targetTail rho_bound
  have middle_v_pos := jLower_pos rho_bound middle_pos
  have middle_v_upper := tinyNormalizedLower_lt rho_bound middle_upper
  have target_normalized_pos :
      0 < normalizedLower (true :: targetTail) [false] :=
    normalizedLower_pos (by simp)
  have target_normalized_upper :
      normalizedLower (true :: targetTail) [false] < 7 / 9 := by
    simpa using
      (normalizedLower_lt_lowShell (upper := true :: targetTail)
        (lower := [false]) (β := 0) (by simp))
  have target_v_pos := jLower_pos rho_bound target_normalized_pos
  have target_v_upper := tinyNormalizedLower_lt rho_bound target_normalized_upper
  have step_high := tinyLower_step_above_three_quarters middle_window.1
    middle_v_pos middle_v_upper source_window.1
  have pole_low := tinyLower_pole_below_one_hundredth target_window.1
    target_v_pos target_v_upper
  linarith

/-- A high-weight rule-containing middle block sends every `c`-leading multi-role source below
zero, away from either singleton target pole. -/
theorem encodedHugeLower_cLeading_avoids_singletonPole {β : Nat} {normalized : ℚ}
    (sourceTail middleTail targetTail : List Bool) (beta_large : 3 ≤ β)
    (normalized_lower : 55 * ((10 : ℚ) ^ β) ^ 2 ≤ normalized) :
    jStep
        (jUpper (10 ^ β) (code (true :: middleTail)) (10 ^ (true :: middleTail).length))
        (jLower (10 ^ β) normalized 1)
        (jUpper (10 ^ β) (code (true :: true :: sourceTail))
          (10 ^ (true :: true :: sourceTail).length)) ≠
      jPole
        (jUpper (10 ^ β) (code (true :: targetTail)) (10 ^ (true :: targetTail).length))
        (jLower (10 ^ β) (normalizedLower (true :: targetTail) [false]) 1) := by
  let ρ : ℚ := 10 ^ β
  have rho_bound : 1000 ≤ ρ := thousand_le_ten_pow beta_large
  have middle_window := encodedJUpper_in_window (ρ := ρ) middleTail rho_bound
  have middle_v_lower : 265 * ρ < jLower ρ normalized 1 :=
    hugeNormalizedLower_gt rho_bound normalized_lower
  have source_window := encodedJUpper_in_window (ρ := ρ) (true :: sourceTail) rho_bound
  have source_upper := cLeadingMulti_jUpper_upper sourceTail beta_large
  have step_negative := jStep_negative_of_hugeLower rho_bound middle_window.2 middle_v_lower
    (lt_trans (by norm_num) source_window.1) source_upper
  have target_window := encodedJUpper_in_window (ρ := ρ) targetTail rho_bound
  have target_normalized_pos :
      0 < normalizedLower (true :: targetTail) [false] :=
    normalizedLower_pos (by simp)
  have target_v_pos := jLower_pos rho_bound target_normalized_pos
  have target_pole :=
    jPole_mem_unit (lt_trans (by norm_num) target_window.1) target_v_pos
  exact ne_of_lt (step_negative.trans target_pole.1)

/-- A high-weight rule-containing middle block sends every `b`-leading source above one, away
from either singleton target pole. -/
theorem encodedHugeLower_bLeading_avoids_singletonPole {β : Nat} {normalized : ℚ}
    (sourceTail middleTail targetTail : List Bool) (beta_large : 3 ≤ β)
    (normalized_lower : 55 * ((10 : ℚ) ^ β) ^ 2 ≤ normalized) :
    jStep
        (jUpper (10 ^ β) (code (true :: middleTail)) (10 ^ (true :: middleTail).length))
        (jLower (10 ^ β) normalized 1)
        (jUpper (10 ^ β) (code (bTag β ++ sourceTail))
          (10 ^ (bTag β ++ sourceTail).length)) ≠
      jPole
        (jUpper (10 ^ β) (code (true :: targetTail)) (10 ^ (true :: targetTail).length))
        (jLower (10 ^ β) (normalizedLower (true :: targetTail) [false]) 1) := by
  let ρ : ℚ := 10 ^ β
  have rho_bound : 1000 ≤ ρ := thousand_le_ten_pow beta_large
  have middle_window := encodedJUpper_in_window (ρ := ρ) middleTail rho_bound
  have middle_v_lower : 265 * ρ < jLower ρ normalized 1 :=
    hugeNormalizedLower_gt rho_bound normalized_lower
  have source_lower := bLeading_jUpper_lower sourceTail beta_large
  let sourceRest := List.replicate β false ++ true :: sourceTail
  have source_window := encodedJUpper_in_window (ρ := ρ) sourceRest rho_bound
  have source_upper :
      jUpper ρ (code (bTag β ++ sourceTail))
          (10 ^ (bTag β ++ sourceTail).length) < 101 / 100 := by
    simpa [bTag, markerWord, sourceRest, List.append_assoc] using source_window.2
  have step_high := jStep_above_one_of_hugeLower rho_bound middle_window.1 middle_v_lower
    source_lower source_upper
  have target_window := encodedJUpper_in_window (ρ := ρ) targetTail rho_bound
  have target_normalized_pos :
      0 < normalizedLower (true :: targetTail) [false] :=
    normalizedLower_pos (by simp)
  have target_v_pos := jLower_pos rho_bound target_normalized_pos
  have target_pole :=
    jPole_mem_unit (lt_trans (by norm_num) target_window.1) target_v_pos
  linarith

/-! ## All-c phase grammar -/

/-- Phase bit for an all-`c` block: `true` is rule and `false` is erasure. -/
def cPhaseTile : Bool → NearyTile
  | true => .rule .c
  | false => .erase .c

/-- Upper spelling of an all-`c` phase word. -/
def cBlockUpper (β : Nat) (phases : List Bool) : List Bool :=
  spell (nearyUpper β) (phases.map cPhaseTile)

/-- Lower spelling of an all-`c` phase word. -/
def cBlockLower (β : Nat) (body : List TagLetter) (phases : List Bool) : List Bool :=
  spell (nearyLower β body) (phases.map cPhaseTile)

theorem cBlockUpper_eq_replicate (β : Nat) (phases : List Bool) :
    cBlockUpper β phases = List.replicate phases.length true := by
  induction phases with
  | nil => rfl
  | cons phase phases ih =>
      cases phase <;>
        change true :: cBlockUpper β phases = List.replicate (phases.length + 1) true <;>
        rw [ih, List.replicate_succ]

theorem cBlockLower_length_ge (β : Nat) (body : List TagLetter) (phases : List Bool) :
    phases.length ≤ (cBlockLower β body phases).length := by
  induction phases with
  | nil => simp [cBlockLower, spell]
  | cons phase phases ih =>
      cases phase <;>
        simp [cBlockLower, spell, cPhaseTile, nearyLower] at ih ⊢ <;>
        omega

theorem cBlockLower_allDeletion (β : Nat) (body : List TagLetter) (width : Nat) :
    cBlockLower β body (List.replicate width false) =
      List.replicate width false := by
  induction width with
  | zero => rfl
  | succ width ih =>
      change false :: cBlockLower β body (List.replicate width false) =
        List.replicate (width + 1) false
      rw [ih, List.replicate_succ]

theorem allDeletion_normalizedLower_mem (β : Nat) (body : List TagLetter) (width : Nat) :
    0 < normalizedLower
        (cBlockUpper β (List.replicate (width + 1) false))
        (cBlockLower β body (List.replicate (width + 1) false)) ∧
      normalizedLower
          (cBlockUpper β (List.replicate (width + 1) false))
          (cBlockLower β body (List.replicate (width + 1) false)) < 7 / 9 := by
  have upper_eq :
      cBlockUpper β (List.replicate (width + 1) false) =
        List.replicate (width + 1) true := by
    rw [cBlockUpper_eq_replicate, List.length_replicate]
  have lower_eq :
      cBlockLower β body (List.replicate (width + 1) false) =
        List.replicate (width + 1) false :=
    cBlockLower_allDeletion β body (width + 1)
  rw [upper_eq, lower_eq]
  constructor
  · exact normalizedLower_pos (by simp)
  · simpa using
      (normalizedLower_lt_lowShell
        (upper := List.replicate (width + 1) true)
        (lower := List.replicate (width + 1) false) (β := 0) (by simp))

/-- Every positive-length all-`D_c` middle block misses both singleton target poles. -/
theorem allDeletion_avoids_singletonPole {ρ : ℚ} (β : Nat) (body : List TagLetter)
    (width : Nat) (sourceTail targetTail : List Bool) (rho_bound : 1000 ≤ ρ) :
    jStep
        (jUpper ρ
          (code (cBlockUpper β (List.replicate (width + 1) false)))
          (10 ^ (cBlockUpper β (List.replicate (width + 1) false)).length))
        (jLower ρ
          (normalizedLower
            (cBlockUpper β (List.replicate (width + 1) false))
            (cBlockLower β body (List.replicate (width + 1) false))) 1)
        (jUpper ρ (code (true :: sourceTail)) (10 ^ (true :: sourceTail).length)) ≠
      jPole
        (jUpper ρ (code (true :: targetTail)) (10 ^ (true :: targetTail).length))
        (jLower ρ (normalizedLower (true :: targetTail) [false]) 1) := by
  have upper_eq :
      cBlockUpper β (List.replicate (width + 1) false) =
        true :: List.replicate width true := by
    rw [cBlockUpper_eq_replicate, List.length_replicate, List.replicate_succ]
  obtain ⟨middle_pos, middle_upper⟩ := allDeletion_normalizedLower_mem β body width
  rw [upper_eq] at middle_pos middle_upper ⊢
  exact encodedTinyLower_avoids_singletonPole sourceTail (List.replicate width true)
    targetTail rho_bound middle_pos middle_upper

theorem cBlockLower_ruleSplit (β : Nat) (body : List TagLetter)
    (deletions : Nat) (suffix : List Bool) :
    cBlockLower β body (List.replicate deletions false ++ true :: suffix) =
      List.replicate deletions false ++ nearyLower β body (.rule .c) ++
        cBlockLower β body suffix := by
  induction deletions with
  | zero => rfl
  | succ deletions ih =>
      change false ::
          cBlockLower β body (List.replicate deletions false ++ true :: suffix) =
        false ::
          (List.replicate deletions false ++ nearyLower β body (.rule .c) ++
            cBlockLower β body suffix)
      exact congrArg (false :: ·) ih

theorem cBlockLower_ruleSplit_length_gap (β : Nat) (body : List TagLetter)
    (deletions : Nat) (suffix : List Bool)
    (tag_length : 2 * β ≤ (tagEncode β body).length) :
    (cBlockUpper β (List.replicate deletions false ++ true :: suffix)).length +
        2 * β + 2 ≤
      (cBlockLower β body (List.replicate deletions false ++ true :: suffix)).length := by
  have suffix_bound := cBlockLower_length_ge β body suffix
  rw [cBlockUpper_eq_replicate, List.length_replicate,
    cBlockLower_ruleSplit]
  simp only [List.length_append, List.length_replicate, List.length_cons]
  simp only [nearyLower, List.length_append, List.length_cons, List.length_nil]
  omega

theorem cBlockLower_ruleHead_shape {β : Nat} {body : List TagLetter}
    (suffix : List Bool) (body_head : body.head? = some .b) :
    ∃ tail, cBlockLower β body (true :: suffix) = true :: true :: tail := by
  cases body with
  | nil => simp at body_head
  | cons letter bodyTail =>
      simp only [List.head?_cons, Option.some.injEq] at body_head
      subst letter
      let tail := List.replicate β false ++ true :: tagEncode β bodyTail ++
        [true, false] ++ cBlockLower β (TagLetter.b :: bodyTail) suffix
      refine ⟨tail, ?_⟩
      simp [cBlockLower, spell, cPhaseTile, nearyLower, tagEncode_cons, tagCode,
        tail, List.append_assoc]

theorem cBlockLower_deletionPrefix_shape (β : Nat) (body : List TagLetter)
    (deletions : Nat) (suffix : List Bool) :
    ∃ tail,
      cBlockLower β body
          (List.replicate (deletions + 1) false ++ true :: suffix) = false :: tail := by
  refine ⟨List.replicate deletions false ++ nearyLower β body (.rule .c) ++
    cBlockLower β body suffix, ?_⟩
  rw [cBlockLower_ruleSplit, List.replicate_succ]
  rfl

/-- Every all-`c` phase word containing a rule has huge normalized lower weight for an emitted
body. The split chooses any rule and records the preceding deletions. -/
theorem ruleBearing_normalizedLower_huge {β : Nat} {body : List TagLetter}
    (deletions : Nat) (suffix : List Bool)
    (body_long : β - 1 ≤ body.length) (body_head : body.head? = some .b) :
    55 * ((10 : ℚ) ^ β) ^ 2 ≤
      normalizedLower
        (cBlockUpper β (List.replicate deletions false ++ true :: suffix))
        (cBlockLower β body (List.replicate deletions false ++ true :: suffix)) := by
  have tag_length := tagEncode_length_of_head_b body_long body_head
  have length_gap := cBlockLower_ruleSplit_length_gap β body deletions suffix tag_length
  have scale_identity :
      55 * ((10 : ℚ) ^ β) ^ 2 = 11 / 2 * (10 : ℚ) ^ (2 * β + 1) := by
    rw [show 2 * β + 1 = β + β + 1 by omega, pow_succ, pow_add]
    ring
  cases deletions with
  | zero =>
      obtain ⟨tail, lower_shape⟩ := cBlockLower_ruleHead_shape suffix body_head
      have zero_gap :
          (cBlockUpper β (true :: suffix)).length + 2 * β + 2 ≤
            (cBlockLower β body (true :: suffix)).length := by
        simpa using length_gap
      have shell := normalizedLower_highShell_true_true
        (upper := cBlockUpper β (true :: suffix)) (tail := tail)
        (β := 2 * β + 1) (by
          rw [← lower_shape]
          omega)
      have result :
          55 * ((10 : ℚ) ^ β) ^ 2 ≤
            normalizedLower (cBlockUpper β (true :: suffix))
              (cBlockLower β body (true :: suffix)) := by
        calc
          55 * ((10 : ℚ) ^ β) ^ 2 =
              11 / 2 * (10 : ℚ) ^ (2 * β + 1) := scale_identity
          _ ≤ normalizedLower (cBlockUpper β (true :: suffix))
              (true :: true :: tail) := shell
          _ = normalizedLower (cBlockUpper β (true :: suffix))
              (cBlockLower β body (true :: suffix)) := by rw [lower_shape]
      simpa using result
  | succ deletions =>
      obtain ⟨tail, lower_shape⟩ :=
        cBlockLower_deletionPrefix_shape β body deletions suffix
      have shell := normalizedLower_highShell_false
        (upper := cBlockUpper β
          (List.replicate (deletions + 1) false ++ true :: suffix))
        (tail := tail) (β := 2 * β + 1) (by
          rw [← lower_shape]
          omega)
      calc
        55 * ((10 : ℚ) ^ β) ^ 2 =
            11 / 2 * (10 : ℚ) ^ (2 * β + 1) := scale_identity
        _ ≤ normalizedLower
            (cBlockUpper β
              (List.replicate (deletions + 1) false ++ true :: suffix))
            (false :: tail) := shell
        _ = normalizedLower
            (cBlockUpper β
              (List.replicate (deletions + 1) false ++ true :: suffix))
            (cBlockLower β body
              (List.replicate (deletions + 1) false ++ true :: suffix)) := by
              rw [lower_shape]

/-- A rule-bearing all-`c` middle block misses a singleton target from every `c`-leading
multi-role source. -/
theorem ruleBearing_cLeading_avoids_singletonPole {β : Nat} {body : List TagLetter}
    (deletions : Nat) (suffix sourceTail targetTail : List Bool)
    (beta_large : 3 ≤ β) (body_long : β - 1 ≤ body.length)
    (body_head : body.head? = some .b) :
    jStep
        (jUpper (10 ^ β)
          (code (cBlockUpper β (List.replicate deletions false ++ true :: suffix)))
          (10 ^ (cBlockUpper β
            (List.replicate deletions false ++ true :: suffix)).length))
        (jLower (10 ^ β)
          (normalizedLower
            (cBlockUpper β (List.replicate deletions false ++ true :: suffix))
            (cBlockLower β body
              (List.replicate deletions false ++ true :: suffix))) 1)
        (jUpper (10 ^ β) (code (true :: true :: sourceTail))
          (10 ^ (true :: true :: sourceTail).length)) ≠
      jPole
        (jUpper (10 ^ β) (code (true :: targetTail)) (10 ^ (true :: targetTail).length))
        (jLower (10 ^ β) (normalizedLower (true :: targetTail) [false]) 1) := by
  let middleTail := List.replicate (deletions + suffix.length) true
  have upper_eq :
      cBlockUpper β (List.replicate deletions false ++ true :: suffix) =
        true :: middleTail := by
    rw [cBlockUpper_eq_replicate]
    simp only [List.length_append, List.length_replicate, List.length_cons]
    rw [show deletions + (suffix.length + 1) =
      deletions + suffix.length + 1 by omega, List.replicate_succ]
  have lower_bound :=
    ruleBearing_normalizedLower_huge deletions suffix body_long body_head
  rw [upper_eq] at lower_bound ⊢
  exact encodedHugeLower_cLeading_avoids_singletonPole sourceTail middleTail targetTail
    beta_large lower_bound

/-- A rule-bearing all-`c` middle block misses a singleton target from every `b`-leading
source. -/
theorem ruleBearing_bLeading_avoids_singletonPole {β : Nat} {body : List TagLetter}
    (deletions : Nat) (suffix sourceTail targetTail : List Bool)
    (beta_large : 3 ≤ β) (body_long : β - 1 ≤ body.length)
    (body_head : body.head? = some .b) :
    jStep
        (jUpper (10 ^ β)
          (code (cBlockUpper β (List.replicate deletions false ++ true :: suffix)))
          (10 ^ (cBlockUpper β
            (List.replicate deletions false ++ true :: suffix)).length))
        (jLower (10 ^ β)
          (normalizedLower
            (cBlockUpper β (List.replicate deletions false ++ true :: suffix))
            (cBlockLower β body
              (List.replicate deletions false ++ true :: suffix))) 1)
        (jUpper (10 ^ β) (code (bTag β ++ sourceTail))
          (10 ^ (bTag β ++ sourceTail).length)) ≠
      jPole
        (jUpper (10 ^ β) (code (true :: targetTail)) (10 ^ (true :: targetTail).length))
        (jLower (10 ^ β) (normalizedLower (true :: targetTail) [false]) 1) := by
  let middleTail := List.replicate (deletions + suffix.length) true
  have upper_eq :
      cBlockUpper β (List.replicate deletions false ++ true :: suffix) =
        true :: middleTail := by
    rw [cBlockUpper_eq_replicate]
    simp only [List.length_append, List.length_replicate, List.length_cons]
    rw [show deletions + (suffix.length + 1) =
      deletions + suffix.length + 1 by omega, List.replicate_succ]
  have lower_bound :=
    ruleBearing_normalizedLower_huge deletions suffix body_long body_head
  rw [upper_eq] at lower_bound ⊢
  exact encodedHugeLower_bLeading_avoids_singletonPole sourceTail middleTail targetTail
    beta_large lower_bound

theorem phaseWord_allDeletion_or_ruleSplit (phases : List Bool) :
    phases = List.replicate phases.length false ∨
      ∃ deletions suffix,
        phases = List.replicate deletions false ++ true :: suffix := by
  induction phases with
  | nil => exact Or.inl rfl
  | cons phase phases ih =>
      cases phase with
      | false =>
          rcases ih with all_deletion | ⟨deletions, suffix, rule_split⟩
          · exact Or.inl (by
              rw [List.length_cons, List.replicate_succ]
              exact congrArg (false :: ·) all_deletion)
          · exact Or.inr ⟨deletions + 1, suffix, by
              rw [rule_split, List.replicate_succ]
              rfl⟩
      | true => exact Or.inr ⟨0, phases, rfl⟩

/-- Every nonempty all-`c` middle phase word misses a singleton target from a `c`-leading
multi-role source. This extinguishes both long A/B shell resonances for that source prefix. -/
theorem allC_cLeading_avoids_singletonPole {β : Nat} {body : List TagLetter}
    (phases : List Bool) (sourceTail targetTail : List Bool)
    (phases_ne : phases ≠ []) (beta_large : 3 ≤ β)
    (body_long : β - 1 ≤ body.length) (body_head : body.head? = some .b) :
    jStep
        (jUpper (10 ^ β) (code (cBlockUpper β phases))
          (10 ^ (cBlockUpper β phases).length))
        (jLower (10 ^ β)
          (normalizedLower (cBlockUpper β phases) (cBlockLower β body phases)) 1)
        (jUpper (10 ^ β) (code (true :: true :: sourceTail))
          (10 ^ (true :: true :: sourceTail).length)) ≠
      jPole
        (jUpper (10 ^ β) (code (true :: targetTail)) (10 ^ (true :: targetTail).length))
        (jLower (10 ^ β) (normalizedLower (true :: targetTail) [false]) 1) := by
  rcases phaseWord_allDeletion_or_ruleSplit phases with all_deletion |
    ⟨deletions, suffix, rule_split⟩
  · have length_ne : phases.length ≠ 0 :=
      Nat.ne_of_gt (List.length_pos_iff.mpr phases_ne)
    obtain ⟨width, length_eq⟩ := Nat.exists_eq_succ_of_ne_zero length_ne
    have phases_eq : phases = List.replicate (width + 1) false := by
      rw [all_deletion, length_eq]
    rw [phases_eq]
    exact allDeletion_avoids_singletonPole β body width (true :: sourceTail)
      targetTail (thousand_le_ten_pow beta_large)
  · rw [rule_split]
    exact ruleBearing_cLeading_avoids_singletonPole deletions suffix sourceTail targetTail
      beta_large body_long body_head

/-- Every nonempty all-`c` middle phase word misses a singleton target from a `b`-leading
source. Together with `allC_cLeading_avoids_singletonPole`, this extinguishes the A/B family. -/
theorem allC_bLeading_avoids_singletonPole {β : Nat} {body : List TagLetter}
    (phases : List Bool) (sourceTail targetTail : List Bool)
    (phases_ne : phases ≠ []) (beta_large : 3 ≤ β)
    (body_long : β - 1 ≤ body.length) (body_head : body.head? = some .b) :
    jStep
        (jUpper (10 ^ β) (code (cBlockUpper β phases))
          (10 ^ (cBlockUpper β phases).length))
        (jLower (10 ^ β)
          (normalizedLower (cBlockUpper β phases) (cBlockLower β body phases)) 1)
        (jUpper (10 ^ β) (code (bTag β ++ sourceTail))
          (10 ^ (bTag β ++ sourceTail).length)) ≠
      jPole
        (jUpper (10 ^ β) (code (true :: targetTail)) (10 ^ (true :: targetTail).length))
        (jLower (10 ^ β) (normalizedLower (true :: targetTail) [false]) 1) := by
  rcases phaseWord_allDeletion_or_ruleSplit phases with all_deletion |
    ⟨deletions, suffix, rule_split⟩
  · have length_ne : phases.length ≠ 0 :=
      Nat.ne_of_gt (List.length_pos_iff.mpr phases_ne)
    obtain ⟨width, length_eq⟩ := Nat.exists_eq_succ_of_ne_zero length_ne
    have phases_eq : phases = List.replicate (width + 1) false := by
      rw [all_deletion, length_eq]
    let sourceRest := List.replicate β false ++ true :: sourceTail
    have avoidance := allDeletion_avoids_singletonPole β body width sourceRest
      targetTail (thousand_le_ten_pow beta_large)
    rw [phases_eq]
    simpa [bTag, markerWord, sourceRest, List.append_assoc] using avoidance
  · rw [rule_split]
    exact ruleBearing_bLeading_avoids_singletonPole deletions suffix sourceTail targetTail
      beta_large body_long body_head

/-- Neary's compiler discharges every body hypothesis used by the A/B chamber. -/
theorem compilerBody_resonanceEnvelope {period : Nat}
    (system : CyclicTag period) (input : List Bool) (haltPhase : Fin period)
    (period_pos : 0 < period) :
    let β := NearyCompiler.deletionWidth period
    let body := NearyCompiler.body system input haltPhase period_pos
    3 ≤ β ∧ β - 1 ≤ body.length ∧ body.head? = some .b := by
  dsimp only
  have body_long :
      NearyCompiler.deletionWidth period - 1 ≤
        (NearyCompiler.body system input haltPhase period_pos).length := by
    simpa using
      (NearyArithmeticEnvelope.body_long
        (NearyCompiler.arithmeticEnvelope system input haltPhase period_pos))
  exact ⟨NearyCompiler.deletionWidth_large period_pos, body_long,
    NearyCompiler.body_head_b system input haltPhase period_pos⟩

end MatrixMortality.DecimalSetterResonance
