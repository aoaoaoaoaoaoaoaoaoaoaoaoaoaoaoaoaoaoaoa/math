import MatrixMortality.DecimalSetterThreeBlockSingletonPrefix

/-!
# Three-block singleton-next extinction

A singleton erasure block over a physical root never supplies decimal-unit peeled ancestry.
The `D_b` case is separated from every singleton pole by a quotient-one wall. In the `D_c`
case, non-unit ancestry forces a short all-`c` current, whose pole equation has incompatible
two- and five-adic balances. Thus both non-root blocks in every lawful three-block singleton
pole are multi-role.
-/

namespace MatrixMortality.DecimalSetterBridgeRay

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterBridge
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterMatrix
open MatrixMortality.PadicValuation

/-- At a singleton pole, every erasure-ended current sees an older quotient above one.

The punctuated upper code starts with a physical decimal digit, so its product with the target
trace strictly dominates the pole correction. After cancellation in the exact ray recurrence,
this is precisely positivity of the older quotient minus one. -/
theorem singletonPole_erasureCurrent_olderRatio_gt_one
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    {rest : List (List NearyTile)} (current_ends : EndsInErase current)
    (tail_law : BlocksLaw (next :: rest))
    (pole : HitsSquarePole β body [.erase targetLetter]
      (current :: next :: rest)) :
    1 < (parsedRay β body (next :: rest)).2 /
      (parsedRay β body (next :: rest)).1 := by
  have β_pos : 0 < β := by omega
  let ray := parsedRay β body (next :: rest)
  let x := ray.1
  let y := ray.2
  let q := y / x
  let ρ : ℚ := 10 ^ β
  let E := gap ρ
  let G := lift ρ
  let μ := DecimalSetterMatrix.marker β
  let T := boundaryTrace β body current
  let P := upperBoundaryCode β current
  let V := lowerBoundaryCode β body current
  let A := upperScale β current
  let S := singletonTrace β targetLetter
  let upperWord := spell (nearyUpper β) current ++ nearyMarker β
  let m := (spell (nearyUpper β) current).length
  have q_pos : 0 < q := by
    simpa only [q, x, y, ray] using
      singletonPole_olderRatio_pos β_large body targetLetter current_ends tail_law pole
  have x_ne : x ≠ 0 := by
    intro x_zero
    simp [q, x_zero] at q_pos
  have E_pos : 0 < E := by
    dsimp only [E, ρ]
    unfold gap
    have rho_bound : (1000 : ℚ) ≤ (10 : ℚ) ^ β := by
      have natural_bound : 10 ^ 3 ≤ 10 ^ β :=
        Nat.pow_le_pow_right (by norm_num) β_large
      norm_num at natural_bound ⊢
      exact_mod_cast natural_bound
    linarith
  have G_pos : 0 < G := by
    dsimp only [G, ρ]
    unfold lift
    have rho_bound : (1000 : ℚ) ≤ (10 : ℚ) ^ β := by
      have natural_bound : 10 ^ 3 ≤ 10 ^ β :=
        Nat.pow_le_pow_right (by norm_num) β_large
      norm_num at natural_bound ⊢
      exact_mod_cast natural_bound
    linarith
  have μ_pos : 0 < μ := by
    simpa only [μ] using DecimalSetterMatrix.marker_pos β
  have V_ne : V ≠ 0 := by
    simpa only [V] using
      (lowerBoundaryCode_hasDecimalShell_of_endsInErase β body current_ends).1.1
  have V_nonneg : 0 ≤ V := by
    dsimp only [V, lowerBoundaryCode]
    positivity
  have V_pos : 0 < V := lt_of_le_of_ne V_nonneg (Ne.symm V_ne)
  have A_pos : 0 < A := by
    simp [A, upperScale]
  have S_pos : 0 < S := by
    have target_lower :=
      two_mul_tenPow_lift_le_singletonTrace β_large targetLetter
    have rho_pos : (0 : ℚ) < ρ := by positivity
    have target_base_pos : 0 < 2 * ρ * G := by positivity
    exact target_base_pos.trans_le (by simpa only [ρ, G, S] using target_lower)
  have upperWord_ne : upperWord ≠ [] := by
    simp [upperWord, nearyMarker]
  obtain ⟨first, tail, upperWord_eq⟩ := List.exists_cons_of_ne_nil upperWord_ne
  have upperWord_length : upperWord.length = m + β + 1 := by
    simp [upperWord, m, nearyMarker]
    omega
  have tail_length : tail.length = m + β := by
    simpa [upperWord_eq] using upperWord_length
  have P_lower_nat : 5 * 10 ^ (m + β) ≤ code upperWord := by
    rw [upperWord_eq]
    simpa only [tail_length] using five_mul_pow_length_le_code first tail
  have P_lower : (5 : ℚ) * ρ * A ≤ P := by
    have cast_lower : (5 : ℚ) * 10 ^ (m + β) ≤ code upperWord := by
      exact_mod_cast P_lower_nat
    rw [pow_add] at cast_lower
    simpa only [P, upperBoundaryCode, upperWord, ρ, A, upperScale,
      mul_assoc, mul_left_comm, mul_comm] using cast_lower
  have P_pos : 0 < P := lt_of_lt_of_le (by positivity) P_lower
  have marker_bound_nat : code (nearyMarker β) < 10 ^ (β + 1) :=
    code_lt_pow_length (nearyMarker β) |>.trans_eq (by simp [nearyMarker])
  have μ_upper : μ < 10 * ρ := by
    have rational_bound :
        (code (nearyMarker β) : ℚ) < (10 : ℚ) ^ (β + 1) := by
      exact_mod_cast marker_bound_nat
    rw [pow_succ] at rational_bound
    simpa only [μ, DecimalSetterMatrix.marker, ρ, mul_comm] using rational_bound
  have rho_bound : (1000 : ℚ) ≤ ρ := by
    have natural_bound : 10 ^ 3 ≤ 10 ^ β :=
      Nat.pow_le_pow_right (by norm_num) β_large
    norm_num at natural_bound ⊢
    simpa only [ρ] using (show (1000 : ℚ) ≤ (10 : ℚ) ^ β by
      exact_mod_cast natural_bound)
  have rho_pos : 0 < ρ := lt_of_lt_of_le (by norm_num) rho_bound
  have target_lower : 2 * ρ * G ≤ S := by
    simpa only [ρ, G, S] using
      two_mul_tenPow_lift_le_singletonTrace β_large targetLetter
  have product_lower : 10 * ρ ^ 2 * G * A ≤ P * S := by
    have multiplied := mul_le_mul P_lower target_lower (by positivity) P_pos.le
    nlinarith
  have marker_correction_upper : 7 * μ * G * A < 70 * ρ * G * A := by
    have scaled := mul_lt_mul_of_pos_right μ_upper (show 0 < 7 * G * A by positivity)
    nlinarith
  have growth : 70 * ρ * G * A < 10 * ρ ^ 2 * G * A := by
    have rho_growth : (70 : ℚ) * ρ < 10 * ρ ^ 2 := by nlinarith
    have scaled := mul_lt_mul_of_pos_right rho_growth (show 0 < G * A by positivity)
    nlinarith
  have coefficient_pos : 0 < P * S - 7 * μ * G * A := by
    have correction_lt := marker_correction_upper.trans (growth.trans_le product_lower)
    linarith
  have G_ne : G ≠ 0 := ne_of_gt G_pos
  have S_ne : S ≠ 0 := ne_of_gt S_pos
  have pole_equation :=
    (hitsSquarePole_singleton_cons_iff_rayRecurrence β_pos body targetLetter
      current next rest).mp pole
  change (T * x - G * V * y) * S = E * μ * G * A * x * 7 at pole_equation
  have quotient_formula :
      q = T / (G * V) - E * μ * A * 7 / (S * V) := by
    dsimp only [q]
    field_simp [x_ne, G_ne, V_ne, S_ne]
    linear_combination -pole_equation
  have trace_eq : T = E * P + G * V := rfl
  have difference_formula :
      q - 1 = E * (P * S - 7 * μ * G * A) / (G * V * S) := by
    rw [quotient_formula, trace_eq]
    field_simp [G_ne, V_ne, S_ne]
    ring
  have difference_pos : 0 < q - 1 := by
    rw [difference_formula]
    exact div_pos (mul_pos E_pos coefficient_pos) (by positivity)
  simpa only [q, x, y, ray] using (sub_pos.mp difference_pos)

/-- A singleton `D_b` block over any physical root has quotient below one. -/
theorem parsedRay_singletonB_root_ratio_lt_one
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (root : List NearyTile) :
    (parsedRay β body [[.erase .b], root]).2 /
        (parsedRay β body [[.erase .b], root]).1 < 1 := by
  have β_pos : 0 < β := by omega
  let ρ : ℚ := 10 ^ β
  let E := gap ρ
  let G := lift ρ
  let μ := DecimalSetterMatrix.marker β
  let q := (rootRay β root).2 / (rootRay β root).1
  let K := singletonTrace β .b - 7 * G * q
  let N := upperScale β [.erase .b] * E * μ
  have rho_bound : (1000 : ℚ) ≤ ρ := by
    have natural_bound : 10 ^ 3 ≤ 10 ^ β :=
      Nat.pow_le_pow_right (by norm_num) β_large
    norm_num at natural_bound ⊢
    simpa only [ρ] using (show (1000 : ℚ) ≤ (10 : ℚ) ^ β by
      exact_mod_cast natural_bound)
  have rho_pos : 0 < ρ := lt_of_lt_of_le (by norm_num) rho_bound
  have E_pos : 0 < E := by
    dsimp only [E]
    unfold gap
    linarith
  have G_pos : 0 < G := by
    dsimp only [G]
    unfold lift
    linarith
  have μ_pos : 0 < μ := by
    simpa only [μ] using DecimalSetterMatrix.marker_pos β
  have q_lt : q < 2 := by
    simpa only [q] using rootRay_ratio_lt_two β root
  have q_scaled : 7 * G * q < 14 * G := by
    have scaled := mul_lt_mul_of_pos_left q_lt (show 0 < 7 * G by positivity)
    nlinarith
  have marker_eq : μ = (52 * ρ - 7) / 9 := by
    have relation := DecimalSetterMatrix.marker_relation β
    change 9 * μ = 52 * ρ - 7 at relation
    linarith
  let H := 5200 * ρ ^ 2 - 18398 * ρ + 2443
  have trace_eq : singletonTrace β .b = 2 * ρ * H := by
    simpa only [ρ, H] using singletonBTrace_eq β
  have scale_eq : upperScale β [.erase .b] = 100 * ρ := by
    simp [upperScale, spell, nearyUpper, tagCode, ρ, pow_add]
    ring
  have N_pos : 0 < N := by
    dsimp only [N]
    exact mul_pos (mul_pos (by simpa only [scale_eq] using
      (show (0 : ℚ) < 100 * ρ by positivity)) E_pos) μ_pos
  have N_lt_trace_minus : N < 2 * ρ * H - 14 * G := by
    dsimp only [N]
    rw [scale_eq, marker_eq]
    dsimp only [E, G, H]
    unfold gap lift
    nlinarith
  have N_lt_K : N < K := by
    dsimp only [K]
    rw [trace_eq]
    linarith
  have K_pos : 0 < K := N_pos.trans N_lt_K
  have root_fst_ne : (rootRay β root).1 ≠ 0 :=
    (rootRay_fst_hasDecimalShell β_pos root).1.1
  have ratio_eq :
      (parsedRay β body [[.erase .b], root]).2 /
          (parsedRay β body [[.erase .b], root]).1 = N / K := by
    simpa only [parsedRay, N, K, E, G, μ, q, ρ] using
      rayStep_singleton_ratio_eq β_pos body .b (rootRay β root)
        root_fst_ne (ne_of_gt K_pos)
  rw [ratio_eq]
  rw [div_lt_iff₀ K_pos]
  simpa using N_lt_K

/-- No lawful three-block singleton pole has an intervening singleton `D_b` block. The physical
tail quotient is below one, while the pole equation forces it above one. -/
theorem singletonPole_threeBlock_singletonBNext_impossible
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current root : List NearyTile}
    (source_law : BlocksLaw [current, [.erase .b], root]) :
    ¬HitsSquarePole β body [.erase targetLetter]
      [current, [.erase .b], root] := by
  intro pole
  have ratio_lower :=
    singletonPole_erasureCurrent_olderRatio_gt_one
      β_large body targetLetter source_law.1 source_law.2 pole
  have ratio_upper := parsedRay_singletonB_root_ratio_lt_one β_large body root
  exact (not_lt_of_ge ratio_lower.le) ratio_upper

/-- A singleton erasure block over a physical root never has decimal-unit peeled ancestry.

For `D_c`, both terms of the new numerator have positive two-adic valuation, whereas unit
ancestry would make that numerator a decimal unit. For `D_b`, a root depth at most `β` fixes
the two-adic numerator depth below `β+1`; a larger root depth fixes its five-adic depth at `β`.
Both alternatives contradict the depth `β+1` required by unit ancestry. -/
theorem parsedRay_singleton_root_not_admitsUnitPeeledCarrier
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (nextLetter : TagLetter) {root : List NearyTile}
    (root_ends : EndsInRule root) :
    ¬AdmitsUnitPeeledCarrier β
      (parsedRay β body [[.erase nextLetter], root]) := by
  intro ancestry
  let r := (spell (nearyUpper β) root).length
  let oldRay := rootRay β root
  let ray := parsedRay β body [[.erase nextLetter], root]
  let C := singletonTrace β nextLetter
  let E := gap ((10 : ℚ) ^ β)
  let G := lift ((10 : ℚ) ^ β)
  let μ := DecimalSetterMatrix.marker β
  let numerator := C * oldRay.1 - G * 7 * oldRay.2
  let denominator := E * μ
  let a := (spell (nearyUpper β) [.erase nextLetter]).length
  have r_pos : 0 < r := by
    obtain ⟨front, letter, root_eq⟩ := root_ends
    have upper_ne : spell (nearyUpper β) root ≠ [] := by
      rw [root_eq, spell_append]
      simp [spell, nearyUpper_ne_nil]
    exact List.length_pos_of_ne_nil upper_ne
  obtain ⟨ray_first_ne, ratio_shell⟩ :=
    (admitsUnitPeeledCarrier_iff_ratio_hasDecimalShell β_pos ray).mp ancestry
  have old_first_shell : HasDecimalShell oldRay.1 0 0 := by
    simpa only [oldRay] using rootRay_fst_hasDecimalShell β_pos root
  have old_second_shell : HasDecimalShell oldRay.2 r r := by
    simpa only [oldRay, r] using rootRay_snd_hasDecimalShell β root
  have trace_shell : HasDecimalShell C (β + 1) β := by
    simpa only [C] using singletonTrace_hasDecimalShell β_pos nextLetter
  have trace_term_shell : HasDecimalShell (C * oldRay.1) (β + 1) β := by
    convert trace_shell.mul old_first_shell using 1 <;> simp
  have seven_unit : HasDecimalShell (7 : ℚ) 0 0 :=
    intCast_hasDecimalShell_of_mod_seven (Int.ModEq.refl 7)
  have lower_term_shell : HasDecimalShell (G * 7 * oldRay.2) r r := by
    simpa only [G, zero_add] using
      ((lift_tenPow_hasDecimalShell β_pos).mul seven_unit).mul old_second_shell
  have denominator_unit : HasDecimalShell denominator 0 0 := by
    simpa only [denominator, E, μ, zero_add] using
      (gap_tenPow_hasDecimalShell β_pos).mul (marker_hasDecimalShell β_pos)
  have scale_shell : HasDecimalShell (upperScale β [.erase nextLetter]) a a := by
    have shell := ten_hasDecimalShell.pow a
    norm_num at shell
    simpa only [upperScale, a] using shell
  have ray_second_shell : HasDecimalShell ray.2 a a := by
    have shell := scale_shell.mul old_first_shell
    convert shell using 1 <;> simp [ray, oldRay, parsedRay, rayStep]
  have ray_second_ne : ray.2 ≠ 0 := ray_second_shell.1.1
  have ray_first_eq : ray.1 = ray.2 / (ray.2 / ray.1) := by
    field_simp [ray_first_ne, ray_second_ne]
  have ray_first_shell : HasDecimalShell ray.1 (a - 1) (a - 1) := by
    rw [ray_first_eq]
    exact ⟨div_hasValue ray_second_shell.1 ratio_shell.1,
      div_hasValue ray_second_shell.2 ratio_shell.2⟩
  have ray_first_formula : ray.1 = numerator / denominator := by
    simp [ray, parsedRay, rayStep, numerator, denominator, C, E, G, μ,
      oldRay, boundaryTrace, singletonTrace, lowerBoundaryCode, spell,
      nearyLower, code, digit, mul_left_comm, mul_comm]
  have numerator_ne : numerator ≠ 0 := by
    intro numerator_zero
    apply ray_first_ne
    rw [ray_first_formula, numerator_zero, zero_div]
  cases nextLetter with
  | c =>
      have ray_first_unit : HasDecimalShell ray.1 0 0 := by
        simpa [a, spell, nearyUpper, tagCode] using ray_first_shell
      have numerator_two_lower : (1 : ℤ) ≤ padicValRat 2 numerator := by
        have raw := padicValRat.min_le_padicValRat_add (p := 2)
          (show C * oldRay.1 + -(G * 7 * oldRay.2) ≠ 0 by
            simpa only [numerator, sub_eq_add_neg] using numerator_ne)
        rw [trace_term_shell.1.2, padicValRat.neg, lower_term_shell.1.2] at raw
        have one_le_min : (1 : ℤ) ≤ min ((β : ℤ) + 1) r :=
          le_min (by omega) (by exact_mod_cast r_pos)
        exact one_le_min.trans (by
          simpa only [numerator, sub_eq_add_neg] using raw)
      have numerator_two_zero : padicValRat 2 numerator = 0 := by
        have first_depth := ray_first_unit.1.2
        rw [ray_first_formula, padicValRat.div numerator_ne denominator_unit.1.1,
          denominator_unit.1.2] at first_depth
        omega
      omega
  | b =>
      have ray_first_depth : HasDecimalShell ray.1 (β + 1) (β + 1) := by
        simpa [a, spell, nearyUpper, tagCode] using ray_first_shell
      by_cases r_small : r ≤ β
      · have numerator_two : HasValue 2 numerator r := by
          have shell := sub_hasValue_min trace_term_shell.1.1 lower_term_shell.1.1 (by
            rw [trace_term_shell.1.2, lower_term_shell.1.2]
            omega)
          rw [trace_term_shell.1.2, lower_term_shell.1.2,
            min_eq_right (show (r : ℤ) ≤ β + 1 by omega)] at shell
          simpa only [numerator] using shell
        have ray_first_two : HasValue 2 ray.1 r := by
          rw [ray_first_formula]
          have shell := div_hasValue numerator_two denominator_unit.1
          simpa using shell
        have depth_eq : (r : ℤ) = β + 1 :=
          ray_first_two.2.symm.trans ray_first_depth.1.2
        omega
      · have β_lt_r : β < r := by omega
        have numerator_five : HasValue 5 numerator β := by
          have shell := sub_hasValue_min trace_term_shell.2.1 lower_term_shell.2.1 (by
            rw [trace_term_shell.2.2, lower_term_shell.2.2]
            omega)
          rw [trace_term_shell.2.2, lower_term_shell.2.2,
            min_eq_left (show (β : ℤ) ≤ r by omega)] at shell
          simpa only [numerator] using shell
        have ray_first_five : HasValue 5 ray.1 β := by
          rw [ray_first_formula]
          have shell := div_hasValue numerator_five denominator_unit.2
          simpa using shell
        have depth_eq : (β : ℤ) = β + 1 :=
          ray_first_five.2.symm.trans ray_first_depth.2.2
        omega

/-- At any lawful three-block singleton pole with singleton intervening block, a multi-role
current is forced into the short marker-free all-`c` chamber. -/
theorem singletonPole_threeBlock_singletonNext_forces_shortAllC
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter nextLetter : TagLetter) {current root : List NearyTile}
    (source_law : BlocksLaw [current, [.erase nextLetter], root])
    (current_multi : 2 ≤ current.length)
    (pole : HitsSquarePole β body [.erase targetLetter]
      [current, [.erase nextLetter], root]) :
    current.length ≤ β + 2 ∧
      current.map NearyTile.letter = List.replicate current.length .c := by
  have current_ends : EndsInErase current := source_law.1
  have tail_law : BlocksLaw [[.erase nextLetter], root] := source_law.2
  have root_ends : EndsInRule root := source_law.2.2
  have no_ancestry :
      ¬AdmitsUnitPeeledCarrier β
        (parsedRay β body [[.erase nextLetter], root]) :=
    parsedRay_singleton_root_not_admitsUnitPeeledCarrier
      (by omega) body nextLetter root_ends
  have short_grammar :=
    (singletonPole_tail_not_admitsUnitPeeledCarrier_iff_singleton_or_shortAllC
      β_large body targetLetter current_ends tail_law pole).mp no_ancestry
  rcases short_grammar with current_singleton |
      ⟨_, current_width, current_letters⟩
  · omega
  · exact ⟨current_width, current_letters⟩

/-- No lawful three-block singleton pole with multi-role current has an intervening singleton
`D_c` block. Non-unit ancestry first makes the current a short all-`c` block. The pole equation
then forces the older ray's two- and five-adic numerator depths to differ by one. A root shallower
than `β` gives equal depths, while a root of depth at least `β` makes the five-adic depth too
large. -/
theorem singletonPole_threeBlock_singletonCNext_multiCurrent_impossible
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current root : List NearyTile}
    (source_law : BlocksLaw [current, [.erase .c], root])
    (current_multi : 2 ≤ current.length) :
    ¬HitsSquarePole β body [.erase targetLetter]
      [current, [.erase .c], root] := by
  intro pole
  have β_pos : 0 < β := by omega
  obtain ⟨current_width, current_letters⟩ :=
    singletonPole_threeBlock_singletonNext_forces_shortAllC
      β_large body targetLetter .c source_law current_multi pole
  have current_ends : EndsInErase current := source_law.1
  have root_ends : EndsInRule root := source_law.2.2
  let m := (spell (nearyUpper β) current).length
  let r := (spell (nearyUpper β) root).length
  let oldRay := rootRay β root
  let ray := parsedRay β body [[.erase .c], root]
  let x := ray.1
  let y := ray.2
  let C := singletonTrace β .c
  let E := gap ((10 : ℚ) ^ β)
  let G := lift ((10 : ℚ) ^ β)
  let μ := DecimalSetterMatrix.marker β
  let numerator := C * oldRay.1 - G * 7 * oldRay.2
  let denominator := E * μ
  let T := boundaryTrace β body current
  let V := lowerBoundaryCode β body current
  let A := upperScale β current
  let S := singletonTrace β targetLetter
  let R := T * x - G * V * y
  let xTwo := padicValRat 2 x
  let xFive := padicValRat 5 x
  have m_eq : m = current.length := by
    dsimp only [m]
    rw [spell_nearyUpper,
      MatrixMortality.DecimalSetterAncestry.tagEncode_length_eq_roleLength_add_markerCount,
      current_letters]
    simp [List.count_replicate]
  have m_two_le : 2 ≤ m := by omega
  have m_upper : m ≤ β + 2 := by omega
  have r_pos : 0 < r := by
    obtain ⟨front, letter, root_eq⟩ := root_ends
    have upper_ne : spell (nearyUpper β) root ≠ [] := by
      rw [root_eq, spell_append]
      simp [spell, nearyUpper_ne_nil]
    exact List.length_pos_of_ne_nil upper_ne
  have old_first_shell : HasDecimalShell oldRay.1 0 0 := by
    simpa only [oldRay] using rootRay_fst_hasDecimalShell β_pos root
  have old_second_shell : HasDecimalShell oldRay.2 r r := by
    simpa only [oldRay, r] using rootRay_snd_hasDecimalShell β root
  have next_trace_shell : HasDecimalShell C (β + 1) β := by
    simpa only [C] using singletonTrace_hasDecimalShell β_pos .c
  have next_trace_term_shell :
      HasDecimalShell (C * oldRay.1) (β + 1) β := by
    convert next_trace_shell.mul old_first_shell using 1 <;> simp
  have seven_unit : HasDecimalShell (7 : ℚ) 0 0 :=
    intCast_hasDecimalShell_of_mod_seven (Int.ModEq.refl 7)
  have next_lower_term_shell : HasDecimalShell (G * 7 * oldRay.2) r r := by
    simpa only [G, zero_add] using
      ((lift_tenPow_hasDecimalShell β_pos).mul seven_unit).mul old_second_shell
  have denominator_unit : HasDecimalShell denominator 0 0 := by
    simpa only [denominator, E, μ, zero_add] using
      (gap_tenPow_hasDecimalShell β_pos).mul (marker_hasDecimalShell β_pos)
  have ray_second_shell : HasDecimalShell y 1 1 := by
    have scale_shell : HasDecimalShell (upperScale β [.erase .c]) 1 1 := by
      simpa [upperScale, spell, nearyUpper, tagCode] using ten_hasDecimalShell
    have shell := scale_shell.mul old_first_shell
    convert shell using 1 <;> simp [y, ray, oldRay, parsedRay, rayStep]
  have y_ne : y ≠ 0 := ray_second_shell.1.1
  have V_ne : V ≠ 0 := by
    simpa only [V] using
      (lowerBoundaryCode_hasDecimalShell_of_endsInErase β body current_ends).1.1
  have S_ne : S ≠ 0 := by
    simpa only [S] using (singletonTrace_hasDecimalShell β_pos targetLetter).1.1
  have G_ne : G ≠ 0 := by
    simpa only [G] using (lift_tenPow_hasDecimalShell β_pos).1.1
  have pole_equation :=
    (hitsSquarePole_singleton_cons_iff_rayRecurrence β_pos body targetLetter
      current [.erase .c] [root]).mp pole
  change R * S = E * μ * G * A * x * 7 at pole_equation
  have x_ne : x ≠ 0 := by
    intro x_zero
    have left_ne : (-(G * V * y)) * S ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero G_ne V_ne) y_ne)) S_ne
    apply left_ne
    simpa only [R, x_zero, mul_zero, zero_sub, zero_mul] using pole_equation
  have ray_first_formula : x = numerator / denominator := by
    simp [x, ray, parsedRay, rayStep, numerator, denominator, C, E, G, μ,
      oldRay, boundaryTrace, singletonTrace, lowerBoundaryCode, spell,
      nearyLower, code, digit, mul_left_comm, mul_comm]
  have numerator_ne : numerator ≠ 0 := by
    intro numerator_zero
    apply x_ne
    rw [ray_first_formula, numerator_zero, zero_div]
  have numerator_two_lower : (1 : ℤ) ≤ padicValRat 2 numerator := by
    have raw := padicValRat.min_le_padicValRat_add (p := 2)
      (show C * oldRay.1 + -(G * 7 * oldRay.2) ≠ 0 by
        simpa only [numerator, sub_eq_add_neg] using numerator_ne)
    rw [next_trace_term_shell.1.2, padicValRat.neg,
      next_lower_term_shell.1.2] at raw
    have lower : (1 : ℤ) ≤ min ((β : ℤ) + 1) r :=
      le_min (by omega) (by exact_mod_cast r_pos)
    exact lower.trans (by simpa only [numerator, sub_eq_add_neg] using raw)
  have numerator_five_lower : (1 : ℤ) ≤ padicValRat 5 numerator := by
    have raw := padicValRat.min_le_padicValRat_add (p := 5)
      (show C * oldRay.1 + -(G * 7 * oldRay.2) ≠ 0 by
        simpa only [numerator, sub_eq_add_neg] using numerator_ne)
    rw [next_trace_term_shell.2.2, padicValRat.neg,
      next_lower_term_shell.2.2] at raw
    have lower : (1 : ℤ) ≤ min (β : ℤ) r :=
      le_min (by omega) (by exact_mod_cast r_pos)
    exact lower.trans (by simpa only [numerator, sub_eq_add_neg] using raw)
  have xTwo_lower : (1 : ℤ) ≤ xTwo := by
    dsimp only [xTwo]
    rw [ray_first_formula, padicValRat.div numerator_ne denominator_unit.1.1,
      denominator_unit.1.2]
    omega
  have xFive_lower : (1 : ℤ) ≤ xFive := by
    dsimp only [xFive]
    rw [ray_first_formula, padicValRat.div numerator_ne denominator_unit.2.1,
      denominator_unit.2.2]
    omega
  have x_two : HasValue 2 x xTwo := ⟨x_ne, rfl⟩
  have x_five : HasValue 5 x xFive := ⟨x_ne, rfl⟩
  have current_trace_shell : HasDecimalShell T 1 1 := by
    simpa only [T, boundaryTrace] using
      MatrixMortality.DecimalSetterShallow.multiRoleErasureEnded_boundaryTrace_hasDecimalShell
        (show 2 ≤ β by omega) body current_multi current_ends
  have current_lower_unit : HasDecimalShell V 0 0 := by
    simpa only [V] using
      lowerBoundaryCode_hasDecimalShell_of_endsInErase β body current_ends
  have trace_term_two : HasValue 2 (T * x) (xTwo + 1) := by
    simpa [add_comm] using mul_hasValue current_trace_shell.1 x_two
  have trace_term_five : HasValue 5 (T * x) (xFive + 1) := by
    simpa [add_comm] using mul_hasValue current_trace_shell.2 x_five
  have lower_term_shell : HasDecimalShell (G * V * y) 1 1 := by
    simpa only [G, zero_add] using
      ((lift_tenPow_hasDecimalShell β_pos).mul current_lower_unit).mul ray_second_shell
  have residual_two : HasValue 2 R 1 := by
    have shell := sub_hasValue_min trace_term_two.1 lower_term_shell.1.1 (by
      rw [trace_term_two.2, lower_term_shell.1.2]
      omega)
    rw [trace_term_two.2, lower_term_shell.1.2,
      min_eq_right (show (1 : ℤ) ≤ xTwo + 1 by omega)] at shell
    simpa only [R] using shell
  have residual_five : HasValue 5 R 1 := by
    have shell := sub_hasValue_min trace_term_five.1 lower_term_shell.2.1 (by
      rw [trace_term_five.2, lower_term_shell.2.2]
      omega)
    rw [trace_term_five.2, lower_term_shell.2.2,
      min_eq_right (show (1 : ℤ) ≤ xFive + 1 by omega)] at shell
    simpa only [R] using shell
  have target_shell : HasDecimalShell S (β + 1) β := by
    simpa only [S] using singletonTrace_hasDecimalShell β_pos targetLetter
  have left_two : HasValue 2 (R * S) (β + 2) := by
    have shell := mul_hasValue residual_two target_shell.1
    convert shell using 1
    omega
  have left_five : HasValue 5 (R * S) (β + 1) := by
    have shell := mul_hasValue residual_five target_shell.2
    convert shell using 1
    omega
  have scale_shell : HasDecimalShell A m m := by
    have shell := ten_hasDecimalShell.pow m
    norm_num at shell
    simpa only [A, upperScale, m] using shell
  have right_two : HasValue 2 (E * μ * G * A * x * 7) (m + xTwo) := by
    have prefix_shell := (((gap_tenPow_hasDecimalShell β_pos).mul
      (marker_hasDecimalShell β_pos)).mul
        (lift_tenPow_hasDecimalShell β_pos)).mul scale_shell
    have shell := mul_hasValue (mul_hasValue prefix_shell.1 x_two) seven_unit.1
    simpa [add_assoc] using shell
  have right_five : HasValue 5 (E * μ * G * A * x * 7) (m + xFive) := by
    have prefix_shell := (((gap_tenPow_hasDecimalShell β_pos).mul
      (marker_hasDecimalShell β_pos)).mul
        (lift_tenPow_hasDecimalShell β_pos)).mul scale_shell
    have shell := mul_hasValue (mul_hasValue prefix_shell.2 x_five) seven_unit.2
    simpa [add_assoc] using shell
  have two_balance : (β : ℤ) + 2 = m + xTwo := by
    have balance := congrArg (padicValRat 2) pole_equation
    rw [left_two.2, right_two.2] at balance
    exact balance
  have five_balance : (β : ℤ) + 1 = m + xFive := by
    have balance := congrArg (padicValRat 5) pole_equation
    rw [left_five.2, right_five.2] at balance
    exact balance
  have xFive_upper : xFive ≤ (β : ℤ) - 1 := by omega
  by_cases root_deep : β ≤ r
  · have numerator_five_deep : (β : ℤ) ≤ padicValRat 5 numerator := by
      have raw := padicValRat.min_le_padicValRat_add (p := 5)
        (show C * oldRay.1 + -(G * 7 * oldRay.2) ≠ 0 by
          simpa only [numerator, sub_eq_add_neg] using numerator_ne)
      rw [next_trace_term_shell.2.2, padicValRat.neg,
        next_lower_term_shell.2.2] at raw
      have lower : (β : ℤ) ≤ min (β : ℤ) r :=
        le_min le_rfl (by exact_mod_cast root_deep)
      exact lower.trans (by simpa only [numerator, sub_eq_add_neg] using raw)
    have xFive_deep : (β : ℤ) ≤ xFive := by
      dsimp only [xFive]
      rw [ray_first_formula, padicValRat.div numerator_ne denominator_unit.2.1,
        denominator_unit.2.2]
      omega
    omega
  · have root_shallow : r < β := by omega
    have numerator_two : HasValue 2 numerator r := by
      have shell := sub_hasValue_min next_trace_term_shell.1.1
        next_lower_term_shell.1.1 (by
          rw [next_trace_term_shell.1.2, next_lower_term_shell.1.2]
          omega)
      rw [next_trace_term_shell.1.2, next_lower_term_shell.1.2,
        min_eq_right (show (r : ℤ) ≤ β + 1 by omega)] at shell
      simpa only [numerator] using shell
    have numerator_five : HasValue 5 numerator r := by
      have shell := sub_hasValue_min next_trace_term_shell.2.1
        next_lower_term_shell.2.1 (by
          rw [next_trace_term_shell.2.2, next_lower_term_shell.2.2]
          omega)
      rw [next_trace_term_shell.2.2, next_lower_term_shell.2.2,
        min_eq_right (show (r : ℤ) ≤ β by omega)] at shell
      simpa only [numerator] using shell
    have xTwo_eq : xTwo = r := by
      dsimp only [xTwo]
      rw [ray_first_formula, padicValRat.div numerator_two.1 denominator_unit.1.1,
        numerator_two.2, denominator_unit.1.2]
      omega
    have xFive_eq : xFive = r := by
      dsimp only [xFive]
      rw [ray_first_formula, padicValRat.div numerator_five.1 denominator_unit.2.1,
        numerator_five.2, denominator_unit.2.2]
      omega
    omega

/-- No lawful three-block singleton pole with multi-role current has a singleton intervening
block. The `D_b` case is separated by the quotient-one wall; the `D_c` case by the incompatible
two- and five-adic depth balances. -/
theorem singletonPole_threeBlock_singletonNext_multiCurrent_impossible
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter nextLetter : TagLetter) {current root : List NearyTile}
    (source_law : BlocksLaw [current, [.erase nextLetter], root])
    (current_multi : 2 ≤ current.length) :
    ¬HitsSquarePole β body [.erase targetLetter]
      [current, [.erase nextLetter], root] := by
  cases nextLetter with
  | b =>
      exact singletonPole_threeBlock_singletonBNext_impossible
        β_large body targetLetter source_law
  | c =>
      exact singletonPole_threeBlock_singletonCNext_multiCurrent_impossible
        β_large body targetLetter source_law current_multi

/-- Every lawful three-block singleton pole has a multi-role intervening block. -/
theorem singletonPole_threeBlock_forces_next_multi
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next root : List NearyTile}
    (source_law : BlocksLaw [current, next, root])
    (pole : HitsSquarePole β body [.erase targetLetter]
      [current, next, root]) :
    2 ≤ next.length := by
  have current_multi :=
    singletonPole_threeBlock_forces_current_multi
      β_large body targetLetter source_law pole
  by_contra next_not_multi
  obtain ⟨front, nextLetter, next_eq⟩ := source_law.2.1
  have front_nil : front = [] := by
    apply List.length_eq_zero_iff.mp
    have next_length : next.length = front.length + 1 := by simp [next_eq]
    omega
  have next_singleton : next = [.erase nextLetter] := by
    simpa [front_nil] using next_eq
  have singleton_law : BlocksLaw [current, [.erase nextLetter], root] := by
    simpa only [next_singleton] using source_law
  have singleton_pole :
      HitsSquarePole β body [.erase targetLetter]
        [current, [.erase nextLetter], root] := by
    simpa only [next_singleton] using pole
  exact singletonPole_threeBlock_singletonNext_multiCurrent_impossible
    β_large body targetLetter nextLetter singleton_law current_multi singleton_pole

/-- Unconditional classifier for every lawful three-block singleton pole. Both non-root blocks
are automatically multi-role. A deep root forces the intervening block to be exactly two `c`
roles and the current into the long corridor. A shallow root is `R_c`, where the discrepancy
shell is equivalent to the long corridor and its complement is the short all-`c` chamber. -/
theorem singletonPole_threeBlock_classifier
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next root : List NearyTile}
    (source_law : BlocksLaw [current, next, root])
    (pole : HitsSquarePole β body [.erase targetLetter]
      [current, next, root]) :
    (2 ≤ (spell (nearyUpper β) root).length ∧
      next.length = 2 ∧ next.map NearyTile.letter = [.c, .c] ∧
        β + 3 ≤ (spell (nearyUpper β) current).length) ∨
      (root = DecimalSetterMinimumBody.ruleCRoot ∧
        ((β + 3 ≤ (spell (nearyUpper β) current).length ∧
            HasDecimalShell
              (upperBoundaryCode β next - lowerBoundaryCode β body next)
              ((spell (nearyUpper β) next).length - 1)
              ((spell (nearyUpper β) next).length - 1)) ∨
          (current.length ≤ β + 2 ∧
            current.map NearyTile.letter = List.replicate current.length .c ∧
              ¬HasDecimalShell
                (upperBoundaryCode β next - lowerBoundaryCode β body next)
                ((spell (nearyUpper β) next).length - 1)
                ((spell (nearyUpper β) next).length - 1)))) := by
  have next_multi :=
    singletonPole_threeBlock_forces_next_multi
      β_large body targetLetter source_law pole
  exact singletonPole_threeBlock_nextMulti_classifier
    β_large body targetLetter source_law next_multi pole

end MatrixMortality.DecimalSetterBridgeRay
