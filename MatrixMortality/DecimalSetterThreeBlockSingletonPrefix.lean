import MatrixMortality.DecimalSetterThreeBlockSingletonCurrent

/-!
# Singleton prefixes above physical root rays

Every physical root quotient is below two. One singleton erasure step preserves this strict
upper chamber when `β ≥ 3`. An actual singleton pole with singleton current forces the older
quotient above two, so no three-block source can have two consecutive singleton erasure blocks.
-/

namespace MatrixMortality.DecimalSetterBridgeRay

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterBridge
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterMatrix
open MatrixMortality.PadicValuation

/-- Every physical root ray has projective quotient below two. -/
theorem rootRay_ratio_lt_two
    (β : Nat) (root : List NearyTile) :
    (rootRay β root).2 / (rootRay β root).1 < 2 := by
  let upperWord := spell (nearyUpper β) root ++ nearyMarker β
  let r := (spell (nearyUpper β) root).length
  let P : ℚ := code upperWord
  let μ := DecimalSetterMatrix.marker β
  let A : ℚ := 10 ^ r
  have upperWord_ne : upperWord ≠ [] := by
    simp [upperWord, nearyMarker]
  obtain ⟨first, tail, upperWord_eq⟩ := List.exists_cons_of_ne_nil upperWord_ne
  have upperWord_length : upperWord.length = r + β + 1 := by
    simp [upperWord, r, nearyMarker]
    omega
  have tail_length : tail.length = r + β := by
    simpa [upperWord_eq] using upperWord_length
  have P_lower_nat : 5 * 10 ^ (r + β) ≤ code upperWord := by
    rw [upperWord_eq]
    simpa only [tail_length] using five_mul_pow_length_le_code first tail
  have P_lower : (5 : ℚ) * 10 ^ (r + β) ≤ P := by
    dsimp only [P]
    exact_mod_cast P_lower_nat
  have P_pos : 0 < P := lt_of_lt_of_le (by positivity) P_lower
  have marker_bound_nat : code (nearyMarker β) < 10 ^ (β + 1) :=
    code_lt_pow_length (nearyMarker β) |>.trans_eq (by simp [nearyMarker])
  have μ_upper : μ < (10 : ℚ) ^ (β + 1) := by
    dsimp only [μ, DecimalSetterMatrix.marker]
    exact_mod_cast marker_bound_nat
  have A_pos : 0 < A := by positivity
  have numerator_upper : A * μ < 10 ^ (r + β + 1) := by
    have scaled := mul_lt_mul_of_pos_left μ_upper A_pos
    rw [show r + β + 1 = r + (β + 1) by omega, pow_add]
    simpa only [A, mul_comm] using scaled
  have twice_lower : (10 : ℚ) ^ (r + β + 1) ≤ 2 * P := by
    have scaled := mul_le_mul_of_nonneg_left P_lower (show (0 : ℚ) ≤ 2 by norm_num)
    rw [show r + β + 1 = (r + β) + 1 by omega, pow_succ]
    nlinarith
  have numerator_lt : A * μ < 2 * P := numerator_upper.trans_le twice_lower
  have marker_ne : μ ≠ 0 := by
    simpa only [μ] using ne_of_gt (DecimalSetterMatrix.marker_pos β)
  change A / (P / μ) < 2
  calc
    A / (P / μ) = A * μ / P := by field_simp [marker_ne]
    _ < 2 := (div_lt_iff₀ P_pos).2 numerator_lt

/-- Exact projective quotient after a singleton erasure step. -/
theorem rayStep_singleton_ratio_eq
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (letter : TagLetter) (ray : ℚ × ℚ)
    (ray_fst_ne : ray.1 ≠ 0)
    (_coefficient_ne :
      singletonTrace β letter - 7 * lift ((10 : ℚ) ^ β) * (ray.2 / ray.1) ≠ 0) :
    (rayStep β body [.erase letter] ray).2 /
        (rayStep β body [.erase letter] ray).1 =
      upperScale β [.erase letter] * gap ((10 : ℚ) ^ β) *
          DecimalSetterMatrix.marker β /
        (singletonTrace β letter -
          7 * lift ((10 : ℚ) ^ β) * (ray.2 / ray.1)) := by
  have gap_ne := (gap_tenPow_hasDecimalShell β_pos).1.1
  have marker_ne := (marker_hasDecimalShell β_pos).1.1
  have current_trace :
      boundaryTrace β body [.erase letter] = singletonTrace β letter := by
    simp [boundaryTrace, singletonTrace, lowerBoundaryCode, spell, nearyLower,
      code, digit, mul_comm]
  have current_lower : lowerBoundaryCode β body [.erase letter] = 7 := by
    simp [lowerBoundaryCode, spell, nearyLower, code, digit]
  rw [rayStep]
  rw [current_trace, current_lower]
  field_simp [ray_fst_ne, gap_ne, marker_ne, _coefficient_ne]

/-- A singleton erasure block above any physical root still has quotient below two. -/
theorem parsedRay_singleton_root_ratio_lt_two
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (letter : TagLetter) (root : List NearyTile) :
    (parsedRay β body [[.erase letter], root]).2 /
        (parsedRay β body [[.erase letter], root]).1 < 2 := by
  have β_pos : 0 < β := by omega
  let ρ : ℚ := 10 ^ β
  let E := gap ρ
  let G := lift ρ
  let μ := DecimalSetterMatrix.marker β
  let q := (rootRay β root).2 / (rootRay β root).1
  let K := singletonTrace β letter - 7 * G * q
  let N := upperScale β [.erase letter] * E * μ
  have rho_bound : (1000 : ℚ) ≤ ρ := by
    have natural_bound : 10 ^ 3 ≤ 10 ^ β :=
      Nat.pow_le_pow_right (by norm_num) β_large
    norm_num at natural_bound ⊢
    simpa only [ρ] using (show (1000 : ℚ) ≤ (10 : ℚ) ^ β by
      exact_mod_cast natural_bound)
  have rho_pos : 0 < ρ := lt_of_lt_of_le (by norm_num) rho_bound
  have square_growth : 1000 * ρ ≤ ρ ^ 2 := by nlinarith
  have cube_growth : 1000 * ρ ^ 2 ≤ ρ ^ 3 := by nlinarith
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
  have N_pos : 0 < N := by
    dsimp only [N]
    exact mul_pos (mul_pos (by simp [upperScale]) E_pos) μ_pos
  have N_lt_twice_K : N < 2 * K := by
    cases letter with
    | c =>
        have trace_eq : singletonTrace β .c = 2 * ρ * G := by
          simpa only [ρ, G] using singletonCTrace_eq β
        have scale_eq : upperScale β [.erase .c] = 10 := by
          simp [upperScale, spell, nearyUpper, tagCode]
        have coarse : N < 2 * (2 * ρ * G - 14 * G) := by
          dsimp only [N]
          rw [scale_eq, marker_eq]
          dsimp only [E, G]
          unfold gap lift
          nlinarith
        dsimp only [K]
        rw [trace_eq]
        nlinarith
    | b =>
        let H := 5200 * ρ ^ 2 - 18398 * ρ + 2443
        have trace_eq : singletonTrace β .b = 2 * ρ * H := by
          simpa only [ρ, H] using singletonBTrace_eq β
        have scale_eq : upperScale β [.erase .b] = 100 * ρ := by
          simp [upperScale, spell, nearyUpper, tagCode, ρ, pow_add]
          ring
        have coarse : N < 2 * (2 * ρ * H - 14 * G) := by
          dsimp only [N]
          rw [scale_eq, marker_eq]
          dsimp only [E, G, H]
          unfold gap lift
          nlinarith
        dsimp only [K]
        rw [trace_eq]
        nlinarith
  have K_pos : 0 < K := by nlinarith
  have root_fst_ne : (rootRay β root).1 ≠ 0 :=
    (rootRay_fst_hasDecimalShell β_pos root).1.1
  have ratio_eq :
      (parsedRay β body [[.erase letter], root]).2 /
          (parsedRay β body [[.erase letter], root]).1 = N / K := by
    simpa only [parsedRay, N, K, E, G, μ, q, ρ] using
      rayStep_singleton_ratio_eq β_pos body letter (rootRay β root)
        root_fst_ne (ne_of_gt K_pos)
  rw [ratio_eq]
  exact (div_lt_iff₀ K_pos).2 N_lt_twice_K

/-- At a singleton target with singleton current, every lawful older parser quotient is above
two. The bound is independent of the older history's depth and letters. -/
theorem singletonPole_singletonCurrent_olderRatio_gt_two
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter currentLetter : TagLetter) {next : List NearyTile}
    {rest : List (List NearyTile)} (tail_law : BlocksLaw (next :: rest))
    (pole : HitsSquarePole β body [.erase targetLetter]
      ([.erase currentLetter] :: next :: rest)) :
    2 < (parsedRay β body (next :: rest)).2 /
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
  let C := singletonTrace β currentLetter
  let S := singletonTrace β targetLetter
  let A := upperScale β [.erase currentLetter]
  have q_pos : 0 < q := by
    simpa only [q, x, y, ray] using
      singletonPole_olderRatio_pos β_large body targetLetter
        (current_ends := ⟨[], currentLetter, rfl⟩) tail_law pole
  have x_ne : x ≠ 0 := by
    intro x_zero
    simp [q, x_zero] at q_pos
  have G_ne : G ≠ 0 := by
    simpa only [G, ρ] using (lift_tenPow_hasDecimalShell β_pos).1.1
  have S_ne : S ≠ 0 := by
    simpa only [S] using (singletonTrace_hasDecimalShell β_pos targetLetter).1.1
  have pole_equation :=
    (hitsSquarePole_singleton_cons_iff_rayRecurrence β_pos body targetLetter
      [.erase currentLetter] next rest).mp pole
  have current_trace :
      boundaryTrace β body [.erase currentLetter] = C := by
    simp [C, boundaryTrace, singletonTrace, lowerBoundaryCode, spell, nearyLower,
      code, digit, mul_comm]
  have current_lower : lowerBoundaryCode β body [.erase currentLetter] = 7 := by
    simp [lowerBoundaryCode, spell, nearyLower, code, digit]
  change
    (boundaryTrace β body [.erase currentLetter] * x -
        G * lowerBoundaryCode β body [.erase currentLetter] * y) * S =
      E * μ * G * A * x * 7 at pole_equation
  rw [current_trace, current_lower] at pole_equation
  have quotient_formula : q = C / (7 * G) - E * μ * A / S := by
    dsimp only [q]
    field_simp [x_ne, G_ne, S_ne]
    linear_combination -pole_equation
  have rho_bound : (1000 : ℚ) ≤ ρ := by
    have natural_bound : 10 ^ 3 ≤ 10 ^ β :=
      Nat.pow_le_pow_right (by norm_num) β_large
    norm_num at natural_bound ⊢
    simpa only [ρ] using (show (1000 : ℚ) ≤ (10 : ℚ) ^ β by
      exact_mod_cast natural_bound)
  have rho_pos : 0 < ρ := lt_of_lt_of_le (by norm_num) rho_bound
  have square_growth : 1000 * ρ ≤ ρ ^ 2 := by nlinarith
  have cube_growth : 1000 * ρ ^ 2 ≤ ρ ^ 3 := by nlinarith
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
  have S_lower : 2 * ρ * G ≤ S := by
    simpa only [ρ, G, S] using
      two_mul_tenPow_lift_le_singletonTrace β_large targetLetter
  have S_pos : 0 < S := lt_of_lt_of_le (by positivity) S_lower
  have marker_eq : μ = (52 * ρ - 7) / 9 := by
    have relation := DecimalSetterMatrix.marker_relation β
    change 9 * μ = 52 * ρ - 7 at relation
    linarith
  change 2 < q
  rw [quotient_formula]
  cases currentLetter with
  | c =>
      have trace_eq : C = 2 * ρ * G := by
        simpa only [C, ρ, G] using singletonCTrace_eq β
      have scale_eq : A = 10 := by
        simp [A, upperScale, spell, nearyUpper, tagCode]
      have correction_numerator : 10 * E * μ < 2 * S := by
        have raw : 10 * E * μ < 4 * ρ * G := by
          rw [marker_eq]
          dsimp only [E, G]
          unfold gap lift
          nlinarith
        nlinarith
      have correction_upper : E * μ * A / S < 2 := by
        rw [scale_eq, div_lt_iff₀ S_pos]
        nlinarith
      rw [trace_eq]
      have principal_lower : 4 < 2 * ρ * G / (7 * G) := by
        field_simp [G_ne]
        nlinarith
      linarith
  | b =>
      let H := 5200 * ρ ^ 2 - 18398 * ρ + 2443
      have trace_eq : C = 2 * ρ * H := by
        simpa only [C, ρ, H] using singletonBTrace_eq β
      have scale_eq : A = 100 * ρ := by
        dsimp only [A]
        simp [upperScale, spell, nearyUpper, tagCode, ρ, pow_add]
        ring
      have correction_numerator : 100 * ρ * E * μ < 11 * ρ * S := by
        have raw : 100 * ρ * E * μ < 22 * ρ ^ 2 * G := by
          rw [marker_eq]
          dsimp only [E, G]
          unfold gap lift
          nlinarith
        have scaled_target : 22 * ρ ^ 2 * G ≤ 11 * ρ * S := by
          nlinarith
        exact raw.trans_le scaled_target
      have correction_upper : E * μ * A / S < 11 * ρ := by
        rw [scale_eq, div_lt_iff₀ S_pos]
        nlinarith
      have principal_lower : 11 * ρ + 2 < 2 * ρ * H / (7 * G) := by
        rw [lt_div_iff₀ (show 0 < 7 * G by positivity)]
        dsimp only [H, G]
        unfold lift
        nlinarith
      rw [trace_eq]
      linarith

/-- No lawful three-block source with two consecutive singleton erasure blocks reaches a
singleton pole. -/
theorem singletonPole_threeBlock_consecutiveSingleton_impossible
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter currentLetter nextLetter : TagLetter) (root : List NearyTile)
    (source_law : BlocksLaw
      [[.erase currentLetter], [.erase nextLetter], root]) :
    ¬HitsSquarePole β body [.erase targetLetter]
      [[.erase currentLetter], [.erase nextLetter], root] := by
  intro pole
  have older_lower :=
    singletonPole_singletonCurrent_olderRatio_gt_two β_large body
      targetLetter currentLetter source_law.2 pole
  have older_upper :=
    parsedRay_singleton_root_ratio_lt_two β_large body nextLetter root
  exact (not_lt_of_ge older_lower.le) older_upper

/-- Coordinate shells of a multi-role block above a root of upper depth at least two. -/
theorem pair_deepRoot_multi_ray_hasDecimalShell
    {β : Nat} (β_large : 2 ≤ β) (body : List TagLetter)
    {next root : List NearyTile}
    (next_multi : 2 ≤ next.length) (next_ends : EndsInErase next)
    (root_deep : 2 ≤ (spell (nearyUpper β) root).length) :
    HasDecimalShell (parsedRay β body [next, root]).1 1 1 ∧
      HasDecimalShell (parsedRay β body [next, root]).2
        (spell (nearyUpper β) next).length
        (spell (nearyUpper β) next).length := by
  have β_pos : 0 < β := by omega
  let k := (spell (nearyUpper β) next).length
  let ray := parsedRay β body [next, root]
  have ratio_shell : HasDecimalShell (ray.2 / ray.1) (k - 1) (k - 1) := by
    simpa only [ray, k] using
      pair_deepRoot_multi_ratio_hasDecimalShell
        β_large body next_multi next_ends root_deep
  have root_first_unit := rootRay_fst_hasDecimalShell β_pos root
  have scale_shell : HasDecimalShell (upperScale β next) k k := by
    have shell := ten_hasDecimalShell.pow k
    norm_num at shell
    simpa only [upperScale, k] using shell
  have second_shell : HasDecimalShell ray.2 k k := by
    have shell := scale_shell.mul root_first_unit
    convert shell using 1 <;> simp [ray, parsedRay, rayStep]
  have first_ne : ray.1 ≠ 0 := by
    intro first_zero
    apply ratio_shell.1.1
    simp [first_zero]
  have second_ne : ray.2 ≠ 0 := second_shell.1.1
  have first_eq : ray.1 = ray.2 / (ray.2 / ray.1) := by
    field_simp [first_ne, second_ne]
  have first_shell : HasDecimalShell ray.1 1 1 := by
    rw [first_eq]
    have depth : (k : ℤ) - (k - 1) = 1 := by
      have next_length_le_upper : next.length ≤ k := by
        dsimp only [k]
        rw [spell_nearyUpper]
        simpa using DecimalSetterChamber.length_le_tagEncode β
          (next.map NearyTile.letter)
      omega
    constructor
    · have shell := div_hasValue second_shell.1 ratio_shell.1
      simpa only [depth] using shell
    · have shell := div_hasValue second_shell.2 ratio_shell.2
      simpa only [depth] using shell
  exact ⟨by simpa only [ray] using first_shell,
    by simpa only [ray, k] using second_shell⟩

/-- A singleton current cannot precede a multi-role block above a deep physical root at a
singleton pole. The `D_c` branch fails the ultrametric lower bound; the `D_b` branch first
forces intervening upper length two and then fails at five. -/
theorem singletonPole_threeBlock_singletonCurrent_deepRoot_impossible
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter currentLetter : TagLetter) {next root : List NearyTile}
    (next_multi : 2 ≤ next.length) (next_ends : EndsInErase next)
    (root_deep : 2 ≤ (spell (nearyUpper β) root).length) :
    ¬HitsSquarePole β body [.erase targetLetter]
      [[.erase currentLetter], next, root] := by
  intro pole
  have β_pos : 0 < β := by omega
  let k := (spell (nearyUpper β) next).length
  let m := (spell (nearyUpper β) [.erase currentLetter]).length
  let ray := parsedRay β body [next, root]
  let T := boundaryTrace β body [.erase currentLetter]
  let G := lift ((10 : ℚ) ^ β)
  let E := gap ((10 : ℚ) ^ β)
  let μ := DecimalSetterMatrix.marker β
  let A := upperScale β [.erase currentLetter]
  let S := singletonTrace β targetLetter
  let R := T * ray.1 - G * 7 * ray.2
  have next_length_le_upper : next.length ≤ k := by
    dsimp only [k]
    rw [spell_nearyUpper]
    simpa using DecimalSetterChamber.length_le_tagEncode β
      (next.map NearyTile.letter)
  have k_two_le : 2 ≤ k := next_multi.trans next_length_le_upper
  obtain ⟨first_shell, second_shell⟩ :=
    pair_deepRoot_multi_ray_hasDecimalShell
      (show 2 ≤ β by omega) body next_multi next_ends root_deep
  change HasDecimalShell ray.1 1 1 at first_shell
  change HasDecimalShell ray.2 k k at second_shell
  have current_trace : T = singletonTrace β currentLetter := by
    simp [T, boundaryTrace, singletonTrace, lowerBoundaryCode, spell, nearyLower,
      code, digit, mul_comm]
  have current_trace_shell : HasDecimalShell T (β + 1) β := by
    rw [current_trace]
    exact singletonTrace_hasDecimalShell β_pos currentLetter
  have trace_term_shell : HasDecimalShell (T * ray.1) (β + 2) (β + 1) := by
    convert current_trace_shell.mul first_shell using 1
    omega
  have seven_unit : HasDecimalShell (7 : ℚ) 0 0 :=
    intCast_hasDecimalShell_of_mod_seven (Int.ModEq.refl 7)
  have lower_term_shell : HasDecimalShell (G * 7 * ray.2) k k := by
    simpa only [G, zero_add] using
      ((lift_tenPow_hasDecimalShell β_pos).mul seven_unit).mul second_shell
  have target_shell : HasDecimalShell S (β + 1) β := by
    simpa only [S] using singletonTrace_hasDecimalShell β_pos targetLetter
  have scale_shell : HasDecimalShell A m m := by
    have shell := ten_hasDecimalShell.pow m
    norm_num at shell
    simpa only [A, upperScale, m] using shell
  have right_shell :
      HasDecimalShell (E * μ * G * A * ray.1 * 7) (m + 1) (m + 1) := by
    convert (((((gap_tenPow_hasDecimalShell β_pos).mul
      (marker_hasDecimalShell β_pos)).mul
        (lift_tenPow_hasDecimalShell β_pos)).mul scale_shell).mul
          first_shell).mul seven_unit using 1 <;> simp
  have pole_equation :=
    (hitsSquarePole_singleton_cons_iff_rayRecurrence β_pos body targetLetter
      [.erase currentLetter] next [root]).mp pole
  have current_lower : lowerBoundaryCode β body [.erase currentLetter] = 7 := by
    simp [lowerBoundaryCode, spell, nearyLower, code, digit]
  change
    (T * ray.1 - G * lowerBoundaryCode β body [.erase currentLetter] * ray.2) * S =
      E * μ * G * A * ray.1 * 7 at pole_equation
  rw [current_lower] at pole_equation
  change R * S = E * μ * G * A * ray.1 * 7 at pole_equation
  have R_ne : R ≠ 0 := by
    intro R_zero
    have right_zero : E * μ * G * A * ray.1 * 7 = 0 := by
      rw [← pole_equation, R_zero, zero_mul]
    exact right_shell.1.1 right_zero
  have two_balance := congrArg (padicValRat 2) pole_equation
  rw [padicValRat.mul R_ne target_shell.1.1, target_shell.1.2,
    right_shell.1.2] at two_balance
  have five_balance := congrArg (padicValRat 5) pole_equation
  rw [padicValRat.mul R_ne target_shell.2.1, target_shell.2.2,
    right_shell.2.2] at five_balance
  have ultrametric_two :
      min ((β : ℤ) + 2) k ≤ padicValRat 2 R := by
    have raw := padicValRat.min_le_padicValRat_add (p := 2)
      (show T * ray.1 + -(G * 7 * ray.2) ≠ 0 by
        simpa only [R, sub_eq_add_neg] using R_ne)
    rw [trace_term_shell.1.2, padicValRat.neg, lower_term_shell.1.2] at raw
    simpa only [R, sub_eq_add_neg] using raw
  cases currentLetter with
  | c =>
      have m_eq : m = 1 := by
        simp [m, spell, nearyUpper, tagCode]
      have residual_two_upper : padicValRat 2 R ≤ 1 - β := by
        omega
      have residual_two_lower : 2 ≤ padicValRat 2 R := by
        have min_lower : (2 : ℤ) ≤ min ((β : ℤ) + 2) k := by
          exact le_min (by omega) (by omega)
        exact min_lower.trans ultrametric_two
      omega
  | b =>
      have m_eq : m = β + 2 := by
        simp [m, spell, nearyUpper, tagCode]
      have residual_two_eq : padicValRat 2 R = 2 := by omega
      have k_le_two : (k : ℤ) ≤ 2 := by
        by_contra k_not_le
        have min_lower : (3 : ℤ) ≤ min ((β : ℤ) + 2) k := by
          exact le_min (by omega) (by omega)
        omega
      have k_eq : k = 2 := by omega
      have residual_five_shell : HasValue 5 R 2 := by
        have shell := sub_hasValue_min trace_term_shell.2.1 lower_term_shell.2.1 (by
          rw [trace_term_shell.2.2, lower_term_shell.2.2, k_eq]
          omega)
        rw [trace_term_shell.2.2, lower_term_shell.2.2, k_eq] at shell
        norm_num at shell
        rw [min_eq_right (show (2 : ℤ) ≤ β + 1 by omega)] at shell
        simpa only [R] using shell
      rw [residual_five_shell.2] at five_balance
      omega

/-- No lawful three-block singleton pole has a singleton current block. Shallow roots reduce to
`R_c`; deep roots are excluded separately for singleton and multi-role intervening blocks. -/
theorem singletonPole_threeBlock_singletonCurrent_impossible
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter currentLetter : TagLetter) {next root : List NearyTile}
    (source_law : BlocksLaw [[.erase currentLetter], next, root]) :
    ¬HitsSquarePole β body [.erase targetLetter]
      [[.erase currentLetter], next, root] := by
  intro pole
  have next_ends : EndsInErase next := source_law.2.1
  have root_ends : EndsInRule root := source_law.2.2
  have root_upper_pos : 0 < (spell (nearyUpper β) root).length := by
    obtain ⟨front, letter, root_eq⟩ := root_ends
    have upper_ne : spell (nearyUpper β) root ≠ [] := by
      rw [root_eq, spell_append]
      simp [spell, nearyUpper_ne_nil]
    exact List.length_pos_of_ne_nil upper_ne
  by_cases root_deep : 2 ≤ (spell (nearyUpper β) root).length
  · by_cases next_multi : 2 ≤ next.length
    · exact singletonPole_threeBlock_singletonCurrent_deepRoot_impossible
        β_large body targetLetter currentLetter next_multi next_ends root_deep pole
    · obtain ⟨front, nextLetter, next_eq⟩ := next_ends
      have front_nil : front = [] := by
        apply List.length_eq_zero_iff.mp
        have next_length : next.length = front.length + 1 := by simp [next_eq]
        omega
      have next_singleton : next = [.erase nextLetter] := by
        simpa [front_nil] using next_eq
      have singleton_law :
          BlocksLaw [[.erase currentLetter], [.erase nextLetter], root] := by
        simpa only [next_singleton] using source_law
      have singleton_pole :
          HitsSquarePole β body [.erase targetLetter]
            [[.erase currentLetter], [.erase nextLetter], root] := by
        simpa only [next_singleton] using pole
      exact singletonPole_threeBlock_consecutiveSingleton_impossible
        β_large body targetLetter currentLetter nextLetter root singleton_law singleton_pole
  · have root_shallow : (spell (nearyUpper β) root).length = 1 := by omega
    have root_eq := ruleEnded_eq_ruleCRoot_of_upperLength_eq_one root_ends root_shallow
    subst root
    cases currentLetter with
    | c =>
        exact singletonPole_threeBlock_ruleCRoot_currentC_impossible
          β_large body targetLetter next pole
    | b =>
        exact singletonPole_threeBlock_ruleCRoot_currentB_impossible
          β_large body targetLetter next pole

/-- Every lawful three-block singleton pole has a multi-role current block. -/
theorem singletonPole_threeBlock_forces_current_multi
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next root : List NearyTile}
    (source_law : BlocksLaw [current, next, root])
    (pole : HitsSquarePole β body [.erase targetLetter] [current, next, root]) :
    2 ≤ current.length := by
  by_contra current_not_multi
  obtain ⟨front, currentLetter, current_eq⟩ := source_law.1
  have front_nil : front = [] := by
    apply List.length_eq_zero_iff.mp
    have current_length : current.length = front.length + 1 := by simp [current_eq]
    omega
  have current_singleton : current = [.erase currentLetter] := by
    simpa [front_nil] using current_eq
  have singleton_law : BlocksLaw [[.erase currentLetter], next, root] := by
    simpa only [current_singleton] using source_law
  have singleton_pole :
      HitsSquarePole β body [.erase targetLetter] [[.erase currentLetter], next, root] := by
    simpa only [current_singleton] using pole
  exact singletonPole_threeBlock_singletonCurrent_impossible
    β_large body targetLetter currentLetter singleton_law singleton_pole

/-- With a multi-role intervening block, the three-block classifier no longer needs a
current-block cardinality hypothesis. -/
theorem singletonPole_threeBlock_nextMulti_classifier
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next root : List NearyTile}
    (source_law : BlocksLaw [current, next, root]) (next_multi : 2 ≤ next.length)
    (pole : HitsSquarePole β body [.erase targetLetter] [current, next, root]) :
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
  have current_multi :=
    singletonPole_threeBlock_forces_current_multi
      β_large body targetLetter source_law pole
  exact singletonPole_threeBlock_multi_classifier
    β_large body targetLetter source_law current_multi next_multi pole

end MatrixMortality.DecimalSetterBridgeRay
