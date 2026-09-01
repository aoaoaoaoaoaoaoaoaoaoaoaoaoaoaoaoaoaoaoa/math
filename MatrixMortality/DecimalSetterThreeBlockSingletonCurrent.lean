import MatrixMortality.DecimalSetterThreeBlockSingleton

/-!
# Three-block singleton-current extinction

Exact resonant discrepancy shells and quotient bounds extinguish both physical singleton
currents over the canonical `R_c` tail.
-/

namespace MatrixMortality.DecimalSetterBridgeRay

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterBridge
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterDepth
open MatrixMortality.DecimalSetterMatrix
open MatrixMortality.PadicValuation
/-- A singleton `D_c` current over the resonant `R_c` tail forces the intervening discrepancy
into the excessive shell `(k+β,k+β-1)`. -/
theorem singletonPole_threeBlock_ruleCRoot_currentC_discrepancyShell
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) (next : List NearyTile)
    (pole : HitsSquarePole β body [.erase targetLetter]
      [[.erase .c], next, DecimalSetterMinimumBody.ruleCRoot]) :
    HasDecimalShell
      (upperBoundaryCode β next - lowerBoundaryCode β body next)
      ((spell (nearyUpper β) next).length + β)
      ((spell (nearyUpper β) next).length + β - 1) := by
  have β_pos : 0 < β := by omega
  let k := (spell (nearyUpper β) next).length
  let δ := upperBoundaryCode β next - lowerBoundaryCode β body next
  let E := gap ((10 : ℚ) ^ β)
  let G := lift ((10 : ℚ) ^ β)
  let μ := DecimalSetterMatrix.marker β
  let S := singletonTrace β targetLetter
  let C := singletonTrace β .c
  let B := upperScale β next
  let K := C * S - 7 * E * μ * G * 10
  have target_shell : HasDecimalShell S (β + 1) β := by
    simpa only [S] using singletonTrace_hasDecimalShell β_pos targetLetter
  have current_shell : HasDecimalShell C (β + 1) β := by
    simpa only [C] using singletonTrace_hasDecimalShell β_pos .c
  have trace_product_shell : HasDecimalShell (C * S) (2 * β + 2) (2 * β) := by
    convert current_shell.mul target_shell using 1 <;> omega
  have seven_unit : HasDecimalShell (7 : ℚ) 0 0 :=
    intCast_hasDecimalShell_of_mod_seven (Int.ModEq.refl 7)
  have correction_shell : HasDecimalShell (7 * E * μ * G * 10) 1 1 := by
    convert ((((seven_unit.mul (gap_tenPow_hasDecimalShell β_pos)).mul
      (marker_hasDecimalShell β_pos)).mul (lift_tenPow_hasDecimalShell β_pos)).mul
        ten_hasDecimalShell) using 1 <;> simp
  have coefficient_shell : HasDecimalShell K 1 1 := by
    constructor
    · have shell := sub_hasValue_min trace_product_shell.1.1 correction_shell.1.1 (by
        rw [trace_product_shell.1.2, correction_shell.1.2]
        omega)
      rw [trace_product_shell.1.2, correction_shell.1.2,
        min_eq_right (show (1 : ℤ) ≤ 2 * β + 2 by omega)] at shell
      simpa only [K] using shell
    · have shell := sub_hasValue_min trace_product_shell.2.1 correction_shell.2.1 (by
        rw [trace_product_shell.2.2, correction_shell.2.2]
        omega)
      rw [trace_product_shell.2.2, correction_shell.2.2,
        min_eq_right (show (1 : ℤ) ≤ 2 * β by omega)] at shell
      simpa only [K] using shell
  have scale_shell : HasDecimalShell B k k := by
    have shell := ten_hasDecimalShell.pow k
    norm_num at shell
    simpa only [B, upperScale, k] using shell
  have right_shell : HasDecimalShell (G * 7 * B * μ * S)
      (k + β + 1) (k + β) := by
    convert (((((lift_tenPow_hasDecimalShell β_pos).mul seven_unit).mul scale_shell).mul
      (marker_hasDecimalShell β_pos)).mul target_shell) using 1 <;> omega
  have exact_equation :=
    (hitsSquarePole_singleton_pair_ruleCRoot_iff_discrepancyEquation
      β_pos body targetLetter [.erase .c] next).mp pole
  have current_trace_eq : boundaryTrace β body [.erase .c] = C := by
    simp [C, boundaryTrace, singletonTrace, lowerBoundaryCode, spell, nearyLower,
      code, digit, mul_comm]
  have current_lower_eq : lowerBoundaryCode β body [.erase .c] = 7 := by
    simp [lowerBoundaryCode, spell, nearyLower, code, digit]
  have current_scale_eq : upperScale β [.erase .c] = 10 := by
    simp [upperScale, spell, nearyUpper, tagCode]
  rw [current_trace_eq, current_lower_eq, current_scale_eq] at exact_equation
  change δ * K = G * 7 * B * μ * S at exact_equation
  have δ_eq : δ = (G * 7 * B * μ * S) / K := by
    apply (eq_div_iff coefficient_shell.1.1).2
    exact exact_equation
  change HasDecimalShell δ (k + β) (k + β - 1)
  rw [δ_eq]
  constructor
  · have shell := div_hasValue right_shell.1 coefficient_shell.1
    have depth : (k + β + 1 : ℤ) - 1 = k + β := by omega
    simpa only [depth] using shell
  · have shell := div_hasValue right_shell.2 coefficient_shell.2
    have depth : (k + β : ℤ) - 1 = k + β - 1 := by omega
    simpa only [depth] using shell

/-- A singleton `D_c` current at an `R_c`-rooted pole forces the older quotient above one
quarter of the decimal width. -/
theorem singletonPole_threeBlock_ruleCRoot_currentC_ratio_lower
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) (next : List NearyTile)
    (pole : HitsSquarePole β body [.erase targetLetter]
      [[.erase .c], next, DecimalSetterMinimumBody.ruleCRoot]) :
    (10 : ℚ) ^ β / 4 <
      (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).2 /
        (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).1 := by
  have β_pos : 0 < β := by omega
  let ρ : ℚ := 10 ^ β
  let E := gap ρ
  let G := lift ρ
  let μ := DecimalSetterMatrix.marker β
  let C := singletonTrace β .c
  let S := singletonTrace β targetLetter
  let B := upperScale β next
  let δ := upperBoundaryCode β next - lowerBoundaryCode β body next
  let q := (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).2 /
    (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).1
  have current_ends : EndsInErase ([.erase .c] : List NearyTile) := ⟨[], .c, rfl⟩
  have discrepancy_pos : 0 < δ := by
    have positive := singletonPole_threeBlock_ruleCRoot_discrepancy_pos
      β_large body targetLetter current_ends pole
    exact sub_pos.mpr (by simpa only [δ] using positive)
  have δ_ne : δ ≠ 0 := ne_of_gt discrepancy_pos
  have G_ne : G ≠ 0 := by
    simpa only [G, ρ] using (lift_tenPow_hasDecimalShell β_pos).1.1
  have S_ne : S ≠ 0 := by
    simpa only [S] using (singletonTrace_hasDecimalShell β_pos targetLetter).1.1
  have ratio_eq : q = B * μ / δ := by
    simpa only [q, B, μ, δ] using
      parsedRay_pair_ruleCRoot_ratio_eq β_pos body next δ_ne
  have exact_equation :=
    (hitsSquarePole_singleton_pair_ruleCRoot_iff_discrepancyEquation
      β_pos body targetLetter [.erase .c] next).mp pole
  have current_trace_eq : boundaryTrace β body [.erase .c] = C := by
    simp [C, boundaryTrace, singletonTrace, lowerBoundaryCode, spell, nearyLower,
      code, digit, mul_comm]
  have current_lower_eq : lowerBoundaryCode β body [.erase .c] = 7 := by
    simp [lowerBoundaryCode, spell, nearyLower, code, digit]
  have current_scale_eq : upperScale β [.erase .c] = 10 := by
    simp [upperScale, spell, nearyUpper, tagCode]
  rw [current_trace_eq, current_lower_eq, current_scale_eq] at exact_equation
  change δ * (C * S - 7 * E * μ * G * 10) = G * 7 * B * μ * S at exact_equation
  have current_trace_formula : C = 2 * ρ * G := by
    simpa only [C, ρ, G] using singletonCTrace_eq β
  rw [current_trace_formula] at exact_equation
  have reduced_equation :
      δ * (2 * ρ * S - 70 * E * μ) = 7 * B * μ * S := by
    apply mul_left_cancel₀ G_ne
    linear_combination exact_equation
  have quotient_formula : q = 2 * ρ / 7 - 10 * E * μ / S := by
    rw [ratio_eq]
    field_simp [δ_ne, S_ne]
    linear_combination - reduced_equation
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
  have E_upper : E < 18 * ρ := by
    dsimp only [E]
    unfold gap
    linarith
  have G_pos : 0 < G := by
    dsimp only [G]
    unfold lift
    linarith
  have G_lower : (25200 : ℚ) < G := by
    dsimp only [G]
    unfold lift
    linarith
  have μ_pos : 0 < μ := by
    simpa only [μ] using DecimalSetterMatrix.marker_pos β
  have marker_bound_nat : code (nearyMarker β) < 10 ^ (β + 1) :=
    code_lt_pow_length (nearyMarker β) |>.trans_eq (by simp [nearyMarker])
  have μ_upper : μ < 10 * ρ := by
    have rational_bound :
        (code (nearyMarker β) : ℚ) < (10 : ℚ) ^ (β + 1) := by
      exact_mod_cast marker_bound_nat
    rw [pow_succ] at rational_bound
    simpa only [μ, DecimalSetterMatrix.marker, ρ, mul_comm] using rational_bound
  have product_upper : E * μ < (18 * ρ) * (10 * ρ) :=
    mul_lt_mul E_upper μ_upper.le μ_pos (by positivity)
  have left_upper : 280 * E * μ < 50400 * ρ ^ 2 := by nlinarith
  have lift_scaled : 50400 * ρ ^ 2 < 2 * ρ ^ 2 * G := by
    have scaled := mul_lt_mul_of_pos_left G_lower (show 0 < 2 * ρ ^ 2 by positivity)
    nlinarith
  have target_shell : 2 * ρ * G ≤ S := by
    simpa only [ρ, G, S] using
      two_mul_tenPow_lift_le_singletonTrace β_large targetLetter
  have S_pos : 0 < S := lt_of_lt_of_le (by positivity) target_shell
  have target_scaled : 2 * ρ ^ 2 * G ≤ ρ * S := by
    have scaled := mul_le_mul_of_nonneg_left target_shell rho_pos.le
    nlinarith
  have correction_numerator_bound : 280 * E * μ < ρ * S :=
    left_upper.trans (lift_scaled.trans_le target_scaled)
  have correction_bound : 10 * E * μ / S < ρ / 28 := by
    rw [div_lt_iff₀ S_pos]
    nlinarith
  change ρ / 4 < q
  rw [quotient_formula]
  linarith

/-- No `R_c`-rooted three-block singleton pole has singleton current `D_c`. The pole forces
the intervening discrepancy below forty upper-scale units, while its exact decimal shell makes
it a positive multiple of at least one hundred such units. -/
theorem singletonPole_threeBlock_ruleCRoot_currentC_impossible
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) (next : List NearyTile) :
    ¬HitsSquarePole β body [.erase targetLetter]
      [[.erase .c], next, DecimalSetterMinimumBody.ruleCRoot] := by
  intro pole
  have β_pos : 0 < β := by omega
  let upperWord := spell (nearyUpper β) next ++ nearyMarker β
  let lowerWord := spell (nearyLower β body) next
  let P := code upperWord
  let V := code lowerWord
  let k := (spell (nearyUpper β) next).length
  let width := k + β - 1
  let ρ : ℚ := 10 ^ β
  let μ := DecimalSetterMatrix.marker β
  let B := upperScale β next
  let δ := upperBoundaryCode β next - lowerBoundaryCode β body next
  let q := (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).2 /
    (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).1
  have current_ends : EndsInErase ([.erase .c] : List NearyTile) := ⟨[], .c, rfl⟩
  have discrepancy_pos : V < P := by
    have rational := singletonPole_threeBlock_ruleCRoot_discrepancy_pos
      β_large body targetLetter current_ends pole
    have cast_bound : (V : ℚ) < P := by
      simpa only [V, P, upperWord, lowerWord, upperBoundaryCode, lowerBoundaryCode] using rational
    exact_mod_cast cast_bound
  have difference_cast : (((P - V : Nat) : ℚ)) = δ := by
    rw [Nat.cast_sub discrepancy_pos.le]
    rfl
  have δ_pos : 0 < δ := by
    rw [← difference_cast]
    exact_mod_cast Nat.sub_pos_of_lt discrepancy_pos
  have δ_ne : δ ≠ 0 := ne_of_gt δ_pos
  have ratio_lower : ρ / 4 < q := by
    simpa only [ρ, q] using
      singletonPole_threeBlock_ruleCRoot_currentC_ratio_lower
        β_large body targetLetter next pole
  have ratio_eq : q = B * μ / δ := by
    simpa only [q, B, μ, δ] using
      parsedRay_pair_ruleCRoot_ratio_eq β_pos body next δ_ne
  have ratio_scaled : ρ / 4 * δ < q * δ :=
    mul_lt_mul_of_pos_right ratio_lower δ_pos
  have ratio_product : q * δ = B * μ := by
    rw [ratio_eq]
    field_simp [δ_ne]
  have rho_bound : (1000 : ℚ) ≤ ρ := by
    have natural_bound : 10 ^ 3 ≤ 10 ^ β :=
      Nat.pow_le_pow_right (by norm_num) β_large
    norm_num at natural_bound ⊢
    simpa only [ρ] using (show (1000 : ℚ) ≤ (10 : ℚ) ^ β by
      exact_mod_cast natural_bound)
  have rho_pos : 0 < ρ := lt_of_lt_of_le (by norm_num) rho_bound
  have marker_bound_nat : code (nearyMarker β) < 10 ^ (β + 1) :=
    code_lt_pow_length (nearyMarker β) |>.trans_eq (by simp [nearyMarker])
  have μ_upper : μ < 10 * ρ := by
    have rational_bound :
        (code (nearyMarker β) : ℚ) < (10 : ℚ) ^ (β + 1) := by
      exact_mod_cast marker_bound_nat
    rw [pow_succ] at rational_bound
    simpa only [μ, DecimalSetterMatrix.marker, ρ, mul_comm] using rational_bound
  have B_pos : 0 < B := by simp [B, upperScale]
  have marker_scaled : B * μ < B * (10 * ρ) :=
    mul_lt_mul_of_pos_left μ_upper B_pos
  have discrepancy_upper : δ < 40 * B := by
    have scaled_bound : δ * ρ < 40 * B * ρ := by
      rw [ratio_product] at ratio_scaled
      nlinarith
    nlinarith
  have discrepancy_shell :=
    singletonPole_threeBlock_ruleCRoot_currentC_discrepancyShell
      β_large body targetLetter next pole
  change HasDecimalShell δ ((k : ℤ) + β) ((k : ℤ) + β - 1) at discrepancy_shell
  have difference_two_value : padicValNat 2 (P - V) = k + β := by
    have valuation := discrepancy_shell.1.2
    rw [← difference_cast, padicValRat.of_nat] at valuation
    exact_mod_cast valuation
  have difference_five_value : padicValNat 5 (P - V) = k + β - 1 := by
    have valuation := discrepancy_shell.2.2
    rw [← difference_cast, padicValRat.of_nat] at valuation
    have depth_cast : ((k + β - 1 : Nat) : ℤ) = (k : ℤ) + β - 1 := by omega
    rw [← depth_cast] at valuation
    exact_mod_cast valuation
  have two_power_dvd : 2 ^ width ∣ P - V := by
    apply (padicValNat_dvd_iff (p := 2) width (P - V)).mpr
    exact Or.inr (by rw [difference_two_value]; omega)
  have five_power_dvd : 5 ^ width ∣ P - V := by
    apply (padicValNat_dvd_iff (p := 5) width (P - V)).mpr
    exact Or.inr (by simpa only [width] using difference_five_value.ge)
  have ten_power_dvd : 10 ^ width ∣ P - V := by
    rw [show 10 ^ width = 2 ^ width * 5 ^ width by
      rw [show 10 = 2 * 5 by norm_num, mul_pow]]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
      ((by norm_num : Nat.Coprime 2 5).pow width width) two_power_dvd five_power_dvd
  have power_le_difference : 10 ^ width ≤ P - V :=
    Nat.le_of_dvd (Nat.sub_pos_of_lt discrepancy_pos) ten_power_dvd
  have discrepancy_lower : ((10 ^ width : Nat) : ℚ) ≤ δ := by
    have cast_bound : ((10 ^ width : Nat) : ℚ) ≤ ((P - V : Nat) : ℚ) := by
      exact_mod_cast power_le_difference
    simpa only [difference_cast] using cast_bound
  have beta_factor_nat : 100 ≤ 10 ^ (β - 1) := by
    have exponent : 2 ≤ β - 1 := by omega
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 10) exponent
  have beta_factor : (100 : ℚ) ≤ (10 : ℚ) ^ (β - 1) := by
    exact_mod_cast beta_factor_nat
  have B_eq : B = (10 : ℚ) ^ k := by
    simp only [B, upperScale, k]
  have width_eq : width = k + (β - 1) := by omega
  have power_factor : (10 : ℚ) ^ width = B * (10 : ℚ) ^ (β - 1) := by
    rw [width_eq, pow_add, B_eq]
  have scaled_factor : B * 100 ≤ B * (10 : ℚ) ^ (β - 1) :=
    mul_le_mul_of_nonneg_left beta_factor B_pos.le
  have power_growth : 40 * B < (10 : ℚ) ^ width := by
    rw [power_factor]
    exact (show 40 * B < B * 100 by nlinarith).trans_le scaled_factor
  have discrepancy_below_power : δ < (10 : ℚ) ^ width :=
    discrepancy_upper.trans power_growth
  norm_num at discrepancy_lower
  exact (not_lt_of_ge discrepancy_lower) discrepancy_below_power

/-- A singleton `D_b` current over the resonant `R_c` tail forces the intervening discrepancy
into the shell `(k-1,k-2)`. -/
theorem singletonPole_threeBlock_ruleCRoot_currentB_discrepancyShell
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) (next : List NearyTile)
    (pole : HitsSquarePole β body [.erase targetLetter]
      [[.erase .b], next, DecimalSetterMinimumBody.ruleCRoot]) :
    HasDecimalShell
      (upperBoundaryCode β next - lowerBoundaryCode β body next)
      ((spell (nearyUpper β) next).length - 1)
      ((spell (nearyUpper β) next).length - 2) := by
  have β_pos : 0 < β := by omega
  let k := (spell (nearyUpper β) next).length
  let δ := upperBoundaryCode β next - lowerBoundaryCode β body next
  let E := gap ((10 : ℚ) ^ β)
  let G := lift ((10 : ℚ) ^ β)
  let μ := DecimalSetterMatrix.marker β
  let S := singletonTrace β targetLetter
  let C := singletonTrace β .b
  let B := upperScale β next
  let K := C * S - 7 * E * μ * G * 10 ^ (β + 2)
  have target_shell : HasDecimalShell S (β + 1) β := by
    simpa only [S] using singletonTrace_hasDecimalShell β_pos targetLetter
  have current_shell : HasDecimalShell C (β + 1) β := by
    simpa only [C] using singletonTrace_hasDecimalShell β_pos .b
  have trace_product_shell : HasDecimalShell (C * S) (2 * β + 2) (2 * β) := by
    convert current_shell.mul target_shell using 1 <;> omega
  have seven_unit : HasDecimalShell (7 : ℚ) 0 0 :=
    intCast_hasDecimalShell_of_mod_seven (Int.ModEq.refl 7)
  have current_scale_shell : HasDecimalShell ((10 : ℚ) ^ (β + 2)) (β + 2) (β + 2) := by
    simpa using ten_hasDecimalShell.pow (β + 2)
  have correction_shell :
      HasDecimalShell (7 * E * μ * G * 10 ^ (β + 2)) (β + 2) (β + 2) := by
    convert ((((seven_unit.mul (gap_tenPow_hasDecimalShell β_pos)).mul
      (marker_hasDecimalShell β_pos)).mul (lift_tenPow_hasDecimalShell β_pos)).mul
        current_scale_shell) using 1 <;> simp
  have coefficient_shell : HasDecimalShell K (β + 2) (β + 2) := by
    constructor
    · have shell := sub_hasValue_min trace_product_shell.1.1 correction_shell.1.1 (by
        rw [trace_product_shell.1.2, correction_shell.1.2]
        omega)
      rw [trace_product_shell.1.2, correction_shell.1.2,
        min_eq_right (show (β + 2 : ℤ) ≤ 2 * β + 2 by omega)] at shell
      simpa only [K] using shell
    · have shell := sub_hasValue_min trace_product_shell.2.1 correction_shell.2.1 (by
        rw [trace_product_shell.2.2, correction_shell.2.2]
        omega)
      rw [trace_product_shell.2.2, correction_shell.2.2,
        min_eq_right (show (β + 2 : ℤ) ≤ 2 * β by omega)] at shell
      simpa only [K] using shell
  have scale_shell : HasDecimalShell B k k := by
    have shell := ten_hasDecimalShell.pow k
    norm_num at shell
    simpa only [B, upperScale, k] using shell
  have right_shell : HasDecimalShell (G * 7 * B * μ * S)
      (k + β + 1) (k + β) := by
    convert (((((lift_tenPow_hasDecimalShell β_pos).mul seven_unit).mul scale_shell).mul
      (marker_hasDecimalShell β_pos)).mul target_shell) using 1 <;> omega
  have exact_equation :=
    (hitsSquarePole_singleton_pair_ruleCRoot_iff_discrepancyEquation
      β_pos body targetLetter [.erase .b] next).mp pole
  have current_trace_eq : boundaryTrace β body [.erase .b] = C := by
    simp [C, boundaryTrace, singletonTrace, lowerBoundaryCode, spell, nearyLower,
      code, digit, mul_comm]
  have current_lower_eq : lowerBoundaryCode β body [.erase .b] = 7 := by
    simp [lowerBoundaryCode, spell, nearyLower, code, digit]
  have current_scale_eq : upperScale β [.erase .b] = 10 ^ (β + 2) := by
    simp [upperScale, spell, nearyUpper, tagCode]
  rw [current_trace_eq, current_lower_eq, current_scale_eq] at exact_equation
  change δ * K = G * 7 * B * μ * S at exact_equation
  have δ_eq : δ = (G * 7 * B * μ * S) / K := by
    apply (eq_div_iff coefficient_shell.1.1).2
    exact exact_equation
  change HasDecimalShell δ (k - 1) (k - 2)
  rw [δ_eq]
  constructor
  · have shell := div_hasValue right_shell.1 coefficient_shell.1
    have depth : (k + β + 1 : ℤ) - (β + 2) = k - 1 := by omega
    simpa only [depth] using shell
  · have shell := div_hasValue right_shell.2 coefficient_shell.2
    have depth : (k + β : ℤ) - (β + 2) = k - 2 := by omega
    simpa only [depth] using shell

/-- A singleton `D_b` current at an `R_c`-rooted pole forces the older quotient above twice
the square of the decimal width. -/
theorem singletonPole_threeBlock_ruleCRoot_currentB_ratio_lower
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) (next : List NearyTile)
    (pole : HitsSquarePole β body [.erase targetLetter]
      [[.erase .b], next, DecimalSetterMinimumBody.ruleCRoot]) :
    2 * ((10 : ℚ) ^ β) ^ 2 <
      (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).2 /
        (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).1 := by
  have β_pos : 0 < β := by omega
  let ρ : ℚ := 10 ^ β
  let E := gap ρ
  let G := lift ρ
  let μ := DecimalSetterMatrix.marker β
  let H := 5200 * ρ ^ 2 - 18398 * ρ + 2443
  let C := singletonTrace β .b
  let S := singletonTrace β targetLetter
  let B := upperScale β next
  let δ := upperBoundaryCode β next - lowerBoundaryCode β body next
  let q := (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).2 /
    (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).1
  have current_ends : EndsInErase ([.erase .b] : List NearyTile) := ⟨[], .b, rfl⟩
  have discrepancy_pos : 0 < δ := by
    have positive := singletonPole_threeBlock_ruleCRoot_discrepancy_pos
      β_large body targetLetter current_ends pole
    exact sub_pos.mpr (by simpa only [δ] using positive)
  have δ_ne : δ ≠ 0 := ne_of_gt discrepancy_pos
  have G_ne : G ≠ 0 := by
    simpa only [G, ρ] using (lift_tenPow_hasDecimalShell β_pos).1.1
  have S_ne : S ≠ 0 := by
    simpa only [S] using (singletonTrace_hasDecimalShell β_pos targetLetter).1.1
  have ratio_eq : q = B * μ / δ := by
    simpa only [q, B, μ, δ] using
      parsedRay_pair_ruleCRoot_ratio_eq β_pos body next δ_ne
  have exact_equation :=
    (hitsSquarePole_singleton_pair_ruleCRoot_iff_discrepancyEquation
      β_pos body targetLetter [.erase .b] next).mp pole
  have current_trace_eq : boundaryTrace β body [.erase .b] = C := by
    simp [C, boundaryTrace, singletonTrace, lowerBoundaryCode, spell, nearyLower,
      code, digit, mul_comm]
  have current_lower_eq : lowerBoundaryCode β body [.erase .b] = 7 := by
    simp [lowerBoundaryCode, spell, nearyLower, code, digit]
  have current_scale_eq : upperScale β [.erase .b] = 10 ^ (β + 2) := by
    simp [upperScale, spell, nearyUpper, tagCode]
  rw [current_trace_eq, current_lower_eq, current_scale_eq] at exact_equation
  change δ * (C * S - 7 * E * μ * G * 10 ^ (β + 2)) =
    G * 7 * B * μ * S at exact_equation
  have current_trace_formula : C = 2 * ρ * H := by
    simpa only [C, ρ, H] using singletonBTrace_eq β
  have current_scale_formula : (10 : ℚ) ^ (β + 2) = 100 * ρ := by
    rw [show β + 2 = β + 2 by rfl, pow_add]
    norm_num [ρ]
    ring
  rw [current_trace_formula, current_scale_formula] at exact_equation
  have quotient_formula : q = 2 * ρ * H / (7 * G) - 100 * ρ * E * μ / S := by
    rw [ratio_eq]
    field_simp [δ_ne, G_ne, S_ne]
    linear_combination - exact_equation
  have rho_bound : (1000 : ℚ) ≤ ρ := by
    have natural_bound : 10 ^ 3 ≤ 10 ^ β :=
      Nat.pow_le_pow_right (by norm_num) β_large
    norm_num at natural_bound ⊢
    simpa only [ρ] using (show (1000 : ℚ) ≤ (10 : ℚ) ^ β by
      exact_mod_cast natural_bound)
  have rho_pos : 0 < ρ := lt_of_lt_of_le (by norm_num) rho_bound
  have square_growth : 1000 * ρ ≤ ρ ^ 2 := by nlinarith
  have E_pos : 0 < E := by
    dsimp only [E]
    unfold gap
    linarith
  have E_upper : E < 18 * ρ := by
    dsimp only [E]
    unfold gap
    linarith
  have G_pos : 0 < G := by
    dsimp only [G]
    unfold lift
    linarith
  have G_constant : (90000 : ℚ) < G := by
    dsimp only [G]
    unfold lift
    linarith
  have μ_pos : 0 < μ := by
    simpa only [μ] using DecimalSetterMatrix.marker_pos β
  have marker_bound_nat : code (nearyMarker β) < 10 ^ (β + 1) :=
    code_lt_pow_length (nearyMarker β) |>.trans_eq (by simp [nearyMarker])
  have μ_upper : μ < 10 * ρ := by
    have rational_bound :
        (code (nearyMarker β) : ℚ) < (10 : ℚ) ^ (β + 1) := by
      exact_mod_cast marker_bound_nat
    rw [pow_succ] at rational_bound
    simpa only [μ, DecimalSetterMatrix.marker, ρ, mul_comm] using rational_bound
  have trace_inner : 203 * ρ * G < 20 * H := by
    dsimp only [G, H]
    unfold lift
    nlinarith
  have trace_scaled := mul_lt_mul_of_pos_left trace_inner rho_pos
  have trace_quotient_lower : 29 / 10 * ρ ^ 2 < 2 * ρ * H / (7 * G) := by
    rw [lt_div_iff₀ (by positivity : 0 < 7 * G)]
    nlinarith
  have product_upper : E * μ < (18 * ρ) * (10 * ρ) :=
    mul_lt_mul E_upper μ_upper.le μ_pos (by positivity)
  have correction_left : 1000 * ρ * E * μ < 180000 * ρ ^ 3 := by
    have scaled := mul_lt_mul_of_pos_left product_upper (show 0 < 1000 * ρ by positivity)
    nlinarith
  have correction_middle : 180000 * ρ ^ 3 < 2 * ρ ^ 3 * G := by
    have scaled := mul_lt_mul_of_pos_left G_constant (show 0 < 2 * ρ ^ 3 by positivity)
    nlinarith
  have target_lower : 2 * ρ * G ≤ S := by
    simpa only [ρ, G, S] using
      two_mul_tenPow_lift_le_singletonTrace β_large targetLetter
  have S_pos : 0 < S := lt_of_lt_of_le (by positivity) target_lower
  have correction_right : 2 * ρ ^ 3 * G ≤ ρ ^ 2 * S := by
    have scaled := mul_le_mul_of_nonneg_left target_lower (show 0 ≤ ρ ^ 2 by positivity)
    nlinarith
  have correction_cross : 1000 * ρ * E * μ < ρ ^ 2 * S :=
    correction_left.trans (correction_middle.trans_le correction_right)
  have correction_upper : 100 * ρ * E * μ / S < ρ ^ 2 / 10 := by
    rw [div_lt_iff₀ S_pos]
    nlinarith
  change 2 * ρ ^ 2 < q
  rw [quotient_formula]
  linarith


/-- No `R_c`-rooted three-block singleton pole has singleton current `D_b`. The quotient
lower bound forces its positive integral discrepancy below the minimum magnitude imposed by
the exact `(k-1,k-2)` shell. -/
theorem singletonPole_threeBlock_ruleCRoot_currentB_impossible
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) (next : List NearyTile) :
    ¬HitsSquarePole β body [.erase targetLetter]
      [[.erase .b], next, DecimalSetterMinimumBody.ruleCRoot] := by
  intro pole
  have β_pos : 0 < β := by omega
  let upperWord := spell (nearyUpper β) next ++ nearyMarker β
  let lowerWord := spell (nearyLower β body) next
  let P := code upperWord
  let V := code lowerWord
  let k := (spell (nearyUpper β) next).length
  let ρ : ℚ := 10 ^ β
  let μ := DecimalSetterMatrix.marker β
  let B := upperScale β next
  let δ := upperBoundaryCode β next - lowerBoundaryCode β body next
  let q := (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).2 /
    (parsedRay β body [next, DecimalSetterMinimumBody.ruleCRoot]).1
  have current_ends : EndsInErase ([.erase .b] : List NearyTile) := ⟨[], .b, rfl⟩
  have discrepancy_pos : V < P := by
    have rational := singletonPole_threeBlock_ruleCRoot_discrepancy_pos
      β_large body targetLetter current_ends pole
    have cast_bound : (V : ℚ) < P := by
      simpa only [V, P, upperWord, lowerWord, upperBoundaryCode, lowerBoundaryCode] using rational
    exact_mod_cast cast_bound
  have difference_cast : (((P - V : Nat) : ℚ)) = δ := by
    rw [Nat.cast_sub discrepancy_pos.le]
    rfl
  have δ_pos : 0 < δ := by
    rw [← difference_cast]
    exact_mod_cast Nat.sub_pos_of_lt discrepancy_pos
  have δ_ne : δ ≠ 0 := ne_of_gt δ_pos
  have ratio_lower : 2 * ρ ^ 2 < q := by
    simpa only [ρ, q] using
      singletonPole_threeBlock_ruleCRoot_currentB_ratio_lower
        β_large body targetLetter next pole
  have ratio_eq : q = B * μ / δ := by
    simpa only [q, B, μ, δ] using
      parsedRay_pair_ruleCRoot_ratio_eq β_pos body next δ_ne
  have ratio_scaled : 2 * ρ ^ 2 * δ < q * δ :=
    mul_lt_mul_of_pos_right ratio_lower δ_pos
  have ratio_product : q * δ = B * μ := by
    rw [ratio_eq]
    field_simp [δ_ne]
  have rho_bound : (1000 : ℚ) ≤ ρ := by
    have natural_bound : 10 ^ 3 ≤ 10 ^ β :=
      Nat.pow_le_pow_right (by norm_num) β_large
    norm_num at natural_bound ⊢
    simpa only [ρ] using (show (1000 : ℚ) ≤ (10 : ℚ) ^ β by
      exact_mod_cast natural_bound)
  have rho_pos : 0 < ρ := lt_of_lt_of_le (by norm_num) rho_bound
  have marker_bound_nat : code (nearyMarker β) < 10 ^ (β + 1) :=
    code_lt_pow_length (nearyMarker β) |>.trans_eq (by simp [nearyMarker])
  have μ_upper : μ < 10 * ρ := by
    have rational_bound :
        (code (nearyMarker β) : ℚ) < (10 : ℚ) ^ (β + 1) := by
      exact_mod_cast marker_bound_nat
    rw [pow_succ] at rational_bound
    simpa only [μ, DecimalSetterMatrix.marker, ρ, mul_comm] using rational_bound
  have B_pos : 0 < B := by simp [B, upperScale]
  have marker_scaled : B * μ < B * (10 * ρ) :=
    mul_lt_mul_of_pos_left μ_upper B_pos
  have discrepancy_scaled_upper : δ * ρ < 5 * B := by
    rw [ratio_product] at ratio_scaled
    nlinarith
  have discrepancy_shell :=
    singletonPole_threeBlock_ruleCRoot_currentB_discrepancyShell
      β_large body targetLetter next pole
  change HasDecimalShell δ ((k : ℤ) - 1) ((k : ℤ) - 2) at discrepancy_shell
  have five_cast_value :
      (padicValNat 5 (P - V) : ℤ) = (k : ℤ) - 2 := by
    have valuation := discrepancy_shell.2.2
    rw [← difference_cast, padicValRat.of_nat] at valuation
    exact valuation
  have k_two_le : 2 ≤ k := by
    have valuation_nonneg : 0 ≤ (padicValNat 5 (P - V) : ℤ) := Int.natCast_nonneg _
    omega
  let width := k - 2
  have width_cast : (width : ℤ) = (k : ℤ) - 2 := by omega
  have difference_five_value : padicValNat 5 (P - V) = width := by
    rw [← width_cast] at five_cast_value
    exact_mod_cast five_cast_value
  have difference_two_value : padicValNat 2 (P - V) = k - 1 := by
    have valuation := discrepancy_shell.1.2
    rw [← difference_cast, padicValRat.of_nat] at valuation
    have depth_cast : ((k - 1 : Nat) : ℤ) = (k : ℤ) - 1 := by omega
    rw [← depth_cast] at valuation
    exact_mod_cast valuation
  have two_power_dvd : 2 ^ width ∣ P - V := by
    apply (padicValNat_dvd_iff (p := 2) width (P - V)).mpr
    exact Or.inr (by rw [difference_two_value]; omega)
  have five_power_dvd : 5 ^ width ∣ P - V := by
    apply (padicValNat_dvd_iff (p := 5) width (P - V)).mpr
    exact Or.inr (by rw [difference_five_value])
  have ten_power_dvd : 10 ^ width ∣ P - V := by
    rw [show 10 ^ width = 2 ^ width * 5 ^ width by
      rw [show 10 = 2 * 5 by norm_num, mul_pow]]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
      ((by norm_num : Nat.Coprime 2 5).pow width width) two_power_dvd five_power_dvd
  have power_le_difference : 10 ^ width ≤ P - V :=
    Nat.le_of_dvd (Nat.sub_pos_of_lt discrepancy_pos) ten_power_dvd
  have discrepancy_lower : ((10 ^ width : Nat) : ℚ) ≤ δ := by
    have cast_bound : ((10 ^ width : Nat) : ℚ) ≤ ((P - V : Nat) : ℚ) := by
      exact_mod_cast power_le_difference
    simpa only [difference_cast] using cast_bound
  have B_eq : B = (10 : ℚ) ^ k := by
    simp only [B, upperScale, k]
  have k_eq : k = width + 2 := by omega
  have power_factor : B = 100 * (10 : ℚ) ^ width := by
    rw [B_eq, k_eq, pow_add]
    norm_num
    ring
  have power_pos : 0 < (10 : ℚ) ^ width := by positivity
  norm_num at discrepancy_lower
  have power_scaled_lower : (10 : ℚ) ^ width * ρ ≤ δ * ρ :=
    mul_le_mul_of_nonneg_right discrepancy_lower rho_pos.le
  have rho_scaled_lower :
      1000 * (10 : ℚ) ^ width ≤ (10 : ℚ) ^ width * ρ := by
    have scaled := mul_le_mul_of_nonneg_left rho_bound power_pos.le
    nlinarith
  have forbidden_lower : 5 * B < δ * ρ := by
    rw [power_factor]
    have strict : 5 * (100 * (10 : ℚ) ^ width) <
        1000 * (10 : ℚ) ^ width := by nlinarith
    exact strict.trans_le (rho_scaled_lower.trans power_scaled_lower)
  exact (not_lt_of_ge forbidden_lower.le) discrepancy_scaled_upper

/-- No singleton current can reach a singleton target through any intervening block above the
canonical `R_c` root. -/
theorem singletonPole_threeBlock_ruleCRoot_singletonCurrent_impossible
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter currentLetter : TagLetter) (next : List NearyTile) :
    ¬HitsSquarePole β body [.erase targetLetter]
      [[.erase currentLetter], next, DecimalSetterMinimumBody.ruleCRoot] := by
  cases currentLetter with
  | b =>
      exact singletonPole_threeBlock_ruleCRoot_currentB_impossible
        β_large body targetLetter next
  | c =>
      exact singletonPole_threeBlock_ruleCRoot_currentC_impossible
        β_large body targetLetter next

end MatrixMortality.DecimalSetterBridgeRay
