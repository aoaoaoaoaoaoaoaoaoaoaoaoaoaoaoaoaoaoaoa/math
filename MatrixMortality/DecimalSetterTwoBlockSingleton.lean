import MatrixMortality.DecimalSetterRuleCRootSingleton

/-!
# Complete two-block decimal singleton extinction

The two-block parser classifier fixes every prospective singleton pole above the canonical
`R_c` root with a current upper spelling of length `m≥β+3`. The `D_c` target is already
empty. For `D_b`, shell balance and decimal suffix exhaustion leave a prefix of length
`2β+2` satisfying

```text
B·K = 35μ·lift,    B=5200ρ²−18398ρ+2443.
```

The lawful lower bound on `K` exceeds the right side under coarse positive bounds. Hence
neither singleton target is reachable from a parser-lawful two-block source.
-/

namespace MatrixMortality.DecimalSetterBridgeRay

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterBridge
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterMatrix
open MatrixMortality.PadicValuation

/-- Exact trace polynomial for the singleton `D_b` target. -/
theorem singletonBTrace_eq (β : Nat) :
    singletonTrace β .b =
      2 * (10 : ℚ) ^ β *
        (5200 * ((10 : ℚ) ^ β) ^ 2 - 18398 * (10 : ℚ) ^ β + 2443) := by
  have marker_eq : DecimalSetterMatrix.marker β =
      (52 * (10 : ℚ) ^ β - 7) / 9 := by
    have relation := DecimalSetterMatrix.marker_relation β
    linarith
  have upper_eq : upperBoundaryCode β [.erase .b] =
      (10 * DecimalSetterMatrix.marker β + 5) * 10 ^ (β + 1) +
        DecimalSetterMatrix.marker β := by
    rw [upperBoundaryCode_eq]
    rw [show spell (nearyUpper β) [.erase .b] = tagCode β .b by
      simp [spell, nearyUpper]]
    rw [DecimalSetterMinimumBody.tagCodeB_code_eq]
    rfl
  rw [singletonTrace, upper_eq, marker_eq, pow_succ]
  unfold gap lift
  ring

/-- Over the canonical `R_c` root, the physical `D_b` singleton pole is exactly the displayed
coefficient-weighted upper/lower code discrepancy. -/
theorem hitsSquarePole_singletonB_ruleCRoot_iff_codeDiscrepancy
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (current : List NearyTile) :
    HitsSquarePole β body [.erase .b]
        [current, DecimalSetterMinimumBody.ruleCRoot] ↔
      2 * (10 : ℚ) ^ β *
          (5200 * ((10 : ℚ) ^ β) ^ 2 - 18398 * (10 : ℚ) ^ β + 2443) *
          (upperBoundaryCode β current - lowerBoundaryCode β body current) =
        7 * DecimalSetterMatrix.marker β * lift ((10 : ℚ) ^ β) *
          upperScale β current := by
  rw [hitsSquarePole_singleton_ruleCRoot_iff_traceDiscrepancy β_pos,
    singletonBTrace_eq]

/-- No parser-lawful two-block source reaches the singleton `D_b` pole when `β≥3`.

The exact shell forces a shared decimal suffix. Its complementary prefix has length `2β+2`,
but the reduced pole equation and coarse positive coefficient bounds make that prefix too small. -/
theorem singletonB_twoBlockSource_impossible
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    {current root : List NearyTile} (source_law : BlocksLaw [current, root]) :
    ¬HitsSquarePole β body [.erase .b] [current, root] := by
  intro pole
  obtain ⟨root_eq, _, current_long⟩ :=
    singletonPole_twoBlockSource_classifier β_large body .b source_law pole
  subst root
  let upperWord := spell (nearyUpper β) current ++ nearyMarker β
  let lowerWord := spell (nearyLower β body) current
  let m := (spell (nearyUpper β) current).length
  let P := code upperWord
  let V := code lowerWord
  let ρ : ℚ := 10 ^ β
  let μ : ℚ := DecimalSetterMatrix.marker β
  let G := lift ρ
  let B := 5200 * ρ ^ 2 - 18398 * ρ + 2443
  have β_pos : 0 < β := by omega
  have m_large : β + 3 ≤ m := by simpa only [m] using current_long
  let width := m - β - 1
  have width_pos : 0 < width := by omega
  have m_eq : m = β + (width + 1) := by omega
  have rational_equation :=
    (hitsSquarePole_singletonB_ruleCRoot_iff_codeDiscrepancy β_pos body current).mp pole
  have rational_equation' :
      2 * ρ * B * ((P : ℚ) - V) =
        7 * μ * G * (10 : ℚ) ^ m := by
    simpa only [upperBoundaryCode, lowerBoundaryCode, upperScale,
      upperWord, lowerWord, m, P, V, ρ, μ, G, B] using rational_equation
  have rho_bound : (1000 : ℚ) ≤ ρ := by
    have natural_bound : 10 ^ 3 ≤ 10 ^ β :=
      Nat.pow_le_pow_right (by norm_num) β_large
    norm_num at natural_bound ⊢
    dsimp only [ρ]
    exact_mod_cast natural_bound
  have rho_pos : 0 < ρ := lt_of_lt_of_le (by norm_num) rho_bound
  have μ_pos : 0 < μ := by
    simpa only [μ] using DecimalSetterMatrix.marker_pos β
  have G_pos : 0 < G := by
    dsimp only [G]
    unfold lift
    linarith
  have B_lower : (4000 : ℚ) < B := by
    have factor_lower : (2 : ℚ) < 5200 * ρ - 18398 := by linarith
    have product_lower : (2000 : ℚ) < ρ * (5200 * ρ - 18398) := by
      nlinarith
    dsimp only [B]
    nlinarith
  have difference_pos_rat : (0 : ℚ) < (P : ℚ) - V := by
    have left_scale_pos : 0 < 2 * ρ * B := by positivity
    have right_pos : 0 < 7 * μ * G * (10 : ℚ) ^ m := by positivity
    nlinarith [rational_equation']
  have difference_pos : V < P := by exact_mod_cast sub_pos.mp difference_pos_rat
  have difference_cast : (((P - V : Nat) : ℚ)) = (P : ℚ) - V := by
    rw [Nat.cast_sub difference_pos.le]
  have marker_unit := marker_hasDecimalShell β_pos
  have lift_unit := lift_tenPow_hasDecimalShell β_pos
  have seven_unit : HasDecimalShell (7 : ℚ) 0 0 :=
    intCast_hasDecimalShell_of_mod_seven (Int.ModEq.refl 7)
  have scale_shell : HasDecimalShell ((10 : ℚ) ^ m) m m := by
    simpa using ten_hasDecimalShell.pow m
  have right_shell : HasDecimalShell (7 * μ * G * (10 : ℚ) ^ m) m m := by
    simpa only [μ, G, ρ, zero_add, add_zero] using
      ((seven_unit.mul marker_unit).mul lift_unit).mul scale_shell
  have target_shell := singletonTrace_hasDecimalShell β_pos .b
  have trace_equation :
      singletonTrace β .b * ((P : ℚ) - V) =
        7 * μ * G * (10 : ℚ) ^ m := by
    rw [singletonBTrace_eq]
    simpa only [ρ, B] using rational_equation'
  have difference_eq_div :
      (P : ℚ) - V =
        (7 * μ * G * (10 : ℚ) ^ m) / singletonTrace β .b := by
    apply (eq_div_iff target_shell.1.1).2
    simpa only [mul_comm] using trace_equation
  have difference_shell :
      HasDecimalShell ((P : ℚ) - V) width (width + 1) := by
    have two_depth : (m : ℤ) - ((β : ℤ) + 1) = width := by
      dsimp only [width]
      omega
    have five_depth : (m : ℤ) - (β : ℤ) = width + 1 := by
      dsimp only [width]
      omega
    rw [difference_eq_div]
    constructor
    · have shell := div_hasValue right_shell.1 target_shell.1
      simpa only [two_depth] using shell
    · have shell := div_hasValue right_shell.2 target_shell.2
      simpa only [five_depth] using shell
  have difference_two_value : padicValNat 2 (P - V) = width := by
    have valuation := difference_shell.1.2
    rw [← difference_cast, padicValRat.of_nat] at valuation
    exact_mod_cast valuation
  have difference_five_value : padicValNat 5 (P - V) = width + 1 := by
    have valuation := difference_shell.2.2
    rw [← difference_cast, padicValRat.of_nat] at valuation
    exact_mod_cast valuation
  have two_power_dvd : 2 ^ width ∣ P - V := by
    apply (padicValNat_dvd_iff (p := 2) width (P - V)).mpr
    exact Or.inr (by rw [difference_two_value])
  have five_power_dvd : 5 ^ width ∣ P - V := by
    apply (padicValNat_dvd_iff (p := 5) width (P - V)).mpr
    exact Or.inr (by rw [difference_five_value]; omega)
  have ten_power_dvd : 10 ^ width ∣ P - V := by
    rw [show 10 ^ width = 2 ^ width * 5 ^ width by
      rw [show 10 = 2 * 5 by norm_num, mul_pow]]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
      ((by norm_num : Nat.Coprime 2 5).pow width width) two_power_dvd five_power_dvd
  have next_two_not_dvd : ¬2 ^ (width + 1) ∣ P - V := by
    intro next_dvd
    have valuation_bound := (padicValNat_dvd_iff (p := 2) (width + 1) (P - V)).mp next_dvd
    rcases valuation_bound with difference_zero | valuation_bound
    · omega
    · rw [difference_two_value] at valuation_bound
      omega
  have two_power_exact : ¬2 * 10 ^ width ∣ P - V := by
    intro forbidden
    apply next_two_not_dvd
    apply dvd_trans _ forbidden
    refine ⟨5 ^ width, ?_⟩
    rw [pow_succ, show 10 ^ width = (2 * 5) ^ width by norm_num, mul_pow]
    ring
  have upper_length : upperWord.length = m + β + 1 := by
    simp [upperWord, m, nearyMarker]
    omega
  have width_lt_upper : width < upperWord.length := by omega
  obtain ⟨_, _, difference_front⟩ :=
    suffix_exhaustion_factorization upperWord lowerWord width width_pos width_lt_upper
      difference_pos ten_power_dvd two_power_exact
  let K := code (front width upperWord)
  have difference_front_rat : (P : ℚ) - V = K * (10 : ℚ) ^ width := by
    rw [← difference_cast, difference_front]
    norm_num [K]
  have front_equation : B * K = 35 * μ * G := by
    have scale_ne : 2 * ρ * (10 : ℚ) ^ width ≠ 0 := by positivity
    apply mul_left_cancel₀ scale_ne
    calc
      (2 * ρ * 10 ^ width) * (B * K) =
          2 * ρ * B * (K * 10 ^ width) := by ring
      _ = 7 * μ * G * 10 ^ m := by
        rw [← rational_equation', difference_front_rat]
      _ = (2 * ρ * 10 ^ width) * (35 * μ * G) := by
        rw [m_eq, pow_add, pow_succ]
        dsimp only [ρ]
        ring
  have front_length : (front width upperWord).length = 2 * β + 2 := by
    rw [length_front, upper_length]
    omega
  have front_ne : front width upperWord ≠ [] := by
    intro front_nil
    have length_eq := congrArg List.length front_nil
    simp [front_length] at length_eq
  obtain ⟨frontBit, frontTail, front_eq⟩ := List.exists_cons_of_ne_nil front_ne
  have frontTail_length : frontTail.length = 2 * β + 1 := by
    simpa [front_eq] using front_length
  have front_lower : 5 * 10 ^ (2 * β + 1) ≤ K := by
    dsimp only [K]
    rw [front_eq]
    simpa only [frontTail_length] using five_mul_pow_length_le_code frontBit frontTail
  have front_power_eq : 5 * 10 ^ (2 * β + 1) = 50 * (10 ^ β) ^ 2 := by
    rw [show 2 * β + 1 = β + β + 1 by omega, pow_succ, pow_add]
    ring
  have front_lower_rat : 50 * ρ ^ 2 ≤ (K : ℚ) := by
    rw [front_power_eq] at front_lower
    dsimp only [ρ]
    exact_mod_cast front_lower
  have K_pos : (0 : ℚ) < K := lt_of_lt_of_le (by positivity) front_lower_rat
  have marker_upper_nat : code (nearyMarker β) < 10 ^ (β + 1) :=
    code_lt_pow_length (nearyMarker β) |>.trans_eq (by simp [nearyMarker])
  have marker_power_eq : 10 ^ (β + 1) = 10 * 10 ^ β := by
    rw [pow_succ, mul_comm]
  have μ_upper : μ < 10 * ρ := by
    rw [marker_power_eq] at marker_upper_nat
    simpa only [μ, DecimalSetterMatrix.marker, ρ] using
      (show (code (nearyMarker β) : ℚ) < 10 * (10 : ℚ) ^ β by
        exact_mod_cast marker_upper_nat)
  have G_upper : G < 502 * ρ := by
    dsimp only [G]
    unfold lift
    linarith
  have right_upper : 35 * μ * G < 175700 * ρ ^ 2 := by
    calc
      35 * μ * G < 35 * (10 * ρ) * G := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_left μ_upper (by norm_num)) G_pos
      _ < 35 * (10 * ρ) * (502 * ρ) := by
        exact mul_lt_mul_of_pos_left G_upper (mul_pos (by norm_num) (mul_pos (by norm_num) rho_pos))
      _ = 175700 * ρ ^ 2 := by ring
  have left_lower : 200000 * ρ ^ 2 < B * (K : ℚ) := by
    calc
      200000 * ρ ^ 2 = 4000 * (50 * ρ ^ 2) := by ring
      _ ≤ 4000 * (K : ℚ) :=
        mul_le_mul_of_nonneg_left front_lower_rat (by norm_num)
      _ < B * (K : ℚ) := mul_lt_mul_of_pos_right B_lower K_pos
  rw [front_equation] at left_lower
  nlinarith [sq_pos_of_pos rho_pos]

/-- No parser-lawful two-block source reaches either singleton target when `β≥3`. -/
theorem singletonTarget_twoBlockSource_impossible
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (letter : TagLetter) {current root : List NearyTile}
    (source_law : BlocksLaw [current, root]) :
    ¬HitsSquarePole β body [.erase letter] [current, root] := by
  cases letter with
  | b => exact singletonB_twoBlockSource_impossible β_large body source_law
  | c => exact singletonC_twoBlockSource_impossible β_large body source_law

end MatrixMortality.DecimalSetterBridgeRay
