import MatrixMortality.DecimalSetterContaminatedPoleGate
import MatrixMortality.DecimalSetterThreeBlockLongContamination

namespace MatrixMortality.DecimalSetterBridgeRay

open MatrixMortality.DecimalSetterAncestry
open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterBridge
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterChamber
open MatrixMortality.DecimalSetterDepth
open MatrixMortality.DecimalSetterMatrix

private theorem longRc_gapFactor_coprime_seven (β : Nat) :
    IsCoprime (gapFactor β) (7 : ℤ) := by
  have ten_coprime : IsCoprime ((10 : ℤ) ^ β) 7 :=
    (by norm_num : IsCoprime (10 : ℤ) 7).pow_left
  have twice_coprime : IsCoprime (2 * (10 : ℤ) ^ β) 7 :=
    (by norm_num : IsCoprime (2 : ℤ) 7).mul_left ten_coprime
  have shifted := twice_coprime.add_mul_left_left (-1)
  rw [show gapFactor β = 2 * (10 : ℤ) ^ β + 7 * (-1) by
    simp [gapFactor]
    ring]
  exact shifted

private theorem longRc_gapFactor_coprime_lift
    {β : Nat} (β_pos : 0 < β) :
    IsCoprime (gapFactor β) (decimalLift ((10 : ℤ) ^ β)) := by
  have q_ten := gapFactor_coprime_ten β_pos
  have q_two : IsCoprime (gapFactor β) (2 : ℤ) :=
    IsCoprime.of_isCoprime_of_dvd_right q_ten (by norm_num)
  have q_five : IsCoprime (gapFactor β) (5 : ℤ) :=
    IsCoprime.of_isCoprime_of_dvd_right q_ten (by norm_num)
  have q_seven := longRc_gapFactor_coprime_seven β
  have q_1750 : IsCoprime (gapFactor β) (1750 : ℤ) := by
    simpa using (q_two.mul_right (q_five.pow_right (n := 3))).mul_right q_seven
  have lift_eq :
      decimalLift ((10 : ℤ) ^ β) = 251 * gapFactor β + 1750 := by
    simp [decimalLift, gapFactor]
    ring
  rw [lift_eq]
  have shifted := q_1750.add_mul_right_right (251 : ℤ)
  simpa [add_comm] using shifted

private theorem longRc_singletonTrace_integer_coprime_gapFactor
    {β : Nat} (β_pos : 0 < β) (letter : TagLetter) :
    ∃ trace : ℤ,
      singletonTrace β letter = (trace : ℚ) ∧
        IsCoprime (gapFactor β) trace := by
  let ρ : ℤ := 10 ^ β
  let G : ℤ := decimalLift ρ
  have q_ten := gapFactor_coprime_ten β_pos
  have q_two : IsCoprime (gapFactor β) (2 : ℤ) :=
    IsCoprime.of_isCoprime_of_dvd_right q_ten (by norm_num)
  have q_rho : IsCoprime (gapFactor β) ρ := by
    simpa only [ρ] using q_ten.pow_right (n := β)
  have q_G : IsCoprime (gapFactor β) G := by
    simpa only [G, ρ] using longRc_gapFactor_coprime_lift β_pos
  cases letter with
  | c =>
      refine ⟨2 * ρ * G, ?_, (q_two.mul_right q_rho).mul_right q_G⟩
      rw [singletonCTrace_eq]
      norm_num [ρ, G, lift, decimalLift, Int.cast_sub, Int.cast_mul,
        Int.cast_pow]
  | b =>
      let B : ℤ := 5200 * ρ ^ 2 - 18398 * ρ + 2443
      have B_relation : B = G + gapFactor β * (2600 * ρ - 350) := by
        dsimp only [B, G, ρ]
        simp only [decimalLift, gapFactor]
        ring
      have q_B : IsCoprime (gapFactor β) B := by
        rw [B_relation]
        simpa [add_comm] using q_G.add_mul_right_right (2600 * ρ - 350)
      refine ⟨2 * ρ * B, ?_, (q_two.mul_right q_rho).mul_right q_B⟩
      rw [singletonBTrace_eq]
      norm_num [B, ρ, Int.cast_sub, Int.cast_add, Int.cast_mul,
        Int.cast_pow]

theorem terminalHead_sub_ten_marker_eq_neg_gapFactor (β : Nat) :
    (code (terminalHeadWord β) : ℤ) -
        10 * code (nearyMarker β) = -gapFactor β := by
  have marker_identity := markerWord_code_identity β
  have marker_relation :
      9 * (code (nearyMarker β) : ℤ) + 7 = 52 * (10 : ℤ) ^ β := by
    simpa only [markerWord, nearyMarker] using (by exact_mod_cast marker_identity)
  have terminal_code :
      (code (terminalHeadWord β) : ℤ) =
        50 * (10 : ℤ) ^ β + code (nearyMarker β) := by
    rw [show terminalHeadWord β = true :: markerWord β by rfl, code_cons]
    simp only [markerWord, nearyMarker, List.length_cons, List.length_replicate,
      digit, Int.natCast_add, Int.natCast_mul, Int.natCast_pow]
    rw [pow_succ]
    ring
  rw [terminal_code]
  simp only [gapFactor]
  linear_combination -marker_relation

theorem doubleCHead_sub_ten_marker_residue
    (β : Nat) (fringe : List Bool) (fringe_length : fringe.length = β) :
    18 *
        ((code (true :: true :: fringe) : ℤ) -
          10 * code (nearyMarker β)) =
      18 * (code fringe : ℤ) - 25 * gapFactor β - 35 := by
  have marker_relation_int :
      9 * (code (nearyMarker β) : ℤ) = 52 * (10 : ℤ) ^ β - 7 := by
    have marker_identity := markerWord_code_identity β
    have relation :
        9 * (code (nearyMarker β) : ℤ) + 7 = 52 * (10 : ℤ) ^ β := by
      simpa only [markerWord, nearyMarker] using (by exact_mod_cast marker_identity)
    linarith
  have head_code :
      (code (true :: true :: fringe) : ℤ) =
        55 * (10 : ℤ) ^ β + code fringe := by
    have natural :
        code (true :: true :: fringe) = 55 * 10 ^ β + code fringe := by
      rw [code_cons, code_cons]
      simp only [fringe_length]
      norm_num [digit]
      rw [fringe_length]
      ring
    exact_mod_cast natural
  rw [head_code]
  simp only [gapFactor]
  linear_combination -20 * marker_relation_int

theorem singletonPole_threeBlock_ruleCRoot_long_forces_headSupportProduct
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (next_multi : 2 ≤ next.length) (next_ends : EndsInErase next)
    (current_long : β + 3 ≤ (spell (nearyUpper β) current).length)
    (pole : HitsSquarePole β body [.erase targetLetter]
      [current, next, DecimalSetterMinimumBody.ruleCRoot]) :
    gapFactor β ∣
      (code (spell (nearyLower β body) current) : ℤ) *
        ((code (peeledHeadWord β (next.map NearyTile.letter)) : ℤ) -
          10 * code (nearyMarker β)) := by
  have β_pos : 0 < β := by omega
  let upperWord := spell (nearyUpper β) next ++ nearyMarker β
  let lowerWord := spell (nearyLower β body) next
  let k := (spell (nearyUpper β) next).length
  let width := k - 1
  let Hn := code (front width upperWord)
  let δ := upperBoundaryCode β next - lowerBoundaryCode β body next
  let E := gap ((10 : ℚ) ^ β)
  let G := lift ((10 : ℚ) ^ β)
  let μ := DecimalSetterMatrix.marker β
  let T := boundaryTrace β body current
  let V := lowerBoundaryCode β body current
  let A := upperScale β current
  let B := upperScale β next
  let S := singletonTrace β targetLetter
  let q : ℤ := gapFactor β
  let Ei : ℤ := decimalGap ((10 : ℤ) ^ β)
  let Gi : ℤ := decimalLift ((10 : ℤ) ^ β)
  let Mi : ℤ := code (nearyMarker β)
  let Hi : ℤ := code (peeledHeadWord β (next.map NearyTile.letter))
  let Pi : ℤ := code (spell (nearyUpper β) current ++ nearyMarker β)
  let Vi : ℤ := code (spell (nearyLower β body) current)
  let Ai : ℤ := 10 ^ (spell (nearyUpper β) current).length
  obtain ⟨Si, S_eq, qS_coprime⟩ :=
    longRc_singletonTrace_integer_coprime_gapFactor β_pos targetLetter
  have suffix := singletonPole_threeBlock_ruleCRoot_long_suffix
    β_large body targetLetter current_multi current_ends next_multi next_ends current_long pole
  change lowerWord.length = width ∧ back width upperWord = lowerWord ∧
    code upperWord - code lowerWord = Hn * 10 ^ width ∧
      HasDecimalShell (Hn : ℚ) 0 0 at suffix
  have discrepancy_pos : code lowerWord < code upperWord := by
    have rational := singletonPole_threeBlock_ruleCRoot_discrepancy_pos
      β_large body targetLetter current_ends pole
    change (code lowerWord : ℚ) < code upperWord at rational
    exact_mod_cast rational
  have difference_cast :
      (((code upperWord - code lowerWord : Nat) : ℚ)) =
        (code upperWord : ℚ) - code lowerWord := by
    rw [Nat.cast_sub discrepancy_pos.le]
  have δ_eq : δ = (Hn : ℚ) * (10 : ℚ) ^ width := by
    change (code upperWord : ℚ) - code lowerWord =
      (Hn : ℚ) * (10 : ℚ) ^ width
    rw [← difference_cast, suffix.2.2.1]
    norm_num
  have next_length_le_upper : next.length ≤ k := by
    dsimp only [k]
    rw [spell_nearyUpper]
    simpa using DecimalSetterChamber.length_le_tagEncode β (next.map NearyTile.letter)
  have k_two_le : 2 ≤ k := next_multi.trans next_length_le_upper
  have k_eq : k = width + 1 := by omega
  have B_eq : B = (10 : ℚ) ^ (width + 1) := by
    simp only [B, upperScale, k_eq, k]
  have exact_equation :=
    (hitsSquarePole_singleton_pair_ruleCRoot_iff_discrepancyEquation
      β_pos body targetLetter current next).mp pole
  change δ * (T * S - 7 * E * μ * G * A) = G * V * B * μ * S at exact_equation
  rw [δ_eq, B_eq] at exact_equation
  have power_ne : (10 : ℚ) ^ width ≠ 0 := pow_ne_zero _ (by norm_num)
  have core :
      (Hn : ℚ) * (T * S - 7 * E * μ * G * A) =
        10 * G * V * μ * S := by
    apply mul_left_cancel₀ power_ne
    linear_combination exact_equation
  have next_nonempty : next ≠ [] := by
    intro next_nil
    simp [next_nil] at next_multi
  have head_eq : Hn = code (peeledHeadWord β (next.map NearyTile.letter)) := by
    dsimp only [Hn, width, upperWord]
    rw [front_punctuatedUpper_eq_peeledHeadWord β next_nonempty]
  have E_cast : (Ei : ℚ) = E := by
    simp [Ei, E, decimalGap, gap]
  have G_cast : (Gi : ℚ) = G := by
    simp [Gi, G, decimalLift, lift]
  have M_cast : (Mi : ℚ) = μ := by
    simp [Mi, μ, DecimalSetterMatrix.marker]
  have H_cast : (Hi : ℚ) = Hn := by
    simp only [Hi, Int.cast_natCast, head_eq]
  have P_cast : (Pi : ℚ) = upperBoundaryCode β current := by
    simp [Pi, upperBoundaryCode]
  have V_cast : (Vi : ℚ) = V := by
    simp [Vi, V, lowerBoundaryCode]
  have A_cast : (Ai : ℚ) = A := by
    simp [Ai, A, upperScale]
  have T_eq : T = E * upperBoundaryCode β current + G * V := by
    rfl
  have core_integer_cast :
      (Hi : ℚ) *
          (((Ei * Pi + Gi * Vi : ℤ) : ℚ) * Si -
            7 * Ei * Mi * Gi * Ai) =
        10 * Gi * Vi * Mi * Si := by
    norm_num only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_ofNat]
    rw [H_cast, E_cast, G_cast, M_cast, P_cast, V_cast, A_cast, ← S_eq]
    rw [T_eq] at core
    exact core
  have core_integer :
      Hi * ((Ei * Pi + Gi * Vi) * Si - 7 * Ei * Mi * Gi * Ai) =
        10 * Gi * Vi * Mi * Si := by
    exact_mod_cast core_integer_cast
  have Ei_eq : Ei = 9 * q := by
    simp [Ei, q, decimalGap, gapFactor]
  have q_dvd_Ei : q ∣ Ei := ⟨9, by rw [Ei_eq]; ring⟩
  have support_identity :
      Gi * Si * (Vi * (Hi - 10 * Mi)) =
        Ei * (7 * Hi * Mi * Gi * Ai - Hi * Pi * Si) := by
    linear_combination core_integer
  have support_dvd : q ∣ Gi * Si * (Vi * (Hi - 10 * Mi)) := by
    rw [support_identity]
    exact dvd_mul_of_dvd_left q_dvd_Ei _
  have qG_coprime : IsCoprime q Gi := by
    simpa only [q, Gi] using longRc_gapFactor_coprime_lift β_pos
  have coefficient_coprime : IsCoprime q (Gi * Si) := by
    simpa only [q] using qG_coprime.mul_right qS_coprime
  have desired : q ∣ Vi * (Hi - 10 * Mi) :=
    coefficient_coprime.dvd_of_dvd_mul_left support_dvd
  simpa only [q, Vi, Hi, Mi] using desired

/-- On the `c c` peeled-head branch, the general support product reduces to the exact fringe
residue `18F-35` modulo the primitive gap. -/
theorem singletonPole_threeBlock_ruleCRoot_long_doubleC_forces_fringeSupportProduct
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (next_multi : 2 ≤ next.length) (next_ends : EndsInErase next)
    (current_long : β + 3 ≤ (spell (nearyUpper β) current).length)
    {fringe : List Bool} (fringe_length : fringe.length = β)
    (head_eq : peeledHeadWord β (next.map NearyTile.letter) =
      true :: true :: fringe)
    (pole : HitsSquarePole β body [.erase targetLetter]
      [current, next, DecimalSetterMinimumBody.ruleCRoot]) :
    gapFactor β ∣
      (code (spell (nearyLower β body) current) : ℤ) *
        (18 * code fringe - 35) := by
  let q : ℤ := gapFactor β
  let V : ℤ := code (spell (nearyLower β body) current)
  let H : ℤ := code (peeledHeadWord β (next.map NearyTile.letter))
  let M : ℤ := code (nearyMarker β)
  let R : ℤ := 18 * code fringe - 35
  have support : q ∣ V * (H - 10 * M) := by
    simpa only [q, V, H, M] using
      singletonPole_threeBlock_ruleCRoot_long_forces_headSupportProduct
        β_large body targetLetter current_multi current_ends next_multi next_ends current_long pole
  have coefficient_relation : 18 * (H - 10 * M) = R - 25 * q := by
    dsimp only [H, M, R, q]
    rw [head_eq]
    have relation := doubleCHead_sub_ten_marker_residue β fringe fringe_length
    linear_combination relation
  have scaled_support : q ∣ V * (18 * (H - 10 * M)) := by
    have multiplied := support.mul_right 18
    simpa [mul_assoc, mul_left_comm, mul_comm] using multiplied
  have shifted_support : q ∣ V * (R - 25 * q) := by
    rw [← coefficient_relation]
    exact scaled_support
  have correction : q ∣ V * (25 * q) := by
    exact dvd_mul_of_dvd_right (dvd_mul_left q 25) V
  have desired : q ∣ V * R := by
    have summed := dvd_add shifted_support correction
    simpa [mul_sub] using summed
  simpa only [q, V, R] using desired

/-- Every gap divisor absent from the `c c` fringe residue must enter the current lower code. -/
theorem singletonPole_threeBlock_ruleCRoot_long_doubleC_forces_gapDivisor_currentLower
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (next_multi : 2 ≤ next.length) (next_ends : EndsInErase next)
    (current_long : β + 3 ≤ (spell (nearyUpper β) current).length)
    {fringe : List Bool} (fringe_length : fringe.length = β)
    (head_eq : peeledHeadWord β (next.map NearyTile.letter) =
      true :: true :: fringe)
    {r : ℤ} (r_dvd_q : r ∣ gapFactor β)
    (fringe_coprime : IsCoprime r (18 * code fringe - 35))
    (pole : HitsSquarePole β body [.erase targetLetter]
      [current, next, DecimalSetterMinimumBody.ruleCRoot]) :
    r ∣ (code (spell (nearyLower β body) current) : ℤ) := by
  have q_product :=
    singletonPole_threeBlock_ruleCRoot_long_doubleC_forces_fringeSupportProduct
      β_large body targetLetter current_multi current_ends next_multi next_ends current_long
        fringe_length head_eq pole
  have r_product := r_dvd_q.trans q_product
  exact fringe_coprime.dvd_of_dvd_mul_right r_product

end MatrixMortality.DecimalSetterBridgeRay
