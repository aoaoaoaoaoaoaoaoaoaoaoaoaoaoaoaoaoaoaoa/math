import MatrixMortality.DecimalSetterThreeBlockSingletonCurrent

/-!
# Short-current valuations at a three-block singleton pole

The exact `R_c` discrepancy equation determines both decimal valuations through upper length
`β+1`. At upper length `β+2`, only the two-adic boundary cancellation remains.
-/

namespace MatrixMortality.DecimalSetterBridgeRay

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterBridge
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterDepth
open MatrixMortality.DecimalSetterMatrix
open MatrixMortality.PadicValuation

private theorem code_append_bit_false_false_mod_forty
    (stem : List Bool) (bit : Bool) :
    (code (stem ++ [bit, false, false]) : ℤ) ≡ 17 [ZMOD 40] := by
  rw [code_append]
  cases bit with
  | false =>
      change (code stem : ℤ) * 1000 + 777 ≡ 17 [ZMOD 40]
      rw [Int.modEq_iff_dvd]
      exact ⟨-19 - 25 * (code stem : ℤ), by ring⟩
  | true =>
      change (code stem : ℤ) * 1000 + 577 ≡ 17 [ZMOD 40]
      rw [Int.modEq_iff_dvd]
      exact ⟨-14 - 25 * (code stem : ℤ), by ring⟩

private theorem punctuatedUpper_mod_forty
    {β : Nat} (β_large : 3 ≤ β) (roles : List NearyTile) :
    (code (spell (nearyUpper β) roles ++ nearyMarker β) : ℤ) ≡ 17 [ZMOD 40] := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le β_large
  have word_eq :
      spell (nearyUpper (3 + offset)) roles ++ nearyMarker (3 + offset) =
        (spell (nearyUpper (3 + offset)) roles ++
          true :: List.replicate offset false) ++ [false, false, false] := by
    simp [nearyMarker, List.replicate_add, List.append_assoc, Nat.add_comm]
  rw [word_eq]
  exact code_append_bit_false_false_mod_forty _ false

private theorem spellLower_ends_false
    (β : Nat) (body : List TagLetter) (roles : List NearyTile) (roles_ne : roles ≠ []) :
    ∃ stem, spell (nearyLower β body) roles = stem ++ [false] := by
  induction roles with
  | nil => exact False.elim (roles_ne rfl)
  | cons role tail induction =>
      by_cases tail_empty : tail = []
      · subst tail
        obtain ⟨_, lower, _, lower_eq⟩ := nearyTile_final_mismatch β body role
        exact ⟨lower, by simpa [spell] using lower_eq⟩
      · obtain ⟨stem, shape⟩ := induction tail_empty
        exact ⟨nearyLower β body role ++ stem, by
          change nearyLower β body role ++ spell (nearyLower β body) tail = _
          rw [shape, List.append_assoc]⟩

private theorem spellLower_ends_false_false
    (β : Nat) (body : List TagLetter) {roles : List NearyTile}
    (roles_multi : 2 ≤ roles.length) (roles_ends : EndsInErase roles) :
    ∃ stem, spell (nearyLower β body) roles = stem ++ [false, false] := by
  obtain ⟨front, letter, roles_eq⟩ := roles_ends
  have front_ne : front ≠ [] := by
    intro front_eq
    rw [roles_eq, front_eq] at roles_multi
    simp at roles_multi
  obtain ⟨stem, front_eq⟩ := spellLower_ends_false β body front front_ne
  refine ⟨stem, ?_⟩
  rw [roles_eq, spell_append, front_eq]
  simp [spell, nearyLower, List.append_assoc]

private theorem roleLength_le_lowerLength
    (β : Nat) (body : List TagLetter) (roles : List NearyTile) :
    roles.length ≤ (spell (nearyLower β body) roles).length := by
  induction roles with
  | nil => simp [spell]
  | cons role tail induction =>
      have role_pos : 0 < (nearyLower β body role).length :=
        List.length_pos_of_ne_nil (nearyLower_ne_nil β body role)
      rw [show spell (nearyLower β body) (role :: tail) =
        nearyLower β body role ++ spell (nearyLower β body) tail by rfl]
      simp only [List.length_cons, List.length_append]
      omega

private theorem lowerBoundary_mod_forty_of_three_le_endsInErase
    (β : Nat) (body : List TagLetter) {roles : List NearyTile}
    (roles_large : 3 ≤ roles.length) (roles_ends : EndsInErase roles) :
    (code (spell (nearyLower β body) roles) : ℤ) ≡ 17 [ZMOD 40] := by
  obtain ⟨stem, lower_eq⟩ :=
    spellLower_ends_false_false β body (by omega) roles_ends
  have stem_ne : stem ≠ [] := by
    intro stem_empty
    have length_bound := roleLength_le_lowerLength β body roles
    rw [lower_eq, stem_empty] at length_bound
    simp at length_bound
    omega
  let bit := stem.getLast stem_ne
  have stem_eq : stem = stem.dropLast ++ [bit] := by
    simpa only [bit] using (List.dropLast_append_getLast stem_ne).symm
  rw [lower_eq, stem_eq, List.append_assoc]
  exact code_append_bit_false_false_mod_forty _ bit

/-- A multi-role erasure-ended boundary trace is ten times an integer congruent to one modulo
five. This retains the leading residue discarded by its `(1,1)` shell. -/
theorem multiRoleErasureEnded_boundaryTrace_tenFactor
    {β : Nat} (β_large : 2 ≤ β) (body : List TagLetter)
    {roles : List NearyTile} (roles_multi : 2 ≤ roles.length)
    (roles_ends : EndsInErase roles) :
    ∃ unit : ℤ,
      boundaryTrace β body roles = ((10 * unit : ℤ) : ℚ) ∧
        unit ≡ 1 [ZMOD 5] := by
  let ρ : ℤ := 10 ^ β
  let E : ℤ := decimalGap ρ
  let G : ℤ := decimalLift ρ
  let P : ℤ := code (spell (nearyUpper β) roles ++ nearyMarker β)
  let V : ℤ := code (spell (nearyLower β body) roles)
  let T : ℤ := E * P + G * V
  have rho_mod : ρ ≡ 0 [ZMOD 100] := by
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le β_large
    have square_mod : (10 : ℤ) ^ 2 ≡ 0 [ZMOD 100] := by norm_num
    simpa [ρ, pow_add, mul_comm] using
      square_mod.mul (Int.ModEq.refl ((10 : ℤ) ^ offset))
  have gap_mod : E ≡ 37 [ZMOD 100] := by
    calc
      E = 18 * ρ - 63 := by simp [E, decimalGap]; ring
      _ ≡ 18 * 0 - 63 [ZMOD 100] :=
        ((Int.ModEq.refl 18).mul rho_mod).sub (Int.ModEq.refl 63)
      _ ≡ 37 [ZMOD 100] := by norm_num
  have lift_mod : G ≡ 93 [ZMOD 100] := by
    calc
      G = 502 * ρ - 7 := by simp [G, decimalLift]
      _ ≡ 502 * 0 - 7 [ZMOD 100] :=
        ((Int.ModEq.refl 502).mul rho_mod).sub (Int.ModEq.refl 7)
      _ ≡ 93 [ZMOD 100] := by norm_num
  have upper_mod : P ≡ 77 [ZMOD 100] := by
    simpa only [P] using
      MatrixMortality.DecimalSetterShallow.upperBoundaryCode_mod_hundred β_large roles
  have lower_mod : V ≡ 77 [ZMOD 100] := by
    simpa only [V] using
      MatrixMortality.DecimalSetterShallow.lowerBoundaryCode_mod_hundred_of_multi_endsInErase
        β body roles_multi roles_ends
  have trace_mod : T ≡ 10 [ZMOD 100] := by
    calc
      T = E * P + G * V := rfl
      _ ≡ 37 * 77 + 93 * 77 [ZMOD 100] :=
        (gap_mod.mul upper_mod).add (lift_mod.mul lower_mod)
      _ ≡ 10 [ZMOD 100] := by norm_num
  rw [Int.modEq_iff_dvd] at trace_mod
  obtain ⟨carry, carry_eq⟩ := trace_mod
  let unit := 1 - 10 * carry
  have trace_eq : T = 10 * unit := by
    dsimp only [unit]
    omega
  have unit_mod : unit ≡ 1 [ZMOD 5] := by
    dsimp only [unit]
    rw [Int.modEq_iff_dvd]
    exact ⟨2 * carry, by ring⟩
  refine ⟨unit, ?_, unit_mod⟩
  have boundary_eq : boundaryTrace β body roles = (T : ℚ) := by
    norm_num [T, E, G, P, V, ρ, boundaryTrace, gap, lift, decimalGap,
      decimalLift, upperBoundaryCode, lowerBoundaryCode]
  rw [boundary_eq, trace_eq]

/-- A three-role erasure-ended boundary trace is ten times an integer congruent to one modulo
four. The modulus forty sees one digit beyond the ordinary `(1,1)` shell. -/
theorem threeRoleErasureEnded_boundaryTrace_tenFactor_mod_four
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    {roles : List NearyTile} (roles_large : 3 ≤ roles.length)
    (roles_ends : EndsInErase roles) :
    ∃ unit : ℤ,
      boundaryTrace β body roles = ((10 * unit : ℤ) : ℚ) ∧
        unit ≡ 1 [ZMOD 4] := by
  let ρ : ℤ := 10 ^ β
  let E : ℤ := decimalGap ρ
  let G : ℤ := decimalLift ρ
  let P : ℤ := code (spell (nearyUpper β) roles ++ nearyMarker β)
  let V : ℤ := code (spell (nearyLower β body) roles)
  let T : ℤ := E * P + G * V
  have rho_mod : ρ ≡ 0 [ZMOD 40] := by
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le β_large
    have cube_mod : (10 : ℤ) ^ 3 ≡ 0 [ZMOD 40] := by norm_num
    simpa [ρ, pow_add, mul_comm] using
      cube_mod.mul (Int.ModEq.refl ((10 : ℤ) ^ offset))
  have gap_mod : E ≡ 17 [ZMOD 40] := by
    calc
      E = 18 * ρ - 63 := by simp [E, decimalGap]; ring
      _ ≡ 18 * 0 - 63 [ZMOD 40] :=
        ((Int.ModEq.refl 18).mul rho_mod).sub (Int.ModEq.refl 63)
      _ ≡ 17 [ZMOD 40] := by norm_num
  have lift_mod : G ≡ 33 [ZMOD 40] := by
    calc
      G = 502 * ρ - 7 := by simp [G, decimalLift]
      _ ≡ 502 * 0 - 7 [ZMOD 40] :=
        ((Int.ModEq.refl 502).mul rho_mod).sub (Int.ModEq.refl 7)
      _ ≡ 33 [ZMOD 40] := by norm_num
  have upper_mod : P ≡ 17 [ZMOD 40] := by
    simpa only [P] using punctuatedUpper_mod_forty β_large roles
  have lower_mod : V ≡ 17 [ZMOD 40] := by
    simpa only [V] using
      lowerBoundary_mod_forty_of_three_le_endsInErase β body roles_large roles_ends
  have trace_mod : T ≡ 10 [ZMOD 40] := by
    calc
      T = E * P + G * V := rfl
      _ ≡ 17 * 17 + 33 * 17 [ZMOD 40] :=
        (gap_mod.mul upper_mod).add (lift_mod.mul lower_mod)
      _ ≡ 10 [ZMOD 40] := by norm_num
  rw [Int.modEq_iff_dvd] at trace_mod
  obtain ⟨carry, carry_eq⟩ := trace_mod
  let unit := 1 - 4 * carry
  have trace_eq : T = 10 * unit := by
    dsimp only [unit]
    omega
  have unit_mod : unit ≡ 1 [ZMOD 4] := by
    dsimp only [unit]
    rw [Int.modEq_iff_dvd]
    exact ⟨carry, by ring⟩
  refine ⟨unit, ?_, unit_mod⟩
  have boundary_eq : boundaryTrace β body roles = (T : ℚ) := by
    norm_num [T, E, G, P, V, ρ, boundaryTrace, gap, lift, decimalGap,
      decimalLift, upperBoundaryCode, lowerBoundaryCode]
  rw [boundary_eq, trace_eq]

/-- Both singleton traces are `2·10^β` times an integer congruent to three modulo five. -/
theorem singletonTrace_two_tenPowFactor
    {β : Nat} (β_pos : 0 < β) (letter : TagLetter) :
    ∃ unit : ℤ,
      singletonTrace β letter = ((2 * 10 ^ β * unit : ℤ) : ℚ) ∧
        unit ≡ 3 [ZMOD 5] := by
  let ρ : ℤ := 10 ^ β
  have rho_mod : ρ ≡ 0 [ZMOD 5] := by
    have ten_mod : (10 : ℤ) ≡ 0 [ZMOD 5] := by norm_num
    simpa only [ρ, zero_pow β_pos.ne'] using ten_mod.pow β
  cases letter with
  | c =>
      let unit : ℤ := decimalLift ρ
      have unit_mod : unit ≡ 3 [ZMOD 5] := by
        calc
          unit = 502 * ρ - 7 := by simp [unit, decimalLift]
          _ ≡ 502 * 0 - 7 [ZMOD 5] :=
            ((Int.ModEq.refl 502).mul rho_mod).sub (Int.ModEq.refl 7)
          _ ≡ 3 [ZMOD 5] := by norm_num
      refine ⟨unit, ?_, unit_mod⟩
      rw [singletonCTrace_eq]
      norm_num [unit, ρ, lift, decimalLift]
  | b =>
      let unit : ℤ := 5200 * ρ ^ 2 - 18398 * ρ + 2443
      have unit_mod : unit ≡ 3 [ZMOD 5] := by
        calc
          unit = 5200 * ρ ^ 2 - 18398 * ρ + 2443 := rfl
          _ ≡ 5200 * 0 ^ 2 - 18398 * 0 + 2443 [ZMOD 5] :=
            (((Int.ModEq.refl 5200).mul (rho_mod.pow 2)).sub
              ((Int.ModEq.refl 18398).mul rho_mod)).add (Int.ModEq.refl 2443)
          _ ≡ 3 [ZMOD 5] := by norm_num
      refine ⟨unit, ?_, unit_mod⟩
      rw [singletonBTrace_eq]
      norm_num [unit, ρ]

/-- Below the first boundary length, an `R_c`-rooted three-block singleton pole fixes both
valuations of the intervening discrepancy. -/
theorem singletonPole_threeBlock_ruleCRoot_currentUpper_le_beta_discrepancyShell
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (current_upper_le : (spell (nearyUpper β) current).length ≤ β)
    (pole : HitsSquarePole β body [.erase targetLetter]
      [current, next, DecimalSetterMinimumBody.ruleCRoot]) :
    HasDecimalShell
      (upperBoundaryCode β next - lowerBoundaryCode β body next)
      (((spell (nearyUpper β) next).length : ℤ) + β + 1 -
        (spell (nearyUpper β) current).length)
      (((spell (nearyUpper β) next).length : ℤ) + β -
        (spell (nearyUpper β) current).length) := by
  have β_pos : 0 < β := by omega
  let m := (spell (nearyUpper β) current).length
  let k := (spell (nearyUpper β) next).length
  let δ := upperBoundaryCode β next - lowerBoundaryCode β body next
  let E := gap ((10 : ℚ) ^ β)
  let G := lift ((10 : ℚ) ^ β)
  let μ := DecimalSetterMatrix.marker β
  let T := boundaryTrace β body current
  let V := lowerBoundaryCode β body current
  let A := upperScale β current
  let B := upperScale β next
  let S := singletonTrace β targetLetter
  let K := T * S - 7 * E * μ * G * A
  have trace_shell : HasDecimalShell T 1 1 := by
    simpa only [T, boundaryTrace] using
      MatrixMortality.DecimalSetterShallow.multiRoleErasureEnded_boundaryTrace_hasDecimalShell
        (show 2 ≤ β by omega) body current_multi current_ends
  have target_shell : HasDecimalShell S (β + 1) β := by
    simpa only [S] using singletonTrace_hasDecimalShell β_pos targetLetter
  have trace_product_shell : HasDecimalShell (T * S) (β + 2) (β + 1) := by
    convert trace_shell.mul target_shell using 1 <;> omega
  have seven_unit : HasDecimalShell (7 : ℚ) 0 0 :=
    intCast_hasDecimalShell_of_mod_seven (Int.ModEq.refl 7)
  have scale_shell : HasDecimalShell A m m := by
    have shell := ten_hasDecimalShell.pow m
    norm_num at shell
    simpa only [A, upperScale, m] using shell
  have correction_shell : HasDecimalShell (7 * E * μ * G * A) m m := by
    convert ((((seven_unit.mul (gap_tenPow_hasDecimalShell β_pos)).mul
      (marker_hasDecimalShell β_pos)).mul (lift_tenPow_hasDecimalShell β_pos)).mul
        scale_shell) using 1 <;> simp
  have coefficient_shell : HasDecimalShell K m m := by
    constructor
    · have shell := sub_hasValue_min trace_product_shell.1.1 correction_shell.1.1 (by
        rw [trace_product_shell.1.2, correction_shell.1.2]
        omega)
      rw [trace_product_shell.1.2, correction_shell.1.2,
        min_eq_right (show (m : ℤ) ≤ β + 2 by omega)] at shell
      simpa only [K] using shell
    · have shell := sub_hasValue_min trace_product_shell.2.1 correction_shell.2.1 (by
        rw [trace_product_shell.2.2, correction_shell.2.2]
        omega)
      rw [trace_product_shell.2.2, correction_shell.2.2,
        min_eq_right (show (m : ℤ) ≤ β + 1 by omega)] at shell
      simpa only [K] using shell
  have lower_unit : HasDecimalShell V 0 0 := by
    simpa only [V] using
      lowerBoundaryCode_hasDecimalShell_of_endsInErase β body current_ends
  have next_scale_shell : HasDecimalShell B k k := by
    have shell := ten_hasDecimalShell.pow k
    norm_num at shell
    simpa only [B, upperScale, k] using shell
  have right_shell : HasDecimalShell (G * V * B * μ * S)
      (k + β + 1) (k + β) := by
    convert (((((lift_tenPow_hasDecimalShell β_pos).mul lower_unit).mul
      next_scale_shell).mul (marker_hasDecimalShell β_pos)).mul target_shell) using 1 <;>
        omega
  have exact_equation :=
    (hitsSquarePole_singleton_pair_ruleCRoot_iff_discrepancyEquation
      β_pos body targetLetter current next).mp pole
  change δ * K = G * V * B * μ * S at exact_equation
  have δ_eq : δ = (G * V * B * μ * S) / K := by
    apply (eq_div_iff coefficient_shell.1.1).2
    exact exact_equation
  change HasDecimalShell δ ((k : ℤ) + β + 1 - m) ((k : ℤ) + β - m)
  rw [δ_eq]
  constructor
  · simpa using div_hasValue right_shell.1 coefficient_shell.1
  · simpa using div_hasValue right_shell.2 coefficient_shell.2

/-- At upper length `β+1`, the singleton coefficient has exact five-depth `β+1`; the apparent
equal-depth cancellation is excluded by its normalized residue `2 mod 5`. -/
theorem singletonCoefficient_currentUpper_eq_beta_add_one_hasValue_five
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current : List NearyTile}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (current_upper_eq : (spell (nearyUpper β) current).length = β + 1) :
    HasValue 5
      (boundaryTrace β body current * singletonTrace β targetLetter -
        7 * gap ((10 : ℚ) ^ β) * DecimalSetterMatrix.marker β *
          lift ((10 : ℚ) ^ β) * upperScale β current)
      (β + 1) := by
  have β_pos : 0 < β := by omega
  let ρ : ℤ := 10 ^ β
  let E : ℤ := decimalGap ρ
  let G : ℤ := decimalLift ρ
  let M : ℤ := code (nearyMarker β)
  obtain ⟨traceUnit, trace_eq, trace_mod⟩ :=
    multiRoleErasureEnded_boundaryTrace_tenFactor
      (show 2 ≤ β by omega) body current_multi current_ends
  obtain ⟨targetUnit, target_eq, target_mod⟩ :=
    singletonTrace_two_tenPowFactor β_pos targetLetter
  have rho_dvd : (5 : ℤ) ∣ ρ := by
    have power_dvd : (5 : ℤ) ^ β ∣ (10 : ℤ) ^ β :=
      pow_dvd_pow_of_dvd (by norm_num) β
    exact (dvd_pow_self 5 (Nat.ne_of_gt β_pos)).trans power_dvd
  have gap_mod : E ≡ 2 [ZMOD 5] := by
    calc
      E = 18 * ρ - 63 := by simp [E, decimalGap]; ring
      _ ≡ 18 * 0 - 63 [ZMOD 5] :=
        ((Int.ModEq.refl 18).mul (Int.modEq_zero_iff_dvd.mpr rho_dvd)).sub
          (Int.ModEq.refl 63)
      _ ≡ 2 [ZMOD 5] := by norm_num
  have lift_mod : G ≡ 3 [ZMOD 5] := by
    calc
      G = 502 * ρ - 7 := by simp [G, decimalLift]
      _ ≡ 502 * 0 - 7 [ZMOD 5] :=
        ((Int.ModEq.refl 502).mul (Int.modEq_zero_iff_dvd.mpr rho_dvd)).sub
          (Int.ModEq.refl 7)
      _ ≡ 3 [ZMOD 5] := by norm_num
  have marker_relation : 9 * M + 7 = 52 * ρ := by
    have natural_relation :
        9 * code (nearyMarker β) + 7 = 52 * 10 ^ β := by
      simpa only [MatrixMortality.DecimalSetterChamber.markerWord, nearyMarker] using
        MatrixMortality.DecimalSetterChamber.markerWord_code_identity β
    dsimp only [M, ρ]
    exact_mod_cast natural_relation
  have marker_scaled_dvd : (5 : ℤ) ∣ 9 * (M - 2) := by
    have right_dvd : (5 : ℤ) ∣ 52 * ρ - 25 :=
      dvd_sub (rho_dvd.mul_left 52) (by norm_num)
    rw [show 9 * (M - 2) = 52 * ρ - 25 by linear_combination marker_relation]
    exact right_dvd
  have marker_dvd : (5 : ℤ) ∣ M - 2 :=
    (by norm_num : IsCoprime (5 : ℤ) 9).dvd_of_dvd_mul_left marker_scaled_dvd
  have marker_mod : M ≡ 2 [ZMOD 5] :=
    (Int.modEq_iff_dvd.mpr marker_dvd).symm
  let coefficient : ℤ := 2 * traceUnit * targetUnit - 7 * E * M * G
  have coefficient_mod : coefficient ≡ 2 [ZMOD 5] := by
    calc
      coefficient = 2 * traceUnit * targetUnit - 7 * E * M * G := rfl
      _ ≡ 2 * 1 * 3 - 7 * 2 * 2 * 3 [ZMOD 5] :=
        (((Int.ModEq.refl 2).mul trace_mod).mul target_mod).sub
          ((((Int.ModEq.refl 7).mul gap_mod).mul marker_mod).mul lift_mod)
      _ ≡ 2 [ZMOD 5] := by norm_num
  have coefficient_unit : ¬(5 : ℤ) ∣ coefficient := by
    intro coefficient_dvd
    rw [Int.modEq_iff_dvd] at coefficient_mod
    have two_dvd : (5 : ℤ) ∣ 2 := by
      simpa using dvd_add coefficient_mod coefficient_dvd
    norm_num at two_dvd
  have gap_cast : gap ((10 : ℚ) ^ β) = (E : ℚ) := by
    norm_num [E, ρ, gap, decimalGap]
  have lift_cast : lift ((10 : ℚ) ^ β) = (G : ℚ) := by
    norm_num [G, ρ, lift, decimalLift]
  have marker_cast : DecimalSetterMatrix.marker β = (M : ℚ) := by
    norm_num [M, DecimalSetterMatrix.marker]
  have scale_eq : upperScale β current = (10 : ℚ) ^ (β + 1) := by
    simp only [upperScale, current_upper_eq]
  have factorization :
      boundaryTrace β body current * singletonTrace β targetLetter -
          7 * gap ((10 : ℚ) ^ β) * DecimalSetterMatrix.marker β *
            lift ((10 : ℚ) ^ β) * upperScale β current =
        (10 : ℚ) ^ (β + 1) * (coefficient : ℚ) := by
    rw [trace_eq, target_eq, gap_cast, marker_cast, lift_cast, scale_eq]
    dsimp only [coefficient, ρ]
    push_cast
    rw [pow_succ]
    ring
  rw [factorization]
  have scale_value : HasValue 5 ((10 : ℚ) ^ (β + 1)) (β + 1) := by
    simpa using (ten_hasDecimalShell.pow (β + 1)).2
  have coefficient_value : HasValue 5 (coefficient : ℚ) 0 :=
    intCast_isUnit_of_not_dvd coefficient_unit
  simpa using mul_hasValue scale_value coefficient_value

/-- At upper length `β+2`, a `D_c` target leaves exactly one additional factor of two after
the common `2^(β+2)` scale. The normalized coefficient is `2 mod 4`. -/
theorem singletonC_coefficient_currentUpper_eq_beta_add_two_hasValue_two
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    {current : List NearyTile} (current_large : 3 ≤ current.length)
    (current_ends : EndsInErase current)
    (current_upper_eq : (spell (nearyUpper β) current).length = β + 2) :
    HasValue 2
      (boundaryTrace β body current * singletonTrace β .c -
        7 * gap ((10 : ℚ) ^ β) * DecimalSetterMatrix.marker β *
          lift ((10 : ℚ) ^ β) * upperScale β current)
      (β + 3) := by
  have β_pos : 0 < β := by omega
  let ρ : ℤ := 10 ^ β
  let E : ℤ := decimalGap ρ
  let G : ℤ := decimalLift ρ
  let M : ℤ := code (nearyMarker β)
  obtain ⟨traceUnit, trace_eq, trace_mod⟩ :=
    threeRoleErasureEnded_boundaryTrace_tenFactor_mod_four
      β_large body current_large current_ends
  have rho_dvd : (4 : ℤ) ∣ ρ := by
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ β by omega)
    refine ⟨25 * 10 ^ offset, ?_⟩
    simp only [ρ, pow_add]
    ring
  have gap_mod : E ≡ 1 [ZMOD 4] := by
    calc
      E = 18 * ρ - 63 := by simp [E, decimalGap]; ring
      _ ≡ 18 * 0 - 63 [ZMOD 4] :=
        ((Int.ModEq.refl 18).mul (Int.modEq_zero_iff_dvd.mpr rho_dvd)).sub
          (Int.ModEq.refl 63)
      _ ≡ 1 [ZMOD 4] := by norm_num
  have lift_mod : G ≡ 1 [ZMOD 4] := by
    calc
      G = 502 * ρ - 7 := by simp [G, decimalLift]
      _ ≡ 502 * 0 - 7 [ZMOD 4] :=
        ((Int.ModEq.refl 502).mul (Int.modEq_zero_iff_dvd.mpr rho_dvd)).sub
          (Int.ModEq.refl 7)
      _ ≡ 1 [ZMOD 4] := by norm_num
  have marker_relation : 9 * M + 7 = 52 * ρ := by
    have natural_relation :
        9 * code (nearyMarker β) + 7 = 52 * 10 ^ β := by
      simpa only [MatrixMortality.DecimalSetterChamber.markerWord, nearyMarker] using
        MatrixMortality.DecimalSetterChamber.markerWord_code_identity β
    dsimp only [M, ρ]
    exact_mod_cast natural_relation
  have marker_scaled_dvd : (4 : ℤ) ∣ 9 * (M - 1) := by
    have right_dvd : (4 : ℤ) ∣ 52 * ρ - 16 :=
      dvd_sub (rho_dvd.mul_left 52) (by norm_num)
    rw [show 9 * (M - 1) = 52 * ρ - 16 by linear_combination marker_relation]
    exact right_dvd
  have marker_dvd : (4 : ℤ) ∣ M - 1 :=
    (by norm_num : IsCoprime (4 : ℤ) 9).dvd_of_dvd_mul_left marker_scaled_dvd
  have marker_mod : M ≡ 1 [ZMOD 4] :=
    (Int.modEq_iff_dvd.mpr marker_dvd).symm
  let coefficient : ℤ :=
    5 ^ (β + 1) * (traceUnit * G - 35 * E * M * G)
  have five_power_mod : (5 : ℤ) ^ (β + 1) ≡ 1 [ZMOD 4] := by
    simpa using (show (5 : ℤ) ≡ 1 [ZMOD 4] by norm_num).pow (β + 1)
  have inner_mod : traceUnit * G - 35 * E * M * G ≡ 2 [ZMOD 4] := by
    calc
      traceUnit * G - 35 * E * M * G ≡ 1 * 1 - 35 * 1 * 1 * 1 [ZMOD 4] :=
        (trace_mod.mul lift_mod).sub
          ((((Int.ModEq.refl 35).mul gap_mod).mul marker_mod).mul lift_mod)
      _ ≡ 2 [ZMOD 4] := by norm_num
  have coefficient_mod : coefficient ≡ 2 [ZMOD 4] := by
    dsimp only [coefficient]
    exact (five_power_mod.mul inner_mod).trans (by norm_num)
  rw [Int.modEq_iff_dvd] at coefficient_mod
  obtain ⟨carry, carry_eq⟩ := coefficient_mod
  let unit : ℤ := 1 - 2 * carry
  have coefficient_eq : coefficient = 2 * unit := by
    dsimp only [unit]
    omega
  have unit_odd : ¬(2 : ℤ) ∣ unit := by
    rintro ⟨quotient, quotient_eq⟩
    dsimp only [unit] at quotient_eq
    omega
  have gap_cast : gap ((10 : ℚ) ^ β) = (E : ℚ) := by
    norm_num [E, ρ, gap, decimalGap]
  have lift_cast : lift ((10 : ℚ) ^ β) = (G : ℚ) := by
    norm_num [G, ρ, lift, decimalLift]
  have marker_cast : DecimalSetterMatrix.marker β = (M : ℚ) := by
    norm_num [M, DecimalSetterMatrix.marker]
  have scale_eq : upperScale β current = (10 : ℚ) ^ (β + 2) := by
    simp only [upperScale, current_upper_eq]
  have ten_pow_eq :
      (10 : ℚ) ^ β = (2 : ℚ) ^ β * (5 : ℚ) ^ β := by
    rw [show (10 : ℚ) = 2 * 5 by norm_num, mul_pow]
  have current_scale_eq :
      (10 : ℚ) ^ (β + 2) = (2 : ℚ) ^ (β + 2) * (5 : ℚ) ^ (β + 2) := by
    rw [show (10 : ℚ) = 2 * 5 by norm_num, mul_pow]
  have factorization :
      boundaryTrace β body current * singletonTrace β .c -
          7 * gap ((10 : ℚ) ^ β) * DecimalSetterMatrix.marker β *
            lift ((10 : ℚ) ^ β) * upperScale β current =
        (2 : ℚ) ^ (β + 2) * (coefficient : ℚ) := by
    rw [trace_eq, singletonCTrace_eq, gap_cast, marker_cast, lift_cast, scale_eq,
      ten_pow_eq, current_scale_eq]
    dsimp only [coefficient]
    push_cast
    rw [pow_add, pow_succ]
    norm_num
    ring
  rw [factorization]
  have scale_value : HasValue 2 ((2 : ℚ) ^ (β + 2)) (β + 2) :=
    primePower_hasValue (β + 2)
  have coefficient_value : HasValue 2 (coefficient : ℚ) 1 := by
    rw [coefficient_eq, Int.cast_mul]
    simpa using mul_hasValue (primePower_hasValue (prime := 2) 1)
      (intCast_isUnit_of_not_dvd unit_odd)
  have product := mul_hasValue scale_value coefficient_value
  convert product using 1
  omega

/-- At upper length `β+2`, a `D_b` target cancels through at least two normalized two-adic
digits. Thus the singleton coefficient contains the common factor `2^(β+4)`; the remaining
quotient is the sole short-current valuation seam. -/
theorem singletonB_coefficient_currentUpper_eq_beta_add_two_factor
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    {current : List NearyTile} (current_large : 3 ≤ current.length)
    (current_ends : EndsInErase current)
    (current_upper_eq : (spell (nearyUpper β) current).length = β + 2) :
    ∃ coefficient : ℤ,
      boundaryTrace β body current * singletonTrace β .b -
          7 * gap ((10 : ℚ) ^ β) * DecimalSetterMatrix.marker β *
            lift ((10 : ℚ) ^ β) * upperScale β current =
        (2 : ℚ) ^ (β + 4) * (coefficient : ℚ) := by
  let ρ : ℤ := 10 ^ β
  let E : ℤ := decimalGap ρ
  let G : ℤ := decimalLift ρ
  let M : ℤ := code (nearyMarker β)
  let H : ℤ := 5200 * ρ ^ 2 - 18398 * ρ + 2443
  obtain ⟨traceUnit, trace_eq, trace_mod⟩ :=
    threeRoleErasureEnded_boundaryTrace_tenFactor_mod_four
      β_large body current_large current_ends
  have rho_dvd : (4 : ℤ) ∣ ρ := by
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ β by omega)
    refine ⟨25 * 10 ^ offset, ?_⟩
    simp only [ρ, pow_add]
    ring
  have gap_mod : E ≡ 1 [ZMOD 4] := by
    calc
      E = 18 * ρ - 63 := by simp [E, decimalGap]; ring
      _ ≡ 18 * 0 - 63 [ZMOD 4] :=
        ((Int.ModEq.refl 18).mul (Int.modEq_zero_iff_dvd.mpr rho_dvd)).sub
          (Int.ModEq.refl 63)
      _ ≡ 1 [ZMOD 4] := by norm_num
  have lift_mod : G ≡ 1 [ZMOD 4] := by
    calc
      G = 502 * ρ - 7 := by simp [G, decimalLift]
      _ ≡ 502 * 0 - 7 [ZMOD 4] :=
        ((Int.ModEq.refl 502).mul (Int.modEq_zero_iff_dvd.mpr rho_dvd)).sub
          (Int.ModEq.refl 7)
      _ ≡ 1 [ZMOD 4] := by norm_num
  have target_mod : H ≡ 3 [ZMOD 4] := by
    calc
      H = 5200 * ρ ^ 2 - 18398 * ρ + 2443 := rfl
      _ ≡ 5200 * 0 ^ 2 - 18398 * 0 + 2443 [ZMOD 4] :=
        (((Int.ModEq.refl 5200).mul
          ((Int.modEq_zero_iff_dvd.mpr rho_dvd).pow 2)).sub
            ((Int.ModEq.refl 18398).mul (Int.modEq_zero_iff_dvd.mpr rho_dvd))).add
              (Int.ModEq.refl 2443)
      _ ≡ 3 [ZMOD 4] := by norm_num
  have marker_relation : 9 * M + 7 = 52 * ρ := by
    have natural_relation :
        9 * code (nearyMarker β) + 7 = 52 * 10 ^ β := by
      simpa only [MatrixMortality.DecimalSetterChamber.markerWord, nearyMarker] using
        MatrixMortality.DecimalSetterChamber.markerWord_code_identity β
    dsimp only [M, ρ]
    exact_mod_cast natural_relation
  have marker_scaled_dvd : (4 : ℤ) ∣ 9 * (M - 1) := by
    have right_dvd : (4 : ℤ) ∣ 52 * ρ - 16 :=
      dvd_sub (rho_dvd.mul_left 52) (by norm_num)
    rw [show 9 * (M - 1) = 52 * ρ - 16 by linear_combination marker_relation]
    exact right_dvd
  have marker_dvd : (4 : ℤ) ∣ M - 1 :=
    (by norm_num : IsCoprime (4 : ℤ) 9).dvd_of_dvd_mul_left marker_scaled_dvd
  have marker_mod : M ≡ 1 [ZMOD 4] :=
    (Int.modEq_iff_dvd.mpr marker_dvd).symm
  let normalized : ℤ :=
    5 ^ (β + 1) * (traceUnit * H - 35 * E * M * G)
  have five_power_mod : (5 : ℤ) ^ (β + 1) ≡ 1 [ZMOD 4] := by
    simpa using (show (5 : ℤ) ≡ 1 [ZMOD 4] by norm_num).pow (β + 1)
  have inner_mod : traceUnit * H - 35 * E * M * G ≡ 0 [ZMOD 4] := by
    calc
      traceUnit * H - 35 * E * M * G ≡ 1 * 3 - 35 * 1 * 1 * 1 [ZMOD 4] :=
        (trace_mod.mul target_mod).sub
          ((((Int.ModEq.refl 35).mul gap_mod).mul marker_mod).mul lift_mod)
      _ ≡ 0 [ZMOD 4] := by norm_num
  have normalized_dvd : (4 : ℤ) ∣ normalized := by
    rw [← Int.modEq_zero_iff_dvd]
    dsimp only [normalized]
    exact (five_power_mod.mul inner_mod).trans (by norm_num)
  obtain ⟨coefficient, normalized_eq⟩ := normalized_dvd
  refine ⟨coefficient, ?_⟩
  have gap_cast : gap ((10 : ℚ) ^ β) = (E : ℚ) := by
    norm_num [E, ρ, gap, decimalGap]
  have lift_cast : lift ((10 : ℚ) ^ β) = (G : ℚ) := by
    norm_num [G, ρ, lift, decimalLift]
  have marker_cast : DecimalSetterMatrix.marker β = (M : ℚ) := by
    norm_num [M, DecimalSetterMatrix.marker]
  have scale_eq : upperScale β current = (10 : ℚ) ^ (β + 2) := by
    simp only [upperScale, current_upper_eq]
  have ten_pow_eq :
      (10 : ℚ) ^ β = (2 : ℚ) ^ β * (5 : ℚ) ^ β := by
    rw [show (10 : ℚ) = 2 * 5 by norm_num, mul_pow]
  have current_scale_eq :
      (10 : ℚ) ^ (β + 2) = (2 : ℚ) ^ (β + 2) * (5 : ℚ) ^ (β + 2) := by
    rw [show (10 : ℚ) = 2 * 5 by norm_num, mul_pow]
  have base_factorization :
      boundaryTrace β body current * singletonTrace β .b -
          7 * gap ((10 : ℚ) ^ β) * DecimalSetterMatrix.marker β *
            lift ((10 : ℚ) ^ β) * upperScale β current =
        (2 : ℚ) ^ (β + 2) * (normalized : ℚ) := by
    rw [trace_eq, singletonBTrace_eq, gap_cast, marker_cast, lift_cast, scale_eq,
      ten_pow_eq, current_scale_eq]
    dsimp only [H, ρ, normalized]
    push_cast
    rw [ten_pow_eq]
    rw [pow_add, pow_succ]
    norm_num
    ring
  have normalized_eq_rat : (normalized : ℚ) = 4 * coefficient := by
    exact_mod_cast normalized_eq
  rw [base_factorization, normalized_eq_rat]
  rw [show β + 4 = (β + 2) + 2 by omega, pow_add]
  rw [pow_add]
  rw [pow_add]
  norm_num
  ring

/-- At upper length `β+1`, the intervening discrepancy has shell `(k,k-1)`. A normalized
residue computation excludes the apparent five-adic coefficient cancellation. -/
theorem singletonPole_threeBlock_ruleCRoot_currentUpper_eq_beta_add_one_discrepancyShell
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (current_upper_eq : (spell (nearyUpper β) current).length = β + 1)
    (pole : HitsSquarePole β body [.erase targetLetter]
      [current, next, DecimalSetterMinimumBody.ruleCRoot]) :
    HasDecimalShell (upperBoundaryCode β next - lowerBoundaryCode β body next)
      (spell (nearyUpper β) next).length
      (((spell (nearyUpper β) next).length : ℤ) - 1) := by
  have β_pos : 0 < β := by omega
  let k := (spell (nearyUpper β) next).length
  let δ := upperBoundaryCode β next - lowerBoundaryCode β body next
  let E := gap ((10 : ℚ) ^ β)
  let G := lift ((10 : ℚ) ^ β)
  let μ := DecimalSetterMatrix.marker β
  let T := boundaryTrace β body current
  let V := lowerBoundaryCode β body current
  let A := upperScale β current
  let B := upperScale β next
  let S := singletonTrace β targetLetter
  let K := T * S - 7 * E * μ * G * A
  have trace_shell : HasDecimalShell T 1 1 := by
    simpa only [T, boundaryTrace] using
      MatrixMortality.DecimalSetterShallow.multiRoleErasureEnded_boundaryTrace_hasDecimalShell
        (show 2 ≤ β by omega) body current_multi current_ends
  have target_shell : HasDecimalShell S (β + 1) β := by
    simpa only [S] using singletonTrace_hasDecimalShell β_pos targetLetter
  have trace_product_two : HasValue 2 (T * S) (β + 2) := by
    convert mul_hasValue trace_shell.1 target_shell.1 using 1
    omega
  have seven_unit : HasDecimalShell (7 : ℚ) 0 0 :=
    intCast_hasDecimalShell_of_mod_seven (Int.ModEq.refl 7)
  have scale_shell : HasDecimalShell A (β + 1) (β + 1) := by
    have scale_eq : A = (10 : ℚ) ^ (β + 1) := by
      simp only [A, upperScale, current_upper_eq]
    rw [scale_eq]
    simpa using ten_hasDecimalShell.pow (β + 1)
  have correction_shell : HasDecimalShell (7 * E * μ * G * A) (β + 1) (β + 1) := by
    convert ((((seven_unit.mul (gap_tenPow_hasDecimalShell β_pos)).mul
      (marker_hasDecimalShell β_pos)).mul (lift_tenPow_hasDecimalShell β_pos)).mul
        scale_shell) using 1 <;> simp
  have correction_two : HasValue 2 (7 * E * μ * G * A) (β + 1) :=
    correction_shell.1
  have coefficient_two : HasValue 2 K (β + 1) := by
    have shell := sub_hasValue_min trace_product_two.1 correction_two.1 (by
      rw [trace_product_two.2, correction_two.2]
      omega)
    rw [trace_product_two.2, correction_two.2,
      min_eq_right (show (β + 1 : ℤ) ≤ β + 2 by omega)] at shell
    simpa only [K] using shell
  have coefficient_five : HasValue 5 K (β + 1) := by
    simpa only [K, T, S, E, μ, G, A] using
      singletonCoefficient_currentUpper_eq_beta_add_one_hasValue_five
        β_large body targetLetter current_multi current_ends current_upper_eq
  have lower_unit : HasDecimalShell V 0 0 := by
    simpa only [V] using
      lowerBoundaryCode_hasDecimalShell_of_endsInErase β body current_ends
  have next_scale_shell : HasDecimalShell B k k := by
    have shell := ten_hasDecimalShell.pow k
    norm_num at shell
    simpa only [B, upperScale, k] using shell
  have right_shell : HasDecimalShell (G * V * B * μ * S)
      (k + β + 1) (k + β) := by
    convert (((((lift_tenPow_hasDecimalShell β_pos).mul lower_unit).mul
      next_scale_shell).mul (marker_hasDecimalShell β_pos)).mul target_shell) using 1 <;>
        omega
  have right_two : HasValue 2 (G * V * B * μ * S) (k + β + 1) :=
    right_shell.1
  have right_five : HasValue 5 (G * V * B * μ * S) (k + β) :=
    right_shell.2
  have exact_equation :=
    (hitsSquarePole_singleton_pair_ruleCRoot_iff_discrepancyEquation
      β_pos body targetLetter current next).mp pole
  change δ * K = G * V * B * μ * S at exact_equation
  have δ_eq : δ = (G * V * B * μ * S) / K := by
    apply (eq_div_iff coefficient_two.1).2
    exact exact_equation
  change HasDecimalShell δ k ((k : ℤ) - 1)
  rw [δ_eq]
  constructor
  · have quotient := div_hasValue right_two coefficient_two
    convert quotient using 1
    omega
  · have quotient := div_hasValue right_five coefficient_five
    convert quotient using 1
    omega

/-- At upper length `β+2`, the five-adic valuation of the intervening discrepancy is one below
its upper length. The two-adic coefficient is the second boundary cancellation seam. -/
theorem singletonPole_threeBlock_ruleCRoot_currentUpper_eq_beta_add_two_discrepancyFive
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (current_upper_eq : (spell (nearyUpper β) current).length = β + 2)
    (pole : HitsSquarePole β body [.erase targetLetter]
      [current, next, DecimalSetterMinimumBody.ruleCRoot]) :
    HasValue 5 (upperBoundaryCode β next - lowerBoundaryCode β body next)
      (((spell (nearyUpper β) next).length : ℤ) - 1) := by
  have β_pos : 0 < β := by omega
  let k := (spell (nearyUpper β) next).length
  let δ := upperBoundaryCode β next - lowerBoundaryCode β body next
  let E := gap ((10 : ℚ) ^ β)
  let G := lift ((10 : ℚ) ^ β)
  let μ := DecimalSetterMatrix.marker β
  let T := boundaryTrace β body current
  let V := lowerBoundaryCode β body current
  let A := upperScale β current
  let B := upperScale β next
  let S := singletonTrace β targetLetter
  let K := T * S - 7 * E * μ * G * A
  have trace_shell : HasDecimalShell T 1 1 := by
    simpa only [T, boundaryTrace] using
      MatrixMortality.DecimalSetterShallow.multiRoleErasureEnded_boundaryTrace_hasDecimalShell
        (show 2 ≤ β by omega) body current_multi current_ends
  have target_shell : HasDecimalShell S (β + 1) β := by
    simpa only [S] using singletonTrace_hasDecimalShell β_pos targetLetter
  have trace_product_five : HasValue 5 (T * S) (β + 1) := by
    convert mul_hasValue trace_shell.2 target_shell.2 using 1
    omega
  have seven_unit : HasDecimalShell (7 : ℚ) 0 0 :=
    intCast_hasDecimalShell_of_mod_seven (Int.ModEq.refl 7)
  have scale_shell : HasDecimalShell A (β + 2) (β + 2) := by
    have scale_eq : A = (10 : ℚ) ^ (β + 2) := by
      simp only [A, upperScale, current_upper_eq]
    rw [scale_eq]
    simpa using ten_hasDecimalShell.pow (β + 2)
  have correction_shell : HasDecimalShell (7 * E * μ * G * A) (β + 2) (β + 2) := by
    convert ((((seven_unit.mul (gap_tenPow_hasDecimalShell β_pos)).mul
      (marker_hasDecimalShell β_pos)).mul (lift_tenPow_hasDecimalShell β_pos)).mul
        scale_shell) using 1 <;> simp
  have correction_five : HasValue 5 (7 * E * μ * G * A) (β + 2) :=
    correction_shell.2
  have coefficient_five : HasValue 5 K (β + 1) := by
    have shell := sub_hasValue_min trace_product_five.1 correction_five.1 (by
      rw [trace_product_five.2, correction_five.2]
      omega)
    rw [trace_product_five.2, correction_five.2,
      min_eq_left (show (β + 1 : ℤ) ≤ β + 2 by omega)] at shell
    simpa only [K] using shell
  have lower_unit : HasDecimalShell V 0 0 := by
    simpa only [V] using
      lowerBoundaryCode_hasDecimalShell_of_endsInErase β body current_ends
  have next_scale_shell : HasDecimalShell B k k := by
    have shell := ten_hasDecimalShell.pow k
    norm_num at shell
    simpa only [B, upperScale, k] using shell
  have right_shell : HasDecimalShell (G * V * B * μ * S)
      (k + β + 1) (k + β) := by
    convert (((((lift_tenPow_hasDecimalShell β_pos).mul lower_unit).mul
      next_scale_shell).mul (marker_hasDecimalShell β_pos)).mul target_shell) using 1 <;>
        omega
  have right_five : HasValue 5 (G * V * B * μ * S) (k + β) :=
    right_shell.2
  have exact_equation :=
    (hitsSquarePole_singleton_pair_ruleCRoot_iff_discrepancyEquation
      β_pos body targetLetter current next).mp pole
  change δ * K = G * V * B * μ * S at exact_equation
  have δ_eq : δ = (G * V * B * μ * S) / K := by
    apply (eq_div_iff coefficient_five.1).2
    exact exact_equation
  change HasValue 5 δ ((k : ℤ) - 1)
  rw [δ_eq]
  have quotient := div_hasValue right_five coefficient_five
  convert quotient using 1
  omega

/-- At upper length `β+2`, a `D_c` target resolves the remaining two-adic cancellation. The
intervening discrepancy has the reversed boundary shell `(k-2,k-1)`. -/
theorem singletonPole_threeBlock_ruleCRoot_currentUpper_eq_beta_add_two_targetC_discrepancyShell
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    {current next : List NearyTile} (current_large : 3 ≤ current.length)
    (current_ends : EndsInErase current)
    (current_upper_eq : (spell (nearyUpper β) current).length = β + 2)
    (pole : HitsSquarePole β body [.erase .c]
      [current, next, DecimalSetterMinimumBody.ruleCRoot]) :
    HasDecimalShell (upperBoundaryCode β next - lowerBoundaryCode β body next)
      (((spell (nearyUpper β) next).length : ℤ) - 2)
      (((spell (nearyUpper β) next).length : ℤ) - 1) := by
  have β_pos : 0 < β := by omega
  let k := (spell (nearyUpper β) next).length
  let δ := upperBoundaryCode β next - lowerBoundaryCode β body next
  let E := gap ((10 : ℚ) ^ β)
  let G := lift ((10 : ℚ) ^ β)
  let μ := DecimalSetterMatrix.marker β
  let T := boundaryTrace β body current
  let V := lowerBoundaryCode β body current
  let A := upperScale β current
  let B := upperScale β next
  let S := singletonTrace β .c
  let K := T * S - 7 * E * μ * G * A
  have coefficient_two : HasValue 2 K (β + 3) := by
    simpa only [K, T, S, E, μ, G, A] using
      singletonC_coefficient_currentUpper_eq_beta_add_two_hasValue_two
        β_large body current_large current_ends current_upper_eq
  have coefficient_five : HasValue 5 K (β + 1) := by
    have current_multi : 2 ≤ current.length := by omega
    have trace_shell : HasDecimalShell T 1 1 := by
      simpa only [T, boundaryTrace] using
        MatrixMortality.DecimalSetterShallow.multiRoleErasureEnded_boundaryTrace_hasDecimalShell
          (show 2 ≤ β by omega) body current_multi current_ends
    have target_shell : HasDecimalShell S (β + 1) β := by
      simpa only [S] using singletonTrace_hasDecimalShell β_pos .c
    have trace_product_five : HasValue 5 (T * S) (β + 1) := by
      convert mul_hasValue trace_shell.2 target_shell.2 using 1
      omega
    have seven_unit : HasDecimalShell (7 : ℚ) 0 0 :=
      intCast_hasDecimalShell_of_mod_seven (Int.ModEq.refl 7)
    have scale_shell : HasDecimalShell A (β + 2) (β + 2) := by
      have scale_eq : A = (10 : ℚ) ^ (β + 2) := by
        simp only [A, upperScale, current_upper_eq]
      rw [scale_eq]
      simpa using ten_hasDecimalShell.pow (β + 2)
    have correction_shell :
        HasDecimalShell (7 * E * μ * G * A) (β + 2) (β + 2) := by
      convert ((((seven_unit.mul (gap_tenPow_hasDecimalShell β_pos)).mul
        (marker_hasDecimalShell β_pos)).mul (lift_tenPow_hasDecimalShell β_pos)).mul
          scale_shell) using 1 <;> simp
    have shell := sub_hasValue_min trace_product_five.1 correction_shell.2.1 (by
      rw [trace_product_five.2, correction_shell.2.2]
      omega)
    rw [trace_product_five.2, correction_shell.2.2,
      min_eq_left (show (β + 1 : ℤ) ≤ β + 2 by omega)] at shell
    simpa only [K] using shell
  have lower_unit : HasDecimalShell V 0 0 := by
    simpa only [V] using
      lowerBoundaryCode_hasDecimalShell_of_endsInErase β body current_ends
  have next_scale_shell : HasDecimalShell B k k := by
    have shell := ten_hasDecimalShell.pow k
    norm_num at shell
    simpa only [B, upperScale, k] using shell
  have target_shell : HasDecimalShell S (β + 1) β := by
    simpa only [S] using singletonTrace_hasDecimalShell β_pos .c
  have right_shell : HasDecimalShell (G * V * B * μ * S)
      (k + β + 1) (k + β) := by
    convert (((((lift_tenPow_hasDecimalShell β_pos).mul lower_unit).mul
      next_scale_shell).mul (marker_hasDecimalShell β_pos)).mul target_shell) using 1 <;>
        omega
  have exact_equation :=
    (hitsSquarePole_singleton_pair_ruleCRoot_iff_discrepancyEquation
      β_pos body .c current next).mp pole
  change δ * K = G * V * B * μ * S at exact_equation
  have δ_eq : δ = (G * V * B * μ * S) / K := by
    apply (eq_div_iff coefficient_two.1).2
    exact exact_equation
  change HasDecimalShell δ ((k : ℤ) - 2) ((k : ℤ) - 1)
  rw [δ_eq]
  constructor
  · have quotient := div_hasValue right_shell.1 coefficient_two
    convert quotient using 1
    omega
  · have quotient := div_hasValue right_shell.2 coefficient_five
    convert quotient using 1
    omega

/-- An all-`c` role block has one upper digit per role, independently of its phase word. -/
theorem upperLength_eq_length_of_letters_allC
    (β : Nat) {roles : List NearyTile}
    (letters_all_c :
      roles.map NearyTile.letter = List.replicate roles.length .c) :
    (spell (nearyUpper β) roles).length = roles.length := by
  rw [spell_nearyUpper,
    DecimalSetterAncestry.tagEncode_length_eq_roleLength_add_markerCount,
    letters_all_c]
  simp [List.count_replicate]

/-- Exhaustive valuation grammar for the short all-`c` current chamber. Widths through `β+1`
fix both discrepancy valuations; width `β+2` leaves only the two-adic boundary cancellation. -/
theorem singletonPole_threeBlock_ruleCRoot_shortAllC_discrepancyGrammar
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (targetLetter : TagLetter) {current next : List NearyTile}
    (current_multi : 2 ≤ current.length) (current_ends : EndsInErase current)
    (current_width : current.length ≤ β + 2)
    (letters_all_c :
      current.map NearyTile.letter = List.replicate current.length .c)
    (pole : HitsSquarePole β body [.erase targetLetter]
      [current, next, DecimalSetterMinimumBody.ruleCRoot]) :
    (current.length ≤ β ∧
      HasDecimalShell
        (upperBoundaryCode β next - lowerBoundaryCode β body next)
        (((spell (nearyUpper β) next).length : ℤ) + β + 1 - current.length)
        (((spell (nearyUpper β) next).length : ℤ) + β - current.length)) ∨
      (current.length = β + 1 ∧
        HasDecimalShell (upperBoundaryCode β next - lowerBoundaryCode β body next)
          (spell (nearyUpper β) next).length
          (((spell (nearyUpper β) next).length : ℤ) - 1)) ∨
        (current.length = β + 2 ∧
          HasValue 5 (upperBoundaryCode β next - lowerBoundaryCode β body next)
            (((spell (nearyUpper β) next).length : ℤ) - 1)) := by
  have current_upper_eq :
      (spell (nearyUpper β) current).length = current.length :=
    upperLength_eq_length_of_letters_allC β letters_all_c
  by_cases below_boundary : current.length ≤ β
  · left
    refine ⟨below_boundary, ?_⟩
    have shell :=
      singletonPole_threeBlock_ruleCRoot_currentUpper_le_beta_discrepancyShell
        β_large body targetLetter current_multi current_ends
          (by simpa only [current_upper_eq] using below_boundary) pole
    simpa only [current_upper_eq] using shell
  · have boundary_cases : current.length = β + 1 ∨ current.length = β + 2 := by omega
    rcases boundary_cases with first_boundary | second_boundary
    · right
      left
      refine ⟨first_boundary, ?_⟩
      apply singletonPole_threeBlock_ruleCRoot_currentUpper_eq_beta_add_one_discrepancyShell
        β_large body targetLetter current_multi current_ends
      · omega
      · exact pole
    · right
      right
      refine ⟨second_boundary, ?_⟩
      apply singletonPole_threeBlock_ruleCRoot_currentUpper_eq_beta_add_two_discrepancyFive
        β_large body targetLetter current_multi current_ends
      · omega
      · exact pole

end MatrixMortality.DecimalSetterBridgeRay
