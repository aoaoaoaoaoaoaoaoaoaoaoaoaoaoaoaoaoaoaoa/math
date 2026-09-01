import MatrixMortality.DecimalSetterAncestry
import MatrixMortality.DecimalSetterThreeBlockShortCurrent

/-!
# Pure-erasure refinement of the short three-block seam

The all-erasure point of the surviving `D_b`, width-`β+2` coefficient seam has an exact
two-adic valuation.  Its trace unit retains one more binary residue than an arbitrary phase
word.
-/

namespace MatrixMortality.DecimalSetterBridgeRay

open MatrixMortality.DecimalSetterAncestry
open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterBridge
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterDepth
open MatrixMortality.DecimalSetterMatrix
open MatrixMortality.PadicValuation

private theorem tagEncode_replicate_c (β width : Nat) :
    tagEncode β (List.replicate width .c) = List.replicate width true := by
  induction width with
  | zero => rfl
  | succ width induction =>
      rw [List.replicate_succ, tagEncode_cons, tagCode, induction,
        List.replicate_succ]
      rfl

private theorem allEraseBlock_punctuatedUpper
    (β width : Nat) :
    spell (nearyUpper β) (allEraseBlock width) ++ nearyMarker β =
      punctuatedUpper β (List.replicate width .c) := by
  rw [spell_nearyUpper]
  simp only [allEraseBlock, List.map_replicate, NearyTile.letter,
    tagEncode_replicate_c, punctuatedUpper, nearyMarker,
    MatrixMortality.DecimalSetterChamber.markerWord]

private theorem allEraseBlock_upperLength
    (β width : Nat) :
    (spell (nearyUpper β) (allEraseBlock width)).length = width := by
  simp [allEraseBlock, nearyUpper, tagCode, spell]

private theorem allEraseBlock_endsInErase
    {width : Nat} (width_pos : 0 < width) :
    EndsInErase (allEraseBlock width) := by
  obtain ⟨frontWidth, rfl⟩ := Nat.exists_eq_succ_of_ne_zero width_pos.ne'
  refine ⟨List.replicate frontWidth (.erase .c), .c, ?_⟩
  simp only [allEraseBlock]
  change List.replicate (frontWidth + 1) (NearyTile.erase TagLetter.c) =
    List.replicate frontWidth (NearyTile.erase TagLetter.c) ++
      [NearyTile.erase TagLetter.c]
  rw [List.replicate_add]
  rfl

private theorem hasValue_intCast_nonnegative
    {prime : Nat} {value : ℤ} {depth : ℤ}
    (value_depth : HasValue prime (value : ℚ) depth) :
    0 ≤ depth := by
  have valuation := value_depth.2
  rw [padicValRat.of_int] at valuation
  rw [← valuation]
  exact Int.natCast_nonneg _

private theorem boundaryDiscrepancy_intCast
    (β : Nat) (body : List TagLetter) (roles : List NearyTile) :
    upperBoundaryCode β roles - lowerBoundaryCode β body roles =
      (((code (spell (nearyUpper β) roles ++ nearyMarker β) : ℤ) -
        (code (spell (nearyLower β body) roles) : ℤ) : ℤ) : ℚ) := by
  norm_num [upperBoundaryCode, lowerBoundaryCode]

private theorem allEraseBlock_traceUnit_polynomial
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter) :
    ∃ traceUnit : ℤ,
      boundaryTrace β body (allEraseBlock (β + 2)) =
          ((10 * traceUnit : ℤ) : ℚ) ∧
        45 * traceUnit =
          45000 * ((10 : ℤ) ^ β) ^ 3 +
            18218 * ((10 : ℤ) ^ β) ^ 2 -
              4333 * (10 : ℤ) ^ β + 245 := by
  let ρ : ℤ := 10 ^ β
  let E : ℤ := decimalGap ρ
  let G : ℤ := decimalLift ρ
  let P : ℤ := code
    (spell (nearyUpper β) (allEraseBlock (β + 2)) ++ nearyMarker β)
  let V : ℤ := code (spell (nearyLower β body) (allEraseBlock (β + 2)))
  let T : ℤ := E * P + G * V
  have upper_relation :
      9 * P = 5000 * ρ ^ 2 + 2 * ρ - 7 := by
    have relation := allC_punctuatedUpper_code_identity β (β + 2)
    rw [← allEraseBlock_punctuatedUpper] at relation
    dsimp only [P, ρ]
    rw [pow_add, pow_two] at relation
    norm_num at relation ⊢
    ring_nf at relation ⊢
    exact relation
  have lower_relation : 9 * V + 7 = 700 * ρ := by
    have relation := allEraseLowerCode_identity β body (β + 2)
    have lower_eq :
        V = allEraseLowerCode β body (β + 2) := by
      rfl
    rw [lower_eq]
    calc
      9 * allEraseLowerCode β body (β + 2) + 7 =
          7 * (10 : ℤ) ^ (β + 2) := relation
      _ = 700 * ρ := by
        dsimp only [ρ]
        rw [pow_add]
        norm_num
        ring
  have current_large : 3 ≤ (allEraseBlock (β + 2)).length := by
    simp [allEraseBlock]
    omega
  have current_ends : EndsInErase (allEraseBlock (β + 2)) := by
    refine ⟨List.replicate (β + 1) (.erase .c), .c, ?_⟩
    simp only [allEraseBlock]
    rw [show β + 2 = (β + 1) + 1 by omega, List.replicate_add]
    rfl
  obtain ⟨traceUnit, boundary_trace_eq, _⟩ :=
    threeRoleErasureEnded_boundaryTrace_tenFactor_mod_four
      β_large body current_large current_ends
  have trace_eq : T = 10 * traceUnit := by
    have boundary_eq : boundaryTrace β body (allEraseBlock (β + 2)) = (T : ℚ) := by
      norm_num [T, E, G, P, V, ρ, boundaryTrace, gap, lift, decimalGap, decimalLift,
        upperBoundaryCode, lowerBoundaryCode]
    rw [boundary_eq] at boundary_trace_eq
    exact_mod_cast boundary_trace_eq
  refine ⟨traceUnit, ?_, ?_⟩
  · exact boundary_trace_eq
  · have lower_nine : 9 * V = 700 * ρ - 7 := by
      calc
        9 * V = (9 * V + 7) - 7 := by ring
        _ = 700 * ρ - 7 := by rw [lower_relation]
    have scaled_trace :
        90 * traceUnit =
          (18 * ρ - 63) * (9 * P) +
            (502 * ρ - 7) * (9 * V) := by
      calc
        90 * traceUnit = 9 * (10 * traceUnit) := by ring
        _ = 9 * T := by rw [trace_eq]
        _ = (18 * ρ - 63) * (9 * P) +
            (502 * ρ - 7) * (9 * V) := by
          simp only [T, E, G, decimalGap, decimalLift]
          ring
    rw [upper_relation, lower_nine] at scaled_trace
    have polynomial_identity :
        (18 * ρ - 63) * (5000 * ρ ^ 2 + 2 * ρ - 7) +
            (502 * ρ - 7) * (700 * ρ - 7) =
          2 *
            (45000 * ρ ^ 3 + 18218 * ρ ^ 2 - 4333 * ρ + 245) := by
      ring
    rw [polynomial_identity] at scaled_trace
    have relation_rho :
        45 * traceUnit =
          45000 * ρ ^ 3 + 18218 * ρ ^ 2 - 4333 * ρ + 245 := by
      apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num)
      calc
        2 * (45 * traceUnit) = 90 * traceUnit := by ring
        _ = 2 *
            (45000 * ρ ^ 3 + 18218 * ρ ^ 2 - 4333 * ρ + 245) :=
          scaled_trace
    simpa only [ρ] using relation_rho

private theorem allEraseBlock_traceUnit_mod_sixteen
    {β : Nat} (β_large : 4 ≤ β) (body : List TagLetter) :
    ∃ traceUnit : ℤ,
      boundaryTrace β body (allEraseBlock (β + 2)) =
          ((10 * traceUnit : ℤ) : ℚ) ∧
        traceUnit ≡ 9 [ZMOD 16] := by
  obtain ⟨traceUnit, trace_eq, polynomial⟩ :=
    allEraseBlock_traceUnit_polynomial (show 3 ≤ β by omega) body
  let ρ : ℤ := 10 ^ β
  have rho_dvd : (16 : ℤ) ∣ ρ := by
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le β_large
    refine ⟨625 * 10 ^ offset, ?_⟩
    simp only [ρ, pow_add]
    ring
  obtain ⟨rhoUnit, rho_eq⟩ := rho_dvd
  have polynomial_rho :
      45 * traceUnit =
        45000 * ρ ^ 3 + 18218 * ρ ^ 2 - 4333 * ρ + 245 := by
    simpa only [ρ] using polynomial
  have scaled_dvd : (16 : ℤ) ∣ 45 * (traceUnit - 9) := by
    rw [show
      45 * (traceUnit - 9) =
        (45000 * ρ ^ 3 + 18218 * ρ ^ 2 - 4333 * ρ + 245) - 405 by
      linear_combination polynomial_rho]
    refine ⟨45000 * 256 * rhoUnit ^ 3 + 18218 * 16 * rhoUnit ^ 2 -
      4333 * rhoUnit - 10, ?_⟩
    rw [rho_eq]
    ring
  have unit_dvd : (16 : ℤ) ∣ traceUnit - 9 :=
    (by norm_num : IsCoprime (16 : ℤ) 45).dvd_of_dvd_mul_left scaled_dvd
  refine ⟨traceUnit, trace_eq, ?_⟩
  exact (Int.modEq_iff_dvd.mpr unit_dvd).symm

/-- For `β≥4`, the pure all-erasure point of the `D_b`, width-`β+2` coefficient seam has
exact two-adic depth `β+5`. -/
theorem singletonB_coefficient_allEraseBlock_beta_add_two_hasValue_two
    {β : Nat} (β_large : 4 ≤ β) (body : List TagLetter) :
    HasValue 2
      (boundaryTrace β body (allEraseBlock (β + 2)) * singletonTrace β .b -
        7 * gap ((10 : ℚ) ^ β) * DecimalSetterMatrix.marker β *
          lift ((10 : ℚ) ^ β) * upperScale β (allEraseBlock (β + 2)))
      (β + 5) := by
  let ρ : ℤ := 10 ^ β
  let E : ℤ := decimalGap ρ
  let G : ℤ := decimalLift ρ
  let M : ℤ := code (nearyMarker β)
  let H : ℤ := 5200 * ρ ^ 2 - 18398 * ρ + 2443
  obtain ⟨traceUnit, trace_eq, trace_mod⟩ :=
    allEraseBlock_traceUnit_mod_sixteen β_large body
  have rho_dvd : (16 : ℤ) ∣ ρ := by
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le β_large
    refine ⟨625 * 10 ^ offset, ?_⟩
    simp only [ρ, pow_add]
    ring
  have rho_mod : ρ ≡ 0 [ZMOD 16] :=
    Int.modEq_zero_iff_dvd.mpr rho_dvd
  have gap_mod : E ≡ 1 [ZMOD 16] := by
    calc
      E = 18 * ρ - 63 := by simp [E, decimalGap]; ring
      _ ≡ 18 * 0 - 63 [ZMOD 16] :=
        ((Int.ModEq.refl 18).mul rho_mod).sub (Int.ModEq.refl 63)
      _ ≡ 1 [ZMOD 16] := by norm_num
  have lift_mod : G ≡ 9 [ZMOD 16] := by
    calc
      G = 502 * ρ - 7 := by simp [G, decimalLift]
      _ ≡ 502 * 0 - 7 [ZMOD 16] :=
        ((Int.ModEq.refl 502).mul rho_mod).sub (Int.ModEq.refl 7)
      _ ≡ 9 [ZMOD 16] := by norm_num
  have target_mod : H ≡ 11 [ZMOD 16] := by
    calc
      H = 5200 * ρ ^ 2 - 18398 * ρ + 2443 := rfl
      _ ≡ 5200 * 0 ^ 2 - 18398 * 0 + 2443 [ZMOD 16] :=
        (((Int.ModEq.refl 5200).mul (rho_mod.pow 2)).sub
          ((Int.ModEq.refl 18398).mul rho_mod)).add (Int.ModEq.refl 2443)
      _ ≡ 11 [ZMOD 16] := by norm_num
  have marker_relation : 9 * M + 7 = 52 * ρ := by
    have natural_relation :
        9 * code (nearyMarker β) + 7 = 52 * 10 ^ β := by
      simpa only [MatrixMortality.DecimalSetterChamber.markerWord, nearyMarker] using
        MatrixMortality.DecimalSetterChamber.markerWord_code_identity β
    dsimp only [M, ρ]
    exact_mod_cast natural_relation
  have marker_scaled_dvd : (16 : ℤ) ∣ 9 * (M - 1) := by
    have right_dvd : (16 : ℤ) ∣ 52 * ρ - 16 :=
      dvd_sub (rho_dvd.mul_left 52) (by norm_num)
    rw [show 9 * (M - 1) = 52 * ρ - 16 by linear_combination marker_relation]
    exact right_dvd
  have marker_dvd : (16 : ℤ) ∣ M - 1 :=
    (by norm_num : IsCoprime (16 : ℤ) 9).dvd_of_dvd_mul_left marker_scaled_dvd
  have marker_mod : M ≡ 1 [ZMOD 16] :=
    (Int.modEq_iff_dvd.mpr marker_dvd).symm
  let inner : ℤ := traceUnit * H - 35 * E * M * G
  have inner_mod : inner ≡ 8 [ZMOD 16] := by
    dsimp only [inner]
    calc
      traceUnit * H - 35 * E * M * G ≡
          9 * 11 - 35 * 1 * 1 * 9 [ZMOD 16] :=
        (trace_mod.mul target_mod).sub
          ((((Int.ModEq.refl 35).mul gap_mod).mul marker_mod).mul lift_mod)
      _ ≡ 8 [ZMOD 16] := by norm_num
  rw [Int.modEq_iff_dvd] at inner_mod
  obtain ⟨carry, carry_eq⟩ := inner_mod
  let unit : ℤ := 1 - 2 * carry
  have inner_eq : inner = 8 * unit := by
    dsimp only [unit]
    omega
  have unit_odd : ¬(2 : ℤ) ∣ unit := by
    rintro ⟨quotient, quotient_eq⟩
    dsimp only [unit] at quotient_eq
    omega
  let coefficient : ℤ := 5 ^ (β + 1) * inner
  have gap_cast : gap ((10 : ℚ) ^ β) = (E : ℚ) := by
    norm_num [E, ρ, gap, decimalGap]
  have lift_cast : lift ((10 : ℚ) ^ β) = (G : ℚ) := by
    norm_num [G, ρ, lift, decimalLift]
  have marker_cast : DecimalSetterMatrix.marker β = (M : ℚ) := by
    norm_num [M, DecimalSetterMatrix.marker]
  have scale_eq :
      upperScale β (allEraseBlock (β + 2)) = (10 : ℚ) ^ (β + 2) := by
    simp only [upperScale, allEraseBlock_upperLength]
  have ten_pow_eq :
      (10 : ℚ) ^ β = (2 : ℚ) ^ β * (5 : ℚ) ^ β := by
    rw [show (10 : ℚ) = 2 * 5 by norm_num, mul_pow]
  have current_scale_eq :
      (10 : ℚ) ^ (β + 2) = (2 : ℚ) ^ (β + 2) * (5 : ℚ) ^ (β + 2) := by
    rw [show (10 : ℚ) = 2 * 5 by norm_num, mul_pow]
  have factorization :
      boundaryTrace β body (allEraseBlock (β + 2)) * singletonTrace β .b -
          7 * gap ((10 : ℚ) ^ β) * DecimalSetterMatrix.marker β *
            lift ((10 : ℚ) ^ β) * upperScale β (allEraseBlock (β + 2)) =
        (2 : ℚ) ^ (β + 2) * (coefficient : ℚ) := by
    rw [trace_eq, singletonBTrace_eq, gap_cast, marker_cast, lift_cast, scale_eq,
      ten_pow_eq, current_scale_eq]
    dsimp only [coefficient, inner, H, ρ]
    push_cast
    rw [ten_pow_eq]
    rw [pow_add, pow_succ]
    norm_num
    ring
  rw [factorization]
  have scale_value : HasValue 2 ((2 : ℚ) ^ (β + 2)) (β + 2) :=
    primePower_hasValue (β + 2)
  have five_odd : ¬(2 : ℤ) ∣ (5 : ℤ) ^ (β + 1) := by
    intro five_dvd
    have base_dvd : (2 : ℤ) ∣ 5 :=
      Int.Prime.dvd_pow' Nat.prime_two five_dvd
    norm_num at base_dvd
  have five_value : HasValue 2 (((5 : ℤ) ^ (β + 1) : ℤ) : ℚ) 0 :=
    intCast_isUnit_of_not_dvd five_odd
  have inner_value : HasValue 2 (inner : ℚ) 3 := by
    rw [inner_eq, Int.cast_mul]
    convert mul_hasValue (primePower_hasValue (prime := 2) 3)
      (intCast_isUnit_of_not_dvd unit_odd) using 1 <;> norm_num
  have coefficient_value : HasValue 2 (coefficient : ℚ) 3 := by
    dsimp only [coefficient]
    rw [Int.cast_mul]
    simpa using mul_hasValue five_value inner_value
  have product := mul_hasValue scale_value coefficient_value
  convert product using 1
  omega

/-- At the exceptional deletion width `β=3`, the same pure all-erasure coefficient has exact
two-adic depth ten, two digits deeper than the stable `β≥4` formula. -/
theorem singletonB_coefficient_allEraseBlock_beta_three_hasValue_two
    (body : List TagLetter) :
    HasValue 2
      (boundaryTrace 3 body (allEraseBlock 5) * singletonTrace 3 .b -
        7 * gap ((10 : ℚ) ^ 3) * DecimalSetterMatrix.marker 3 *
          lift ((10 : ℚ) ^ 3) * upperScale 3 (allEraseBlock 5))
      10 := by
  have coefficient_eq :
      boundaryTrace 3 body (allEraseBlock 5) * singletonTrace 3 .b -
          7 * gap ((10 : ℚ) ^ 3) * DecimalSetterMatrix.marker 3 *
            lift ((10 : ℚ) ^ 3) * upperScale 3 (allEraseBlock 5) =
        (2 : ℚ) ^ 10 * (101244138032330471705625 : ℤ) := by
    obtain ⟨traceUnit, trace_eq, polynomial⟩ :=
      allEraseBlock_traceUnit_polynomial (β := 3) (by norm_num) body
    have traceUnit_eq : traceUnit = 1000404748161 := by
      norm_num at polynomial
      omega
    rw [traceUnit_eq] at trace_eq
    have scale_eq : upperScale 3 (allEraseBlock 5) = (10 : ℚ) ^ 5 := by
      simp only [upperScale, allEraseBlock_upperLength]
    have marker_eq : DecimalSetterMatrix.marker 3 = 5777 := by
      have relation := DecimalSetterMatrix.marker_relation 3
      norm_num at relation ⊢
      linarith
    rw [trace_eq, singletonBTrace_eq, scale_eq, marker_eq]
    norm_num [gap, lift]
  rw [coefficient_eq]
  have unit_value :
      HasValue 2 ((101244138032330471705625 : ℤ) : ℚ) 0 :=
    intCast_isUnit_of_not_dvd (by norm_num)
  simpa using mul_hasValue (primePower_hasValue (prime := 2) 10) unit_value

private theorem singletonPole_threeBlock_ruleCRoot_allEraseBlock_discrepancyTwo_of_coefficient
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter) (next : List NearyTile)
    {coefficientDepth : ℤ}
    (coefficient_value :
      HasValue 2
        (boundaryTrace β body (allEraseBlock (β + 2)) * singletonTrace β .b -
          7 * gap ((10 : ℚ) ^ β) * DecimalSetterMatrix.marker β *
            lift ((10 : ℚ) ^ β) * upperScale β (allEraseBlock (β + 2)))
        coefficientDepth)
    (pole : HitsSquarePole β body [.erase .b]
      [allEraseBlock (β + 2), next, DecimalSetterMinimumBody.ruleCRoot]) :
    HasValue 2 (upperBoundaryCode β next - lowerBoundaryCode β body next)
      (((spell (nearyUpper β) next).length : ℤ) + β + 1 - coefficientDepth) := by
  let k := (spell (nearyUpper β) next).length
  let δ := upperBoundaryCode β next - lowerBoundaryCode β body next
  let G := lift ((10 : ℚ) ^ β)
  let V := lowerBoundaryCode β body (allEraseBlock (β + 2))
  let B := upperScale β next
  let μ := DecimalSetterMatrix.marker β
  let S := singletonTrace β .b
  let K := boundaryTrace β body (allEraseBlock (β + 2)) * S -
    7 * gap ((10 : ℚ) ^ β) * μ * G * upperScale β (allEraseBlock (β + 2))
  have lower_unit : HasValue 2 V 0 := by
    have lower_shell := lowerBoundaryCode_hasDecimalShell_of_endsInErase β body
      (allEraseBlock_endsInErase (show 0 < β + 2 by omega))
    simpa only [V] using lower_shell.1
  have next_scale_value : HasValue 2 B k := by
    have shell := (ten_hasDecimalShell.pow k).1
    norm_num at shell
    simpa only [B, upperScale, k] using shell
  have target_value : HasValue 2 S (β + 1) := by
    simpa only [S] using (singletonTrace_hasDecimalShell β_pos .b).1
  have right_value : HasValue 2 (G * V * B * μ * S) (k + β + 1) := by
    have product := mul_hasValue
      (mul_hasValue
        (mul_hasValue
          (mul_hasValue (lift_tenPow_hasDecimalShell β_pos).1 lower_unit)
          next_scale_value)
        (marker_hasDecimalShell β_pos).1)
      target_value
    convert product using 1
    omega
  have exact_equation :=
    (hitsSquarePole_singleton_pair_ruleCRoot_iff_discrepancyEquation
      β_pos body .b (allEraseBlock (β + 2)) next).mp pole
  change δ * K = G * V * B * μ * S at exact_equation
  have coefficient_value' : HasValue 2 K coefficientDepth := by
    simpa only [K, S, G, μ] using coefficient_value
  have δ_eq : δ = (G * V * B * μ * S) / K := by
    apply (eq_div_iff coefficient_value'.1).2
    exact exact_equation
  change HasValue 2 δ ((k : ℤ) + β + 1 - coefficientDepth)
  rw [δ_eq]
  exact div_hasValue right_value coefficient_value'

/-- For `β≥4`, a pure width-`β+2` all-erasure current before a `D_b` singleton forces the
intervening discrepancy into the reversed shell `(k-4,k-1)`. -/
theorem singletonPole_threeBlock_ruleCRoot_allEraseBlock_targetB_discrepancyShell
    {β : Nat} (β_large : 4 ≤ β) (body : List TagLetter) (next : List NearyTile)
    (pole : HitsSquarePole β body [.erase .b]
      [allEraseBlock (β + 2), next, DecimalSetterMinimumBody.ruleCRoot]) :
    HasDecimalShell (upperBoundaryCode β next - lowerBoundaryCode β body next)
      (((spell (nearyUpper β) next).length : ℤ) - 4)
      (((spell (nearyUpper β) next).length : ℤ) - 1) := by
  have coefficient_value :=
    singletonB_coefficient_allEraseBlock_beta_add_two_hasValue_two β_large body
  have two_value :=
    singletonPole_threeBlock_ruleCRoot_allEraseBlock_discrepancyTwo_of_coefficient
      (show 0 < β by omega) body next coefficient_value pole
  have current_multi : 2 ≤ (allEraseBlock (β + 2)).length := by
    simp [allEraseBlock]
  have current_ends : EndsInErase (allEraseBlock (β + 2)) :=
    allEraseBlock_endsInErase (by omega)
  have current_upper :
      (spell (nearyUpper β) (allEraseBlock (β + 2))).length = β + 2 :=
    allEraseBlock_upperLength β (β + 2)
  have five_value :=
    singletonPole_threeBlock_ruleCRoot_currentUpper_eq_beta_add_two_discrepancyFive
      (show 3 ≤ β by omega) body .b current_multi current_ends current_upper pole
  constructor
  · convert two_value using 1
    omega
  · exact five_value

/-- At `β=3`, the pure width-five all-erasure current before a `D_b` singleton forces the
exceptional reversed shell `(k-6,k-1)`. -/
theorem singletonPole_threeBlock_ruleCRoot_allEraseBlock_targetB_beta_three_discrepancyShell
    (body : List TagLetter) (next : List NearyTile)
    (pole : HitsSquarePole 3 body [.erase .b]
      [allEraseBlock 5, next, DecimalSetterMinimumBody.ruleCRoot]) :
    HasDecimalShell (upperBoundaryCode 3 next - lowerBoundaryCode 3 body next)
      (((spell (nearyUpper 3) next).length : ℤ) - 6)
      (((spell (nearyUpper 3) next).length : ℤ) - 1) := by
  have coefficient_value :=
    singletonB_coefficient_allEraseBlock_beta_three_hasValue_two body
  have two_value :=
    singletonPole_threeBlock_ruleCRoot_allEraseBlock_discrepancyTwo_of_coefficient
      (β := 3) (by norm_num) body next coefficient_value pole
  have current_multi : 2 ≤ (allEraseBlock 5).length := by
    simp [allEraseBlock]
  have current_ends : EndsInErase (allEraseBlock 5) :=
    allEraseBlock_endsInErase (by norm_num)
  have current_upper :
      (spell (nearyUpper 3) (allEraseBlock 5)).length = 3 + 2 := by
    simpa using allEraseBlock_upperLength 3 5
  have five_value :=
    singletonPole_threeBlock_ruleCRoot_currentUpper_eq_beta_add_two_discrepancyFive
      (β := 3) (by norm_num) body .b current_multi current_ends current_upper pole
  constructor
  · convert two_value using 1
    norm_num
    omega
  · exact five_value

/-- For `β≥4`, the pure width-`β+2` all-erasure current cannot precede a `D_b` singleton when
the intervening block has fewer than four upper digits. -/
theorem singletonPole_threeBlock_ruleCRoot_allEraseBlock_targetB_shortNext_impossible
    {β : Nat} (β_large : 4 ≤ β) (body : List TagLetter) (next : List NearyTile)
    (next_short : (spell (nearyUpper β) next).length < 4) :
    ¬HitsSquarePole β body [.erase .b]
      [allEraseBlock (β + 2), next, DecimalSetterMinimumBody.ruleCRoot] := by
  intro pole
  have shell :=
    singletonPole_threeBlock_ruleCRoot_allEraseBlock_targetB_discrepancyShell
      β_large body next pole
  rw [boundaryDiscrepancy_intCast] at shell
  have depth_nonnegative := hasValue_intCast_nonnegative shell.1
  omega

/-- At `β=3`, the exceptional pure width-five all-erasure current cannot precede a `D_b`
singleton when the intervening block has fewer than six upper digits. -/
theorem singletonPole_threeBlock_ruleCRoot_allEraseBlock_targetB_beta_three_shortNext_impossible
    (body : List TagLetter) (next : List NearyTile)
    (next_short : (spell (nearyUpper 3) next).length < 6) :
    ¬HitsSquarePole 3 body [.erase .b]
      [allEraseBlock 5, next, DecimalSetterMinimumBody.ruleCRoot] := by
  intro pole
  have shell :=
    singletonPole_threeBlock_ruleCRoot_allEraseBlock_targetB_beta_three_discrepancyShell
      body next pole
  rw [boundaryDiscrepancy_intCast] at shell
  have depth_nonnegative := hasValue_intCast_nonnegative shell.1
  omega

end MatrixMortality.DecimalSetterBridgeRay
