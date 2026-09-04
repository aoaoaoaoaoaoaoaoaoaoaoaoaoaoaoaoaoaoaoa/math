import MatrixMortality.DecimalSetterGapCleanAncestry

/-!
# Factorwise pole gate above the uniform contaminated tail

At a singleton pole over `gapContaminatedTail`, the primitive decimal-gap factor divides the
product of the current and inherited lower boundary codes. More precisely, every divisor of
the gap that is coprime to the inherited lower code divides the current lower code; the final
theorem records the corresponding primewise gate.

This conclusion is factorwise. The inherited lower code is not uniformly coprime to the gap and
can contain the whole gap factor, so it cannot be cancelled without an additional hypothesis.
The gate therefore does not exclude the contaminated family by itself.
-/

namespace MatrixMortality.DecimalSetterBridgeRay

open MatrixMortality.DecimalSetterAncestry
open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterBridge
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterChamber
open MatrixMortality.DecimalSetterMatrix

private theorem gapContaminated_marker_relation (β : Nat) :
    9 * (code (nearyMarker β) : ℤ) = 26 * gapFactor β + 175 := by
  have identity := markerWord_code_identity β
  have integer_identity :
      9 * (code (nearyMarker β) : ℤ) + 7 = 52 * (10 : ℤ) ^ β := by
    simpa only [markerWord, nearyMarker] using (by exact_mod_cast identity)
  simp only [gapFactor]
  linear_combination integer_identity

private theorem gapContaminated_upper_relation (β : Nat) :
    9 *
        (code
          (spell (nearyUpper β) gapContaminatedRoot ++ nearyMarker β) : ℤ) =
      2501 * gapFactor β + 17500 := by
  have marker_relation := gapContaminated_marker_relation β
  let P : ℤ :=
    code (spell (nearyUpper β) gapContaminatedRoot ++ nearyMarker β)
  have P_eq : P = 55 * (10 : ℤ) ^ (β + 1) + code (nearyMarker β) := by
    dsimp only [P]
    have spelling : spell (nearyUpper β) gapContaminatedRoot = [true, true] := rfl
    rw [spelling, code_append]
    norm_num [code, digit, Nat.ofDigits, nearyMarker]
  change 9 * P = _
  rw [P_eq]
  rw [pow_succ]
  have q_relation :
      2 * (10 : ℤ) ^ β = gapFactor β + 7 := by
    simp [gapFactor]
  linear_combination marker_relation + 2475 * q_relation

private theorem gapContaminated_lift_relation (β : Nat) :
    decimalLift ((10 : ℤ) ^ β) = 251 * gapFactor β + 1750 := by
  simp [decimalLift, gapFactor]
  ring

private theorem gapFactor_coprime_seven (β : Nat) :
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

private theorem gapFactor_coprime_1750
    {β : Nat} (β_pos : 0 < β) :
    IsCoprime (gapFactor β) (1750 : ℤ) := by
  have q_ten := gapFactor_coprime_ten β_pos
  have q_two : IsCoprime (gapFactor β) (2 : ℤ) :=
    IsCoprime.of_isCoprime_of_dvd_right q_ten (by norm_num)
  have q_five : IsCoprime (gapFactor β) (5 : ℤ) :=
    IsCoprime.of_isCoprime_of_dvd_right q_ten (by norm_num)
  have q_seven := gapFactor_coprime_seven β
  simpa using (q_two.mul_right (q_five.pow_right (n := 3))).mul_right q_seven

private theorem gapFactor_coprime_lift
    {β : Nat} (β_pos : 0 < β) :
    IsCoprime (gapFactor β) (decimalLift ((10 : ℤ) ^ β)) := by
  have base := gapFactor_coprime_1750 β_pos
  rw [gapContaminated_lift_relation]
  have shifted := base.add_mul_right_right (251 : ℤ)
  simpa [add_comm] using shifted

private theorem gapFactor_coprime_eleven (β : Nat) :
    IsCoprime (gapFactor β) (11 : ℤ) := by
  have ten_mod : (10 : ℤ) ≡ -1 [ZMOD 11] := by norm_num
  have power_mod := ten_mod.pow β
  have residue_cases : (10 : ℤ) ^ β ≡ 1 [ZMOD 11] ∨
      (10 : ℤ) ^ β ≡ -1 [ZMOD 11] := by
    rcases Nat.even_or_odd β with β_even | β_odd
    · obtain ⟨k, rfl⟩ := β_even
      left
      simpa [pow_mul] using power_mod
    · obtain ⟨k, rfl⟩ := β_odd
      right
      simpa [pow_add, pow_mul] using power_mod
  rcases residue_cases with residue | residue
  · have q_mod : gapFactor β ≡ 6 [ZMOD 11] := by
      simp only [gapFactor]
      calc
        2 * (10 : ℤ) ^ β - 7 ≡ 2 * 1 - 7 [ZMOD 11] :=
          (Int.ModEq.refl 2).mul residue |>.sub (Int.ModEq.refl 7)
        _ ≡ 6 [ZMOD 11] := by norm_num
    rw [Int.modEq_iff_dvd] at q_mod
    obtain ⟨k, relation⟩ := q_mod
    have q_eq : gapFactor β = 6 + 11 * (-k) := by omega
    rw [q_eq]
    exact (by norm_num : IsCoprime (6 : ℤ) 11).add_mul_left_left (-k)
  · have q_mod : gapFactor β ≡ 2 [ZMOD 11] := by
      simp only [gapFactor]
      calc
        2 * (10 : ℤ) ^ β - 7 ≡ 2 * (-1) - 7 [ZMOD 11] :=
          (Int.ModEq.refl 2).mul residue |>.sub (Int.ModEq.refl 7)
        _ ≡ 2 [ZMOD 11] := by norm_num
    rw [Int.modEq_iff_dvd] at q_mod
    obtain ⟨k, relation⟩ := q_mod
    have q_eq : gapFactor β = 2 + 11 * (-k) := by omega
    rw [q_eq]
    exact (by norm_num : IsCoprime (2 : ℤ) 11).add_mul_left_left (-k)

private theorem singletonTrace_integer_coprime_gapFactor
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
    simpa only [G, ρ] using gapFactor_coprime_lift β_pos
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

private theorem isCoprime_iff_of_unit_linear_relation
    {r left right leftUnit rightUnit multiple : ℤ}
    (leftUnit_coprime : IsCoprime r leftUnit)
    (rightUnit_coprime : IsCoprime r rightUnit)
    (relation : leftUnit * left + rightUnit * right = r * multiple) :
    IsCoprime r left ↔ IsCoprime r right := by
  constructor
  · intro left_coprime
    have left_product : IsCoprime r (leftUnit * left) :=
      leftUnit_coprime.mul_right left_coprime
    have shifted := left_product.neg_right.add_mul_right_right multiple
    have right_product : IsCoprime r (rightUnit * right) := by
      rw [show rightUnit * right = -(leftUnit * left) + multiple * r by
        linear_combination relation]
      exact shifted
    exact right_product.of_mul_right_right
  · intro right_coprime
    have right_product : IsCoprime r (rightUnit * right) :=
      rightUnit_coprime.mul_right right_coprime
    have shifted := right_product.neg_right.add_mul_right_right multiple
    have left_product : IsCoprime r (leftUnit * left) := by
      rw [show leftUnit * left = -(rightUnit * right) + multiple * r by
        linear_combination relation]
      exact shifted
    exact left_product.of_mul_right_right

/-- Every divisor of the primitive gap sees exactly the same coprime support in the reduced
quotient discrepancy `b - 10a` as in the tail's lower boundary code. -/
theorem gapContaminatedTail_reducedDiscrepancy_coprime_iff_lower
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter) {r : ℤ}
    (r_dvd_q : r ∣ gapFactor β) :
    let reduced :=
      (parsedRay β body gapContaminatedTail).2 /
        (parsedRay β body gapContaminatedTail).1 / 10
    IsCoprime r ((reduced.den : ℤ) - 10 * reduced.num) ↔
      IsCoprime r
        (code (spell (nearyLower β body) gapContaminatedNext) : ℤ) := by
  let q : ℤ := gapFactor β
  let M : ℤ := code (nearyMarker β)
  let P : ℤ :=
    code (spell (nearyUpper β) gapContaminatedRoot ++ nearyMarker β)
  let G : ℤ := decimalLift ((10 : ℤ) ^ β)
  let V : ℤ := code (spell (nearyLower β body) gapContaminatedNext)
  let numerator : ℤ := 90 * M * P
  let denominator : ℤ := 9 * P ^ 2 - 11 * G * V
  let reduced :=
    (parsedRay β body gapContaminatedTail).2 /
      (parsedRay β body gapContaminatedTail).1 / 10
  have β_pos : 0 < β := by omega
  have reduced_ne : reduced ≠ 0 := by
    have ratio_ne :=
      (gapContaminatedTail_ratio_hasDecimalShell β_large body).1.1
    exact div_ne_zero ratio_ne (by norm_num)
  have formula := gapContaminatedTail_normalizedQuotient_formula β_large body
  have reduced_eq : reduced = (numerator : ℚ) / denominator := by
    norm_num [reduced, numerator, denominator, M, P, G, V,
      DecimalSetterMatrix.marker, upperBoundaryCode, lowerBoundaryCode,
      lift, decimalLift, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
      Int.cast_pow] at formula ⊢
    exact formula
  have denominator_ne : denominator ≠ 0 := by
    intro denominator_zero
    apply reduced_ne
    rw [reduced_eq, denominator_zero]
    simp
  obtain ⟨common, numerator_eq, denominator_eq⟩ :=
    Rat.exists_eq_mul_div_num_and_eq_mul_div_den numerator denominator_ne
  rw [← reduced_eq] at numerator_eq denominator_eq
  have common_dvd_numerator : common ∣ numerator :=
    ⟨reduced.num, numerator_eq⟩
  have q_common : IsCoprime q common := by
    have q_numerator := gapContaminatedTail_rawNumerator_coprime_gapFactor β_pos
    exact IsCoprime.of_isCoprime_of_dvd_right
      (by simpa only [q, numerator, M, P] using q_numerator)
      common_dvd_numerator
  have r_common : IsCoprime r common :=
    IsCoprime.of_isCoprime_of_dvd_left q_common (by
      simpa only [q] using r_dvd_q)
  have q_eleven := gapFactor_coprime_eleven β
  have q_G := gapFactor_coprime_lift β_pos
  have r_eleven : IsCoprime r (11 : ℤ) :=
    IsCoprime.of_isCoprime_of_dvd_left q_eleven r_dvd_q
  have r_G : IsCoprime r G :=
    IsCoprime.of_isCoprime_of_dvd_left
      (by simpa only [G] using q_G) r_dvd_q
  have P_relation : 9 * P = 2501 * q + 17500 := by
    simpa only [P, q] using gapContaminated_upper_relation β
  have M_relation : 9 * M = 26 * q + 175 := by
    simpa only [M, q] using gapContaminated_marker_relation β
  have discrepancy_relation :
      common * ((reduced.den : ℤ) - 10 * reduced.num) + 11 * G * V =
        q * (-99 * P) := by
    dsimp only [denominator, numerator] at denominator_eq numerator_eq
    calc
      common * ((reduced.den : ℤ) - 10 * reduced.num) + 11 * G * V =
          (9 * P ^ 2 - 11 * G * V) - 10 * (90 * M * P) + 11 * G * V := by
            rw [denominator_eq, numerator_eq]
            ring
      _ = P * (9 * P - 100 * (9 * M)) := by ring
      _ = P * ((2501 * q + 17500) - 100 * (26 * q + 175)) := by
        rw [P_relation, M_relation]
      _ = q * (-99 * P) := by ring
  obtain ⟨quotient, q_eq⟩ := r_dvd_q
  have q_eq' : q = r * quotient := by
    simpa only [q] using q_eq
  have discrepancy_relation_r :
      common * ((reduced.den : ℤ) - 10 * reduced.num) + 11 * G * V =
        r * (quotient * (-99 * P)) := by
    rw [discrepancy_relation, q_eq']
    ring
  simpa only [reduced, V] using
    isCoprime_iff_of_unit_linear_relation
      r_common (r_eleven.mul_right r_G) discrepancy_relation_r

/-- The unreduced quotient discrepancy and the tail lower code have identical coprime support
at every divisor of the primitive gap. -/
theorem gapContaminatedTail_rawDiscrepancy_coprime_iff_lower
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter) {r : ℤ}
    (r_dvd_q : r ∣ gapFactor β) :
    let M : ℤ := code (nearyMarker β)
    let P : ℤ :=
      code (spell (nearyUpper β) gapContaminatedRoot ++ nearyMarker β)
    let G : ℤ := decimalLift ((10 : ℤ) ^ β)
    let V : ℤ := code (spell (nearyLower β body) gapContaminatedNext)
    let numerator : ℤ := 90 * M * P
    let denominator : ℤ := 9 * P ^ 2 - 11 * G * V
    IsCoprime r (denominator - 10 * numerator) ↔ IsCoprime r V := by
  let q : ℤ := gapFactor β
  let M : ℤ := code (nearyMarker β)
  let P : ℤ :=
    code (spell (nearyUpper β) gapContaminatedRoot ++ nearyMarker β)
  let G : ℤ := decimalLift ((10 : ℤ) ^ β)
  let V : ℤ := code (spell (nearyLower β body) gapContaminatedNext)
  let numerator : ℤ := 90 * M * P
  let denominator : ℤ := 9 * P ^ 2 - 11 * G * V
  have q_eleven := gapFactor_coprime_eleven β
  have q_G := gapFactor_coprime_lift β_pos
  have r_eleven : IsCoprime r (11 : ℤ) :=
    IsCoprime.of_isCoprime_of_dvd_left q_eleven r_dvd_q
  have r_G : IsCoprime r G :=
    IsCoprime.of_isCoprime_of_dvd_left
      (by simpa only [G] using q_G) r_dvd_q
  have P_relation : 9 * P = 2501 * q + 17500 := by
    simpa only [P, q] using gapContaminated_upper_relation β
  have M_relation : 9 * M = 26 * q + 175 := by
    simpa only [M, q] using gapContaminated_marker_relation β
  have discrepancy_relation :
      (denominator - 10 * numerator) + 11 * G * V = q * (-99 * P) := by
    dsimp only [denominator, numerator]
    calc
      9 * P ^ 2 - 11 * G * V - 10 * (90 * M * P) + 11 * G * V =
          P * (9 * P - 100 * (9 * M)) := by ring
      _ = P * ((2501 * q + 17500) - 100 * (26 * q + 175)) := by
        rw [P_relation, M_relation]
      _ = q * (-99 * P) := by ring
  obtain ⟨quotient, q_eq⟩ := r_dvd_q
  have q_eq' : q = r * quotient := by simpa only [q] using q_eq
  have discrepancy_relation_r :
      (denominator - 10 * numerator) + 11 * G * V =
        r * (quotient * (-99 * P)) := by
    rw [discrepancy_relation, q_eq']
    ring
  have discrepancy_relation_for_helper :
      1 * (denominator - 10 * numerator) + 11 * G * V =
        r * (quotient * (-99 * P)) := by
    simpa using discrepancy_relation_r
  have support_iff :
      IsCoprime r (denominator - 10 * numerator) ↔ IsCoprime r V :=
    isCoprime_iff_of_unit_linear_relation
      (isCoprime_one_right : IsCoprime r (1 : ℤ))
      (r_eleven.mul_right r_G) discrepancy_relation_for_helper
  simpa only [M, P, G, V, numerator, denominator] using support_iff

private theorem gapContaminatedTail_singletonPole_integerEquation
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (letter : TagLetter) (current : List NearyTile)
    (pole :
      HitsSquarePole β body [.erase letter]
        (current :: gapContaminatedTail)) :
    let q : ℤ := gapFactor β
    let E : ℤ := decimalGap ((10 : ℤ) ^ β)
    let M : ℤ := code (nearyMarker β)
    let G : ℤ := decimalLift ((10 : ℤ) ^ β)
    let P : ℤ :=
      code (spell (nearyUpper β) gapContaminatedRoot ++ nearyMarker β)
    let V : ℤ := code (spell (nearyLower β body) gapContaminatedNext)
    let numerator : ℤ := 90 * M * P
    let denominator : ℤ := 9 * P ^ 2 - 11 * G * V
    let currentUpper : ℤ :=
      code (spell (nearyUpper β) current ++ nearyMarker β)
    let currentLower : ℤ := code (spell (nearyLower β body) current)
    let currentScale : ℤ := 10 ^ (spell (nearyUpper β) current).length
    ∃ trace : ℤ,
      singletonTrace β letter = (trace : ℚ) ∧
        IsCoprime q trace ∧
          (((E * currentUpper + G * currentLower) * denominator -
              10 * G * currentLower * numerator) * trace =
            E * M * G * currentScale * denominator * 7) := by
  let q : ℤ := gapFactor β
  let E : ℤ := decimalGap ((10 : ℤ) ^ β)
  let M : ℤ := code (nearyMarker β)
  let G : ℤ := decimalLift ((10 : ℤ) ^ β)
  let P : ℤ :=
    code (spell (nearyUpper β) gapContaminatedRoot ++ nearyMarker β)
  let V : ℤ := code (spell (nearyLower β body) gapContaminatedNext)
  let numerator : ℤ := 90 * M * P
  let denominator : ℤ := 9 * P ^ 2 - 11 * G * V
  let currentUpper : ℤ :=
    code (spell (nearyUpper β) current ++ nearyMarker β)
  let currentLower : ℤ := code (spell (nearyLower β body) current)
  let currentScale : ℤ := 10 ^ (spell (nearyUpper β) current).length
  obtain ⟨trace, trace_eq, trace_coprime⟩ :=
    singletonTrace_integer_coprime_gapFactor β_pos letter
  refine ⟨trace, trace_eq, by simpa only [q] using trace_coprime, ?_⟩
  have recurrence :=
    (hitsSquarePole_singleton_cons_iff_rayRecurrence β_pos body letter current
      gapContaminatedNext [gapContaminatedRoot]).mp pole
  have coordinates := gapContaminatedTail_parsedRay_coordinates β_pos body
  have coordinates' :
      parsedRay β body [gapContaminatedNext, gapContaminatedRoot] =
        ((9 * upperBoundaryCode β gapContaminatedRoot ^ 2 -
            11 * lift ((10 : ℚ) ^ β) *
              lowerBoundaryCode β body gapContaminatedNext) /
            (9 * DecimalSetterMatrix.marker β ^ 2),
          100 * upperBoundaryCode β gapContaminatedRoot /
            DecimalSetterMatrix.marker β) := by
    simpa only [gapContaminatedTail] using coordinates
  rw [coordinates'] at recurrence
  rw [trace_eq] at recurrence
  have M_ne : (M : ℚ) ≠ 0 := by
    simpa only [M, DecimalSetterMatrix.marker, Int.cast_natCast] using
      (marker_hasDecimalShell β_pos).1.1
  have recurrence' :
      ((((E : ℚ) * currentUpper + G * currentLower) *
              ((denominator : ℚ) / (9 * (M : ℚ) ^ 2)) -
            (G : ℚ) * currentLower * (100 * (P : ℚ) / M)) * trace =
        (E : ℚ) * M * G * currentScale *
          ((denominator : ℚ) / (9 * (M : ℚ) ^ 2)) * 7) := by
    norm_num [E, M, G, P, V, denominator, currentUpper, currentLower,
      currentScale, boundaryTrace, gap, lift, DecimalSetterMatrix.marker,
      upperBoundaryCode, lowerBoundaryCode, upperScale, decimalGap,
      decimalLift, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      Int.cast_pow] at recurrence ⊢
    exact recurrence
  field_simp [M_ne] at recurrence'
  have rational_equation :
      ((((E : ℚ) * currentUpper + G * currentLower) * denominator -
          10 * G * currentLower * numerator) * trace =
        E * M * G * currentScale * denominator * 7) := by
    norm_num [numerator, Int.cast_mul] at recurrence' ⊢
    linear_combination recurrence'
  exact_mod_cast rational_equation

/-- A singleton pole over the contaminated tail forces the primitive gap into the current
lower code times the unreduced quotient discrepancy. -/
theorem gapContaminatedTail_singletonPole_forces_rawDiscrepancy
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (letter : TagLetter) (current : List NearyTile)
    (pole :
      HitsSquarePole β body [.erase letter]
        (current :: gapContaminatedTail)) :
    let M : ℤ := code (nearyMarker β)
    let G : ℤ := decimalLift ((10 : ℤ) ^ β)
    let P : ℤ :=
      code (spell (nearyUpper β) gapContaminatedRoot ++ nearyMarker β)
    let V : ℤ := code (spell (nearyLower β body) gapContaminatedNext)
    let numerator : ℤ := 90 * M * P
    let denominator : ℤ := 9 * P ^ 2 - 11 * G * V
    let currentLower : ℤ := code (spell (nearyLower β body) current)
    gapFactor β ∣ currentLower * (denominator - 10 * numerator) := by
  let q : ℤ := gapFactor β
  let E : ℤ := decimalGap ((10 : ℤ) ^ β)
  let M : ℤ := code (nearyMarker β)
  let G : ℤ := decimalLift ((10 : ℤ) ^ β)
  let P : ℤ :=
    code (spell (nearyUpper β) gapContaminatedRoot ++ nearyMarker β)
  let V : ℤ := code (spell (nearyLower β body) gapContaminatedNext)
  let numerator : ℤ := 90 * M * P
  let denominator : ℤ := 9 * P ^ 2 - 11 * G * V
  let currentUpper : ℤ :=
    code (spell (nearyUpper β) current ++ nearyMarker β)
  let currentLower : ℤ := code (spell (nearyLower β body) current)
  let currentScale : ℤ := 10 ^ (spell (nearyUpper β) current).length
  obtain ⟨trace, _, trace_coprime, pole_equation⟩ :=
    gapContaminatedTail_singletonPole_integerEquation β_pos body letter current pole
  have E_eq : E = 9 * q := by
    simp [E, q, decimalGap, gapFactor]
  change
    (((E * currentUpper + G * currentLower) * denominator -
        10 * G * currentLower * numerator) * trace =
      E * M * G * currentScale * denominator * 7) at pole_equation
  have raw_product_dvd :
      q ∣ G * trace * (currentLower * (denominator - 10 * numerator)) := by
    refine ⟨9 *
      (M * G * currentScale * denominator * 7 -
        currentUpper * denominator * trace), ?_⟩
    rw [E_eq] at pole_equation
    linear_combination pole_equation
  have q_G : IsCoprime q G := by
    simpa only [q, G] using gapFactor_coprime_lift β_pos
  have coefficient_coprime : IsCoprime q (G * trace) :=
    q_G.mul_right (by simpa only [q] using trace_coprime)
  have desired : q ∣ currentLower * (denominator - 10 * numerator) := by
    apply coefficient_coprime.dvd_of_dvd_mul_right
    simpa [mul_assoc, mul_left_comm, mul_comm] using raw_product_dvd
  simpa only [q, M, G, P, V, numerator, denominator, currentLower] using desired

/-- Reduced-coordinate form of the pole congruence. If the normalized inherited quotient is
`a/b`, a singleton pole forces `q ∣ Vcurrent·(b−10a)`. -/
theorem gapContaminatedTail_singletonPole_forces_reducedDiscrepancy
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (letter : TagLetter) (current : List NearyTile)
    (pole :
      HitsSquarePole β body [.erase letter]
        (current :: gapContaminatedTail)) :
    let reduced :=
      (parsedRay β body gapContaminatedTail).2 /
        (parsedRay β body gapContaminatedTail).1 / 10
    gapFactor β ∣
      (code (spell (nearyLower β body) current) : ℤ) *
        ((reduced.den : ℤ) - 10 * reduced.num) := by
  let q : ℤ := gapFactor β
  let M : ℤ := code (nearyMarker β)
  let P : ℤ :=
    code (spell (nearyUpper β) gapContaminatedRoot ++ nearyMarker β)
  let G : ℤ := decimalLift ((10 : ℤ) ^ β)
  let V : ℤ := code (spell (nearyLower β body) gapContaminatedNext)
  let numerator : ℤ := 90 * M * P
  let denominator : ℤ := 9 * P ^ 2 - 11 * G * V
  let currentLower : ℤ := code (spell (nearyLower β body) current)
  let reduced :=
    (parsedRay β body gapContaminatedTail).2 /
      (parsedRay β body gapContaminatedTail).1 / 10
  have β_pos : 0 < β := by omega
  have raw_dvd : q ∣ currentLower * (denominator - 10 * numerator) := by
    simpa only [q, M, P, G, V, numerator, denominator, currentLower] using
      gapContaminatedTail_singletonPole_forces_rawDiscrepancy
        β_pos body letter current pole
  have reduced_ne : reduced ≠ 0 := by
    have ratio_ne :=
      (gapContaminatedTail_ratio_hasDecimalShell β_large body).1.1
    exact div_ne_zero ratio_ne (by norm_num)
  have formula := gapContaminatedTail_normalizedQuotient_formula β_large body
  have reduced_eq : reduced = (numerator : ℚ) / denominator := by
    norm_num [reduced, numerator, denominator, M, P, G, V,
      DecimalSetterMatrix.marker, upperBoundaryCode, lowerBoundaryCode,
      lift, decimalLift, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
      Int.cast_pow] at formula ⊢
    exact formula
  have denominator_ne : denominator ≠ 0 := by
    intro denominator_zero
    apply reduced_ne
    rw [reduced_eq, denominator_zero]
    simp
  obtain ⟨common, numerator_eq, denominator_eq⟩ :=
    Rat.exists_eq_mul_div_num_and_eq_mul_div_den numerator denominator_ne
  rw [← reduced_eq] at numerator_eq denominator_eq
  have common_dvd_numerator : common ∣ numerator :=
    ⟨reduced.num, numerator_eq⟩
  have q_common : IsCoprime q common := by
    have q_numerator := gapContaminatedTail_rawNumerator_coprime_gapFactor β_pos
    exact IsCoprime.of_isCoprime_of_dvd_right
      (by simpa only [q, numerator, M, P] using q_numerator)
      common_dvd_numerator
  have raw_discrepancy_eq :
      denominator - 10 * numerator =
        common * ((reduced.den : ℤ) - 10 * reduced.num) := by
    rw [denominator_eq, numerator_eq]
    ring
  have scaled_dvd :
      q ∣ common *
        (currentLower * ((reduced.den : ℤ) - 10 * reduced.num)) := by
    rw [raw_discrepancy_eq] at raw_dvd
    simpa [mul_assoc, mul_left_comm, mul_comm] using raw_dvd
  have desired :
      q ∣ currentLower * ((reduced.den : ℤ) - 10 * reduced.num) :=
    q_common.dvd_of_dvd_mul_left scaled_dvd
  simpa only [q, currentLower, reduced] using desired

/-- A singleton pole over the uniform contaminated tail forces every primitive-gap factor into
the product of the current and inherited lower boundary codes. -/
theorem gapContaminatedTail_singletonPole_forces_lowerProduct
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (letter : TagLetter) (current : List NearyTile)
    (pole :
      HitsSquarePole β body [.erase letter]
        (current :: gapContaminatedTail)) :
    gapFactor β ∣
      (code (spell (nearyLower β body) current) : ℤ) *
        code (spell (nearyLower β body) gapContaminatedNext) := by
  let q : ℤ := gapFactor β
  let M : ℤ := code (nearyMarker β)
  let P : ℤ :=
    code (spell (nearyUpper β) gapContaminatedRoot ++ nearyMarker β)
  let G : ℤ := decimalLift ((10 : ℤ) ^ β)
  let V : ℤ := code (spell (nearyLower β body) gapContaminatedNext)
  let numerator : ℤ := 90 * M * P
  let denominator : ℤ := 9 * P ^ 2 - 11 * G * V
  let currentLower : ℤ := code (spell (nearyLower β body) current)
  have raw_dvd : q ∣ currentLower * (denominator - 10 * numerator) := by
    simpa only [q, M, P, G, V, numerator, denominator, currentLower] using
      gapContaminatedTail_singletonPole_forces_rawDiscrepancy
        β_pos body letter current pole
  have P_relation : 9 * P = 2501 * q + 17500 := by
    simpa only [P, q] using gapContaminated_upper_relation β
  have M_relation : 9 * M = 26 * q + 175 := by
    simpa only [M, q] using gapContaminated_marker_relation β
  have discrepancy_relation :
      (denominator - 10 * numerator) + 11 * G * V = q * (-99 * P) := by
    dsimp only [denominator, numerator]
    calc
      9 * P ^ 2 - 11 * G * V - 10 * (90 * M * P) + 11 * G * V =
          P * (9 * P - 100 * (9 * M)) := by ring
      _ = P * ((2501 * q + 17500) - 100 * (26 * q + 175)) := by
        rw [P_relation, M_relation]
      _ = q * (-99 * P) := by ring
  have sum_dvd :
      q ∣ currentLower * (denominator - 10 * numerator) +
        11 * G * (currentLower * V) := by
    refine ⟨currentLower * (-99 * P), ?_⟩
    linear_combination currentLower * discrepancy_relation
  have coefficient_product_dvd : q ∣ 11 * G * (currentLower * V) := by
    have difference := dvd_sub sum_dvd raw_dvd
    simpa only [add_sub_cancel_left] using difference
  have q_eleven : IsCoprime q (11 : ℤ) := by
    simpa only [q] using gapFactor_coprime_eleven β
  have q_G : IsCoprime q G := by
    simpa only [q, G] using gapFactor_coprime_lift β_pos
  have desired : q ∣ currentLower * V :=
    (q_eleven.mul_right q_G).dvd_of_dvd_mul_left coefficient_product_dvd
  simpa only [q, currentLower, V] using desired

/-- Any composite or prime-power divisor of the primitive gap that is absent from the inherited
lower code must occur in the current lower code at a singleton pole. -/
theorem gapContaminatedTail_singletonPole_forces_gapDivisor_dvd_currentLower
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (letter : TagLetter) (current : List NearyTile) {r : ℤ}
    (r_dvd_q : r ∣ gapFactor β)
    (tailLower_coprime :
      IsCoprime r
        (code (spell (nearyLower β body) gapContaminatedNext) : ℤ))
    (pole :
      HitsSquarePole β body [.erase letter]
        (current :: gapContaminatedTail)) :
    r ∣ (code (spell (nearyLower β body) current) : ℤ) := by
  have q_product :=
    gapContaminatedTail_singletonPole_forces_lowerProduct
      (by omega : 0 < β) body letter current pole
  have r_product := r_dvd_q.trans q_product
  exact tailLower_coprime.dvd_of_dvd_mul_right r_product

/-- Primewise form of the contaminated-tail pole gate: every gap prime absent from the tail
lower code must occur in the current lower code. -/
theorem gapContaminatedTail_singletonPole_forces_gapPrime_dvd_currentLower
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter)
    (letter : TagLetter) (current : List NearyTile) {p : ℤ}
    (p_prime : Prime p) (p_dvd_q : p ∣ gapFactor β)
    (p_not_dvd_tailLower :
      ¬p ∣ (code (spell (nearyLower β body) gapContaminatedNext) : ℤ))
    (pole :
      HitsSquarePole β body [.erase letter]
        (current :: gapContaminatedTail)) :
    p ∣ (code (spell (nearyLower β body) current) : ℤ) := by
  apply gapContaminatedTail_singletonPole_forces_gapDivisor_dvd_currentLower
    β_large body letter current p_dvd_q
  · exact p_prime.coprime_iff_not_dvd.mpr p_not_dvd_tailLower
  · exact pole

/-- The inherited-support boundary is genuine. At deletion width three, this explicit lawful
body makes the inherited lower code contain the whole primitive gap. This is not a pole witness;
it shows only that the coprimality premise in the factorwise cancellation theorem is necessary. -/
theorem betaThree_gapContaminatedNext_lower_contains_gapFactor :
    gapFactor 3 ∣
      (code
        (spell (nearyLower 3
          [.b, .b, .b, .b, .c, .b, .c, .c, .c, .c])
          gapContaminatedNext) : ℤ) := by
  norm_num [gapFactor, gapContaminatedNext, spell, nearyLower, tagEncode,
    tagCode, code, digit, Nat.ofDigits, List.replicate_succ]

end MatrixMortality.DecimalSetterBridgeRay
