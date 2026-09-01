import MatrixMortality.DecimalSetterSingletonAncestry

/-!
# Integral and gap-clean singleton ancestry

A decimal `(1,1)` parser quotient always admits integral decimal-unit peeled coordinates whose
denominator descends through the decimal gap. For a single recursive parser step, these
coordinates are a common nonzero rational rescaling of the physical residual and inherited
upper coordinate.

The primitive gap factor need not be coprime to the resulting numerator. Such a gap-clean
normalization exists exactly when the reduced numerator of the parser quotient contains the
full primitive gap factor. A lawful two-block family violates this divisibility for every
`β≥3` and every tag body, so decimal shell data and arbitrary projective rescaling alone cannot
supply the coprimality hypothesis used by the gap-factor ancestry gates.
-/

namespace MatrixMortality.DecimalSetterBridgeRay

open MatrixMortality.DecimalSetterAncestry
open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterBridge
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterMatrix
open MatrixMortality.PadicValuation

private theorem rat_denominator_not_dvd_of_isUnit
    {prime : Nat} [Fact prime.Prime] {value : ℚ}
    (unit : IsUnit prime value) :
    ¬(prime : ℤ) ∣ (value.den : ℤ) := by
  intro denominator_dvd
  have denominator_dvd_nat : prime ∣ value.den := by
    exact_mod_cast denominator_dvd
  have denominator_value_ne : padicValNat prime value.den ≠ 0 :=
    (dvd_iff_padicValNat_ne_zero value.den_ne_zero).mp denominator_dvd_nat
  have valuation_eq :
      padicValInt prime value.num = padicValNat prime value.den := by
    have valuation_zero := unit.2
    rw [padicValRat_def] at valuation_zero
    omega
  have numerator_value_ne : padicValInt prime value.num ≠ 0 := by
    rw [valuation_eq]
    exact_mod_cast denominator_value_ne
  have numerator_dvd : (prime : ℤ) ∣ value.num := by
    rw [show (prime : ℤ) = (prime : ℤ) ^ 1 by simp,
      padicValInt_dvd_iff]
    exact Or.inr (Nat.one_le_iff_ne_zero.mpr numerator_value_ne)
  obtain ⟨left, right, bezout⟩ := Rat.isCoprime_num_den value
  have prime_dvd_one : (prime : ℤ) ∣ 1 := by
    rw [← bezout]
    exact dvd_add (numerator_dvd.mul_left left)
      (denominator_dvd.mul_left right)
  have prime_dvd_one_nat : prime ∣ 1 := by
    exact_mod_cast prime_dvd_one
  exact (Fact.out : prime.Prime).not_dvd_one prime_dvd_one_nat

private theorem rat_numerator_not_dvd_of_isUnit
    {prime : Nat} [Fact prime.Prime] {value : ℚ}
    (unit : IsUnit prime value) :
    ¬(prime : ℤ) ∣ value.num := by
  have denominator_not_dvd := rat_denominator_not_dvd_of_isUnit unit
  have denominator_not_dvd_nat : ¬prime ∣ value.den := by
    intro denominator_dvd
    apply denominator_not_dvd
    exact_mod_cast denominator_dvd
  have denominator_value_zero : padicValNat prime value.den = 0 :=
    padicValNat.eq_zero_of_not_dvd denominator_not_dvd_nat
  have numerator_value_zero : padicValInt prime value.num = 0 := by
    have valuation_zero := unit.2
    rw [padicValRat_def, denominator_value_zero] at valuation_zero
    have cast_zero : (padicValInt prime value.num : ℤ) = 0 := by
      simpa using valuation_zero
    exact Int.ofNat_inj.mp cast_zero
  intro numerator_dvd
  have numerator_ne : value.num ≠ 0 := Rat.num_ne_zero.mpr unit.1
  have numerator_value_positive : 1 ≤ padicValInt prime value.num :=
    ((padicValInt_dvd_iff (p := prime) 1 value.num).mp (by
      simpa using numerator_dvd)).resolve_left numerator_ne
  omega

private theorem rat_num_isUnit
    {prime : Nat} [Fact prime.Prime] {value : ℚ}
    (unit : IsUnit prime value) :
    IsUnit prime (value.num : ℚ) :=
  intCast_isUnit_of_not_dvd (rat_numerator_not_dvd_of_isUnit unit)

private theorem rat_den_isUnit
    {prime : Nat} [Fact prime.Prime] {value : ℚ}
    (unit : IsUnit prime value) :
    IsUnit prime (value.den : ℚ) := by
  have denominator_not_dvd := rat_denominator_not_dvd_of_isUnit unit
  simpa using intCast_isUnit_of_not_dvd denominator_not_dvd

private theorem rat_num_hasDecimalShell
    {value : ℚ} (unit : HasDecimalShell value 0 0) :
    HasDecimalShell (value.num : ℚ) 0 0 :=
  ⟨rat_num_isUnit unit.1, rat_num_isUnit unit.2⟩

private theorem rat_den_hasDecimalShell
    {value : ℚ} (unit : HasDecimalShell value 0 0) :
    HasDecimalShell (value.den : ℚ) 0 0 :=
  ⟨rat_den_isUnit unit.1, rat_den_isUnit unit.2⟩

/-- Every decimal `(1,1)` ray quotient admits integral decimal-unit peeled coordinates whose
denominator is the decimal gap times an integral decimal unit.

The canonical construction puts the entire decimal gap into the carrier numerator. It therefore
does not imply that the primitive gap factor is coprime to that numerator. -/
theorem admitsIntegralGapPeeledCarrier_of_ratio_shell
    {β : Nat} (β_pos : 0 < β) (ray : ℚ × ℚ)
    (ratio_shell : HasDecimalShell (ray.2 / ray.1) 1 1) :
    ∃ N D Nprev : ℤ,
      HasDecimalShell (N : ℚ) 0 0 ∧
        HasDecimalShell (D : ℚ) 0 0 ∧
          HasDecimalShell (Nprev : ℚ) 0 0 ∧
            D = decimalGap ((10 : ℤ) ^ β) * Nprev ∧
              RepresentsPeeledCarrier β ray N D := by
  let quotient := ray.2 / ray.1
  let reduced := quotient / 10
  let E : ℤ := decimalGap ((10 : ℤ) ^ β)
  let M : ℤ := code (nearyMarker β)
  let Nprev : ℤ := reduced.num
  let D : ℤ := E * Nprev
  let N : ℤ := E * M * reduced.den
  have reduced_shell : HasDecimalShell reduced 0 0 := by
    constructor
    · have shell := div_hasValue ratio_shell.1 ten_hasDecimalShell.1
      norm_num at shell
      simpa only [reduced, quotient] using shell
    · have shell := div_hasValue ratio_shell.2 ten_hasDecimalShell.2
      norm_num at shell
      simpa only [reduced, quotient] using shell
  have numerator_unit : HasDecimalShell (Nprev : ℚ) 0 0 := by
    simpa only [Nprev] using rat_num_hasDecimalShell reduced_shell
  have denominator_unit : HasDecimalShell (reduced.den : ℚ) 0 0 :=
    rat_den_hasDecimalShell reduced_shell
  have E_unit : HasDecimalShell (E : ℚ) 0 0 := by
    simpa only [E, gap, decimalGap, Int.cast_mul, Int.cast_sub,
      Int.cast_ofNat, Int.cast_pow] using gap_tenPow_hasDecimalShell β_pos
  have M_unit : HasDecimalShell (M : ℚ) 0 0 := by
    simpa only [M, DecimalSetterMatrix.marker, Int.cast_natCast] using
      marker_hasDecimalShell β_pos
  have N_unit : HasDecimalShell (N : ℚ) 0 0 := by
    simpa only [N, Int.cast_mul, Int.cast_natCast, zero_add] using
      (E_unit.mul M_unit).mul denominator_unit
  have D_unit : HasDecimalShell (D : ℚ) 0 0 := by
    simpa only [D, Int.cast_mul, zero_add] using E_unit.mul numerator_unit
  refine ⟨N, D, Nprev, N_unit, D_unit, numerator_unit, rfl, ?_⟩
  have ray_first_ne : ray.1 ≠ 0 := by
    intro ray_first_zero
    apply ratio_shell.1.1
    simp [ray_first_zero]
  have E_ne : (E : ℚ) ≠ 0 := E_unit.1.1
  have M_ne : (M : ℚ) ≠ 0 := M_unit.1.1
  have denominator_ne : (reduced.den : ℚ) ≠ 0 := denominator_unit.1.1
  have reduced_eq :
      (reduced.num : ℚ) / reduced.den = ray.2 / ray.1 / 10 := by
    simpa only [reduced, quotient] using reduced.num_div_den
  unfold RepresentsPeeledCarrier
  dsimp only [N, D, Nprev, E, M]
  simp only [Int.cast_mul, DecimalSetterMatrix.marker]
  field_simp [ray_first_ne, E_ne, M_ne, denominator_ne] at reduced_eq ⊢
  linear_combination E * M * reduced_eq

/-- The integral descended coordinates for one recursive parser step are a common nonzero
rational rescaling of the step residual and the inherited upper coordinate. -/
theorem rayStep_admitsIntegralGapPeeledCarrier_of_ratio_shell
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (roles : List NearyTile) (older : ℚ × ℚ)
    (ratio_shell :
      HasDecimalShell
        ((rayStep β body roles older).2 / (rayStep β body roles older).1) 1 1) :
    ∃ N D Nprev : ℤ, ∃ scale : ℚ,
      HasDecimalShell (N : ℚ) 0 0 ∧
        HasDecimalShell (D : ℚ) 0 0 ∧
          HasDecimalShell (Nprev : ℚ) 0 0 ∧
            scale ≠ 0 ∧
              (N : ℚ) =
                10 *
                  (boundaryTrace β body roles * older.1 -
                    lift ((10 : ℚ) ^ β) * lowerBoundaryCode β body roles * older.2) *
                    scale ∧
                (Nprev : ℚ) = upperScale β roles * older.1 * scale ∧
                  D = decimalGap ((10 : ℤ) ^ β) * Nprev ∧
                    RepresentsPeeledCarrier β (rayStep β body roles older) N D := by
  let ray := rayStep β body roles older
  obtain ⟨N, D, Nprev, N_unit, D_unit, Nprev_unit, D_eq, represents⟩ :=
    admitsIntegralGapPeeledCarrier_of_ratio_shell β_pos ray ratio_shell
  let E := gap ((10 : ℚ) ^ β)
  let μ := DecimalSetterMatrix.marker β
  let R := boundaryTrace β body roles * older.1 -
    lift ((10 : ℚ) ^ β) * lowerBoundaryCode β body roles * older.2
  let A := upperScale β roles
  let scale := (N : ℚ) / (10 * R)
  have E_ne : E ≠ 0 := (gap_tenPow_hasDecimalShell β_pos).1.1
  have μ_ne : μ ≠ 0 := (marker_hasDecimalShell β_pos).1.1
  have ray_first_ne : ray.1 ≠ 0 := by
    change HasDecimalShell (ray.2 / ray.1) 1 1 at ratio_shell
    intro ray_first_zero
    apply ratio_shell.1.1
    simp [ray_first_zero]
  have ray_first_eq : ray.1 = R / (E * μ) := by
    rfl
  have R_ne : R ≠ 0 := by
    intro R_zero
    apply ray_first_ne
    rw [ray_first_eq, R_zero]
    simp
  have scale_ne : scale ≠ 0 :=
    div_ne_zero N_unit.1.1 (mul_ne_zero (by norm_num) R_ne)
  have N_eq : (N : ℚ) = 10 * R * scale := by
    dsimp only [scale]
    field_simp [R_ne]
  have D_eq_rat : (D : ℚ) = E * Nprev := by
    rw [D_eq]
    simp only [E, gap, decimalGap, Int.cast_mul, Int.cast_sub,
      Int.cast_ofNat, Int.cast_pow]
  have representation : ray.1 * (10 * μ * D) = ray.2 * N := represents
  have ray_second_eq : ray.2 = A * older.1 := rfl
  have Nprev_eq : (Nprev : ℚ) = A * older.1 * scale := by
    rw [ray_first_eq, ray_second_eq, D_eq_rat, N_eq] at representation
    have scaled :
        (10 * R) * (Nprev : ℚ) = (10 * R) * (A * older.1 * scale) := by
      field_simp [E_ne, μ_ne] at representation
      rw [representation]
    exact mul_left_cancel₀ (mul_ne_zero (by norm_num) R_ne) scaled
  exact ⟨N, D, Nprev, scale, N_unit, D_unit, Nprev_unit, scale_ne,
    N_eq, Nprev_eq, D_eq, represents⟩

/-- The primitive gap factor is coprime to the decimal marker. -/
theorem gapFactor_coprime_marker
    {β : Nat} (β_pos : 0 < β) :
    IsCoprime (gapFactor β) (code (nearyMarker β) : ℤ) := by
  let q : ℤ := gapFactor β
  let M : ℤ := code (nearyMarker β)
  have q10 : IsCoprime q (10 : ℤ) := by
    simpa only [q] using gapFactor_coprime_ten β_pos
  have q2 : IsCoprime q (2 : ℤ) :=
    IsCoprime.of_isCoprime_of_dvd_right q10 (by norm_num)
  have q5 : IsCoprime q (5 : ℤ) :=
    IsCoprime.of_isCoprime_of_dvd_right q10 (by norm_num)
  have qpow : IsCoprime q ((10 : ℤ) ^ β) := q10.pow_right
  have q2rho : IsCoprime q (2 * (10 : ℤ) ^ β) := q2.mul_right qpow
  have rho_relation : 2 * (10 : ℤ) ^ β = 7 + q := by
    simp only [q, gapFactor]
    ring
  rw [rho_relation] at q2rho
  have q7 : IsCoprime q (7 : ℤ) := by
    exact IsCoprime.of_add_mul_left_right (z := 1) (by simpa using q2rho)
  have q25 : IsCoprime q ((5 : ℤ) ^ 2) := q5.pow_right
  have q175 : IsCoprime q ((5 : ℤ) ^ 2 * 7) := q25.mul_right q7
  have marker_relation_rat := DecimalSetterMatrix.marker_relation β
  have marker_relation_int : 9 * M = 52 * (10 : ℤ) ^ β - 7 := by
    have cast_relation :
        ((9 * M : ℤ) : ℚ) = ((52 * (10 : ℤ) ^ β - 7 : ℤ) : ℚ) := by
      simpa [M, DecimalSetterMatrix.marker] using marker_relation_rat
    exact_mod_cast cast_relation
  have marker_gap_relation : 9 * M = 26 * q + 175 := by
    dsimp only [q, gapFactor]
    linear_combination marker_relation_int
  have q_scaledMarker : IsCoprime q (9 * M) := by
    rw [marker_gap_relation]
    have shifted := q175.add_mul_right_right (26 : ℤ)
    norm_num at q175 shifted ⊢
    simpa [add_comm] using shifted
  exact IsCoprime.of_isCoprime_of_dvd_right q_scaledMarker ⟨9, by ring⟩

/-- A shell-unit parser quotient has a gap-clean descended integral carrier exactly when the
reduced numerator of its quotient after removing the built-in factor ten contains the primitive
gap factor. -/
theorem exists_gapCleanIntegralPeeledCarrier_iff_gapFactor_dvd_reducedNumerator
    {β : Nat} (β_pos : 0 < β) (ray : ℚ × ℚ)
    (ratio_shell : HasDecimalShell (ray.2 / ray.1) 1 1) :
    (∃ N D Nprev : ℤ,
      HasDecimalShell (N : ℚ) 0 0 ∧
        HasDecimalShell (D : ℚ) 0 0 ∧
          HasDecimalShell (Nprev : ℚ) 0 0 ∧
            D = decimalGap ((10 : ℤ) ^ β) * Nprev ∧
              IsCoprime (gapFactor β) N ∧
                RepresentsPeeledCarrier β ray N D) ↔
      gapFactor β ∣ ((ray.2 / ray.1) / 10).num := by
  let quotient := ray.2 / ray.1
  let reduced := quotient / 10
  let q : ℤ := gapFactor β
  let E : ℤ := decimalGap ((10 : ℤ) ^ β)
  let M : ℤ := code (nearyMarker β)
  have reduced_shell : HasDecimalShell reduced 0 0 := by
    constructor
    · have shell := div_hasValue ratio_shell.1 ten_hasDecimalShell.1
      norm_num at shell
      simpa only [reduced, quotient] using shell
    · have shell := div_hasValue ratio_shell.2 ten_hasDecimalShell.2
      norm_num at shell
      simpa only [reduced, quotient] using shell
  have numerator_unit : HasDecimalShell (reduced.num : ℚ) 0 0 :=
    rat_num_hasDecimalShell reduced_shell
  have denominator_unit : HasDecimalShell (reduced.den : ℚ) 0 0 :=
    rat_den_hasDecimalShell reduced_shell
  have ray_first_ne : ray.1 ≠ 0 := by
    intro ray_first_zero
    apply ratio_shell.1.1
    simp [ray_first_zero]
  have denominator_ne : (reduced.den : ℚ) ≠ 0 := denominator_unit.1.1
  have E_eq : E = 9 * q := by
    simp [E, q, decimalGap, gapFactor]
  have E_cast : (E : ℚ) = gap ((10 : ℚ) ^ β) := by
    simp [E, decimalGap, gap]
  have M_cast : (M : ℚ) = DecimalSetterMatrix.marker β := by
    simp [M, DecimalSetterMatrix.marker]
  have E_unit : HasDecimalShell (E : ℚ) 0 0 := by
    rw [E_cast]
    exact gap_tenPow_hasDecimalShell β_pos
  have M_unit : HasDecimalShell (M : ℚ) 0 0 := by
    rw [M_cast]
    exact marker_hasDecimalShell β_pos
  have nine_unit : HasDecimalShell (9 : ℚ) 0 0 :=
    ⟨intCast_isUnit_of_not_dvd (by norm_num),
      intCast_isUnit_of_not_dvd (by norm_num)⟩
  have q_cast : (q : ℚ) = (E : ℚ) / 9 := by
    rw [E_eq, Int.cast_mul]
    norm_num
  have q_unit : HasDecimalShell (q : ℚ) 0 0 := by
    rw [q_cast]
    exact ⟨by simpa using div_hasValue E_unit.1 nine_unit.1,
      by simpa using div_hasValue E_unit.2 nine_unit.2⟩
  have q_ne : q ≠ 0 := by
    exact_mod_cast q_unit.1.1
  have reduced_eq :
      (reduced.num : ℚ) / reduced.den = ray.2 / ray.1 / 10 := by
    simpa only [reduced, quotient] using reduced.num_div_den
  constructor
  · rintro ⟨N, D, Nprev, N_unit, _D_unit, _Nprev_unit, D_eq,
      qN_coprime, represents⟩
    have N_ne : (N : ℚ) ≠ 0 := N_unit.1.1
    have carrier_eq :
        (reduced.num : ℚ) / reduced.den =
          (M : ℚ) * E * Nprev / N := by
      rw [reduced_eq]
      unfold RepresentsPeeledCarrier at represents
      rw [D_eq, Int.cast_mul, E_cast] at represents
      rw [E_cast, M_cast]
      field_simp [ray_first_ne, N_ne]
      linear_combination -represents
    have cross_eq : reduced.num * N = (reduced.den : ℤ) * M * E * Nprev := by
      field_simp [denominator_ne, N_ne] at carrier_eq
      exact_mod_cast carrier_eq
    have q_dvd_E : q ∣ E := ⟨9, by rw [E_eq]; ring⟩
    have q_dvd_right : q ∣ (reduced.den : ℤ) * M * E * Nprev := by
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right q_dvd_E _) _
    have q_dvd_product : q ∣ reduced.num * N := by
      rw [cross_eq]
      exact q_dvd_right
    have q_dvd_numerator : q ∣ reduced.num :=
      qN_coprime.dvd_of_dvd_mul_right q_dvd_product
    simpa only [q, reduced, quotient] using q_dvd_numerator
  · intro q_dvd_numerator
    have q_dvd_numerator' : q ∣ reduced.num := by
      simpa only [q, reduced, quotient] using q_dvd_numerator
    have q_dvd_for_coprime := q_dvd_numerator'
    obtain ⟨carrier, numerator_eq⟩ := q_dvd_numerator'
    let Nprev : ℤ := carrier
    let D : ℤ := E * Nprev
    let N : ℤ := 9 * M * reduced.den
    have carrier_cast : (Nprev : ℚ) = (reduced.num : ℚ) / q := by
      dsimp only [Nprev]
      rw [numerator_eq]
      field_simp [q_ne]
      push_cast
      ring
    have Nprev_unit : HasDecimalShell (Nprev : ℚ) 0 0 := by
      rw [carrier_cast]
      exact ⟨by simpa using div_hasValue numerator_unit.1 q_unit.1,
        by simpa using div_hasValue numerator_unit.2 q_unit.2⟩
    have D_unit : HasDecimalShell (D : ℚ) 0 0 := by
      simpa only [D, Int.cast_mul, zero_add] using E_unit.mul Nprev_unit
    have N_unit : HasDecimalShell (N : ℚ) 0 0 := by
      simpa only [N, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, zero_add] using
        (nine_unit.mul M_unit).mul denominator_unit
    have q9_coprime : IsCoprime q (9 : ℤ) := by
      simpa only [q] using gapFactorDivisor_coprime_nine β_pos (r_dvd_q := dvd_rfl)
    have qM_coprime : IsCoprime q M := by
      simpa only [q, M] using gapFactor_coprime_marker β_pos
    have numerator_denominator_coprime :
        IsCoprime reduced.num (reduced.den : ℤ) :=
      Rat.isCoprime_num_den reduced
    have qDenominator_coprime : IsCoprime q (reduced.den : ℤ) :=
      IsCoprime.of_isCoprime_of_dvd_left numerator_denominator_coprime
        q_dvd_for_coprime
    have qN_coprime : IsCoprime q N := by
      dsimp only [N]
      exact (q9_coprime.mul_right qM_coprime).mul_right qDenominator_coprime
    refine ⟨N, D, Nprev, N_unit, D_unit, Nprev_unit, rfl, qN_coprime, ?_⟩
    unfold RepresentsPeeledCarrier
    dsimp only [N, D]
    simp only [Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
    rw [E_cast, M_cast]
    change ray.1 * (10 * DecimalSetterMatrix.marker β *
        (gap ((10 : ℚ) ^ β) * (Nprev : ℚ))) =
      ray.2 * (9 * DecimalSetterMatrix.marker β * (reduced.den : ℚ))
    have quotient_eq : ray.2 / ray.1 =
        10 * (reduced.num : ℚ) / reduced.den := by
      calc
        ray.2 / ray.1 = 10 * (ray.2 / ray.1 / 10) := by ring
        _ = 10 * ((reduced.num : ℚ) / reduced.den) := by rw [reduced_eq]
        _ = 10 * (reduced.num : ℚ) / reduced.den := by ring
    have cross_eq : ray.2 * (reduced.den : ℚ) =
        ray.1 * 10 * (reduced.num : ℚ) := by
      field_simp [ray_first_ne, denominator_ne] at quotient_eq
      exact quotient_eq
    have numerator_cast_eq : (reduced.num : ℚ) =
        (q : ℚ) * (Nprev : ℚ) := by
      rw [numerator_eq]
      simp only [Nprev, Int.cast_mul]
    have cross_clean : ray.2 * (reduced.den : ℚ) =
        ray.1 * 10 * (q : ℚ) * (Nprev : ℚ) := by
      rw [cross_eq, numerator_cast_eq]
      ring
    have gap_eq_q : gap ((10 : ℚ) ^ β) = 9 * (q : ℚ) := by
      rw [← E_cast, E_eq, Int.cast_mul]
      norm_num
    calc
      ray.1 * (10 * DecimalSetterMatrix.marker β *
          (gap ((10 : ℚ) ^ β) * (Nprev : ℚ))) =
          9 * DecimalSetterMatrix.marker β *
            (ray.1 * 10 * (q : ℚ) * (Nprev : ℚ)) := by
              rw [gap_eq_q]
              ring
      _ = 9 * DecimalSetterMatrix.marker β *
            (ray.2 * (reduced.den : ℚ)) := by rw [cross_clean]
      _ = ray.2 *
          (9 * DecimalSetterMatrix.marker β * (reduced.den : ℚ)) := by ring

/-- The intervening `R_c D_c` block in the uniform gap-contaminated parser tail. -/
def gapContaminatedNext : List NearyTile :=
  [.rule .c, .erase .c]

/-- The two-role `R_c R_c` root in the uniform gap-contaminated parser tail. -/
def gapContaminatedRoot : List NearyTile :=
  [.rule .c, .rule .c]

/-- A lawful two-block parser tail whose reduced quotient numerator avoids the primitive gap
factor at every deletion width `β≥3` and for every tag body. -/
def gapContaminatedTail : List (List NearyTile) :=
  [gapContaminatedNext, gapContaminatedRoot]

/-- The uniform gap-contaminated tail obeys the parser block law. -/
theorem gapContaminatedTail_blocksLaw :
    BlocksLaw gapContaminatedTail := by
  exact ⟨⟨[.rule .c], .c, rfl⟩, ⟨[.rule .c], .c, rfl⟩⟩

/-- Exact punctuated upper code of the two-role all-`c` root. -/
theorem gapContaminatedRoot_upperBoundaryCode_eq (β : Nat) :
    upperBoundaryCode β gapContaminatedRoot =
      55 * (10 : ℚ) ^ (β + 1) + DecimalSetterMatrix.marker β := by
  have spelling : spell (nearyUpper β) gapContaminatedRoot = [true, true] := rfl
  rw [upperBoundaryCode_eq, spelling]
  norm_num [code, digit, Nat.ofDigits, markerScale]

private theorem gapContaminatedRoot_sub_scaleMarker (β : Nat) :
    upperBoundaryCode β gapContaminatedRoot -
        100 * DecimalSetterMatrix.marker β =
      -11 * (2 * (10 : ℚ) ^ β - 7) := by
  have marker_relation := DecimalSetterMatrix.marker_relation β
  rw [gapContaminatedRoot_upperBoundaryCode_eq, pow_succ]
  linear_combination -11 * marker_relation

private theorem gap_tenPow_eq_nine_mul_gapFactor {β : Nat} :
    gap ((10 : ℚ) ^ β) = 9 * (2 * (10 : ℚ) ^ β - 7) := by
  rfl

/-- Closed homogeneous coordinates of the gap-contaminated parser tail. -/
theorem gapContaminatedTail_parsedRay_coordinates
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter) :
    let μ := DecimalSetterMatrix.marker β
    let G := lift ((10 : ℚ) ^ β)
    let P := upperBoundaryCode β gapContaminatedRoot
    let V := lowerBoundaryCode β body gapContaminatedNext
    let K := 9 * P ^ 2 - 11 * G * V
    parsedRay β body gapContaminatedTail = (K / (9 * μ ^ 2), 100 * P / μ) := by
  dsimp only
  have μ_ne := ne_of_gt (DecimalSetterMatrix.marker_pos β)
  have q_ne : (2 * (10 : ℚ) ^ β - 7) ≠ 0 := by
    have rho_ge : (10 : ℚ) ≤ 10 ^ β := by
      obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt β_pos)
      rw [pow_succ]
      have power_ge : (1 : ℚ) ≤ 10 ^ offset := one_le_pow₀ (by norm_num)
      nlinarith
    nlinarith
  apply Prod.ext
  · change (rayStep β body gapContaminatedNext
      (rootRay β gapContaminatedRoot)).1 = _
    simp only [rayStep, rootRay]
    have P_shift := gapContaminatedRoot_sub_scaleMarker β
    have E_eq := gap_tenPow_eq_nine_mul_gapFactor (β := β)
    have current_upper : upperBoundaryCode β gapContaminatedNext =
        upperBoundaryCode β gapContaminatedRoot := rfl
    have root_scale : upperScale β gapContaminatedRoot = 100 := by
      norm_num [upperScale, gapContaminatedRoot, spell, nearyUpper, tagCode]
    rw [root_scale]
    unfold boundaryTrace
    rw [current_upper, E_eq]
    field_simp [μ_ne, q_ne]
    linear_combination lift ((10 : ℚ) ^ β) *
      lowerBoundaryCode β body gapContaminatedNext * P_shift
  · change (rayStep β body gapContaminatedNext
      (rootRay β gapContaminatedRoot)).2 = _
    simp only [rayStep, rootRay]
    rw [show upperScale β gapContaminatedNext = 100 by
      norm_num [upperScale, gapContaminatedNext, spell, nearyUpper, tagCode]]
    ring

private theorem code_append_false_three_mod_thousand (stem : List Bool) :
    (code (stem ++ [false, false, false]) : ℤ) ≡ 777 [ZMOD 1000] := by
  rw [code_append]
  norm_num [code, digit, Nat.ofDigits]

private theorem code_append_true_false_false_mod_thousand (stem : List Bool) :
    (code (stem ++ [true, false, false]) : ℤ) ≡ 577 [ZMOD 1000] := by
  rw [code_append]
  norm_num [code, digit, Nat.ofDigits]

private theorem gapContaminatedRoot_upper_mod_thousand
    {β : Nat} (β_large : 3 ≤ β) :
    (code (spell (nearyUpper β) gapContaminatedRoot ++ nearyMarker β) : ℤ) ≡
      777 [ZMOD 1000] := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le β_large
  have suffix := code_append_false_three_mod_thousand
    (spell (nearyUpper (3 + offset)) gapContaminatedRoot ++
      true :: List.replicate offset false)
  simpa [nearyMarker, List.replicate_add, List.append_assoc,
    Nat.add_comm] using suffix

private theorem gapContaminatedNext_lower_mod_thousand
    (β : Nat) (body : List TagLetter) :
    (code (spell (nearyLower β body) gapContaminatedNext) : ℤ) ≡
      577 [ZMOD 1000] := by
  have suffix := code_append_true_false_false_mod_thousand
    ([true] ++ tagEncode β body)
  simpa [gapContaminatedNext, spell, nearyLower, List.append_assoc] using suffix

private theorem ten_pow_mod_thousand
    {β : Nat} (β_large : 3 ≤ β) :
    (10 : ℤ) ^ β ≡ 0 [ZMOD 1000] := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le β_large
  simpa [pow_add, Nat.add_comm] using
    (Int.ModEq.refl ((10 : ℤ) ^ offset)).mul
      (by norm_num : (10 : ℤ) ^ 3 ≡ 0 [ZMOD 1000])

private theorem decimalLift_tenPow_mod_thousand
    {β : Nat} (β_large : 3 ≤ β) :
    decimalLift ((10 : ℤ) ^ β) ≡ 993 [ZMOD 1000] := by
  have rho_zero := ten_pow_mod_thousand β_large
  simp only [decimalLift]
  calc
    502 * (10 : ℤ) ^ β - 7 ≡ 502 * 0 - 7 [ZMOD 1000] :=
      (Int.ModEq.refl 502).mul rho_zero |>.sub (Int.ModEq.refl 7)
    _ ≡ 993 [ZMOD 1000] := by norm_num

private theorem gapContaminatedDenominator_mod_thousand
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter) :
    let P : ℤ :=
      code (spell (nearyUpper β) gapContaminatedRoot ++ nearyMarker β)
    let G : ℤ := decimalLift ((10 : ℤ) ^ β)
    let V : ℤ := code (spell (nearyLower β body) gapContaminatedNext)
    9 * P ^ 2 - 11 * G * V ≡ 990 [ZMOD 1000] := by
  dsimp only
  have P_mod := gapContaminatedRoot_upper_mod_thousand β_large
  have G_mod := decimalLift_tenPow_mod_thousand β_large
  have V_mod := gapContaminatedNext_lower_mod_thousand β body
  calc
    9 * (code
          (spell (nearyUpper β) gapContaminatedRoot ++ nearyMarker β) : ℤ) ^ 2 -
        11 * decimalLift ((10 : ℤ) ^ β) *
          code (spell (nearyLower β body) gapContaminatedNext) ≡
      9 * 777 ^ 2 - 11 * 993 * 577 [ZMOD 1000] :=
        (Int.ModEq.refl 9).mul (P_mod.pow 2) |>.sub
          (((Int.ModEq.refl 11).mul G_mod).mul V_mod)
    _ ≡ 990 [ZMOD 1000] := by norm_num

private theorem intCast_hasDecimalShell_of_mod_nineNinety
    {value : ℤ} (value_mod : value ≡ 990 [ZMOD 1000]) :
    HasDecimalShell (value : ℚ) 1 1 := by
  rw [Int.modEq_iff_dvd] at value_mod
  obtain ⟨carry, carry_eq⟩ := value_mod
  have value_eq : value = 10 * (99 - 100 * carry) := by omega
  have unit_two : ¬(2 : ℤ) ∣ 99 - 100 * carry := by
    rintro ⟨quotient, quotient_eq⟩
    omega
  have unit_five : ¬(5 : ℤ) ∣ 99 - 100 * carry := by
    rintro ⟨quotient, quotient_eq⟩
    omega
  rw [value_eq, Int.cast_mul]
  exact ten_hasDecimalShell.mul
    ⟨intCast_isUnit_of_not_dvd unit_two, intCast_isUnit_of_not_dvd unit_five⟩

/-- The normalized quotient of the gap-contaminated tail is a fixed rational function of its
punctuated upper and lower codes. -/
theorem gapContaminatedTail_normalizedQuotient_formula
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter) :
    let μ := DecimalSetterMatrix.marker β
    let G := lift ((10 : ℚ) ^ β)
    let P := upperBoundaryCode β gapContaminatedRoot
    let V := lowerBoundaryCode β body gapContaminatedNext
    let K := 9 * P ^ 2 - 11 * G * V
    (parsedRay β body gapContaminatedTail).2 /
        (parsedRay β body gapContaminatedTail).1 / 10 =
      90 * μ * P / K := by
  dsimp only
  have β_pos : 0 < β := by omega
  rw [gapContaminatedTail_parsedRay_coordinates β_pos]
  have K_shell :
      HasDecimalShell
        (9 * upperBoundaryCode β gapContaminatedRoot ^ 2 -
          11 * lift ((10 : ℚ) ^ β) *
            lowerBoundaryCode β body gapContaminatedNext) 1 1 := by
    have shell := intCast_hasDecimalShell_of_mod_nineNinety
      (gapContaminatedDenominator_mod_thousand β_large body)
    norm_num [upperBoundaryCode, lowerBoundaryCode, lift, decimalLift,
      Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_pow] at shell ⊢
    exact shell
  have μ_ne := ne_of_gt (DecimalSetterMatrix.marker_pos β)
  field_simp [μ_ne, K_shell.1.1]
  ring

/-- For every `β≥3` and every tag body, the lawful gap-contaminated tail has decimal `(1,1)`
quotient shell. -/
theorem gapContaminatedTail_ratio_hasDecimalShell
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter) :
    HasDecimalShell
      ((parsedRay β body gapContaminatedTail).2 /
        (parsedRay β body gapContaminatedTail).1) 1 1 := by
  let M : ℤ := code (nearyMarker β)
  let P : ℤ :=
    code (spell (nearyUpper β) gapContaminatedRoot ++ nearyMarker β)
  let G : ℤ := decimalLift ((10 : ℤ) ^ β)
  let V : ℤ := code (spell (nearyLower β body) gapContaminatedNext)
  let K : ℤ := 9 * P ^ 2 - 11 * G * V
  have β_pos : 0 < β := by omega
  have nine_unit : HasDecimalShell (9 : ℚ) 0 0 :=
    ⟨intCast_isUnit_of_not_dvd (by norm_num),
      intCast_isUnit_of_not_dvd (by norm_num)⟩
  have ninety_shell : HasDecimalShell (90 : ℚ) 1 1 := by
    have shell := nine_unit.mul ten_hasDecimalShell
    norm_num at shell ⊢
    exact shell
  have marker_unit : HasDecimalShell (M : ℚ) 0 0 := by
    simpa only [M, DecimalSetterMatrix.marker, Int.cast_natCast] using
      marker_hasDecimalShell β_pos
  have upper_unit : HasDecimalShell (P : ℚ) 0 0 := by
    simpa only [P, upperBoundaryCode, Int.cast_natCast] using
      upperBoundaryCode_decimalUnit β_pos gapContaminatedRoot
  have numerator_shell : HasDecimalShell ((90 * M * P : ℤ) : ℚ) 1 1 := by
    simpa only [Int.cast_mul, Int.cast_ofNat, add_zero, zero_add] using
      (ninety_shell.mul marker_unit).mul upper_unit
  have denominator_shell : HasDecimalShell (K : ℚ) 1 1 :=
    intCast_hasDecimalShell_of_mod_nineNinety (by
      simpa only [K, P, G, V] using
        gapContaminatedDenominator_mod_thousand β_large body)
  have normalized_shell :
      HasDecimalShell (((90 * M * P : ℤ) : ℚ) / K) 0 0 := by
    constructor
    · have shell := div_hasValue numerator_shell.1 denominator_shell.1
      norm_num at shell
      norm_num [Int.cast_mul] at shell ⊢
      exact shell
    · have shell := div_hasValue numerator_shell.2 denominator_shell.2
      norm_num at shell
      norm_num [Int.cast_mul] at shell ⊢
      exact shell
  have formula := gapContaminatedTail_normalizedQuotient_formula β_large body
  have normalized_eq :
      (parsedRay β body gapContaminatedTail).2 /
          (parsedRay β body gapContaminatedTail).1 / 10 =
        (((90 * M * P : ℤ) : ℚ) / K) := by
    norm_num [M, P, G, V, K, DecimalSetterMatrix.marker,
      upperBoundaryCode, lowerBoundaryCode, lift, decimalLift,
      Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_pow] at formula ⊢
    exact formula
  have ratio_eq :
      (parsedRay β body gapContaminatedTail).2 /
          (parsedRay β body gapContaminatedTail).1 =
        10 * (((90 * M * P : ℤ) : ℚ) / K) := by
    have scaled := (div_eq_iff (by norm_num : (10 : ℚ) ≠ 0)).mp normalized_eq
    simpa only [mul_comm] using scaled
  rw [ratio_eq]
  have shell := ten_hasDecimalShell.mul normalized_shell
  norm_num at shell ⊢
  exact shell

private theorem gapContaminatedMarker_integer_relation (β : Nat) :
    9 * (code (nearyMarker β) : ℤ) + 7 = 52 * (10 : ℤ) ^ β := by
  have identity := DecimalSetterChamber.markerWord_code_identity β
  simpa only [DecimalSetterChamber.markerWord, nearyMarker] using
    (by exact_mod_cast identity)

private theorem gapFactor_coprime_17500
    {β : Nat} (β_pos : 0 < β) :
    IsCoprime (gapFactor β) (17500 : ℤ) := by
  let q : ℤ := gapFactor β
  let M : ℤ := code (nearyMarker β)
  have q9 : IsCoprime q (9 : ℤ) := by
    simpa only [q] using
      gapFactorDivisor_coprime_nine β_pos (r_dvd_q := dvd_rfl)
  have qM : IsCoprime q M := by
    simpa only [q, M] using gapFactor_coprime_marker β_pos
  have marker_relation : 9 * M = 26 * q + 175 := by
    have identity := gapContaminatedMarker_integer_relation β
    dsimp only [q, gapFactor]
    linear_combination identity
  have q175 : IsCoprime q (175 : ℤ) := by
    have q9M : IsCoprime q (9 * M) := q9.mul_right qM
    rw [marker_relation] at q9M
    have shifted := q9M.add_mul_right_right (-26 : ℤ)
    norm_num at shifted ⊢
    simpa [add_comm] using shifted
  have q10 : IsCoprime q (10 : ℤ) := by
    simpa only [q] using gapFactor_coprime_ten β_pos
  have q100 : IsCoprime q (100 : ℤ) := by
    simpa using q10.pow_right (n := 2)
  simpa using q175.mul_right q100

private theorem gapFactor_coprime_gapContaminatedUpper
    {β : Nat} (β_pos : 0 < β) :
    IsCoprime (gapFactor β)
      (code
        (spell (nearyUpper β) gapContaminatedRoot ++ nearyMarker β) : ℤ) := by
  let q : ℤ := gapFactor β
  let P : ℤ :=
    code (spell (nearyUpper β) gapContaminatedRoot ++ nearyMarker β)
  have q17500 : IsCoprime q (17500 : ℤ) := by
    simpa only [q] using gapFactor_coprime_17500 β_pos
  have marker_relation := gapContaminatedMarker_integer_relation β
  have P_eq : P = 55 * (10 : ℤ) ^ (β + 1) + code (nearyMarker β) := by
    dsimp only [P]
    have spelling : spell (nearyUpper β) gapContaminatedRoot = [true, true] := rfl
    rw [spelling, code_append]
    norm_num [code, digit, Nat.ofDigits, nearyMarker]
  have P_relation : 9 * P = 2501 * q + 17500 := by
    rw [P_eq]
    dsimp only [q, gapFactor]
    rw [pow_succ]
    linear_combination marker_relation
  have q9P : IsCoprime q (9 * P) := by
    rw [P_relation]
    have shifted := q17500.add_mul_right_right (2501 : ℤ)
    simpa [add_comm] using shifted
  exact IsCoprime.of_isCoprime_of_dvd_right q9P ⟨9, by ring⟩

/-- The primitive gap factor is coprime to the unreduced numerator in the uniform quotient
formula. -/
theorem gapContaminatedTail_rawNumerator_coprime_gapFactor
    {β : Nat} (β_pos : 0 < β) :
    IsCoprime (gapFactor β)
      (90 * (code (nearyMarker β) : ℤ) *
        code
          (spell (nearyUpper β) gapContaminatedRoot ++ nearyMarker β)) := by
  have q_ten := gapFactor_coprime_ten β_pos
  have q_nine := gapFactorDivisor_coprime_nine β_pos
    (show gapFactor β ∣ gapFactor β from dvd_refl _)
  have q_ninety : IsCoprime (gapFactor β) (90 : ℤ) := by
    simpa using q_ten.mul_right q_nine
  exact (q_ninety.mul_right (gapFactor_coprime_marker β_pos)).mul_right
    (gapFactor_coprime_gapContaminatedUpper β_pos)

/-- The reduced normalized quotient numerator of the uniform lawful tail is coprime to the
primitive gap factor for every `β≥3` and every tag body. -/
theorem gapContaminatedTail_reducedNumerator_coprime_gapFactor
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter) :
    IsCoprime (gapFactor β)
      (((parsedRay β body gapContaminatedTail).2 /
        (parsedRay β body gapContaminatedTail).1 / 10).num) := by
  let M : ℤ := code (nearyMarker β)
  let P : ℤ :=
    code (spell (nearyUpper β) gapContaminatedRoot ++ nearyMarker β)
  let G : ℤ := decimalLift ((10 : ℤ) ^ β)
  let V : ℤ := code (spell (nearyLower β body) gapContaminatedNext)
  let numerator : ℤ := 90 * M * P
  let denominator : ℤ := 9 * P ^ 2 - 11 * G * V
  let reduced := (parsedRay β body gapContaminatedTail).2 /
    (parsedRay β body gapContaminatedTail).1 / 10
  have denominator_shell : HasDecimalShell (denominator : ℚ) 1 1 :=
    intCast_hasDecimalShell_of_mod_nineNinety (by
      simpa only [denominator, P, G, V] using
        gapContaminatedDenominator_mod_thousand β_large body)
  have denominator_ne : denominator ≠ 0 := by
    exact_mod_cast denominator_shell.1.1
  have formula := gapContaminatedTail_normalizedQuotient_formula β_large body
  have reduced_eq : reduced = (numerator : ℚ) / denominator := by
    norm_num [reduced, numerator, denominator, M, P, G, V,
      DecimalSetterMatrix.marker, upperBoundaryCode, lowerBoundaryCode,
      lift, decimalLift, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
      Int.cast_pow] at formula ⊢
    exact formula
  obtain ⟨common, numerator_eq, _⟩ :=
    Rat.exists_eq_mul_div_num_and_eq_mul_div_den numerator denominator_ne
  rw [← reduced_eq] at numerator_eq
  have reduced_dvd : reduced.num ∣ numerator := by
    refine ⟨common, ?_⟩
    rw [numerator_eq]
    ring
  have raw_coprime :=
    gapContaminatedTail_rawNumerator_coprime_gapFactor (by omega : 0 < β)
  exact IsCoprime.of_isCoprime_of_dvd_right
    (by simpa only [numerator, M, P] using raw_coprime) reduced_dvd

/-- The lawful gap-contaminated tail refutes global gap-clean ancestry. For every `β≥3` and
every tag body, its quotient has the required decimal shell, but no integral decimal-unit
denominator descent can have numerator coprime to the primitive gap factor. -/
theorem gapContaminatedTail_no_gapCleanIntegralCarrier
    {β : Nat} (β_large : 3 ≤ β) (body : List TagLetter) :
    ¬∃ N D Nprev : ℤ,
      HasDecimalShell (N : ℚ) 0 0 ∧
        HasDecimalShell (D : ℚ) 0 0 ∧
          HasDecimalShell (Nprev : ℚ) 0 0 ∧
            D = decimalGap ((10 : ℤ) ^ β) * Nprev ∧
              IsCoprime (gapFactor β) N ∧
                RepresentsPeeledCarrier β
                  (parsedRay β body gapContaminatedTail) N D := by
  intro clean_carrier
  have β_pos : 0 < β := by omega
  have numerator_dvd :
      gapFactor β ∣
        (((parsedRay β body gapContaminatedTail).2 /
          (parsedRay β body gapContaminatedTail).1) / 10).num :=
    (exists_gapCleanIntegralPeeledCarrier_iff_gapFactor_dvd_reducedNumerator
      β_pos (parsedRay β body gapContaminatedTail)
        (gapContaminatedTail_ratio_hasDecimalShell β_large body)).mp clean_carrier
  have numerator_coprime :=
    gapContaminatedTail_reducedNumerator_coprime_gapFactor β_large body
  have gap_unit := numerator_coprime.isUnit_of_dvd numerator_dvd
  have gap_gt_one : (1 : ℤ) < gapFactor β := by
    obtain ⟨offset, β_eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt β_pos)
    rw [β_eq, gapFactor, pow_succ]
    have power_pos : (0 : ℤ) < 10 ^ offset := pow_pos (by norm_num) offset
    nlinarith
  rw [Int.isUnit_iff] at gap_unit
  omega

end MatrixMortality.DecimalSetterBridgeRay
