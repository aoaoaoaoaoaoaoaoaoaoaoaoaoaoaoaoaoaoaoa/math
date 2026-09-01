import MatrixMortality.DecimalSetterPhase

/-!
# Decimal setter rule resonances

The phase-toggle cut becomes sharp only after the all-`D_c` comparison residual is assigned
its exact five-adic depth.  A regular raw head has depth `min n (s+1)`, where `s` is its final
run of sevens; the exceptional raw head has depth `min n (2β-1)`.  These exact depths turn a
prospective rule-bearing pole into a small equality grammar rather than a search over words.
-/

namespace MatrixMortality.DecimalSetterRuleResonance

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterAncestry
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterChamber
open MatrixMortality.DecimalSetterDepth
open MatrixMortality.DecimalSetterPhase
open MatrixMortality.PadicValuation

private instance factPrimeFive : Fact (Nat.Prime 5) :=
  ⟨by norm_num⟩

private theorem fivePower_dvd_tenPower {small large : Nat} (bound : small ≤ large) :
    (5 : ℤ) ^ small ∣ 10 ^ large :=
  (pow_dvd_pow (5 : ℤ) bound).trans
    (pow_dvd_pow_of_dvd (by norm_num : (5 : ℤ) ∣ 10) large)

private theorem intCast_hasValue_five_of_exact_divisibility
    {value : ℤ} {depth : Nat}
    (depth_dvd : (5 : ℤ) ^ depth ∣ value)
    (next_not_dvd : ¬(5 : ℤ) ^ (depth + 1) ∣ value) :
    HasValue 5 (value : ℚ) depth := by
  have value_ne : value ≠ 0 := by
    intro value_zero
    exact next_not_dvd (value_zero ▸ dvd_zero ((5 : ℤ) ^ (depth + 1)))
  have depth_le : depth ≤ padicValInt 5 value :=
    ((padicValInt_dvd_iff depth value).mp depth_dvd).resolve_left value_ne
  have valuation_lt : padicValInt 5 value < depth + 1 := by
    by_contra valuation_not_lt
    have next_bound : depth + 1 ≤ padicValInt 5 value := by omega
    exact next_not_dvd ((padicValInt_dvd_iff (depth + 1) value).mpr (Or.inr next_bound))
  have valuation_eq : padicValInt 5 value = depth := by omega
  refine ⟨by exact_mod_cast value_ne, ?_⟩
  rw [padicValRat.of_int, valuation_eq]

private theorem fivePower_dvd_of_scaled_eightyOne
    {value : ℤ} {depth : Nat}
    (scaled_dvd : (5 : ℤ) ^ depth ∣ 81 * value) :
    (5 : ℤ) ^ depth ∣ value := by
  have coprime : IsCoprime ((5 : ℤ) ^ depth) 81 :=
    (by norm_num : IsCoprime (5 : ℤ) 81).pow_left
  exact coprime.dvd_of_dvd_mul_left scaled_dvd

private theorem fivePower_dvd_of_scaled_fortyFive
    {value : ℤ} {depth : Nat}
    (scaled_dvd : (5 : ℤ) ^ (depth + 1) ∣ 45 * value) :
    (5 : ℤ) ^ depth ∣ value := by
  rw [show (45 : ℤ) = 5 * 9 by norm_num, pow_succ] at scaled_dvd
  have reduced : (5 : ℤ) ^ depth ∣ 9 * value := by
    have rearranged : (5 : ℤ) * 5 ^ depth ∣ 5 * (9 * value) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using scaled_dvd
    exact (mul_dvd_mul_iff_left (show (5 : ℤ) ≠ 0 by norm_num)).mp rearranged
  have coprime : IsCoprime ((5 : ℤ) ^ depth) 9 :=
    (by norm_num : IsCoprime (5 : ℤ) 9).pow_left
  exact coprime.dvd_of_dvd_mul_left reduced

/-- A regular two-`c` raw head followed by an all-`D_c` word of width `n` has exact
five-adic residual depth `min n (s+1)`, where `s` is the nonexceptional final-seven width of
the head. -/
theorem allCDeletion_regularRawHead_hasValue_five
    {β s n : Nat} {H μ E G P V T R : ℤ}
    (s_positive : 1 ≤ s) (suffix_below : s + 2 ≤ β) (n_positive : 1 ≤ n)
    (head_eq : 9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ s - 7)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (upper_eq : 9 * P = 50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7)
    (lower_eq : 9 * V = 7 * 10 ^ n - 7)
    (trace_eq : T = E * P + G * V)
    (residual_eq : R = H * T - 10 * μ * G * V) :
    HasValue 5 (R : ℚ) ((min n (s + 1) : Nat) : ℤ) := by
  let ρ : ℤ := 10 ^ β
  let K : ℤ := 245 * 10 ^ (β + 2 - s) + 98
  let A : ℤ :=
    8100 * H * ρ ^ 2 + 3276 * H * ρ - 441 * H -
      1827280 * ρ ^ 2 + 271460 * ρ - 3430
  let B : ℤ :=
    324 * H * ρ - 33894 * H + 1827280 * ρ - 271460
  have head_factor := rawHead_linear_factor (show s ≤ β + 2 by omega) head_eq
  have decomposition := allCDeletion_residual_decomposition
    (ρ := ρ) (q := (10 : ℤ) ^ n)
    mu_eq gap_eq lift_eq upper_eq lower_eq trace_eq residual_eq
  have decomposition' :
      81 * R = 10 ^ (s + 1) * K + 10 ^ n * A + 10 ^ β * B := by
    rw [head_factor] at decomposition
    dsimp [ρ, K, A, B]
    rw [pow_two, ← pow_add] at decomposition
    simpa [pow_succ, pow_add, mul_assoc, mul_left_comm, mul_comm] using decomposition
  by_cases width_below : n ≤ s + 1
  · have scaled_dvd : (5 : ℤ) ^ n ∣ 81 * R := by
      rw [decomposition']
      exact dvd_add
        (dvd_add
          (dvd_mul_of_dvd_left (fivePower_dvd_tenPower width_below) K)
          (dvd_mul_of_dvd_left (fivePower_dvd_tenPower le_rfl) A))
        (dvd_mul_of_dvd_left (fivePower_dvd_tenPower (by omega)) B)
    have depth_dvd : (5 : ℤ) ^ n ∣ R :=
      fivePower_dvd_of_scaled_eightyOne scaled_dvd
    have next_not_dvd : ¬(5 : ℤ) ^ (n + 1) ∣ R :=
      allCDeletion_regularRawHead_not_fiveAboveWidth s_positive suffix_below n_positive
        head_eq mu_eq gap_eq lift_eq upper_eq lower_eq trace_eq residual_eq
    simpa [min_eq_left width_below] using
      intCast_hasValue_five_of_exact_divisibility depth_dvd next_not_dvd
  · have head_below : s + 1 < n := by omega
    have K_five_unit : ¬(5 : ℤ) ∣ K := by
      intro K_dvd
      have first_five : (5 : ℤ) ∣ 245 * 10 ^ (β + 2 - s) :=
        dvd_mul_of_dvd_left (by norm_num) _
      have ninetyEight_five : (5 : ℤ) ∣ 98 := by
        dsimp only [K] at K_dvd
        simpa using dvd_sub K_dvd first_five
      norm_num at ninetyEight_five
    have scaled_dvd : (5 : ℤ) ^ (s + 1) ∣ 81 * R := by
      rw [decomposition']
      exact dvd_add
        (dvd_add
          (dvd_mul_of_dvd_left (fivePower_dvd_tenPower le_rfl) K)
          (dvd_mul_of_dvd_left (fivePower_dvd_tenPower (by omega)) A))
        (dvd_mul_of_dvd_left (fivePower_dvd_tenPower (by omega)) B)
    have depth_dvd : (5 : ℤ) ^ (s + 1) ∣ R :=
      fivePower_dvd_of_scaled_eightyOne scaled_dvd
    have next_not_dvd : ¬(5 : ℤ) ^ (s + 2) ∣ R := by
      intro next_dvd
      have scaled_next : (5 : ℤ) ^ (s + 2) ∣ 81 * R :=
        dvd_mul_of_dvd_right next_dvd 81
      have second_dvd : (5 : ℤ) ^ (s + 2) ∣ 10 ^ n * A :=
        dvd_mul_of_dvd_left (fivePower_dvd_tenPower (by omega)) A
      have third_dvd : (5 : ℤ) ^ (s + 2) ∣ 10 ^ β * B :=
        dvd_mul_of_dvd_left (fivePower_dvd_tenPower suffix_below) B
      rw [decomposition'] at scaled_next
      have first_dvd : (5 : ℤ) ^ (s + 2) ∣ 10 ^ (s + 1) * K := by
        have isolated := dvd_sub (dvd_sub scaled_next third_dvd) second_dvd
        rw [show 10 ^ (s + 1) * K + 10 ^ n * A + 10 ^ β * B -
          10 ^ β * B - 10 ^ n * A = 10 ^ (s + 1) * K by ring] at isolated
        exact isolated
      have ten_expansion : (10 : ℤ) ^ (s + 1) =
          5 ^ (s + 1) * 2 ^ (s + 1) := by
        rw [show (10 : ℤ) = 5 * 2 by norm_num, mul_pow]
      rw [ten_expansion, pow_succ, mul_assoc] at first_dvd
      have rearranged : (5 : ℤ) ^ (s + 1) * 5 ∣
          5 ^ (s + 1) * (2 ^ (s + 1) * K) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using first_dvd
      have power_ne : (5 : ℤ) ^ (s + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
      have five_scaled : (5 : ℤ) ∣ 2 ^ (s + 1) * K :=
        (mul_dvd_mul_iff_left power_ne).mp rearranged
      have coprime : IsCoprime (5 : ℤ) (2 ^ (s + 1)) :=
        (by norm_num : IsCoprime (5 : ℤ) 2).pow_right
      exact K_five_unit (coprime.dvd_of_dvd_mul_left five_scaled)
    simpa [min_eq_right (Nat.le_of_lt head_below)] using
      intCast_hasValue_five_of_exact_divisibility depth_dvd next_not_dvd

/-- The exceptional two-`c` raw head followed by an all-`D_c` word of width `n` has exact
five-adic residual depth `min n (2β-1)`. -/
theorem allCDeletion_exceptionalRawHead_hasValue_five
    {β n : Nat} {H μ E G P V T R : ℤ}
    (β_large : 2 ≤ β)
    (head_eq : 9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ (β - 1) - 7)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (upper_eq : 9 * P = 50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7)
    (lower_eq : 9 * V = 7 * 10 ^ n - 7)
    (trace_eq : T = E * P + G * V)
    (residual_eq : R = H * T - 10 * μ * G * V) :
    HasValue 5 (R : ℚ) ((min n (2 * β - 1) : Nat) : ℤ) := by
  obtain ⟨C, B, decomposition, _, B_sub_one_dvd⟩ :=
    allCDeletion_firstRawHead_residueNormalForm β_large head_eq mu_eq gap_eq lift_eq
      upper_eq lower_eq trace_eq residual_eq
  have B_five_unit : ¬(5 : ℤ) ∣ B := by
    intro B_dvd
    have one_dvd : (5 : ℤ) ∣ 1 := by
      simpa using dvd_sub B_dvd B_sub_one_dvd
    norm_num at one_dvd
  by_cases width_below : n ≤ 2 * β - 1
  · have scaled_dvd : (5 : ℤ) ^ (n + 1) ∣ 45 * R := by
      rw [decomposition]
      have base : (5 : ℤ) ^ n ∣ 10 ^ n := fivePower_dvd_tenPower le_rfl
      have scaled := mul_dvd_mul base (dvd_refl (5 : ℤ))
      have first_dvd : (5 : ℤ) ^ (n + 1) ∣ 10 ^ n * (5 * C) := by
        simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using scaled.mul_right C
      have second_dvd : (5 : ℤ) ^ (n + 1) ∣ 10 ^ (2 * β) * B :=
        dvd_mul_of_dvd_left (fivePower_dvd_tenPower (by omega)) B
      exact dvd_add first_dvd second_dvd
    have depth_dvd : (5 : ℤ) ^ n ∣ R :=
      fivePower_dvd_of_scaled_fortyFive scaled_dvd
    have next_not_dvd : ¬(5 : ℤ) ^ (n + 1) ∣ R :=
      allCDeletion_firstRawHead_not_fiveAboveWidth β_large head_eq mu_eq gap_eq lift_eq
        upper_eq lower_eq trace_eq residual_eq
    simpa [min_eq_left width_below] using
      intCast_hasValue_five_of_exact_divisibility depth_dvd next_not_dvd
  · have head_below : 2 * β - 1 < n := by omega
    have scaled_dvd : (5 : ℤ) ^ (2 * β) ∣ 45 * R := by
      rw [decomposition]
      have base : (5 : ℤ) ^ (2 * β - 1) ∣ 10 ^ n :=
        fivePower_dvd_tenPower (by omega)
      have scaled := mul_dvd_mul base (dvd_refl (5 : ℤ))
      have first_dvd : (5 : ℤ) ^ (2 * β) ∣ 10 ^ n * (5 * C) := by
        rw [show 2 * β = (2 * β - 1) + 1 by omega, pow_succ]
        simpa only [mul_assoc] using scaled.mul_right C
      have second_dvd : (5 : ℤ) ^ (2 * β) ∣ 10 ^ (2 * β) * B :=
        dvd_mul_of_dvd_left (fivePower_dvd_tenPower le_rfl) B
      exact dvd_add first_dvd second_dvd
    have depth_dvd : (5 : ℤ) ^ (2 * β - 1) ∣ R := by
      apply fivePower_dvd_of_scaled_fortyFive
      simpa [show (2 * β - 1) + 1 = 2 * β by omega] using scaled_dvd
    have next_not_dvd : ¬(5 : ℤ) ^ (2 * β) ∣ R := by
      intro next_dvd
      have scaled_next : (5 : ℤ) ^ (2 * β + 1) ∣ 45 * R := by
        rw [show (45 : ℤ) = 5 * 9 by norm_num, pow_succ]
        have raw := mul_dvd_mul (dvd_refl (5 : ℤ)) next_dvd
        simpa [mul_assoc, mul_left_comm, mul_comm] using raw.mul_right 9
      have first_dvd : (5 : ℤ) ^ (2 * β + 1) ∣ 10 ^ n * (5 * C) := by
        have base : (5 : ℤ) ^ (2 * β) ∣ 10 ^ n :=
          fivePower_dvd_tenPower (by omega)
        have scaled := mul_dvd_mul base (dvd_refl (5 : ℤ))
        simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using scaled.mul_right C
      rw [decomposition] at scaled_next
      have second_dvd : (5 : ℤ) ^ (2 * β + 1) ∣ 10 ^ (2 * β) * B := by
        have isolated := dvd_sub scaled_next first_dvd
        simpa using isolated
      have ten_expansion : (10 : ℤ) ^ (2 * β) =
          5 ^ (2 * β) * 2 ^ (2 * β) := by
        rw [show (10 : ℤ) = 5 * 2 by norm_num, mul_pow]
      rw [ten_expansion, pow_succ, mul_assoc] at second_dvd
      have rearranged : (5 : ℤ) ^ (2 * β) * 5 ∣
          5 ^ (2 * β) * (2 ^ (2 * β) * B) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using second_dvd
      have power_ne : (5 : ℤ) ^ (2 * β) ≠ 0 := pow_ne_zero _ (by norm_num)
      have five_scaled : (5 : ℤ) ∣ 2 ^ (2 * β) * B :=
        (mul_dvd_mul_iff_left power_ne).mp rearranged
      have coprime : IsCoprime (5 : ℤ) (2 ^ (2 * β)) :=
        (by norm_num : IsCoprime (5 : ℤ) 2).pow_right
      exact B_five_unit (coprime.dvd_of_dvd_mul_left five_scaled)
    have exponent_eq : 2 * β - 1 + 1 = 2 * β := by omega
    have exact_value : HasValue 5 (R : ℚ) (((2 * β - 1 : Nat) : ℤ)) :=
      intCast_hasValue_five_of_exact_divisibility depth_dvd
        (by simpa only [exponent_eq] using next_not_dvd)
    simpa [min_eq_right (Nat.le_of_lt head_below)] using exact_value

/-- Every lawful two-`c` raw head exposes an exact all-`D_c` five-depth frontier.  Regular
heads stop at `min n (s+1)`; the unique exceptional head stops at `min n (2β-1)`. -/
theorem allCDeletion_peeledDoubleCHead_hasValue_five
    {β n : Nat} (headTail : List TagLetter) {μ E G P V T R : ℤ}
    (β_large : 2 ≤ β) (n_positive : 1 ≤ n)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: headTail)) : ℚ) 0 0)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (upper_eq : 9 * P = 50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7)
    (lower_eq : 9 * V = 7 * 10 ^ n - 7)
    (trace_eq : T = E * P + G * V)
    (residual_eq :
      R = (code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) * T -
        10 * μ * G * V) :
    ∃ suffix, 1 ≤ suffix ∧ suffix ≤ β - 1 ∧
      peeledHeadWord β (.c :: .c :: headTail) =
        List.replicate (β + 2 - suffix) true ++ List.replicate suffix false ∧
      ((suffix + 2 ≤ β ∧
          HasValue 5 (R : ℚ) ((min n (suffix + 1) : Nat) : ℤ)) ∨
        (suffix = β - 1 ∧
          HasValue 5 (R : ℚ) ((min n (2 * β - 1) : Nat) : ℤ))) := by
  obtain ⟨suffix, suffix_positive, suffix_le, head_shape, head_eq⟩ :=
    peeledDoubleCHead_unit_shape headTail (by omega) head_unit
  refine ⟨suffix, suffix_positive, suffix_le, head_shape, ?_⟩
  rcases lt_or_eq_of_le suffix_le with suffix_regular | suffix_exceptional
  · left
    refine ⟨by omega, ?_⟩
    exact allCDeletion_regularRawHead_hasValue_five suffix_positive (by omega) n_positive
      head_eq mu_eq gap_eq lift_eq upper_eq lower_eq trace_eq residual_eq
  · right
    refine ⟨suffix_exceptional, ?_⟩
    rw [suffix_exceptional] at head_eq
    exact allCDeletion_exceptionalRawHead_hasValue_five β_large head_eq mu_eq gap_eq lift_eq
      upper_eq lower_eq trace_eq residual_eq

/-- Replacing the rightmost `b` tag of an all-erasure comparison word by `c`, together with
every earlier `b`, changes the raw residual at exact five-depth `tailWidth+β+2`.  Earlier
markers affect only a five-adic unit coefficient. -/
theorem rightmostB_allEraseResidual_sub_allC_hasValue_five
    {β tailWidth : Nat} (body headTail front : List TagLetter) {μ E G : ℤ}
    (β_large : 2 ≤ β)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: headTail)) : ℚ) 0 0)
    (gap_eq : E = 18 * 10 ^ β - 63) :
    let n := front.length + tailWidth + 1
    let H : ℤ := code (peeledHeadWord β (.c :: .c :: headTail))
    let V : ℤ := allEraseLowerCode β body n
    let P : ℤ := code (punctuatedUpper β
      (front ++ .b :: List.replicate tailWidth .c))
    let PAll : ℤ := code (punctuatedUpper β (List.replicate n .c))
    let R : ℤ := H * (E * P + G * V) - 10 * μ * G * V
    let RAll : ℤ := H * (E * PAll + G * V) - 10 * μ * G * V
    HasValue 5 (((R - RAll : ℤ) : ℚ)) (tailWidth + β + 2) := by
  dsimp only
  let D := rightmostBUpperCoefficient β front
  have upper_difference :
      (code (punctuatedUpper β
          (front ++ .b :: List.replicate tailWidth .c)) : ℤ) -
        code (punctuatedUpper β
          (List.replicate (front.length + tailWidth + 1) .c)) =
        D * 10 ^ (tailWidth + β + 2) := by
    simpa only [D] using rightmostB_punctuatedUpper_code_sub_eq β front tailWidth
  have residual_difference :
      (code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) *
            (E * code (punctuatedUpper β
                (front ++ .b :: List.replicate tailWidth .c)) +
              G * allEraseLowerCode β body (front.length + tailWidth + 1)) -
          10 * μ * G * allEraseLowerCode β body (front.length + tailWidth + 1) -
        ((code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) *
            (E * code (punctuatedUpper β
                (List.replicate (front.length + tailWidth + 1) .c)) +
              G * allEraseLowerCode β body (front.length + tailWidth + 1)) -
          10 * μ * G * allEraseLowerCode β body (front.length + tailWidth + 1)) =
        (code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) * E * D *
          10 ^ (tailWidth + β + 2) := by
    linear_combination
      (code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) * E * upper_difference
  have D_sub_two_dvd : (5 : ℤ) ∣ D - 2 := by
    simpa only [D] using rightmostBUpperCoefficient_sub_two_dvd_five (by omega) front
  have D_unit : HasValue 5 (D : ℚ) 0 := by
    apply intCast_isUnit_of_not_dvd
    intro D_dvd
    have two_dvd : (5 : ℤ) ∣ 2 := by
      simpa using dvd_sub D_dvd D_sub_two_dvd
    norm_num at two_dvd
  have E_sub_two_dvd : (5 : ℤ) ∣ E - 2 := by
    have ten_dvd : (5 : ℤ) ∣ 10 ^ β :=
      fivePower_dvd_tenPower (small := 1) (large := β) (by omega)
    rw [gap_eq]
    have first_dvd : (5 : ℤ) ∣ 18 * 10 ^ β := ten_dvd.mul_left 18
    obtain ⟨quotient, quotient_eq⟩ := first_dvd
    refine ⟨quotient - 13, ?_⟩
    rw [quotient_eq]
    ring
  have E_unit : HasValue 5 (E : ℚ) 0 := by
    apply intCast_isUnit_of_not_dvd
    intro E_dvd
    have two_dvd : (5 : ℤ) ∣ 2 := by
      simpa using dvd_sub E_dvd E_sub_two_dvd
    norm_num at two_dvd
  have scale_value := (ten_hasDecimalShell.pow (tailWidth + β + 2)).2
  have product_value :=
    mul_hasValue (mul_hasValue (mul_hasValue head_unit.2 E_unit) D_unit) scale_value
  rw [residual_difference]
  push_cast
  simpa [add_assoc] using product_value

/-- A sum cannot lie strictly deeper than one summand unless the two input depths resonate. -/
theorem twoTerm_deep_forces_depth_resonance
    {left right : ℚ} {leftDepth rightDepth targetDepth : ℤ}
    (left_value : HasValue 5 left leftDepth)
    (right_value : HasValue 5 right rightDepth)
    (sum_value : HasValue 5 (left + right) targetDepth)
    (right_shallow : rightDepth < targetDepth) :
    leftDepth = rightDepth := by
  by_contra depth_ne
  rcases lt_or_gt_of_ne depth_ne with left_right | right_left
  · have total_value := add_hasValue_left left_value right_value left_right
    have depth_eq : leftDepth = targetDepth := total_value.2.symm.trans sum_value.2
    omega
  · have total_value := add_hasValue_right left_value right_value right_left
    have depth_eq : rightDepth = targetDepth := total_value.2.symm.trans sum_value.2
    omega

/-- Three nonzero summands cannot acquire a target valuation strictly deeper than one of them
unless at least two input depths resonate. -/
theorem threeTerm_deep_forces_depth_resonance
    {left middle right : ℚ} {leftDepth middleDepth rightDepth targetDepth : ℤ}
    (left_value : HasValue 5 left leftDepth)
    (middle_value : HasValue 5 middle middleDepth)
    (right_value : HasValue 5 right rightDepth)
    (sum_value : HasValue 5 (left + middle + right) targetDepth)
    (right_shallow : rightDepth < targetDepth) :
    leftDepth = middleDepth ∨ leftDepth = rightDepth ∨ middleDepth = rightDepth := by
  by_contra no_resonance
  push Not at no_resonance
  obtain ⟨left_middle_ne, left_right_ne, middle_right_ne⟩ := no_resonance
  rcases lt_or_gt_of_ne left_middle_ne with left_middle | middle_left
  · have left_middle_value := add_hasValue_left left_value middle_value left_middle
    rcases lt_or_gt_of_ne left_right_ne with left_right | right_left
    · have total_value := add_hasValue_left left_middle_value right_value left_right
      have depth_eq : leftDepth = targetDepth := total_value.2.symm.trans sum_value.2
      omega
    · have total_value := add_hasValue_right left_middle_value right_value right_left
      have depth_eq : rightDepth = targetDepth := total_value.2.symm.trans sum_value.2
      omega
  · have middle_left_value := add_hasValue_right left_value middle_value middle_left
    rcases lt_or_gt_of_ne middle_right_ne with middle_right | right_middle
    · have total_value := add_hasValue_left middle_left_value right_value middle_right
      have depth_eq : middleDepth = targetDepth := total_value.2.symm.trans sum_value.2
      omega
    · have total_value := add_hasValue_right middle_left_value right_value right_middle
      have depth_eq : rightDepth = targetDepth := total_value.2.symm.trans sum_value.2
      omega

/-- The resonant pair forced by a deep three-term sum occurs at the minimum input depth. -/
theorem threeTerm_deep_forces_minimum_resonance
    {left middle right : ℚ} {leftDepth middleDepth rightDepth targetDepth : ℤ}
    (left_value : HasValue 5 left leftDepth)
    (middle_value : HasValue 5 middle middleDepth)
    (right_value : HasValue 5 right rightDepth)
    (sum_value : HasValue 5 (left + middle + right) targetDepth)
    (right_shallow : rightDepth < targetDepth) :
    (leftDepth = middleDepth ∧ leftDepth ≤ rightDepth) ∨
      (leftDepth = rightDepth ∧ leftDepth ≤ middleDepth) ∨
      (middleDepth = rightDepth ∧ middleDepth ≤ leftDepth) := by
  by_contra no_minimum_resonance
  have unique_minimum :
      (leftDepth < middleDepth ∧ leftDepth < rightDepth) ∨
        (middleDepth < leftDepth ∧ middleDepth < rightDepth) ∨
        (rightDepth < leftDepth ∧ rightDepth < middleDepth) := by
    by_contra no_unique_minimum
    push Not at no_minimum_resonance no_unique_minimum
    omega
  rcases unique_minimum with left_minimum | middle_minimum | right_minimum
  · have left_middle := add_hasValue_left left_value middle_value left_minimum.1
    have total_value := add_hasValue_left left_middle right_value left_minimum.2
    have depth_eq : leftDepth = targetDepth := total_value.2.symm.trans sum_value.2
    omega
  · have left_middle := add_hasValue_right left_value middle_value middle_minimum.1
    have total_value := add_hasValue_left left_middle right_value middle_minimum.2
    have depth_eq : middleDepth = targetDepth := total_value.2.symm.trans sum_value.2
    omega
  · by_cases pair_zero : left + middle = 0
    · have total_eq : left + middle + right = right := by rw [pair_zero, zero_add]
      have depth_eq : rightDepth = targetDepth := by
        calc
          rightDepth = padicValRat 5 right := right_value.2.symm
          _ = padicValRat 5 (left + middle + right) := congrArg _ total_eq.symm
          _ = targetDepth := sum_value.2
      omega
    · have pair_lower :
          min leftDepth middleDepth ≤ padicValRat 5 (left + middle) := by
        have raw := padicValRat.min_le_padicValRat_add
          (p := 5) pair_zero
        simpa [left_value.2, middle_value.2] using raw
      have pair_value :
          HasValue 5 (left + middle) (padicValRat 5 (left + middle)) :=
        ⟨pair_zero, rfl⟩
      have right_lt_pair : rightDepth < padicValRat 5 (left + middle) := by
        have right_lt_min : rightDepth < min leftDepth middleDepth := by
          simp only [lt_min_iff]
          exact right_minimum
        exact right_lt_min.trans_le pair_lower
      have total_value := add_hasValue_right pair_value right_value right_lt_pair
      have depth_eq : rightDepth = targetDepth := total_value.2.symm.trans sum_value.2
      omega

/-- Solving the minimum-resonance equations collapses every regular-head branch to one exact
rule-tail width.  At the exceptional head only the same phase frontier and two explicit
rightmost-`b` relative-position resonances remain. -/
theorem rightmostRule_minimumResonance_positionGrammar
    {β suffix rulePrefix ruleTail bTail : Nat} (β_large : 2 ≤ β)
    (resonance :
      let n := rulePrefix + ruleTail + 1
      let phaseDepth := if rulePrefix = 0 then ruleTail + 2 else ruleTail + 1
      let upperDepth := bTail + β + 2
      ((suffix + 2 ≤ β ∧
          ((min n (suffix + 1) = upperDepth ∧ min n (suffix + 1) ≤ phaseDepth) ∨
            (min n (suffix + 1) = phaseDepth ∧ min n (suffix + 1) ≤ upperDepth) ∨
            (upperDepth = phaseDepth ∧ upperDepth ≤ min n (suffix + 1)))) ∨
        (suffix = β - 1 ∧
          ((min n (2 * β - 1) = upperDepth ∧ min n (2 * β - 1) ≤ phaseDepth) ∨
            (min n (2 * β - 1) = phaseDepth ∧ min n (2 * β - 1) ≤ upperDepth) ∨
            (upperDepth = phaseDepth ∧ upperDepth ≤ min n (2 * β - 1)))))) :
    (suffix + 2 ≤ β ∧ 1 ≤ rulePrefix ∧ ruleTail = suffix) ∨
      (suffix = β - 1 ∧
        ((1 ≤ rulePrefix ∧ ruleTail = 2 * β - 2 ∧
            2 * β - 1 ≤ bTail + β + 2) ∨
          (min (rulePrefix + ruleTail + 1) (2 * β - 1) = bTail + β + 2 ∧
            bTail + β + 2 ≤
              (if rulePrefix = 0 then ruleTail + 2 else ruleTail + 1)) ∨
          (bTail + β + 2 =
              (if rulePrefix = 0 then ruleTail + 2 else ruleTail + 1) ∧
            bTail + β + 2 ≤ min (rulePrefix + ruleTail + 1) (2 * β - 1)))) := by
  dsimp only at resonance
  rcases resonance with ⟨suffix_regular, regular⟩ | ⟨suffix_exceptional, exceptional⟩
  · left
    refine ⟨suffix_regular, ?_⟩
    have base_upper_lt :
        min (rulePrefix + ruleTail + 1) (suffix + 1) < bTail + β + 2 := by
      calc
        min (rulePrefix + ruleTail + 1) (suffix + 1) ≤ suffix + 1 := min_le_right _ _
        _ < bTail + β + 2 := by omega
    rcases regular with base_upper | base_phase | upper_phase
    · omega
    · have rulePrefix_positive : 1 ≤ rulePrefix := by
        by_contra prefix_not_positive
        have prefix_zero : rulePrefix = 0 := by omega
        subst rulePrefix
        simp only [↓reduceIte] at base_phase
        have base_le_width :
            min (0 + ruleTail + 1) (suffix + 1) ≤ ruleTail + 1 := by
          simpa only [Nat.zero_add] using min_le_left (ruleTail + 1) (suffix + 1)
        omega
      refine ⟨rulePrefix_positive, ?_⟩
      simp only [if_neg (by omega : rulePrefix ≠ 0)] at base_phase
      by_cases suffix_le_width : suffix + 1 ≤ rulePrefix + ruleTail + 1
      · rw [min_eq_right suffix_le_width] at base_phase
        omega
      · rw [min_eq_left (by omega)] at base_phase
        omega
    · omega
  · right
    refine ⟨suffix_exceptional, ?_⟩
    rcases exceptional with base_upper | base_phase | upper_phase
    · refine Or.inr (Or.inl ⟨base_upper.1, ?_⟩)
      omega
    · left
      have rulePrefix_positive : 1 ≤ rulePrefix := by
        by_contra prefix_not_positive
        have prefix_zero : rulePrefix = 0 := by omega
        subst rulePrefix
        simp only [↓reduceIte] at base_phase
        have base_le_width :
            min (0 + ruleTail + 1) (2 * β - 1) ≤ ruleTail + 1 := by
          simpa only [Nat.zero_add] using min_le_left (ruleTail + 1) (2 * β - 1)
        omega
      simp only [if_neg (by omega : rulePrefix ≠ 0)] at base_phase
      have frontier_le_width : 2 * β - 1 ≤ rulePrefix + ruleTail + 1 := by
        by_contra frontier_not_le
        rw [min_eq_left (by omega)] at base_phase
        omega
      rw [min_eq_right frontier_le_width] at base_phase
      refine ⟨rulePrefix_positive, by omega, ?_⟩
      omega
    · exact Or.inr (Or.inr upper_phase)

private theorem exists_rightmostB_of_mem
    {letters : List TagLetter} (marker_mem : .b ∈ letters) :
    ∃ front tailWidth,
      letters = front ++ .b :: List.replicate tailWidth .c := by
  induction letters with
  | nil => simp at marker_mem
  | cons letter letters induction =>
      by_cases tail_marker : .b ∈ letters
      · obtain ⟨front, tailWidth, rightmost⟩ := induction tail_marker
        exact ⟨letter :: front, tailWidth, by rw [rightmost]; rfl⟩
      · have letter_b : letter = .b := by
          have reverse : .b = letter := by simpa [tail_marker] using marker_mem
          exact reverse.symm
        subst letter
        have tail_all_c : letters = List.replicate letters.length .c := by
          apply List.eq_replicate_length.mpr
          intro tile tile_mem
          cases tile with
          | b => exact False.elim (tail_marker tile_mem)
          | c => rfl
        refine ⟨[], letters.length, ?_⟩
        simpa only [List.nil_append] using congrArg (.b :: ·) tail_all_c

/-- A `b`-bearing rule block can hit its physical raw-entry shell only on a pairwise equality
among three exact five-depths: the all-`D_c` raw-head frontier, the rightmost-`b` upper
perturbation, and the rightmost-rule phase perturbation.  This is a finite positional resonance
grammar; no spelling enumeration remains. -/
theorem bBearingRightmostRule_rawHead_forces_resonance
    {β : Nat} (body headTail : List TagLetter) (front : List NearyTile)
    (ruleLetter : TagLetter) (tail : List TagLetter) {μ E G : ℤ}
    (β_large : 2 ≤ β)
    (marker_mem : .b ∈ front.map NearyTile.letter ++ ruleLetter :: tail)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: headTail)) : ℚ) 0 0)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (shell :
      HasDecimalShell
        (((code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) *
          (E * code (punctuatedUpper β
              (front.map NearyTile.letter ++ ruleLetter :: tail)) +
            G * code
              (spell (nearyLower β body)
                (front ++ .rule ruleLetter :: tail.map NearyTile.erase))) -
          10 * μ * G * code
            (spell (nearyLower β body)
              (front ++ .rule ruleLetter :: tail.map NearyTile.erase)) : ℤ) : ℚ)
        (((front.length + tail.length + 1 +
          (front.map NearyTile.letter ++ ruleLetter :: tail).count .b * (β + 1) - 1 : Nat) : ℤ))
        (((front.length + tail.length + 1 +
          (front.map NearyTile.letter ++ ruleLetter :: tail).count .b * (β + 1) - 1 : Nat) : ℤ))) :
    ∃ suffix bFront bTailWidth,
      front.map NearyTile.letter ++ ruleLetter :: tail =
        bFront ++ .b :: List.replicate bTailWidth .c ∧
      1 ≤ suffix ∧ suffix ≤ β - 1 ∧
      peeledHeadWord β (.c :: .c :: headTail) =
        List.replicate (β + 2 - suffix) true ++ List.replicate suffix false ∧
      let phaseDepth := if front = [] then tail.length + 2 else tail.length + 1
      let upperDepth := bTailWidth + β + 2
      ((suffix + 2 ≤ β ∧
          ((((min (front.length + tail.length + 1) (suffix + 1) : Nat) : ℤ) = upperDepth ∧
              ((min (front.length + tail.length + 1) (suffix + 1) : Nat) : ℤ) ≤ phaseDepth) ∨
            (((min (front.length + tail.length + 1) (suffix + 1) : Nat) : ℤ) = phaseDepth ∧
              ((min (front.length + tail.length + 1) (suffix + 1) : Nat) : ℤ) ≤ upperDepth) ∨
            ((upperDepth : ℤ) = phaseDepth ∧
              (upperDepth : ℤ) ≤ (min (front.length + tail.length + 1) (suffix + 1) : Nat)))) ∨
        (suffix = β - 1 ∧
          ((((min (front.length + tail.length + 1) (2 * β - 1) : Nat) : ℤ) = upperDepth ∧
              ((min (front.length + tail.length + 1) (2 * β - 1) : Nat) : ℤ) ≤ phaseDepth) ∨
            (((min (front.length + tail.length + 1) (2 * β - 1) : Nat) : ℤ) = phaseDepth ∧
              ((min (front.length + tail.length + 1) (2 * β - 1) : Nat) : ℤ) ≤ upperDepth) ∨
            ((upperDepth : ℤ) = phaseDepth ∧
              (upperDepth : ℤ) ≤ (min (front.length + tail.length + 1) (2 * β - 1) : Nat))))) := by
  let letters := front.map NearyTile.letter ++ ruleLetter :: tail
  let n := front.length + tail.length + 1
  let targetDepth := n + letters.count .b * (β + 1) - 1
  let phaseDepth := if front = [] then tail.length + 2 else tail.length + 1
  let H : ℤ := code (peeledHeadWord β (.c :: .c :: headTail))
  let P : ℤ := code (punctuatedUpper β letters)
  let PAll : ℤ := code (punctuatedUpper β (List.replicate n .c))
  let VRule : ℤ := code
    (spell (nearyLower β body) (front ++ .rule ruleLetter :: tail.map NearyTile.erase))
  let VErase : ℤ := allEraseLowerCode β body n
  let RRule : ℤ := H * (E * P + G * VRule) - 10 * μ * G * VRule
  let RErase : ℤ := H * (E * P + G * VErase) - 10 * μ * G * VErase
  let RAll : ℤ := H * (E * PAll + G * VErase) - 10 * μ * G * VErase
  obtain ⟨bFront, bTailWidth, letters_eq⟩ :=
    exists_rightmostB_of_mem (letters := letters) (by simpa only [letters] using marker_mem)
  have n_eq : n = bFront.length + bTailWidth + 1 := by
    have lengths : front.length + tail.length + 1 =
        bFront.length + bTailWidth + 1 := by
      have raw := congrArg List.length letters_eq
      dsimp only [letters] at raw
      simp only [List.length_append, List.length_cons, List.length_replicate,
        List.length_map] at raw
      omega
    dsimp only [n]
    omega
  have rule_value : HasValue 5 (RRule : ℚ) targetDepth := by
    simpa only [RRule, H, P, VRule, targetDepth, n, letters] using shell.2
  have lower_difference :
      HasValue 5 (((VRule - VErase : ℤ) : ℚ))
        (phaseDepth : ℤ) := by
    have companion_spell :
        spell (nearyLower β body)
            (front.map erasePhaseTile ++ .erase ruleLetter :: tail.map NearyTile.erase) =
          List.replicate n false := by
      have erased := spell_erasePhase_lower β body
        (front ++ .rule ruleLetter :: tail.map NearyTile.erase)
      simpa [n, List.map_append, List.map_map, erasePhaseTile, Function.comp_def,
        Nat.add_assoc] using erased
    have companion_code :
        (code (spell (nearyLower β body)
          (front.map erasePhaseTile ++ .erase ruleLetter :: tail.map NearyTile.erase)) : ℤ) =
          VErase := by
      rw [companion_spell]
      simp only [VErase, allEraseLowerCode, spell_allEraseBlock]
    by_cases front_nil : front = []
    · subst front
      have raw := rightmostRuleLowerCode_sub_hasDecimalShell_of_front_nil
        β body ruleLetter tail
      have companion_code' :
          (code (spell (nearyLower β body)
            (.erase ruleLetter :: tail.map NearyTile.erase)) : ℤ) = VErase := by
        simpa using companion_code
      rw [companion_code'] at raw
      simpa [phaseDepth, VRule] using raw.2
    · rcases front with _ | ⟨frontTile, front⟩
      · exact False.elim (front_nil rfl)
      · by_cases front_tail_nil : front = []
        · subst front
          have raw := rightmostRuleLowerCode_sub_hasValue_five_of_front_one
            β body frontTile ruleLetter tail
          have companion_code' :
              (code (spell (nearyLower β body)
                (erasePhaseTile frontTile :: .erase ruleLetter ::
                  tail.map NearyTile.erase)) : ℤ) = VErase := by
            simpa using companion_code
          rw [companion_code'] at raw
          simpa [phaseDepth, VRule] using raw
        · have front_large : 2 ≤ (frontTile :: front).length := by
            simp only [List.length_cons]
            have front_positive : 0 < front.length :=
              List.length_pos_iff_ne_nil.mpr front_tail_nil
            omega
          have raw := rightmostRuleLowerCode_sub_hasDecimalShell_of_two_le_front
            β body (frontTile :: front) ruleLetter tail front_large
          have companion_code' :
              (code (spell (nearyLower β body)
                ((frontTile :: front).map erasePhaseTile ++ .erase ruleLetter ::
                  tail.map NearyTile.erase)) : ℤ) = VErase := by
            simpa using companion_code
          rw [companion_code'] at raw
          simpa [phaseDepth, VRule] using raw.2
  have lift_unit := calibratedLift_decimalUnit (G := G) (by omega) lift_eq
  have head_gap_unit := peeledDoubleCHead_sub_tenMarker_decimalUnit
    headTail μ (by omega) head_unit
  have phase_value :
      HasValue 5 (((RRule - RErase : ℤ) : ℚ))
        (phaseDepth : ℤ) := by
    have raw := peeledNumerator_sameUpper_sub_hasValue_five
      (H := H) (μ := μ) (E := E) (G := G) (P := P)
      (V₁ := VRule) (V₂ := VErase)
      lift_unit.2 (by simpa only [H] using head_gap_unit.2) lower_difference
    simpa [RRule, RErase, H, P, VRule, VErase, peeledNumerator, transferTrace] using raw
  have upper_value :
      HasValue 5 (((RErase - RAll : ℤ) : ℚ)) (bTailWidth + β + 2) := by
    have raw := rightmostB_allEraseResidual_sub_allC_hasValue_five
      (tailWidth := bTailWidth) body headTail bFront (μ := μ) (E := E) (G := G)
      β_large head_unit gap_eq
    simpa [RErase, RAll, H, P, PAll, VErase, letters_eq, n_eq] using raw
  have allC_upper_eq : 9 * PAll = 50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7 :=
    allC_punctuatedUpper_code_identity β n
  have lower_eq : 9 * VErase = 7 * 10 ^ n - 7 := by
    have identity := allEraseLowerCode_identity β body n
    dsimp only [VErase]
    omega
  obtain ⟨suffix, suffix_positive, suffix_le, head_shape, frontier⟩ :=
    allCDeletion_peeledDoubleCHead_hasValue_five headTail β_large
      (by dsimp only [n]; omega) head_unit mu_eq gap_eq lift_eq
      allC_upper_eq lower_eq rfl rfl
  refine ⟨suffix, bFront, bTailWidth, by simpa only [letters] using letters_eq,
    suffix_positive, suffix_le, head_shape, ?_⟩
  have sum_value :
      HasValue 5
        ((RAll : ℚ) + ((RErase - RAll : ℤ) : ℚ) + ((RRule - RErase : ℤ) : ℚ))
        targetDepth := by
    have sum_eq :
        (RAll : ℚ) + ((RErase - RAll : ℤ) : ℚ) + ((RRule - RErase : ℤ) : ℚ) =
          (RRule : ℚ) := by
      push_cast
      ring
    rw [sum_eq]
    exact rule_value
  have phase_shallow :
      (phaseDepth : ℤ) < targetDepth := by
    have marker_positive : 1 ≤ letters.count .b :=
      List.count_pos_iff.mpr (by simpa only [letters] using marker_mem)
    have marker_scale : 3 ≤ letters.count .b * (β + 1) := by
      have scaled := Nat.mul_le_mul marker_positive (show 3 ≤ β + 1 by omega)
      simpa only [Nat.one_mul] using scaled
    have target_eq : targetDepth =
        front.length + tail.length + letters.count .b * (β + 1) := by
      dsimp only [targetDepth, n]
      omega
    have phase_shallow_nat : phaseDepth < targetDepth := by
      rw [target_eq]
      by_cases front_nil : front = []
      · subst front
        simp only [phaseDepth, ↓reduceIte, List.length_nil, Nat.zero_add]
        omega
      · have front_positive : 1 ≤ front.length :=
          List.length_pos_iff_ne_nil.mpr front_nil
        simp only [phaseDepth, if_neg front_nil]
        omega
    exact_mod_cast phase_shallow_nat
  rcases frontier with ⟨suffix_regular, erase_value⟩ |
      ⟨suffix_exceptional, erase_value⟩
  · left
    refine ⟨suffix_regular, ?_⟩
    exact threeTerm_deep_forces_minimum_resonance erase_value upper_value phase_value
      sum_value phase_shallow
  · right
    refine ⟨suffix_exceptional, ?_⟩
    exact threeTerm_deep_forces_minimum_resonance erase_value upper_value phase_value
      sum_value phase_shallow

/-- For an all-`c` rule-bearing raw entry, the rightmost rule is either in position two or its
erasure tail is forced onto the raw-head five-depth frontier.  A regular head forces exactly
`tailWidth = suffix`; the exceptional head forces `tailWidth = 2β-2`. -/
theorem allCRightmostRule_rawHead_forces_boundary
    {β tailWidth : Nat} (body headTail : List TagLetter) (front : List NearyTile)
    {μ E G : ℤ}
    (β_large : 2 ≤ β)
    (multi_role : 2 ≤ front.length + tailWidth + 1)
    (front_all_c : front.map NearyTile.letter = List.replicate front.length .c)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: headTail)) : ℚ) 0 0)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (shell :
      HasDecimalShell
        (((code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) *
          (E * code (punctuatedUpper β
              (front.map NearyTile.letter ++
                .c :: List.replicate tailWidth .c)) +
            G * code
              (spell (nearyLower β body)
                (front ++ .rule .c :: List.replicate tailWidth (.erase .c)))) -
          10 * μ * G * code
            (spell (nearyLower β body)
              (front ++ .rule .c :: List.replicate tailWidth (.erase .c))) : ℤ) : ℚ)
        (front.length + tailWidth) (front.length + tailWidth)) :
    front.length = 1 ∨
      ∃ suffix, 1 ≤ suffix ∧ suffix ≤ β - 1 ∧
        peeledHeadWord β (.c :: .c :: headTail) =
          List.replicate (β + 2 - suffix) true ++ List.replicate suffix false ∧
        ((suffix + 2 ≤ β ∧ tailWidth = suffix) ∨
          (suffix = β - 1 ∧ tailWidth = 2 * β - 2)) := by
  rcases lt_trichotomy front.length 1 with front_nil | front_one | front_large
  · have front_eq : front = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst front
    exfalso
    apply leadingRuleC_rawHead_multi_shell_impossible body headTail
      β_large (by simpa using multi_role) head_unit mu_eq gap_eq lift_eq
    simpa [List.replicate_succ, peeledNumerator, transferTrace] using shell
  · exact Or.inl front_one
  · right
    let n := front.length + tailWidth + 1
    let H : ℤ := code (peeledHeadWord β (.c :: .c :: headTail))
    let P : ℤ := code (punctuatedUpper β (List.replicate n .c))
    let VRule : ℤ := code
      (spell (nearyLower β body)
        (front ++ .rule .c :: List.replicate tailWidth (.erase .c)))
    let VErase : ℤ := allEraseLowerCode β body n
    let RRule : ℤ := H * (E * P + G * VRule) - 10 * μ * G * VRule
    let RErase : ℤ := H * (E * P + G * VErase) - 10 * μ * G * VErase
    have letters_eq :
        front.map NearyTile.letter ++ .c :: List.replicate tailWidth .c =
          List.replicate n .c := by
      dsimp only [n]
      rw [front_all_c]
      rw [show front.length + tailWidth + 1 = front.length + (tailWidth + 1) by omega,
        List.replicate_add, List.replicate_succ]
    have rule_shell :
        HasValue 5 (RRule : ℚ) (front.length + tailWidth) := by
      simpa only [RRule, H, P, VRule, letters_eq] using shell.2
    have lower_difference :
        HasDecimalShell (((VRule - VErase : ℤ) : ℚ))
          (tailWidth + 2) (tailWidth + 1) := by
      have raw := rightmostRuleLowerCode_sub_hasDecimalShell_of_two_le_front
        β body front TagLetter.c (List.replicate tailWidth .c) (by omega)
      have companion_spell :
          spell (nearyLower β body)
              (front.map erasePhaseTile ++
                .erase .c :: List.replicate tailWidth (.erase .c)) =
            List.replicate n false := by
        have erased := spell_erasePhase_lower β body
          (front ++ .rule .c :: List.replicate tailWidth (.erase .c))
        simpa [n, List.map_append, List.map_replicate, erasePhaseTile,
          Nat.add_assoc] using erased
      simp only [List.map_replicate, List.length_replicate] at raw
      rw [companion_spell] at raw
      simpa [VRule, VErase, allEraseLowerCode, spell_allEraseBlock] using raw
    have lift_unit := calibratedLift_decimalUnit (G := G) (by omega) lift_eq
    have head_gap_unit := peeledDoubleCHead_sub_tenMarker_decimalUnit
      headTail μ (by omega) head_unit
    have residual_difference :
        HasValue 5 (((RRule - RErase : ℤ) : ℚ)) (tailWidth + 1) := by
      have raw := peeledNumerator_sameUpper_sub_hasValue_five
        (H := H) (μ := μ) (E := E) (G := G) (P := P)
        (V₁ := VRule) (V₂ := VErase)
        lift_unit.2 (by simpa only [H] using head_gap_unit.2) lower_difference.2
      simpa [RRule, RErase, H, P, VRule, VErase, peeledNumerator, transferTrace]
        using raw
    have allC_upper_eq : 9 * P = 50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7 := by
      exact allC_punctuatedUpper_code_identity β n
    have lower_eq : 9 * VErase = 7 * 10 ^ n - 7 := by
      have identity := allEraseLowerCode_identity β body n
      dsimp only [VErase]
      omega
    obtain ⟨suffix, suffix_positive, suffix_le, head_shape, frontier⟩ :=
      allCDeletion_peeledDoubleCHead_hasValue_five headTail β_large
        (by dsimp only [n]; omega) head_unit mu_eq gap_eq lift_eq
        allC_upper_eq lower_eq rfl rfl
    refine ⟨suffix, suffix_positive, suffix_le, head_shape, ?_⟩
    rcases frontier with ⟨suffix_regular, erase_value⟩ |
        ⟨suffix_exceptional, erase_value⟩
    · left
      refine ⟨suffix_regular, ?_⟩
      have sum_value :
          HasValue 5
            ((RErase : ℚ) + ((RRule - RErase : ℤ) : ℚ))
            (front.length + tailWidth) := by
        have sum_eq :
            (RErase : ℚ) + ((RRule - RErase : ℤ) : ℚ) = (RRule : ℚ) := by
          push_cast
          ring
        rw [sum_eq]
        exact rule_shell
      have depth_eq := twoTerm_deep_forces_depth_resonance erase_value
        residual_difference sum_value (by omega)
      have width_large : suffix + 1 < n := by
        dsimp only [n]
        omega
      simpa [min_eq_right (Nat.le_of_lt width_large)] using depth_eq.symm
    · right
      refine ⟨suffix_exceptional, ?_⟩
      have sum_value :
          HasValue 5
            ((RErase : ℚ) + ((RRule - RErase : ℤ) : ℚ))
            (front.length + tailWidth) := by
        have sum_eq :
            (RErase : ℚ) + ((RRule - RErase : ℤ) : ℚ) = (RRule : ℚ) := by
          push_cast
          ring
        rw [sum_eq]
        exact rule_shell
      have depth_eq := twoTerm_deep_forces_depth_resonance erase_value
        residual_difference sum_value (by omega)
      have width_large : 2 * β - 1 < n := by
        by_contra width_not_large
        have minimum_eq : min n (2 * β - 1) = n := min_eq_left (by omega)
        rw [minimum_eq] at depth_eq
        dsimp only [n] at depth_eq
        omega
      have depth_eq' : ((tailWidth + 1 : Nat) : ℤ) = ((2 * β - 1 : Nat) : ℤ) := by
        simpa [min_eq_right (Nat.le_of_lt width_large)] using depth_eq.symm
      have depth_eq_nat : tailWidth + 1 = 2 * β - 1 := by
        exact_mod_cast depth_eq'
      omega

end MatrixMortality.DecimalSetterRuleResonance
