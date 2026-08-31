import MatrixMortality.DecimalSetterDepth
import Mathlib.Tactic

/-!
# Deep five-adic obstruction for the decimal setter

The all-`D_c` raw residual already falls short of five-adic depth `n+1` at every positive width.
Any upper-code perturbation at that depth preserves the obstruction. This excludes a sole
`D_b` in any of the first `β+1` roles.
-/

namespace MatrixMortality.DecimalSetterDepth

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterChamber

private theorem fivePower_dvd_tenPower {small large : Nat} (bound : small ≤ large) :
    (5 : ℤ) ^ small ∣ 10 ^ large :=
  (pow_dvd_pow (5 : ℤ) bound).trans
    (pow_dvd_pow_of_dvd (by norm_num : (5 : ℤ) ∣ 10) large)

private theorem five_dvd_of_pow_succ_dvd_ten_pow_mul
    {depth : Nat} {coefficient : ℤ}
    (divides : (5 : ℤ) ^ (depth + 1) ∣ 10 ^ depth * coefficient) :
    (5 : ℤ) ∣ coefficient := by
  have ten_power : (10 : ℤ) ^ depth = 5 ^ depth * 2 ^ depth := by
    rw [show (10 : ℤ) = 5 * 2 by norm_num, mul_pow]
  rw [ten_power, pow_succ, mul_assoc] at divides
  have rearranged : (5 : ℤ) ^ depth * 5 ∣
      5 ^ depth * (2 ^ depth * coefficient) := by
    simpa [mul_assoc] using divides
  have power_ne : (5 : ℤ) ^ depth ≠ 0 := pow_ne_zero _ (by norm_num)
  have five_dvd_scaled : (5 : ℤ) ∣ 2 ^ depth * coefficient :=
    (mul_dvd_mul_iff_left power_ne).mp rearranged
  have coprime : IsCoprime (5 : ℤ) ((2 : ℤ) ^ depth) :=
    (by norm_num : IsCoprime (5 : ℤ) 2).pow_right
  exact coprime.dvd_of_dvd_mul_left five_dvd_scaled

private theorem five_dvd_of_pow_add_two_dvd_ten_pow_mul_five
    {depth : Nat} {coefficient : ℤ}
    (divides : (5 : ℤ) ^ (depth + 2) ∣ 10 ^ depth * 5 * coefficient) :
    (5 : ℤ) ∣ coefficient := by
  have factored : (5 : ℤ) * 5 ^ (depth + 1) ∣
      5 * (10 ^ depth * coefficient) := by
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using divides
  have reduced : (5 : ℤ) ^ (depth + 1) ∣ 10 ^ depth * coefficient :=
    (mul_dvd_mul_iff_left (show (5 : ℤ) ≠ 0 by norm_num)).mp factored
  exact five_dvd_of_pow_succ_dvd_ten_pow_mul reduced

private theorem fivePower_succ_dvd_fortyFive_mul
    {depth : Nat} {value : ℤ} (divides : (5 : ℤ) ^ depth ∣ value) :
    (5 : ℤ) ^ (depth + 1) ∣ 45 * value := by
  obtain ⟨quotient, rfl⟩ := divides
  refine ⟨9 * quotient, ?_⟩
  rw [pow_succ]
  ring

private theorem fivePower_succ_dvd_tenPower_mul_five
    {small large : Nat} (bound : small ≤ large) (coefficient : ℤ) :
    (5 : ℤ) ^ (small + 1) ∣ 10 ^ large * 5 * coefficient := by
  have base : (5 : ℤ) ^ small ∣ 10 ^ large := fivePower_dvd_tenPower bound
  have scaled : (5 : ℤ) ^ small * 5 ∣ 10 ^ large * 5 :=
    mul_dvd_mul base (dvd_refl 5)
  simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using scaled.mul_right coefficient

private theorem not_five_dvd_of_sub_residue
    {value residue : ℤ} (deviation : (5 : ℤ) ∣ value - residue)
    (residue_unit : ¬(5 : ℤ) ∣ residue) :
    ¬(5 : ℤ) ∣ value := by
  intro value_dvd
  exact residue_unit (by simpa using dvd_sub value_dvd deviation)

/-- Before the first-head boundary, an all-`D_c` raw residual misses five-adic depth `n+1`. -/
theorem allCDeletion_regularRawHead_not_fiveAboveWidth
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
    ¬(5 : ℤ) ^ (n + 1) ∣ R := by
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
  have rho_five : (5 : ℤ) ∣ ρ := by
    dsimp [ρ]
    exact fivePower_dvd_tenPower (show 1 ≤ β by omega)
  obtain ⟨rhoQuotient, rho_eq⟩ := rho_five
  have H_sub_two_dvd : (5 : ℤ) ∣ H - 2 := by
    have scaled_eq : 9 * (H - 2) =
        5 * 10 ^ (β + 2) + 2 * 10 ^ s - 25 := by
      linear_combination head_eq
    have first_dvd : (5 : ℤ) ∣ 5 * 10 ^ (β + 2) := dvd_mul_right 5 _
    have second_dvd : (5 : ℤ) ∣ 2 * 10 ^ s := by
      exact dvd_mul_of_dvd_right
        (fivePower_dvd_tenPower (show 1 ≤ s by omega)) 2
    have scaled_dvd : (5 : ℤ) ∣ 9 * (H - 2) := by
      rw [scaled_eq]
      exact dvd_sub (dvd_add first_dvd second_dvd) (by norm_num)
    exact (by norm_num : IsCoprime (5 : ℤ) 9).dvd_of_dvd_mul_left scaled_dvd
  have H_five_unit : ¬(5 : ℤ) ∣ H := by
    intro H_dvd
    have two_dvd : (5 : ℤ) ∣ 2 := by
      simpa using dvd_sub H_dvd H_sub_two_dvd
    norm_num at two_dvd
  have K_sub_three_dvd : (5 : ℤ) ∣ K - 3 := by
    refine ⟨49 * 10 ^ (β + 2 - s) + 19, ?_⟩
    dsimp [K]
    ring
  have K_five_unit : ¬(5 : ℤ) ∣ K := by
    intro K_dvd
    have three_dvd : (5 : ℤ) ∣ 3 := by
      simpa using dvd_sub K_dvd K_sub_three_dvd
    norm_num at three_dvd
  have A_add_H_dvd : (5 : ℤ) ∣ A + H := by
    refine ⟨1620 * H * ρ ^ 2 + 3276 * H * rhoQuotient - 88 * H -
      365456 * ρ ^ 2 + 54292 * ρ - 686, ?_⟩
    dsimp [A]
    rw [rho_eq]
    ring
  have A_five_unit : ¬(5 : ℤ) ∣ A := by
    intro A_dvd
    have H_dvd : (5 : ℤ) ∣ H := by
      simpa using dvd_sub A_add_H_dvd A_dvd
    exact H_five_unit H_dvd
  have K_add_A_five_unit : ¬(5 : ℤ) ∣ K + A := by
    intro sum_dvd
    have one_dvd : (5 : ℤ) ∣ 1 := by
      have combined := dvd_add
        (dvd_sub (dvd_sub sum_dvd K_sub_three_dvd) A_add_H_dvd) H_sub_two_dvd
      rw [show K + A - (K - 3) - (A + H) + (H - 2) = 1 by ring] at combined
      exact combined
    norm_num at one_dvd
  intro width_dvd
  rcases lt_trichotomy n (s + 1) with n_small | n_equal | n_large
  · have reduced_dvd : (5 : ℤ) ^ (n + 1) ∣ 81 * R := by
      exact dvd_mul_of_dvd_right width_dvd 81
    have first_dvd : (5 : ℤ) ^ (n + 1) ∣ 10 ^ (s + 1) * K :=
      dvd_mul_of_dvd_left (fivePower_dvd_tenPower (by omega)) K
    have third_dvd : (5 : ℤ) ^ (n + 1) ∣ 10 ^ β * B :=
      dvd_mul_of_dvd_left (fivePower_dvd_tenPower (by omega)) B
    rw [decomposition'] at reduced_dvd
    have first_second : (5 : ℤ) ^ (n + 1) ∣ 10 ^ (s + 1) * K + 10 ^ n * A := by
      have truncated := dvd_sub reduced_dvd third_dvd
      rw [show 10 ^ (s + 1) * K + 10 ^ n * A + 10 ^ β * B - 10 ^ β * B =
        10 ^ (s + 1) * K + 10 ^ n * A by ring] at truncated
      exact truncated
    have second_dvd : (5 : ℤ) ^ (n + 1) ∣ 10 ^ n * A := by
      simpa using dvd_sub first_second first_dvd
    exact A_five_unit (five_dvd_of_pow_succ_dvd_ten_pow_mul second_dvd)
  · subst n
    have reduced_dvd : (5 : ℤ) ^ (s + 2) ∣ 81 * R := by
      simpa only [Nat.add_assoc] using dvd_mul_of_dvd_right width_dvd 81
    have third_dvd : (5 : ℤ) ^ (s + 2) ∣ 10 ^ β * B :=
      dvd_mul_of_dvd_left (fivePower_dvd_tenPower suffix_below) B
    rw [decomposition'] at reduced_dvd
    have first_second : (5 : ℤ) ^ (s + 2) ∣
        10 ^ (s + 1) * K + 10 ^ (s + 1) * A := by
      have truncated := dvd_sub reduced_dvd third_dvd
      rw [show 10 ^ (s + 1) * K + 10 ^ (s + 1) * A + 10 ^ β * B -
        10 ^ β * B = 10 ^ (s + 1) * K + 10 ^ (s + 1) * A by ring] at truncated
      exact truncated
    have combined_dvd : (5 : ℤ) ^ (s + 2) ∣ 10 ^ (s + 1) * (K + A) := by
      simpa [mul_add] using first_second
    exact K_add_A_five_unit
      (five_dvd_of_pow_succ_dvd_ten_pow_mul combined_dvd)
  · have reduced_dvd : (5 : ℤ) ^ (s + 2) ∣ 81 * R := by
      have power_dvd : (5 : ℤ) ^ (s + 2) ∣ R :=
        (pow_dvd_pow (5 : ℤ) (by omega)).trans width_dvd
      exact dvd_mul_of_dvd_right power_dvd 81
    have second_dvd : (5 : ℤ) ^ (s + 2) ∣ 10 ^ n * A :=
      dvd_mul_of_dvd_left (fivePower_dvd_tenPower (by omega)) A
    have third_dvd : (5 : ℤ) ^ (s + 2) ∣ 10 ^ β * B :=
      dvd_mul_of_dvd_left (fivePower_dvd_tenPower suffix_below) B
    rw [decomposition'] at reduced_dvd
    have first_second : (5 : ℤ) ^ (s + 2) ∣ 10 ^ (s + 1) * K + 10 ^ n * A := by
      have truncated := dvd_sub reduced_dvd third_dvd
      rw [show 10 ^ (s + 1) * K + 10 ^ n * A + 10 ^ β * B - 10 ^ β * B =
        10 ^ (s + 1) * K + 10 ^ n * A by ring] at truncated
      exact truncated
    have first_dvd : (5 : ℤ) ^ (s + 2) ∣ 10 ^ (s + 1) * K := by
      simpa using dvd_sub first_second second_dvd
    exact K_five_unit
      (five_dvd_of_pow_succ_dvd_ten_pow_mul first_dvd)

/-- A regular raw head leaves the all-`D_c` residual below five-adic depth `β`, independently
of the all-erasure word width. -/
theorem allCDeletion_regularRawHead_not_fiveAtBeta
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
    ¬(5 : ℤ) ^ β ∣ R := by
  have above_width_cut := allCDeletion_regularRawHead_not_fiveAboveWidth
    s_positive suffix_below n_positive head_eq mu_eq gap_eq lift_eq upper_eq lower_eq
      trace_eq residual_eq
  intro beta_dvd
  by_cases n_below_beta : n < β
  · exact above_width_cut ((pow_dvd_pow (5 : ℤ) (by omega)).trans beta_dvd)
  · let ρ : ℤ := 10 ^ β
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
    have K_sub_three_dvd : (5 : ℤ) ∣ K - 3 := by
      refine ⟨49 * 10 ^ (β + 2 - s) + 19, ?_⟩
      dsimp [K]
      ring
    have K_five_unit : ¬(5 : ℤ) ∣ K := by
      intro K_dvd
      have three_dvd : (5 : ℤ) ∣ 3 := by
        simpa using dvd_sub K_dvd K_sub_three_dvd
      norm_num at three_dvd
    have scaled_dvd : (5 : ℤ) ^ β ∣ 81 * R :=
      dvd_mul_of_dvd_right beta_dvd 81
    have second_dvd : (5 : ℤ) ^ β ∣ 10 ^ n * A := by
      exact dvd_mul_of_dvd_left
        (fivePower_dvd_tenPower (Nat.le_of_not_gt n_below_beta)) A
    have third_dvd : (5 : ℤ) ^ β ∣ 10 ^ β * B := by
      exact dvd_mul_of_dvd_left (fivePower_dvd_tenPower le_rfl) B
    rw [decomposition'] at scaled_dvd
    have first_dvd : (5 : ℤ) ^ β ∣ 10 ^ (s + 1) * K := by
      have isolated := dvd_sub (dvd_sub scaled_dvd third_dvd) second_dvd
      rw [show 10 ^ (s + 1) * K + 10 ^ n * A + 10 ^ β * B - 10 ^ β * B -
        10 ^ n * A = 10 ^ (s + 1) * K by ring] at isolated
      exact isolated
    have shallow_dvd : (5 : ℤ) ^ (s + 2) ∣ 10 ^ (s + 1) * K :=
      (pow_dvd_pow (5 : ℤ) suffix_below).trans first_dvd
    exact K_five_unit
      (five_dvd_of_pow_succ_dvd_ten_pow_mul (by simpa only [Nat.add_assoc] using shallow_dvd))

/-- The exceptional raw-head residual has a two-term five-adic normal form. Its coefficients
have fixed nonzero residues modulo `5`. -/
theorem allCDeletion_firstRawHead_residueNormalForm
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
    ∃ C B : ℤ,
      45 * R = 10 ^ n * (5 * C) + 10 ^ (2 * β) * B ∧
      (5 : ℤ) ∣ C - 2 ∧
      (5 : ℤ) ∣ B - 1 := by
  let ρ : ℤ := 10 ^ β
  let a : ℤ := 10 ^ (β - 1)
  let A : ℤ := 250100 * ρ ^ 3 - 917504 * ρ ^ 2 + 135779 * ρ - 1715
  let B : ℤ := 10004 * ρ - 31514
  have exponent_eq : β = (β - 1) + 1 := by omega
  have rho_eq_ten : ρ = 10 * a := by
    dsimp [ρ, a]
    calc
      (10 : ℤ) ^ β = 10 ^ ((β - 1) + 1) := congrArg _ exponent_eq
      _ = 10 ^ (β - 1) * 10 := pow_succ _ _
      _ = 10 * 10 ^ (β - 1) := mul_comm _ _
  have head_eq' : 9 * H = 500 * ρ + 2 * a - 7 := by
    calc
      9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ (β - 1) - 7 := head_eq
      _ = 500 * ρ + 2 * a - 7 := by
        dsimp [ρ, a]
        rw [pow_add]
        norm_num
        ring
  have decomposition := allCDeletion_firstRawHead_residual_decomposition
    rho_eq_ten head_eq' mu_eq gap_eq lift_eq upper_eq lower_eq trace_eq residual_eq
  have decomposition' : 45 * R = 10 ^ n * A + 10 ^ (2 * β) * B := by
    have scale_eq : (10 : ℤ) ^ (2 * β) = ρ ^ 2 := by
      dsimp [ρ]
      rw [two_mul, pow_add, pow_two]
    rw [scale_eq]
    simpa [A, B, mul_assoc, mul_left_comm, mul_comm] using decomposition
  have rho_twenty_five : (25 : ℤ) ∣ ρ := by
    dsimp [ρ]
    simpa using fivePower_dvd_tenPower (small := 2) (show 2 ≤ β by omega)
  obtain ⟨rhoQuotient, rho_eq⟩ := rho_twenty_five
  let C : ℤ :=
    250100 * 3125 * rhoQuotient ^ 3 - 917504 * 125 * rhoQuotient ^ 2 +
      135779 * 5 * rhoQuotient - 343
  have A_eq : A = 5 * C := by
    dsimp [A, C]
    rw [rho_eq]
    ring
  have C_sub_two_dvd : (5 : ℤ) ∣ C - 2 := by
    refine ⟨250100 * 625 * rhoQuotient ^ 3 - 917504 * 25 * rhoQuotient ^ 2 +
      135779 * rhoQuotient - 69, ?_⟩
    dsimp [C]
    ring
  have B_sub_one_dvd : (5 : ℤ) ∣ B - 1 := by
    refine ⟨50020 * rhoQuotient - 6303, ?_⟩
    dsimp [B]
    rw [rho_eq]
    ring
  refine ⟨C, B, ?_, C_sub_two_dvd, B_sub_one_dvd⟩
  rw [decomposition', A_eq]

/-- At the first-head boundary, an all-`D_c` raw residual also misses five-adic depth `n+1`.
The proof resolves the possible collision between exponents `n+1` and `2β`. -/
theorem allCDeletion_firstRawHead_not_fiveAboveWidth
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
    ¬(5 : ℤ) ^ (n + 1) ∣ R := by
  have first_ten_bound : n + 1 < 2 * β → n + 2 ≤ 2 * β := by omega
  have equal_reduction_bound : n + 1 = 2 * β → 2 * β + 1 ≤ n + 2 := by omega
  have third_reduction_bound : 2 * β < n + 1 → 2 * β + 1 ≤ n + 2 := by omega
  have third_ten_bound : 2 * β < n + 1 → 2 * β ≤ n := by omega
  obtain ⟨C, B, decomposition, C_sub_two_dvd, B_sub_one_dvd⟩ :=
    allCDeletion_firstRawHead_residueNormalForm β_large head_eq mu_eq gap_eq lift_eq
      upper_eq lower_eq trace_eq residual_eq
  have C_five_unit : ¬(5 : ℤ) ∣ C := by
    intro C_dvd
    have two_dvd : (5 : ℤ) ∣ 2 := by
      simpa using dvd_sub C_dvd C_sub_two_dvd
    norm_num at two_dvd
  have B_five_unit : ¬(5 : ℤ) ∣ B := by
    intro B_dvd
    have one_dvd : (5 : ℤ) ∣ 1 := by
      simpa using dvd_sub B_dvd B_sub_one_dvd
    norm_num at one_dvd
  have C_add_two_B_five_unit : ¬(5 : ℤ) ∣ C + 2 * B := by
    intro sum_dvd
    have four_dvd : (5 : ℤ) ∣ 4 := by
      have deviation_dvd : (5 : ℤ) ∣ (C - 2) + 2 * (B - 1) :=
        dvd_add C_sub_two_dvd (B_sub_one_dvd.mul_left 2)
      have difference := dvd_sub sum_dvd deviation_dvd
      rw [show C + 2 * B - ((C - 2) + 2 * (B - 1)) = 4 by ring] at difference
      exact difference
    norm_num at four_dvd
  intro width_dvd
  have product_deep : (5 : ℤ) ^ (n + 2) ∣ 45 * R := by
    exact fivePower_succ_dvd_fortyFive_mul width_dvd
  rw [decomposition] at product_deep
  rcases lt_trichotomy (n + 1) (2 * β) with first_shallow | exponents_equal | second_shallow
  · have reduced : (5 : ℤ) ^ (n + 2) ∣
        10 ^ n * (5 * C) + 10 ^ (2 * β) * B := product_deep
    have second_dvd : (5 : ℤ) ^ (n + 2) ∣ 10 ^ (2 * β) * B :=
      dvd_mul_of_dvd_left (fivePower_dvd_tenPower (first_ten_bound first_shallow)) B
    have first_dvd : (5 : ℤ) ^ (n + 2) ∣ 10 ^ n * 5 * C := by
      have isolated := dvd_sub reduced second_dvd
      rw [show 10 ^ n * (5 * C) + 10 ^ (2 * β) * B - 10 ^ (2 * β) * B =
        10 ^ n * 5 * C by ring] at isolated
      exact isolated
    exact C_five_unit
      (five_dvd_of_pow_add_two_dvd_ten_pow_mul_five first_dvd)
  · have reduced : (5 : ℤ) ^ (2 * β + 1) ∣
        10 ^ n * (5 * C) + 10 ^ (2 * β) * B :=
      (pow_dvd_pow (5 : ℤ) (equal_reduction_bound exponents_equal)).trans product_deep
    have ten_expansion :
        10 ^ n * (5 * C) + 10 ^ (2 * β) * B =
          5 ^ (2 * β) * (2 ^ n * C + 2 ^ (2 * β) * B) := by
      rw [show (10 : ℤ) = 5 * 2 by norm_num]
      simp only [mul_pow]
      rw [← exponents_equal, pow_succ]
      ring
    rw [ten_expansion] at reduced
    have power_ne : (5 : ℤ) ^ (2 * β) ≠ 0 := pow_ne_zero _ (by norm_num)
    have coefficient_dvd : (5 : ℤ) ∣ 2 ^ n * C + 2 ^ (2 * β) * B := by
      have rearranged : (5 : ℤ) ^ (2 * β) * 5 ∣
          5 ^ (2 * β) * (2 ^ n * C + 2 ^ (2 * β) * B) := by
        simpa [pow_succ] using reduced
      exact (mul_dvd_mul_iff_left power_ne).mp rearranged
    have coefficient_factor :
        2 ^ n * C + 2 ^ (2 * β) * B = 2 ^ n * (C + 2 * B) := by
      rw [← exponents_equal, pow_succ]
      ring
    rw [coefficient_factor] at coefficient_dvd
    have two_coprime : IsCoprime (5 : ℤ) (2 ^ n) :=
      (by norm_num : IsCoprime (5 : ℤ) 2).pow_right
    exact C_add_two_B_five_unit
      (two_coprime.dvd_of_dvd_mul_left coefficient_dvd)
  · have reduced : (5 : ℤ) ^ (2 * β + 1) ∣
        10 ^ n * (5 * C) + 10 ^ (2 * β) * B :=
      (pow_dvd_pow (5 : ℤ) (third_reduction_bound second_shallow)).trans product_deep
    have first_dvd : (5 : ℤ) ^ (2 * β + 1) ∣ 10 ^ n * (5 * C) := by
      have base : (5 : ℤ) ^ (2 * β) ∣ 10 ^ n :=
        fivePower_dvd_tenPower (third_ten_bound second_shallow)
      have scaled : (5 : ℤ) ^ (2 * β) * 5 ∣ 10 ^ n * 5 :=
        mul_dvd_mul base (dvd_refl 5)
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using scaled.mul_right C
    have second_dvd : (5 : ℤ) ^ (2 * β + 1) ∣ 10 ^ (2 * β) * B := by
      have isolated := dvd_sub reduced first_dvd
      rw [show 10 ^ n * (5 * C) + 10 ^ (2 * β) * B - 10 ^ n * (5 * C) =
        10 ^ (2 * β) * B by ring] at isolated
      exact isolated
    exact B_five_unit
      (five_dvd_of_pow_succ_dvd_ten_pow_mul second_dvd)

/-- Every decimal-unit two-`c` raw head followed by an all-`D_c` word has five-adic residual
depth at most the word width `n`. -/
theorem allCDeletion_peeledDoubleCHead_not_fiveAboveWidth
    {β n : Nat} (tail : List TagLetter) {μ E G P V T R : ℤ}
    (β_large : 2 ≤ β) (n_positive : 1 ≤ n)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: tail)) : ℚ) 0 0)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (upper_eq : 9 * P = 50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7)
    (lower_eq : 9 * V = 7 * 10 ^ n - 7)
    (trace_eq : T = E * P + G * V)
    (residual_eq :
      R = (code (peeledHeadWord β (.c :: .c :: tail)) : ℤ) * T -
        10 * μ * G * V) :
    ¬(5 : ℤ) ^ (n + 1) ∣ R := by
  obtain ⟨suffix, suffix_positive, suffix_le, _, head_eq⟩ :=
    peeledDoubleCHead_unit_shape tail (by omega) head_unit
  rcases lt_or_eq_of_le suffix_le with suffix_below | first_head
  · exact allCDeletion_regularRawHead_not_fiveAboveWidth suffix_positive (by omega) n_positive
      head_eq
      mu_eq gap_eq lift_eq upper_eq lower_eq trace_eq residual_eq
  · rw [first_head] at head_eq
    exact allCDeletion_firstRawHead_not_fiveAboveWidth β_large head_eq
      mu_eq gap_eq lift_eq upper_eq lower_eq trace_eq residual_eq

private theorem fivePower_dvd_int_of_hasDecimalShell
    {value : ℤ} {depth : Nat}
    (shell : HasDecimalShell (value : ℚ) depth depth) :
    (5 : ℤ) ^ depth ∣ value := by
  have valuation_eq : padicValInt 5 value = depth := by
    have valuation_rat := shell.2.2
    rw [padicValRat.of_int] at valuation_rat
    exact_mod_cast valuation_rat
  exact (padicValInt_dvd_iff depth value).mpr (Or.inr (by rw [valuation_eq]))

/-- A late upper perturbation with unit coefficient cannot repair the exceptional raw-head
residual. The two strict depth orders and all three resonance patterns are excluded. -/
theorem exceptionalRawHead_lateUpperPerturbation_shell_impossible
    {β prefixWidth tailWidth : Nat} {H μ E G PAll P V RAll R D : ℤ}
    (β_large : 2 ≤ β) (prefix_late : β < prefixWidth)
    (head_eq : 9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ (β - 1) - 7)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (allC_upper_eq :
      9 * PAll = 50 * 10 ^ β * 10 ^ (prefixWidth + tailWidth + 1) +
        2 * 10 ^ β - 7)
    (lower_eq : 9 * V = 7 * 10 ^ (prefixWidth + tailWidth + 1) - 7)
    (allC_residual_eq :
      RAll = H * (E * PAll + G * V) - 10 * μ * G * V)
    (upper_difference_eq :
      P - PAll = D * 10 ^ (tailWidth + β + 2))
    (coefficient_sub_two_dvd : (5 : ℤ) ∣ D - 2)
    (residual_eq : R = H * (E * P + G * V) - 10 * μ * G * V)
    (shell :
      HasDecimalShell (R : ℚ)
        (prefixWidth + tailWidth + 1 + β)
        (prefixWidth + tailWidth + 1 + β)) :
    False := by
  let n := prefixWidth + tailWidth + 1
  let d := tailWidth + β + 2
  let Q := 9 * H * E * D
  obtain ⟨C, B, allC_decomposition, C_sub_two_dvd, B_sub_one_dvd⟩ :=
    allCDeletion_firstRawHead_residueNormalForm
      (n := n) (T := E * PAll + G * V) β_large head_eq mu_eq gap_eq lift_eq
      (by simpa only [n] using allC_upper_eq)
      (by simpa only [n] using lower_eq) rfl allC_residual_eq
  have ten_beta_minus_one_dvd : (5 : ℤ) ∣ 10 ^ (β - 1) := by
    simpa using fivePower_dvd_tenPower (small := 1) (show 1 ≤ β - 1 by omega)
  have H_sub_two_dvd : (5 : ℤ) ∣ H - 2 := by
    have scaled_eq : 9 * (H - 2) =
        5 * 10 ^ (β + 2) + 2 * 10 ^ (β - 1) - 25 := by
      linear_combination head_eq
    have scaled_dvd : (5 : ℤ) ∣ 9 * (H - 2) := by
      rw [scaled_eq]
      exact dvd_sub
        (dvd_add (dvd_mul_right 5 _)
          (dvd_mul_of_dvd_right ten_beta_minus_one_dvd 2))
        (by norm_num)
    exact (by norm_num : IsCoprime (5 : ℤ) 9).dvd_of_dvd_mul_left scaled_dvd
  have ten_beta_dvd : (5 : ℤ) ∣ 10 ^ β := by
    simpa using fivePower_dvd_tenPower (small := 1) (show 1 ≤ β by omega)
  have E_sub_two_dvd : (5 : ℤ) ∣ E - 2 := by
    have gap_deviation : E - 2 = 18 * 10 ^ β - 65 := by
      rw [gap_eq]
      ring
    rw [gap_deviation]
    exact dvd_sub (ten_beta_dvd.mul_left 18) (by norm_num)
  have product_sub_eight_dvd : (5 : ℤ) ∣ H * E * D - 8 := by
    rw [show H * E * D - 8 =
      (H - 2) * E * D + 2 * (E - 2) * D + 4 * (D - 2) by ring]
    exact dvd_add
      (dvd_add ((H_sub_two_dvd.mul_right E).mul_right D)
        ((E_sub_two_dvd.mul_left 2).mul_right D))
      (coefficient_sub_two_dvd.mul_left 4)
  have Q_sub_two_dvd : (5 : ℤ) ∣ Q - 2 := by
    rw [show Q - 2 = 9 * (H * E * D - 8) + 70 by
      dsimp only [Q]
      ring]
    exact dvd_add (product_sub_eight_dvd.mul_left 9) (by norm_num)
  have C_add_Q_sub_four_dvd : (5 : ℤ) ∣ C + Q - 4 := by
    rw [show C + Q - 4 = (C - 2) + (Q - 2) by ring]
    exact dvd_add C_sub_two_dvd Q_sub_two_dvd
  have two_B_add_Q_sub_four_dvd : (5 : ℤ) ∣ 2 * B + Q - 4 := by
    rw [show 2 * B + Q - 4 = 2 * (B - 1) + (Q - 2) by ring]
    exact dvd_add (B_sub_one_dvd.mul_left 2) Q_sub_two_dvd
  have C_add_two_B_add_Q_sub_one_dvd : (5 : ℤ) ∣ C + 2 * B + Q - 1 := by
    rw [show C + 2 * B + Q - 1 =
      (C - 2) + 2 * (B - 1) + (Q - 2) + 5 by ring]
    exact dvd_add
      (dvd_add (dvd_add C_sub_two_dvd (B_sub_one_dvd.mul_left 2)) Q_sub_two_dvd)
      (by norm_num)
  have B_five_unit : ¬(5 : ℤ) ∣ B :=
    not_five_dvd_of_sub_residue B_sub_one_dvd (by norm_num)
  have Q_five_unit : ¬(5 : ℤ) ∣ Q :=
    not_five_dvd_of_sub_residue Q_sub_two_dvd (by norm_num)
  have C_add_Q_five_unit : ¬(5 : ℤ) ∣ C + Q :=
    not_five_dvd_of_sub_residue C_add_Q_sub_four_dvd (by norm_num)
  have two_B_add_Q_five_unit : ¬(5 : ℤ) ∣ 2 * B + Q :=
    not_five_dvd_of_sub_residue two_B_add_Q_sub_four_dvd (by norm_num)
  have triple_five_unit : ¬(5 : ℤ) ∣ C + 2 * B + Q :=
    not_five_dvd_of_sub_residue C_add_two_B_add_Q_sub_one_dvd (by norm_num)
  have residual_difference : R - RAll = H * E * D * 10 ^ d := by
    rw [residual_eq, allC_residual_eq]
    calc
      H * (E * P + G * V) - 10 * μ * G * V -
          (H * (E * PAll + G * V) - 10 * μ * G * V) =
        H * E * (P - PAll) := by ring
      _ = H * E * D * 10 ^ d := by
        rw [show P - PAll = D * 10 ^ d by simpa only [d] using upper_difference_eq]
        ring
  have decomposition :
      45 * R = 10 ^ n * (5 * C) + 10 ^ (2 * β) * B + 10 ^ d * (5 * Q) := by
    calc
      45 * R = 45 * RAll + 45 * (R - RAll) := by ring
      _ = 10 ^ n * (5 * C) + 10 ^ (2 * β) * B + 10 ^ d * (5 * Q) := by
        rw [allC_decomposition, residual_difference]
        dsimp only [Q]
        ring
  have target_deep : (5 : ℤ) ^ (n + β) ∣ R := by
    simpa only [n] using fivePower_dvd_int_of_hasDecimalShell shell
  have product_deep : (5 : ℤ) ^ (n + β + 1) ∣ 45 * R :=
    fivePower_succ_dvd_fortyFive_mul target_deep
  by_cases first_late : prefixWidth = β + 1
  · have n_eq_d : n = d := by
      dsimp only [n, d]
      omega
    rcases lt_trichotomy (tailWidth + 3) β with tail_before | tail_corner | tail_after
    · have reduced : (5 : ℤ) ^ (n + 2) ∣ 45 * R :=
        (pow_dvd_pow (5 : ℤ) (by omega)).trans product_deep
      rw [decomposition] at reduced
      have second_dvd : (5 : ℤ) ^ (n + 2) ∣ 10 ^ (2 * β) * B :=
        dvd_mul_of_dvd_left (fivePower_dvd_tenPower (by
          dsimp only [n]
          omega)) B
      have collided := dvd_sub reduced second_dvd
      rw [show 10 ^ n * (5 * C) + 10 ^ (2 * β) * B + 10 ^ d * (5 * Q) -
          10 ^ (2 * β) * B = 10 ^ n * 5 * (C + Q) by
        rw [← n_eq_d]
        ring] at collided
      exact C_add_Q_five_unit
        (five_dvd_of_pow_add_two_dvd_ten_pow_mul_five collided)
    · have two_beta_eq : 2 * β = n + 1 := by
        dsimp only [n]
        omega
      have reduced : (5 : ℤ) ^ (n + 2) ∣ 45 * R :=
        (pow_dvd_pow (5 : ℤ) (by omega)).trans product_deep
      rw [decomposition] at reduced
      rw [show 10 ^ n * (5 * C) + 10 ^ (2 * β) * B + 10 ^ d * (5 * Q) =
          10 ^ n * 5 * (C + 2 * B + Q) by
        rw [← n_eq_d, two_beta_eq, pow_succ]
        ring] at reduced
      exact triple_five_unit
        (five_dvd_of_pow_add_two_dvd_ten_pow_mul_five reduced)
    · have reduced : (5 : ℤ) ^ (2 * β + 1) ∣ 45 * R :=
        (pow_dvd_pow (5 : ℤ) (by
          dsimp only [n]
          omega)).trans product_deep
      rw [decomposition] at reduced
      have first_dvd : (5 : ℤ) ^ (2 * β + 1) ∣ 10 ^ n * (5 * C) := by
        simpa [mul_assoc] using
          fivePower_succ_dvd_tenPower_mul_five (small := 2 * β) (large := n)
            (by
              dsimp only [n]
              omega) C
      have third_dvd : (5 : ℤ) ^ (2 * β + 1) ∣ 10 ^ d * (5 * Q) := by
        simpa [mul_assoc] using
          fivePower_succ_dvd_tenPower_mul_five (small := 2 * β) (large := d)
            (by rw [← n_eq_d]; dsimp only [n]; omega) Q
      have isolated := dvd_sub (dvd_sub reduced first_dvd) third_dvd
      rw [show 10 ^ n * (5 * C) + 10 ^ (2 * β) * B + 10 ^ d * (5 * Q) -
          10 ^ n * (5 * C) - 10 ^ d * (5 * Q) = 10 ^ (2 * β) * B by ring]
        at isolated
      exact B_five_unit (five_dvd_of_pow_succ_dvd_ten_pow_mul isolated)
  · have d_lt_n : d < n := by
      dsimp only [n, d]
      omega
    rcases lt_trichotomy (tailWidth + 3) β with tail_before | tail_corner | tail_after
    · have reduced : (5 : ℤ) ^ (d + 2) ∣ 45 * R :=
        (pow_dvd_pow (5 : ℤ) (by
          dsimp only [n, d]
          omega)).trans product_deep
      rw [decomposition] at reduced
      have first_dvd : (5 : ℤ) ^ (d + 2) ∣ 10 ^ n * (5 * C) := by
        simpa [mul_assoc] using
          fivePower_succ_dvd_tenPower_mul_five (small := d + 1) (large := n)
            (by omega) C
      have second_dvd : (5 : ℤ) ^ (d + 2) ∣ 10 ^ (2 * β) * B :=
        dvd_mul_of_dvd_left (fivePower_dvd_tenPower (by
          dsimp only [d]
          omega)) B
      have isolated := dvd_sub (dvd_sub reduced first_dvd) second_dvd
      rw [show 10 ^ n * (5 * C) + 10 ^ (2 * β) * B + 10 ^ d * (5 * Q) -
          10 ^ n * (5 * C) - 10 ^ (2 * β) * B = 10 ^ d * 5 * Q by ring]
        at isolated
      exact Q_five_unit
        (five_dvd_of_pow_add_two_dvd_ten_pow_mul_five isolated)
    · have two_beta_eq : 2 * β = d + 1 := by
        dsimp only [d]
        omega
      have reduced : (5 : ℤ) ^ (d + 2) ∣ 45 * R :=
        (pow_dvd_pow (5 : ℤ) (by
          dsimp only [n, d]
          omega)).trans product_deep
      rw [decomposition] at reduced
      have first_dvd : (5 : ℤ) ^ (d + 2) ∣ 10 ^ n * (5 * C) := by
        simpa [mul_assoc] using
          fivePower_succ_dvd_tenPower_mul_five (small := d + 1) (large := n)
            (by omega) C
      have collided := dvd_sub reduced first_dvd
      rw [show 10 ^ n * (5 * C) + 10 ^ (2 * β) * B + 10 ^ d * (5 * Q) -
          10 ^ n * (5 * C) = 10 ^ d * 5 * (2 * B + Q) by
        rw [two_beta_eq, pow_succ]
        ring] at collided
      exact two_B_add_Q_five_unit
        (five_dvd_of_pow_add_two_dvd_ten_pow_mul_five collided)
    · have reduced : (5 : ℤ) ^ (2 * β + 1) ∣ 45 * R :=
        (pow_dvd_pow (5 : ℤ) (by
          dsimp only [n]
          omega)).trans product_deep
      rw [decomposition] at reduced
      have first_dvd : (5 : ℤ) ^ (2 * β + 1) ∣ 10 ^ n * (5 * C) := by
        have d_lt_n_expanded : tailWidth + β + 2 < n := by
          simpa only [d] using d_lt_n
        simpa [mul_assoc] using
          fivePower_succ_dvd_tenPower_mul_five (small := 2 * β) (large := n)
            (by omega) C
      have third_dvd : (5 : ℤ) ^ (2 * β + 1) ∣ 10 ^ d * (5 * Q) := by
        simpa [mul_assoc] using
          fivePower_succ_dvd_tenPower_mul_five (small := 2 * β) (large := d)
            (by
              dsimp only [d]
              omega) Q
      have isolated := dvd_sub (dvd_sub reduced first_dvd) third_dvd
      rw [show 10 ^ n * (5 * C) + 10 ^ (2 * β) * B + 10 ^ d * (5 * Q) -
          10 ^ n * (5 * C) - 10 ^ d * (5 * Q) = 10 ^ (2 * β) * B by ring]
        at isolated
      exact B_five_unit (five_dvd_of_pow_succ_dvd_ten_pow_mul isolated)

/-- Changing an all-`D_c` punctuated upper code only above five-adic width `n` cannot create
the deeper multi-role shell missing from the all-`D_c` raw residual. -/
theorem aboveWidthUpperPerturbation_peeledDoubleCHead_shell_impossible
    {β n : Nat} (tail : List TagLetter) {μ E G PAll P V RAll R : ℤ}
    (β_large : 2 ≤ β) (n_positive : 1 ≤ n)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: tail)) : ℚ) 0 0)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (allC_upper_eq : 9 * PAll = 50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7)
    (lower_eq : 9 * V = 7 * 10 ^ n - 7)
    (allC_residual_eq :
      RAll = (code (peeledHeadWord β (.c :: .c :: tail)) : ℤ) *
          (E * PAll + G * V) - 10 * μ * G * V)
    (upper_difference_deep : (5 : ℤ) ^ (n + 1) ∣ P - PAll)
    (residual_eq :
      R = (code (peeledHeadWord β (.c :: .c :: tail)) : ℤ) *
          (E * P + G * V) - 10 * μ * G * V)
    (shell : HasDecimalShell (R : ℚ) (n + β) (n + β)) :
    False := by
  let H : ℤ := code (peeledHeadWord β (.c :: .c :: tail))
  have allC_not_deep : ¬(5 : ℤ) ^ (n + 1) ∣ RAll := by
    refine allCDeletion_peeledDoubleCHead_not_fiveAboveWidth
      (T := E * PAll + G * V) (R := RAll) tail β_large n_positive
        head_unit mu_eq gap_eq lift_eq allC_upper_eq lower_eq ?_ ?_
    · rfl
    · simpa only [H] using allC_residual_eq
  have residual_difference : R - RAll = H * E * (P - PAll) := by
    rw [residual_eq, allC_residual_eq]
    dsimp only [H]
    ring
  have perturbation_deep : (5 : ℤ) ^ (n + 1) ∣ R - RAll := by
    rw [residual_difference]
    exact upper_difference_deep.mul_left (H * E)
  have target_deep : (5 : ℤ) ^ (n + β) ∣ R :=
    fivePower_dvd_int_of_hasDecimalShell shell
  have residual_deep : (5 : ℤ) ^ (n + 1) ∣ R :=
    (pow_dvd_pow (5 : ℤ) (by omega)).trans target_deep
  have allC_deep : (5 : ℤ) ^ (n + 1) ∣ RAll := by
    have isolated := dvd_sub residual_deep perturbation_deep
    simpa only [sub_sub_cancel] using isolated
  exact allC_not_deep allC_deep

/-- At a regular raw head, any upper-code perturbation invisible modulo `5^β` preserves the
all-`D_c` obstruction, independently of its position in the role word. -/
theorem betaDeepUpperPerturbation_regularRawHead_shell_impossible
    {β s n : Nat} {H μ E G PAll P V RAll R : ℤ}
    (s_positive : 1 ≤ s) (suffix_below : s + 2 ≤ β) (n_positive : 1 ≤ n)
    (head_eq : 9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ s - 7)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (allC_upper_eq : 9 * PAll = 50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7)
    (lower_eq : 9 * V = 7 * 10 ^ n - 7)
    (allC_residual_eq : RAll = H * (E * PAll + G * V) - 10 * μ * G * V)
    (upper_difference_deep : (5 : ℤ) ^ β ∣ P - PAll)
    (residual_eq : R = H * (E * P + G * V) - 10 * μ * G * V)
    (shell : HasDecimalShell (R : ℚ) (n + β) (n + β)) :
    False := by
  have allC_not_deep : ¬(5 : ℤ) ^ β ∣ RAll := by
    refine allCDeletion_regularRawHead_not_fiveAtBeta s_positive suffix_below n_positive
      head_eq mu_eq gap_eq lift_eq allC_upper_eq lower_eq ?_ allC_residual_eq
    rfl
  have residual_difference : R - RAll = H * E * (P - PAll) := by
    rw [residual_eq, allC_residual_eq]
    ring
  have perturbation_deep : (5 : ℤ) ^ β ∣ R - RAll := by
    rw [residual_difference]
    exact upper_difference_deep.mul_left (H * E)
  have target_deep : (5 : ℤ) ^ (n + β) ∣ R :=
    fivePower_dvd_int_of_hasDecimalShell shell
  have residual_deep : (5 : ℤ) ^ β ∣ R :=
    (pow_dvd_pow (5 : ℤ) (by omega)).trans target_deep
  have allC_deep : (5 : ℤ) ^ β ∣ RAll := by
    have isolated := dvd_sub residual_deep perturbation_deep
    simpa only [sub_sub_cancel] using isolated
  exact allC_not_deep allC_deep

/-- Prefixing an all-`D_c` upper word by the marker-scale `D_b` perturbation cannot create the
deeper multi-role shell. The conclusion holds at every positive erasure width. -/
theorem leadingBDeletion_peeledDoubleCHead_shell_impossible
    {β n : Nat} (tail : List TagLetter) {μ E G PAll PB V RAll RB : ℤ}
    (β_large : 2 ≤ β) (n_positive : 1 ≤ n)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: tail)) : ℚ) 0 0)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (allC_upper_eq : 9 * PAll = 50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7)
    (lower_eq : 9 * V = 7 * 10 ^ n - 7)
    (allC_residual_eq :
      RAll = (code (peeledHeadWord β (.c :: .c :: tail)) : ℤ) *
          (E * PAll + G * V) - 10 * μ * G * V)
    (leadingB_upper_eq : PB = PAll + μ * 10 ^ (n + β + 1))
    (leadingB_residual_eq :
      RB = (code (peeledHeadWord β (.c :: .c :: tail)) : ℤ) *
          (E * PB + G * V) - 10 * μ * G * V)
    (shell : HasDecimalShell (RB : ℚ) (n + β) (n + β)) :
    False := by
  apply aboveWidthUpperPerturbation_peeledDoubleCHead_shell_impossible
    (PAll := PAll) (P := PB) (RAll := RAll) (R := RB) tail β_large n_positive
      head_unit mu_eq gap_eq lift_eq allC_upper_eq lower_eq allC_residual_eq
  · rw [leadingB_upper_eq]
    have power_dvd : (5 : ℤ) ^ (n + 1) ∣ 10 ^ (n + β + 1) :=
      fivePower_dvd_tenPower (by omega)
    simpa using power_dvd.mul_left μ
  · exact leadingB_residual_eq
  · exact shell

end MatrixMortality.DecimalSetterDepth
