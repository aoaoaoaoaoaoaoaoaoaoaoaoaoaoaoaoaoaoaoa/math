import MatrixMortality.DecimalSetterRuleResonance

/-!
# Decimal setter rule coefficients

The exceptional rightmost-rule grammar has equal five-depth arms.  This module retains the
normalized leading residue on each arm: the all-`D_c` base contributes `2` or `4`, while both
the rightmost-`b` and phase perturbations contribute `2`, after the common power of two is
removed.  No nonempty subset of these coefficients vanishes modulo five.
-/

namespace MatrixMortality.DecimalSetterRuleCoefficient

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterAncestry
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterChamber
open MatrixMortality.DecimalSetterDepth
open MatrixMortality.DecimalSetterPhase
open MatrixMortality.DecimalSetterRuleResonance
open MatrixMortality.PadicValuation

private instance factPrimeFive : Fact (Nat.Prime 5) :=
  ⟨by norm_num⟩

/-- An integer with a prescribed five-power factor and prescribed normalized residue modulo
five. -/
def HasFiveLeadingResidue (value : ℤ) (depth : Nat) (residue : ℤ) : Prop :=
  ∃ coefficient : ℤ,
    value = 5 ^ depth * coefficient ∧ coefficient ≡ residue [ZMOD 5]

namespace HasFiveLeadingResidue

theorem add
    {left right : ℤ} {depth : Nat} {leftResidue rightResidue : ℤ}
    (left_lead : HasFiveLeadingResidue left depth leftResidue)
    (right_lead : HasFiveLeadingResidue right depth rightResidue) :
    HasFiveLeadingResidue (left + right) depth (leftResidue + rightResidue) := by
  obtain ⟨leftCoefficient, left_eq, left_mod⟩ := left_lead
  obtain ⟨rightCoefficient, right_eq, right_mod⟩ := right_lead
  refine ⟨leftCoefficient + rightCoefficient, ?_, left_mod.add right_mod⟩
  rw [left_eq, right_eq]
  ring

theorem hasValue
    {value : ℤ} {depth : Nat} {residue : ℤ}
    (lead : HasFiveLeadingResidue value depth residue)
    (residue_unit : ¬(5 : ℤ) ∣ residue) :
    HasValue 5 (value : ℚ) depth := by
  obtain ⟨coefficient, value_eq, coefficient_mod⟩ := lead
  have coefficient_unit : ¬(5 : ℤ) ∣ coefficient := by
    intro coefficient_dvd
    have residue_dvd : (5 : ℤ) ∣ residue := by
      rw [Int.modEq_iff_dvd] at coefficient_mod
      simpa using dvd_add coefficient_dvd coefficient_mod
    exact residue_unit residue_dvd
  have power_value : HasValue 5 ((5 : ℚ) ^ depth) depth :=
    primePower_hasValue depth
  have coefficient_value : HasValue 5 (coefficient : ℚ) 0 :=
    intCast_isUnit_of_not_dvd coefficient_unit
  rw [value_eq]
  push_cast
  simpa using mul_hasValue power_value coefficient_value

end HasFiveLeadingResidue

private theorem twoPower_mul_not_five_dvd
    (depth : Nat) {coefficient : ℤ} (coefficient_unit : ¬(5 : ℤ) ∣ coefficient) :
    ¬(5 : ℤ) ∣ 2 ^ depth * coefficient := by
  intro product_dvd
  have coprime : IsCoprime (5 : ℤ) (2 ^ depth) :=
    (by norm_num : IsCoprime (5 : ℤ) 2).pow_right
  exact coefficient_unit (coprime.dvd_of_dvd_mul_left product_dvd)

private theorem twoPower_add_not_five_dvd
    (depth : Nat) (left right : ℤ)
    (sum_unit : ¬(5 : ℤ) ∣ left + right) :
    ¬(5 : ℤ) ∣ 2 ^ depth * left + 2 ^ depth * right := by
  rw [← mul_add]
  exact twoPower_mul_not_five_dvd depth sum_unit

private theorem twoPower_triple_not_five_dvd
    (depth : Nat) (first second third : ℤ)
    (sum_unit : ¬(5 : ℤ) ∣ first + second + third) :
    ¬(5 : ℤ) ∣ 2 ^ depth * first + 2 ^ depth * second + 2 ^ depth * third := by
  rw [show 2 ^ depth * first + 2 ^ depth * second + 2 ^ depth * third =
    2 ^ depth * (first + second + third) by ring]
  exact twoPower_mul_not_five_dvd depth sum_unit

/-- Three exceptional scaled summands with the physical leading residues always have the
minimum of their three displayed depths.  Equal-depth collisions cannot deepen the sum. -/
theorem exceptionalThreeLead_hasValue
    {base upper phase : ℤ} {baseDepth upperDepth phaseDepth : Nat}
    {baseCoefficient : ℤ}
    (base_coefficient : baseCoefficient = 2 ∨ baseCoefficient = 4)
    (base_lead :
      HasFiveLeadingResidue base (baseDepth + 1) (2 ^ baseDepth * baseCoefficient))
    (upper_lead :
      HasFiveLeadingResidue upper (upperDepth + 1) (2 ^ upperDepth * 2))
    (phase_lead :
      HasFiveLeadingResidue phase (phaseDepth + 1) (2 ^ phaseDepth * 2)) :
    HasValue 5 ((base + upper + phase : ℤ) : ℚ)
      (((min baseDepth (min upperDepth phaseDepth) : Nat) + 1 : Nat) : ℤ) := by
  rcases base_coefficient with rfl | rfl
  · have base_value := base_lead.hasValue
      (twoPower_mul_not_five_dvd baseDepth (by norm_num : ¬(5 : ℤ) ∣ 2))
    have upper_value := upper_lead.hasValue
      (twoPower_mul_not_five_dvd upperDepth (by norm_num : ¬(5 : ℤ) ∣ 2))
    have phase_value := phase_lead.hasValue
      (twoPower_mul_not_five_dvd phaseDepth (by norm_num : ¬(5 : ℤ) ∣ 2))
    rcases lt_trichotomy baseDepth upperDepth with base_upper | base_upper | upper_base
    · have base_upper_value := add_hasValue_left base_value upper_value (by omega)
      rcases lt_trichotomy baseDepth phaseDepth with base_phase | base_phase | phase_base
      · have minimum_eq : min baseDepth (min upperDepth phaseDepth) = baseDepth := by omega
        rw [minimum_eq]
        simpa using add_hasValue_left base_upper_value phase_value (by omega)
      · subst phaseDepth
        have collision := base_lead.add phase_lead
        have collision_value := collision.hasValue
          (twoPower_add_not_five_dvd baseDepth 2 2 (by norm_num))
        have total := add_hasValue_left collision_value upper_value (by omega)
        have minimum_eq : min baseDepth (min upperDepth baseDepth) = baseDepth := by omega
        rw [show base + upper + phase = (base + phase) + upper by ring]
        rw [minimum_eq]
        simpa using total
      · have total := add_hasValue_right base_upper_value phase_value (by omega)
        have minimum_eq : min baseDepth (min upperDepth phaseDepth) = phaseDepth := by omega
        rw [minimum_eq]
        simpa using total
    · subst upperDepth
      have collision := base_lead.add upper_lead
      have collision_value := collision.hasValue
        (twoPower_add_not_five_dvd baseDepth 2 2 (by norm_num))
      rcases lt_trichotomy baseDepth phaseDepth with base_phase | base_phase | phase_base
      · have minimum_eq : min baseDepth (min baseDepth phaseDepth) = baseDepth := by omega
        rw [minimum_eq]
        simpa using add_hasValue_left collision_value phase_value (by omega)
      · subst phaseDepth
        have triple := collision.add phase_lead
        have minimum_eq : min baseDepth (min baseDepth baseDepth) = baseDepth := by omega
        rw [minimum_eq]
        simpa using triple.hasValue
          (twoPower_triple_not_five_dvd baseDepth 2 2 2 (by norm_num))
      · have minimum_eq : min baseDepth (min baseDepth phaseDepth) = phaseDepth := by omega
        rw [minimum_eq]
        simpa using add_hasValue_right collision_value phase_value (by omega)
    · have base_upper_value := add_hasValue_right base_value upper_value (by omega)
      rcases lt_trichotomy upperDepth phaseDepth with upper_phase | upper_phase | phase_upper
      · have minimum_eq : min baseDepth (min upperDepth phaseDepth) = upperDepth := by omega
        rw [minimum_eq]
        simpa using add_hasValue_left base_upper_value phase_value (by omega)
      · subst phaseDepth
        have collision := upper_lead.add phase_lead
        have collision_value := collision.hasValue
          (twoPower_add_not_five_dvd upperDepth 2 2 (by norm_num))
        have total := add_hasValue_right base_value collision_value (by omega)
        have minimum_eq : min baseDepth (min upperDepth upperDepth) = upperDepth := by omega
        rw [show base + upper + phase = base + (upper + phase) by ring]
        rw [minimum_eq]
        simpa using total
      · have total := add_hasValue_right base_upper_value phase_value (by omega)
        have minimum_eq : min baseDepth (min upperDepth phaseDepth) = phaseDepth := by omega
        rw [minimum_eq]
        simpa using total
  · have base_value := base_lead.hasValue
      (twoPower_mul_not_five_dvd baseDepth (by norm_num : ¬(5 : ℤ) ∣ 4))
    have upper_value := upper_lead.hasValue
      (twoPower_mul_not_five_dvd upperDepth (by norm_num : ¬(5 : ℤ) ∣ 2))
    have phase_value := phase_lead.hasValue
      (twoPower_mul_not_five_dvd phaseDepth (by norm_num : ¬(5 : ℤ) ∣ 2))
    rcases lt_trichotomy baseDepth upperDepth with base_upper | base_upper | upper_base
    · have base_upper_value := add_hasValue_left base_value upper_value (by omega)
      rcases lt_trichotomy baseDepth phaseDepth with base_phase | base_phase | phase_base
      · have minimum_eq : min baseDepth (min upperDepth phaseDepth) = baseDepth := by omega
        rw [minimum_eq]
        simpa using add_hasValue_left base_upper_value phase_value (by omega)
      · subst phaseDepth
        have collision := base_lead.add phase_lead
        have collision_value := collision.hasValue
          (twoPower_add_not_five_dvd baseDepth 4 2 (by norm_num))
        have total := add_hasValue_left collision_value upper_value (by omega)
        have minimum_eq : min baseDepth (min upperDepth baseDepth) = baseDepth := by omega
        rw [show base + upper + phase = (base + phase) + upper by ring]
        rw [minimum_eq]
        simpa using total
      · have total := add_hasValue_right base_upper_value phase_value (by omega)
        have minimum_eq : min baseDepth (min upperDepth phaseDepth) = phaseDepth := by omega
        rw [minimum_eq]
        simpa using total
    · subst upperDepth
      have collision := base_lead.add upper_lead
      have collision_value := collision.hasValue
        (twoPower_add_not_five_dvd baseDepth 4 2 (by norm_num))
      rcases lt_trichotomy baseDepth phaseDepth with base_phase | base_phase | phase_base
      · have minimum_eq : min baseDepth (min baseDepth phaseDepth) = baseDepth := by omega
        rw [minimum_eq]
        simpa using add_hasValue_left collision_value phase_value (by omega)
      · subst phaseDepth
        have triple := collision.add phase_lead
        have minimum_eq : min baseDepth (min baseDepth baseDepth) = baseDepth := by omega
        rw [minimum_eq]
        simpa using triple.hasValue
          (twoPower_triple_not_five_dvd baseDepth 4 2 2 (by norm_num))
      · have minimum_eq : min baseDepth (min baseDepth phaseDepth) = phaseDepth := by omega
        rw [minimum_eq]
        simpa using add_hasValue_right collision_value phase_value (by omega)
    · have base_upper_value := add_hasValue_right base_value upper_value (by omega)
      rcases lt_trichotomy upperDepth phaseDepth with upper_phase | upper_phase | phase_upper
      · have minimum_eq : min baseDepth (min upperDepth phaseDepth) = upperDepth := by omega
        rw [minimum_eq]
        simpa using add_hasValue_left base_upper_value phase_value (by omega)
      · subst phaseDepth
        have collision := upper_lead.add phase_lead
        have collision_value := collision.hasValue
          (twoPower_add_not_five_dvd upperDepth 2 2 (by norm_num))
        have total := add_hasValue_right base_value collision_value (by omega)
        have minimum_eq : min baseDepth (min upperDepth upperDepth) = upperDepth := by omega
        rw [show base + upper + phase = base + (upper + phase) by ring]
        rw [minimum_eq]
        simpa using total
      · have total := add_hasValue_right base_upper_value phase_value (by omega)
        have minimum_eq : min baseDepth (min upperDepth phaseDepth) = phaseDepth := by omega
        rw [minimum_eq]
        simpa using total

private theorem tenPower_eq_fivePower_mul_twoPower (depth : Nat) :
    (10 : ℤ) ^ depth = 5 ^ depth * 2 ^ depth := by
  rw [show (10 : ℤ) = 5 * 2 by norm_num, mul_pow]

private theorem tenPower_factor_five
    {small large : Nat} (bound : small ≤ large) :
    (10 : ℤ) ^ large = 5 ^ small * (5 ^ (large - small) * 2 ^ large) := by
  have exponent_eq : small + (large - small) = large := by omega
  have power_eq : (5 : ℤ) ^ large = 5 ^ small * 5 ^ (large - small) := by
    rw [← pow_add, exponent_eq]
  rw [tenPower_eq_fivePower_mul_twoPower, power_eq]
  ring

private theorem tenPower_mul_five_factor
    {small large : Nat} (bound : small ≤ large + 1) (coefficient : ℤ) :
    (10 : ℤ) ^ large * (5 * coefficient) =
      5 ^ small * (5 ^ (large + 1 - small) * 2 ^ large * coefficient) := by
  have exponent_eq : small + (large + 1 - small) = large + 1 := by omega
  have power_eq : (5 : ℤ) ^ large * 5 =
      5 ^ small * 5 ^ (large + 1 - small) := by
    rw [← pow_succ, ← pow_add, exponent_eq]
  rw [tenPower_eq_fivePower_mul_twoPower]
  rw [show 5 ^ large * 2 ^ large * (5 * coefficient) =
    (5 ^ large * 5) * 2 ^ large * coefficient by ring, power_eq]
  ring

/-- The scaled exceptional all-`D_c` residual retains a normalized leading residue.  Away
from the collision `n=2β-1` it is `2`; at the collision the two arms add to `4`. -/
theorem exceptionalAllC_scaled_lead
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
    ∃ baseCoefficient : ℤ,
      (baseCoefficient = 2 ∨ baseCoefficient = 4) ∧
      HasFiveLeadingResidue (45 * R) (min n (2 * β - 1) + 1)
        (2 ^ min n (2 * β - 1) * baseCoefficient) := by
  obtain ⟨C, B, decomposition, C_sub_two_dvd, B_sub_one_dvd⟩ :=
    allCDeletion_firstRawHead_residueNormalForm β_large head_eq mu_eq gap_eq lift_eq
      upper_eq lower_eq trace_eq residual_eq
  have C_mod : C ≡ 2 [ZMOD 5] :=
    (Int.modEq_iff_dvd.mpr C_sub_two_dvd).symm
  have B_mod : B ≡ 1 [ZMOD 5] :=
    (Int.modEq_iff_dvd.mpr B_sub_one_dvd).symm
  let frontier := 2 * β - 1
  rcases lt_trichotomy n frontier with width_shallow | collision | frontier_shallow
  · have minimum_eq : min n frontier = n := min_eq_left (by omega)
    let remainder := 2 * β - (n + 1)
    have remainder_positive : 1 ≤ remainder := by
      dsimp only [frontier, remainder] at width_shallow ⊢
      omega
    have exponent_eq : 2 * β = (n + 1) + remainder := by
      dsimp only [frontier, remainder] at width_shallow ⊢
      omega
    let coefficient : ℤ :=
      2 ^ n * C + 5 ^ remainder * 2 ^ (2 * β) * B
    have factorization : 45 * R = 5 ^ (n + 1) * coefficient := by
      rw [decomposition,
        tenPower_mul_five_factor (small := n + 1) (by omega) C,
        tenPower_factor_five (small := n + 1) (by omega)]
      dsimp only [coefficient]
      rw [show 2 * β - (n + 1) = remainder by rfl]
      simp only [Nat.sub_self, pow_zero]
      ring
    have remainder_dvd : (5 : ℤ) ∣ 5 ^ remainder := by
      simpa using pow_dvd_pow (5 : ℤ) remainder_positive
    have second_mod :
        5 ^ remainder * 2 ^ (2 * β) * B ≡ 0 [ZMOD 5] :=
      by simpa [mul_assoc] using
        (remainder_dvd.mul_right (2 ^ (2 * β) * B)).modEq_zero_int
    have coefficient_mod : coefficient ≡ 2 ^ n * 2 [ZMOD 5] := by
      dsimp only [coefficient]
      exact ((Int.ModEq.refl (2 ^ n)).mul C_mod).add second_mod
    refine ⟨2, Or.inl rfl, ?_⟩
    rw [minimum_eq]
    exact ⟨coefficient, factorization, coefficient_mod⟩
  · subst frontier
    have frontier_eq : 2 * β = n + 1 := by omega
    have minimum_eq : min n n = n := min_self n
    let coefficient : ℤ := 2 ^ n * (C + 2 * B)
    have factorization : 45 * R = 5 ^ (n + 1) * coefficient := by
      rw [decomposition,
        tenPower_mul_five_factor (small := n + 1) (by omega) C,
        tenPower_factor_five (small := n + 1) (by omega), frontier_eq]
      dsimp only [coefficient]
      simp only [Nat.sub_self, pow_zero]
      ring
    have inner_mod : C + 2 * B ≡ 4 [ZMOD 5] := by
      simpa using C_mod.add ((Int.ModEq.refl (2 : ℤ)).mul B_mod)
    have coefficient_mod : coefficient ≡ 2 ^ n * 4 [ZMOD 5] := by
      dsimp only [coefficient]
      exact (Int.ModEq.refl (2 ^ n)).mul inner_mod
    refine ⟨4, Or.inr rfl, ?_⟩
    simpa [collision] using
      (show HasFiveLeadingResidue (45 * R) (n + 1) (2 ^ n * 4) from
        ⟨coefficient, factorization, coefficient_mod⟩)
  · have minimum_eq : min n frontier = frontier := min_eq_right (by omega)
    let remainder := n + 1 - 2 * β
    have remainder_positive : 1 ≤ remainder := by
      dsimp only [frontier, remainder] at frontier_shallow ⊢
      omega
    have exponent_eq : n + 1 = 2 * β + remainder := by
      dsimp only [frontier, remainder] at frontier_shallow ⊢
      omega
    have frontier_succ : frontier + 1 = 2 * β := by
      dsimp only [frontier]
      omega
    let coefficient : ℤ :=
      5 ^ remainder * 2 ^ n * C + 2 ^ (2 * β) * B
    have factorization : 45 * R = 5 ^ (frontier + 1) * coefficient := by
      rw [decomposition, frontier_succ,
        tenPower_mul_five_factor (small := 2 * β) (by omega) C,
        tenPower_factor_five (small := 2 * β) le_rfl]
      dsimp only [coefficient]
      rw [show n + 1 - 2 * β = remainder by rfl]
      simp only [Nat.sub_self, pow_zero]
      ring
    have remainder_dvd : (5 : ℤ) ∣ 5 ^ remainder := by
      simpa using pow_dvd_pow (5 : ℤ) remainder_positive
    have first_mod : 5 ^ remainder * 2 ^ n * C ≡ 0 [ZMOD 5] :=
      by simpa [mul_assoc] using
        (remainder_dvd.mul_right (2 ^ n * C)).modEq_zero_int
    have second_mod : 2 ^ (2 * β) * B ≡ 2 ^ frontier * 2 [ZMOD 5] := by
      have power_eq : (2 : ℤ) ^ (2 * β) = 2 ^ frontier * 2 := by
        rw [← frontier_succ, pow_succ]
      rw [power_eq]
      simpa using (Int.ModEq.refl (2 ^ frontier * 2)).mul B_mod
    have coefficient_mod : coefficient ≡ 2 ^ frontier * 2 [ZMOD 5] := by
      dsimp only [coefficient]
      simpa using first_mod.add second_mod
    refine ⟨2, Or.inl rfl, ?_⟩
    rw [minimum_eq]
    exact ⟨coefficient, factorization, coefficient_mod⟩

/-- At the exceptional raw head, the scaled rightmost-`b` upper perturbation has normalized
leading residue `2`. -/
theorem exceptionalUpper_scaled_lead
    {β depth : Nat} {H E D difference : ℤ}
    (β_large : 2 ≤ β)
    (head_eq : 9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ (β - 1) - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (D_sub_two_dvd : (5 : ℤ) ∣ D - 2)
    (difference_eq : difference = H * E * D * 10 ^ depth) :
    HasFiveLeadingResidue (45 * difference) (depth + 1) (2 ^ depth * 2) := by
  have head_scaled_eq :
      9 * (H - 2) = 5 * 10 ^ (β + 2) + 2 * 10 ^ (β - 1) - 25 := by
    linear_combination head_eq
  have five_dvd_ten_beta_sub_one : (5 : ℤ) ∣ 10 ^ (β - 1) := by
    have exponent_positive : 1 ≤ β - 1 := by omega
    exact (pow_dvd_pow (5 : ℤ) exponent_positive).trans
      (pow_dvd_pow_of_dvd (by norm_num : (5 : ℤ) ∣ 10) (β - 1))
  have head_scaled_dvd : (5 : ℤ) ∣ 9 * (H - 2) := by
    rw [head_scaled_eq]
    exact dvd_sub
      (dvd_add (dvd_mul_right 5 _) (five_dvd_ten_beta_sub_one.mul_left 2))
      (by norm_num)
  have H_sub_two_dvd : (5 : ℤ) ∣ H - 2 :=
    (by norm_num : IsCoprime (5 : ℤ) 9).dvd_of_dvd_mul_left head_scaled_dvd
  have E_sub_two_dvd : (5 : ℤ) ∣ E - 2 := by
    have ten_dvd : (5 : ℤ) ∣ 10 ^ β := by
      have β_positive : 1 ≤ β := by omega
      exact (pow_dvd_pow (5 : ℤ) β_positive).trans
        (pow_dvd_pow_of_dvd (by norm_num : (5 : ℤ) ∣ 10) β)
    rw [gap_eq]
    have first_dvd : (5 : ℤ) ∣ 18 * 10 ^ β := ten_dvd.mul_left 18
    have constant_dvd : (5 : ℤ) ∣ (-63 : ℤ) - 2 := by norm_num
    simpa [sub_eq_add_neg, add_assoc] using dvd_add first_dvd constant_dvd
  have H_mod : H ≡ 2 [ZMOD 5] :=
    (Int.modEq_iff_dvd.mpr H_sub_two_dvd).symm
  have E_mod : E ≡ 2 [ZMOD 5] :=
    (Int.modEq_iff_dvd.mpr E_sub_two_dvd).symm
  have D_mod : D ≡ 2 [ZMOD 5] :=
    (Int.modEq_iff_dvd.mpr D_sub_two_dvd).symm
  let coefficient : ℤ := 9 * H * E * D * 2 ^ depth
  have factorization : 45 * difference = 5 ^ (depth + 1) * coefficient := by
    rw [difference_eq, tenPower_eq_fivePower_mul_twoPower, pow_succ]
    dsimp only [coefficient]
    ring
  have unit_mod : 9 * H * E * D ≡ 2 [ZMOD 5] := by
    calc
      9 * H * E * D ≡ 9 * 2 * 2 * 2 [ZMOD 5] :=
        (((Int.ModEq.refl (9 : ℤ)).mul H_mod).mul E_mod).mul D_mod
      _ ≡ 2 [ZMOD 5] := by norm_num
  have coefficient_mod : coefficient ≡ 2 ^ depth * 2 [ZMOD 5] := by
    dsimp only [coefficient]
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      unit_mod.mul (Int.ModEq.refl (2 ^ depth))
  exact ⟨coefficient, factorization, coefficient_mod⟩

private theorem modFiveHundredFifty_factor
    {coefficient : ℤ} (coefficient_mod : coefficient ≡ 550 [ZMOD 1000]) :
    ∃ quotient : ℤ, coefficient = 25 * quotient ∧ quotient ≡ 2 [ZMOD 5] := by
  rw [Int.modEq_iff_dvd] at coefficient_mod
  obtain ⟨carry, carry_eq⟩ := coefficient_mod
  refine ⟨22 - 40 * carry, by omega, ?_⟩
  rw [Int.modEq_iff_dvd]
  refine ⟨-4 + 8 * carry, by ring⟩

private theorem modFourHundredEighty_factor
    {coefficient : ℤ} (coefficient_mod : coefficient ≡ 480 [ZMOD 1000]) :
    ∃ quotient : ℤ, coefficient = 5 * quotient ∧ quotient ≡ 1 [ZMOD 5] := by
  rw [Int.modEq_iff_dvd] at coefficient_mod
  obtain ⟨carry, carry_eq⟩ := coefficient_mod
  refine ⟨96 - 200 * carry, by omega, ?_⟩
  rw [Int.modEq_iff_dvd]
  refine ⟨-19 + 40 * carry, by ring⟩

private theorem modSevenHundredEighty_factor
    {coefficient : ℤ} (coefficient_mod : coefficient ≡ 780 [ZMOD 1000]) :
    ∃ quotient : ℤ, coefficient = 5 * quotient ∧ quotient ≡ 1 [ZMOD 5] := by
  rw [Int.modEq_iff_dvd] at coefficient_mod
  obtain ⟨carry, carry_eq⟩ := coefficient_mod
  refine ⟨156 - 200 * carry, by omega, ?_⟩
  rw [Int.modEq_iff_dvd]
  refine ⟨-31 + 40 * carry, by ring⟩

private theorem scaledPhase_lead_of_factor
    {tailDepth factorDepth : Nat} {G headGap phaseCoefficient quotient difference : ℤ}
    (coefficient_eq : phaseCoefficient = 5 ^ factorDepth * quotient)
    (unit_mod : 9 * G * headGap * quotient ≡ 2 ^ factorDepth * 2 [ZMOD 5])
    (difference_eq :
      difference = G * headGap * (phaseCoefficient * 10 ^ tailDepth)) :
    HasFiveLeadingResidue (45 * difference) (tailDepth + factorDepth + 1)
      (2 ^ (tailDepth + factorDepth) * 2) := by
  let normalized : ℤ := 9 * G * headGap * quotient * 2 ^ tailDepth
  have power_eq : (5 : ℤ) ^ (tailDepth + factorDepth + 1) =
      5 * 5 ^ factorDepth * 5 ^ tailDepth := by
    rw [show tailDepth + factorDepth + 1 = 1 + factorDepth + tailDepth by omega,
      pow_add, pow_add]
    norm_num
  have factorization : 45 * difference =
      5 ^ (tailDepth + factorDepth + 1) * normalized := by
    rw [difference_eq, coefficient_eq, tenPower_eq_fivePower_mul_twoPower, power_eq]
    dsimp only [normalized]
    ring
  have normalized_mod : normalized ≡ 2 ^ (tailDepth + factorDepth) * 2 [ZMOD 5] := by
    have product_mod := unit_mod.mul (Int.ModEq.refl (2 ^ tailDepth))
    dsimp only [normalized]
    rw [pow_add]
    simpa [mul_assoc, mul_comm, mul_left_comm] using product_mod
  exact ⟨normalized, factorization, normalized_mod⟩

private theorem exceptionalHead_mod_two
    {β : Nat} {H : ℤ} (β_large : 2 ≤ β)
    (head_eq : 9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ (β - 1) - 7) :
    H ≡ 2 [ZMOD 5] := by
  have scaled_eq :
      9 * (H - 2) = 5 * 10 ^ (β + 2) + 2 * 10 ^ (β - 1) - 25 := by
    linear_combination head_eq
  have five_dvd_ten_beta_sub_one : (5 : ℤ) ∣ 10 ^ (β - 1) := by
    have exponent_positive : 1 ≤ β - 1 := by omega
    exact (pow_dvd_pow (5 : ℤ) exponent_positive).trans
      (pow_dvd_pow_of_dvd (by norm_num : (5 : ℤ) ∣ 10) (β - 1))
  have scaled_dvd : (5 : ℤ) ∣ 9 * (H - 2) := by
    rw [scaled_eq]
    exact dvd_sub
      (dvd_add (dvd_mul_right 5 _) (five_dvd_ten_beta_sub_one.mul_left 2))
      (by norm_num)
  have head_dvd : (5 : ℤ) ∣ H - 2 :=
    (by norm_num : IsCoprime (5 : ℤ) 9).dvd_of_dvd_mul_left scaled_dvd
  exact (Int.modEq_iff_dvd.mpr head_dvd).symm

private theorem calibratedLift_mod_three
    {β : Nat} {G : ℤ} (β_positive : 1 ≤ β)
    (lift_eq : G = 502 * 10 ^ β - 7) :
    G ≡ 3 [ZMOD 5] := by
  have ten_dvd : (5 : ℤ) ∣ 10 ^ β :=
    (pow_dvd_pow (5 : ℤ) β_positive).trans
      (pow_dvd_pow_of_dvd (by norm_num : (5 : ℤ) ∣ 10) β)
  have difference_dvd : (5 : ℤ) ∣ G - 3 := by
    obtain ⟨quotient, quotient_eq⟩ := ten_dvd
    refine ⟨502 * quotient - 2, ?_⟩
    rw [lift_eq, quotient_eq]
    ring
  exact (Int.modEq_iff_dvd.mpr difference_dvd).symm

private theorem exceptionalHeadGap_mod_two
    {H μ : ℤ} (H_mod : H ≡ 2 [ZMOD 5]) :
    H - 10 * μ ≡ 2 [ZMOD 5] := by
  have scaled_mod : 10 * μ ≡ 0 [ZMOD 5] := by
    simpa using ((by norm_num : (10 : ℤ) ≡ 0 [ZMOD 5])).mul (Int.ModEq.refl μ)
  simpa using H_mod.sub scaled_mod

/-- The scaled phase perturbation of a leading rightmost rule has normalized leading residue
`2`; its unscaled five-depth is `tailDepth+2`. -/
theorem exceptionalLeadingPhase_scaled_lead
    {β tailDepth : Nat} {H μ G phaseCoefficient difference : ℤ}
    (β_large : 2 ≤ β)
    (head_eq : 9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ (β - 1) - 7)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (coefficient_mod : phaseCoefficient ≡ 550 [ZMOD 1000])
    (difference_eq :
      difference = G * (H - 10 * μ) * (phaseCoefficient * 10 ^ tailDepth)) :
    HasFiveLeadingResidue (45 * difference) (tailDepth + 2 + 1)
      (2 ^ (tailDepth + 2) * 2) := by
  obtain ⟨quotient, coefficient_eq, quotient_mod⟩ :=
    modFiveHundredFifty_factor coefficient_mod
  have H_mod := exceptionalHead_mod_two β_large head_eq
  have G_mod := calibratedLift_mod_three (G := G) (by omega) lift_eq
  have head_gap_mod := exceptionalHeadGap_mod_two (μ := μ) H_mod
  have unit_mod :
      9 * G * (H - 10 * μ) * quotient ≡ 2 ^ (2 : Nat) * 2 [ZMOD 5] := by
    calc
      9 * G * (H - 10 * μ) * quotient ≡ 9 * 3 * 2 * 2 [ZMOD 5] :=
        (((Int.ModEq.refl (9 : ℤ)).mul G_mod).mul head_gap_mod).mul quotient_mod
      _ ≡ 2 ^ (2 : Nat) * 2 [ZMOD 5] := by norm_num
  exact scaledPhase_lead_of_factor
    (factorDepth := 2) coefficient_eq unit_mod difference_eq

/-- The scaled phase perturbation of a nonleading rightmost rule has normalized leading
residue `2`; its unscaled five-depth is `tailDepth+1`. -/
theorem exceptionalNonleadingPhase_scaled_lead
    {β tailDepth : Nat} {H μ G phaseCoefficient difference : ℤ}
    (β_large : 2 ≤ β)
    (head_eq : 9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ (β - 1) - 7)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (coefficient_mod :
      phaseCoefficient ≡ 480 [ZMOD 1000] ∨
        phaseCoefficient ≡ 780 [ZMOD 1000])
    (difference_eq :
      difference = G * (H - 10 * μ) * (phaseCoefficient * 10 ^ tailDepth)) :
    HasFiveLeadingResidue (45 * difference) (tailDepth + 1 + 1)
      (2 ^ (tailDepth + 1) * 2) := by
  have H_mod := exceptionalHead_mod_two β_large head_eq
  have G_mod := calibratedLift_mod_three (G := G) (by omega) lift_eq
  have head_gap_mod := exceptionalHeadGap_mod_two (μ := μ) H_mod
  rcases coefficient_mod with coefficient_mod | coefficient_mod
  · obtain ⟨quotient, coefficient_eq, quotient_mod⟩ :=
      modFourHundredEighty_factor coefficient_mod
    have unit_mod :
        9 * G * (H - 10 * μ) * quotient ≡ 2 ^ (1 : Nat) * 2 [ZMOD 5] := by
      calc
        9 * G * (H - 10 * μ) * quotient ≡ 9 * 3 * 2 * 1 [ZMOD 5] :=
          (((Int.ModEq.refl (9 : ℤ)).mul G_mod).mul head_gap_mod).mul quotient_mod
        _ ≡ 2 ^ (1 : Nat) * 2 [ZMOD 5] := by norm_num
    exact scaledPhase_lead_of_factor
      (factorDepth := 1) coefficient_eq unit_mod difference_eq
  · obtain ⟨quotient, coefficient_eq, quotient_mod⟩ :=
      modSevenHundredEighty_factor coefficient_mod
    have unit_mod :
        9 * G * (H - 10 * μ) * quotient ≡ 2 ^ (1 : Nat) * 2 [ZMOD 5] := by
      calc
        9 * G * (H - 10 * μ) * quotient ≡ 9 * 3 * 2 * 1 [ZMOD 5] :=
          (((Int.ModEq.refl (9 : ℤ)).mul G_mod).mul head_gap_mod).mul quotient_mod
        _ ≡ 2 ^ (1 : Nat) * 2 [ZMOD 5] := by norm_num
    exact scaledPhase_lead_of_factor
      (factorDepth := 1) coefficient_eq unit_mod difference_eq

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

/-- The exceptional two-`c` raw head admits no b-bearing rightmost-rule entry at the physical
pole shell.  The three possible minimum-depth arms have normalized residues `2` or `4`, `2`,
and `2`; none of their collisions vanishes modulo five. -/
theorem exceptionalBBearingRightmostRule_rawHead_shell_impossible
    {β : Nat} (body headTail : List TagLetter) (front : List NearyTile)
    (ruleLetter : TagLetter) (tail : List TagLetter) {μ E G : ℤ}
    (β_large : 2 ≤ β)
    (marker_mem : .b ∈ front.map NearyTile.letter ++ ruleLetter :: tail)
    (head_eq :
      9 * (code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) =
        5 * 10 ^ (β + 2) + 2 * 10 ^ (β - 1) - 7)
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
          (front.map NearyTile.letter ++ ruleLetter :: tail).count .b *
            (β + 1) - 1 : Nat) : ℤ))
        (((front.length + tail.length + 1 +
          (front.map NearyTile.letter ++ ruleLetter :: tail).count .b *
            (β + 1) - 1 : Nat) : ℤ))) :
    False := by
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
  have head_eq' : 9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ (β - 1) - 7 := by
    simpa only [H] using head_eq
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
  have allC_upper_eq : 9 * PAll = 50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7 :=
    allC_punctuatedUpper_code_identity β n
  have lower_eq : 9 * VErase = 7 * 10 ^ n - 7 := by
    have identity := allEraseLowerCode_identity β body n
    dsimp only [VErase]
    omega
  obtain ⟨baseCoefficient, base_coefficient, base_lead⟩ :=
    exceptionalAllC_scaled_lead
      (H := H) (μ := μ) (E := E) (G := G) (P := PAll) (V := VErase)
      (T := E * PAll + G * VErase) (R := RAll)
      β_large head_eq' mu_eq gap_eq lift_eq allC_upper_eq lower_eq rfl rfl
  let upperDepth := bTailWidth + β + 2
  let D := rightmostBUpperCoefficient β bFront
  have upper_code_difference : P - PAll = D * 10 ^ upperDepth := by
    have raw := rightmostB_punctuatedUpper_code_sub_eq β bFront bTailWidth
    simpa [P, PAll, D, upperDepth, letters_eq, n_eq] using raw
  have upper_residual_difference :
      RErase - RAll = H * E * D * 10 ^ upperDepth := by
    dsimp only [RErase, RAll]
    linear_combination H * E * upper_code_difference
  have D_sub_two_dvd : (5 : ℤ) ∣ D - 2 := by
    simpa only [D] using rightmostBUpperCoefficient_sub_two_dvd_five (by omega) bFront
  have upper_lead :
      HasFiveLeadingResidue (45 * (RErase - RAll)) (upperDepth + 1)
        (2 ^ upperDepth * 2) :=
    exceptionalUpper_scaled_lead β_large head_eq' gap_eq D_sub_two_dvd
      upper_residual_difference
  let K := rightmostRuleLowerCoefficient β body front ruleLetter
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
  have lower_difference : VRule - VErase = K * 10 ^ tail.length := by
    have raw := rightmostRuleLowerCode_sub_eq β body front ruleLetter tail
    rw [companion_code] at raw
    simpa only [VRule, K] using raw
  have phase_residual_difference :
      RRule - RErase = G * (H - 10 * μ) * (K * 10 ^ tail.length) := by
    dsimp only [RRule, RErase]
    linear_combination G * (H - 10 * μ) * lower_difference
  have phase_lead :
      HasFiveLeadingResidue (45 * (RRule - RErase)) (phaseDepth + 1)
        (2 ^ phaseDepth * 2) := by
    by_cases front_nil : front = []
    · subst front
      have coefficient_mod :=
        rightmostRuleLowerCoefficient_mod_thousand_of_prefix_nil β body ruleLetter
      have raw := exceptionalLeadingPhase_scaled_lead
        β_large head_eq' lift_eq coefficient_mod phase_residual_difference
      simpa only [phaseDepth, ↓reduceIte] using raw
    · rcases front with _ | ⟨frontTile, frontTail⟩
      · exact False.elim (front_nil rfl)
      · by_cases front_tail_nil : frontTail = []
        · subst frontTail
          have coefficient_mod :=
            rightmostRuleLowerCoefficient_mod_thousand_of_prefix_one
              β body frontTile ruleLetter
          have raw := exceptionalNonleadingPhase_scaled_lead
            β_large head_eq' lift_eq (Or.inl coefficient_mod) phase_residual_difference
          simpa only [phaseDepth, if_neg front_nil] using raw
        · have front_large : 2 ≤ (frontTile :: frontTail).length := by
            simp only [List.length_cons]
            exact Nat.succ_le_succ (List.length_pos_iff_ne_nil.mpr front_tail_nil)
          have coefficient_mod :=
            rightmostRuleLowerCoefficient_mod_thousand_of_two_le_prefix
              β body (frontTile :: frontTail) ruleLetter front_large
          have raw := exceptionalNonleadingPhase_scaled_lead
            β_large head_eq' lift_eq (Or.inr coefficient_mod) phase_residual_difference
          simpa only [phaseDepth, if_neg front_nil] using raw
  have scaled_sum_value :=
    exceptionalThreeLead_hasValue base_coefficient base_lead upper_lead phase_lead
  have scaled_sum_eq :
      (((45 * RAll + 45 * (RErase - RAll) + 45 * (RRule - RErase) : ℤ) : ℚ)) =
        ((45 * RRule : ℤ) : ℚ) := by
    push_cast
    ring
  rw [scaled_sum_eq] at scaled_sum_value
  have rule_value : HasValue 5 (RRule : ℚ) (targetDepth : ℤ) := by
    simpa only [RRule, H, P, VRule, targetDepth, n, letters] using shell.2
  have fortyFive_lead : HasFiveLeadingResidue 45 1 4 :=
    ⟨9, by norm_num, by norm_num⟩
  have fortyFive_value : HasValue 5 (45 : ℚ) 1 :=
    fortyFive_lead.hasValue (by norm_num)
  have scaled_rule_value :
      HasValue 5 (((45 * RRule : ℤ) : ℚ)) (((targetDepth + 1 : Nat) : ℤ)) := by
    have product_value := mul_hasValue fortyFive_value rule_value
    simpa [Int.cast_mul, add_comm] using product_value
  have depth_eq :
      (((min (min n (2 * β - 1)) (min upperDepth phaseDepth) + 1 : Nat) : ℤ)) =
        (((targetDepth + 1 : Nat) : ℤ)) :=
    scaled_sum_value.2.symm.trans scaled_rule_value.2
  have depth_eq_nat :
      min (min n (2 * β - 1)) (min upperDepth phaseDepth) + 1 = targetDepth + 1 := by
    exact_mod_cast depth_eq
  have phase_shallow : phaseDepth < targetDepth := by
    have marker_positive : 1 ≤ letters.count .b :=
      List.count_pos_iff.mpr (by simpa only [letters] using marker_mem)
    have marker_scale : 3 ≤ letters.count .b * (β + 1) := by
      have scaled := Nat.mul_le_mul marker_positive (show 3 ≤ β + 1 by omega)
      simpa only [Nat.one_mul] using scaled
    have target_eq : targetDepth =
        front.length + tail.length + letters.count .b * (β + 1) := by
      dsimp only [targetDepth, n]
      omega
    rw [target_eq]
    by_cases front_nil : front = []
    · subst front
      simp only [phaseDepth, ↓reduceIte, List.length_nil, Nat.zero_add]
      omega
    · have front_positive : 1 ≤ front.length :=
        List.length_pos_iff_ne_nil.mpr front_nil
      simp only [phaseDepth, if_neg front_nil]
      omega
  have minimum_le_phase :
      min (min n (2 * β - 1)) (min upperDepth phaseDepth) ≤ phaseDepth := by
    exact (min_le_right _ _).trans (min_le_right _ _)
  omega

/-- Beyond the regular raw-head frontier, scaling the all-`D_c` residual by `81` exposes the
normalized leading residue `2^suffix`. -/
theorem regularAllC_scaledEightyOne_lead
    {β suffix n : Nat} {H μ E G P V T R : ℤ}
    (suffix_below : suffix + 2 ≤ β)
    (width_deep : suffix + 1 < n)
    (head_eq : 9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ suffix - 7)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (upper_eq : 9 * P = 50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7)
    (lower_eq : 9 * V = 7 * 10 ^ n - 7)
    (trace_eq : T = E * P + G * V)
    (residual_eq : R = H * T - 10 * μ * G * V) :
    HasFiveLeadingResidue (81 * R) (suffix + 1) (2 ^ suffix) := by
  let ρ : ℤ := 10 ^ β
  let K : ℤ := 245 * 10 ^ (β + 2 - suffix) + 98
  let A : ℤ :=
    8100 * H * ρ ^ 2 + 3276 * H * ρ - 441 * H -
      1827280 * ρ ^ 2 + 271460 * ρ - 3430
  let B : ℤ :=
    324 * H * ρ - 33894 * H + 1827280 * ρ - 271460
  have head_factor := rawHead_linear_factor (show suffix ≤ β + 2 by omega) head_eq
  have decomposition := allCDeletion_residual_decomposition
    (ρ := ρ) (q := (10 : ℤ) ^ n)
    mu_eq gap_eq lift_eq upper_eq lower_eq trace_eq residual_eq
  have decomposition' :
      81 * R = 10 ^ (suffix + 1) * K + 10 ^ n * A + 10 ^ β * B := by
    rw [head_factor] at decomposition
    dsimp [ρ, K, A, B]
    rw [pow_two, ← pow_add] at decomposition
    simpa [pow_succ, pow_add, mul_assoc, mul_left_comm, mul_comm] using decomposition
  let widthRemainder := n - (suffix + 1)
  let headRemainder := β - (suffix + 1)
  have width_remainder_positive : 1 ≤ widthRemainder := by
    dsimp only [widthRemainder]
    omega
  have head_remainder_positive : 1 ≤ headRemainder := by
    dsimp only [headRemainder]
    omega
  let coefficient : ℤ :=
    2 ^ (suffix + 1) * K +
      5 ^ widthRemainder * 2 ^ n * A +
      5 ^ headRemainder * 2 ^ β * B
  have factorization : 81 * R = 5 ^ (suffix + 1) * coefficient := by
    rw [decomposition',
      tenPower_factor_five (small := suffix + 1) le_rfl,
      tenPower_factor_five (small := suffix + 1) (by omega),
      tenPower_factor_five (small := suffix + 1) (by omega)]
    dsimp only [coefficient]
    rw [show suffix + 1 - (suffix + 1) = 0 by omega,
      show n - (suffix + 1) = widthRemainder by rfl,
      show β - (suffix + 1) = headRemainder by rfl]
    norm_num
    ring
  have K_sub_three_dvd : (5 : ℤ) ∣ K - 3 := by
    refine ⟨49 * 10 ^ (β + 2 - suffix) + 19, ?_⟩
    dsimp only [K]
    ring
  have K_mod : K ≡ 3 [ZMOD 5] :=
    (Int.modEq_iff_dvd.mpr K_sub_three_dvd).symm
  have width_power_dvd : (5 : ℤ) ∣ 5 ^ widthRemainder := by
    simpa using pow_dvd_pow (5 : ℤ) width_remainder_positive
  have head_power_dvd : (5 : ℤ) ∣ 5 ^ headRemainder := by
    simpa using pow_dvd_pow (5 : ℤ) head_remainder_positive
  have width_mod : 5 ^ widthRemainder * 2 ^ n * A ≡ 0 [ZMOD 5] := by
    simpa [mul_assoc] using
      (width_power_dvd.mul_right (2 ^ n * A)).modEq_zero_int
  have head_mod : 5 ^ headRemainder * 2 ^ β * B ≡ 0 [ZMOD 5] := by
    simpa [mul_assoc] using
      (head_power_dvd.mul_right (2 ^ β * B)).modEq_zero_int
  have leading_mod : 2 ^ (suffix + 1) * K ≡ 2 ^ suffix [ZMOD 5] := by
    calc
      2 ^ (suffix + 1) * K ≡ 2 ^ (suffix + 1) * 3 [ZMOD 5] :=
        (Int.ModEq.refl (2 ^ (suffix + 1))).mul K_mod
      _ ≡ 2 ^ suffix [ZMOD 5] := by
        rw [pow_succ, show (2 : ℤ) ^ suffix * 2 * 3 = 2 ^ suffix * 6 by ring]
        simpa using (Int.ModEq.refl (2 ^ suffix)).mul
          (by norm_num : (6 : ℤ) ≡ 1 [ZMOD 5])
  have coefficient_mod : coefficient ≡ 2 ^ suffix [ZMOD 5] := by
    dsimp only [coefficient]
    simpa using (leading_mod.add width_mod).add head_mod
  exact ⟨coefficient, factorization, coefficient_mod⟩

private theorem regularHead_mod_two
    {β suffix : Nat} {H : ℤ} (suffix_positive : 1 ≤ suffix)
    (head_eq : 9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ suffix - 7) :
    H ≡ 2 [ZMOD 5] := by
  have scaled_eq :
      9 * (H - 2) = 5 * 10 ^ (β + 2) + 2 * 10 ^ suffix - 25 := by
    linear_combination head_eq
  have ten_dvd : (5 : ℤ) ∣ 10 ^ suffix :=
    (pow_dvd_pow (5 : ℤ) suffix_positive).trans
      (pow_dvd_pow_of_dvd (by norm_num : (5 : ℤ) ∣ 10) suffix)
  have scaled_dvd : (5 : ℤ) ∣ 9 * (H - 2) := by
    rw [scaled_eq]
    exact dvd_sub (dvd_add (dvd_mul_right 5 _) (ten_dvd.mul_left 2)) (by norm_num)
  have head_dvd : (5 : ℤ) ∣ H - 2 :=
    (by norm_num : IsCoprime (5 : ℤ) 9).dvd_of_dvd_mul_left scaled_dvd
  exact (Int.modEq_iff_dvd.mpr head_dvd).symm

private theorem regularNonleadingPhase_scaledEightyOne_lead_of_factor
    {tailDepth : Nat} {G headGap phaseCoefficient quotient difference : ℤ}
    (coefficient_eq : phaseCoefficient = 5 * quotient)
    (unit_mod : 81 * G * headGap * quotient ≡ 1 [ZMOD 5])
    (difference_eq :
      difference = G * headGap * (phaseCoefficient * 10 ^ tailDepth)) :
    HasFiveLeadingResidue (81 * difference) (tailDepth + 1) (2 ^ tailDepth) := by
  let normalized : ℤ := 81 * G * headGap * quotient * 2 ^ tailDepth
  have factorization : 81 * difference = 5 ^ (tailDepth + 1) * normalized := by
    rw [difference_eq, coefficient_eq, tenPower_eq_fivePower_mul_twoPower, pow_succ]
    dsimp only [normalized]
    ring
  have normalized_mod : normalized ≡ 2 ^ tailDepth [ZMOD 5] := by
    dsimp only [normalized]
    simpa using unit_mod.mul (Int.ModEq.refl (2 ^ tailDepth))
  exact ⟨normalized, factorization, normalized_mod⟩

/-- A nonleading phase perturbation at a regular raw head has the same scaled normalized
residue `2^tailDepth` as the all-`D_c` frontier. -/
theorem regularNonleadingPhase_scaledEightyOne_lead
    {β suffix tailDepth : Nat} {H μ G phaseCoefficient difference : ℤ}
    (β_positive : 1 ≤ β)
    (suffix_positive : 1 ≤ suffix)
    (head_eq : 9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ suffix - 7)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (coefficient_mod :
      phaseCoefficient ≡ 480 [ZMOD 1000] ∨
        phaseCoefficient ≡ 780 [ZMOD 1000])
    (difference_eq :
      difference = G * (H - 10 * μ) * (phaseCoefficient * 10 ^ tailDepth)) :
    HasFiveLeadingResidue (81 * difference) (tailDepth + 1) (2 ^ tailDepth) := by
  have H_mod := regularHead_mod_two suffix_positive head_eq
  have G_mod := calibratedLift_mod_three (G := G) β_positive lift_eq
  have head_gap_mod := exceptionalHeadGap_mod_two (μ := μ) H_mod
  rcases coefficient_mod with coefficient_mod | coefficient_mod
  · obtain ⟨quotient, coefficient_eq, quotient_mod⟩ :=
      modFourHundredEighty_factor coefficient_mod
    have unit_mod :
        81 * G * (H - 10 * μ) * quotient ≡ 1 [ZMOD 5] := by
      calc
        81 * G * (H - 10 * μ) * quotient ≡ 81 * 3 * 2 * 1 [ZMOD 5] :=
          (((Int.ModEq.refl (81 : ℤ)).mul G_mod).mul head_gap_mod).mul quotient_mod
        _ ≡ 1 [ZMOD 5] := by norm_num
    exact regularNonleadingPhase_scaledEightyOne_lead_of_factor
      coefficient_eq unit_mod difference_eq
  · obtain ⟨quotient, coefficient_eq, quotient_mod⟩ :=
      modSevenHundredEighty_factor coefficient_mod
    have unit_mod :
        81 * G * (H - 10 * μ) * quotient ≡ 1 [ZMOD 5] := by
      calc
        81 * G * (H - 10 * μ) * quotient ≡ 81 * 3 * 2 * 1 [ZMOD 5] :=
          (((Int.ModEq.refl (81 : ℤ)).mul G_mod).mul head_gap_mod).mul quotient_mod
        _ ≡ 1 [ZMOD 5] := by norm_num
    exact regularNonleadingPhase_scaledEightyOne_lead_of_factor
      coefficient_eq unit_mod difference_eq

/-- The sole regular b-bearing resonance left by the depth grammar is also empty: its
all-`D_c` and phase arms have equal normalized residue `2^suffix`, so their collision remains
a unit; the rightmost-`b` arm is strictly deeper. -/
theorem regularBBearingRightmostRule_rawHead_shell_impossible
    {β suffix : Nat} (body headTail : List TagLetter) (front : List NearyTile)
    (ruleLetter : TagLetter) (tail : List TagLetter) {μ E G : ℤ}
    (β_large : 2 ≤ β)
    (suffix_positive : 1 ≤ suffix)
    (suffix_below : suffix + 2 ≤ β)
    (front_positive : 1 ≤ front.length)
    (tail_width : tail.length = suffix)
    (marker_mem : .b ∈ front.map NearyTile.letter ++ ruleLetter :: tail)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: headTail)) : ℚ) 0 0)
    (head_eq :
      9 * (code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) =
        5 * 10 ^ (β + 2) + 2 * 10 ^ suffix - 7)
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
          (front.map NearyTile.letter ++ ruleLetter :: tail).count .b *
            (β + 1) - 1 : Nat) : ℤ))
        (((front.length + tail.length + 1 +
          (front.map NearyTile.letter ++ ruleLetter :: tail).count .b *
            (β + 1) - 1 : Nat) : ℤ))) :
    False := by
  let letters := front.map NearyTile.letter ++ ruleLetter :: tail
  let n := front.length + tail.length + 1
  let targetDepth := n + letters.count .b * (β + 1) - 1
  let H : ℤ := code (peeledHeadWord β (.c :: .c :: headTail))
  let P : ℤ := code (punctuatedUpper β letters)
  let PAll : ℤ := code (punctuatedUpper β (List.replicate n .c))
  let VRule : ℤ := code
    (spell (nearyLower β body) (front ++ .rule ruleLetter :: tail.map NearyTile.erase))
  let VErase : ℤ := allEraseLowerCode β body n
  let RRule : ℤ := H * (E * P + G * VRule) - 10 * μ * G * VRule
  let RErase : ℤ := H * (E * P + G * VErase) - 10 * μ * G * VErase
  let RAll : ℤ := H * (E * PAll + G * VErase) - 10 * μ * G * VErase
  have head_eq' : 9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ suffix - 7 := by
    simpa only [H] using head_eq
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
  have allC_upper_eq : 9 * PAll = 50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7 :=
    allC_punctuatedUpper_code_identity β n
  have lower_eq : 9 * VErase = 7 * 10 ^ n - 7 := by
    have identity := allEraseLowerCode_identity β body n
    dsimp only [VErase]
    omega
  have width_deep : suffix + 1 < n := by
    dsimp only [n]
    omega
  have base_lead :
      HasFiveLeadingResidue (81 * RAll) (suffix + 1) (2 ^ suffix) :=
    regularAllC_scaledEightyOne_lead suffix_below width_deep head_eq'
      mu_eq gap_eq lift_eq allC_upper_eq lower_eq rfl rfl
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
  let K := rightmostRuleLowerCoefficient β body front ruleLetter
  have lower_difference : VRule - VErase = K * 10 ^ tail.length := by
    have raw := rightmostRuleLowerCode_sub_eq β body front ruleLetter tail
    rw [companion_code] at raw
    simpa only [VRule, K] using raw
  have phase_residual_difference :
      RRule - RErase = G * (H - 10 * μ) * (K * 10 ^ tail.length) := by
    dsimp only [RRule, RErase]
    linear_combination G * (H - 10 * μ) * lower_difference
  have coefficient_mod :
      K ≡ 480 [ZMOD 1000] ∨ K ≡ 780 [ZMOD 1000] := by
    rcases front with _ | ⟨frontTile, frontTail⟩
    · simp at front_positive
    · by_cases front_tail_nil : frontTail = []
      · subst frontTail
        exact Or.inl
          (rightmostRuleLowerCoefficient_mod_thousand_of_prefix_one
            β body frontTile ruleLetter)
      · right
        exact rightmostRuleLowerCoefficient_mod_thousand_of_two_le_prefix
          β body (frontTile :: frontTail) ruleLetter
          (by
            simp only [List.length_cons]
            have tail_positive := List.length_pos_iff_ne_nil.mpr front_tail_nil
            omega)
  have phase_lead :
      HasFiveLeadingResidue (81 * (RRule - RErase)) (suffix + 1) (2 ^ suffix) := by
    have raw := regularNonleadingPhase_scaledEightyOne_lead
      (by omega : 1 ≤ β) suffix_positive head_eq' lift_eq coefficient_mod
      phase_residual_difference
    simpa only [tail_width] using raw
  have collision := base_lead.add phase_lead
  have collision_value := collision.hasValue
    (by simpa using twoPower_add_not_five_dvd suffix 1 1 (by norm_num))
  let upperDepth := bTailWidth + β + 2
  have upper_value :
      HasValue 5 (((RErase - RAll : ℤ) : ℚ)) (upperDepth : ℤ) := by
    have raw := rightmostB_allEraseResidual_sub_allC_hasValue_five
      (tailWidth := bTailWidth) body headTail bFront (μ := μ) (E := E) (G := G)
      β_large head_unit gap_eq
    simpa [RErase, RAll, H, P, PAll, VErase, upperDepth, letters_eq, n_eq] using raw
  have eightyOne_lead : HasFiveLeadingResidue 81 0 1 :=
    ⟨81, by norm_num, by norm_num⟩
  have eightyOne_value : HasValue 5 (81 : ℚ) 0 :=
    eightyOne_lead.hasValue (by norm_num)
  have scaled_upper_value :
      HasValue 5 (((81 * (RErase - RAll) : ℤ) : ℚ)) (upperDepth : ℤ) := by
    have product_value := mul_hasValue eightyOne_value upper_value
    simpa [Int.cast_mul] using product_value
  have upper_deep : suffix + 1 < upperDepth := by
    dsimp only [upperDepth]
    omega
  have scaled_total_value :=
    add_hasValue_left collision_value scaled_upper_value (by exact_mod_cast upper_deep)
  have scaled_total_eq :
      ((81 * RAll + 81 * (RRule - RErase) : ℤ) : ℚ) +
          ((81 * (RErase - RAll) : ℤ) : ℚ) =
        ((81 * RRule : ℤ) : ℚ) := by
    push_cast
    ring
  rw [scaled_total_eq] at scaled_total_value
  have rule_value : HasValue 5 (RRule : ℚ) (targetDepth : ℤ) := by
    simpa only [RRule, H, P, VRule, targetDepth, n, letters] using shell.2
  have scaled_rule_value :
      HasValue 5 (((81 * RRule : ℤ) : ℚ)) (targetDepth : ℤ) := by
    have product_value := mul_hasValue eightyOne_value rule_value
    simpa [Int.cast_mul] using product_value
  have depth_eq : ((suffix + 1 : Nat) : ℤ) = (targetDepth : ℤ) :=
    scaled_total_value.2.symm.trans scaled_rule_value.2
  have depth_eq_nat : suffix + 1 = targetDepth := by
    exact_mod_cast depth_eq
  have marker_positive : 1 ≤ letters.count .b :=
    List.count_pos_iff.mpr (by simpa only [letters] using marker_mem)
  have marker_scale : 3 ≤ letters.count .b * (β + 1) := by
    have scaled := Nat.mul_le_mul marker_positive (show 3 ≤ β + 1 by omega)
    simpa only [Nat.one_mul] using scaled
  have target_eq : targetDepth =
      front.length + tail.length + letters.count .b * (β + 1) := by
    dsimp only [targetDepth, n]
    omega
  omega

private theorem repeatedTrue_intCode_identity (width : Nat) :
    9 * (code (List.replicate width true) : ℤ) + 5 = 5 * 10 ^ width := by
  induction width with
  | zero => norm_num
  | succ width induction =>
      rw [List.replicate_succ, code_cons, digit_true, List.length_replicate, pow_succ]
      push_cast
      omega

private theorem rawHeadShape_code_identity
    {β suffix : Nat} {word : List Bool} (suffix_bound : suffix ≤ β + 2)
    (word_eq : word =
      List.replicate (β + 2 - suffix) true ++ List.replicate suffix false) :
    9 * (code word : ℤ) = 5 * 10 ^ (β + 2) + 2 * 10 ^ suffix - 7 := by
  have true_identity := repeatedTrue_intCode_identity (β + 2 - suffix)
  have false_identity :
      9 * (code (List.replicate suffix false) : ℤ) + 7 = 7 * 10 ^ suffix := by
    exact_mod_cast replicateFalse_code_identity suffix
  have total_width : β + 2 - suffix + suffix = β + 2 := by omega
  have power_eq : (10 : ℤ) ^ (β + 2) =
      10 ^ (β + 2 - suffix) * 10 ^ suffix := by
    rw [← pow_add, total_width]
  rw [word_eq, code_append, List.length_replicate]
  push_cast
  rw [power_eq]
  linear_combination (10 : ℤ) ^ suffix * true_identity + false_identity

/-- Every b-bearing rightmost-rule entry from a decimal-unit two-`c` raw head misses the
physical pole shell.  The S56 position grammar is exhausted: regular heads die by the `81`
scaled equal-residue collision, and the exceptional head dies by the `45` scaled three-arm
coefficient classifier. -/
theorem bBearingRightmostRule_rawHead_shell_impossible
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
          (front.map NearyTile.letter ++ ruleLetter :: tail).count .b *
            (β + 1) - 1 : Nat) : ℤ))
        (((front.length + tail.length + 1 +
          (front.map NearyTile.letter ++ ruleLetter :: tail).count .b *
            (β + 1) - 1 : Nat) : ℤ))) :
    False := by
  obtain ⟨suffix, bFront, bTailWidth, letters_eq, suffix_positive, suffix_le,
      head_shape, resonance⟩ :=
    MatrixMortality.DecimalSetterRuleResonance.bBearingRightmostRule_rawHead_forces_resonance
      body headTail front ruleLetter tail β_large marker_mem head_unit
      mu_eq gap_eq lift_eq shell
  have head_eq :
      9 * (code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) =
        5 * 10 ^ (β + 2) + 2 * 10 ^ suffix - 7 :=
    rawHeadShape_code_identity (by omega) head_shape
  have resonance_nat :
      let n := front.length + tail.length + 1
      let phaseDepth := if front.length = 0 then tail.length + 2 else tail.length + 1
      let upperDepth := bTailWidth + β + 2
      ((suffix + 2 ≤ β ∧
          ((min n (suffix + 1) = upperDepth ∧ min n (suffix + 1) ≤ phaseDepth) ∨
            (min n (suffix + 1) = phaseDepth ∧ min n (suffix + 1) ≤ upperDepth) ∨
            (upperDepth = phaseDepth ∧ upperDepth ≤ min n (suffix + 1)))) ∨
        (suffix = β - 1 ∧
          ((min n (2 * β - 1) = upperDepth ∧ min n (2 * β - 1) ≤ phaseDepth) ∨
            (min n (2 * β - 1) = phaseDepth ∧ min n (2 * β - 1) ≤ upperDepth) ∨
            (upperDepth = phaseDepth ∧ upperDepth ≤ min n (2 * β - 1))))) := by
    dsimp only at resonance ⊢
    have front_nil_iff : front = [] ↔ front.length = 0 := List.length_eq_zero_iff.symm
    simp only [front_nil_iff] at resonance
    exact_mod_cast resonance
  have grammar := rightmostRule_minimumResonance_positionGrammar
    (β := β) (suffix := suffix) (rulePrefix := front.length)
    (ruleTail := tail.length) (bTail := bTailWidth) β_large resonance_nat
  rcases grammar with regular | exceptional
  · exact regularBBearingRightmostRule_rawHead_shell_impossible
      body headTail front ruleLetter tail β_large suffix_positive regular.1
      regular.2.1 regular.2.2 marker_mem head_unit head_eq mu_eq gap_eq lift_eq shell
  · rw [exceptional.1] at head_eq
    exact exceptionalBBearingRightmostRule_rawHead_shell_impossible
      body headTail front ruleLetter tail β_large marker_mem head_eq
      mu_eq gap_eq lift_eq shell

end MatrixMortality.DecimalSetterRuleCoefficient
