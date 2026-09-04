import MatrixMortality.MixedPrimeRealTrapLengthThreeChambers

set_option exponentiation.threshold 1300

/-!
# Exact rebounding residue classifiers

This file starts after the generic terminal-carry and rebounding offset-transport theorems.
It classifies the two finite carry rectangles and then the exact target residues.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation
open PeriodicShell

private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private theorem reboundingTable_depth_zero_iff_odd (gap : ℕ) :
    shellSlopeGapFiveDepth gap = 0 ↔ Odd gap := by
  constructor
  · intro depth_zero
    by_contra gap_not_odd
    rw [shellSlopeGapFiveDepth, if_neg gap_not_odd] at depth_zero
    omega
  · intro gap_odd
    rw [shellSlopeGapFiveDepth, if_pos gap_odd]

private theorem reboundingTable_depth_one_iff
    {gap : ℕ} (gap_positive : 0 < gap) :
    shellSlopeGapFiveDepth gap = 1 ↔ Even gap ∧ ¬5 ∣ gap / 2 := by
  constructor
  · intro depth_one
    have gap_not_odd : ¬Odd gap := by
      intro gap_odd
      rw [shellSlopeGapFiveDepth, if_pos gap_odd] at depth_one
      omega
    have gap_even : Even gap := Nat.not_odd_iff_even.mp gap_not_odd
    have half_ne : gap / 2 ≠ 0 := by
      obtain ⟨half, gap_eq⟩ := gap_even
      omega
    have half_value : padicValNat 5 (gap / 2) = 0 := by
      rw [shellSlopeGapFiveDepth, if_neg gap_not_odd] at depth_one
      omega
    have half_not_dvd : ¬5 ∣ gap / 2 := by
      intro half_dvd
      exact (dvd_iff_padicValNat_ne_zero half_ne).1 half_dvd half_value
    exact ⟨gap_even, half_not_dvd⟩
  · rintro ⟨gap_even, half_not_dvd⟩
    have gap_not_odd : ¬Odd gap := Nat.not_odd_iff_even.mpr gap_even
    rw [shellSlopeGapFiveDepth, if_neg gap_not_odd,
      padicValNat.eq_zero_of_not_dvd half_not_dvd]

private theorem reboundingTable_depth_zero_add_even
    {gap shift : ℕ} (gap_depth : shellSlopeGapFiveDepth gap = 0)
    (shift_even : Even shift) :
    shellSlopeGapFiveDepth (gap + shift) = 0 := by
  have gap_odd := (reboundingTable_depth_zero_iff_odd gap).1 gap_depth
  obtain ⟨gapHalf, gap_eq⟩ := gap_odd
  obtain ⟨shiftHalf, shift_eq⟩ := shift_even
  exact (reboundingTable_depth_zero_iff_odd (gap + shift)).2
    ⟨gapHalf + shiftHalf, by omega⟩

private theorem reboundingTable_depth_one_add_ten_mul
    {gap multiplier : ℕ} (gap_positive : 0 < gap)
    (gap_depth : shellSlopeGapFiveDepth gap = 1) :
    shellSlopeGapFiveDepth (gap + 10 * multiplier) = 1 := by
  obtain ⟨gap_even, half_not_dvd⟩ :=
    (reboundingTable_depth_one_iff gap_positive).1 gap_depth
  obtain ⟨half, gap_eq⟩ := gap_even
  have shifted_even : Even (gap + 10 * multiplier) :=
    ⟨half + 5 * multiplier, by omega⟩
  have shifted_half_not_dvd : ¬5 ∣ (gap + 10 * multiplier) / 2 := by
    rw [Nat.dvd_iff_mod_eq_zero] at half_not_dvd ⊢
    omega
  exact (reboundingTable_depth_one_iff (by omega)).2
    ⟨shifted_even, shifted_half_not_dvd⟩

private theorem reboundingTable_padicValInt_five_eq_two_iff (value : ℤ) :
    padicValInt 5 value = 2 ↔ (25 : ℤ) ∣ value ∧ ¬(125 : ℤ) ∣ value := by
  constructor
  · intro value_eq
    have value_ne : value ≠ 0 := by
      intro value_zero
      subst value
      norm_num at value_eq
    have square_dvd : (5 : ℤ) ^ 2 ∣ value :=
      (padicValInt_dvd_iff 2 value).2 (Or.inr (by rw [value_eq]))
    have cube_not_dvd : ¬(5 : ℤ) ^ 3 ∣ value := by
      intro cube_dvd
      rcases (padicValInt_dvd_iff 3 value).1 cube_dvd with impossible | three_le
      · exact value_ne impossible
      · rw [value_eq] at three_le
        omega
    norm_num at square_dvd cube_not_dvd ⊢
    exact ⟨square_dvd, cube_not_dvd⟩
  · rintro ⟨square_dvd, cube_not_dvd⟩
    have value_ne : value ≠ 0 := by
      intro value_zero
      subst value
      exact cube_not_dvd (dvd_zero _)
    have square_power_dvd : (5 : ℤ) ^ 2 ∣ value := by
      norm_num at square_dvd ⊢
      exact square_dvd
    have two_le : 2 ≤ padicValInt 5 value := by
      rcases (padicValInt_dvd_iff 2 value).1 square_power_dvd with impossible | two_le
      · exact (value_ne impossible).elim
      · exact two_le
    have not_three_le : ¬3 ≤ padicValInt 5 value := by
      intro three_le
      apply cube_not_dvd
      have cube_power_dvd := (padicValInt_dvd_iff 3 value).2 (Or.inr three_le)
      norm_num at cube_power_dvd ⊢
      exact cube_power_dvd
    omega

private theorem reboundingTable_padicValInt_five_cast_eq_two_iff (value : ℤ) :
    (padicValInt 5 value : ℤ) = 2 ↔
      (25 : ℤ) ∣ value ∧ ¬(125 : ℤ) ∣ value := by
  norm_cast
  exact reboundingTable_padicValInt_five_eq_two_iff value

/-- Exact depth two in the `B = 6` carry reduces to the offset modulo fifty. -/
theorem lengthThreeReboundingTargetCarry_six_hasValue_two_iff_mod_fifty
    (offset : ℕ) (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 0) :
    HasValue 5 (lengthThreeReboundingTargetCarry 6 offset) 2 ↔
      HasValue 5 (lengthThreeReboundingTargetCarry 6 (offset % 50)) 2 := by
  have residue_depth : shellSlopeGapFiveDepth (offset % 50 + 1) = 0 := by
    have gap_odd := (reboundingTable_depth_zero_iff_odd (offset + 1)).1 gap_depth
    obtain ⟨half, gap_eq⟩ := gap_odd
    exact (reboundingTable_depth_zero_iff_odd (offset % 50 + 1)).2
      ⟨(offset % 50) / 2, by omega⟩
  have periodic (base repetitions : ℕ)
      (base_depth : shellSlopeGapFiveDepth (base + 1) = 0) :
      HasValue 5
          (lengthThreeReboundingTargetCarry 6 (base + 50 * repetitions)) 2 ↔
        HasValue 5 (lengthThreeReboundingTargetCarry 6 base) 2 := by
    induction repetitions with
    | zero => simp
    | succ repetitions induction =>
        have current_depth :
            shellSlopeGapFiveDepth (base + 50 * repetitions + 1) = 0 := by
          have shifted := reboundingTable_depth_zero_add_even base_depth
            (show Even (50 * repetitions) from ⟨25 * repetitions, by omega⟩)
          rw [show base + 50 * repetitions + 1 =
            base + 1 + 50 * repetitions by omega]
          exact shifted
        rw [Nat.mul_succ, ← Nat.add_assoc,
          lengthThreeReboundingTargetCarry_six_add_fifty_hasValue_two_iff
            (base + 50 * repetitions) current_depth]
        exact induction
  have decomposition : offset % 50 + 50 * (offset / 50) = offset :=
    Nat.mod_add_div offset 50
  have reduced := periodic (offset % 50) (offset / 50) residue_depth
  rwa [decomposition] at reduced

/-- Exact depth two in the `B = 7` carry reduces to the offset modulo 250. -/
theorem lengthThreeReboundingTargetCarry_seven_hasValue_two_iff_mod_twoFifty
    (offset : ℕ) (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 1) :
    HasValue 5 (lengthThreeReboundingTargetCarry 7 offset) 2 ↔
      HasValue 5 (lengthThreeReboundingTargetCarry 7 (offset % 250)) 2 := by
  have gap_positive : 0 < offset + 1 := by omega
  obtain ⟨gap_even, half_not_dvd⟩ :=
    (reboundingTable_depth_one_iff gap_positive).1 gap_depth
  have residue_even : Even (offset % 250 + 1) := by
    obtain ⟨half, gap_eq⟩ := gap_even
    exact ⟨(offset % 250 + 1) / 2, by omega⟩
  have residue_half_not_dvd : ¬5 ∣ (offset % 250 + 1) / 2 := by
    rw [Nat.dvd_iff_mod_eq_zero] at half_not_dvd ⊢
    omega
  have residue_depth : shellSlopeGapFiveDepth (offset % 250 + 1) = 1 :=
    (reboundingTable_depth_one_iff (by omega)).2
      ⟨residue_even, residue_half_not_dvd⟩
  have periodic (base repetitions : ℕ)
      (base_depth : shellSlopeGapFiveDepth (base + 1) = 1) :
      HasValue 5
          (lengthThreeReboundingTargetCarry 7 (base + 250 * repetitions)) 2 ↔
        HasValue 5 (lengthThreeReboundingTargetCarry 7 base) 2 := by
    induction repetitions with
    | zero => simp
    | succ repetitions induction =>
        have current_depth :
            shellSlopeGapFiveDepth (base + 250 * repetitions + 1) = 1 := by
          rw [show base + 250 * repetitions + 1 =
            base + 1 + 10 * (25 * repetitions) by omega]
          exact reboundingTable_depth_one_add_ten_mul
            (show 0 < base + 1 by omega) base_depth
        rw [Nat.mul_succ, ← Nat.add_assoc,
          lengthThreeReboundingTargetCarry_seven_add_twoFifty_hasValue_two_iff
            (base + 250 * repetitions) current_depth]
        exact induction
  have decomposition : offset % 250 + 250 * (offset / 250) = offset :=
    Nat.mod_add_div offset 250
  have reduced := periodic (offset % 250) (offset / 250) residue_depth
  rwa [decomposition] at reduced

/-- The `B = 6` carry has depth two exactly in four gap classes modulo fifty. -/
theorem lengthThreeReboundingTargetCarry_six_hasValue_two_iff_residue
    (offset : ℕ) (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 0) :
    HasValue 5 (lengthThreeReboundingTargetCarry 6 offset) 2 ↔
      (offset + 1) % 50 = 15 ∨ (offset + 1) % 50 = 25 ∨
        (offset + 1) % 50 = 35 ∨ (offset + 1) % 50 = 45 := by
  rw [lengthThreeReboundingTargetCarry_six_hasValue_two_iff_mod_fifty
    offset gap_depth]
  generalize residue_eq : offset % 50 = residue
  have residue_lt : residue < 50 := by
    have := Nat.mod_lt offset (by norm_num : 0 < 50)
    omega
  have gap_odd := (reboundingTable_depth_zero_iff_odd (offset + 1)).1 gap_depth
  obtain ⟨half, gap_eq⟩ := gap_odd
  have residue_even : Even residue := ⟨residue / 2, by omega⟩
  have gap_mod_eq : (offset + 1) % 50 = (residue + 1) % 50 := by
    simp [Nat.add_mod, residue_eq]
  rw [gap_mod_eq]
  interval_cases residue <;>
    norm_num at residue_even <;>
    norm_num [lengthThreeReboundingTargetCarry, HasValue, padicValRat,
      padicValInt.eq_zero_of_not_dvd, padicValNat.eq_zero_of_not_dvd,
      padicValNat_self, padicValNat.mul, padicValNat.prime_pow,
      reboundingTable_padicValInt_five_eq_two_iff,
      reboundingTable_padicValInt_five_cast_eq_two_iff]

/-- The `B = 7` carry has depth two exactly in four gap classes modulo 250. -/
theorem lengthThreeReboundingTargetCarry_seven_hasValue_two_iff_residue
    (offset : ℕ) (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 1) :
    HasValue 5 (lengthThreeReboundingTargetCarry 7 offset) 2 ↔
      (offset + 1) % 250 = 82 ∨ (offset + 1) % 250 = 132 ∨
        (offset + 1) % 250 = 182 ∨ (offset + 1) % 250 = 232 := by
  rw [lengthThreeReboundingTargetCarry_seven_hasValue_two_iff_mod_twoFifty
    offset gap_depth]
  generalize residue_eq : offset % 250 = residue
  have residue_lt : residue < 250 := by
    have := Nat.mod_lt offset (by norm_num : 0 < 250)
    omega
  have gap_positive : 0 < offset + 1 := by omega
  obtain ⟨gap_even, half_not_dvd⟩ :=
    (reboundingTable_depth_one_iff gap_positive).1 gap_depth
  have residue_even : Even (residue + 1) := by
    obtain ⟨half, gap_eq⟩ := gap_even
    exact ⟨(residue + 1) / 2, by omega⟩
  have residue_half_not_dvd : ¬5 ∣ (residue + 1) / 2 := by
    rw [Nat.dvd_iff_mod_eq_zero] at half_not_dvd ⊢
    omega
  have gap_mod_eq : (offset + 1) % 250 = (residue + 1) % 250 := by
    simp [Nat.add_mod, residue_eq]
  rw [gap_mod_eq]
  interval_cases residue <;>
    norm_num at residue_even <;>
    norm_num at residue_half_not_dvd <;>
    norm_num [lengthThreeReboundingTargetCarry, HasValue, padicValRat,
      padicValInt.eq_zero_of_not_dvd, padicValNat.eq_zero_of_not_dvd,
      padicValNat_self, padicValNat.mul, padicValNat.prime_pow,
      reboundingTable_padicValInt_five_eq_two_iff,
      reboundingTable_padicValInt_five_cast_eq_two_iff]

/-- Accepted `(gap mod 250, terminal wait mod 10)` pairs in the `B = 6` fibre. -/
def lengthThreeReboundingSixTargetResidue (gap wait : ℕ) : Prop :=
  (gap = 25 ∧ (wait = 2 ∨ wait = 4 ∨ wait = 6 ∨ wait = 8)) ∨
  (gap = 35 ∧ (wait = 1 ∨ wait = 5 ∨ wait = 7 ∨ wait = 9)) ∨
  (gap = 75 ∧ (wait = 0 ∨ wait = 2 ∨ wait = 6 ∨ wait = 8)) ∨
  (gap = 85 ∧ (wait = 1 ∨ wait = 3 ∨ wait = 5 ∨ wait = 7)) ∨
  (gap = 125 ∧ (wait = 0 ∨ wait = 2 ∨ wait = 4 ∨ wait = 6)) ∨
  (gap = 135 ∧ (wait = 1 ∨ wait = 3 ∨ wait = 7 ∨ wait = 9)) ∨
  (gap = 175 ∧ (wait = 0 ∨ wait = 4 ∨ wait = 6 ∨ wait = 8)) ∨
  (gap = 185 ∧ (wait = 3 ∨ wait = 5 ∨ wait = 7 ∨ wait = 9)) ∨
  (gap = 225 ∧ (wait = 0 ∨ wait = 2 ∨ wait = 4 ∨ wait = 8)) ∨
  gap = 235 ∧ (wait = 1 ∨ wait = 3 ∨ wait = 5 ∨ wait = 9)

/-- Accepted `(gap mod 1250, terminal wait mod 10)` pairs in the `B = 7` fibre. -/
def lengthThreeReboundingSevenTargetResidue (gap wait : ℕ) : Prop :=
  (gap = 82 ∧ (wait = 3 ∨ wait = 5 ∨ wait = 7 ∨ wait = 9)) ∨
  (gap = 232 ∧ (wait = 0 ∨ wait = 2 ∨ wait = 4 ∨ wait = 6)) ∨
  (gap = 332 ∧ (wait = 1 ∨ wait = 3 ∨ wait = 5 ∨ wait = 7)) ∨
  (gap = 482 ∧ (wait = 2 ∨ wait = 4 ∨ wait = 6 ∨ wait = 8)) ∨
  (gap = 582 ∧ (wait = 1 ∨ wait = 3 ∨ wait = 5 ∨ wait = 9)) ∨
  (gap = 732 ∧ (wait = 0 ∨ wait = 4 ∨ wait = 6 ∨ wait = 8)) ∨
  (gap = 832 ∧ (wait = 1 ∨ wait = 3 ∨ wait = 7 ∨ wait = 9)) ∨
  (gap = 982 ∧ (wait = 0 ∨ wait = 2 ∨ wait = 6 ∨ wait = 8)) ∨
  (gap = 1082 ∧ (wait = 1 ∨ wait = 5 ∨ wait = 7 ∨ wait = 9)) ∨
  gap = 1232 ∧ (wait = 0 ∨ wait = 2 ∨ wait = 4 ∨ wait = 8)

private theorem lengthThreeReboundingTarget_six_finiteRectangle
    {offset wait : ℕ} (offset_lt : offset < 250) (wait_lt : wait < 10)
    (carry_residue :
      (offset + 1) % 50 = 15 ∨ (offset + 1) % 50 = 25 ∨
        (offset + 1) % 50 = 35 ∨ (offset + 1) % 50 = 45) :
    IsUnit 5 (lengthThreeReboundingTarget 6 offset wait) ↔
      lengthThreeReboundingSixTargetResidue (offset + 1) wait := by
  interval_cases offset <;>
    norm_num at carry_residue <;>
    interval_cases wait <;>
    norm_num [lengthThreeReboundingSixTargetResidue,
      lengthThreeReboundingTarget, HasValue, padicValRat,
      padicValInt.eq_zero_of_not_dvd, padicValNat.eq_zero_of_not_dvd,
      padicValNat_self, padicValNat.mul, padicValNat.prime_pow,
      reboundingTable_padicValInt_five_eq_two_iff,
      reboundingTable_padicValInt_five_cast_eq_two_iff]

private theorem lengthThreeReboundingTarget_seven_finiteRectangle_eightyTwo
    {offset wait : ℕ} (offset_lt : offset < 1250) (wait_lt : wait < 10)
    (carry_residue : (offset + 1) % 250 = 82) :
    IsUnit 5 (lengthThreeReboundingTarget 7 offset wait) ↔
      lengthThreeReboundingSevenTargetResidue (offset + 1) wait := by
  interval_cases offset <;>
    norm_num at carry_residue <;>
    interval_cases wait <;>
    norm_num [lengthThreeReboundingSevenTargetResidue,
      lengthThreeReboundingTarget, HasValue, padicValRat,
      padicValInt.eq_zero_of_not_dvd, padicValNat.eq_zero_of_not_dvd,
      padicValNat_self, padicValNat.mul, padicValNat.prime_pow,
      reboundingTable_padicValInt_five_eq_two_iff,
      reboundingTable_padicValInt_five_cast_eq_two_iff]

private theorem lengthThreeReboundingTarget_seven_finiteRectangle_oneThirtyTwo
    {offset wait : ℕ} (offset_lt : offset < 1250) (wait_lt : wait < 10)
    (carry_residue : (offset + 1) % 250 = 132) :
    IsUnit 5 (lengthThreeReboundingTarget 7 offset wait) ↔
      lengthThreeReboundingSevenTargetResidue (offset + 1) wait := by
  interval_cases offset <;>
    norm_num at carry_residue <;>
    interval_cases wait <;>
    norm_num [lengthThreeReboundingSevenTargetResidue,
      lengthThreeReboundingTarget, HasValue, padicValRat,
      padicValInt.eq_zero_of_not_dvd, padicValNat.eq_zero_of_not_dvd,
      padicValNat_self, padicValNat.mul, padicValNat.prime_pow,
      reboundingTable_padicValInt_five_eq_two_iff,
      reboundingTable_padicValInt_five_cast_eq_two_iff]

private theorem lengthThreeReboundingTarget_seven_finiteRectangle_oneEightyTwo
    {offset wait : ℕ} (offset_lt : offset < 1250) (wait_lt : wait < 10)
    (carry_residue : (offset + 1) % 250 = 182) :
    IsUnit 5 (lengthThreeReboundingTarget 7 offset wait) ↔
      lengthThreeReboundingSevenTargetResidue (offset + 1) wait := by
  interval_cases offset <;>
    norm_num at carry_residue <;>
    interval_cases wait <;>
    norm_num [lengthThreeReboundingSevenTargetResidue,
      lengthThreeReboundingTarget, HasValue, padicValRat,
      padicValInt.eq_zero_of_not_dvd, padicValNat.eq_zero_of_not_dvd,
      padicValNat_self, padicValNat.mul, padicValNat.prime_pow,
      reboundingTable_padicValInt_five_eq_two_iff,
      reboundingTable_padicValInt_five_cast_eq_two_iff]

private theorem lengthThreeReboundingTarget_seven_finiteRectangle_twoThirtyTwo
    {offset wait : ℕ} (offset_lt : offset < 1250) (wait_lt : wait < 10)
    (carry_residue : (offset + 1) % 250 = 232) :
    IsUnit 5 (lengthThreeReboundingTarget 7 offset wait) ↔
      lengthThreeReboundingSevenTargetResidue (offset + 1) wait := by
  interval_cases offset <;>
    norm_num at carry_residue <;>
    interval_cases wait <;>
    norm_num [lengthThreeReboundingSevenTargetResidue,
      lengthThreeReboundingTarget, HasValue, padicValRat,
      padicValInt.eq_zero_of_not_dvd, padicValNat.eq_zero_of_not_dvd,
      padicValNat_self, padicValNat.mul, padicValNat.prime_pow,
      reboundingTable_padicValInt_five_eq_two_iff,
      reboundingTable_padicValInt_five_cast_eq_two_iff]

private theorem lengthThreeReboundingTarget_seven_finiteRectangle
    {offset wait : ℕ} (offset_lt : offset < 1250) (wait_lt : wait < 10)
    (carry_residue :
      (offset + 1) % 250 = 82 ∨ (offset + 1) % 250 = 132 ∨
        (offset + 1) % 250 = 182 ∨ (offset + 1) % 250 = 232) :
    IsUnit 5 (lengthThreeReboundingTarget 7 offset wait) ↔
      lengthThreeReboundingSevenTargetResidue (offset + 1) wait := by
  rcases carry_residue with residue | residue | residue | residue
  · exact lengthThreeReboundingTarget_seven_finiteRectangle_eightyTwo
      offset_lt wait_lt residue
  · exact lengthThreeReboundingTarget_seven_finiteRectangle_oneThirtyTwo
      offset_lt wait_lt residue
  · exact lengthThreeReboundingTarget_seven_finiteRectangle_oneEightyTwo
      offset_lt wait_lt residue
  · exact lengthThreeReboundingTarget_seven_finiteRectangle_twoThirtyTwo
      offset_lt wait_lt residue

/-- The `B = 6` target reduces to the offset modulo 250 on the source-unit fibre. -/
theorem lengthThreeReboundingTarget_six_fiveUnit_iff_mod_twoFifty
    (offset wait : ℕ) (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 0) :
    IsUnit 5 (lengthThreeReboundingTarget 6 offset wait) ↔
      IsUnit 5 (lengthThreeReboundingTarget 6 (offset % 250) wait) := by
  have residue_depth : shellSlopeGapFiveDepth (offset % 250 + 1) = 0 := by
    have gap_odd := (reboundingTable_depth_zero_iff_odd (offset + 1)).1 gap_depth
    obtain ⟨half, gap_eq⟩ := gap_odd
    exact (reboundingTable_depth_zero_iff_odd (offset % 250 + 1)).2
      ⟨(offset % 250) / 2, by omega⟩
  have periodic (base repetitions : ℕ)
      (base_depth : shellSlopeGapFiveDepth (base + 1) = 0) :
      IsUnit 5
          (lengthThreeReboundingTarget 6 (base + 250 * repetitions) wait) ↔
        IsUnit 5 (lengthThreeReboundingTarget 6 base wait) := by
    induction repetitions with
    | zero => simp
    | succ repetitions induction =>
        have current_depth :
            shellSlopeGapFiveDepth (base + 250 * repetitions + 1) = 0 := by
          have shifted := reboundingTable_depth_zero_add_even base_depth
            (show Even (250 * repetitions) from ⟨125 * repetitions, by omega⟩)
          rw [show base + 250 * repetitions + 1 =
            base + 1 + 250 * repetitions by omega]
          exact shifted
        rw [Nat.mul_succ, ← Nat.add_assoc,
          lengthThreeReboundingTarget_six_offset_add_twoFifty_fiveUnit_iff
            (base + 250 * repetitions) wait current_depth]
        exact induction
  have decomposition : offset % 250 + 250 * (offset / 250) = offset :=
    Nat.mod_add_div offset 250
  have reduced := periodic (offset % 250) (offset / 250) residue_depth
  rwa [decomposition] at reduced

/-- The `B = 7` target reduces to the offset modulo 1250 on the source-unit fibre. -/
theorem lengthThreeReboundingTarget_seven_fiveUnit_iff_mod_twelveFifty
    (offset wait : ℕ) (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 1) :
    IsUnit 5 (lengthThreeReboundingTarget 7 offset wait) ↔
      IsUnit 5 (lengthThreeReboundingTarget 7 (offset % 1250) wait) := by
  have gap_positive : 0 < offset + 1 := by omega
  obtain ⟨gap_even, half_not_dvd⟩ :=
    (reboundingTable_depth_one_iff gap_positive).1 gap_depth
  have residue_even : Even (offset % 1250 + 1) := by
    obtain ⟨half, gap_eq⟩ := gap_even
    exact ⟨(offset % 1250 + 1) / 2, by omega⟩
  have residue_half_not_dvd : ¬5 ∣ (offset % 1250 + 1) / 2 := by
    rw [Nat.dvd_iff_mod_eq_zero] at half_not_dvd ⊢
    omega
  have residue_depth : shellSlopeGapFiveDepth (offset % 1250 + 1) = 1 :=
    (reboundingTable_depth_one_iff (by omega)).2
      ⟨residue_even, residue_half_not_dvd⟩
  have periodic (base repetitions : ℕ)
      (base_depth : shellSlopeGapFiveDepth (base + 1) = 1) :
      IsUnit 5
          (lengthThreeReboundingTarget 7 (base + 1250 * repetitions) wait) ↔
        IsUnit 5 (lengthThreeReboundingTarget 7 base wait) := by
    induction repetitions with
    | zero => simp
    | succ repetitions induction =>
        have current_depth :
            shellSlopeGapFiveDepth (base + 1250 * repetitions + 1) = 1 := by
          rw [show base + 1250 * repetitions + 1 =
            base + 1 + 10 * (125 * repetitions) by omega]
          exact reboundingTable_depth_one_add_ten_mul
            (show 0 < base + 1 by omega) base_depth
        rw [Nat.mul_succ, ← Nat.add_assoc,
          lengthThreeReboundingTarget_seven_offset_add_twelveFifty_fiveUnit_iff
            (base + 1250 * repetitions) wait current_depth]
        exact induction
  have decomposition : offset % 1250 + 1250 * (offset / 1250) = offset :=
    Nat.mod_add_div offset 1250
  have reduced := periodic (offset % 1250) (offset / 1250) residue_depth
  rwa [decomposition] at reduced

private theorem reboundingSixTargetResidue_carryResidue
    {gap wait : ℕ} (accepted : lengthThreeReboundingSixTargetResidue gap wait) :
    gap % 50 = 15 ∨ gap % 50 = 25 ∨ gap % 50 = 35 ∨ gap % 50 = 45 := by
  rcases accepted with row | row | row | row | row | row | row | row | row | row <;>
    omega

private theorem reboundingSevenTargetResidue_carryResidue
    {gap wait : ℕ} (accepted : lengthThreeReboundingSevenTargetResidue gap wait) :
    gap % 250 = 82 ∨ gap % 250 = 132 ∨ gap % 250 = 182 ∨
      gap % 250 = 232 := by
  rcases accepted with row | row | row | row | row | row | row | row | row | row <;>
    omega

private theorem reboundingTable_gap_mod_twoFifty_eq_offset_mod_add_one
    (offset : ℕ) (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 0) :
    (offset + 1) % 250 = offset % 250 + 1 := by
  have gap_odd := (reboundingTable_depth_zero_iff_odd (offset + 1)).1 gap_depth
  obtain ⟨half, gap_eq⟩ := gap_odd
  have residue_even : Even (offset % 250) := ⟨(offset % 250) / 2, by omega⟩
  have residue_lt : offset % 250 < 250 := Nat.mod_lt offset (by norm_num)
  have sum_lt : offset % 250 + 1 < 250 := by
    obtain ⟨residueHalf, residue_eq⟩ := residue_even
    omega
  calc
    (offset + 1) % 250 = (offset % 250 + 1 % 250) % 250 :=
      Nat.add_mod offset 1 250
    _ = (offset % 250 + 1) % 250 := by norm_num
    _ = offset % 250 + 1 := Nat.mod_eq_of_lt sum_lt

private theorem reboundingTable_gap_mod_twelveFifty_eq_offset_mod_add_one
    (offset : ℕ) (gap_depth : shellSlopeGapFiveDepth (offset + 1) = 1) :
    (offset + 1) % 1250 = offset % 1250 + 1 := by
  have gap_positive : 0 < offset + 1 := by omega
  obtain ⟨gap_even, half_not_dvd⟩ :=
    (reboundingTable_depth_one_iff gap_positive).1 gap_depth
  have residue_even : Even (offset % 1250 + 1) := by
    obtain ⟨half, gap_eq⟩ := gap_even
    exact ⟨(offset % 1250 + 1) / 2, by omega⟩
  have residue_half_not_dvd : ¬5 ∣ (offset % 1250 + 1) / 2 := by
    rw [Nat.dvd_iff_mod_eq_zero] at half_not_dvd ⊢
    omega
  have residue_lt : offset % 1250 < 1250 := Nat.mod_lt offset (by norm_num)
  have sum_lt : offset % 1250 + 1 < 1250 := by
    by_contra sum_not_lt
    have residue_eq : offset % 1250 = 1249 := by omega
    apply residue_half_not_dvd
    rw [residue_eq]
    norm_num
  calc
    (offset + 1) % 1250 = (offset % 1250 + 1 % 1250) % 1250 :=
      Nat.add_mod offset 1 1250
    _ = (offset % 1250 + 1) % 1250 := by norm_num
    _ = offset % 1250 + 1 := Nat.mod_eq_of_lt sum_lt

/-- The `B = 6` target is exactly the displayed forty residue pairs. -/
theorem lengthThreeReboundingTarget_six_fiveUnit_iff_residue
    (offset wait : ℕ) :
    IsUnit 5 (lengthThreeReboundingTarget 6 offset wait) ↔
      lengthThreeReboundingSixTargetResidue
        ((offset + 1) % 250) (wait % 10) := by
  constructor
  · intro target_unit
    have source_unit := lengthThreeReboundingTarget_fiveUnit_forces_source_fiveUnit
      0 6 offset wait target_unit
    have gap_depth :=
      (lengthThreeReboundingSource_six_fiveUnit_iff 0 offset).1 source_unit
    have carry_value :=
      lengthThreeReboundingTarget_fiveUnit_forces_carry 6 offset wait target_unit
    have terminal_reduced :=
      (lengthThreeReboundingTarget_fiveUnit_iff_mod_ten
        6 offset wait carry_value).1 target_unit
    have offset_reduced :=
      (lengthThreeReboundingTarget_six_fiveUnit_iff_mod_twoFifty
        offset (wait % 10) gap_depth).1 terminal_reduced
    have base_gap_depth :
        shellSlopeGapFiveDepth (offset % 250 + 1) = 0 := by
      have gap_odd := (reboundingTable_depth_zero_iff_odd (offset + 1)).1 gap_depth
      obtain ⟨half, gap_eq⟩ := gap_odd
      exact (reboundingTable_depth_zero_iff_odd (offset % 250 + 1)).2
        ⟨(offset % 250) / 2, by omega⟩
    have base_carry_value :=
      lengthThreeReboundingTarget_fiveUnit_forces_carry
        6 (offset % 250) (wait % 10) offset_reduced
    have carry_residue :=
      (lengthThreeReboundingTargetCarry_six_hasValue_two_iff_residue
        (offset % 250) base_gap_depth).1 base_carry_value
    have finite := lengthThreeReboundingTarget_six_finiteRectangle
      (Nat.mod_lt offset (by norm_num)) (Nat.mod_lt wait (by norm_num)) carry_residue
    have accepted := finite.1 offset_reduced
    rw [reboundingTable_gap_mod_twoFifty_eq_offset_mod_add_one offset gap_depth]
    exact accepted
  · intro accepted
    have residue_cases :
        (offset + 1) % 250 = 25 ∨ (offset + 1) % 250 = 35 ∨
          (offset + 1) % 250 = 75 ∨ (offset + 1) % 250 = 85 ∨
          (offset + 1) % 250 = 125 ∨ (offset + 1) % 250 = 135 ∨
          (offset + 1) % 250 = 175 ∨ (offset + 1) % 250 = 185 ∨
          (offset + 1) % 250 = 225 ∨ (offset + 1) % 250 = 235 := by
      rcases accepted with row | row | row | row | row | row | row | row | row | row <;>
        omega
    have gap_odd : Odd (offset + 1) := by
      refine ⟨(offset + 1) / 2, ?_⟩
      rcases residue_cases with residue | residue | residue | residue | residue | residue |
        residue | residue | residue | residue <;> omega
    have gap_depth : shellSlopeGapFiveDepth (offset + 1) = 0 :=
      (reboundingTable_depth_zero_iff_odd (offset + 1)).2 gap_odd
    have gap_residue_eq :=
      reboundingTable_gap_mod_twoFifty_eq_offset_mod_add_one offset gap_depth
    rw [gap_residue_eq] at accepted
    have carry_residue := reboundingSixTargetResidue_carryResidue accepted
    have base_target_unit :=
      (lengthThreeReboundingTarget_six_finiteRectangle
        (Nat.mod_lt offset (by norm_num)) (Nat.mod_lt wait (by norm_num))
        carry_residue).2 accepted
    have base_carry_value :=
      lengthThreeReboundingTarget_fiveUnit_forces_carry
        6 (offset % 250) (wait % 10) base_target_unit
    have base_terminal_unit :=
      (lengthThreeReboundingTarget_fiveUnit_iff_mod_ten
        6 (offset % 250) wait base_carry_value).2 base_target_unit
    exact (lengthThreeReboundingTarget_six_fiveUnit_iff_mod_twoFifty
      offset wait gap_depth).2 base_terminal_unit

/-- The `B = 7` target is exactly the displayed forty residue pairs. -/
theorem lengthThreeReboundingTarget_seven_fiveUnit_iff_residue
    (offset wait : ℕ) :
    IsUnit 5 (lengthThreeReboundingTarget 7 offset wait) ↔
      lengthThreeReboundingSevenTargetResidue
        ((offset + 1) % 1250) (wait % 10) := by
  constructor
  · intro target_unit
    have source_unit := lengthThreeReboundingTarget_fiveUnit_forces_source_fiveUnit
      0 7 offset wait target_unit
    have gap_depth :=
      (lengthThreeReboundingSource_seven_fiveUnit_iff 0 offset).1 source_unit
    have carry_value :=
      lengthThreeReboundingTarget_fiveUnit_forces_carry 7 offset wait target_unit
    have terminal_reduced :=
      (lengthThreeReboundingTarget_fiveUnit_iff_mod_ten
        7 offset wait carry_value).1 target_unit
    have offset_reduced :=
      (lengthThreeReboundingTarget_seven_fiveUnit_iff_mod_twelveFifty
        offset (wait % 10) gap_depth).1 terminal_reduced
    have gap_positive : 0 < offset + 1 := by omega
    obtain ⟨gap_even, half_not_dvd⟩ :=
      (reboundingTable_depth_one_iff gap_positive).1 gap_depth
    have base_even : Even (offset % 1250 + 1) := by
      obtain ⟨half, gap_eq⟩ := gap_even
      exact ⟨(offset % 1250 + 1) / 2, by omega⟩
    have base_half_not_dvd : ¬5 ∣ (offset % 1250 + 1) / 2 := by
      rw [Nat.dvd_iff_mod_eq_zero] at half_not_dvd ⊢
      omega
    have base_gap_depth :
        shellSlopeGapFiveDepth (offset % 1250 + 1) = 1 :=
      (reboundingTable_depth_one_iff (by omega)).2
        ⟨base_even, base_half_not_dvd⟩
    have base_carry_value :=
      lengthThreeReboundingTarget_fiveUnit_forces_carry
        7 (offset % 1250) (wait % 10) offset_reduced
    have carry_residue :=
      (lengthThreeReboundingTargetCarry_seven_hasValue_two_iff_residue
        (offset % 1250) base_gap_depth).1 base_carry_value
    have finite := lengthThreeReboundingTarget_seven_finiteRectangle
      (Nat.mod_lt offset (by norm_num)) (Nat.mod_lt wait (by norm_num)) carry_residue
    have accepted := finite.1 offset_reduced
    rw [reboundingTable_gap_mod_twelveFifty_eq_offset_mod_add_one offset gap_depth]
    exact accepted
  · intro accepted
    have residue_cases :
        (offset + 1) % 1250 = 82 ∨ (offset + 1) % 1250 = 232 ∨
          (offset + 1) % 1250 = 332 ∨ (offset + 1) % 1250 = 482 ∨
          (offset + 1) % 1250 = 582 ∨ (offset + 1) % 1250 = 732 ∨
          (offset + 1) % 1250 = 832 ∨ (offset + 1) % 1250 = 982 ∨
          (offset + 1) % 1250 = 1082 ∨ (offset + 1) % 1250 = 1232 := by
      rcases accepted with row | row | row | row | row | row | row | row | row | row <;>
        omega
    have gap_even : Even (offset + 1) := by
      refine ⟨(offset + 1) / 2, ?_⟩
      rcases residue_cases with residue | residue | residue | residue | residue | residue |
        residue | residue | residue | residue <;> omega
    have half_not_dvd : ¬5 ∣ (offset + 1) / 2 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      rcases residue_cases with residue | residue | residue | residue | residue | residue |
        residue | residue | residue | residue <;> omega
    have gap_depth : shellSlopeGapFiveDepth (offset + 1) = 1 :=
      (reboundingTable_depth_one_iff (by omega)).2 ⟨gap_even, half_not_dvd⟩
    have gap_residue_eq :=
      reboundingTable_gap_mod_twelveFifty_eq_offset_mod_add_one offset gap_depth
    rw [gap_residue_eq] at accepted
    have carry_residue := reboundingSevenTargetResidue_carryResidue accepted
    have base_target_unit :=
      (lengthThreeReboundingTarget_seven_finiteRectangle
        (Nat.mod_lt offset (by norm_num)) (Nat.mod_lt wait (by norm_num))
        carry_residue).2 accepted
    have base_carry_value :=
      lengthThreeReboundingTarget_fiveUnit_forces_carry
        7 (offset % 1250) (wait % 10) base_target_unit
    have base_terminal_unit :=
      (lengthThreeReboundingTarget_fiveUnit_iff_mod_ten
        7 (offset % 1250) wait base_carry_value).2 base_target_unit
    exact (lengthThreeReboundingTarget_seven_fiveUnit_iff_mod_twelveFifty
      offset wait gap_depth).2 base_terminal_unit

private theorem lengthThreeReboundingSixTargetResidue_offset_lower
    {offset wait : ℕ}
    (accepted :
      lengthThreeReboundingSixTargetResidue ((offset + 1) % 250) wait) :
    24 ≤ offset := by
  rcases accepted with row | row | row | row | row | row | row | row | row | row <;>
    omega

private theorem lengthThreeReboundingSevenTargetResidue_offset_lower
    {offset wait : ℕ}
    (accepted :
      lengthThreeReboundingSevenTargetResidue ((offset + 1) % 1250) wait) :
    81 ≤ offset := by
  rcases accepted with row | row | row | row | row | row | row | row | row | row <;>
    omega

/-- Complete guarded real-trap classifier in the `B=6` rebounding fibre. -/
theorem lengthThreeRebounding_six_acceptance_iff
    (p offset wait : ℕ) :
    lengthThreeReboundingSource p 0 (6 + offset) 6 1 ∈ Set.Icc (1 / 5) (1 / 2) ∧
        IsUnit 5 (lengthThreeReboundingTarget 6 offset wait) ↔
      (p = 3 ∨ p = 4) ∧
        lengthThreeReboundingSixTargetResidue
          ((offset + 1) % 250) (wait % 10) := by
  constructor
  · rintro ⟨source_mem, target_unit⟩
    have target_residue :=
      (lengthThreeReboundingTarget_six_fiveUnit_iff_residue offset wait).1 target_unit
    have offset_lower :=
      lengthThreeReboundingSixTargetResidue_offset_lower target_residue
    have real_cell :=
      (lengthThreeReboundingSource_six_mem_realTrap_iff p offset).1 source_mem
    rcases real_cell with first | second | third | fourth | fifth
    · omega
    · omega
    · omega
    · exact ⟨Or.inl fourth.1, target_residue⟩
    · exact ⟨Or.inr fifth.1, target_residue⟩
  · rintro ⟨p_three_or_four, target_residue⟩
    have offset_lower :=
      lengthThreeReboundingSixTargetResidue_offset_lower target_residue
    have source_mem :
        lengthThreeReboundingSource p 0 (6 + offset) 6 1 ∈ Set.Icc (1 / 5) (1 / 2) := by
      apply (lengthThreeReboundingSource_six_mem_realTrap_iff p offset).2
      rcases p_three_or_four with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, by omega⟩)))
    have target_unit :=
      (lengthThreeReboundingTarget_six_fiveUnit_iff_residue offset wait).2
        target_residue
    exact ⟨source_mem, target_unit⟩

/-- Complete guarded real-trap classifier in the `B=7` rebounding fibre. -/
theorem lengthThreeRebounding_seven_acceptance_iff
    (p offset wait : ℕ) :
    lengthThreeReboundingSource p 0 (7 + offset) 7 1 ∈ Set.Icc (1 / 5) (1 / 2) ∧
        IsUnit 5 (lengthThreeReboundingTarget 7 offset wait) ↔
      (p = 0 ∨ p = 1) ∧
        lengthThreeReboundingSevenTargetResidue
          ((offset + 1) % 1250) (wait % 10) := by
  constructor
  · rintro ⟨source_mem, target_unit⟩
    have target_residue :=
      (lengthThreeReboundingTarget_seven_fiveUnit_iff_residue offset wait).1 target_unit
    have real_cell :=
      (lengthThreeReboundingSource_seven_mem_realTrap_iff p offset).1 source_mem
    rcases real_cell with first | second
    · exact ⟨Or.inl first.1, target_residue⟩
    · exact ⟨Or.inr second.1, target_residue⟩
  · rintro ⟨p_zero_or_one, target_residue⟩
    have offset_lower :=
      lengthThreeReboundingSevenTargetResidue_offset_lower target_residue
    have source_mem :
        lengthThreeReboundingSource p 0 (7 + offset) 7 1 ∈ Set.Icc (1 / 5) (1 / 2) := by
      apply (lengthThreeReboundingSource_seven_mem_realTrap_iff p offset).2
      rcases p_zero_or_one with rfl | rfl
      · exact Or.inl ⟨rfl, by omega⟩
      · exact Or.inr ⟨rfl, by omega⟩
    have target_unit :=
      (lengthThreeReboundingTarget_seven_fiveUnit_iff_residue offset wait).2
        target_residue
    exact ⟨source_mem, target_unit⟩

end MatrixMortality.MixedPrimeDebt
