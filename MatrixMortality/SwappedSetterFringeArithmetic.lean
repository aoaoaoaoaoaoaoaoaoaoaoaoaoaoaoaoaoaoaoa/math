import MatrixMortality.SwappedSetterFringeLanguage

/-!
# Arithmetic of complete swapped-setter fringe blocks

Complete `{0, 110}` spellings have a terminal ternary digit rigid enough to exclude the two
high-width divisibility mimics in the all-ones source branch.
-/

namespace MatrixMortality.SwappedSetterFringe

/-- A complete block spelling is empty, or its swapped ternary code is two modulo three. -/
theorem swappedCode_spell_fringeBlock_zero_or_modEq_two (phases : List Bool) :
    swappedCode (spell fringeBlock phases) = 0 ∨
      swappedCode (spell fringeBlock phases) ≡ 2 [MOD 3] := by
  induction phases using List.reverseRecOn with
  | nil => exact Or.inl rfl
  | append_singleton phases phase induction =>
      right
      rw [spell_append]
      rw [show spell fringeBlock [phase] = fringeBlock phase by simp [spell]]
      rw [Nat.ModEq]
      unfold swappedCode
      rw [List.map_append]
      rw [ternaryCode_append]
      cases phase with
      | false => norm_num [fringeBlock, ternaryCode, ternaryDigit, Nat.ofDigits]
      | true =>
          norm_num [fringeBlock, ternaryCode, ternaryDigit, Nat.ofDigits]
          omega

/-- Twice the swapped code of a complete block spelling, plus one, is a ternary unit. -/
theorem three_not_dvd_twice_swappedCode_spell_fringeBlock_add_one (phases : List Bool) :
    ¬3 ∣ 2 * swappedCode (spell fringeBlock phases) + 1 := by
  intro divisibility
  rcases swappedCode_spell_fringeBlock_zero_or_modEq_two phases with zero | residue
  · rw [zero] at divisibility
    norm_num at divisibility
  · have twice := residue.mul_left 2
    have shifted := twice.add (Nat.ModEq.refl 1)
    have nonzero : 2 * swappedCode (spell fringeBlock phases) + 1 ≡ 2 [MOD 3] := by
      norm_num at shifted ⊢
      exact shifted
    have zero : 2 * swappedCode (spell fringeBlock phases) + 1 ≡ 0 [MOD 3] :=
      Nat.modEq_zero_iff_dvd.mpr divisibility
    have impossible := nonzero.symm.trans zero
    norm_num at impossible

/-- A ternary unit cannot supply the missing sixth factor of three in `486 = 2 · 3⁵`. -/
theorem pow_three_not_dvd_486_mul_of_unit {β x : Nat} (β_large : 6 ≤ β)
    (unit : ¬3 ∣ 2 * x + 1) :
    ¬3 ^ β ∣ 486 * (2 * x + 1) := by
  intro divisibility
  have low_power : 3 ^ 6 ∣ 3 ^ β := Nat.pow_dvd_pow 3 β_large
  have low_dvd : 3 ^ 6 ∣ 486 * (2 * x + 1) := low_power.trans divisibility
  have factored : 3 ^ 5 * 3 ∣ 3 ^ 5 * (2 * (2 * x + 1)) := by
    convert low_dvd using 1
    · norm_num
    · ring
  have three_dvd_twice : 3 ∣ 2 * (2 * x + 1) :=
    Nat.dvd_of_mul_dvd_mul_left (pow_pos (by norm_num) 5) factored
  rcases (Nat.prime_three.dvd_mul).mp three_dvd_twice with three_dvd_two | three_dvd_unit
  · norm_num at three_dvd_two
  · exact unit three_dvd_unit

/-- The fixed mimic `10206 = 14 · 3⁶` has insufficient ternary depth from width seven onward. -/
theorem pow_three_not_dvd_10206 {β : Nat} (β_large : 7 ≤ β) :
    ¬3 ^ β ∣ 10206 := by
  intro divisibility
  have low_power : 3 ^ 7 ∣ 3 ^ β := Nat.pow_dvd_pow 3 β_large
  have low_dvd : 3 ^ 7 ∣ 10206 := low_power.trans divisibility
  norm_num at low_dvd

end MatrixMortality.SwappedSetterFringe
