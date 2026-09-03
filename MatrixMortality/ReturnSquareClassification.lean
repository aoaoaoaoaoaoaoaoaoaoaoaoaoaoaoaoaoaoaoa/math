import MatrixMortality.ReturnSquarePrimePower

/-!
# Prime-power ReturnSquare classification

The bridge-polynomial support theorem reduces every negative rational parameter to one
prime. Finite quotient walls eliminate exponents misaligned with the prime-power base.
-/

namespace MatrixMortality.ReturnSquare

open scoped Matrix

noncomputable section

/-- Prime-power ReturnSquare classification from an exact finite-wall obligation. -/
theorem physical_isMortal_primePower_iff_of_finiteWalls
    (p r : Nat) (prime : p.Prime) (r_positive : 0 < r)
    (finite_wall :
      ∀ power : Nat, ¬r ∣ power →
        HasFiniteWall (p ^ r : Nat) (p ^ power : Nat))
    (c : ℚ) :
    IsMortal
        (ReturnFamily.pairGenerator (ambient ((p ^ r : Nat) : ℚ)) (cut c)) ↔
      ∃ power : Nat, c = -(((p ^ r : Nat) : ℚ) ^ power)⁻¹ := by
  have p_two : 2 ≤ p := prime.two_le
  have q_two_nat : 2 ≤ p ^ r := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero r_positive.ne'
    rw [pow_succ]
    have one_le : 1 ≤ p ^ k := one_le_pow₀ prime.one_le
    nlinarith
  have q_two_int : 2 ≤ ((p ^ r : Nat) : ℤ) := by exact_mod_cast q_two_nat
  constructor
  · intro mortal
    by_cases c_neg_one : c = -1
    · exact ⟨0, by simp [c_neg_one]⟩
    have c_add_one_ne : c + 1 ≠ 0 := by
      intro sum_zero
      apply c_neg_one
      linarith only [sum_zero]
    have c_negative : c < 0 := by
      by_contra not_negative
      have c_nonnegative : 0 ≤ c := le_of_not_gt not_negative
      exact not_physical_isMortal_of_nonneg
        ((p ^ r : Nat) : ℤ) c q_two_int c_nonnegative mortal
    obtain ⟨waits, bridge_zero⟩ :=
      (physical_isMortal_iff_positiveBridge
        ((p ^ r : Nat) : ℤ) c (by positivity)).mp mortal
    let d := -c
    have d_positive : 0 < d := by dsimp [d]; linarith
    have d_ne_one : d ≠ 1 := by
      intro d_one
      apply c_neg_one
      dsimp [d] at d_one
      linarith only [d_one]
    have bridge_zero_neg :
        positiveBridge (((p ^ r : Nat) : ℚ)) (-d) waits = 0 := by
      simpa [d] using bridge_zero
    obtain ⟨power, power_shape | reciprocal_shape⟩ :=
      positiveBridge_zero_primePower_shape
        p r prime d d_positive d_ne_one waits bridge_zero_neg
    · have power_positive : 0 < power := by
        apply Nat.pos_of_ne_zero
        intro power_zero
        rw [power_zero, pow_zero] at power_shape
        exact d_ne_one power_shape
      have d_beyond :
          1 + (((p ^ r : Nat) : ℚ) - 1) / (((p ^ r : Nat) : ℚ) ^ 2) <
            (p : ℚ) ^ power := by
        have q_two : (2 : ℚ) ≤ (p ^ r : Nat) := by exact_mod_cast q_two_nat
        have q_positive : (0 : ℚ) < (p ^ r : Nat) := by linarith
        have ratio_lt_one :
            ((((p ^ r : Nat) : ℚ) - 1) / (((p ^ r : Nat) : ℚ) ^ 2) < 1) := by
          rw [div_lt_one (sq_pos_of_pos q_positive)]
          nlinarith [sq_nonneg ((((p ^ r : Nat) : ℚ) - 1))]
        obtain ⟨k, rfl⟩ :=
          Nat.exists_eq_succ_of_ne_zero power_positive.ne'
        have p_power_ge_p : (p : ℚ) ≤ (p : ℚ) ^ Nat.succ k := by
          rw [pow_succ]
          have one_le : (1 : ℚ) ≤ (p : ℚ) ^ k :=
            one_le_pow₀ (by exact_mod_cast prime.one_le)
          simpa using
            mul_le_mul_of_nonneg_right one_le (by positivity : (0 : ℚ) ≤ p)
        calc
          1 + (((p ^ r : Nat) : ℚ) - 1) / (((p ^ r : Nat) : ℚ) ^ 2) <
              2 := by linarith
          _ ≤ (p : ℚ) := by exact_mod_cast p_two
          _ ≤ (p : ℚ) ^ Nat.succ k := p_power_ge_p
      have immortal :=
        not_physical_isMortal_of_beyond_negative_wall
          ((p ^ r : Nat) : ℤ) ((p : ℚ) ^ power) q_two_int d_beyond
      have c_eq : c = -((p : ℚ) ^ power) := by
        dsimp [d] at power_shape
        linarith only [power_shape]
      rw [c_eq] at mortal
      exact (immortal mortal).elim
    · by_cases divisible : r ∣ power
      · obtain ⟨quotient, rfl⟩ := divisible
        refine ⟨quotient, ?_⟩
        dsimp [d] at reciprocal_shape
        rw [pow_mul] at reciprocal_shape
        norm_cast at reciprocal_shape ⊢
        linarith only [reciprocal_shape]
      · have wall := finite_wall power divisible
        have denominator_ne : ((p ^ power : Nat) : ℤ) ≠ 0 := by
          exact_mod_cast pow_ne_zero power prime.ne_zero
        have immortal :=
          not_physical_isMortal_of_finiteWall
            ((p ^ r : Nat) : ℤ) ((p ^ power : Nat) : ℤ) denominator_ne wall
        have c_eq : c = -((p : ℚ) ^ power)⁻¹ := by
          dsimp [d] at reciprocal_shape
          linarith only [reciprocal_shape]
        rw [c_eq] at mortal
        apply (immortal ?_).elim
        simpa using mortal
  · rintro ⟨power, rfl⟩
    exact physical_isMortal_of_resonance
      ((p ^ r : Nat) : ℤ) q_two_int power

/-- Complete ReturnSquare classification at every prime-power base. No multi-return word
introduces a rational mortal parameter beyond the one-return resonances. -/
theorem physical_isMortal_primePower_iff
    (p r : Nat) (prime : p.Prime) (r_positive : 0 < r) (c : ℚ) :
    IsMortal
        (ReturnFamily.pairGenerator (ambient ((p ^ r : Nat) : ℚ)) (cut c)) ↔
      ∃ power : Nat, c = -(((p ^ r : Nat) : ℚ) ^ power)⁻¹ :=
  physical_isMortal_primePower_iff_of_finiteWalls p r prime r_positive
    (hasFiniteWall_primePower p r · prime r_positive) c

end

end MatrixMortality.ReturnSquare
