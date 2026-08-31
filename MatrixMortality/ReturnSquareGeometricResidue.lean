import MatrixMortality.ReturnSquareGeometricCenter

/-!
# Geometric residue transitions for ReturnSquare

The zero first residue on the equal-scale wall has one exact affine image.  If its next step is
an exact denominator center, the resulting cyclotomic equation is incompatible with every odd
signed-ray quotient whose next exponent is odd.
-/

namespace MatrixMortality.ReturnSquare

/-- Integer equation for a zero equal-scale residue followed by a denominator center. -/
def fractionEqualScaleZeroCenterResidue
    (q A B : ℤ) (equalExponent centerExponent : Nat) : ℤ :=
  (q ^ centerExponent * (q ^ equalExponent) ^ 2 - 1) * B -
    q ^ centerExponent * ((q ^ equalExponent) ^ 2 - 1) * A

/-- Exact transition equation from the zero equal-scale residue to the next denominator center.
No primitive normalization occurs between the two steps. -/
theorem fractionPredecessor_equalScale_zero_then_center_iff
    (q A B : ℤ) (equalExponent centerExponent : Nat) (B_ne : B ≠ 0) :
    fractionPredecessor (A : ℚ) B ((q : ℚ) ^ equalExponent)
          (((q : ℚ) ^ equalExponent) * ((A : ℚ) - B)) *
        (q : ℚ) ^ centerExponent = B ↔
      fractionEqualScaleZeroCenterResidue
        q A B equalExponent centerExponent = 0 := by
  have B_ne_rat : (B : ℚ) ≠ 0 := by exact_mod_cast B_ne
  have first_residue_zero :
      ((A : ℚ) - B) + B - A = 0 := by
    ring
  rw [fractionPredecessor_equal_scale_eq_of_residue_zero
    (A : ℚ) B ((q : ℚ) ^ equalExponent) ((A : ℚ) - B)
      B_ne_rat first_residue_zero]
  constructor
  · intro center
    have cast_residue :
        ((fractionEqualScaleZeroCenterResidue
          q A B equalExponent centerExponent : ℤ) : ℚ) = 0 := by
      norm_num [fractionEqualScaleZeroCenterResidue]
      linear_combination center
    exact_mod_cast cast_residue
  · intro residue_zero
    have cast_residue :
        ((fractionEqualScaleZeroCenterResidue
          q A B equalExponent centerExponent : ℤ) : ℚ) = 0 := by
      exact_mod_cast residue_zero
    norm_num [fractionEqualScaleZeroCenterResidue] at cast_residue
    linear_combination cast_residue

/-- In a signed-ray quotient, an odd-exponent center after the zero equal-scale residue forces
the fraction denominator to vanish. -/
theorem fractionEqualScaleZeroCenterResidue_zero_forces_denominator_mod_neg_one
    (q A B : ℤ) (equalExponent centerExponent : Nat) (ell : Nat)
    (ell_prime : ell.Prime)
    (q_neg_one : (q : ZMod ell) = -1) (center_odd : Odd centerExponent)
    (two_ne : (2 : ZMod ell) ≠ 0)
    (residue_zero :
    fractionEqualScaleZeroCenterResidue
        q A B equalExponent centerExponent = 0) :
    (B : ZMod ell) = 0 := by
  let _ : Fact ell.Prime := ⟨ell_prime⟩
  have cast_residue :
      ((fractionEqualScaleZeroCenterResidue
        q A B equalExponent centerExponent : ℤ) : ZMod ell) = 0 := by
    rw [residue_zero]
    simp
  have equal_square_one :
      (((q : ZMod ell) ^ equalExponent) ^ 2) = 1 := by
    rw [q_neg_one]
    rcases neg_one_pow_eq_or (ZMod ell) equalExponent with power_one | power_neg_one
    · rw [power_one]
      ring
    · rw [power_neg_one]
      ring
  have center_neg_one :
      (q : ZMod ell) ^ centerExponent = -1 := by
    rw [q_neg_one]
    exact center_odd.neg_one_pow
  norm_num [fractionEqualScaleZeroCenterResidue] at cast_residue
  rw [center_neg_one, equal_square_one] at cast_residue
  have two_mul_denominator : (2 : ZMod ell) * B = 0 := by
    linear_combination -cast_residue
  exact (mul_eq_zero.mp two_mul_denominator).resolve_left two_ne

/-- A mortal reduced fraction cannot satisfy the odd signed center equation after the zero
equal-scale residue. -/
theorem fractionEqualScaleZeroCenterResidue_ne_zero_of_mortal
    (q A B : ℤ) (B_ne : B ≠ 0)
    (mortal :
      IsMortal
        (ReturnFamily.pairGenerator (ambient (q : ℚ))
          (cut (-((A : ℚ) / B)))))
    (equalExponent centerExponent : Nat) (ell : Nat) (ell_prime : ell.Prime)
    (q_neg_one : (q : ZMod ell) = -1) (center_odd : Odd centerExponent)
    (two_ne : (2 : ZMod ell) ≠ 0)
    (reduced : (A : ZMod ell) ≠ 0 ∨ (B : ZMod ell) ≠ 0) :
    fractionEqualScaleZeroCenterResidue
      q A B equalExponent centerExponent ≠ 0 := by
  intro residue_zero
  have B_zero :=
    fractionEqualScaleZeroCenterResidue_zero_forces_denominator_mod_neg_one
      q A B equalExponent centerExponent ell ell_prime q_neg_one center_odd two_ne
        residue_zero
  have signed :=
    isMortal_forces_fraction_mod_neg_one
      q A B B_ne mortal ell ell_prime q_neg_one
  have A_zero : (A : ZMod ell) = 0 := by
    rcases signed with B_eq_A | B_eq_neg_A
    · rw [B_zero] at B_eq_A
      exact B_eq_A.symm
    · rw [B_zero] at B_eq_neg_A
      simpa using B_eq_neg_A
  rcases reduced with A_ne | B_ne_mod
  · exact A_ne A_zero
  · exact B_ne_mod B_zero

/-- Affine form of the odd signed-center exclusion. -/
theorem not_fractionPredecessor_equalScale_zero_then_odd_center_of_mortal
    (q A B : ℤ) (B_ne : B ≠ 0)
    (mortal :
      IsMortal
        (ReturnFamily.pairGenerator (ambient (q : ℚ))
          (cut (-((A : ℚ) / B)))))
    (equalExponent centerExponent : Nat) (ell : Nat) (ell_prime : ell.Prime)
    (q_neg_one : (q : ZMod ell) = -1) (center_odd : Odd centerExponent)
    (two_ne : (2 : ZMod ell) ≠ 0)
    (reduced : (A : ZMod ell) ≠ 0 ∨ (B : ZMod ell) ≠ 0) :
    fractionPredecessor (A : ℚ) B ((q : ℚ) ^ equalExponent)
          (((q : ℚ) ^ equalExponent) * ((A : ℚ) - B)) *
        (q : ℚ) ^ centerExponent ≠ B := by
  intro center
  apply fractionEqualScaleZeroCenterResidue_ne_zero_of_mortal
    q A B B_ne mortal equalExponent centerExponent ell ell_prime q_neg_one center_odd
      two_ne reduced
  exact (fractionPredecessor_equalScale_zero_then_center_iff
    q A B equalExponent centerExponent B_ne).mp center

end MatrixMortality.ReturnSquare
