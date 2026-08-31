import MatrixMortality.ReturnSquareFractionFiniteWall

/-!
# Geometric center chains for ReturnSquare

The exact center of the denominator-scale wall doubles its base exponent.  Iterating only this
center therefore produces one forced exponent ray, and a terminal hit on that ray is already a
one-return resonance.  The zero residue of the critical wall is incompatible with mortality in
every fixed-ray quotient where the fraction remains reduced.
-/

namespace MatrixMortality.ReturnSquare

/-- Exponent reached after `depth` exact denominator-center transitions from `seed`. -/
def fractionCenterExponent (seed depth : Nat) : Nat :=
  2 ^ depth * seed

/-- Forced geometric scales along an exact denominator-center chain. -/
def fractionCenterScales (q : ℚ) (seed : Nat) : Nat → List ℚ
  | 0 => []
  | depth + 1 => q ^ seed :: fractionCenterScales q (2 * seed) depth

/-- Successive affine pullbacks through a displayed scale word. -/
def fractionPredecessorChain (A B : ℚ) (scales : List ℚ) (state : ℚ) : ℚ :=
  scales.foldl (fun target scale => fractionPredecessor A B scale target) state

/-- One exact denominator-center transition doubles its geometric exponent. -/
theorem fractionPredecessor_eq_of_geometric_denominator_center
    (A B q : ℚ) (exponent : Nat)
    (B_sub_A_ne : B - A ≠ 0) (q_ne : q ≠ 0) :
    fractionPredecessor A B (q ^ exponent) (B / q ^ exponent) =
      B / q ^ (2 * exponent) := by
  have scale_ne : q ^ exponent ≠ 0 := pow_ne_zero exponent q_ne
  have target_scale_eq : (B / q ^ exponent) * q ^ exponent = B := by
    exact div_mul_cancel₀ B scale_ne
  rw [fractionPredecessor_eq_of_target_scale_eq_denominator
    A B (q ^ exponent) (B / q ^ exponent) B_sub_A_ne scale_ne target_scale_eq]
  have power_eq : (q ^ exponent) ^ 2 = q ^ (2 * exponent) := by
    rw [pow_two, ← pow_add]
    congr 1
    omega
  rw [power_eq]

/-- An exact denominator-center chain has no unit freedom: its exponent doubles at every
transition. -/
theorem fractionPredecessorChain_centerScales
    (A B q : ℚ) (seed depth : Nat)
    (B_sub_A_ne : B - A ≠ 0) (q_ne : q ≠ 0) :
    fractionPredecessorChain A B (fractionCenterScales q seed depth)
        (B / q ^ seed) =
      B / q ^ fractionCenterExponent seed depth := by
  induction depth generalizing seed with
  | zero => simp [fractionPredecessorChain, fractionCenterScales, fractionCenterExponent]
  | succ depth induction =>
      rw [fractionCenterScales, fractionPredecessorChain, List.foldl_cons,
        fractionPredecessor_eq_of_geometric_denominator_center
          A B q seed B_sub_A_ne q_ne]
      change
        fractionPredecessorChain A B (fractionCenterScales q (2 * seed) depth)
            (B / q ^ (2 * seed)) = _
      rw [induction (2 * seed)]
      congr 2
      simp only [fractionCenterExponent, pow_succ]
      ring

/-- If an exact denominator-center chain reaches the physical terminal coordinate `Aqʰ`, then
its fraction is already the one-return resonance with exponent `h + 2ᵈ seed`. -/
theorem fractionPredecessorChain_centerScales_terminal_forces_resonance
    (A B q : ℚ) (seed depth headExponent : Nat)
    (B_sub_A_ne : B - A ≠ 0) (q_ne : q ≠ 0)
    (terminal :
      fractionPredecessorChain A B (fractionCenterScales q seed depth)
          (B / q ^ seed) = A * q ^ headExponent) :
    B = A * q ^ (headExponent + fractionCenterExponent seed depth) := by
  rw [fractionPredecessorChain_centerScales
    A B q seed depth B_sub_A_ne q_ne] at terminal
  have exponent_ne : q ^ fractionCenterExponent seed depth ≠ 0 :=
    pow_ne_zero _ q_ne
  have cleared := (div_eq_iff exponent_ne).mp terminal
  calc
    B = A * q ^ headExponent * q ^ fractionCenterExponent seed depth := cleared
    _ = A * q ^ (headExponent + fractionCenterExponent seed depth) := by
      rw [pow_add]
      ring

/-- Ratio form of the terminal center-chain law. -/
theorem fractionPredecessorChain_centerScales_terminal_ratio
    (A B q : ℚ) (seed depth headExponent : Nat)
    (B_sub_A_ne : B - A ≠ 0) (B_ne : B ≠ 0) (q_ne : q ≠ 0)
    (terminal :
      fractionPredecessorChain A B (fractionCenterScales q seed depth)
          (B / q ^ seed) = A * q ^ headExponent) :
    A / B =
      (q ^ (headExponent + fractionCenterExponent seed depth))⁻¹ := by
  have denominator_eq :=
    fractionPredecessorChain_centerScales_terminal_forces_resonance
      A B q seed depth headExponent B_sub_A_ne q_ne terminal
  have q_power_ne :
      q ^ (headExponent + fractionCenterExponent seed depth) ≠ 0 :=
    pow_ne_zero _ q_ne
  have A_ne : A ≠ 0 := by
    intro A_zero
    rw [A_zero, zero_mul] at denominator_eq
    exact B_ne denominator_eq
  rw [denominator_eq]
  field_simp

/-- Denominator-cleared zero residue on the common-geometric critical wall. -/
def fractionCriticalIntegralResidue
    (q A B : ℤ) (exponent : Nat) : ℤ :=
  (B - A) * (q ^ exponent) ^ 2 - B

/-- The rational critical residue vanishes exactly when its integer clearing does. -/
theorem fractionCriticalResidue_geometric_eq_zero_iff
    (q A B : ℤ) (exponent : Nat) (B_ne : B ≠ 0) :
    fractionCriticalResidue (A : ℚ) B ((q : ℚ) ^ exponent) = 0 ↔
      fractionCriticalIntegralResidue q A B exponent = 0 := by
  rw [fractionCriticalResidue]
  have B_ne_rat : (B : ℚ) ≠ 0 := by exact_mod_cast B_ne
  constructor
  · intro residue_zero
    have quotient_one :
        ((B : ℚ) - A) * ((q : ℚ) ^ exponent) ^ 2 / B = 1 := by
      linarith only [residue_zero]
    have numerator_eq :
        ((B : ℚ) - A) * ((q : ℚ) ^ exponent) ^ 2 = B :=
      (div_eq_one_iff_eq B_ne_rat).mp quotient_one
    have cleared_rat :
        (((B - A) * (q ^ exponent) ^ 2 - B : ℤ) : ℚ) = 0 := by
      norm_num
      exact sub_eq_zero.mpr numerator_eq
    exact_mod_cast cleared_rat
  · intro cleared_zero
    have cleared_zero_rat :
        (((B - A) * (q ^ exponent) ^ 2 - B : ℤ) : ℚ) = 0 := by
      exact_mod_cast cleared_zero
    norm_num at cleared_zero_rat
    have numerator_eq :
        ((B : ℚ) - A) * ((q : ℚ) ^ exponent) ^ 2 = B :=
      sub_eq_zero.mp cleared_zero_rat
    exact sub_eq_zero.mpr ((div_eq_one_iff_eq B_ne_rat).2 numerator_eq)

/-- When the base is one in a quotient, a zero critical residue forces the fraction numerator
to vanish there. -/
theorem fractionCriticalIntegralResidue_zero_forces_numerator_mod_one
    (q A B : ℤ) (exponent : Nat) (ell : Nat)
    (q_one : (q : ZMod ell) = 1)
    (residue_zero : fractionCriticalIntegralResidue q A B exponent = 0) :
    (A : ZMod ell) = 0 := by
  have cast_zero :
      ((fractionCriticalIntegralResidue q A B exponent : ℤ) : ZMod ell) = 0 := by
    rw [residue_zero]
    simp
  simpa [fractionCriticalIntegralResidue, q_one] using cast_zero

/-- Mortality excludes the exact zero residue of a common-geometric critical wall whenever a
fixed-ray quotient sees a reduced numerator-denominator pair. -/
theorem fractionCriticalIntegralResidue_ne_zero_of_mortal
    (q A B : ℤ) (B_ne : B ≠ 0)
    (mortal :
      IsMortal
        (ReturnFamily.pairGenerator (ambient (q : ℚ))
          (cut (-((A : ℚ) / B)))))
    (exponent : Nat) (ell : Nat) (ell_prime : ell.Prime)
    (q_one : (q : ZMod ell) = 1)
    (reduced : (A : ZMod ell) ≠ 0 ∨ (B : ZMod ell) ≠ 0) :
    fractionCriticalIntegralResidue q A B exponent ≠ 0 := by
  intro residue_zero
  have A_zero :=
    fractionCriticalIntegralResidue_zero_forces_numerator_mod_one
      q A B exponent ell q_one residue_zero
  have B_eq_A :=
    isMortal_forces_fraction_mod_one
      q A B B_ne mortal ell ell_prime q_one
  have B_zero : (B : ZMod ell) = 0 := B_eq_A.trans A_zero
  rcases reduced with A_ne | B_ne_mod
  · exact A_ne A_zero
  · exact B_ne_mod B_zero

/-- Rational form of the critical-center exclusion. -/
theorem fractionCriticalResidue_geometric_ne_zero_of_mortal
    (q A B : ℤ) (B_ne : B ≠ 0)
    (mortal :
      IsMortal
        (ReturnFamily.pairGenerator (ambient (q : ℚ))
          (cut (-((A : ℚ) / B)))))
    (exponent : Nat) (ell : Nat) (ell_prime : ell.Prime)
    (q_one : (q : ZMod ell) = 1)
    (reduced : (A : ZMod ell) ≠ 0 ∨ (B : ZMod ell) ≠ 0) :
    fractionCriticalResidue (A : ℚ) B ((q : ℚ) ^ exponent) ≠ 0 := by
  intro residue_zero
  apply fractionCriticalIntegralResidue_ne_zero_of_mortal
    q A B B_ne mortal exponent ell ell_prime q_one reduced
  exact (fractionCriticalResidue_geometric_eq_zero_iff
    q A B exponent B_ne).mp residue_zero

end MatrixMortality.ReturnSquare
