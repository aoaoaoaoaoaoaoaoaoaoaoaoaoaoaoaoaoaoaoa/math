import MatrixMortality.ReturnSquareFractionPullback

/-!
# Fractional finite walls for ReturnSquare

This file extends the fixed- and signed-ray finite quotients from reciprocal-integer parameters
to every rational fraction `d=A/B`. Any mortal fraction must reduce to `A/B=1` whenever the base
does, and to `A/B=±1` whenever the base reduces to `-1`.
-/

namespace MatrixMortality.ReturnSquare

open scoped Matrix

/-- Denominator-cleared physical cut at parameter `c=-A/B`. -/
def fractionIntegralScaledCut (A B : ℤ) : Square (Fin 3) ℤ :=
  !![-B, B, B - A;
     -A, B, 0;
     -B, B, B - A]

/-- Integer ReturnSquare pair obtained after clearing a general cut denominator. -/
def fractionIntegralGenerator (q A B : ℤ) : Option Unit → Square (Fin 3) ℤ :=
  ReturnFamily.pairGenerator (ambient q) (fractionIntegralScaledCut A B)

/-- The general cleared cut specializes to the earlier reciprocal-integer cut at `A=1`. -/
theorem fractionIntegralScaledCut_one (B : ℤ) :
    fractionIntegralScaledCut 1 B = integralScaledCut B := by
  rfl

/-- Casting the cleared cut recovers `B` times the rational physical cut. -/
theorem cast_fractionIntegralScaledCut (A B : ℤ) (B_ne : B ≠ 0) :
    castMatrix (fractionIntegralScaledCut A B) =
      (B : ℚ) • cut (-((A : ℚ) / B)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fractionIntegralScaledCut, cut_eq, castMatrix, Matrix.smul_apply]
  all_goals field_simp
  all_goals ring

/-- Clearing a general rational cut denominator preserves mortality exactly. -/
theorem fractionIntegralGenerator_isMortal_iff
    (q A B : ℤ) (B_ne : B ≠ 0) :
    IsMortal (fractionIntegralGenerator q A B) ↔
      IsMortal
        (ReturnFamily.pairGenerator (ambient (q : ℚ))
          (cut (-((A : ℚ) / B)))) := by
  let scale : Option Unit → ℚ
    | none => B
    | some _ => 1
  let rational :=
    ReturnFamily.pairGenerator (ambient (q : ℚ))
      (cut (-((A : ℚ) / B)))
  have scale_ne : ∀ label, scale label ≠ 0 := by
    intro label
    cases label with
    | none =>
        have cast_ne : (B : ℚ) ≠ 0 := by exact_mod_cast B_ne
        simpa [scale] using cast_ne
    | some _ => simp [scale]
  have cast_family :
      castMatrix ∘ fractionIntegralGenerator q A B =
        fun label => scale label • rational label := by
    funext label
    cases label with
    | none =>
        simpa [fractionIntegralGenerator, rational, scale] using
          cast_fractionIntegralScaledCut A B B_ne
    | some _ =>
        simp [fractionIntegralGenerator, rational, scale, cast_ambient]
  rw [← isMortal_cast_iff (fractionIntegralGenerator q A B), cast_family,
    isMortal_smulMatrix_iff scale scale_ne rational]

/-- The positive ray remains common when the ambient base reduces to one. -/
theorem mapped_fractionIntegralGenerator_positiveRay
    (q A B : ℤ) (ell : Nat)
    (q_one : (q : ZMod ell) = 1) (label : Option Unit) :
    Matrix.mulVec
        ((fractionIntegralGenerator q A B label).map
          (Int.castRingHom (ZMod ell))) positiveRay =
      (match label with
        | none => (B : ZMod ell) - A
        | some _ => 1) • positiveRay := by
  cases label with
  | none =>
      ext i
      fin_cases i <;>
        simp [fractionIntegralGenerator, fractionIntegralScaledCut, positiveRay,
          Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      all_goals ring
  | some _ =>
      ext i
      fin_cases i <;>
        simp [fractionIntegralGenerator, ambient, positiveRay, Matrix.mulVec,
          dotProduct, Matrix.diagonal_apply, q_one]

/-- A quotient with `q=1` but `B≠A` certifies immortality of the cleared fraction. -/
theorem not_fractionIntegralGenerator_isMortal_of_mod_one
    (q A B : ℤ) (ell : Nat) (ell_prime : ell.Prime)
    (q_one : (q : ZMod ell) = 1)
    (B_ne_A : (B : ZMod ell) ≠ A) :
    ¬IsMortal (fractionIntegralGenerator q A B) := by
  let _ : Fact ell.Prime := ⟨ell_prime⟩
  let quotient :=
    ((Int.castRingHom (ZMod ell)).mapMatrix (m := Fin 3)).toMonoidWithZeroHom
  apply not_isMortal_of_map_not_isMortal quotient
    (fractionIntegralGenerator q A B)
  apply not_isMortal_of_common_eigenvector
    (quotient ∘ fractionIntegralGenerator q A B) positiveRay
    (fun label => match label with
      | none => (B : ZMod ell) - A
      | some _ => 1)
  · intro ray_zero
    have entry := congrFun ray_zero 0
    norm_num [positiveRay] at entry
  · intro label
    cases label with
    | none => exact sub_ne_zero.mpr B_ne_A
    | some _ => simp
  · intro label
    simpa [quotient, Function.comp_def] using
      mapped_fractionIntegralGenerator_positiveRay q A B ell q_one label

/-- Nonzero weights for the two signed rays at a general rational fraction. -/
def fractionSignedRayWeight {R : Type*} [Ring R] (A B : R) :
    Option Unit → Bool → R
  | none, false => B - A
  | none, true => -(B + A)
  | some _, _ => 1

/-- The positive and alternating rays remain closed when the ambient base reduces to `-1`. -/
theorem mapped_fractionIntegralGenerator_signedRay
    (q A B : ℤ) (ell : Nat)
    (q_neg_one : (q : ZMod ell) = -1)
    (label : Option Unit) (state : Bool) :
    Matrix.mulVec
        ((fractionIntegralGenerator q A B label).map
          (Int.castRingHom (ZMod ell)))
        (if state then alternatingRay else positiveRay) =
      fractionSignedRayWeight (A : ZMod ell) B label state •
        (if signedRayTransition label state then alternatingRay else positiveRay) := by
  cases label with
  | none =>
      cases state <;>
        ext i <;>
        fin_cases i <;>
        simp [fractionIntegralGenerator, fractionIntegralScaledCut, positiveRay,
          alternatingRay, fractionSignedRayWeight, signedRayTransition,
          Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      all_goals ring
  | some _ =>
      cases state <;>
        ext i <;>
        fin_cases i <;>
        simp [fractionIntegralGenerator, ambient, positiveRay, alternatingRay,
          fractionSignedRayWeight, signedRayTransition, Matrix.mulVec,
          dotProduct, Matrix.diagonal_apply, q_neg_one]

/-- A quotient with `q=-1` but `B≠±A` certifies immortality of the cleared fraction. -/
theorem not_fractionIntegralGenerator_isMortal_of_mod_neg_one
    (q A B : ℤ) (ell : Nat) (ell_prime : ell.Prime)
    (q_neg_one : (q : ZMod ell) = -1)
    (B_ne_A : (B : ZMod ell) ≠ A)
    (B_ne_neg_A : (B : ZMod ell) ≠ -A) :
    ¬IsMortal (fractionIntegralGenerator q A B) := by
  let _ : Fact ell.Prime := ⟨ell_prime⟩
  let quotient :=
    ((Int.castRingHom (ZMod ell)).mapMatrix (m := Fin 3)).toMonoidWithZeroHom
  apply not_isMortal_of_map_not_isMortal quotient
    (fractionIntegralGenerator q A B)
  apply not_isMortal_of_ray_action
    (quotient ∘ fractionIntegralGenerator q A B)
    (fun state => if state then alternatingRay else positiveRay)
    signedRayTransition (fractionSignedRayWeight (A : ZMod ell) B) false
  · intro state ray_zero
    have entry := congrFun ray_zero 0
    cases state <;> norm_num [positiveRay, alternatingRay] at entry
  · intro label state
    cases label with
    | none =>
        cases state
        · exact sub_ne_zero.mpr B_ne_A
        · apply neg_ne_zero.mpr
          intro sum_zero
          apply B_ne_neg_A
          simpa using (add_eq_zero_iff_eq_neg.mp sum_zero)
    | some _ => simp [fractionSignedRayWeight]
  · intro label state
    simpa [quotient, Function.comp_def] using
      mapped_fractionIntegralGenerator_signedRay
        q A B ell q_neg_one label state

/-- A fixed- or signed-ray finite wall for a general cleared fraction `A/B`. -/
def HasFractionFiniteWall (q A B : ℤ) : Prop :=
  ∃ ell : Nat, ell.Prime ∧
    (((q : ZMod ell) = 1 ∧ (B : ZMod ell) ≠ A) ∨
      ((q : ZMod ell) = -1 ∧
        (B : ZMod ell) ≠ A ∧ (B : ZMod ell) ≠ -A))

/-- A fractional finite wall excludes the corresponding rational ReturnSquare parameter. -/
theorem not_physical_isMortal_of_fractionFiniteWall
    (q A B : ℤ) (B_ne : B ≠ 0)
    (wall : HasFractionFiniteWall q A B) :
    ¬IsMortal
      (ReturnFamily.pairGenerator (ambient (q : ℚ))
        (cut (-((A : ℚ) / B)))) := by
  intro mortal
  have integral_mortal :=
    (fractionIntegralGenerator_isMortal_iff q A B B_ne).mpr mortal
  obtain ⟨ell, ell_prime, fixed | alternating⟩ := wall
  · exact not_fractionIntegralGenerator_isMortal_of_mod_one
      q A B ell ell_prime fixed.1 fixed.2 integral_mortal
  · exact not_fractionIntegralGenerator_isMortal_of_mod_neg_one
      q A B ell ell_prime alternating.1 alternating.2.1 alternating.2.2
        integral_mortal

/-- Mortality forces `A/B=1` in every prime quotient where the base becomes one. -/
theorem isMortal_forces_fraction_mod_one
    (q A B : ℤ) (B_ne : B ≠ 0)
    (mortal :
      IsMortal
        (ReturnFamily.pairGenerator (ambient (q : ℚ))
          (cut (-((A : ℚ) / B)))))
    (ell : Nat) (ell_prime : ell.Prime)
    (q_one : (q : ZMod ell) = 1) :
    (B : ZMod ell) = A := by
  by_contra B_ne_A
  exact not_physical_isMortal_of_fractionFiniteWall q A B B_ne
    ⟨ell, ell_prime, Or.inl ⟨q_one, B_ne_A⟩⟩ mortal

/-- Mortality forces `A/B=±1` in every prime quotient where the base becomes `-1`. -/
theorem isMortal_forces_fraction_mod_neg_one
    (q A B : ℤ) (B_ne : B ≠ 0)
    (mortal :
      IsMortal
        (ReturnFamily.pairGenerator (ambient (q : ℚ))
          (cut (-((A : ℚ) / B)))))
    (ell : Nat) (ell_prime : ell.Prime)
    (q_neg_one : (q : ZMod ell) = -1) :
    (B : ZMod ell) = A ∨ (B : ZMod ell) = -A := by
  by_contra neither
  push Not at neither
  exact not_physical_isMortal_of_fractionFiniteWall q A B B_ne
    ⟨ell, ell_prime, Or.inr ⟨q_neg_one, neither.1, neither.2⟩⟩ mortal

/-- Integer congruence form of the fixed-ray law. -/
theorem isMortal_forces_fraction_modEq_one
    (q A B : ℤ) (B_ne : B ≠ 0)
    (mortal :
      IsMortal
        (ReturnFamily.pairGenerator (ambient (q : ℚ))
          (cut (-((A : ℚ) / B)))))
    (ell : Nat) (ell_prime : ell.Prime)
    (q_one : Int.ModEq ell q 1) :
    Int.ModEq ell B A := by
  have q_one_cast : (q : ZMod ell) = 1 := by
    simpa using (ZMod.intCast_eq_intCast_iff q 1 ell).2 q_one
  have fraction_one :=
    isMortal_forces_fraction_mod_one
      q A B B_ne mortal ell ell_prime q_one_cast
  exact (ZMod.intCast_eq_intCast_iff _ _ _).1 fraction_one

/-- Integer congruence form of the signed-ray law. -/
theorem isMortal_forces_fraction_modEq_neg_one
    (q A B : ℤ) (B_ne : B ≠ 0)
    (mortal :
      IsMortal
        (ReturnFamily.pairGenerator (ambient (q : ℚ))
          (cut (-((A : ℚ) / B)))))
    (ell : Nat) (ell_prime : ell.Prime)
    (q_neg_one : Int.ModEq ell q (-1)) :
    Int.ModEq ell B A ∨ Int.ModEq ell B (-A) := by
  have q_neg_one_cast : (q : ZMod ell) = -1 := by
    simpa using (ZMod.intCast_eq_intCast_iff q (-1) ell).2 q_neg_one
  rcases isMortal_forces_fraction_mod_neg_one
      q A B B_ne mortal ell ell_prime q_neg_one_cast with
    fraction_one | fraction_neg_one
  · exact Or.inl ((ZMod.intCast_eq_intCast_iff _ _ _).1 fraction_one)
  · have fraction_neg_one' :
        (B : ZMod ell) = ((-A : ℤ) : ZMod ell) := by
      simpa using fraction_neg_one
    exact Or.inr ((ZMod.intCast_eq_intCast_iff _ _ _).1 fraction_neg_one')

/-- Every prime divisor of `q-1` must also divide the cleared fraction difference `B-A`. -/
theorem isMortal_forces_prime_dvd_fraction_sub_of_dvd_q_sub_one
    (q A B : ℤ) (B_ne : B ≠ 0)
    (mortal :
      IsMortal
        (ReturnFamily.pairGenerator (ambient (q : ℚ))
          (cut (-((A : ℚ) / B)))))
    (ell : Nat) (ell_prime : ell.Prime)
    (ell_dvd : (ell : ℤ) ∣ q - 1) :
    (ell : ℤ) ∣ B - A := by
  have q_one : Int.ModEq ell q 1 := by
    rw [Int.modEq_iff_dvd]
    simpa using (dvd_neg.mpr ell_dvd)
  have fraction_one :=
    isMortal_forces_fraction_modEq_one
      q A B B_ne mortal ell ell_prime q_one
  rw [Int.modEq_iff_dvd] at fraction_one
  simpa using (dvd_neg.mpr fraction_one)

/-- Every prime divisor of `q+1` must divide one of the cleared fraction signs `B-A` or
`B+A`. -/
theorem isMortal_forces_prime_dvd_fraction_sign_of_dvd_q_add_one
    (q A B : ℤ) (B_ne : B ≠ 0)
    (mortal :
      IsMortal
        (ReturnFamily.pairGenerator (ambient (q : ℚ))
          (cut (-((A : ℚ) / B)))))
    (ell : Nat) (ell_prime : ell.Prime)
    (ell_dvd : (ell : ℤ) ∣ q + 1) :
    (ell : ℤ) ∣ B - A ∨ (ell : ℤ) ∣ B + A := by
  have q_neg_one : Int.ModEq ell q (-1) := by
    rw [Int.modEq_iff_dvd]
    obtain ⟨multiple, multiple_eq⟩ := ell_dvd
    refine ⟨-multiple, ?_⟩
    linear_combination -multiple_eq
  rcases isMortal_forces_fraction_modEq_neg_one
      q A B B_ne mortal ell ell_prime q_neg_one with
    fraction_one | fraction_neg_one
  · rw [Int.modEq_iff_dvd] at fraction_one
    exact Or.inl (by simpa using (dvd_neg.mpr fraction_one))
  · exact Or.inr (by
      rw [Int.modEq_iff_dvd] at fraction_neg_one
      simpa using (dvd_neg.mpr fraction_neg_one))

end MatrixMortality.ReturnSquare
