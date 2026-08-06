import MatrixMortality.ParabolicBlade

/-!
# Residue-two wall for the parabolic blade

After one uniform integral clearing, every gap congruent to zero or one modulo three acts on a
two-ray automaton over `ZMod 3` with nonzero transition weight. Hence every zero atom word must
contain a gap congruent to two modulo three.
-/

namespace MatrixMortality

open scoped Matrix

namespace ParabolicBlade

private def liftResidue (quotient residue : ℤ) : ℤ := 3 * quotient + residue

@[simp]
private theorem cast_liftResidue (quotient residue : ℤ) :
    ((liftResidue quotient residue : ℤ) : ZMod 3) = (residue : ZMod 3) := by
  push_cast [liftResidue]
  have h3 : (3 : ZMod 3) = 0 := by decide
  linear_combination (quotient : ZMod 3) * h3

/-- The atom alphabet on the safe side of the residue-two wall. The Boolean records whether the
gap is `3j` or `3j+1`. -/
def residueTwoWallGenerator (β : Nat) (body : List TagLetter) :
    TagLetter × Nat × Bool → Matrix (Fin 3) (Fin 3) ℚ
  | (letter, j, false) => atom β body letter (3 * j)
  | (letter, j, true) => atom β body letter (3 * j + 1)

/-- Sixty-four times each residue-zero or residue-one atom, represented integrally. -/
private def numerator (β : Nat) (body : List TagLetter) :
    TagLetter × Nat × Bool → Matrix (Fin 3) (Fin 3) ℤ
  | (.b, j, false) =>
      let ρ : ℤ := 3 ^ β
      !![liftResidue 21 1, liftResidue (160 * ρ + 10) 2,
          liftResidue (1024 * j + 42) 2;
         0, liftResidue (192 * ρ) 0, 0;
         0, 0, liftResidue (512 * j + 64) 0]
  | (.b, j, true) =>
      let ρ : ℤ := 3 ^ β
      !![liftResidue (768 * ρ - 48) 0, liftResidue (144 - 768 * ρ) 0,
          liftResidue (1024 * j + 384) 0;
         liftResidue (192 * ρ) 0, liftResidue (-192 * ρ) 0, 0;
         liftResidue (304 * ρ - 30) 2, liftResidue (88 - 304 * ρ) 0,
          liftResidue (512 * j + 234) 2]
  | (.c, j, false) =>
      let K : ℤ := ternaryCode (true :: tagEncode β body)
      let P : ℤ := 3 ^ (tagEncode β body).length
      !![liftResidue 21 1, liftResidue 42 2,
          liftResidue (384 * K * j + 256 * j + 42) 2;
         0, liftResidue 64 0, 0;
         0, 0, liftResidue (64 * j * (9 * P - 1) + 64) 0]
  | (.c, j, true) =>
      let ρ : ℤ := 3 ^ β
      let K : ℤ := ternaryCode (true :: tagEncode β body)
      let P : ℤ := 3 ^ (tagEncode β body).length
      !![liftResidue (228 * K * ρ - 22 * K + 152 * ρ + 28) 0,
          liftResidue (-228 * K * ρ + 66 * K - 152 * ρ - 20) 0,
          liftResidue (384 * K * j + 128 * K + 256 * j + 128) 0;
         liftResidue 64 0, liftResidue (-64) 0, 0;
         liftResidue (342 * P * ρ - 33 * P - 38 * ρ + 3) 2,
          liftResidue (-342 * P * ρ + 99 * P + 38 * ρ - 11) 0,
          liftResidue (576 * P * j + 192 * P - 64 * j + 42) 2]

private theorem cAtom_three_mul_add_one (ρ L M : ℚ) (j : Nat) :
    cAtom ρ L M (3 * j + 1) =
      !![2 + (L - 1) * (114 * ρ - 11) / 96,
          -3 - (L - 1) * (38 * ρ - 11) / 32,
          2 * L / 3 + 2 * j * (L - 1) + 4 / 3;
         3, -3, 0;
         (M - 3) * (114 * ρ - 11) / 192,
          -(M - 3) * (38 * ρ - 11) / 64,
          M / 3 + j * (M - 3) + 2] := by
  rw [cAtom, pow_add, normalRoot_pow_three_mul]
  simp only [pow_one]
  ext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [cFlank, flank, drift, normalRoot, injection, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    ring

private theorem cast_numerator_b_zero (β : Nat) (body : List TagLetter) (j : Nat) :
    castMatrix (numerator β body (.b, j, false)) =
      (64 : ℚ) • residueTwoWallGenerator β body (.b, j, false) := by
  rw [show residueTwoWallGenerator β body (.b, j, false) =
      bAtom ((3 : ℚ) ^ β) (3 * j) by rfl,
    bAtom, normalRoot_pow_three_mul]
  ext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [numerator, liftResidue, bFlank, flank, drift, injection, castMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

private theorem cast_numerator_b_one (β : Nat) (body : List TagLetter) (j : Nat) :
    castMatrix (numerator β body (.b, j, true)) =
      (64 : ℚ) • residueTwoWallGenerator β body (.b, j, true) := by
  rw [show residueTwoWallGenerator β body (.b, j, true) =
      bAtom ((3 : ℚ) ^ β) (3 * j + 1) by rfl,
    bAtom, pow_add, normalRoot_pow_three_mul]
  simp only [pow_one]
  ext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [numerator, liftResidue, bFlank, flank, drift, normalRoot, injection, castMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

private theorem cast_numerator_c_zero (β : Nat) (body : List TagLetter) (j : Nat) :
    castMatrix (numerator β body (.c, j, false)) =
      (64 : ℚ) • residueTwoWallGenerator β body (.c, j, false) := by
  rw [show residueTwoWallGenerator β body (.c, j, false) =
      cAtom ((3 : ℚ) ^ β) (nearySideLowerC β body)
        (nearySideLowerCScale β body) (3 * j) by rfl,
    cAtom, normalRoot_pow_three_mul,
    nearySideLowerC_eq_nine_mul_add_seven]
  rw [show nearySideLowerCScale β body =
      27 * (3 : ℚ) ^ (tagEncode β body).length by
        rw [nearySideLowerCScale_eq_nine_mul, pow_succ]
        ring]
  ext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [numerator, liftResidue, cFlank, flank, drift, injection, castMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

private theorem cast_numerator_c_one (β : Nat) (body : List TagLetter) (j : Nat) :
    castMatrix (numerator β body (.c, j, true)) =
      (64 : ℚ) • residueTwoWallGenerator β body (.c, j, true) := by
  rw [show residueTwoWallGenerator β body (.c, j, true) =
      cAtom ((3 : ℚ) ^ β) (nearySideLowerC β body)
        (nearySideLowerCScale β body) (3 * j + 1) by rfl,
    cAtom_three_mul_add_one,
    nearySideLowerC_eq_nine_mul_add_seven]
  rw [show nearySideLowerCScale β body =
      27 * (3 : ℚ) ^ (tagEncode β body).length by
        rw [nearySideLowerCScale_eq_nine_mul, pow_succ]
        ring]
  ext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [numerator, liftResidue, castMatrix] <;>
    ring

private theorem cast_numerator
    (β : Nat) (body : List TagLetter) (label : TagLetter × Nat × Bool) :
    castMatrix (numerator β body label) =
      (64 : ℚ) • residueTwoWallGenerator β body label := by
  obtain ⟨letter, j, residueOne⟩ := label
  cases letter <;> cases residueOne
  · exact cast_numerator_b_zero β body j
  · exact cast_numerator_b_one β body j
  · exact cast_numerator_c_zero β body j
  · exact cast_numerator_c_one β body j

private def residue : Bool → Matrix (Fin 3) (Fin 3) (ZMod 3)
  | false =>
      !![1, 2, 2;
         0, 0, 0;
         0, 0, 0]
  | true =>
      !![0, 0, 0;
         0, 0, 0;
         2, 0, 2]

private theorem mapped_numerator
    (β : Nat) (body : List TagLetter) (label : TagLetter × Nat × Bool) :
    (numerator β body label).map (Int.castRingHom (ZMod 3)) = residue label.2.2 := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨letter, j, residueOne⟩ := label
  cases letter <;> cases residueOne <;>
    ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [numerator, residue, Matrix.vecHead, Matrix.vecTail]

private def ray : Bool → Fin 3 → ZMod 3
  | false => ![1, 0, 0]
  | true => ![0, 0, 1]

private def transition (label : TagLetter × Nat × Bool) (_ : Bool) : Bool := label.2.2

private def weight : TagLetter × Nat × Bool → Bool → ZMod 3
  | (_, _, false), false => 1
  | (_, _, false), true => 2
  | (_, _, true), _ => 2

private theorem mapped_numerator_mulVec
    (β : Nat) (body : List TagLetter)
    (label : TagLetter × Nat × Bool) (state : Bool) :
    Matrix.mulVec
        ((numerator β body label).map (Int.castRingHom (ZMod 3)))
        (ray state) =
      weight label state • ray (transition label state) := by
  rw [mapped_numerator β body label]
  obtain ⟨letter, j, residueOne⟩ := label
  cases letter <;> cases residueOne <;> cases state <;>
    ext i <;> fin_cases i <;>
    norm_num [residue, ray, transition, weight, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_succ]

private theorem numerator_immortal (β : Nat) (body : List TagLetter) :
    ¬IsMortal (numerator β body) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let quotient :=
    ((Int.castRingHom (ZMod 3)).mapMatrix (m := Fin 3)).toMonoidWithZeroHom
  apply not_isMortal_of_map_not_isMortal quotient (numerator β body)
  apply not_isMortal_of_ray_action
    (quotient ∘ numerator β body) ray transition weight false
  · intro state state_zero
    cases state
    · have entry := congr_fun state_zero 0
      norm_num [ray] at entry
    · have entry := congr_fun state_zero 2
      norm_num [ray] at entry
  · intro label state
    obtain ⟨letter, j, residueOne⟩ := label
    cases letter <;> cases residueOne <;> cases state <;>
      norm_num [weight]
    all_goals exact (by decide : (2 : ZMod 3) ≠ 0)
  · intro label state
    simpa [quotient, Function.comp_def] using
      mapped_numerator_mulVec β body label state

/-- Every atom word whose gaps are congruent to zero or one modulo three is nonzero. Equivalently,
every zero word contains a residue-two gap. -/
theorem residueTwoWall_wordProduct_ne_zero
    (β : Nat) (body : List TagLetter) (word : List (TagLetter × Nat × Bool)) :
    wordProduct (residueTwoWallGenerator β body) word ≠ 0 := by
  intro product_zero
  have cast_immortal : ¬IsMortal (castMatrix ∘ numerator β body) := by
    rw [isMortal_cast_iff]
    exact numerator_immortal β body
  have cast_eq :
      castMatrix ∘ numerator β body =
        fun label => (64 : ℚ) • residueTwoWallGenerator β body label := by
    funext label
    exact cast_numerator β body label
  rw [cast_eq] at cast_immortal
  have word_nonempty : word ≠ [] := by
    rintro rfl
    simp at product_zero
  apply cast_immortal
  refine ⟨word, word_nonempty, ?_⟩
  rw [wordProduct_smulMatrix]
  exact smul_eq_zero.mpr (Or.inr product_zero)

end ParabolicBlade

end MatrixMortality
