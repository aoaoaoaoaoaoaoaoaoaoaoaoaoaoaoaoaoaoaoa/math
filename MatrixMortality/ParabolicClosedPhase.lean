import MatrixMortality.ParabolicBlade

/-!
# Closed-phase extermination for the parabolic blade

After uniform denominator clearing, every closed gap and the exceptional atom act on a
two-ray automaton over `ZMod 3` with nonzero transition weight. Hence no word confined to the
closed phase can vanish, regardless of its length or number of exceptional atoms.
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

/-- The closed-phase alphabet: `none` is the exceptional atom `Q(b,1)`, while
`some (letter,j)` is the closed atom `Q(letter,3j)`. -/
def closedPhaseGenerator (β : Nat) (body : List TagLetter) :
    Option (TagLetter × Nat) → Matrix (Fin 3) (Fin 3) ℚ
  | none => atom β body .b 1
  | some (letter, j) => atom β body letter (3 * j)

/-- Eight times a closed `c`-atom, in the coordinates that expose its fixed residue. -/
private def cNumerator (K P : ℤ) (j : Nat) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![liftResidue 2 2, liftResidue 5 1,
      liftResidue (16 * (3 * K + 2) * j + 5) 1;
     0, liftResidue 8 0, 0;
     0, 0, liftResidue (8 * ((9 * P - 1) * j + 1)) 0]

/-- Eight times each closed-phase generator, represented integrally. -/
private def numerator (β : Nat) (body : List TagLetter) :
    Option (TagLetter × Nat) → Matrix (Fin 3) (Fin 3) ℤ
  | none =>
      let ρ : ℤ := 3 ^ β
      !![liftResidue (96 * ρ - 6) 0, liftResidue (-96 * ρ + 18) 0,
          liftResidue 48 0;
         liftResidue (24 * ρ) 0, liftResidue (-24 * ρ) 0, 0;
         liftResidue (38 * ρ - 4) 1, liftResidue (-38 * ρ + 11) 0,
          liftResidue 29 1]
  | some (.b, j) =>
      let ρ : ℤ := 3 ^ β
      !![liftResidue 2 2, liftResidue (20 * ρ + 1) 1,
          liftResidue (128 * j + 5) 1;
         0, liftResidue (24 * ρ) 0, 0;
         0, 0, liftResidue (64 * j + 8) 0]
  | some (.c, j) =>
      let K : ℤ := ternaryCode (true :: tagEncode β body)
      let P : ℤ := 3 ^ (tagEncode β body).length
      cNumerator K P j

private theorem cAtom_closed (ρ L M : ℚ) (j : Nat) :
    cAtom ρ L M (3 * j) =
      !![1, 2, 2 * ((L - 1) * j + 1);
         0, 3, 0;
         0, 0, (M - 3) * j + 3] := by
  rw [cAtom, normalRoot_pow_three_mul]
  ext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [cFlank, flank, drift, injection, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    ring

private theorem cast_cNumerator (K P : ℤ) (j : Nat) :
    castMatrix (cNumerator K P j) =
      (8 : ℚ) •
        !![1, 2, 2 * (((9 : ℚ) * K + 7 - 1) * j + 1);
           0, 3, 0;
           0, 0, ((27 : ℚ) * P - 3) * j + 3] := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [cNumerator, liftResidue, castMatrix] <;>
    ring

private theorem cast_numerator
    (β : Nat) (body : List TagLetter) (label : Option (TagLetter × Nat)) :
    castMatrix (numerator β body label) =
      (8 : ℚ) • closedPhaseGenerator β body label := by
  cases label with
  | none =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [numerator, liftResidue, closedPhaseGenerator, atom, bAtom, bFlank, flank,
          normalRoot, injection, castMatrix, pow_succ, Matrix.mul_apply,
          Fin.sum_univ_succ] <;>
        ring
  | some label =>
      obtain ⟨letter, gap⟩ := label
      cases letter with
      | b =>
          rw [show closedPhaseGenerator β body (some (.b, gap)) =
              bAtom ((3 : ℚ) ^ β) (3 * gap) by rfl,
            bAtom, normalRoot_pow_three_mul]
          ext i j
          fin_cases i <;> fin_cases j <;>
            norm_num [numerator, liftResidue, bFlank, flank, drift, injection, castMatrix,
              Matrix.mul_apply, Fin.sum_univ_succ] <;>
            ring
      | c =>
          have L_eq :
              nearySideLowerC β body =
                9 * ternaryCode (true :: tagEncode β body) + 7 :=
            nearySideLowerC_eq_nine_mul_add_seven β body
          have M_eq :
              nearySideLowerCScale β body =
                27 * (3 : ℚ) ^ (tagEncode β body).length := by
            rw [nearySideLowerCScale_eq_nine_mul, pow_succ]
            ring
          rw [show closedPhaseGenerator β body (some (.c, gap)) =
              cAtom ((3 : ℚ) ^ β) (nearySideLowerC β body)
                (nearySideLowerCScale β body) (3 * gap) by rfl,
            cAtom_closed, L_eq, M_eq]
          rw [numerator, cast_cNumerator]
          have K_cast :
              (((ternaryCode (true :: tagEncode β body) : Nat) : ℤ) : ℚ) =
                (ternaryCode (true :: tagEncode β body) : ℚ) := by
            norm_num
          have P_cast :
              (((3 ^ (tagEncode β body).length : ℤ) : ℚ)) =
                (3 : ℚ) ^ (tagEncode β body).length := by
            norm_num
          rw [K_cast, P_cast]

private def closedResidue : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  !![2, 1, 1;
     0, 0, 0;
     0, 0, 0]

private def exceptionalResidue : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  !![0, 0, 0;
     0, 0, 0;
     1, 0, 1]

private theorem mapped_numerator
    (β : Nat) (body : List TagLetter) (label : Option (TagLetter × Nat)) :
    (numerator β body label).map (Int.castRingHom (ZMod 3)) =
      match label with
      | none => exceptionalResidue
      | some _ => closedResidue := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  cases label with
  | none =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [numerator, exceptionalResidue, Matrix.vecHead, Matrix.vecTail]
  | some label =>
      obtain ⟨letter, gap⟩ := label
      cases letter with
      | b =>
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [numerator, closedResidue, Matrix.vecHead, Matrix.vecTail]
      | c =>
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [numerator, cNumerator, closedResidue, Matrix.vecHead, Matrix.vecTail]

private def ray : Bool → Fin 3 → ZMod 3
  | false => ![1, 0, 0]
  | true => ![0, 0, 1]

private def transition : Option (TagLetter × Nat) → Bool → Bool
  | none, _ => true
  | some _, _ => false

private def weight : Option (TagLetter × Nat) → Bool → ZMod 3
  | some _, false => 2
  | _, _ => 1

private theorem mapped_numerator_mulVec
    (β : Nat) (body : List TagLetter)
    (label : Option (TagLetter × Nat)) (state : Bool) :
    Matrix.mulVec
        ((numerator β body label).map (Int.castRingHom (ZMod 3)))
        (ray state) =
      weight label state • ray (transition label state) := by
  rw [mapped_numerator β body]
  cases label <;> cases state <;>
    ext i <;> fin_cases i <;>
    norm_num [closedResidue, exceptionalResidue, ray, transition, weight,
      Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]

private theorem numerator_immortal
    (β : Nat) (body : List TagLetter) :
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
    cases label <;> cases state <;> simp only [weight]
    · exact one_ne_zero
    · exact one_ne_zero
    · exact (by decide : (2 : ZMod 3) ≠ 0)
    · exact one_ne_zero
  · intro label state
    simpa [quotient, Function.comp_def] using
      mapped_numerator_mulVec β body label state

/-- Every word assembled solely from closed gaps `Q(x,3j)` and the exceptional atom `Q(b,1)`
is nonzero. -/
theorem closedPhase_wordProduct_ne_zero
    (β : Nat) (body : List TagLetter)
    (word : List (Option (TagLetter × Nat))) :
    wordProduct (closedPhaseGenerator β body) word ≠ 0 := by
  intro product_zero
  have cast_immortal : ¬IsMortal (castMatrix ∘ numerator β body) := by
    rw [isMortal_cast_iff]
    exact numerator_immortal β body
  have cast_eq :
      castMatrix ∘ numerator β body =
        fun label => (8 : ℚ) • closedPhaseGenerator β body label := by
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
