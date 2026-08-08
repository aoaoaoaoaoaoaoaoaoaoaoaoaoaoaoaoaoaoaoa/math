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

/-- Explicit residue-one `c` atom before integral clearing or exterior transport. -/
theorem cAtom_three_mul_add_one_matrix (ρ L M : ℚ) (j : Nat) :
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

private theorem cAtom_three_mul_add_two (ρ L M : ℚ) (j : Nat) :
    cAtom ρ L M (3 * j + 2) =
      !![(11 * L - 155) / 48,
          -(114 * L * ρ - 11 * L - 114 * ρ - 85) / 96,
          2 * (3 * L * j + 2 * L - 3 * j + 1) / 3;
         -3, 0, 0;
         11 * (M - 3) / 96,
          -(M - 3) * (114 * ρ - 11) / 192,
          (3 * M * j + 2 * M - 9 * j + 3) / 3] := by
  rw [cAtom, pow_add, normalRoot_pow_three_mul]
  ext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [cFlank, flank, drift, normalRoot, injection, pow_succ, Matrix.mul_apply,
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

/-- Exact residue-one `b` atom, recovered from the already-cleared integral model. -/
theorem residueTwoWallGenerator_b_one_matrix
    (β : Nat) (body : List TagLetter) (j : Nat) :
    residueTwoWallGenerator β body (.b, j, true) =
      !![36 * (3 : ℚ) ^ β - 9 / 4, 27 / 4 - 36 * (3 : ℚ) ^ β, 48 * j + 18;
         9 * (3 : ℚ) ^ β, -9 * (3 : ℚ) ^ β, 0;
         57 * (3 : ℚ) ^ β / 4 - 11 / 8, 33 / 8 - 57 * (3 : ℚ) ^ β / 4,
          24 * j + 11] := by
  ext i k
  have entry := congrArg (fun matrix => matrix i k) (cast_numerator_b_one β body j)
  fin_cases i <;> fin_cases k <;>
    norm_num [numerator, liftResidue, castMatrix, residueTwoWallGenerator] at entry ⊢ <;>
    linarith

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
    cAtom_three_mul_add_one_matrix,
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

/-- Sixty-four times a residue-two atom, represented integrally. -/
private def defectNumerator (β : Nat) (body : List TagLetter) :
    TagLetter × Nat → Matrix (Fin 3) (Fin 3) ℤ
  | (.b, j) =>
      let ρ : ℤ := 3 ^ β
      !![liftResidue (85 - 160 * ρ) 1, liftResidue (80 - 608 * ρ) 0,
          liftResidue (1024 * j + 725) 1;
         liftResidue (-192 * ρ) 0, 0, 0;
         liftResidue 58 2, liftResidue (29 - 304 * ρ) 1,
          liftResidue (512 * j + 405) 1]
  | (.c, j) =>
      let ρ : ℤ := 3 ^ β
      let K : ℤ := ternaryCode (true :: tagEncode β body)
      let P : ℤ := 3 ^ (tagEncode β body).length
      !![liftResidue (44 * K - 35) 1,
          liftResidue (-2 * (114 * K * ρ - 11 * K + 76 * ρ - 18)) 0,
          liftResidue (384 * K * j + 256 * K + 256 * j + 213) 1;
         liftResidue (-64) 0, 0, 0;
         liftResidue (2 * (33 * P - 4)) 2,
          liftResidue (-342 * P * ρ + 33 * P + 38 * ρ - 4) 1,
          liftResidue (576 * P * j + 384 * P - 64 * j + 21) 1]

private theorem cast_defectNumerator_b
    (β : Nat) (body : List TagLetter) (j : Nat) :
    castMatrix (defectNumerator β body (.b, j)) =
      (64 : ℚ) • atom β body .b (3 * j + 2) := by
  rw [show atom β body .b (3 * j + 2) =
      bAtom ((3 : ℚ) ^ β) (3 * j + 2) by rfl,
    bAtom, pow_add, normalRoot_pow_three_mul]
  ext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [defectNumerator, liftResidue, bFlank, flank, drift, normalRoot, injection,
      castMatrix, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

private theorem cast_defectNumerator_c
    (β : Nat) (body : List TagLetter) (j : Nat) :
    castMatrix (defectNumerator β body (.c, j)) =
      (64 : ℚ) • atom β body .c (3 * j + 2) := by
  rw [show atom β body .c (3 * j + 2) =
      cAtom ((3 : ℚ) ^ β) (nearySideLowerC β body)
        (nearySideLowerCScale β body) (3 * j + 2) by rfl,
    cAtom_three_mul_add_two,
    nearySideLowerC_eq_nine_mul_add_seven]
  rw [show nearySideLowerCScale β body =
      27 * (3 : ℚ) ^ (tagEncode β body).length by
        rw [nearySideLowerCScale_eq_nine_mul, pow_succ]
        ring]
  ext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [defectNumerator, liftResidue, castMatrix] <;>
    ring

private theorem cast_defectNumerator
    (β : Nat) (body : List TagLetter) (label : TagLetter × Nat) :
    castMatrix (defectNumerator β body label) =
      (64 : ℚ) • atom β body label.1 (3 * label.2 + 2) := by
  obtain ⟨letter, j⟩ := label
  cases letter
  · exact cast_defectNumerator_b β body j
  · exact cast_defectNumerator_c β body j

private theorem cast_numerator_wordProduct
    (β : Nat) (body : List TagLetter) (word : List (TagLetter × Nat × Bool)) :
    castMatrix (wordProduct (numerator β body) word) =
      (word.map fun _ => (64 : ℚ)).prod •
        wordProduct (residueTwoWallGenerator β body) word := by
  rw [castMatrix_wordProduct]
  change wordProduct (fun label => castMatrix (numerator β body label)) word = _
  simp_rw [cast_numerator]
  exact wordProduct_smulMatrix (fun _ => (64 : ℚ))
    (residueTwoWallGenerator β body) word

private def residue : Bool → Matrix (Fin 3) (Fin 3) (ZMod 3)
  | false =>
      !![1, 2, 2;
         0, 0, 0;
         0, 0, 0]
  | true =>
      !![0, 0, 0;
         0, 0, 0;
         2, 0, 2]

private def defectResidue : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  !![1, 0, 1;
     0, 0, 0;
     2, 1, 1]

private theorem mapped_numerator
    (β : Nat) (body : List TagLetter) (label : TagLetter × Nat × Bool) :
    (numerator β body label).map (Int.castRingHom (ZMod 3)) = residue label.2.2 := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨letter, j, residueOne⟩ := label
  cases letter <;> cases residueOne <;>
    ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [numerator, residue, Matrix.vecHead, Matrix.vecTail]

private theorem mapped_defectNumerator
    (β : Nat) (body : List TagLetter) (label : TagLetter × Nat) :
    (defectNumerator β body label).map (Int.castRingHom (ZMod 3)) = defectResidue := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨letter, j⟩ := label
  cases letter <;>
    ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [defectNumerator, defectResidue, Matrix.vecHead, Matrix.vecTail]

private def ray : Bool → Fin 3 → ZMod 3
  | false => ![1, 0, 0]
  | true => ![0, 0, 1]

private def transition (label : TagLetter × Nat × Bool) (_ : Bool) : Bool := label.2.2

private def weight : TagLetter × Nat × Bool → Bool → ZMod 3
  | (_, _, false), false => 1
  | (_, _, false), true => 2
  | (_, _, true), _ => 2

private def defectWeight : Bool → ZMod 3
  | false => 2
  | true => 1

private theorem ray_ne_zero (state : Bool) : ray state ≠ 0 := by
  cases state
  · intro ray_zero
    have entry := congr_fun ray_zero 0
    norm_num [ray] at entry
  · intro ray_zero
    have entry := congr_fun ray_zero 2
    norm_num [ray] at entry

private theorem weight_ne_zero (label : TagLetter × Nat × Bool) (state : Bool) :
    weight label state ≠ 0 := by
  obtain ⟨letter, j, residueOne⟩ := label
  cases letter <;> cases residueOne <;> cases state <;>
    norm_num [weight]
  all_goals exact (by decide : (2 : ZMod 3) ≠ 0)

private theorem defectWeight_ne_zero (state : Bool) : defectWeight state ≠ 0 := by
  cases state
  · exact (by decide : (2 : ZMod 3) ≠ 0)
  · norm_num [defectWeight]

private theorem rayWeight_ne_zero
    (word : List (TagLetter × Nat × Bool)) (state : Bool) :
    rayWeight transition weight word state ≠ 0 := by
  induction word generalizing state with
  | nil => simp [rayWeight]
  | cons label tail induction =>
      rw [rayWeight]
      exact mul_ne_zero (induction state)
        (weight_ne_zero label (rayState transition tail state))

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

private theorem mapped_same_residue_defect_action
    (β : Nat) (body : List TagLetter)
    (left right : TagLetter × Nat × Bool) (defect : TagLetter × Nat)
    (sameResidue : left.2.2 = right.2.2) :
    Matrix.mulVec ((numerator β body left).map (Int.castRingHom (ZMod 3)))
        (Matrix.mulVec ((defectNumerator β body defect).map (Int.castRingHom (ZMod 3)))
          (ray right.2.2)) =
      defectWeight right.2.2 • ray left.2.2 := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [mapped_numerator, mapped_defectNumerator]
  obtain ⟨leftLetter, leftWait, leftResidue⟩ := left
  obtain ⟨rightLetter, rightWait, rightResidue⟩ := right
  cases leftResidue <;> cases rightResidue <;> simp at sameResidue
  all_goals
    ext i
    fin_cases i
    all_goals
      norm_num [residue, defectResidue, ray, defectWeight, Matrix.mulVec,
        Matrix.dotProduct, Fin.sum_univ_succ] <;>
      first
      | exact (show (5 : ZMod 3) = 2 by decide)
      | exact (show (4 : ZMod 3) = 1 by decide)

private theorem mapped_oneDefect_ne_zero_of_same_residue
    (β : Nat) (body : List TagLetter)
    (leftPrefix rightSuffix : List (TagLetter × Nat × Bool))
    (leftAdjacent rightAdjacent : TagLetter × Nat × Bool)
    (defect : TagLetter × Nat)
    (sameResidue : leftAdjacent.2.2 = rightAdjacent.2.2) :
    wordProduct
          (fun label => (numerator β body label).map (Int.castRingHom (ZMod 3)))
          (leftPrefix ++ [leftAdjacent]) *
        (defectNumerator β body defect).map (Int.castRingHom (ZMod 3)) *
      wordProduct
          (fun label => (numerator β body label).map (Int.castRingHom (ZMod 3)))
          (rightAdjacent :: rightSuffix) ≠ 0 := by
  let mapped :=
    fun label => (numerator β body label).map (Int.castRingHom (ZMod 3))
  have prefixAction :=
    wordProduct_mulVec_ray_action mapped ray transition weight
      (mapped_numerator_mulVec β body) leftPrefix leftAdjacent.2.2
  have rightAction :
      Matrix.mulVec (wordProduct mapped (rightAdjacent :: rightSuffix)) (ray false) =
        rayWeight transition weight (rightAdjacent :: rightSuffix) false •
          ray rightAdjacent.2.2 := by
    simpa [rayState, transition] using
      wordProduct_mulVec_ray_action mapped ray transition weight
        (mapped_numerator_mulVec β body) (rightAdjacent :: rightSuffix) false
  have coreAction :
      Matrix.mulVec (mapped leftAdjacent)
          (Matrix.mulVec
            ((defectNumerator β body defect).map (Int.castRingHom (ZMod 3)))
            (ray rightAdjacent.2.2)) =
        defectWeight rightAdjacent.2.2 • ray leftAdjacent.2.2 := by
    simpa [mapped] using
      mapped_same_residue_defect_action β body leftAdjacent rightAdjacent defect sameResidue
  have imageAction :
      Matrix.mulVec
          (wordProduct mapped (leftPrefix ++ [leftAdjacent]) *
              (defectNumerator β body defect).map (Int.castRingHom (ZMod 3)) *
            wordProduct mapped (rightAdjacent :: rightSuffix))
          (ray false) =
        rayWeight transition weight (rightAdjacent :: rightSuffix) false •
          (defectWeight rightAdjacent.2.2 •
            (rayWeight transition weight leftPrefix leftAdjacent.2.2 •
              ray (rayState transition leftPrefix leftAdjacent.2.2))) := by
    rw [wordProduct_append, wordProduct_cons, wordProduct_nil, mul_one]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [rightAction]
    simp only [Matrix.mulVec_smul, coreAction, prefixAction]
  have imageNonzero :
      rayWeight transition weight (rightAdjacent :: rightSuffix) false •
          (defectWeight rightAdjacent.2.2 •
            (rayWeight transition weight leftPrefix leftAdjacent.2.2 •
              ray (rayState transition leftPrefix leftAdjacent.2.2))) ≠ 0 :=
    smul_ne_zero (rayWeight_ne_zero (rightAdjacent :: rightSuffix) false)
      (smul_ne_zero (defectWeight_ne_zero rightAdjacent.2.2)
        (smul_ne_zero (rayWeight_ne_zero leftPrefix leftAdjacent.2.2)
          (ray_ne_zero (rayState transition leftPrefix leftAdjacent.2.2))))
  intro productZero
  apply imageNonzero
  rw [← imageAction, productZero, Matrix.zero_mulVec]

private theorem numerator_immortal (β : Nat) (body : List TagLetter) :
    ¬IsMortal (numerator β body) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let quotient :=
    ((Int.castRingHom (ZMod 3)).mapMatrix (m := Fin 3)).toMonoidWithZeroHom
  apply not_isMortal_of_map_not_isMortal quotient (numerator β body)
  apply not_isMortal_of_ray_action
    (quotient ∘ numerator β body) ray transition weight false
  · exact ray_ne_zero
  · exact weight_ne_zero
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

/-- A word with one residue-two atom and nonempty safe contexts is nonzero when the two atoms
adjacent to the defect have the same residue. -/
theorem oneDefect_wordProduct_ne_zero_of_same_residue
    (β : Nat) (body : List TagLetter)
    (leftPrefix rightSuffix : List (TagLetter × Nat × Bool))
    (leftAdjacent rightAdjacent : TagLetter × Nat × Bool)
    (defect : TagLetter × Nat)
    (sameResidue : leftAdjacent.2.2 = rightAdjacent.2.2) :
    wordProduct (residueTwoWallGenerator β body) (leftPrefix ++ [leftAdjacent]) *
          atom β body defect.1 (3 * defect.2 + 2) *
        wordProduct (residueTwoWallGenerator β body) (rightAdjacent :: rightSuffix) ≠ 0 := by
  intro productZero
  have integerZero :
      wordProduct (numerator β body) (leftPrefix ++ [leftAdjacent]) *
            defectNumerator β body defect *
          wordProduct (numerator β body) (rightAdjacent :: rightSuffix) = 0 := by
    apply (castMatrix_eq_zero_iff _).mp
    rw [show
      castMatrix
          (wordProduct (numerator β body) (leftPrefix ++ [leftAdjacent]) *
              defectNumerator β body defect *
            wordProduct (numerator β body) (rightAdjacent :: rightSuffix)) =
        castMatrix (wordProduct (numerator β body) (leftPrefix ++ [leftAdjacent])) *
            castMatrix (defectNumerator β body defect) *
          castMatrix (wordProduct (numerator β body) (rightAdjacent :: rightSuffix)) by
      simp only [castMatrix, Matrix.map_mul]]
    rw [cast_numerator_wordProduct, cast_defectNumerator, cast_numerator_wordProduct]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [productZero, smul_zero]
  have mappedZero :=
    congrArg (fun matrix => matrix.map (Int.castRingHom (ZMod 3))) integerZero
  simp only [Matrix.map_mul, map_zero] at mappedZero
  rw [wordProduct_mapMatrix, wordProduct_mapMatrix] at mappedZero
  exact mapped_oneDefect_ne_zero_of_same_residue β body leftPrefix rightSuffix
    leftAdjacent rightAdjacent defect sameResidue mappedZero

end ParabolicBlade

end MatrixMortality
