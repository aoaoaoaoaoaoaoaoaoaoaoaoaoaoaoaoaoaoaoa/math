import MatrixMortality.ParabolicBlade

/-!
# Original parabolic semantic obstruction

This file places one complete side-normal correspondence block between the original parabolic
blade factors.  It proves that no fixed pair of projective endpoints can recognize the formal
terminal plane: incidence on every terminal point forces incidence on the entire length plane.
-/

namespace MatrixMortality

open scoped Matrix

namespace ParabolicBlade

/-- A complete side-normal correspondence block in the original blade's reduced basis. -/
def semanticMiddle (upperCode lowerCode upperScale lowerScale : ℚ) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, upperCode, 2 * lowerCode;
     0, upperScale, 0;
     0, 0, lowerScale]

/-- The reduced middle carried by two concrete ternary words. -/
def semanticWordMiddle (upper lower : List Bool) : Matrix (Fin 3) (Fin 3) ℚ :=
  semanticMiddle (ternaryCode upper) (ternaryCode lower)
    (3 ^ upper.length) (3 ^ lower.length)

/-- Original reduced atom naming one complete Neary tile. -/
def completeTileAtom (β : Nat) (body : List TagLetter) (tile : NearyTile) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  atom β body tile.letter (completeGap tile)

/-- Every complete original gap is exactly its ternary semantic middle. -/
theorem completeTileAtom_eq_semanticWordMiddle
    (β : Nat) (body : List TagLetter) (tile : NearyTile) :
    completeTileAtom β body tile =
      semanticWordMiddle (nearyUpper β tile) (nearyLower β body tile) := by
  cases tile with
  | erase letter =>
      cases letter with
      | b =>
          change bAtom ((3 : ℚ) ^ β) 0 =
            semanticMiddle (nearySideUpperB β) 1 (nearySideUpperBScale β) 3
          rw [nearySideUpperB_eq, nearySideUpperBScale_eq]
          ext i j
          fin_cases i <;> fin_cases j <;>
            norm_num [semanticMiddle, bAtom, bFlank, flank, injection, Matrix.mul_apply,
              Fin.sum_univ_succ]
      | c =>
          change cAtom ((3 : ℚ) ^ β) (nearySideLowerC β body)
              (nearySideLowerCScale β body) 0 = semanticMiddle 2 1 3 3
          ext i j
          fin_cases i <;> fin_cases j <;>
            norm_num [semanticMiddle, cAtom, cFlank, flank, injection, Matrix.mul_apply,
              Fin.sum_univ_succ] ;
            ring
  | rule letter =>
      cases letter with
      | b =>
          change bAtom ((3 : ℚ) ^ β) 3 =
            semanticMiddle (nearySideUpperB β) 25 (nearySideUpperBScale β) 27
          rw [nearySideUpperB_eq, nearySideUpperBScale_eq]
          rw [bAtom, normalRoot_cube]
          ext i j
          fin_cases i <;> fin_cases j <;>
            norm_num [semanticMiddle, bFlank, flank, drift, injection, Matrix.mul_apply,
              Fin.sum_univ_succ]
      | c =>
          change cAtom ((3 : ℚ) ^ β) (nearySideLowerC β body)
              (nearySideLowerCScale β body) 3 =
            semanticMiddle 2 (nearySideLowerC β body) 3
              (nearySideLowerCScale β body)
          rw [cAtom, normalRoot_cube]
          ext i j
          fin_cases i <;> fin_cases j <;>
            norm_num [semanticMiddle, cFlank, flank, drift, injection, Matrix.mul_apply,
              Fin.sum_univ_succ] <;>
            ring

@[simp] theorem semanticWordMiddle_nil : semanticWordMiddle [] [] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [semanticWordMiddle, semanticMiddle, Matrix.one_apply, Matrix.vecHead,
      Matrix.vecTail]

/-- Complete semantic middles compose in chronological word order. -/
theorem semanticWordMiddle_append
    (upper lower nextUpper nextLower : List Bool) :
    semanticWordMiddle (upper ++ nextUpper) (lower ++ nextLower) =
      semanticWordMiddle upper lower * semanticWordMiddle nextUpper nextLower := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [semanticWordMiddle, semanticMiddle, ternaryCode_append, pow_add,
      Matrix.mul_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_succ] <;>
    ring

/-- Reduced product of the complete original gaps named by a Neary word. -/
def completeTileProduct (β : Nat) (body : List TagLetter) (word : List NearyTile) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  wordProduct (completeTileAtom β body) word

/-- Every complete original atom word is its one side-normal semantic middle. -/
theorem completeTileProduct_eq_semanticWordMiddle
    (β : Nat) (body : List TagLetter) (word : List NearyTile) :
    completeTileProduct β body word =
      semanticWordMiddle (spell (nearyUpper β) word) (spell (nearyLower β body) word) := by
  induction word with
  | nil => simp [completeTileProduct, wordProduct, spell]
  | cons tile word induction =>
      rw [completeTileProduct, wordProduct_cons, completeTileAtom_eq_semanticWordMiddle]
      change semanticWordMiddle _ _ * wordProduct (completeTileAtom β body) word = _
      rw [← completeTileProduct, induction, ← semanticWordMiddle_append]
      rfl

/-- The original blade middle is a fixed conjugate of the repository's side-normal matrix. -/
theorem semanticWordMiddle_eq_sidePcpMatrix_conjugate (upper lower : List Bool) :
    semanticWordMiddle upper lower =
      !![(1 : ℚ), 0, 0; 0, 0, 1; 0, 1 / 2, 0] *
        sidePcpMatrix ℚ upper lower *
          !![(1 : ℚ), 0, 0; 0, 0, 2; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [semanticWordMiddle, semanticMiddle, sidePcpMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    ring

/-- Exact determinant of a complete semantic middle under the original exceptional bridge. -/
theorem bridge_semanticMiddle_det
    (ρ upperCode lowerCode upperScale lowerScale : ℚ) :
    (bridge ρ (semanticMiddle upperCode lowerCode upperScale lowerScale)).det =
      (9 * ρ / 2) *
        (lowerScale * (22 * upperCode + 31) -
          upperScale * (22 * lowerScale + 11 * lowerCode + 9)) := by
  rw [Matrix.det_fin_two]
  norm_num [bridge, semanticMiddle, coreInput, coreOutput, Matrix.mul_apply,
    Fin.sum_univ_succ]
  ring

/-- A nonempty complete correspondence block is never a singular bridge wall. -/
theorem bridge_semanticWordMiddle_det_neg
    (ρ : ℚ) (ρ_pos : 0 < ρ) (upper lower : List Bool)
    (upper_nonempty : upper ≠ []) (lower_nonempty : lower ≠ []) :
    (bridge ρ (semanticWordMiddle upper lower)).det < 0 := by
  rw [semanticWordMiddle, bridge_semanticMiddle_det]
  have upperCodeBound := ternaryCode_lt_pow_length upper
  have lowerCodeBound := ternaryCode_lower_bound lower lower_nonempty
  have upperLength : 0 < upper.length := List.length_pos.mpr upper_nonempty
  have lowerLength : 0 < lower.length := List.length_pos.mpr lower_nonempty
  have upperScaleThree : (3 : ℚ) ≤ 3 ^ upper.length := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 3) upperLength
  have lowerScaleThree : (3 : ℚ) ≤ 3 ^ lower.length := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 3) lowerLength
  have upperCodeCast :
      (ternaryCode upper : ℚ) + 1 ≤ 3 ^ upper.length := by
    exact_mod_cast (by omega : ternaryCode upper + 1 ≤ 3 ^ upper.length)
  have lowerCodeCast :
      3 ^ (lower.length - 1) ≤ (ternaryCode lower : ℚ) := by
    exact_mod_cast lowerCodeBound
  have lowerScaleSplit :
      (3 : ℚ) ^ lower.length = 3 * 3 ^ (lower.length - 1) := by
    obtain ⟨prior, length_eq⟩ :=
      Nat.exists_eq_succ_of_ne_zero (by omega : lower.length ≠ 0)
    rw [length_eq]
    simp [pow_succ, mul_comm]
  have innerNegative :
      (3 : ℚ) ^ lower.length * (22 * ternaryCode upper + 31) -
          3 ^ upper.length *
            (22 * 3 ^ lower.length + 11 * ternaryCode lower + 9) < 0 := by
    rw [lowerScaleSplit]
    nlinarith [mul_nonneg
      (show (0 : ℚ) ≤ 3 ^ (lower.length - 1) by positivity)
      (show (0 : ℚ) ≤ 3 ^ upper.length - 3 by linarith)]
  exact mul_neg_of_pos_of_neg (by positivity) innerNegative

/-- Every nonempty complete original Neary word has a nonsingular exceptional bridge. -/
theorem bridge_completeTileProduct_det_neg
    (β : Nat) (body : List TagLetter) (word : List NearyTile) (word_nonempty : word ≠ []) :
    (bridge ((3 : ℚ) ^ β) (completeTileProduct β body word)).det < 0 := by
  rw [completeTileProduct_eq_semanticWordMiddle]
  apply bridge_semanticWordMiddle_det_neg
  · positivity
  · cases word with
    | nil => exact False.elim (word_nonempty rfl)
    | cons tile word => simp [spell, nearyUpper_ne_nil]
  · cases word with
    | nil => exact False.elim (word_nonempty rfl)
    | cons tile word => simp [spell, nearyLower_ne_nil]

/-- Scalar incidence between fixed endpoint rays through one semantic middle. -/
def semanticIncidence (ρ : ℚ) (left right : Fin 2 → ℚ)
    (upperCode lowerCode upperScale lowerScale : ℚ) : ℚ :=
  left ⬝ᵥ
    (bridge ρ (semanticMiddle upperCode lowerCode upperScale lowerScale) *ᵥ right)

/-- Exact affine expansion of a fixed semantic incidence. -/
theorem semanticIncidence_eq
    (ρ : ℚ) (left right : Fin 2 → ℚ)
    (upperCode lowerCode upperScale lowerScale : ℚ) :
    semanticIncidence ρ left right upperCode lowerCode upperScale lowerScale =
      ((36 * ρ - 9 / 4) * left 0 * right 0 + 18 * left 0 * right 1) +
      (9 * ρ * left 0 * right 0) * upperCode +
      ((57 * ρ / 2 - 11 / 4) * left 0 * right 0 +
        22 * left 0 * right 1) * lowerCode +
      ((-9 * ρ * left 0 + 9 * ρ / 4 * left 1) * right 0) * upperScale +
      ((57 * ρ / 4 - 11 / 8) * left 1 * right 0 +
        11 * left 1 * right 1) * lowerScale := by
  norm_num [semanticIncidence, bridge, semanticMiddle, coreInput, coreOutput,
    Matrix.mul_apply, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]
  ring

/-- If a fixed incidence vanishes on the formal terminal plane, it vanishes on the whole
length plane and therefore cannot distinguish terminal equality. -/
theorem semanticIncidence_terminal_forces_length
    (ρ suffixCode suffixScale : ℚ) (left right : Fin 2 → ℚ)
    (terminal : ∀ upperCode upperScale : ℚ,
      semanticIncidence ρ left right upperCode
        (upperCode + suffixCode * upperScale) upperScale
        (suffixScale * upperScale) = 0) :
    ∀ upperCode lowerCode upperScale : ℚ,
      semanticIncidence ρ left right upperCode lowerCode upperScale
        (suffixScale * upperScale) = 0 := by
  let c₀ := (36 * ρ - 9 / 4) * left 0 * right 0 + 18 * left 0 * right 1
  let cX := 9 * ρ * left 0 * right 0
  let cY := (57 * ρ / 2 - 11 / 4) * left 0 * right 0 + 22 * left 0 * right 1
  let cσ := (-9 * ρ * left 0 + 9 * ρ / 4 * left 1) * right 0
  let cτ := (57 * ρ / 4 - 11 / 8) * left 1 * right 0 + 11 * left 1 * right 1
  have coefficientLaw : 22 * c₀ - 31 * cX - 18 * cY = 0 := by
    dsimp [c₀, cX, cY]
    ring
  have expansion
      (upperCode lowerCode upperScale lowerScale : ℚ) :
      semanticIncidence ρ left right upperCode lowerCode upperScale lowerScale =
        c₀ + cX * upperCode + cY * lowerCode +
          cσ * upperScale + cτ * lowerScale := by
    rw [semanticIncidence_eq]
  have constantZero : c₀ = 0 := by
    have equation := terminal 0 0
    rw [expansion] at equation
    simpa using equation
  have codeSumZero : cX + cY = 0 := by
    have equation := terminal 1 0
    rw [expansion] at equation
    norm_num [constantZero] at equation ⊢
    exact equation
  have scaleSumZero : suffixCode * cY + cσ + suffixScale * cτ = 0 := by
    have equation := terminal 0 1
    rw [expansion] at equation
    norm_num [constantZero] at equation
    linear_combination equation
  have upperZero : cX = 0 := by
    linarith [coefficientLaw, constantZero, codeSumZero]
  have lowerZero : cY = 0 := by linarith [codeSumZero, upperZero]
  have lengthZero : cσ + suffixScale * cτ = 0 := by
    rw [lowerZero] at scaleSumZero
    simpa using scaleSumZero
  intro upperCode lowerCode upperScale
  rw [expansion, constantZero, upperZero, lowerZero]
  linear_combination upperScale * lengthZero

/-- No fixed pair of endpoint rays recognizes the formal terminal equation on the compulsory
length plane by its zero set. -/
theorem no_fixed_semanticIncidence_terminal_zero_set
    (ρ suffixCode suffixScale : ℚ) (left right : Fin 2 → ℚ) :
    ¬∀ upperCode lowerCode upperScale : ℚ,
      semanticIncidence ρ left right upperCode lowerCode upperScale
          (suffixScale * upperScale) = 0 ↔
        lowerCode = upperCode + suffixCode * upperScale := by
  intro recognizes
  have terminal : ∀ upperCode upperScale : ℚ,
      semanticIncidence ρ left right upperCode
        (upperCode + suffixCode * upperScale) upperScale
        (suffixScale * upperScale) = 0 := by
    intro upperCode upperScale
    exact (recognizes upperCode (upperCode + suffixCode * upperScale) upperScale).mpr rfl
  have lengthPlane := semanticIncidence_terminal_forces_length
    ρ suffixCode suffixScale left right terminal
  have falsePositive := lengthPlane 0 (suffixCode + 1) 1
  have impossible := (recognizes 0 (suffixCode + 1) 1).mp falsePositive
  linarith

end ParabolicBlade

end MatrixMortality
