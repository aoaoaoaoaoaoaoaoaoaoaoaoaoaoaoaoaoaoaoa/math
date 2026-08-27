import MatrixMortality.ParabolicBlade

/-!
# Original parabolic semantic endpoint

This file places one complete side-normal correspondence block between the original parabolic
blade factors. It obstructs fixed-ray recognition of the formal terminal plane and reduces the
surviving construction to two exact mixed-gap endpoint rays.
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
    simp [semanticWordMiddle, semanticMiddle]

/-- Complete semantic middles compose in chronological word order. -/
theorem semanticWordMiddle_append
    (upper lower nextUpper nextLower : List Bool) :
    semanticWordMiddle (upper ++ nextUpper) (lower ++ nextLower) =
      semanticWordMiddle upper lower * semanticWordMiddle nextUpper nextLower := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [semanticWordMiddle, semanticMiddle, ternaryCode_append, pow_add,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
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

/-- Fixed terminal column in the original blade's reduced basis. -/
def semanticTerminalColumn (β : Nat) : Fin 3 → ℚ :=
  ![nearySideMarkerValue β, nearySideMarkerScale β, -1 / 2]

/-- Forced terminal ray after a complete semantic match. -/
def semanticTerminalTail : Fin 3 → ℚ := ![0, -2, 1]

/-- Kernel ray of the exceptional blade's input factor. -/
def bladeKernel : Fin 3 → ℚ := ![4, 4, -1]

/-- Column ray of the empty exceptional bridge. -/
def emptyBridgeColumn : Fin 2 → ℚ := ![18, 11]

private def emptyBridgeRow (ρ : ℚ) : Fin 2 → ℚ := ![(12 * ρ - 1) / 8, 1]

private theorem bridge_one_eq_outer (ρ : ℚ) :
    bridge ρ 1 = Matrix.vecMulVec emptyBridgeColumn (emptyBridgeRow ρ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bridge, coreInput, coreOutput, emptyBridgeColumn, emptyBridgeRow,
      Matrix.one_apply, Matrix.mul_apply, Matrix.vecMulVec_apply, Fin.sum_univ_succ] <;>
    ring

private theorem semanticWordMiddle_mulVec_terminalColumn_head
    (β : Nat) (upper lower : List Bool) :
    (semanticWordMiddle upper lower *ᵥ semanticTerminalColumn β) 0 =
      (ternaryCode (upper ++ nearyMarker β) : ℚ) - ternaryCode lower := by
  norm_num [semanticWordMiddle, semanticMiddle, semanticTerminalColumn,
    nearySideMarkerValue, nearySideMarkerScale, ternaryCode_append,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

private theorem semanticWordMiddle_mulVec_terminalColumn_of_terminal
    (β : Nat) (upper lower : List Bool)
    (terminal : upper ++ nearyMarker β = lower) :
    semanticWordMiddle upper lower *ᵥ semanticTerminalColumn β =
      (-(3 : ℚ) ^ lower.length / 2) • semanticTerminalTail := by
  subst lower
  ext i
  fin_cases i <;>
    norm_num [semanticWordMiddle, semanticMiddle, semanticTerminalColumn,
      semanticTerminalTail, nearySideMarkerValue, nearySideMarkerScale,
      ternaryCode_append, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      pow_add] <;>
    ring

private theorem coreInput_mulVec_eq_zero_iff (vector : Fin 3 → ℚ) :
    coreInput *ᵥ vector = 0 ↔ ∃ scalar : ℚ, vector = scalar • bladeKernel := by
  constructor
  · intro zero
    have first := congr_fun zero 0
    have second := congr_fun zero 1
    refine ⟨vector 0 / 4, ?_⟩
    funext i
    fin_cases i
    · norm_num [bladeKernel]
    · norm_num [coreInput, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at first
      norm_num [bladeKernel]
      linear_combination -first
    · norm_num [coreInput, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at first second
      norm_num [bladeKernel]
      change vector (2 : Fin 3) = -(vector 0 / 4)
      linear_combination (1 / 4) * first + second
  · rintro ⟨scalar, rfl⟩
    funext i
    fin_cases i
    all_goals
      norm_num [coreInput, bladeKernel, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ]
    all_goals ring

private theorem mulVec_injective_of_left_inverse
    (matrix inverse : Matrix (Fin 3) (Fin 3) ℚ)
    (left_inverse : inverse * matrix = 1) :
    Function.Injective matrix.mulVec := by
  intro left right equality
  have lifted := congrArg (fun vector => inverse *ᵥ vector) equality
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, left_inverse,
    Matrix.one_mulVec] at lifted
  simpa using lifted

private theorem emptyBridgeRow_ne_zero (ρ : ℚ) : emptyBridgeRow ρ ≠ 0 := by
  intro zero
  have second := congr_fun zero 1
  norm_num [emptyBridgeRow] at second

private theorem bridgeProduct_one_eq_zero_iff
    (ρ : ℚ) (middle : Matrix (Fin 3) (Fin 3) ℚ) :
    bridge ρ middle * bridge ρ 1 = 0 ↔
      bridge ρ middle *ᵥ emptyBridgeColumn = 0 := by
  rw [bridge_one_eq_outer, mul_outer]
  constructor
  · intro zero
    by_contra column_ne
    exact outer_ne_zero column_ne (emptyBridgeRow_ne_zero ρ) zero
  · rintro column_zero
    rw [column_zero]
    ext _i j
    simp [Matrix.vecMulVec_apply]

private theorem semanticBridge_mulVec_emptyBridgeColumn
    (ρ : ℚ) (middle leftContext rightContext : Matrix (Fin 3) (Fin 3) ℚ) :
    bridge ρ (leftContext * middle * rightContext) *ᵥ emptyBridgeColumn =
      coreInput *ᵥ
        (leftContext *ᵥ
          (middle *ᵥ
            ((rightContext * coreOutput ρ) *ᵥ emptyBridgeColumn))) := by
  simp only [bridge, Matrix.mulVec_mulVec, Matrix.mul_assoc]

private theorem core_semantic_zero_iff_terminal
    (β : Nat) (upper lower : List Bool)
    (leftContext leftInverse : Matrix (Fin 3) (Fin 3) ℚ)
    (leftScale : ℚ) (leftScale_ne : leftScale ≠ 0)
    (left_inverse : leftInverse * leftContext = 1)
    (left_target : leftContext *ᵥ semanticTerminalTail = leftScale • bladeKernel) :
    coreInput *ᵥ
        (leftContext *ᵥ
          (semanticWordMiddle upper lower *ᵥ semanticTerminalColumn β)) = 0 ↔
      upper ++ nearyMarker β = lower := by
  let middleVector := semanticWordMiddle upper lower *ᵥ semanticTerminalColumn β
  constructor
  · intro core_zero
    obtain ⟨scalar, context_eq⟩ :=
      (coreInput_mulVec_eq_zero_iff (leftContext *ᵥ middleVector)).mp core_zero
    have scaled_target :
        leftContext *ᵥ middleVector =
          leftContext *ᵥ ((scalar / leftScale) • semanticTerminalTail) := by
      rw [Matrix.mulVec_smul, left_target, context_eq]
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp [leftScale_ne]
    have middle_eq : middleVector = (scalar / leftScale) • semanticTerminalTail :=
      mulVec_injective_of_left_inverse leftContext leftInverse left_inverse scaled_target
    have head_zero : middleVector 0 = 0 := by
      rw [middle_eq]
      norm_num [semanticTerminalTail]
    change (semanticWordMiddle upper lower *ᵥ semanticTerminalColumn β) 0 = 0 at head_zero
    rw [semanticWordMiddle_mulVec_terminalColumn_head] at head_zero
    have code_eq_rat :
        (ternaryCode (upper ++ nearyMarker β) : ℚ) = ternaryCode lower :=
      sub_eq_zero.mp head_zero
    have code_eq_nat :
        ternaryCode (upper ++ nearyMarker β) = ternaryCode lower := by
      exact_mod_cast code_eq_rat
    exact ternaryCode_injective code_eq_nat
  · intro terminal
    rw [semanticWordMiddle_mulVec_terminalColumn_of_terminal β upper lower terminal]
    simp only [Matrix.mulVec_smul]
    rw [left_target]
    simp only [Matrix.mulVec_smul]
    have kernel_zero : coreInput *ᵥ bladeKernel = 0 :=
      (coreInput_mulVec_eq_zero_iff bladeKernel).mpr ⟨1, by simp⟩
    rw [kernel_zero]
    simp

/-- Reaching the two forced mixed-gap endpoint rays makes one semantic bridge followed by the
empty bridge vanish exactly on the Neary terminal language. -/
theorem conditional_semanticBridgeProduct_zero_iff_terminal
    (β : Nat) (upper lower : List Bool)
    (leftContext rightContext leftInverse : Matrix (Fin 3) (Fin 3) ℚ)
    (leftScale rightScale : ℚ)
    (leftScale_ne : leftScale ≠ 0) (rightScale_ne : rightScale ≠ 0)
    (left_inverse : leftInverse * leftContext = 1)
    (left_target : leftContext *ᵥ semanticTerminalTail = leftScale • bladeKernel)
    (right_target :
      (rightContext * coreOutput ((3 : ℚ) ^ β)) *ᵥ emptyBridgeColumn =
        rightScale • semanticTerminalColumn β) :
    bridge ((3 : ℚ) ^ β)
          (leftContext * semanticWordMiddle upper lower * rightContext) *
        bridge ((3 : ℚ) ^ β) 1 = 0 ↔
      upper ++ nearyMarker β = lower := by
  rw [bridgeProduct_one_eq_zero_iff,
    semanticBridge_mulVec_emptyBridgeColumn, right_target]
  simp only [Matrix.mulVec_smul, smul_eq_zero, rightScale_ne, false_or]
  exact core_semantic_zero_iff_terminal β upper lower leftContext leftInverse
    leftScale leftScale_ne left_inverse left_target

/-- A complete semantic context cannot reach the forced left endpoint ray. -/
theorem no_complete_semantic_left_target (upper lower : List Bool) :
    ¬∃ scale : ℚ,
      semanticWordMiddle upper lower *ᵥ semanticTerminalTail = scale • bladeKernel := by
  rintro ⟨scale, target⟩
  have second := congr_fun target 1
  have third := congr_fun target 2
  norm_num [semanticWordMiddle, semanticMiddle, semanticTerminalTail, bladeKernel,
    Matrix.mulVec, dotProduct, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Fin.sum_univ_succ] at second third
  have scaleEquality : (3 : ℚ) ^ upper.length = 2 * 3 ^ lower.length := by
    linarith
  have naturalEquality : 3 ^ upper.length = 2 * 3 ^ lower.length := by
    exact_mod_cast scaleEquality
  have oddThree : Odd 3 := ⟨1, by norm_num⟩
  have oddPower : Odd (3 ^ upper.length) := oddThree.pow
  have evenPower : Even (3 ^ upper.length) := ⟨3 ^ lower.length, by omega⟩
  exact (Nat.not_even_iff_odd.mpr oddPower) evenPower

/-- A complete semantic context cannot reach the forced right endpoint ray. -/
theorem no_complete_semantic_right_target
    (β : Nat) (upper lower : List Bool) :
    ¬∃ scale : ℚ,
      (semanticWordMiddle upper lower * coreOutput ((3 : ℚ) ^ β)) *ᵥ
          emptyBridgeColumn = scale • semanticTerminalColumn β := by
  rintro ⟨scale, target⟩
  have second := congr_fun target 1
  have third := congr_fun target 2
  have second_pos :
      0 < ((semanticWordMiddle upper lower * coreOutput ((3 : ℚ) ^ β)) *ᵥ
        emptyBridgeColumn) 1 := by
    norm_num [semanticWordMiddle, semanticMiddle, coreOutput, emptyBridgeColumn,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_succ]
  have third_pos :
      0 < ((semanticWordMiddle upper lower * coreOutput ((3 : ℚ) ^ β)) *ᵥ
        emptyBridgeColumn) 2 := by
    norm_num [semanticWordMiddle, semanticMiddle, coreOutput, emptyBridgeColumn,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_succ]
    ring_nf
    positivity
  rw [second] at second_pos
  rw [third] at third_pos
  norm_num [semanticTerminalColumn, Matrix.cons_val_two, Matrix.vecHead,
    Matrix.vecTail] at second_pos third_pos
  have markerScale_pos : 0 < nearySideMarkerScale β := by
    rw [nearySideMarkerScale_eq]
    positivity
  nlinarith

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
  have upperLength : 0 < upper.length := List.length_pos_of_ne_nil upper_nonempty
  have lowerLength : 0 < lower.length := List.length_pos_of_ne_nil lower_nonempty
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
    Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- If a fixed incidence vanishes on an affine terminal plane whose code slope escapes the
endpoint coefficient law, it vanishes on the whole length plane. -/
theorem semanticIncidence_terminal_forces_length
    (ρ markerCode markerScale : ℚ) (left right : Fin 2 → ℚ)
    (separates : 31 * markerScale - 22 * markerCode - 18 ≠ 0)
    (terminal : ∀ upperCode upperScale : ℚ,
      semanticIncidence ρ left right upperCode
        (markerScale * upperCode + markerCode) upperScale
        (markerScale * upperScale) = 0) :
    ∀ upperCode lowerCode upperScale : ℚ,
      semanticIncidence ρ left right upperCode lowerCode upperScale
        (markerScale * upperScale) = 0 := by
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
  have constantRelation : c₀ + markerCode * cY = 0 := by
    have equation := terminal 0 0
    rw [expansion] at equation
    norm_num at equation
    linear_combination equation
  have codeRelation : cX + markerScale * cY = 0 := by
    have equation := terminal 1 0
    rw [expansion] at equation
    norm_num at equation
    linear_combination equation - constantRelation
  have lengthRelation : cσ + markerScale * cτ = 0 := by
    have equation := terminal 0 1
    rw [expansion] at equation
    norm_num at equation
    linear_combination equation - constantRelation
  have factorZero : (31 * markerScale - 22 * markerCode - 18) * cY = 0 := by
    linear_combination coefficientLaw - 22 * constantRelation + 31 * codeRelation
  have lowerZero : cY = 0 := (mul_eq_zero.mp factorZero).resolve_left separates
  have constantZero : c₀ = 0 := by
    rw [lowerZero] at constantRelation
    simpa using constantRelation
  have upperZero : cX = 0 := by
    rw [lowerZero] at codeRelation
    simpa using codeRelation
  intro upperCode lowerCode upperScale
  rw [expansion, constantZero, upperZero, lowerZero]
  linear_combination upperScale * lengthRelation

/-- No fixed pair of endpoint rays recognizes an affine terminal equation whose code slope
escapes the endpoint coefficient law. -/
theorem no_fixed_semanticIncidence_terminal_zero_set
    (ρ markerCode markerScale : ℚ) (left right : Fin 2 → ℚ)
    (separates : 31 * markerScale - 22 * markerCode - 18 ≠ 0) :
    ¬∀ upperCode lowerCode upperScale : ℚ,
      semanticIncidence ρ left right upperCode lowerCode upperScale
          (markerScale * upperScale) = 0 ↔
        lowerCode = markerScale * upperCode + markerCode := by
  intro recognizes
  have terminal : ∀ upperCode upperScale : ℚ,
      semanticIncidence ρ left right upperCode
        (markerScale * upperCode + markerCode) upperScale
        (markerScale * upperScale) = 0 := by
    intro upperCode upperScale
    exact (recognizes upperCode (markerScale * upperCode + markerCode) upperScale).mpr rfl
  have lengthPlane := semanticIncidence_terminal_forces_length
    ρ markerCode markerScale left right separates terminal
  have falsePositive := lengthPlane 0 (markerCode + 1) 1
  have impossible := (recognizes 0 (markerCode + 1) 1).mp falsePositive
  linarith

/-- Fixed endpoint rays cannot recognize the actual Neary terminal plane through one intact
complete original block. -/
theorem no_fixed_semanticIncidence_neary_terminal_zero_set
    (β : Nat) (left right : Fin 2 → ℚ) :
    ¬∀ upperCode lowerCode upperScale : ℚ,
      semanticIncidence ((3 : ℚ) ^ β) left right upperCode lowerCode upperScale
          (nearySideMarkerScale β * upperScale) = 0 ↔
        lowerCode = nearySideMarkerScale β * upperCode + nearySideMarkerValue β := by
  apply no_fixed_semanticIncidence_terminal_zero_set
  rw [nearySideMarkerScale_eq, nearySideMarkerValue_eq]
  have scale_one : (1 : ℚ) ≤ 3 ^ β := one_le_pow₀ (by norm_num)
  intro equality
  have positive : (0 : ℚ) < 38 * 3 ^ β - 7 := by linarith
  apply positive.ne'
  linear_combination equality

end ParabolicBlade

end MatrixMortality
