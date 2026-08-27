import MatrixMortality.LinearRepresentation
import MatrixMortality.NearyEncoding

/-!
# Ternary closed-block obstructions

Paired Parikh vectors expose four independent additive channels in Neary's four role pairs.
Consequently, fixed exact role macros still require four source letters even when both target
morphisms may erase. This file also records the arithmetic skeleton of the stronger stationary
closed-block obstruction.
-/

namespace MatrixMortality

namespace TernaryClosedBlockNoGo

/-! ## Paired Parikh rank -/

/-- Canonical order of the four Neary roles used by the Parikh certificate. -/
def role : Fin 4 → NearyTile :=
  ![.rule .c, .rule .b, .erase .b, .erase .c]

/-- Counts of ones and zeros on both sides of a binary word pair. -/
def pairedParikh (upper lower : List Bool) : Fin 4 → ℚ :=
  ![upper.count true, upper.count false, lower.count true, lower.count false]

/-- The actual paired-Parikh matrix of the four Neary roles. -/
def nearyPairedParikh (β : Nat) (body : List TagLetter) : Square (Fin 4) ℚ :=
  fun index => pairedParikh (nearyUpper β (role index)) (nearyLower β body (role index))

theorem tagEncode_count_true (β : Nat) (body : List TagLetter) :
    (tagEncode β body).count true = 2 * body.count .b + body.count .c := by
  change (spell (tagCode β) body).count true = _
  induction body with
  | nil => simp [tagEncode, spell]
  | cons letter tail induction =>
      change (tagCode β letter ++ spell (tagCode β) tail).count true = _
      rw [List.count_append, induction]
      cases letter <;>
        simp [tagCode, List.count_replicate] <;>
        omega

theorem tagEncode_count_false (β : Nat) (body : List TagLetter) :
    (tagEncode β body).count false = β * body.count .b := by
  change (spell (tagCode β) body).count false = _
  induction body with
  | nil => simp [tagEncode, spell]
  | cons letter tail induction =>
      change (tagCode β letter ++ spell (tagCode β) tail).count false = _
      rw [List.count_append, induction]
      cases letter <;>
        simp [tagCode, List.count_replicate, Nat.succ_mul, Nat.mul_succ]
      all_goals omega

/-- Closed arithmetic form of the paired-Parikh matrix. -/
def closedNearyPairedParikh (β bCount cCount : ℚ) : Square (Fin 4) ℚ :=
  !![1, 0, 2 + 2 * bCount + cCount, 1 + β * bCount;
     2, β, 2, 1;
     2, β, 0, 1;
     1, 0, 0, 1]

theorem nearyPairedParikh_eq_closed (β : Nat) (body : List TagLetter) :
    nearyPairedParikh β body =
      closedNearyPairedParikh β (body.count .b) (body.count .c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nearyPairedParikh, pairedParikh, role, closedNearyPairedParikh,
      nearyUpper, nearyLower, tagCode, List.count_append, tagEncode_count_true,
      tagEncode_count_false, List.count_replicate, Matrix.vecHead, Matrix.vecTail]
  all_goals ring

/-- The four closed role vectors are independent whenever the deletion width and the number of
`b` letters in the body are positive. -/
theorem closedNearyPairedParikh_vecMul_injective
    (β bCount cCount : ℚ) (β_pos : 0 < β) (bCount_pos : 0 < bCount) :
    Function.Injective (closedNearyPairedParikh β bCount cCount).vecMul := by
  intro x y equality
  have at0 := congr_fun equality 0
  have at1 := congr_fun equality 1
  have at2 := congr_fun equality 2
  have at3 := congr_fun equality 3
  simp [closedNearyPairedParikh, Matrix.vecMul, Matrix.dotProduct,
    Fin.sum_univ_succ] at at0 at1 at2 at3
  change x 0 + (x 1 * 2 + (x 2 * 2 + x 3)) =
    y 0 + (y 1 * 2 + (y 2 * 2 + y 3)) at at0
  change x 1 * β + x 2 * β = y 1 * β + y 2 * β at at1
  change x 0 * (2 + 2 * bCount + cCount) + x 1 * 2 =
    y 0 * (2 + 2 * bCount + cCount) + y 1 * 2 at at2
  change x 0 * (1 + β * bCount) + (x 1 + (x 2 + x 3)) =
    y 0 * (1 + β * bCount) + (y 1 + (y 2 + y 3)) at at3
  have β_ne_zero : β ≠ 0 := ne_of_gt β_pos
  have bCount_ne_zero : bCount ≠ 0 := ne_of_gt bCount_pos
  have sum12 : x 1 + x 2 = y 1 + y 2 := by
    have product_zero : β * ((x 1 + x 2) - (y 1 + y 2)) = 0 := by
      nlinarith [at1]
    exact sub_eq_zero.mp ((mul_eq_zero.mp product_zero).resolve_left β_ne_zero)
  have first_product_zero :
      (β * bCount) * (x 0 - y 0) = 0 := by
    nlinarith [at0, at3, sum12]
  have first_eq : x 0 = y 0 := by
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp first_product_zero).resolve_left
      (mul_ne_zero β_ne_zero bCount_ne_zero)
  have second_eq : x 1 = y 1 := by
    rw [first_eq] at at2
    linarith
  have third_eq : x 2 = y 2 := by linarith [sum12, second_eq]
  have fourth_eq : x 3 = y 3 := by linarith [at0, sum12, first_eq]
  funext index
  fin_cases index
  · exact first_eq
  · exact second_eq
  · exact third_eq
  · exact fourth_eq

theorem closedNearyPairedParikh_isUnit
    (β bCount cCount : ℚ) (β_pos : 0 < β) (bCount_pos : 0 < bCount) :
    IsUnit (closedNearyPairedParikh β bCount cCount) :=
  Matrix.vecMul_injective_iff_isUnit.mp
    (closedNearyPairedParikh_vecMul_injective β bCount cCount β_pos bCount_pos)

/-- The actual four-role paired-Parikh map is injective under Neary's nondegenerate
parameters. -/
theorem nearyPairedParikh_vecMul_injective
    (β : Nat) (body : List TagLetter) (β_pos : 0 < β) (body_has_b : .b ∈ body) :
    Function.Injective (nearyPairedParikh β body).vecMul := by
  rw [nearyPairedParikh_eq_closed]
  apply closedNearyPairedParikh_vecMul_injective
  · exact_mod_cast β_pos
  · exact_mod_cast List.count_pos_iff_mem.mpr body_has_b

theorem nearyPairedParikh_det_ne_zero
    (β : Nat) (body : List TagLetter) (β_pos : 0 < β) (body_has_b : .b ∈ body) :
    (nearyPairedParikh β body).det ≠ 0 :=
  ((nearyPairedParikh β body).isUnit_iff_isUnit_det.mp
    (Matrix.vecMul_injective_iff_isUnit.mp
      (nearyPairedParikh_vecMul_injective β body β_pos body_has_b))).ne_zero

/-! ## Erasing exact macros -/

/-- Exact rolewise factorization through fixed macros, with no nonerasure assumption. -/
structure ExactErasingMacroFactorization
    (β : Nat) (body : List TagLetter) (C : Type*) where
  /-- Physical word assigned to one semantic Neary role. -/
  code : NearyTile → List C
  /-- Possibly erasing upper target image of one physical letter. -/
  upper : C → List Bool
  /-- Possibly erasing lower target image of one physical letter. -/
  lower : C → List Bool
  upper_exact : ∀ tile, spell upper (code tile) = nearyUpper β tile
  lower_exact : ∀ tile, spell lower (code tile) = nearyLower β body tile

private theorem count_spell_eq_sum {C D : Type*} [Fintype C] [DecidableEq C]
    [DecidableEq D] (side : C → List D) (word : List C) (symbol : D) :
    ((spell side word).count symbol : ℚ) =
      ∑ letter : C,
        (word.count letter : ℚ) * (side letter).count symbol := by
  change ((spell side word).count symbol : ℚ) = _
  induction word with
  | nil => simp [spell]
  | cons head tail induction =>
      change ((side head ++ spell side tail).count symbol : ℚ) = _
      rw [List.count_append, Nat.cast_add, induction]
      simp only [List.count_cons, Nat.cast_add, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib, add_comm]
      simp

private def macroCountMatrix {β : Nat} {body : List TagLetter} {C : Type*}
    [Fintype C] [DecidableEq C]
    (factorization : ExactErasingMacroFactorization β body C) : Matrix (Fin 4) C ℚ :=
  fun index letter => factorization.code (role index) |>.count letter

private def letterParikhMatrix {β : Nat} {body : List TagLetter} {C : Type*}
    [Fintype C] [DecidableEq C]
    (factorization : ExactErasingMacroFactorization β body C) : Matrix C (Fin 4) ℚ :=
  fun letter => pairedParikh (factorization.upper letter) (factorization.lower letter)

private theorem nearyPairedParikh_factor {β : Nat} {body : List TagLetter} {C : Type*}
    [Fintype C] [DecidableEq C]
    (factorization : ExactErasingMacroFactorization β body C) :
    nearyPairedParikh β body =
      macroCountMatrix factorization * letterParikhMatrix factorization := by
  ext index channel
  fin_cases channel
  · rw [nearyPairedParikh, pairedParikh, ← factorization.upper_exact (role index)]
    simpa [macroCountMatrix, letterParikhMatrix, pairedParikh, Matrix.mul_apply] using
      count_spell_eq_sum factorization.upper (factorization.code (role index)) true
  · rw [nearyPairedParikh, pairedParikh, ← factorization.upper_exact (role index)]
    simpa [macroCountMatrix, letterParikhMatrix, pairedParikh, Matrix.mul_apply] using
      count_spell_eq_sum factorization.upper (factorization.code (role index)) false
  · rw [nearyPairedParikh, pairedParikh, ← factorization.lower_exact (role index)]
    simpa [macroCountMatrix, letterParikhMatrix, pairedParikh, Matrix.mul_apply] using
      count_spell_eq_sum factorization.lower (factorization.code (role index)) true
  · rw [nearyPairedParikh, pairedParikh, ← factorization.lower_exact (role index)]
    simpa [macroCountMatrix, letterParikhMatrix, pairedParikh, Matrix.mul_apply] using
      count_spell_eq_sum factorization.lower (factorization.code (role index)) false

/-- Fixed exact macros for the four Neary word pairs require at least four physical letters even
when both target morphisms erase and the four macro words are empty, unequal, coincident, or
nonuniquely decodable. -/
theorem ExactErasingMacroFactorization.four_le_card
    {β : Nat} {body : List TagLetter} {C : Type*}
    [Fintype C] [DecidableEq C]
    (factorization : ExactErasingMacroFactorization β body C)
    (β_pos : 0 < β) (body_has_b : .b ∈ body) :
    4 ≤ Fintype.card C := by
  apply card_le_of_det_rectangular_product_ne_zero
    (macroCountMatrix factorization) (letterParikhMatrix factorization)
  rw [← nearyPairedParikh_factor factorization]
  exact nearyPairedParikh_det_ne_zero β body β_pos body_has_b

/-! ## Closed-block arithmetic skeleton -/

/-- On an exact stroke history, the binary terminal equation is equivalent to the block-level
queue equation: consumed letters followed by `b` equal the leading `c` followed by every rule
output.  This includes arbitrary null-history extensions. -/
theorem tileHistory_terminal_match_iff_block_semantics
    (β : Nat) (body : List TagLetter) (β_pos : 0 < β)
    (first : Stroke TagLetter β) (history : List (Stroke TagLetter β)) :
    spell (nearyUpper β) (tileHistory (first :: history)) ++ nearyMarker β =
        spell (nearyLower β body) (tileHistory (first :: history)) ↔
      consumed (first :: history) ++ [.b] =
        .c :: produced (tagOutput body) (first :: history) := by
  constructor
  · intro terminal_match
    have semantic :=
      tileHistory_semantic_eq_of_terminal_match
        β body β_pos first history terminal_match
    simpa [produced_cons, tagOutput, List.append_assoc] using semantic
  · intro semantic
    apply List.append_cancel_right (bs := [true])
    rw [spell_nearyUpper_tileHistory, spell_nearyLower_tileHistory_append_true]
    calc
      (tagEncode β (consumed (first :: history)) ++ nearyMarker β) ++ [true] =
          tagEncode β (consumed (first :: history) ++ [.b]) := by
            rw [List.append_assoc, marker_append_true, ← tagEncode_append]
      _ = tagEncode β (.c :: produced (tagOutput body) (first :: history)) := by
        rw [semantic]
      _ = tagEncode β
          (.c :: nearyBody body first.head ++ [.b] ++
            produced (tagOutput body) history) := by
        simp [produced_cons, tagOutput, List.append_assoc]

/-- The final arithmetic throat of the three-pulse obstruction: a positive word morphism cannot
contribute one lower letter per block while spelling at least two upper letters per block. -/
theorem no_fractional_lower_contribution
    (β contribution blocks : Nat) (two_le : 2 ≤ β) (blocks_pos : 0 < blocks) :
    contribution * β * blocks ≠ blocks := by
  intro equal
  by_cases contribution_zero : contribution = 0
  · subst contribution
    simp at equal
    omega
  · have contribution_pos : 0 < contribution := Nat.pos_of_ne_zero contribution_zero
    have beta_le_product : β ≤ contribution * β := by
      simpa using Nat.mul_le_mul_right β (Nat.succ_le_iff.mpr contribution_pos)
    have factor_gt : 1 < contribution * β := lt_of_lt_of_le (by omega) beta_le_product
    have scaled := mul_lt_mul_of_pos_right factor_gt blocks_pos
    have blocks_lt : blocks < contribution * β * blocks := by simpa using scaled
    exact (ne_of_gt blocks_lt) equal

/-- Once stationary closed-block identities are reduced to paired Parikh data, the common lower
deletion image has only the two possibilities used by the complete no-go proof. -/
theorem commonLowerDeletion_cases
    (β : ℤ) (dOne dZero : ℤ) (four_le : 4 ≤ β)
    (d_nonnegative : 0 ≤ dOne ∧ 0 ≤ dZero)
    (bounded : (β - 1) * dOne ≤ 2 ∧ (β - 1) * dZero ≤ β) :
    (dOne = 0 ∧ dZero = 0) ∨ (dOne = 0 ∧ dZero = 1) := by
  rcases d_nonnegative with ⟨dOne_nonnegative, dZero_nonnegative⟩
  rcases bounded with ⟨dOne_bound, dZero_bound⟩
  have dOne_zero : dOne = 0 := by nlinarith
  have dZero_le_one : dZero ≤ 1 := by nlinarith
  omega

/-- The upper residual shift forced by a stationary block has only the two integral values used
by the complete no-go proof. -/
theorem upperResidualShift_cases
    (β shiftOne shiftZero : ℤ) (four_le : 4 ≤ β)
    (deleteC_nonnegative : 0 ≤ 1 + shiftOne ∧ 0 ≤ shiftZero)
    (ruleC_nonnegative : 0 ≤ 1 - (β - 1) * shiftOne ∧
      0 ≤ -(β - 1) * shiftZero) :
    (shiftOne = -1 ∧ shiftZero = 0) ∨
      (shiftOne = 0 ∧ shiftZero = 0) := by
  rcases deleteC_nonnegative with ⟨deleteC_one, deleteC_zero⟩
  rcases ruleC_nonnegative with ⟨ruleC_one, ruleC_zero⟩
  have shiftZero_eq : shiftZero = 0 := by nlinarith
  have shiftOne_upper : shiftOne ≤ 0 := by nlinarith
  omega

end TernaryClosedBlockNoGo

end MatrixMortality
