import MatrixMortality.ParabolicRetuned

/-!
# Retuned parabolic semantic boundary

This file evaluates complete Neary gaps under the retuned root, contracts the gap-two blade to a
two-dimensional bridge, and proves that its determinant is exactly the Neary terminal language.
It then realizes the determinant as one fixed minor of a literal word over the same three
physical generators.
-/

namespace MatrixMortality

open scoped Matrix

namespace ParabolicRetuned

/-! ## Complete-gap semantics -/

/-- Sparse side-normal matrix carrying one upper and one lower binary word. -/
def semanticMatrix (upper lower : List Bool) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, sparseCode upper, 2 * sparseCode lower;
     0, 3 ^ upper.length, 0;
     0, 0, 3 ^ lower.length]

@[simp] theorem semanticMatrix_nil : semanticMatrix [] [] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [semanticMatrix, Matrix.one_apply, Matrix.vecHead, Matrix.vecTail]
  all_goals split <;> simp_all

theorem semanticMatrix_append
    (upper lower nextUpper nextLower : List Bool) :
    semanticMatrix (upper ++ nextUpper) (lower ++ nextLower) =
      semanticMatrix upper lower * semanticMatrix nextUpper nextLower := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [semanticMatrix, sparseCode_append, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.vecHead, Matrix.vecTail, pow_add] <;>
    ring

/-- Root gap naming the rule or erasure phase of one Neary tile. -/
def tileGap : NearyTile → Nat
  | .rule _ => 3
  | .erase _ => 0

/-- Reduced retuned atom named by one complete Neary tile. -/
def tileAtom (β : Nat) (body : List TagLetter) (tile : NearyTile) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  atom β body tile.letter (tileGap tile)

private theorem markerCode_cast (β : Nat) :
    (markerCode β : ℚ) = ((3 : ℚ) ^ β - 1) / 2 := by
  have relation : (2 : ℚ) * markerCode β + 1 = 3 ^ β := by
    exact_mod_cast markerCode_relation β
  linarith

private theorem upperBCode_cast (β : Nat) :
    (upperBCode β : ℚ) = 3 * ((3 : ℚ) ^ β - 1) / 2 := by
  have relation : (2 : ℚ) * upperBCode β + 3 = 3 * 3 ^ β := by
    exact_mod_cast upperBCode_relation β
  linarith

/-- Every complete gap is exactly the sparse side-normal matrix of its Neary tile. -/
theorem tileAtom_eq_semanticMatrix
    (β : Nat) (body : List TagLetter) (tile : NearyTile) :
    tileAtom β body tile =
      semanticMatrix (nearyUpper β tile) (nearyLower β body tile) := by
  cases tile with
  | erase letter =>
      cases letter with
      | b =>
          simp only [tileAtom, tileGap, NearyTile.letter, semanticMatrix, nearyUpper,
            nearyLower]
          rw [show sparseCode (tagCode β .b) = upperBCode β by rfl]
          ext i j
          fin_cases i <;> fin_cases j <;>
            norm_num [atom, dataFlank, bFlank, ParabolicBlade.flank,
              ParabolicBlade.injection, tagCode, upperBCode_cast, sparseCode,
              sparseDigit, Matrix.mul_apply, Fin.sum_univ_succ] ;
            ring
      | c =>
          simp only [tileAtom, tileGap, NearyTile.letter, semanticMatrix, nearyUpper,
            nearyLower]
          ext i j
          fin_cases i <;> fin_cases j <;>
            norm_num [atom, dataFlank, cFlank, ParabolicBlade.flank,
              ParabolicBlade.injection, tagCode, lowerCCode, lowerCScale, sparseCode,
              sparseDigit, Matrix.mul_apply, Fin.sum_univ_succ] ;
            ring
  | rule letter =>
      cases letter with
      | b =>
          simp only [tileAtom, tileGap, NearyTile.letter, semanticMatrix, nearyUpper,
            nearyLower]
          rw [show sparseCode (tagCode β .b) = upperBCode β by rfl]
          rw [atom, root_cube]
          ext i j
          fin_cases i <;> fin_cases j <;>
            norm_num [dataFlank, bFlank, ParabolicBlade.flank, ParabolicBlade.drift,
              ParabolicBlade.injection, tagCode, upperBCode_cast, sparseCode, sparseDigit,
              Nat.ofDigits, Matrix.mul_apply, Fin.sum_univ_succ] ;
            ring
      | c =>
          simp only [tileAtom, tileGap, NearyTile.letter, semanticMatrix, nearyUpper,
            nearyLower]
          rw [atom, root_cube]
          ext i j
          fin_cases i <;> fin_cases j <;>
            norm_num [dataFlank, cFlank, ParabolicBlade.flank, ParabolicBlade.drift,
              ParabolicBlade.injection, nearyLower, tagCode, lowerCCode, lowerCScale,
              sparseCode, sparseDigit, pow_add, Matrix.mul_apply, Fin.sum_univ_succ] <;>
            ring

/-- Product of the complete reduced atoms named by a Neary word. -/
def tileProduct (β : Nat) (body : List TagLetter) (word : List NearyTile) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  wordProduct (tileAtom β body) word

/-- Complete retuned words evaluate without reversal to the two sparse correspondence strings. -/
theorem tileProduct_eq_semanticMatrix
    (β : Nat) (body : List TagLetter) (word : List NearyTile) :
    tileProduct β body word =
      semanticMatrix (spell (nearyUpper β) word) (spell (nearyLower β body) word) := by
  induction word with
  | nil => simp [tileProduct, wordProduct, spell]
  | cons tile word induction =>
      rw [tileProduct, wordProduct_cons, tileAtom_eq_semanticMatrix]
      change semanticMatrix _ _ * wordProduct (tileAtom β body) word = _
      rw [← tileProduct, induction, ← semanticMatrix_append]
      rfl

/-! ## Exceptional bridge -/

/-- Full-column-rank output factor of the retuned gap-two `b` atom. -/
def bladeOutput (β : Nat) : Matrix (Fin 3) (Fin 2) ℚ :=
  let ρ : ℚ := 3 ^ β
  let μ : ℚ := markerCode β
  !![-1 - 3 * μ, 2;
     -9 * ρ, 0;
     -8, 19]

/-- Full-row-rank input factor of the retuned gap-two `b` atom. -/
def bladeInput : Matrix (Fin 2) (Fin 3) ℚ :=
  !![1, 0, 0;
     0, 1 / 2, 1]

/-- The retuned exceptional atom is exactly the displayed rank-two factorization. -/
theorem exceptional_factor (β : Nat) (body : List TagLetter) :
    atom β body .b 2 = bladeOutput β * bladeInput := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [atom, dataFlank, bFlank, bladeOutput, bladeInput,
      ParabolicBlade.flank, root, ParabolicBlade.injection, markerCode_cast,
      pow_succ, Matrix.mul_apply, Fin.sum_univ_succ] ;
    ring

/-- Two-dimensional bridge cut out between two retuned exceptional atoms. -/
def bridge (β : Nat) (middle : Matrix (Fin 3) (Fin 3) ℚ) :
    Matrix (Fin 2) (Fin 2) ℚ :=
  bladeInput * middle * bladeOutput β

/-- The bridge determinant is the cross-multiplied difference of the two affine sparse codes. -/
theorem bridge_semanticMatrix_det
    (β : Nat) (upper lower : List Bool) :
    (bridge β (semanticMatrix upper lower)).det =
      3 *
        ((sparseNumerator lower : ℚ) * 3 ^ (upper ++ nearyMarker β).length -
          (sparseNumerator (upper ++ nearyMarker β) : ℚ) * 3 ^ lower.length) := by
  rw [bridge, Matrix.det_fin_two]
  norm_num [bladeInput, bladeOutput, semanticMatrix, sparseNumerator,
    sparseCode_append, markerCode, nearyMarker_length, pow_add, pow_succ,
    Matrix.mul_apply, Fin.sum_univ_succ]
  ring

/-- The bridge always retains a nonzero lower-right entry. -/
theorem bridge_semanticMatrix_bottom_right
    (β : Nat) (upper lower : List Bool) :
    bridge β (semanticMatrix upper lower) 1 1 = 19 * 3 ^ lower.length := by
  norm_num [bridge, bladeInput, bladeOutput, semanticMatrix, Matrix.mul_apply,
    Fin.sum_univ_succ]
  ring

theorem bridge_semanticMatrix_ne_zero
    (β : Nat) (upper lower : List Bool) :
    bridge β (semanticMatrix upper lower) ≠ 0 := by
  intro zero
  have entry := congr_fun (congr_fun zero 1) 1
  rw [bridge_semanticMatrix_bottom_right] at entry
  exact (by positivity : (19 : ℚ) * 3 ^ lower.length ≠ 0) entry

private theorem marker_eq_append_false (β : Nat) (β_pos : 0 < β) :
    ∃ stem, nearyMarker β = stem ++ [false] := by
  obtain ⟨prior, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : β ≠ 0)
  refine ⟨true :: List.replicate prior false, ?_⟩
  simp [nearyMarker, List.replicate_succ']

private theorem lowerTile_eq_append_false
    (β : Nat) (body : List TagLetter) (tile : NearyTile) :
    ∃ stem, nearyLower β body tile = stem ++ [false] := by
  cases tile with
  | erase letter =>
      cases letter <;> exact ⟨[], by simp [nearyLower]⟩
  | rule letter =>
      cases letter
      · exact ⟨[true, true], by simp [nearyLower]⟩
      · exact ⟨true :: tagEncode β body ++ [true], by simp [nearyLower]⟩

private theorem spellLower_eq_append_false
    (β : Nat) (body : List TagLetter) (word : List NearyTile) (word_nonempty : word ≠ []) :
    ∃ stem, spell (nearyLower β body) word = stem ++ [false] := by
  induction word with
  | nil => exact False.elim (word_nonempty rfl)
  | cons tile word induction =>
      by_cases tail_empty : word = []
      · subst word
        simpa [spell] using lowerTile_eq_append_false β body tile
      · obtain ⟨stem, shape⟩ := induction tail_empty
        refine ⟨nearyLower β body tile ++ stem, ?_⟩
        change nearyLower β body tile ++ spell (nearyLower β body) word = _
        rw [shape, List.append_assoc]

private theorem sparse_cross_cast_eq_iff
    (leftStem rightStem : List Bool) :
    (sparseNumerator (leftStem ++ [false]) : ℚ) *
          3 ^ (rightStem ++ [false]).length =
        (sparseNumerator (rightStem ++ [false]) : ℚ) *
          3 ^ (leftStem ++ [false]).length ↔
      leftStem = rightStem := by
  constructor
  · intro equality
    have natural_equality :
        sparseNumerator (leftStem ++ [false]) * 3 ^ (rightStem ++ [false]).length =
          sparseNumerator (rightStem ++ [false]) *
            3 ^ (leftStem ++ [false]).length := by
      exact_mod_cast equality
    exact (sparseFraction_cross_eq_iff leftStem rightStem).mp natural_equality
  · intro equality
    exact_mod_cast (sparseFraction_cross_eq_iff leftStem rightStem).mpr equality

private theorem bridge_semanticMatrix_det_eq_zero_iff_of_suffixes
    (β : Nat) (upper lower upperStem lowerStem : List Bool)
    (upper_shape : upper ++ nearyMarker β = upperStem ++ [false])
    (lower_shape : lower = lowerStem ++ [false]) :
    (bridge β (semanticMatrix upper lower)).det = 0 ↔
      upper ++ nearyMarker β = lower := by
  rw [bridge_semanticMatrix_det, mul_eq_zero]
  simp only [OfNat.ofNat_ne_zero, false_or, sub_eq_zero]
  rw [upper_shape, lower_shape, sparse_cross_cast_eq_iff]
  constructor
  · exact fun equality => congrArg (· ++ [false]) equality.symm
  · exact fun equality => (List.append_cancel_right equality).symm

private theorem bridge_one_det_ne_zero (β : Nat) (β_pos : 0 < β) :
    (bridge β 1).det ≠ 0 := by
  have marker_relation : (2 : ℚ) * markerCode β + 1 = 3 ^ β := by
    exact_mod_cast markerCode_relation β
  have scale_ge : (3 : ℚ) ≤ 3 ^ β := by
    calc
      (3 : ℚ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ β := pow_le_pow_right (by norm_num) β_pos
  rw [Matrix.det_fin_two]
  norm_num [bridge, bladeInput, bladeOutput, Matrix.one_apply, Matrix.mul_apply,
    Fin.sum_univ_succ]
  intro equality
  linarith

/-- The retuned bridge determinant vanishes exactly on the Neary terminal equation. -/
theorem bridge_tileProduct_det_eq_zero_iff_terminal_match
    (β : Nat) (body : List TagLetter) (β_pos : 0 < β) (word : List NearyTile) :
    (bridge β (tileProduct β body word)).det = 0 ↔
      spell (nearyUpper β) word ++ nearyMarker β =
        spell (nearyLower β body) word := by
  cases word with
  | nil =>
      simp only [tileProduct, wordProduct, spell]
      constructor
      · exact False.elim ∘ bridge_one_det_ne_zero β β_pos
      · intro marker_empty
        simp [nearyMarker] at marker_empty
  | cons tile word =>
      rw [tileProduct_eq_semanticMatrix]
      obtain ⟨markerStem, marker_shape⟩ := marker_eq_append_false β β_pos
      obtain ⟨lowerStem, lower_shape⟩ :=
        spellLower_eq_append_false β body (tile :: word) (by simp)
      apply bridge_semanticMatrix_det_eq_zero_iff_of_suffixes
        β _ _ (spell (nearyUpper β) (tile :: word) ++ markerStem) lowerStem
      · rw [marker_shape, List.append_assoc]
      · exact lower_shape

/-- At a terminal match, the two bridge columns have the fixed ratio `-1/2`. -/
theorem bridge_semanticMatrix_terminal_columns
    (β : Nat) (upper : List Bool) (i : Fin 2) :
    bridge β (semanticMatrix upper (upper ++ nearyMarker β)) i 0 =
      -(1 / 2 : ℚ) * bridge β (semanticMatrix upper (upper ++ nearyMarker β)) i 1 := by
  fin_cases i <;>
    norm_num [bridge, bladeInput, bladeOutput, semanticMatrix, sparseCode_append,
      markerCode, markerCode_cast, nearyMarker_length, pow_add, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    ring

/-- For every paired control word, the internal bridge determinant is its checked paired
coefficient zero set. -/
theorem bridge_decoded_det_eq_zero_iff_pairedCoefficient
    (β : Nat) (body : List TagLetter) (β_pos : 0 < β) (word : List PairedControl) :
    (bridge β (tileProduct β body (decodePairedWord word))).det = 0 ↔
      pairedCoefficient ℚ β body word = 0 := by
  rw [pairedCoefficient_eq_sideCoefficient,
    sideCoefficient_eq_zero_iff_terminal_match_rat]
  exact bridge_tileProduct_det_eq_zero_iff_terminal_match
    β body β_pos (decodePairedWord word)

/-! ## Literal physical contexts -/

/-- Physical macro for one complete Neary tile. -/
def physicalTile (β : Nat) (body : List TagLetter) (tile : NearyTile) :
    Matrix (Fin 4) (Fin 4) ℚ :=
  dataGenerator β body tile.letter * root ^ tileGap tile

/-- Physical product of the complete tile macros. -/
def physicalMiddle (β : Nat) (body : List TagLetter) (word : List NearyTile) :
    Matrix (Fin 4) (Fin 4) ℚ :=
  wordProduct (physicalTile β body) word

/-- The physical middle contracts through the common image to the reduced tile product. -/
theorem physicalMiddle_mul_injection
    (β : Nat) (body : List TagLetter) (word : List NearyTile) :
    physicalMiddle β body word * ParabolicBlade.injection =
      ParabolicBlade.injection * tileProduct β body word := by
  induction word with
  | nil => simp [physicalMiddle, tileProduct, wordProduct]
  | cons tile word induction =>
      have contracted :
          wordProduct (physicalTile β body) word * ParabolicBlade.injection =
            ParabolicBlade.injection * wordProduct (tileAtom β body) word := by
        simpa only [physicalMiddle, tileProduct] using induction
      simp only [physicalMiddle, tileProduct, wordProduct_cons]
      rw [Matrix.mul_assoc, contracted]
      simp only [physicalTile, tileAtom, dataGenerator, atom, Matrix.mul_assoc]

/-- Physical context placing two exceptional gap-two atoms around a complete Neary word. -/
def physicalContext (β : Nat) (body : List TagLetter) (word : List NearyTile) :
    Matrix (Fin 4) (Fin 4) ℚ :=
  dataGenerator β body .b * root ^ 2 * physicalMiddle β body word *
    dataGenerator β body .b * root ^ 2 * dataGenerator β body .b

/-- The retuned alphabet consists of the root and the two data generators. -/
def generator (β : Nat) (body : List TagLetter) :
    Option TagLetter → Matrix (Fin 4) (Fin 4) ℚ :=
  separatedGenerator root (dataGenerator β body)

/-- The retuned physical family has exactly three labels. -/
theorem generator_count : Fintype.card (Option TagLetter) = 3 := by decide

/-- Literal three-letter word realizing one complete Neary tile. -/
def tileWord (tile : NearyTile) : List (Option TagLetter) :=
  some tile.letter :: List.replicate (tileGap tile) none

/-- Literal concatenation of the complete tile words. -/
def middleWord (word : List NearyTile) : List (Option TagLetter) :=
  word.bind tileWord

private theorem tileWord_product
    (β : Nat) (body : List TagLetter) (tile : NearyTile) :
    wordProduct (generator β body) (tileWord tile) = physicalTile β body tile := by
  simp [generator, tileWord, physicalTile, wordProduct, separatedGenerator]

private theorem middleWord_product
    (β : Nat) (body : List TagLetter) (word : List NearyTile) :
    wordProduct (generator β body) (middleWord word) = physicalMiddle β body word := by
  induction word with
  | nil => simp [middleWord, physicalMiddle, wordProduct]
  | cons tile word induction =>
      change wordProduct (generator β body) (word.bind tileWord) =
        physicalMiddle β body word at induction
      rw [middleWord, List.bind_cons, wordProduct_append, tileWord_product,
        physicalMiddle, wordProduct_cons, induction]
      rfl

/-- Literal physical context word over the retuned three-generator alphabet. -/
def contextWord (word : List NearyTile) : List (Option TagLetter) :=
  [some .b, none, none] ++ middleWord word ++ [some .b, none, none, some .b]

/-- The literal context word evaluates to the factored physical context. -/
theorem contextWord_product
    (β : Nat) (body : List TagLetter) (word : List NearyTile) :
    wordProduct (generator β body) (contextWord word) = physicalContext β body word := by
  rw [contextWord, wordProduct_append, wordProduct_append, middleWord_product]
  simp [generator, physicalContext, separatedGenerator, wordProduct, pow_two,
    Matrix.mul_assoc]

/-- The physical context factors through exactly the internal two-dimensional bridge. -/
theorem physicalContext_factor
    (β : Nat) (body : List TagLetter) (word : List NearyTile) :
    physicalContext β body word =
      ParabolicBlade.injection * bladeOutput β * bridge β (tileProduct β body word) *
        bladeInput * bFlank β := by
  have middle := physicalMiddle_mul_injection β body word
  have blade :
      bFlank β * root ^ 2 * ParabolicBlade.injection =
        bladeOutput β * bladeInput := by
    simpa [atom, dataFlank] using exceptional_factor β body
  rw [physicalContext]
  simp only [dataGenerator, dataFlank]
  calc
    ParabolicBlade.injection * bFlank β * root ^ 2 * physicalMiddle β body word *
          (ParabolicBlade.injection * bFlank β) * root ^ 2 *
          (ParabolicBlade.injection * bFlank β) =
        (ParabolicBlade.injection * bFlank β * root ^ 2) *
          (physicalMiddle β body word * ParabolicBlade.injection) *
          (bFlank β * root ^ 2 * ParabolicBlade.injection) * bFlank β := by
      simp only [Matrix.mul_assoc]
    _ = (ParabolicBlade.injection * bFlank β * root ^ 2) *
          (ParabolicBlade.injection * tileProduct β body word) *
          (bFlank β * root ^ 2 * ParabolicBlade.injection) * bFlank β := by
      rw [middle]
    _ =
        ParabolicBlade.injection * (bFlank β * root ^ 2 * ParabolicBlade.injection) *
          tileProduct β body word *
          (bFlank β * root ^ 2 * ParabolicBlade.injection) * bFlank β := by
      simp only [Matrix.mul_assoc]
    _ = ParabolicBlade.injection * bladeOutput β *
          bridge β (tileProduct β body word) * bladeInput * bFlank β := by
      rw [blade]
      simp only [bridge, Matrix.mul_assoc]

/-- Fixed right row of every physical context recognizing a terminal match. -/
def terminalRow (β : Nat) : Fin 4 → ℚ :=
  ![-1, (15 * (3 : ℚ) ^ β + 3) / 2, 28, 24]

private theorem physicalTile_preserves_first
    (β : Nat) (body : List TagLetter) (tile : NearyTile) (row : Fin 4 → ℚ) :
    (row ᵥ* physicalTile β body tile) 0 = row 0 := by
  cases tile with
  | erase letter =>
      cases letter <;>
        norm_num [physicalTile, tileGap, NearyTile.letter, dataGenerator, dataFlank,
          bFlank, cFlank, ParabolicBlade.injection, ParabolicBlade.flank, Matrix.vecMul,
          Matrix.dotProduct, Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ]
  | rule letter =>
      rw [physicalTile, tileGap, root_cube]
      cases letter <;>
        norm_num [NearyTile.letter, dataGenerator, dataFlank, bFlank, cFlank,
          ParabolicBlade.injection, ParabolicBlade.flank, ParabolicBlade.drift,
          Matrix.vecMul, Matrix.dotProduct, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Every continuation made only of complete Neary gaps preserves the first row coordinate. -/
theorem physicalMiddle_preserves_first
    (β : Nat) (body : List TagLetter) (word : List NearyTile) (row : Fin 4 → ℚ) :
    (row ᵥ* physicalMiddle β body word) 0 = row 0 := by
  induction word generalizing row with
  | nil => simp [physicalMiddle, wordProduct]
  | cons tile word induction =>
      rw [physicalMiddle, wordProduct_cons, ← Matrix.vecMul_vecMul]
      change ((row ᵥ* physicalTile β body tile) ᵥ*
        physicalMiddle β body word) 0 = row 0
      rw [induction, physicalTile_preserves_first]

/-- The fixed terminal row cannot be annihilated by a continuation of complete gaps. -/
theorem terminalRow_vecMul_physicalMiddle_ne_zero
    (β : Nat) (body : List TagLetter) (word : List NearyTile) :
    terminalRow β ᵥ* physicalMiddle β body word ≠ 0 := by
  intro product_zero
  have first_zero := congr_fun product_zero 0
  rw [physicalMiddle_preserves_first] at first_zero
  norm_num [terminalRow] at first_zero

/-- Projection retracting the common-image injection. -/
def injectionRetraction : Matrix (Fin 3) (Fin 4) ℚ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0]

private theorem injectionRetraction_mul_injection :
    injectionRetraction * ParabolicBlade.injection = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [injectionRetraction, ParabolicBlade.injection, Matrix.one_apply,
      Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals split <;> simp_all

/-- Retraction of the exceptional output factor. -/
def bladeRetraction (β : Nat) : Matrix (Fin 2) (Fin 3) ℚ :=
  let ρ : ℚ := 3 ^ β
  !![0, -1 / (9 * ρ), 0;
     0, -8 / (171 * ρ), 1 / 19]

private theorem bladeRetraction_mul_bladeOutput (β : Nat) :
    bladeRetraction β * bladeOutput β = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bladeRetraction, bladeOutput, Matrix.one_apply, Matrix.mul_apply,
      Fin.sum_univ_succ] ;
    field_simp ;
    ring

/-- Section of the exceptional input factor. -/
def bladeSection : Matrix (Fin 3) (Fin 2) ℚ :=
  !![1, 0;
     0, 0;
     0, 1]

private theorem bladeInput_mul_bladeSection : bladeInput * bladeSection = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bladeInput, bladeSection, Matrix.one_apply, Matrix.mul_apply,
      Fin.sum_univ_succ]

/-- Section of the terminal `b` flank. -/
def bFlankSection (β : Nat) : Matrix (Fin 4) (Fin 3) ℚ :=
  let ρ : ℚ := 3 ^ β
  !![1, -3 * (ρ - 1) / (18 * ρ), 0;
     0, 1 / (9 * ρ), 0;
     0, 0, 0;
     0, 0, 1 / 12]

private theorem bFlank_mul_bFlankSection (β : Nat) :
    bFlank β * bFlankSection β = 1 := by
  have scale_ne : (3 : ℚ) ^ β ≠ 0 := by positivity
  have scale_cancel :
      (9 : ℚ) * 3 ^ β * ((3 ^ β)⁻¹ * (1 / 9)) = 1 := by
    calc
      (9 : ℚ) * 3 ^ β * ((3 ^ β)⁻¹ * (1 / 9)) =
          (3 ^ β * (3 ^ β)⁻¹) * (9 * (1 / 9)) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ scale_ne]; norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bFlank, bFlankSection, ParabolicBlade.flank, Matrix.one_apply,
      Matrix.mul_apply, Fin.sum_univ_succ] ;
    field_simp [scale_ne] ;
    ring
  all_goals first | exact scale_cancel | (split <;> simp_all)

/-- Multiplying the physical context by fixed retractions recovers its bridge exactly. -/
theorem recover_bridge
    (β : Nat) (body : List TagLetter) (word : List NearyTile) :
    bladeRetraction β * injectionRetraction * physicalContext β body word *
          bFlankSection β * bladeSection =
      bridge β (tileProduct β body word) := by
  rw [physicalContext_factor]
  calc
    bladeRetraction β * injectionRetraction *
          (ParabolicBlade.injection * bladeOutput β *
            bridge β (tileProduct β body word) * bladeInput * bFlank β) *
          bFlankSection β * bladeSection =
        (bladeRetraction β *
            (injectionRetraction * ParabolicBlade.injection) * bladeOutput β) *
          bridge β (tileProduct β body word) *
          (bladeInput * (bFlank β * bFlankSection β) * bladeSection) := by
      simp only [Matrix.mul_assoc]
    _ = bridge β (tileProduct β body word) := by
      rw [injectionRetraction_mul_injection, bFlank_mul_bFlankSection]
      simp only [Matrix.mul_one, Matrix.one_mul]
      change (bladeRetraction β * bladeOutput β) *
          bridge β (tileProduct β body word) * (bladeInput * bladeSection) = _
      rw [bladeRetraction_mul_bladeOutput, bladeInput_mul_bladeSection]
      simp

/-- A recognized physical context never vanishes, including on a terminal match. -/
theorem physicalContext_ne_zero
    (β : Nat) (body : List TagLetter) (word : List NearyTile) :
    physicalContext β body word ≠ 0 := by
  intro context_zero
  have bridge_zero : bridge β (tileProduct β body word) = 0 := by
    rw [← recover_bridge β body word, context_zero]
    simp
  rw [tileProduct_eq_semanticMatrix] at bridge_zero
  exact bridge_semanticMatrix_ne_zero β _ _ bridge_zero

/-- A terminal physical context is a nonzero column times the fixed terminal row. -/
theorem physicalContext_outer_of_terminal_match
    (β : Nat) (body : List TagLetter) (word : List NearyTile)
    (terminal_match :
      spell (nearyUpper β) word ++ nearyMarker β = spell (nearyLower β body) word) :
    ∃ column : Fin 4 → ℚ, column ≠ 0 ∧
      physicalContext β body word = Matrix.vecMulVec column (terminalRow β) := by
  let upper := spell (nearyUpper β) word
  let middle := semanticMatrix upper (upper ++ nearyMarker β)
  let core := ParabolicBlade.injection * bladeOutput β * bridge β middle
  let column : Fin 4 → ℚ := fun i => core i 1 / 2
  have bridge_columns (i : Fin 2) :
      bridge β middle i 0 = -(1 / 2 : ℚ) * bridge β middle i 1 := by
    exact bridge_semanticMatrix_terminal_columns β upper i
  have core_columns (i : Fin 4) : core i 0 = -(1 / 2 : ℚ) * core i 1 := by
    simp only [core, Matrix.mul_apply, Fin.sum_univ_two]
    rw [bridge_columns 0, bridge_columns 1]
    ring
  have outer :
      physicalContext β body word = Matrix.vecMulVec column (terminalRow β) := by
    rw [physicalContext_factor, tileProduct_eq_semanticMatrix, ← terminal_match]
    change core * bladeInput * bFlank β = Matrix.vecMulVec column (terminalRow β)
    ext i j
    fin_cases j <;>
      norm_num [column, terminalRow, bladeInput, bFlank, ParabolicBlade.flank,
        Matrix.mul_apply, Matrix.vecMulVec, Fin.sum_univ_succ]
    all_goals try rw [core_columns i]
    all_goals
      ring
  refine ⟨column, ?_, outer⟩
  intro column_zero
  apply physicalContext_ne_zero β body word
  rw [outer, column_zero]
  ext i j
  simp [Matrix.vecMulVec]

/-- After a terminal match, right annihilation of the physical context is exactly annihilation
of the fixed terminal row. -/
theorem physicalContext_mul_eq_zero_iff_terminalRow
    (β : Nat) (body : List TagLetter) (word : List NearyTile)
    (terminal_match :
      spell (nearyUpper β) word ++ nearyMarker β = spell (nearyLower β body) word)
    (continuation : Matrix (Fin 4) (Fin 4) ℚ) :
    physicalContext β body word * continuation = 0 ↔
      terminalRow β ᵥ* continuation = 0 := by
  obtain ⟨column, column_ne, outer⟩ :=
    physicalContext_outer_of_terminal_match β body word terminal_match
  rw [outer, outer_mul]
  constructor
  · intro product_zero
    by_contra row_ne
    exact outer_ne_zero column_ne row_ne product_zero
  · intro row_zero
    rw [row_zero]
    ext i j
    simp [Matrix.vecMulVec]

/-- Fixed rows two and three and columns one and four of the physical context. -/
def physicalMinor (β : Nat) (body : List TagLetter) (word : List NearyTile) :
    Matrix (Fin 2) (Fin 2) ℚ :=
  let context := physicalContext β body word
  !![context 1 0, context 1 3;
     context 2 0, context 2 3]

/-- The fixed physical minor is a nonzero scalar multiple of the bridge determinant. -/
theorem physicalMinor_det
    (β : Nat) (body : List TagLetter) (word : List NearyTile) :
    (physicalMinor β body word).det =
      -2052 * (3 : ℚ) ^ β * (bridge β (tileProduct β body word)).det := by
  rw [physicalMinor, physicalContext_factor, Matrix.det_fin_two]
  norm_num [bladeOutput, bladeInput, bFlank, ParabolicBlade.injection,
    ParabolicBlade.flank, Matrix.mul_apply, Matrix.vecMul, Matrix.dotProduct,
    Matrix.det_fin_two, Fin.sum_univ_succ]
  ring

/-- The fixed physical minor vanishes exactly on the Neary terminal equation. -/
theorem physicalMinor_det_eq_zero_iff_terminal_match
    (β : Nat) (body : List TagLetter) (β_pos : 0 < β) (word : List NearyTile) :
    (physicalMinor β body word).det = 0 ↔
      spell (nearyUpper β) word ++ nearyMarker β =
        spell (nearyLower β body) word := by
  rw [physicalMinor_det]
  have scalar_ne : (-2052 : ℚ) * 3 ^ β ≠ 0 := by positivity
  rw [mul_eq_zero]
  simp only [scalar_ne, false_or]
  exact bridge_tileProduct_det_eq_zero_iff_terminal_match β body β_pos word

/-- On paired controls, the fixed physical minor recognizes exactly the paired coefficient. -/
theorem physicalMinor_decoded_det_eq_zero_iff_pairedCoefficient
    (β : Nat) (body : List TagLetter) (β_pos : 0 < β) (word : List PairedControl) :
    (physicalMinor β body (decodePairedWord word)).det = 0 ↔
      pairedCoefficient ℚ β body word = 0 := by
  rw [physicalMinor_det]
  have scalar_ne : (-2052 : ℚ) * 3 ^ β ≠ 0 := by positivity
  rw [mul_eq_zero]
  simp only [scalar_ne, false_or]
  exact bridge_decoded_det_eq_zero_iff_pairedCoefficient β body β_pos word

end ParabolicRetuned

end MatrixMortality
