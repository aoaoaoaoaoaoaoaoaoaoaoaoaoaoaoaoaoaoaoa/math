import MatrixMortality.LinearRepresentation

/-!
# Singular positive shifts need not saturate to inverses

Three explicit rank-two matrices have zero language `{t}` on the complete free monoid while a
positive `b`-shift collapses the distinct reachable states of `ε` and `t`.  Full reachability,
observability, and arbitrary-word correctness therefore do not imply the backward cancellativity
needed by an inverse-saturated projective action.
-/

namespace MatrixMortality

open scoped Matrix

namespace PositiveShiftCountermodel

/-- The three positive controls in the countermodel. -/
inductive Letter
  | b
  | c
  | t
  deriving DecidableEq

/-- The singular three-state action. -/
def generator (R : Type*) [Semiring R] : Letter → Square (Fin 3) R
  | .b =>
      !![0, 0, 1;
         0, 0, 0;
         1, 1, 1]
  | .c =>
      !![0, 0, 0;
         0, 0, 1;
         1, 1, 1]
  | .t =>
      !![0, 0, 0;
         1, 0, 0;
         0, 1, 1]

/-- Initial column. -/
def column (R : Type*) [Semiring R] : Fin 3 → R := ![1, 0, 0]

/-- Terminal row. -/
def row (R : Type*) [Semiring R] : Fin 3 → R := ![1, 0, 1]

/-- Exact natural-number orbit, evaluated from the right end of a word. -/
def state : List Letter → Fin 3 → Nat
  | [] => ![1, 0, 0]
  | .b :: word =>
      let tail := state word
      ![tail 2, 0, tail 0 + tail 1 + tail 2]
  | .c :: word =>
      let tail := state word
      ![0, tail 2, tail 0 + tail 1 + tail 2]
  | .t :: word =>
      let tail := state word
      ![0, tail 0, tail 1 + tail 2]

/-- Matrix multiplication realizes the natural-number orbit over every target semiring. -/
theorem wordProduct_mulVec_column (R : Type*) [Semiring R] (word : List Letter) :
    wordProduct (generator R) word *ᵥ column R = fun i => (state word i : R) := by
  induction word with
  | nil =>
      ext i
      fin_cases i <;> simp [wordProduct, column, state]
  | cons letter word induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec, induction]
      cases letter <;>
        ext i <;>
        fin_cases i <;>
        simp [generator, state, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ,
          add_assoc]

/-- Scalar coefficient of the countermodel. -/
def coefficient (R : Type*) [Semiring R] (word : List Letter) : R :=
  linearCoefficient (generator R) (row R) (column R) word

/-- The coefficient is the sum of the first and final orbit coordinates. -/
theorem coefficient_eq (R : Type*) [Semiring R] (word : List Letter) :
    coefficient R word = (state word 0 + state word 2 : Nat) := by
  rw [coefficient, linearCoefficient, wordProduct_mulVec_column]
  simp [row, Matrix.dotProduct, Fin.sum_univ_succ]

/-- Apart from `ε` and the sole accepting word `t`, every reachable state has positive final
coordinate. -/
theorem state_trichotomy (word : List Letter) :
    word = [] ∨ word = [.t] ∨ 0 < state word 2 := by
  induction word with
  | nil => simp
  | cons letter word induction =>
      rcases induction with (rfl | word_eq | positive)
      · cases letter <;> simp [state]
      · subst word
        cases letter <;> simp [state]
      · right
        right
        cases letter <;> simp [state] <;> omega

/-- The complete integral zero language is the singleton `{t}`. -/
theorem coefficient_int_eq_zero_iff (word : List Letter) :
    coefficient ℤ word = 0 ↔ word = [.t] := by
  constructor
  · intro zero
    rcases state_trichotomy word with (rfl | word_eq | positive)
    · norm_num [coefficient_eq, state] at zero
    · exact word_eq
    · exfalso
      rw [coefficient_eq] at zero
      have sum_positive : 0 < state word 0 + state word 2 :=
        Nat.add_pos_right _ positive
      have cast_positive : (0 : ℤ) < (state word 0 + state word 2 : Nat) := by
        exact_mod_cast sum_positive
      exact cast_positive.ne' zero
  · rintro rfl
    norm_num [coefficient_eq, state]

/-- No positive matrix word vanishes. -/
theorem wordProduct_int_ne_zero (word : List Letter) :
    wordProduct (generator ℤ) word ≠ 0 := by
  intro product_zero
  have scalar_zero : coefficient ℤ word = 0 := by
    simp [coefficient, linearCoefficient, product_zero]
  have word_eq := (coefficient_int_eq_zero_iff word).mp scalar_zero
  subst word
  have entry := congr_fun (congr_fun product_zero 1) 0
  norm_num [wordProduct, generator, Matrix.vecHead, Matrix.vecTail] at entry

/-! ## Exact rank-two certificates -/

/-- A two-column image factor for each generator. -/
def imageFactor (R : Type*) [Semiring R] : Letter → Matrix (Fin 3) (Fin 2) R
  | .b => !![0, 1; 0, 0; 1, 1]
  | .c => !![0, 0; 0, 1; 1, 1]
  | .t => !![0, 0; 1, 0; 0, 1]

/-- A two-row quotient factor for each generator. -/
def quotientFactor (R : Type*) [Semiring R] : Letter → Matrix (Fin 2) (Fin 3) R
  | .b => !![1, 1, 0; 0, 0, 1]
  | .c => !![1, 1, 0; 0, 0, 1]
  | .t => !![1, 0, 0; 0, 1, 1]

/-- Left inverses for the image factors. -/
def imageRetraction (K : Type*) [Field K] : Letter → Matrix (Fin 2) (Fin 3) K
  | .b => !![-1, 0, 1; 1, 0, 0]
  | .c => !![0, -1, 1; 0, 1, 0]
  | .t => !![0, 1, 0; 0, 0, 1]

/-- Right inverses for the quotient factors. -/
def quotientSection (R : Type*) [Semiring R] : Letter → Matrix (Fin 3) (Fin 2) R
  | .b => !![1, 0; 0, 0; 0, 1]
  | .c => !![1, 0; 0, 0; 0, 1]
  | .t => !![1, 0; 0, 1; 0, 0]

theorem generator_factor (R : Type*) [Semiring R] (letter : Letter) :
    generator R letter = imageFactor R letter * quotientFactor R letter := by
  cases letter <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [generator, imageFactor, quotientFactor, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.vecHead, Matrix.vecTail]

theorem imageRetraction_mul_imageFactor (K : Type*) [Field K] (letter : Letter) :
    imageRetraction K letter * imageFactor K letter = 1 := by
  cases letter <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [imageRetraction, imageFactor, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ]

theorem quotientFactor_mul_quotientSection (R : Type*) [Semiring R] (letter : Letter) :
    quotientFactor R letter * quotientSection R letter = 1 := by
  cases letter <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [quotientFactor, quotientSection, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail]

/-- All three positive generators have rank exactly two. -/
theorem generator_rank (K : Type*) [Field K] (letter : Letter) :
    (generator K letter).rank = 2 := by
  apply le_antisymm
  · rw [generator_factor]
    exact (Matrix.rank_mul_le_left (imageFactor K letter) (quotientFactor K letter)).trans
      (Matrix.rank_le_width (imageFactor K letter))
  · have split :
        imageRetraction K letter * generator K letter * quotientSection K letter = 1 := by
      rw [generator_factor, ← Matrix.mul_assoc, imageRetraction_mul_imageFactor]
      simp [quotientFactor_mul_quotientSection]
    have outerBound := Matrix.rank_mul_le_left
      (imageRetraction K letter * generator K letter) (quotientSection K letter)
    rw [split, Matrix.rank_one] at outerBound
    have innerBound := Matrix.rank_mul_le_right
      (imageRetraction K letter) (generator K letter)
    norm_num at outerBound ⊢
    exact outerBound.trans innerBound

/-! ## Full finite contexts and the failed cancellation law -/

/-- Suffixes selecting three independent reachable columns. -/
def reachableSuffix : Fin 3 → List Letter := ![[], [.t], [.b]]

/-- Prefixes selecting three independent observable rows. -/
def observablePrefix : Fin 3 → List Letter := ![[], [.t], [.c]]

/-- Selected reachable-column matrix. -/
def reachableMatrix : Square (Fin 3) ℚ :=
  finiteSuffixStates (generator ℚ) (column ℚ) reachableSuffix

/-- Selected observable-row matrix. -/
def observableMatrix : Square (Fin 3) ℚ :=
  finitePrefixStates (generator ℚ) (row ℚ) observablePrefix

theorem reachableMatrix_eq : reachableMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reachableMatrix, finiteSuffixStates, reachableSuffix, wordProduct, generator,
      column, Matrix.mulVec, Matrix.dotProduct, Matrix.one_apply, Fin.sum_univ_succ,
      Matrix.vecHead, Matrix.vecTail, Fin.ext_iff]

theorem observableMatrix_eq :
    observableMatrix = !![1, 0, 1; 0, 1, 1; 1, 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [observableMatrix, finitePrefixStates, observablePrefix, wordProduct, generator,
      row, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail]
  all_goals simp [Matrix.one_apply, Fin.ext_iff]

/-- The selected reachable columns span all three states. -/
theorem reachableMatrix_det : reachableMatrix.det = 1 := by
  rw [reachableMatrix_eq]
  simp

/-- The selected observable rows span the full dual space. -/
theorem observableMatrix_det : observableMatrix.det = -1 := by
  rw [observableMatrix_eq, Matrix.det_fin_three]
  norm_num

/-- A positive `b`-shift collapses the distinct columns reached by `ε` and `t`. -/
theorem column_b_eq_bt :
    wordProduct (generator ℚ) [.b] *ᵥ column ℚ =
      wordProduct (generator ℚ) [.b, .t] *ᵥ column ℚ := by
  rw [wordProduct_mulVec_column, wordProduct_mulVec_column]
  ext i
  fin_cases i <;> norm_num [state]

/-- The columns before the collapsed `b`-shift are distinct. -/
theorem column_nil_ne_t :
    wordProduct (generator ℚ) [] *ᵥ column ℚ ≠
      wordProduct (generator ℚ) [.t] *ᵥ column ℚ := by
  rw [wordProduct_mulVec_column, wordProduct_mulVec_column]
  intro equal
  have coordinate := congr_fun equal 0
  norm_num [state] at coordinate

/-- Common positive shifts, full finite contexts, and all-word correctness do not imply backward
cancellativity on the reachable orbit. -/
theorem not_backward_cancellative :
    ¬ ∀ left right : List Letter,
      generator ℚ .b *ᵥ (wordProduct (generator ℚ) left *ᵥ column ℚ) =
          generator ℚ .b *ᵥ (wordProduct (generator ℚ) right *ᵥ column ℚ) →
        wordProduct (generator ℚ) left *ᵥ column ℚ =
          wordProduct (generator ℚ) right *ᵥ column ℚ := by
  intro backward
  apply column_nil_ne_t
  apply backward [] [.t]
  simpa [wordProduct_cons, Matrix.mulVec_mulVec] using column_b_eq_bt

end PositiveShiftCountermodel

end MatrixMortality
