import MatrixMortality.PairedMortality
import MatrixMortality.TwoStatePushout

/-!
# Exact obstructions at the three-generator four-state frontier

This file owns exact compiler obstructions left by the failed `M₄(3)` attack. Each theorem
states only the algebraic architecture it excludes.
-/

namespace MatrixMortality

open scoped Matrix

/-- Replace the paired toggle by one proposed fused generator. -/
def fusedPairedGenerator (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter)
    (fused : Matrix (Fin 4) (Fin 4) R) : Option TagLetter → Matrix (Fin 4) (Fin 4) R
  | none => fused
  | some letter => pairedDataMatrix R β body letter

/-- Exact left-context toggle behavior at even one data letter forces the proposed fusion to
retain the common nonzero anchor. -/
theorem exactLeftToggleFusion_fixes_anchor (R : Type*) [CommRing R]
    (β : Nat) (body : List TagLetter) (fused : Matrix (Fin 4) (Fin 4) R)
    (letter : TagLetter)
    (exact :
      fused * pairedDataMatrix R β body letter =
        pairedToggleMatrix R * pairedDataMatrix R β body letter) :
    fused *ᵥ pairedAnchor R = pairedAnchor R := by
  have applied := congrArg (fun matrix => matrix *ᵥ pairedAnchor R) exact
  change (fused * pairedDataMatrix R β body letter) *ᵥ pairedAnchor R =
    (pairedToggleMatrix R * pairedDataMatrix R β body letter) *ᵥ pairedAnchor R at applied
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at applied
  have data_fixed :
      pairedDataMatrix R β body letter *ᵥ pairedAnchor R = pairedAnchor R := by
    simpa [pairedGenerator] using
      pairedGenerator_mulVec_anchor R β body (.data letter)
  have toggle_fixed :
      pairedToggleMatrix R *ᵥ pairedAnchor R = pairedAnchor R := by
    simpa [pairedGenerator] using
      pairedGenerator_mulVec_anchor R β body .toggle
  simpa [data_fixed, toggle_fixed] using applied

/-- Exact left-context fusion is immortal. The traditional invertible two-plane argument is
unnecessary: the contextual identity already preserves the common first column. -/
theorem exactLeftToggleFusion_immortal (R : Type*) [CommRing R] [Nontrivial R]
    (β : Nat) (body : List TagLetter) (fused : Matrix (Fin 4) (Fin 4) R)
    (letter : TagLetter)
    (exact :
      fused * pairedDataMatrix R β body letter =
        pairedToggleMatrix R * pairedDataMatrix R β body letter) :
    ¬IsMortal (fusedPairedGenerator R β body fused) := by
  have fused_fixed := exactLeftToggleFusion_fixes_anchor R β body fused letter exact
  have fixed :
      ∀ label,
        fusedPairedGenerator R β body fused label *ᵥ pairedAnchor R = pairedAnchor R := by
    intro label
    cases label with
    | none => exact fused_fixed
    | some data =>
        simpa [fusedPairedGenerator, pairedGenerator] using
          pairedGenerator_mulVec_anchor R β body (.data data)
  have anchor_nonzero : pairedAnchor R ≠ 0 := by
    intro anchor_zero
    have entry := congr_fun anchor_zero 0
    simp [pairedAnchor] at entry
  rintro ⟨word, _, product_zero⟩
  exact wordProduct_ne_zero_of_fixed
    (fusedPairedGenerator R β body fused) (pairedAnchor R) fixed anchor_nonzero word
    product_zero

/-! ## Exact delimiter-pair obstruction -/

/-- Add one bordered coordinate to a square matrix. -/
def borderedMatrix {ι K : Type*} [Zero K] (core : Square ι K)
    (column row : ι → K) (corner : K) : Square (ι ⊕ Unit) K
  | .inl i, .inl j => core i j
  | .inl i, .inr _ => column i
  | .inr _, .inl j => row j
  | .inr _, .inr _ => corner

private theorem borderedMatrix_square_upper {ι K : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (core : Square ι K)
    (column row : ι → K) (corner : K)
    (i j : ι) :
    (borderedMatrix core column row corner ^ 2) (.inl i) (.inl j) =
      (core * core + Matrix.vecMulVec column row) i j := by
  simp [borderedMatrix, pow_two, Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.vecMulVec_apply]

private theorem zeroPad_mul_borderedMatrix_sq_mul_zeroPad_upper
    {ι K : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (left right core : Square ι K) (column row : ι → K) (corner : K)
    (i j : ι) :
    (zeroPad (κ := Unit) left * borderedMatrix core column row corner ^ 2 *
        zeroPad (κ := Unit) right) (.inl i) (.inl j) =
      (left * (core * core + Matrix.vecMulVec column row) * right) i j := by
  simp only [Matrix.mul_apply, zeroPad, Fintype.sum_sum_type, Finset.sum_const_zero,
    add_zero, zero_mul, mul_zero]
  apply Finset.sum_congr rfl
  intro middle _
  congr 1
  apply Finset.sum_congr rfl
  intro source _
  rw [borderedMatrix_square_upper]

/-- A family has trivial common kernel when no nonzero column is killed by every member. -/
def HasTrivialCommonKernel {α ι K : Type*} [Semiring K]
    [Fintype ι] (generators : α → Square ι K) : Prop :=
  ∀ vector, (∀ label, generators label *ᵥ vector = 0) → vector = 0

/-- If a bordered involution is required to make every delimiter pair contextually invisible,
the resulting family retains a nonzero column and is therefore immortal. -/
theorem exactDelimiterPair_immortal {α ι K : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Nonempty α]
    (generators : α → Square ι K) (toggle : Square ι K)
    (anchor column row : ι → K) (corner : K)
    (toggle_sq : toggle * toggle = 1)
    (toggle_fixed : toggle *ᵥ anchor = anchor)
    (data_fixed : ∀ label, generators label *ᵥ anchor = anchor)
    (anchor_nonzero : anchor ≠ 0)
    (commonKernel : HasTrivialCommonKernel generators)
    (pair_exact : ∀ left right,
      zeroPad (κ := Unit) (generators left) *
          borderedMatrix toggle column row corner ^ 2 *
          zeroPad (κ := Unit) (generators right) =
        zeroPad (generators left * generators right)) :
    ¬IsMortal (fun label : Option α =>
      match label with
      | none => borderedMatrix toggle column row corner
      | some data => zeroPad (κ := Unit) (generators data)) := by
  let fused : Option α → Square (ι ⊕ Unit) K := fun label =>
    match label with
    | none => borderedMatrix toggle column row corner
    | some data => zeroPad (κ := Unit) (generators data)
  let liftedAnchor : ι ⊕ Unit → K
    | .inl i => anchor i
    | .inr _ => 0
  have context_outer_zero (left right : α) :
      generators left * Matrix.vecMulVec column row * generators right = 0 := by
    have context :
        generators left *
              (toggle * toggle + Matrix.vecMulVec column row) *
              generators right =
            generators left * generators right := by
      ext i j
      have entry := congrFun (congrFun (pair_exact left right) (.inl i)) (.inl j)
      rw [zeroPad_mul_borderedMatrix_sq_mul_zeroPad_upper] at entry
      simpa [zeroPad] using entry
    rw [toggle_sq] at context
    have split :
        generators left * generators right +
              generators left * Matrix.vecMulVec column row * generators right =
            generators left * generators right := by
      simpa [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc] using context
    exact add_left_cancel (split.trans (add_zero _).symm)
  by_cases column_killed : ∀ label, generators label *ᵥ column = 0
  · have column_zero : column = 0 := commonKernel column column_killed
    have step (label : Option α) (vector : ι ⊕ Unit → K)
        (upper : ∀ i, vector (.inl i) = anchor i) :
        ∀ i, (fused label *ᵥ vector) (.inl i) = anchor i := by
      intro i
      cases label with
      | none =>
          simp only [fused, Matrix.mulVec, dotProduct, borderedMatrix,
            Fintype.sum_sum_type, column_zero, Pi.zero_apply, zero_mul,
            Finset.sum_const_zero, add_zero]
          calc
            ∑ j, toggle i j * vector (.inl j) =
                (toggle *ᵥ anchor) i := by
              apply Finset.sum_congr rfl
              intro j _
              rw [upper]
            _ = anchor i := congrFun toggle_fixed i
      | some data =>
          simp only [fused, Matrix.mulVec, dotProduct, zeroPad,
            Fintype.sum_sum_type, zero_mul, Finset.sum_const_zero, add_zero]
          calc
            ∑ j, generators data i j * vector (.inl j) =
                (generators data *ᵥ anchor) i := by
              apply Finset.sum_congr rfl
              intro j _
              rw [upper]
            _ = anchor i := congrFun (data_fixed data) i
    have product_upper (word : List (Option α)) :
        ∀ i, (wordProduct fused word *ᵥ liftedAnchor) (.inl i) = anchor i := by
      induction word with
      | nil => simp [liftedAnchor]
      | cons head tail induction =>
          rw [wordProduct_cons, ← Matrix.mulVec_mulVec]
          exact step head _ induction
    rintro ⟨word, _, product_zero⟩
    apply anchor_nonzero
    funext i
    have upper := product_upper word i
    rw [product_zero] at upper
    simpa using upper.symm
  · have column_alive : ∃ label, generators label *ᵥ column ≠ 0 :=
      not_forall.mp column_killed
    obtain ⟨left, left_alive⟩ := column_alive
    have row_killed (right : α) : row ᵥ* generators right = 0 := by
      have outer_zero :
          Matrix.vecMulVec (generators left *ᵥ column)
              (row ᵥ* generators right) = 0 := by
        simpa [mul_outer, outer_mul, Matrix.mul_assoc] using
          context_outer_zero left right
      by_contra right_alive
      exact outer_ne_zero left_alive right_alive outer_zero
    let pivot : α := Classical.choice inferInstance
    have row_anchor_zero : row ⬝ᵥ anchor = 0 := by
      calc
        row ⬝ᵥ anchor = row ⬝ᵥ generators pivot *ᵥ anchor := by
          rw [data_fixed]
        _ = (row ᵥ* generators pivot) ⬝ᵥ anchor := by
          rw [Matrix.dotProduct_mulVec]
        _ = 0 := by rw [row_killed]; simp
    have fused_fixed : ∀ label, fused label *ᵥ liftedAnchor = liftedAnchor := by
      intro label
      cases label with
      | none =>
          funext index
          cases index with
          | inl i =>
              simp only [fused, Matrix.mulVec, dotProduct, liftedAnchor,
                borderedMatrix, Fintype.sum_sum_type, mul_zero,
                Finset.sum_const_zero, add_zero]
              exact congrFun toggle_fixed i
          | inr extra =>
              cases extra
              simp only [fused, Matrix.mulVec, dotProduct, liftedAnchor,
                borderedMatrix, Fintype.sum_sum_type, mul_zero,
                Finset.sum_const_zero, add_zero]
              exact row_anchor_zero
      | some data =>
          funext index
          cases index with
          | inl i =>
              simpa [fused, liftedAnchor, zeroPad, Matrix.mulVec, dotProduct,
                Fintype.sum_sum_type] using congrFun (data_fixed data) i
          | inr extra =>
              cases extra
              simp [fused, liftedAnchor, zeroPad, Matrix.mulVec, dotProduct]
    have liftedAnchor_nonzero : liftedAnchor ≠ 0 := by
      intro lifted_zero
      apply anchor_nonzero
      funext i
      have entry := congrFun lifted_zero (.inl i)
      simpa [liftedAnchor] using entry
    rintro ⟨word, _, product_zero⟩
    exact wordProduct_ne_zero_of_fixed fused liftedAnchor fused_fixed
      liftedAnchor_nonzero word product_zero

end MatrixMortality
