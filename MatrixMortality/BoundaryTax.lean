import MatrixMortality.LinearRepresentation

/-!
# The two-channel boundary tax

An exact diagonal two-channel bridge needs two coordinates beyond every nonsingular finite
Hankel witness of its active scalar series.  The proof is finite-dimensional: the inactive
column adds an independent state, while the inactive row confines all exposed columns to a
proper hyperplane.
-/

namespace MatrixMortality

open scoped Matrix

/-- Prepend one distinguished column to a rectangular matrix. -/
def prependColumn {ι ν K : Type*} (column : ι → K) (matrix : Matrix ι ν K) :
    Matrix ι (Option ν) K
  | state, none => column state
  | state, some index => matrix state index

theorem prependColumn_mulVec {ι ν K : Type*} [Field K] [Fintype ν]
    (column : ι → K) (matrix : Matrix ι ν K) (coefficients : Option ν → K) :
    prependColumn column matrix *ᵥ coefficients =
      coefficients none • column + matrix *ᵥ fun index => coefficients (some index) := by
  ext state
  simp [prependColumn, Matrix.mulVec, dotProduct, Fintype.sum_option, mul_comm]

/--
A nonsingular `ν × ν` section factored through `stateColumns`, together with a nonzero
distinguished column and a nonzero row annihilating all exposed columns, forces two additional
ambient coordinates.
-/
theorem twoChannelBoundaryTax
    {ν ι K : Type*} [Field K] [Fintype ν] [DecidableEq ν]
    [Fintype ι] [DecidableEq ι]
    (prefixRows : Matrix ν ι K) (stateColumns : Matrix ι ν K)
    (inactiveColumn inactiveRow : ι → K)
    (finiteHankelSection : Matrix ν ν K)
    (section_eq : prefixRows * stateColumns = finiteHankelSection)
    (section_det_ne_zero : finiteHankelSection.det ≠ 0)
    (prefix_annihilates : prefixRows *ᵥ inactiveColumn = 0)
    (row_annihilates_columns : inactiveRow ᵥ* stateColumns = 0)
    (row_annihilates_column : inactiveRow ⬝ᵥ inactiveColumn = 0)
    (column_ne_zero : inactiveColumn ≠ 0)
    (row_ne_zero : inactiveRow ≠ 0) :
    Fintype.card ν + 2 ≤ Fintype.card ι := by
  classical
  let augmented : Matrix ι (Option ν) K :=
    prependColumn inactiveColumn stateColumns
  have section_injective : Function.Injective finiteHankelSection.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      (finiteHankelSection.isUnit_iff_isUnit_det.mpr
        (isUnit_iff_ne_zero.mpr section_det_ne_zero))
  have augmented_injective : Function.Injective augmented.mulVec := by
    intro left right products_equal
    let leftTail : ν → K := fun index => left (some index)
    let rightTail : ν → K := fun index => right (some index)
    have left_projected :
        prefixRows *ᵥ (augmented *ᵥ left) =
          finiteHankelSection *ᵥ leftTail := by
      rw [prependColumn_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
        prefix_annihilates, smul_zero, zero_add, Matrix.mulVec_mulVec,
        section_eq]
    have right_projected :
        prefixRows *ᵥ (augmented *ᵥ right) =
          finiteHankelSection *ᵥ rightTail := by
      rw [prependColumn_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
        prefix_annihilates, smul_zero, zero_add, Matrix.mulVec_mulVec,
        section_eq]
    have tails_equal : leftTail = rightTail := by
      apply section_injective
      rw [← left_projected, ← right_projected, products_equal]
    have none_equal : left none = right none := by
      obtain ⟨state, state_nonzero⟩ := Function.ne_iff.mp column_ne_zero
      simp only [Pi.zero_apply] at state_nonzero
      have state_products := congrFun products_equal state
      rw [prependColumn_mulVec, prependColumn_mulVec] at state_products
      simp only [Pi.add_apply, Pi.smul_apply] at state_products
      change (fun index => left (some index)) =
        (fun index => right (some index)) at tails_equal
      rw [tails_equal] at state_products
      exact mul_right_cancel₀ state_nonzero (add_right_cancel state_products)
    funext index
    cases index with
    | none => exact none_equal
    | some index => exact congrFun tails_equal index
  have augmented_not_surjective : ¬Function.Surjective augmented.mulVec := by
    intro augmented_surjective
    obtain ⟨state, row_state_ne_zero⟩ := Function.ne_iff.mp row_ne_zero
    simp only [Pi.zero_apply] at row_state_ne_zero
    obtain ⟨coefficients, coefficients_image⟩ :=
      augmented_surjective (Pi.single state 1)
    have annihilated :
        inactiveRow ⬝ᵥ (augmented *ᵥ coefficients) = 0 := by
      rw [prependColumn_mulVec, dotProduct_add, dotProduct_smul,
        row_annihilates_column, Matrix.dotProduct_mulVec, row_annihilates_columns]
      simp
    rw [coefficients_image, dotProduct_single_one] at annihilated
    exact row_state_ne_zero annihilated
  have cardinal_le : Fintype.card (Option ν) ≤ Fintype.card ι := by
    simpa [Module.finrank_pi] using
      LinearMap.finrank_le_finrank_of_injective
        (f := augmented.mulVecLin) augmented_injective
  have cardinal_ne : Fintype.card (Option ν) ≠ Fintype.card ι := by
    intro cardinal_eq
    have finrank_eq :
        Module.finrank K (Option ν → K) =
          Module.finrank K (ι → K) := by
      simpa [Module.finrank_pi] using cardinal_eq
    exact augmented_not_surjective
      ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := augmented.mulVecLin) finrank_eq).mp augmented_injective)
  have cardinal_lt : Fintype.card (Option ν) < Fintype.card ι :=
    lt_of_le_of_ne cardinal_le cardinal_ne
  rw [Fintype.card_option] at cardinal_lt
  omega

/--
Finite-witness form of the exact diagonal two-channel theorem.  The three vanishing bridge
entries hold for every word; a nonsingular finite Hankel section of the surviving bottom-right
coefficient then costs two additional states.
-/
theorem exactDiagonalTwoChannel_card_lower_bound
    {α ν ι K : Type*} [Field K] [Fintype ν] [DecidableEq ν]
    [Fintype ι] [DecidableEq ι]
    (generators : α → Matrix ι ι K)
    (inactiveColumn activeColumn inactiveRow activeRow : ι → K)
    (prefixes suffixes : ν → List α)
    (inactive_column_zero :
      ∀ word, activeRow ⬝ᵥ wordProduct generators word *ᵥ inactiveColumn = 0)
    (inactive_row_active_zero :
      ∀ word, inactiveRow ⬝ᵥ wordProduct generators word *ᵥ activeColumn = 0)
    (inactive_diagonal_zero :
      ∀ word, inactiveRow ⬝ᵥ wordProduct generators word *ᵥ inactiveColumn = 0)
    (column_ne_zero : inactiveColumn ≠ 0)
    (row_ne_zero : inactiveRow ≠ 0)
    (section_det_ne_zero :
      (finiteHankel (linearCoefficient generators activeRow activeColumn)
        prefixes suffixes).det ≠ 0) :
    Fintype.card ν + 2 ≤ Fintype.card ι := by
  let prefixRows := finitePrefixStates generators activeRow prefixes
  let stateColumns := finiteSuffixStates generators activeColumn suffixes
  apply twoChannelBoundaryTax prefixRows stateColumns inactiveColumn inactiveRow
    (finiteHankel (linearCoefficient generators activeRow activeColumn)
      prefixes suffixes)
  · exact (finiteHankel_factor
      (linearCoefficient generators activeRow activeColumn)
      generators activeRow activeColumn prefixes suffixes fun _ => rfl).symm
  · exact section_det_ne_zero
  · ext index
    change (activeRow ᵥ* wordProduct generators (prefixes index)) ⬝ᵥ
      inactiveColumn = 0
    rw [← Matrix.dotProduct_mulVec]
    exact inactive_column_zero (prefixes index)
  · ext index
    exact inactive_row_active_zero (suffixes index)
  · simpa using inactive_diagonal_zero []
  · exact column_ne_zero
  · exact row_ne_zero

end MatrixMortality
