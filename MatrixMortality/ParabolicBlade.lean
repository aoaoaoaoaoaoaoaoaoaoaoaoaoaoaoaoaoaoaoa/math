import MatrixMortality.NearySideNormal
import MatrixMortality.PairedCompression
import MatrixMortality.RankOne

/-!
# Parabolic punctuation blade

The paired four-state scalar compiler needs one physical generator to act both as its phase
toggle and as rank-one punctuation.  A finite-order cube root cannot meet the closed Neary
boundary.  This file owns the surviving open root: its cube agrees with the toggle on every
data image, while its incomplete powers form an affine family with one singular atom.
-/

namespace MatrixMortality

open scoped Matrix

namespace ParabolicBlade

/-- The basis in which the paired data images share a three-dimensional hyperplane. -/
def basis : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 0, 0, 0;
     0, 0, 1, 1;
     0, 1, 0, 0;
     0, 0, 1, -1]

/-- Inverse of `basis`. -/
def basisInv : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 0, 0, 0;
     0, 0, 1, 0;
     0, 1 / 2, 0, 1 / 2;
     0, 1 / 2, 0, -1 / 2]

/-- The common three-plane injection in the blade basis. -/
def injection : Matrix (Fin 4) (Fin 3) ℚ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1;
     0, 0, -1]

/-- The paired toggle in the blade basis. -/
def normalToggle : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, -1]

/-- The unipotent drift accumulated by three open-root steps. -/
def drift (j : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 2 * j, 1]

/-- The parabolic open root in the blade basis.  The parameter `ρ` is the Neary width scale. -/
def normalRoot (ρ : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  let x := (114 * ρ - 11) / 96
  let y := -(38 * ρ - 11) / 32
  !![0, -1, 0, 0;
     1, -1, 0, 0;
     0, 0, 1, 0;
     x, y, 2 / 3, 1]

/-- The actual open root in the paired compiler's native basis. -/
def root (ρ : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  basis * normalRoot ρ * basisInv

/-- Generic paired data shape in native coordinates. -/
def data (l u e a m n : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, l, u, e;
     0, 0, 0, 0;
     0, 0, a, 0;
     0, m, 0, n]

/-- Three-dimensional output factor of a paired data matrix in the blade basis. -/
def flank (l u e a m n : ℚ) : Matrix (Fin 3) (Fin 4) ℚ :=
  !![1, u, e + l, l - e;
     0, a, 0, 0;
     0, 0, (m + n) / 2, (m - n) / 2]

theorem basisInv_mul_basis : basisInv * basis = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basisInv, basis, Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals
    split
    · rename_i equality
      have valueEquality := congrArg Fin.val equality
      norm_num at valueEquality
    · norm_num

theorem basis_mul_basisInv : basis * basisInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basisInv, basis, Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals
    split
    · rename_i equality
      have valueEquality := congrArg Fin.val equality
      norm_num at valueEquality
    · norm_num

private theorem basis_isUnit : IsUnit basis := by
  exact isUnit_iff_exists.mpr ⟨basisInv, basis_mul_basisInv, basisInv_mul_basis⟩

private theorem basisInv_isUnit : IsUnit basisInv := by
  exact isUnit_iff_exists.mpr ⟨basis, basisInv_mul_basis, basis_mul_basisInv⟩

/-- One open root cube is a nontrivial unipotent shear. -/
theorem normalRoot_cube (ρ : ℚ) : normalRoot ρ ^ 3 = drift 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [normalRoot, drift, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

/-- The open cube agrees with the paired phase toggle on the common data-image plane. -/
theorem normalRoot_cube_mul_injection (ρ : ℚ) :
    normalRoot ρ ^ 3 * injection = normalToggle * injection := by
  rw [normalRoot_cube]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [drift, normalToggle, injection, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Three open-root steps, conjugated back to the native paired basis. -/
def physicalDrift : Matrix (Fin 4) (Fin 4) ℚ := basis * drift 1 * basisInv

private theorem conjugate_mul (left right : Matrix (Fin 4) (Fin 4) ℚ) :
    (basis * left * basisInv) * (basis * right * basisInv) =
      basis * (left * right) * basisInv := by
  calc
    (basis * left * basisInv) * (basis * right * basisInv) =
        basis * left * (basisInv * basis) * right * basisInv := by
          simp only [Matrix.mul_assoc]
    _ = basis * (left * right) * basisInv := by
      rw [basisInv_mul_basis]
      simp only [Matrix.mul_assoc, mul_one, one_mul]

private theorem normalForm_mul (left right : Matrix (Fin 4) (Fin 4) ℚ) :
    basisInv * (left * right) * basis =
      (basisInv * left * basis) * (basisInv * right * basis) := by
  symm
  calc
    (basisInv * left * basis) * (basisInv * right * basis) =
        basisInv * left * (basis * basisInv) * right * basis := by
          simp only [Matrix.mul_assoc]
    _ = basisInv * (left * right) * basis := by
      rw [basis_mul_basisInv]
      simp only [Matrix.mul_assoc, mul_one, one_mul]

/-- The physical open root cubes to the fixed unipotent shear. -/
theorem root_cube (ρ : ℚ) : root ρ ^ 3 = physicalDrift := by
  rw [show root ρ ^ 3 = root ρ ^ 2 * root ρ by simp [pow_succ]]
  rw [show root ρ ^ 2 = basis * normalRoot ρ ^ 2 * basisInv by
      simp only [pow_two, root, conjugate_mul]]
  rw [root, conjugate_mul, ← pow_succ, normalRoot_cube]
  rfl

/-- Conjugating the physical root recovers its parabolic normal form. -/
theorem root_normal_form (ρ : ℚ) : basisInv * root ρ * basis = normalRoot ρ := by
  simp only [root, ← Matrix.mul_assoc]
  rw [basisInv_mul_basis]
  simp only [one_mul, Matrix.mul_assoc]
  rw [basisInv_mul_basis, mul_one]

/-- Every paired data matrix factors through the common three-plane in the blade basis. -/
theorem data_normal_form (l u e a m n : ℚ) :
    basisInv * data l u e a m n * basis = injection * flank l u e a m n := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basisInv, basis, data, injection, flank, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    ring

/-- The open root cube performs the exact physical toggle after any paired data letter. -/
theorem root_cube_mul_data (ρ l u e a m n : ℚ) :
    root ρ ^ 3 * data l u e a m n =
      pairedToggleMatrix ℚ * data l u e a m n := by
  rw [root_cube]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [physicalDrift, basis, basisInv, drift, data, pairedToggleMatrix_eq_explicit,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- The native paired generator is an instance of the blade's generic data shape. -/
theorem pairedDataMatrix_eq_data (β : Nat) (body : List TagLetter) (letter : TagLetter) :
    pairedDataMatrix ℚ β body letter =
      data
        (ternaryCode (nearyLower β body (.rule letter)))
        (ternaryCode (nearyUpper β (.rule letter)))
        (ternaryCode (nearyLower β body (.erase letter)))
        (3 ^ (nearyUpper β (.rule letter)).length)
        (3 ^ (nearyLower β body (.rule letter)).length)
        (3 ^ (nearyLower β body (.erase letter)).length) := by
  rw [pairedDataMatrix_eq_explicit]
  rfl

/-- The open root realizes the paired phase toggle on both native data images. -/
theorem root_cube_mul_pairedDataMatrix
    (β : Nat) (body : List TagLetter) (letter : TagLetter) :
    root ((3 : ℚ) ^ β) ^ 3 * pairedDataMatrix ℚ β body letter =
      pairedToggleMatrix ℚ * pairedDataMatrix ℚ β body letter := by
  rw [pairedDataMatrix_eq_data]
  exact root_cube_mul_data _ _ _ _ _ _ _

/-! ## Rank-one blade and affine gap atoms -/

/-- The native `b` data flank, with `ρ=3^β` left symbolic. -/
def bFlank (ρ : ℚ) : Matrix (Fin 3) (Fin 4) ℚ :=
  flank 25 ((15 * ρ + 1) / 2) 1 (9 * ρ) 27 3

/-- The body-dependent native `c` data flank. -/
def cFlank (L M : ℚ) : Matrix (Fin 3) (Fin 4) ℚ := flank L 2 1 3 M 3

/-- Native `b` data has the displayed blade-basis factorization. -/
theorem pairedDataMatrix_b_normal_form (β : Nat) (body : List TagLetter) :
    basisInv * pairedDataMatrix ℚ β body .b * basis =
      injection * bFlank ((3 : ℚ) ^ β) := by
  rw [pairedDataMatrix_eq_data, data_normal_form]
  congr 1
  change flank 25 (nearySideUpperB β) 1 (nearySideUpperBScale β) 27 3 =
    bFlank ((3 : ℚ) ^ β)
  rw [nearySideUpperB_eq, nearySideUpperBScale_eq]
  rfl

/-- Native `c` data has the displayed body-dependent blade-basis factorization. -/
theorem pairedDataMatrix_c_normal_form (β : Nat) (body : List TagLetter) :
    basisInv * pairedDataMatrix ℚ β body .c * basis =
      injection * cFlank (nearySideLowerC β body) (nearySideLowerCScale β body) := by
  rw [pairedDataMatrix_eq_data, data_normal_form]
  congr 1

/-- Reduced gap atom beginning with the native `b` data letter. -/
def bAtom (ρ : ℚ) (gap : Nat) : Matrix (Fin 3) (Fin 3) ℚ :=
  bFlank ρ * normalRoot ρ ^ gap * injection

/-- Reduced gap atom beginning with the native `c` data letter. -/
def cAtom (ρ L M : ℚ) (gap : Nat) : Matrix (Fin 3) (Fin 3) ℚ :=
  cFlank L M * normalRoot ρ ^ gap * injection

/-- Column ray of the parabolic rank-one blade. -/
def column (ρ : ℚ) : Fin 3 → ℚ :=
  ![18 * (144 * ρ + 35), 648 * ρ, 1026 * ρ + 385]

/-- Row ray of the parabolic rank-one blade. -/
def row (ρ : ℚ) : Fin 3 → ℚ := ![12 * ρ - 1, -3 * (4 * ρ - 1), 8]

private theorem column_ne_zero (ρ : ℚ) : column ρ ≠ 0 := by
  intro column_zero
  have second := congr_fun column_zero 1
  have third := congr_fun column_zero 2
  norm_num [column] at second third
  linarith

private theorem row_ne_zero (ρ : ℚ) : row ρ ≠ 0 := by
  intro row_zero
  have entry := congr_fun row_zero 2
  norm_num [row] at entry

/-- A fixed nonzero minor certifying that the exceptional atom has rank at least two. -/
def exceptionalMinor (ρ : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![bAtom ρ 1 1 0, bAtom ρ 1 1 2;
     bAtom ρ 1 2 0, bAtom ρ 1 2 2]

/-- The exceptional atom's decisive minor is `99ρ`. -/
theorem exceptionalMinor_det (ρ : ℚ) : (exceptionalMinor ρ).det = 99 * ρ := by
  rw [Matrix.det_fin_two]
  norm_num [exceptionalMinor, bAtom, bFlank, flank, normalRoot, injection, pow_succ,
    Matrix.mul_apply, Fin.sum_univ_succ]
  ring

/-- The exceptional atom has a nonzero rank-two minor at every Neary width. -/
theorem exceptionalMinor_det_ne_zero (β : Nat) :
    (exceptionalMinor ((3 : ℚ) ^ β)).det ≠ 0 := by
  rw [exceptionalMinor_det]
  positivity

private def coreOutput (ρ : ℚ) : Matrix (Fin 3) (Fin 2) ℚ :=
  !![36 * ρ - 9 / 4, 18;
     9 * ρ, 0;
     57 * ρ / 4 - 11 / 8, 11]

private def coreInput : Matrix (Fin 2) (Fin 3) ℚ :=
  !![1, -1, 0;
     0, 1 / 4, 1]

private def coreLeftInverse (ρ : ℚ) : Matrix (Fin 2) (Fin 3) ℚ :=
  !![0, 1 / (9 * ρ), 0;
     0, -(57 * ρ / 4 - 11 / 8) / (99 * ρ), 1 / 11]

private def coreRightInverse : Matrix (Fin 3) (Fin 2) ℚ :=
  !![1, 0;
     0, 0;
     0, 1]

private theorem bAtom_one_factor (ρ : ℚ) :
    bAtom ρ 1 = coreOutput ρ * coreInput := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bAtom, bFlank, flank, normalRoot, injection, coreOutput, coreInput,
      pow_succ, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

private theorem coreLeftInverse_mul_coreOutput (ρ : ℚ) (ρ_ne : ρ ≠ 0) :
    coreLeftInverse ρ * coreOutput ρ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coreLeftInverse, coreOutput, Matrix.one_apply, Matrix.mul_apply,
      Fin.sum_univ_succ]
  all_goals field_simp [ρ_ne]
  all_goals ring

private theorem coreInput_mul_coreRightInverse :
    coreInput * coreRightInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coreInput, coreRightInverse, Matrix.one_apply, Matrix.mul_apply,
      Fin.sum_univ_succ]

private theorem core_sandwich (ρ : ℚ) (ρ_ne : ρ ≠ 0) :
    coreLeftInverse ρ * bAtom ρ 1 * coreRightInverse = 1 := by
  calc
    coreLeftInverse ρ * bAtom ρ 1 * coreRightInverse =
        coreLeftInverse ρ * (coreOutput ρ * coreInput) * coreRightInverse := by
      rw [bAtom_one_factor]
    _ = (coreLeftInverse ρ * coreOutput ρ) *
        (coreInput * coreRightInverse) := by simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [coreLeftInverse_mul_coreOutput ρ ρ_ne, coreInput_mul_coreRightInverse]
      exact one_mul 1

/-- The two-dimensional transfer induced between successive exceptional atoms. -/
def bridge (ρ : ℚ) (middle : Matrix (Fin 3) (Fin 3) ℚ) :
    Matrix (Fin 2) (Fin 2) ℚ :=
  coreInput * middle * coreOutput ρ

/-- Bridge singularity is the first coordinate of the complete adjugate exterior state. -/
theorem bridge_det_eq_adjugate_first (ρ : ℚ)
    (middle : Matrix (Fin 3) (Fin 3) ℚ) :
    (bridge ρ middle).det = (9 * ρ / 2) *
      (-(middle.adjugateᵀ *ᵥ ![(22 : ℚ), -31, -36]) 0 -
        (middle.adjugateᵀ *ᵥ ![(22 : ℚ), -31, -36]) 1 +
          (middle.adjugateᵀ *ᵥ ![(22 : ℚ), -31, -36]) 2 / 4) := by
  rw [Matrix.det_fin_two]
  norm_num [bridge, coreInput, coreOutput, Matrix.adjugate_fin_three,
    Matrix.transpose_apply, Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul,
    Matrix.dotProduct, Fin.sum_univ_succ]
  ring

/-- A chain of exceptional atoms separated by arbitrary three-dimensional matrices. -/
def exceptionalChain (ρ : ℚ) : List (Matrix (Fin 3) (Fin 3) ℚ) →
    Matrix (Fin 3) (Fin 3) ℚ
  | [] => bAtom ρ 1
  | middle :: tail => bAtom ρ 1 * middle * exceptionalChain ρ tail

private theorem exceptionalChain_factor
    (ρ : ℚ) (middles : List (Matrix (Fin 3) (Fin 3) ℚ)) :
    exceptionalChain ρ middles =
      coreOutput ρ * wordProduct (bridge ρ) middles * coreInput := by
  induction middles with
  | nil => simp [exceptionalChain, bAtom_one_factor]
  | cons middle tail induction =>
      rw [exceptionalChain, wordProduct_cons, induction, bAtom_one_factor]
      simp only [bridge, Matrix.mul_assoc]

private theorem core_factor_eq_zero_iff
    (ρ : ℚ) (ρ_ne : ρ ≠ 0) (middle : Matrix (Fin 2) (Fin 2) ℚ) :
    coreOutput ρ * middle * coreInput = 0 ↔ middle = 0 := by
  constructor
  · intro factor_zero
    calc
      middle = (coreLeftInverse ρ * coreOutput ρ) * middle *
          (coreInput * coreRightInverse) := by
        rw [coreLeftInverse_mul_coreOutput ρ ρ_ne, coreInput_mul_coreRightInverse]
        simp
      _ = coreLeftInverse ρ * (coreOutput ρ * middle * coreInput) *
          coreRightInverse := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [factor_zero]; simp
  · rintro rfl
    simp

/-- Mortality of any exceptional-atom chain is exactly mortality of its `2 × 2` bridge word. -/
theorem exceptionalChain_eq_zero_iff
    (ρ : ℚ) (ρ_ne : ρ ≠ 0) (middles : List (Matrix (Fin 3) (Fin 3) ℚ)) :
    exceptionalChain ρ middles = 0 ↔ wordProduct (bridge ρ) middles = 0 := by
  rw [exceptionalChain_factor]
  exact core_factor_eq_zero_iff ρ ρ_ne _

/-- The unique singular atom has rank exactly two. -/
theorem bAtom_one_rank (β : Nat) : (bAtom ((3 : ℚ) ^ β) 1).rank = 2 := by
  let ρ : ℚ := 3 ^ β
  have ρ_ne : ρ ≠ 0 := by dsimp [ρ]; positivity
  apply le_antisymm
  · rw [bAtom_one_factor]
    exact (Matrix.rank_mul_le_left (coreOutput ρ) coreInput).trans
      (Matrix.rank_le_width (coreOutput ρ))
  · have sandwich := core_sandwich ρ ρ_ne
    rw [Matrix.mul_assoc] at sandwich
    have first := Matrix.rank_mul_le_right
      (coreLeftInverse ρ) (bAtom ρ 1 * coreRightInverse)
    have second := Matrix.rank_mul_le_left (bAtom ρ 1) coreRightInverse
    rw [sandwich, Matrix.rank_one] at first
    norm_num at first
    change 2 ≤ (bAtom ρ 1).rank
    exact first.trans second

/-- Two exceptional atoms form the explicit rank-one punctuation blade. -/
theorem bAtom_one_sq (ρ : ℚ) :
    bAtom ρ 1 ^ 2 = (1 / 32 : ℚ) • Matrix.vecMulVec (column ρ) (row ρ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bAtom, bFlank, flank, normalRoot, injection, column, row, pow_succ,
      Matrix.mul_apply, Matrix.vecMulVec_apply, Fin.sum_univ_succ] <;>
    ring

/-- The blade column is an eigenray of the exceptional atom. -/
theorem bAtom_one_mulVec_column (ρ : ℚ) :
    bAtom ρ 1 *ᵥ column ρ = ((108 * ρ + 35) / 4) • column ρ := by
  funext i
  fin_cases i <;>
    norm_num [bAtom, bFlank, flank, normalRoot, injection, column, pow_succ,
      Matrix.mul_apply, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ] <;>
    ring

/-- The blade row is a left eigenray of the exceptional atom. -/
theorem row_vecMul_bAtom_one (ρ : ℚ) :
    row ρ ᵥ* bAtom ρ 1 = ((108 * ρ + 35) / 4) • row ρ := by
  funext i
  fin_cases i <;>
    norm_num [bAtom, bFlank, flank, normalRoot, injection, row, pow_succ,
      Matrix.mul_apply, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_succ] <;>
    ring

/-- The physical mixed word that realizes the parabolic blade. -/
def physicalBlade (β : Nat) (body : List TagLetter) : Matrix (Fin 4) (Fin 4) ℚ :=
  let G := pairedDataMatrix ℚ β body .b
  let S := root ((3 : ℚ) ^ β)
  G * S * G * S * G

/-- In blade coordinates, the physical mixed word is the square of the exceptional atom. -/
theorem physicalBlade_normal_form (β : Nat) (body : List TagLetter) :
    basisInv * physicalBlade β body * basis =
      injection * bAtom ((3 : ℚ) ^ β) 1 ^ 2 * bFlank ((3 : ℚ) ^ β) := by
  simp only [physicalBlade, normalForm_mul, pairedDataMatrix_b_normal_form, root_normal_form]
  simp only [bAtom, pow_one, pow_two, Matrix.mul_assoc]

/-- The physical blade is an explicit nonzero column-row outer product after conjugation. -/
theorem physicalBlade_outer (β : Nat) (body : List TagLetter) :
    basisInv * physicalBlade β body * basis =
      (1 / 32 : ℚ) • Matrix.vecMulVec
        (injection *ᵥ column ((3 : ℚ) ^ β))
        (row ((3 : ℚ) ^ β) ᵥ* bFlank ((3 : ℚ) ^ β)) := by
  rw [physicalBlade_normal_form, bAtom_one_sq]
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [mul_outer, outer_mul]

private theorem injected_column_ne_zero (β : Nat) :
    injection *ᵥ column ((3 : ℚ) ^ β) ≠ 0 := by
  intro product_zero
  have entry := congr_fun product_zero 1
  apply (show (648 : ℚ) * 3 ^ β ≠ 0 by positivity)
  simp [injection, column, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ] at entry

private theorem flanked_row_ne_zero (β : Nat) :
    row ((3 : ℚ) ^ β) ᵥ* bFlank ((3 : ℚ) ^ β) ≠ 0 := by
  intro product_zero
  have entry := congr_fun product_zero 0
  have scale_one : (1 : ℚ) ≤ 3 ^ β := one_le_pow_of_one_le (by norm_num) _
  apply (show (12 : ℚ) * 3 ^ β - 1 ≠ 0 by nlinarith)
  simp [row, bFlank, flank, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_succ] at entry
  exact entry

/-- The physical parabolic blade is nonzero. -/
theorem physicalBlade_ne_zero (β : Nat) (body : List TagLetter) :
    physicalBlade β body ≠ 0 := by
  intro blade_zero
  have conjugate_zero : basisInv * physicalBlade β body * basis = 0 := by
    rw [blade_zero]
    simp
  rw [physicalBlade_outer] at conjugate_zero
  have outer_zero :
      Matrix.vecMulVec
          (injection *ᵥ column ((3 : ℚ) ^ β))
          (row ((3 : ℚ) ^ β) ᵥ* bFlank ((3 : ℚ) ^ β)) = 0 :=
    (smul_eq_zero.mp conjugate_zero).resolve_left (by norm_num)
  exact outer_ne_zero (injected_column_ne_zero β) (flanked_row_ne_zero β) outer_zero

private theorem drift_mul (j k : ℚ) : drift j * drift k = drift (j + k) := by
  ext i l
  fin_cases i <;> fin_cases l <;>
    norm_num [drift, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

private theorem drift_zero : drift 0 = 1 := by
  ext i l
  fin_cases i <;> fin_cases l <;>
    norm_num [drift, Matrix.one_apply]
  all_goals
    split
    · rename_i equality
      have valueEquality := congrArg Fin.val equality
      norm_num at valueEquality
    · norm_num

private theorem drift_isUnit (j : ℚ) : IsUnit (drift j) := by
  apply isUnit_iff_exists.mpr
  refine ⟨drift (-j), ?_, ?_⟩
  · rw [drift_mul]
    convert drift_zero using 1
    ring_nf
  · rw [drift_mul]
    convert drift_zero using 1
    ring_nf

/-- Every incomplete or complete power of the physical open root is invertible. -/
theorem root_isUnit (ρ : ℚ) : IsUnit (root ρ) := by
  apply (isUnit_pow_iff (by norm_num : 3 ≠ 0)).mp
  rw [root_cube, physicalDrift]
  exact (basis_isUnit.mul (drift_isUnit 1)).mul basisInv_isUnit

/-- Every complete triple of open-root steps contributes one unipotent drift. -/
theorem normalRoot_pow_three_mul (ρ : ℚ) (j : Nat) :
    normalRoot ρ ^ (3 * j) = drift j := by
  induction j with
  | zero => exact drift_zero.symm
  | succ j induction =>
      rw [Nat.mul_succ, pow_add, induction, normalRoot_cube, drift_mul]
      norm_num

private theorem normalRoot_pow_three_mul_add_one (ρ : ℚ) (j : Nat) :
    normalRoot ρ ^ (3 * j + 1) = drift j * normalRoot ρ := by
  rw [pow_add, normalRoot_pow_three_mul]
  simp

private theorem normalRoot_pow_three_mul_add_two (ρ : ℚ) (j : Nat) :
    normalRoot ρ ^ (3 * j + 2) = drift j * normalRoot ρ ^ 2 := by
  rw [pow_add, normalRoot_pow_three_mul]

/-- Determinant of every residue-zero `b` gap atom. -/
theorem bAtom_det_three_mul (ρ : ℚ) (j : Nat) :
    (bAtom ρ (3 * j)).det = 27 * ρ * (8 * j + 1) := by
  rw [bAtom, normalRoot_pow_three_mul, Matrix.det_fin_three]
  norm_num [bFlank, flank, drift, injection, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

/-- Determinant of every residue-one `b` gap atom. -/
theorem bAtom_det_three_mul_add_one (ρ : ℚ) (j : Nat) :
    (bAtom ρ (3 * j + 1)).det = 216 * j * ρ := by
  rw [bAtom, normalRoot_pow_three_mul_add_one, Matrix.det_fin_three]
  norm_num [bFlank, flank, drift, normalRoot, injection, Matrix.mul_apply,
    Fin.sum_univ_succ]
  ring

/-- Determinant of every residue-two `b` gap atom. -/
theorem bAtom_det_three_mul_add_two (ρ : ℚ) (j : Nat) :
    (bAtom ρ (3 * j + 2)).det = (9 * ρ / 2) * (48 * j - 114 * ρ + 49) := by
  rw [bAtom, normalRoot_pow_three_mul_add_two, Matrix.det_fin_three]
  norm_num [bFlank, flank, drift, normalRoot, injection, pow_succ, Matrix.mul_apply,
    Fin.sum_univ_succ]
  ring

/-- Determinant of every residue-zero `c` gap atom. -/
theorem cAtom_det_three_mul (ρ L M : ℚ) (j : Nat) :
    (cAtom ρ L M (3 * j)).det = 3 * ((M - 3) * j + 3) := by
  rw [cAtom, normalRoot_pow_three_mul, Matrix.det_fin_three]
  norm_num [cFlank, flank, drift, injection, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

/-- Determinant of every residue-one `c` gap atom. -/
theorem cAtom_det_three_mul_add_one (ρ L M : ℚ) (j : Nat) :
    (cAtom ρ L M (3 * j + 1)).det =
      (3 / 16 : ℚ) * (16 * j * (M - 3) + 9 * M - 11 * L + 32) := by
  rw [cAtom, normalRoot_pow_three_mul_add_one, Matrix.det_fin_three]
  norm_num [cFlank, flank, drift, normalRoot, injection, Matrix.mul_apply,
    Fin.sum_univ_succ]
  ring

/-- Determinant of every residue-two `c` gap atom. -/
theorem cAtom_det_three_mul_add_two (ρ L M : ℚ) (j : Nat) :
    (cAtom ρ L M (3 * j + 2)).det =
      (1 / 32 : ℚ) *
        (96 * j * (M - 3) - (342 * ρ - 33) * L +
          (114 * ρ + 53) * M + 96) := by
  rw [cAtom, normalRoot_pow_three_mul_add_two, Matrix.det_fin_three]
  norm_num [cFlank, flank, drift, normalRoot, injection, pow_succ, Matrix.mul_apply,
    Fin.sum_univ_succ]
  ring

/-- Residue-zero native `b` atoms are invertible at every Neary width. -/
theorem bAtom_det_three_mul_ne_zero (β j : Nat) :
    (bAtom ((3 : ℚ) ^ β) (3 * j)).det ≠ 0 := by
  rw [bAtom_det_three_mul]
  positivity

/-- A residue-one native `b` atom is singular exactly at the first open step. -/
theorem bAtom_det_three_mul_add_one_eq_zero_iff (β j : Nat) :
    (bAtom ((3 : ℚ) ^ β) (3 * j + 1)).det = 0 ↔ j = 0 := by
  rw [bAtom_det_three_mul_add_one]
  simp

/-- The parity defect excludes every residue-two native `b` singularity. -/
theorem bAtom_det_three_mul_add_two_ne_zero (β j : Nat) :
    (bAtom ((3 : ℚ) ^ β) (3 * j + 2)).det ≠ 0 := by
  rw [bAtom_det_three_mul_add_two]
  apply mul_ne_zero
  · positivity
  · intro factor_zero
    have rationalEquality : (48 : ℚ) * j + 49 = 114 * 3 ^ β := by
      linarith
    have naturalEquality : 48 * j + 49 = 114 * 3 ^ β := by
      exact_mod_cast rationalEquality
    omega

private theorem ternaryScale_le_two_mul_code_add_one (word : List Bool) :
    3 ^ word.length ≤ 2 * ternaryCode word + 1 := by
  induction word with
  | nil => simp [ternaryCode]
  | cons bit word induction =>
      rw [ternaryCode_cons]
      simp only [List.length_cons, pow_succ]
      cases bit <;> simp [ternaryDigit] <;> omega

private theorem two_true_ternary_bound (tail : List Bool) :
    17 * 3 ^ (tail.length + 2) ≤ 18 * ternaryCode (true :: true :: tail) + 9 := by
  rw [ternaryCode_cons, ternaryCode_cons]
  simp only [List.length_cons, ternaryDigit, pow_succ]
  have tailBound := ternaryScale_le_two_mul_code_add_one tail
  omega

private theorem neary_rule_c_starts_two_true
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ []) :
    ∃ tail, nearyLower β body (.rule .c) = true :: true :: tail := by
  cases body with
  | nil => exact False.elim (body_nonempty rfl)
  | cons letter body =>
      cases letter with
      | b =>
          refine ⟨List.replicate β false ++ [true] ++ tagEncode β body ++ [true, false], ?_⟩
          simp [nearyLower, tagEncode_cons, tagCode]
      | c =>
          refine ⟨tagEncode β body ++ [true, false], ?_⟩
          simp [nearyLower, tagEncode_cons, tagCode]

private theorem neary_rule_c_scale_lower_bound
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ []) :
    17 * nearySideLowerCScale β body ≤ 18 * nearySideLowerC β body + 9 := by
  obtain ⟨tail, shape⟩ := neary_rule_c_starts_two_true β body body_nonempty
  have bound :
      17 * 3 ^ (nearyLower β body (.rule .c)).length ≤
        18 * ternaryCode (nearyLower β body (.rule .c)) + 9 := by
    simpa [shape] using two_true_ternary_bound tail
  simp only [nearySideLowerCScale, nearySideLowerC]
  exact_mod_cast bound

private theorem neary_rule_c_scale_gt_twenty_seven
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ []) :
    (27 : ℚ) < nearySideLowerCScale β body := by
  have encoded_nonempty : tagEncode β body ≠ [] :=
    (tagEncode_eq_nil_iff β body).not.mpr body_nonempty
  have four_le : 4 ≤ (nearyLower β body (.rule .c)).length := by
    simp only [nearyLower, List.length_append, List.length_cons, List.length_nil]
    have encoded_length := List.length_pos.mpr encoded_nonempty
    omega
  have power_lt : 27 < 3 ^ (nearyLower β body (.rule .c)).length := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 3) four_le
    norm_num at this ⊢
    omega
  simp only [nearySideLowerCScale]
  exact_mod_cast power_lt

private theorem neary_rule_c_code_lt_scale (β : Nat) (body : List TagLetter) :
    nearySideLowerC β body < nearySideLowerCScale β body := by
  simp only [nearySideLowerC, nearySideLowerCScale]
  exact_mod_cast ternaryCode_lt_pow_length (nearyLower β body (.rule .c))

/-- The actual nonempty Neary code keeps every residue-one `c` determinant pencil off zero. -/
theorem neary_rule_c_residue_one_bounds
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ []) :
    let L := nearySideLowerC β body
    let M := nearySideLowerCScale β body
    0 < 11 * L - 9 * M - 32 ∧ 11 * L - 9 * M - 32 < 16 * (M - 3) := by
  dsimp
  have lower := neary_rule_c_scale_lower_bound β body body_nonempty
  have scaleLarge := neary_rule_c_scale_gt_twenty_seven β body body_nonempty
  have upper := neary_rule_c_code_lt_scale β body
  constructor <;> nlinarith

/-- Residue-zero native `c` atoms are invertible. -/
theorem cAtom_det_three_mul_ne_zero (β : Nat) (body : List TagLetter) (j : Nat) :
    (cAtom ((3 : ℚ) ^ β) (nearySideLowerC β body)
        (nearySideLowerCScale β body) (3 * j)).det ≠ 0 := by
  rw [cAtom_det_three_mul]
  have scaleLarge : (3 : ℚ) < nearySideLowerCScale β body := by
    rw [nearySideLowerCScale_eq_nine_mul, pow_succ]
    have encodedScaleOne : (1 : ℚ) ≤ 3 ^ (tagEncode β body).length :=
      one_le_pow_of_one_le (by norm_num) _
    nlinarith
  have gapNonnegative : 0 ≤ nearySideLowerCScale β body - 3 := by linarith
  have indexNonnegative : (0 : ℚ) ≤ j := by positivity
  have determinantPositive :
      0 < 3 * ((nearySideLowerCScale β body - 3) * (j : ℚ) + 3) := by
    nlinarith [mul_nonneg gapNonnegative indexNonnegative]
  exact ne_of_gt determinantPositive

/-- Residue-one native `c` atoms are invertible for every nonempty universal body. -/
theorem cAtom_det_three_mul_add_one_ne_zero
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ []) (j : Nat) :
    (cAtom ((3 : ℚ) ^ β) (nearySideLowerC β body)
        (nearySideLowerCScale β body) (3 * j + 1)).det ≠ 0 := by
  rw [cAtom_det_three_mul_add_one]
  apply mul_ne_zero (by norm_num)
  obtain ⟨defectPositive, defectSmall⟩ :=
    neary_rule_c_residue_one_bounds β body body_nonempty
  cases j with
  | zero => norm_num; linarith
  | succ j =>
      have scalePositive : 0 < nearySideLowerCScale β body - 3 := by
        have := neary_rule_c_scale_gt_twenty_seven β body body_nonempty
        linarith
      have productBound :
          16 * (nearySideLowerCScale β body - 3) ≤
            16 * (j + 1 : ℚ) * (nearySideLowerCScale β body - 3) := by
        gcongr
        norm_num
      push_cast
      nlinarith

/-- Residue-two native `c` atoms are excluded by the terminal `10` congruence. -/
theorem cAtom_det_three_mul_add_two_ne_zero
    (β : Nat) (body : List TagLetter) (j : Nat) :
    (cAtom ((3 : ℚ) ^ β) (nearySideLowerC β body)
        (nearySideLowerCScale β body) (3 * j + 2)).det ≠ 0 := by
  rw [cAtom_det_three_mul_add_two]
  apply mul_ne_zero (by norm_num)
  intro numeratorZero
  let P : ℚ := 3 ^ (tagEncode β body).length
  let V : ℚ := ternaryCode (tagEncode β body)
  have lowerCode : nearySideLowerC β body = 18 * P + 9 * V + 7 := by
    rw [nearySideLowerC_eq_nine_mul_add_seven, ternaryCode_cons]
    simp only [ternaryDigit]
    dsimp [P, V]
    push_cast
    ring
  have lowerScale : nearySideLowerCScale β body = 27 * P := by
    rw [nearySideLowerCScale_eq_nine_mul, pow_succ]
    dsimp [P]
    ring
  rw [lowerCode, lowerScale] at numeratorZero
  have reducedEquality :
      96 * (j : ℚ) * (9 * P - 1) =
        1026 * 3 ^ β * P - 675 * P + 1026 * 3 ^ β * V - 99 * V +
          798 * 3 ^ β - 109 := by
    linear_combination numeratorZero / 3
  have integerEquality :
      (96 : ℤ) * j * (9 * (3 : ℤ) ^ (tagEncode β body).length - 1) =
        1026 * 3 ^ β * 3 ^ (tagEncode β body).length -
          675 * 3 ^ (tagEncode β body).length +
          1026 * 3 ^ β * ternaryCode (tagEncode β body) -
          99 * ternaryCode (tagEncode β body) + 798 * 3 ^ β - 109 := by
    dsimp [P, V] at reducedEquality
    exact_mod_cast reducedEquality
  have residueEquality := congrArg (fun value : ℤ => value % 3) integerEquality
  norm_num [Int.add_emod, Int.sub_emod, Int.mul_emod] at residueEquality

/-- The complete reduced atom family of the parabolic three-generator candidate. -/
def atom (β : Nat) (body : List TagLetter) (letter : TagLetter) (gap : Nat) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  match letter with
  | .b => bAtom ((3 : ℚ) ^ β) gap
  | .c =>
      cAtom ((3 : ℚ) ^ β) (nearySideLowerC β body)
        (nearySideLowerCScale β body) gap

private theorem gap_mod_three_cases (gap : Nat) :
    gap % 3 = 0 ∨ gap % 3 = 1 ∨ gap % 3 = 2 := by
  have residue_lt := Nat.mod_lt gap (by norm_num : 0 < 3)
  omega

/-- The first open `b` gap is the unique singular atom at every admissible source body. -/
theorem atom_det_eq_zero_iff
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ [])
    (letter : TagLetter) (gap : Nat) :
    (atom β body letter gap).det = 0 ↔ letter = .b ∧ gap = 1 := by
  obtain residue_zero | residue_one | residue_two := gap_mod_three_cases gap
  · have gap_shape : gap = 3 * (gap / 3) := by omega
    cases letter with
    | b =>
        simp only [atom, true_and]
        constructor
        · intro determinant_zero
          rw [gap_shape] at determinant_zero
          exact False.elim (bAtom_det_three_mul_ne_zero β (gap / 3) determinant_zero)
        · intro gap_one
          omega
    | c =>
        simp only [atom, reduceCtorEq, false_and]
        rw [gap_shape]
        constructor
        · exact cAtom_det_three_mul_ne_zero β body (gap / 3)
        · exact False.elim
  · have gap_shape : gap = 3 * (gap / 3) + 1 := by omega
    cases letter with
    | b =>
        simp only [atom, true_and]
        rw [gap_shape, bAtom_det_three_mul_add_one_eq_zero_iff]
        omega
    | c =>
        simp only [atom, reduceCtorEq, false_and]
        rw [gap_shape]
        constructor
        · exact cAtom_det_three_mul_add_one_ne_zero β body body_nonempty (gap / 3)
        · exact False.elim
  · have gap_shape : gap = 3 * (gap / 3) + 2 := by omega
    cases letter with
    | b =>
        simp only [atom, true_and]
        constructor
        · intro determinant_zero
          rw [gap_shape] at determinant_zero
          exact False.elim (bAtom_det_three_mul_add_two_ne_zero β (gap / 3) determinant_zero)
        · intro gap_one
          omega
    | c =>
        simp only [atom, reduceCtorEq, false_and]
        rw [gap_shape]
        constructor
        · exact cAtom_det_three_mul_add_two_ne_zero β body (gap / 3)
        · exact False.elim

/-- Every atom except the first open `b` gap is invertible. -/
theorem atom_isUnit_iff
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ [])
    (letter : TagLetter) (gap : Nat) :
    IsUnit (atom β body letter gap) ↔ (letter, gap) ≠ (.b, 1) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  simpa [Prod.ext_iff] using not_congr
    (atom_det_eq_zero_iff β body body_nonempty letter gap)

/-- No single atom annihilates the blade column. -/
theorem atom_mulVec_column_ne_zero
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ [])
    (letter : TagLetter) (gap : Nat) :
    atom β body letter gap *ᵥ column ((3 : ℚ) ^ β) ≠ 0 := by
  by_cases exceptional : (letter, gap) = (.b, 1)
  · have letter_b : letter = .b := congrArg Prod.fst exceptional
    have gap_one : gap = 1 := congrArg Prod.snd exceptional
    subst letter
    subst gap
    simp only [atom]
    rw [bAtom_one_mulVec_column]
    exact smul_ne_zero (by positivity) (column_ne_zero _)
  · exact unit_mulVec_ne_zero
      ((atom_isUnit_iff β body body_nonempty letter gap).mpr exceptional)
      (column_ne_zero _)

/-- No single atom annihilates the blade row. -/
theorem row_vecMul_atom_ne_zero
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ [])
    (letter : TagLetter) (gap : Nat) :
    row ((3 : ℚ) ^ β) ᵥ* atom β body letter gap ≠ 0 := by
  by_cases exceptional : (letter, gap) = (.b, 1)
  · have letter_b : letter = .b := congrArg Prod.fst exceptional
    have gap_one : gap = 1 := congrArg Prod.snd exceptional
    subst letter
    subst gap
    simp only [atom]
    rw [row_vecMul_bAtom_one]
    exact smul_ne_zero (by positivity) (row_ne_zero _)
  · exact vecMul_unit_ne_zero (row_ne_zero _)
      ((atom_isUnit_iff β body body_nonempty letter gap).mpr exceptional)

/-- Two exceptional atoms separated by any regular atom word cannot vanish. -/
theorem two_exceptional_atoms_ne_zero
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ [])
    (middle : List (TagLetter × Nat))
    (regular : ∀ label ∈ middle, label ≠ (.b, 1)) :
    atom β body .b 1 *
        wordProduct (fun label => atom β body label.1 label.2) middle *
        atom β body .b 1 ≠ 0 := by
  let R := atom β body .b 1
  let M := wordProduct (fun label => atom β body label.1 label.2) middle
  have M_unit : IsUnit M := by
    apply wordProduct_isUnit_of_mem
    intro label label_mem
    exact (atom_isUnit_iff β body body_nonempty label.1 label.2).mpr
      (regular label label_mem)
  have M_det_unit : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp M_unit
  have R_rank : R.rank = 2 := by
    change (bAtom ((3 : ℚ) ^ β) 1).rank = 2
    exact bAtom_one_rank β
  have RM_rank : (R * M).rank = 2 := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det M R M_det_unit, R_rank]
  intro product_zero
  have bound := Matrix.rank_add_rank_le_card_of_mul_eq_zero product_zero
  rw [RM_rank, R_rank] at bound
  norm_num at bound

end ParabolicBlade

end MatrixMortality
