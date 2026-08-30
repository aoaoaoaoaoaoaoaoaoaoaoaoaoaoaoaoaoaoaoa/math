import MatrixMortality.PadicValuation
import MatrixMortality.ParabolicResidueWall

/-!
# Complete exterior dynamics of the parabolic blade

The adjugate state below is the exact three-coordinate state consumed by the parabolic bridge.
Its first coordinate is the bridge determinant wall.  Safe atoms act through four explicit
families; the subsequent section proves their arbitrary-switching `3`-adic flag.
-/

namespace MatrixMortality.ParabolicBlade

open scoped Matrix

/-- Covector selected by the two sides of the exceptional bridge. -/
def exteriorSeed : Fin 3 → ℚ := ![22, -31, -36]

/-- Triangle coordinates: the first row is the bridge singularity covector. -/
def exteriorChange : Matrix (Fin 3) (Fin 3) ℚ :=
  !![-1, -1, 1 / 4;
      1, 0, 0;
      0, 0, -1 / 4]

/-- Inverse triangle-coordinate change. -/
def exteriorChangeInv : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, 1, 0;
     -1, -1, -1;
      0, 0, -4]

theorem exteriorChangeInv_mul_exteriorChange : exteriorChangeInv * exteriorChange = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [exteriorChangeInv, exteriorChange, Matrix.one_apply, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem exteriorChange_mul_exteriorChangeInv : exteriorChange * exteriorChangeInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [exteriorChangeInv, exteriorChange, Matrix.one_apply, Matrix.mul_apply,
      Fin.sum_univ_succ]

/-- Complete contragredient exterior state of a safe suffix product. -/
def exteriorState (middle : Matrix (Fin 3) (Fin 3) ℚ) : Fin 3 → ℚ :=
  exteriorChange *ᵥ (middle.adjugateᵀ *ᵥ exteriorSeed)

/-- Left multiplication of the suffix acts linearly on the complete exterior state. -/
def exteriorTransition (atom : Matrix (Fin 3) (Fin 3) ℚ) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  exteriorChange * atom.adjugateᵀ * exteriorChangeInv

@[simp] theorem exteriorState_one : exteriorState 1 = ![0, 22, 9] := by
  rw [exteriorState, Matrix.adjugate_one, Matrix.transpose_one, Matrix.one_mulVec]
  funext i
  fin_cases i <;>
    norm_num [exteriorSeed, exteriorChange, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The exterior transition respects physical left multiplication, including singular atoms. -/
theorem exteriorState_mul (atom middle : Matrix (Fin 3) (Fin 3) ℚ) :
    exteriorState (atom * middle) = exteriorTransition atom *ᵥ exteriorState middle := by
  have transition_cancel :
      exteriorTransition atom * exteriorChange = exteriorChange * atom.adjugateᵀ := by
    simp [exteriorTransition, Matrix.mul_assoc, exteriorChangeInv_mul_exteriorChange]
  have applied := congrArg
    (fun matrix => matrix *ᵥ (middle.adjugateᵀ *ᵥ exteriorSeed)) transition_cancel
  simpa only [exteriorState, Matrix.adjugate_mul_distrib, Matrix.transpose_mul,
    Matrix.mulVec_mulVec, Matrix.mul_assoc] using applied.symm

/-- The bridge determinant is exactly the first complete exterior coordinate. -/
theorem bridge_det_eq_exteriorState_first (ρ : ℚ)
    (middle : Matrix (Fin 3) (Fin 3) ℚ) :
    (bridge ρ middle).det = (9 * ρ / 2) * exteriorState middle 0 := by
  rw [bridge_det_eq_adjugate_first]
  congr 1
  norm_num [exteriorState, exteriorChange, exteriorSeed, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

private theorem cAtom_three_mul_matrix (ρ L M : ℚ) (j : Nat) :
    cAtom ρ L M (3 * j) =
      !![1, 2, 2 * j * (L - 1) + 2;
         0, 3, 0;
         0, 0, j * (M - 3) + 3] := by
  rw [cAtom, normalRoot_pow_three_mul]
  ext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [cFlank, flank, drift, injection, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

/-- Closed formula for the triangle-coordinate transport of an arbitrary three-by-three atom. -/
private theorem exteriorTransition_matrix
    (a b c d e f g h i : ℚ) :
    exteriorTransition !![a, b, c; d, e, f; g, h, i] =
      !![a * f / 4 + a * i - c * d / 4 - c * g - d * i + f * g,
          a * f / 4 + a * i + b * f / 4 + b * i - c * d / 4 - c * e / 4 - c * g -
            c * h - d * i - e * i + f * g + f * h,
          -a * e + a * f / 4 - 4 * a * h + a * i + b * d + 4 * b * g - c * d / 4 -
            c * g + 4 * d * h - d * i - 4 * e * g + f * g;
         d * i - f * g, d * i + e * i - f * g - f * h,
          -4 * d * h + d * i + 4 * e * g - f * g;
         -a * f / 4 + c * d / 4, -a * f / 4 - b * f / 4 + c * d / 4 + c * e / 4,
          a * e - a * f / 4 - b * d + c * d / 4] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [exteriorTransition, exteriorChange, exteriorChangeInv, Matrix.adjugate_fin_three,
      Matrix.transpose_apply, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;>
    ring

/-- The four normalized safe exterior actions. -/
def safeExteriorAction (ρ L M : ℚ) :
    TagLetter × Nat × Bool → Matrix (Fin 3) (Fin 3) ℚ
  | (.b, j, false) =>
      !![8 * j + 1, -(3 / 2) * (32 * j * ρ - 8 * j + 2 * ρ - 1),
          8 * j - 3 * ρ + 1;
         0, 9 * ρ * (8 * j + 1), 0;
         0, (3 * ρ / 2) * (24 * j + 1), 3 * ρ]
  | (.c, j, false) =>
      !![1 + (M / 3 - 1) * j, -((L - 1) * j + 1) / 2, (M - 3) * j / 3;
         0, (M - 3) * j + 3, 0;
         0, ((L - 1) * j + 1) / 2, 1]
  | (.b, j, true) =>
      !![-4 * j * (12 * ρ - 1), -8 * j, -4 * j * (12 * ρ - 1);
         3 * ρ * (24 * j + 11), 0, 72 * j * ρ;
         (9 * ρ / 2) * (8 * j + 3), 0, 36 * j * ρ]
  | (.c, j, true) =>
      !![(-48 * L * j + 114 * L * ρ - 27 * L - 32 * M * j - 38 * M * ρ -
            7 * M + 144 * j - 96) / 96,
          (11 * L - 16 * M * j - 9 * M + 48 * j - 32) / 48,
          (-48 * L * j + 114 * L * ρ - 5 * L - 32 * M * j - 114 * M * ρ +
            15 * M + 144 * j + 228 * ρ - 280) / 96;
         (M - 3) * j + M / 3 + 2, 0, (M - 3) * j + (27 - M) / 8;
         (L - 1) * j / 2 + (L + 2) / 6, 0,
          (L - 1) * j / 2 + (25 - L) / 16]

private theorem exteriorTransition_b_zero (β : Nat) (body : List TagLetter) (j : Nat) :
    exteriorTransition (residueTwoWallGenerator β body (.b, j, false)) =
      (3 : ℚ) • safeExteriorAction ((3 : ℚ) ^ β)
        (nearySideLowerC β body) (nearySideLowerCScale β body) (.b, j, false) := by
  rw [show residueTwoWallGenerator β body (.b, j, false) =
        bAtom ((3 : ℚ) ^ β) (3 * j) by rfl,
    bAtom_three_mul_matrix, exteriorTransition_matrix]
  ext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [safeExteriorAction, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;>
    ring

private theorem exteriorTransition_b_one (β : Nat) (body : List TagLetter) (j : Nat) :
    exteriorTransition (residueTwoWallGenerator β body (.b, j, true)) =
      (3 : ℚ) • safeExteriorAction ((3 : ℚ) ^ β)
        (nearySideLowerC β body) (nearySideLowerCScale β body) (.b, j, true) := by
  rw [residueTwoWallGenerator_b_one_matrix, exteriorTransition_matrix]
  ext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [safeExteriorAction, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;>
    ring

private theorem exteriorTransition_c_zero (β : Nat) (body : List TagLetter) (j : Nat) :
    exteriorTransition (residueTwoWallGenerator β body (.c, j, false)) =
      (3 : ℚ) • safeExteriorAction ((3 : ℚ) ^ β)
        (nearySideLowerC β body) (nearySideLowerCScale β body) (.c, j, false) := by
  rw [show residueTwoWallGenerator β body (.c, j, false) =
        cAtom ((3 : ℚ) ^ β) (nearySideLowerC β body)
          (nearySideLowerCScale β body) (3 * j) by rfl,
    cAtom_three_mul_matrix, exteriorTransition_matrix]
  ext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [safeExteriorAction, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;>
    ring

private theorem exteriorTransition_c_one (β : Nat) (body : List TagLetter) (j : Nat) :
    exteriorTransition (residueTwoWallGenerator β body (.c, j, true)) =
      (3 : ℚ) • safeExteriorAction ((3 : ℚ) ^ β)
        (nearySideLowerC β body) (nearySideLowerCScale β body) (.c, j, true) := by
  rw [show residueTwoWallGenerator β body (.c, j, true) =
        cAtom ((3 : ℚ) ^ β) (nearySideLowerC β body)
          (nearySideLowerCScale β body) (3 * j + 1) by rfl,
    cAtom_three_mul_add_one_matrix, exteriorTransition_matrix]
  ext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [safeExteriorAction, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;>
    ring

/-- Every physical safe atom induces three times its normalized exterior action. -/
theorem exteriorTransition_residueTwoWallGenerator
    (β : Nat) (body : List TagLetter) (label : TagLetter × Nat × Bool) :
    exteriorTransition (residueTwoWallGenerator β body label) =
      (3 : ℚ) • safeExteriorAction ((3 : ℚ) ^ β)
        (nearySideLowerC β body) (nearySideLowerCScale β body) label := by
  obtain ⟨letter, j, residueOne⟩ := label
  cases letter <;> cases residueOne
  · exact exteriorTransition_b_zero β body j
  · exact exteriorTransition_b_one β body j
  · exact exteriorTransition_c_zero β body j
  · exact exteriorTransition_c_one β body j

end MatrixMortality.ParabolicBlade
