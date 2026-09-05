import Mathlib.LinearAlgebra.Matrix.Rank
import MatrixMortality.InterfaceCompression
import MatrixMortality.ProjectiveLine
import MatrixMortality.SingularReturnFamily

/-!
# Four-mode return artery

Interface compression identifies the rank-`(4,2)` binary profile with mortality of one
four-mode unary return family.  Four modes do not, however, inherit the rational-rail rigidity
of the three-mode valuation guard: an explicit rank-two cut produces a nonperiodic affine wait
rail on one rational projective coordinate.
-/

namespace MatrixMortality.FourModeArtery

open scoped Matrix

noncomputable section

/-- The rank-`(4,2)` binary profile is exactly its unary two-dimensional return family. -/
theorem fourModePair_isMortal_iff_returnFamily
    (ambient : Square (Fin 4) ℚ)
    (input : Matrix (Fin 4) (Fin 2) ℚ)
    (output : Matrix (Fin 2) (Fin 4) ℚ)
    (ambient_unit : IsUnit ambient) :
    IsMortal (ReturnFamily.pairGenerator ambient (input * output)) ↔
      IsMortal (ReturnFamily.returnMatrix ambient input output) :=
  ReturnFamily.pairGenerator_isMortal_iff_returnFamily ambient input output
    fun power ↦ (ambient_unit.pow power).ne_zero

/-- Four invertible spectral modes supporting the affine rail. -/
def railbreakerAmbient (radix gear : ℚ) : Square (Fin 4) ℚ :=
  Matrix.diagonal ![1, 1, gear, radix * gear]

/-- Input interface of the affine-rail witness. -/
def railbreakerInput : Matrix (Fin 4) (Fin 2) ℚ :=
  !![1, 0;
     0, 1;
     0, 1;
     0, 1]

/-- Output interface of the affine-rail witness. -/
def railbreakerOutput (radix : ℚ) : Matrix (Fin 2) (Fin 4) ℚ :=
  !![radix, 0, 0, -radix;
     0, 1, -1, 0]

/-- Physical rank-two cut of the affine-rail witness. -/
def railbreakerCut (radix : ℚ) : Square (Fin 4) ℚ :=
  railbreakerInput * railbreakerOutput radix

/-- Left inverse certifying that the input interface has full column rank. -/
def railbreakerInputLeftInverse : Matrix (Fin 2) (Fin 4) ℚ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0]

/-- Right inverse certifying that the output interface has full row rank. -/
def railbreakerOutputRightInverse (radix : ℚ) : Matrix (Fin 4) (Fin 2) ℚ :=
  !![radix⁻¹, 0;
     0, 1;
     0, 0;
     0, 0]

/-- The displayed retraction is a left inverse of the input interface. -/
theorem railbreakerInputLeftInverse_mul_input :
    railbreakerInputLeftInverse * railbreakerInput = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [railbreakerInputLeftInverse, railbreakerInput, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ]

/-- The displayed section is a right inverse of the output interface. -/
theorem railbreakerOutput_mul_outputRightInverse
    (radix : ℚ) (radix_ne_zero : radix ≠ 0) :
    railbreakerOutput radix * railbreakerOutputRightInverse radix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [railbreakerOutput, railbreakerOutputRightInverse, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ]
  field_simp [radix_ne_zero]

/-- The physical railbreaker cut has rank exactly two. -/
theorem railbreakerCut_rank (radix : ℚ) (radix_ne_zero : radix ≠ 0) :
    (railbreakerCut radix).rank = 2 := by
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left railbreakerInput (railbreakerOutput radix)).trans
      (Matrix.rank_le_width railbreakerInput)
  · have output_factor :
        railbreakerOutput radix =
          railbreakerInputLeftInverse * railbreakerCut radix := by
      calc
        railbreakerOutput radix =
            (1 : Square (Fin 2) ℚ) * railbreakerOutput radix := by simp
        _ = (railbreakerInputLeftInverse * railbreakerInput) *
            railbreakerOutput radix := by rw [railbreakerInputLeftInverse_mul_input]
        _ = railbreakerInputLeftInverse *
            (railbreakerInput * railbreakerOutput radix) := Matrix.mul_assoc _ _ _
        _ = railbreakerInputLeftInverse * railbreakerCut radix := rfl
    have output_rank : (railbreakerOutput radix).rank = 2 := by
      apply le_antisymm
      · exact Matrix.rank_le_height (railbreakerOutput radix)
      · have rank_bound := Matrix.rank_mul_le_left
          (railbreakerOutput radix) (railbreakerOutputRightInverse radix)
        rw [railbreakerOutput_mul_outputRightInverse radix radix_ne_zero,
          Matrix.rank_one] at rank_bound
        norm_num at rank_bound ⊢
        exact rank_bound
    have lower :
        (railbreakerOutput radix).rank ≤ (railbreakerCut radix).rank := by
      rw [output_factor]
      exact Matrix.rank_mul_le_right railbreakerInputLeftInverse (railbreakerCut radix)
    rwa [output_rank] at lower

/-- The railbreaker ambient generator is invertible when both bases are nonzero. -/
theorem railbreakerAmbient_isUnit
    (radix gear : ℚ) (radix_ne_zero : radix ≠ 0) (gear_ne_zero : gear ≠ 0) :
    IsUnit (railbreakerAmbient radix gear) := by
  apply (railbreakerAmbient radix gear).isUnit_iff_isUnit_det.mpr
  rw [railbreakerAmbient, Matrix.det_diagonal]
  apply isUnit_iff_ne_zero.mpr
  simp [Fin.prod_univ_succ, radix_ne_zero, gear_ne_zero]

/-- Closed form of every return in the four-mode affine-rail witness. -/
theorem railbreakerReturn_eq (radix gear : ℚ) (wait : Nat) :
    ReturnFamily.returnMatrix (railbreakerAmbient radix gear)
        railbreakerInput (railbreakerOutput radix) wait =
      !![radix, -radix * (radix * gear) ^ wait;
         0, 1 - gear ^ wait] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ReturnFamily.returnMatrix, railbreakerAmbient, railbreakerInput,
      railbreakerOutput, Matrix.diagonal_pow, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Matrix.diagonal_apply, Fin.sum_univ_succ]
  ring

/-- Wait `n` sends the rail point `radixⁿ` exactly to `radixⁿ⁺¹`. -/
theorem railbreaker_affineWait
    (radix gear : ℚ) (wait : Nat) (gear_power_ne_one : gear ^ wait ≠ 1) :
    ProjectiveLine.act
        (ReturnFamily.returnMatrix (railbreakerAmbient radix gear)
          railbreakerInput (railbreakerOutput radix) wait)
        (some (radix ^ wait)) =
      some (radix ^ (wait + 1)) := by
  have denominator_ne_zero : 1 - gear ^ wait ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm gear_power_ne_one)
  let matrix :=
    ReturnFamily.returnMatrix (railbreakerAmbient radix gear)
      railbreakerInput (railbreakerOutput radix) wait
  have image :
      matrix *ᵥ ProjectiveLine.ray (some (radix ^ wait)) =
        (1 - gear ^ wait) • ProjectiveLine.ray (some (radix ^ (wait + 1))) := by
    dsimp [matrix]
    rw [railbreakerReturn_eq]
    ext i
    fin_cases i <;>
      simp [ProjectiveLine.ray, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        mul_pow]
    ring
  calc
    ProjectiveLine.act matrix (some (radix ^ wait)) =
        ProjectiveLine.ofPair
          ((matrix *ᵥ ProjectiveLine.ray (some (radix ^ wait))) 0)
          ((matrix *ᵥ ProjectiveLine.ray (some (radix ^ wait))) 1) :=
      (ProjectiveLine.ofPair_mulVec_ray matrix (some (radix ^ wait))).symm
    _ = ProjectiveLine.ofPair
          (((1 - gear ^ wait) •
            ProjectiveLine.ray (some (radix ^ (wait + 1)))) 0)
          (((1 - gear ^ wait) •
            ProjectiveLine.ray (some (radix ^ (wait + 1)))) 1) := by rw [image]
    _ = some (radix ^ (wait + 1)) := by
      simp [ProjectiveLine.ray, ProjectiveLine.ofPair, denominator_ne_zero]

/-- Radix greater than one makes the exact rail nonperiodic. -/
theorem railbreaker_orbit_injective
    (radix : ℚ) (radix_gt_one : 1 < radix) :
    Function.Injective fun wait : Nat ↦ radix ^ wait :=
  (pow_right_strictMono₀ radix_gt_one).injective

end

end MatrixMortality.FourModeArtery
