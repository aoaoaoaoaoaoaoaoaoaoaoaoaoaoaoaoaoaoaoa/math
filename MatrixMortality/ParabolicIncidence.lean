import MatrixMortality.ParabolicDefect
import MatrixMortality.ParabolicSemanticObstruction

namespace MatrixMortality.ParabolicBlade

open scoped Matrix

/-- Canonical right-kernel coordinate of a wall bridge. -/
def bridgeKernel (ρ : ℚ) (middle : Matrix (Fin 3) (Fin 3) ℚ) : Fin 2 → ℚ :=
  coreLeftInverse ρ *ᵥ (middle.adjugate *ᵥ bladeKernel)

private theorem core_projection (ρ : ℚ) (ρ_ne : ρ ≠ 0) :
    coreOutput ρ * coreLeftInverse ρ =
      1 - (1 / 22 : ℚ) • Matrix.vecMulVec (![1, 0, 0] : Fin 3 → ℚ) exteriorSeed := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coreOutput, coreLeftInverse, exteriorSeed, Matrix.one_apply,
      Matrix.mul_apply, Matrix.vecMulVec_apply, Fin.sum_univ_succ]
  all_goals simp_all
  all_goals field_simp [ρ_ne]
  all_goals ring

private theorem exterior_wall_dot (middle : Matrix (Fin 3) (Fin 3) ℚ) :
    exteriorSeed ⬝ᵥ (middle.adjugate *ᵥ bladeKernel) =
      -4 * exteriorState middle 0 := by
  norm_num [exteriorSeed, bladeKernel, exteriorState, exteriorChange,
    Matrix.adjugate_fin_three, Matrix.transpose_apply, Matrix.mulVec,
    Matrix.dotProduct, Fin.sum_univ_succ]
  ring

private theorem outer_mulVec_apply (column row vector : Fin 3 → ℚ) :
    Matrix.vecMulVec column row *ᵥ vector = (row ⬝ᵥ vector) • column := by
  funext i
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, Matrix.dotProduct,
    Pi.smul_apply, smul_eq_mul]
  calc
    (∑ x, column i * row x * vector x) =
        column i * ∑ x, row x * vector x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (∑ x, row x * vector x) * column i := by ring

theorem coreOutput_mulVec_bridgeKernel_of_wall
    (ρ : ℚ) (ρ_ne : ρ ≠ 0) (middle : Matrix (Fin 3) (Fin 3) ℚ)
    (wall : exteriorState middle 0 = 0) :
    coreOutput ρ *ᵥ bridgeKernel ρ middle = middle.adjugate *ᵥ bladeKernel := by
  rw [bridgeKernel, Matrix.mulVec_mulVec, core_projection ρ ρ_ne]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec_assoc, outer_mulVec_apply]
  rw [exterior_wall_dot, wall]
  simp

/-- An invertible middle block gives a genuine nonzero projective kernel on the wall. -/
theorem bridgeKernel_ne_zero_of_isUnit
    (ρ : ℚ) (ρ_ne : ρ ≠ 0) (middle : Matrix (Fin 3) (Fin 3) ℚ)
    (middle_unit : IsUnit middle) (wall : exteriorState middle 0 = 0) :
    bridgeKernel ρ middle ≠ 0 := by
  intro kernel_zero
  have live_zero : middle.adjugate *ᵥ bladeKernel = 0 := by
    rw [← coreOutput_mulVec_bridgeKernel_of_wall ρ ρ_ne middle wall, kernel_zero]
    simp
  have annihilation : middle.det • bladeKernel = 0 := by
    calc
      middle.det • bladeKernel =
          (middle.det • (1 : Matrix (Fin 3) (Fin 3) ℚ)) *ᵥ bladeKernel := by
        funext i
        fin_cases i <;>
          norm_num [bladeKernel, Matrix.mulVec, Matrix.dotProduct, Matrix.one_apply,
            Matrix.smul_apply, Fin.sum_univ_succ]
      _ = (middle * middle.adjugate) *ᵥ bladeKernel := by rw [Matrix.mul_adjugate]
      _ = middle *ᵥ (middle.adjugate *ᵥ bladeKernel) := by
        rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [live_zero]; simp
  have determinant_ne : middle.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det middle).mp middle_unit).ne_zero
  have kernel_ne : bladeKernel ≠ 0 := by
    intro kernel_zero'
    have entry := congr_fun kernel_zero' 0
    norm_num [bladeKernel] at entry
  exact smul_ne_zero determinant_ne kernel_ne annihilation

private theorem coreInput_mulVec_bladeKernel : coreInput *ᵥ bladeKernel = 0 := by
  funext i
  fin_cases i <;>
    norm_num [coreInput, bladeKernel, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]

theorem bridge_mulVec_bridgeKernel_of_wall
    (ρ : ℚ) (ρ_ne : ρ ≠ 0) (middle : Matrix (Fin 3) (Fin 3) ℚ)
    (wall : exteriorState middle 0 = 0) :
    bridge ρ middle *ᵥ bridgeKernel ρ middle = 0 := by
  rw [bridge,
    ← Matrix.mulVec_mulVec (bridgeKernel ρ middle) (coreInput * middle) (coreOutput ρ),
    ← Matrix.mulVec_mulVec _ coreInput middle,
    coreOutput_mulVec_bridgeKernel_of_wall ρ ρ_ne middle wall]
  rw [Matrix.mulVec_mulVec bladeKernel middle middle.adjugate, Matrix.mul_adjugate]
  rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec, Matrix.mulVec_smul,
    coreInput_mulVec_bladeKernel]
  simp

/-- Every regular wall word exposes a nonzero canonical bridge kernel. -/
theorem bridgeKernel_regular_word_ne_zero
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ [])
    (middle : List (TagLetter × Nat))
    (regular : ∀ label ∈ middle, label ≠ (.b, 1))
    (wall : exteriorState
      (wordProduct (fun label => atom β body label.1 label.2) middle) 0 = 0) :
    bridgeKernel ((3 : ℚ) ^ β)
      (wordProduct (fun label => atom β body label.1 label.2) middle) ≠ 0 := by
  apply bridgeKernel_ne_zero_of_isUnit _ (by positivity) _ _ wall
  exact wordProduct_isUnit_of_mem _ middle (fun label member =>
    (atom_isUnit_iff β body body_nonempty label.1 label.2).mpr
      (regular label member))

end MatrixMortality.ParabolicBlade
