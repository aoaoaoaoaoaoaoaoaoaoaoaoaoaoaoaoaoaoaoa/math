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
    dotProduct, Fin.sum_univ_succ]
  ring

private theorem outer_mulVec_apply (column row vector : Fin 3 → ℚ) :
    Matrix.vecMulVec column row *ᵥ vector = (row ⬝ᵥ vector) • column := by
  funext i
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct,
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
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, outer_mulVec_apply]
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
          norm_num [bladeKernel, Matrix.mulVec, dotProduct, Matrix.one_apply,
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
    norm_num [coreInput, bladeKernel, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem bridge_mulVec_bridgeKernel_of_wall
    (ρ : ℚ) (ρ_ne : ρ ≠ 0) (middle : Matrix (Fin 3) (Fin 3) ℚ)
    (wall : exteriorState middle 0 = 0) :
    bridge ρ middle *ᵥ bridgeKernel ρ middle = 0 := by
  rw [bridge,
    ← Matrix.mulVec_mulVec (bridgeKernel ρ middle) (coreInput * middle) (coreOutput ρ),
    ← Matrix.mulVec_mulVec _ coreInput middle,
    coreOutput_mulVec_bridgeKernel_of_wall ρ ρ_ne middle wall]
  rw [Matrix.mulVec_mulVec bladeKernel middle middle.adjugate, Matrix.mul_adjugate]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul,
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

/-! ## Phase chamber forced by a safe right wall -/

open MatrixMortality.PadicValuation

private theorem valLt_left_of_oriented_incidence
    {high low first second unit : ℚ}
    (orientation : ValLt low high)
    (unit_shell : IsUnit 3 unit)
    (pair_ne : ![first, second] ≠ (0 : Fin 2 → ℚ))
    (incidence : high * first = unit * low * second) :
    ValLt first second := by
  rcases orientation with ⟨low_ne, high_zero | low_lt_high⟩
  · have second_zero : second = 0 := by
      have : unit * low * second = 0 := by simpa [high_zero] using incidence.symm
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero unit_shell.1 low_ne)
    refine ⟨?_, Or.inl second_zero⟩
    intro first_zero
    apply pair_ne
    funext i
    fin_cases i <;> simp [first_zero, second_zero]
  · by_cases high_ne : high = 0
    · have second_zero : second = 0 := by
        have : unit * low * second = 0 := by simpa [high_ne] using incidence.symm
        exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero unit_shell.1 low_ne)
      refine ⟨?_, Or.inl second_zero⟩
      intro first_zero
      apply pair_ne
      funext i
      fin_cases i <;> simp [first_zero, second_zero]
    · have first_ne : first ≠ 0 := by
        intro first_zero
        have : unit * low * second = 0 := by simpa [first_zero] using incidence.symm
        have second_zero : second = 0 :=
          (mul_eq_zero.mp this).resolve_left (mul_ne_zero unit_shell.1 low_ne)
        apply pair_ne
        funext i
        fin_cases i <;> simp [first_zero, second_zero]
      have second_ne : second ≠ 0 := by
        intro second_zero
        have : high * first = 0 := by simpa [second_zero] using incidence
        exact first_ne ((mul_eq_zero.mp this).resolve_left high_ne)
      refine ⟨first_ne, Or.inr ?_⟩
      have valuation_eq :
          padicValRat 3 high + padicValRat 3 first =
            padicValRat 3 low + padicValRat 3 second := by
        have := congrArg (padicValRat 3) incidence
        simpa [padicValRat.mul high_ne first_ne,
          padicValRat.mul unit_shell.1 low_ne,
          padicValRat.mul (mul_ne_zero unit_shell.1 low_ne) second_ne,
          unit_shell.2, add_assoc] using this
      omega

/-- Incidence with a nonempty safe wall forces the transported kernel into the strict
valuation chamber opposite the wall's leftmost residue. -/
theorem safeWall_incidence_orients_transport
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ [])
    (head : TagLetter × Nat × Bool) (tail : List (TagLetter × Nat × Bool))
    (regular : ∀ label ∈ head :: tail, RegularSafeLabel label)
    (wall : exteriorState
      (wordProduct (residueTwoWallGenerator β body) (head :: tail)) 0 = 0)
    (transported : Fin 2 → ℚ) (transported_ne : transported ≠ 0)
    (incidence :
      bridgeCokernel
          (wordProduct (residueTwoWallGenerator β body) (head :: tail)) ⬝ᵥ
        transported = 0) :
    if head.2.2 then
      ValLt (transported 1) (transported 0)
    else
      ValLt (transported 0) (transported 1) := by
  let middle := wordProduct (residueTwoWallGenerator β body) (head :: tail)
  change exteriorState middle 0 = 0 at wall
  change bridgeCokernel middle ⬝ᵥ transported = 0 at incidence
  have orientation := exteriorState_safe_word_wall_orientation
    β body body_nonempty head tail regular wall
  have equation : exteriorState middle 1 * transported 0 =
      4 * exteriorState middle 2 * transported 1 := by
    rw [bridgeCokernel_eq_exteriorTail] at incidence
    norm_num [dotProduct, Fin.sum_univ_succ] at incidence
    linear_combination incidence
  have pair_ne : ![transported 0, transported 1] ≠ (0 : Fin 2 → ℚ) := by
    intro pair_zero
    apply transported_ne
    funext i
    fin_cases i
    · simpa using congr_fun pair_zero 0
    · simpa using congr_fun pair_zero 1
  have swapped_ne : ![transported 1, transported 0] ≠ (0 : Fin 2 → ℚ) := by
    intro pair_zero
    apply transported_ne
    funext i
    fin_cases i
    · simpa using congr_fun pair_zero 1
    · simpa using congr_fun pair_zero 0
  by_cases phase : head.2.2
  · simp only [phase, if_true] at orientation ⊢
    have quarter_unit : IsUnit 3 (1 / 4 : ℚ) :=
      div_hasValue
        (intCast_isUnit_of_not_dvd (by norm_num : ¬(3 : ℤ) ∣ 1))
        (intCast_isUnit_of_not_dvd (by norm_num : ¬(3 : ℤ) ∣ 4))
    apply valLt_left_of_oriented_incidence
      (first := transported 1) (second := transported 0)
      orientation quarter_unit swapped_ne
    linear_combination (1 / 4 : ℚ) * equation.symm
  · simp only [phase] at orientation ⊢
    have four_unit : IsUnit 3 (4 : ℚ) :=
      intCast_isUnit_of_not_dvd (by norm_num : ¬(3 : ℤ) ∣ 4)
    exact valLt_left_of_oriented_incidence
      (first := transported 0) (second := transported 1)
      orientation four_unit pair_ne equation

/-- A transported kernel with two nonzero coordinates of equal valuation cannot close against
a nonempty safe wall. -/
theorem safeWall_rejects_balanced_transport
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ [])
    (head : TagLetter × Nat × Bool) (tail : List (TagLetter × Nat × Bool))
    (regular : ∀ label ∈ head :: tail, RegularSafeLabel label)
    (wall : exteriorState
      (wordProduct (residueTwoWallGenerator β body) (head :: tail)) 0 = 0)
    (transported : Fin 2 → ℚ)
    (first_ne : transported 0 ≠ 0) (second_ne : transported 1 ≠ 0)
    (balanced : padicValRat 3 (transported 0) = padicValRat 3 (transported 1)) :
    bridgeCokernel
        (wordProduct (residueTwoWallGenerator β body) (head :: tail)) ⬝ᵥ
      transported ≠ 0 := by
  intro incidence
  have transported_ne : transported ≠ 0 := by
    intro transported_zero
    exact first_ne (congr_fun transported_zero 0)
  have orientation := safeWall_incidence_orients_transport
    β body body_nonempty head tail regular wall transported transported_ne incidence
  split at orientation
  · rcases orientation with ⟨_, first_zero | second_lt_first⟩
    · exact first_ne first_zero
    · omega
  · rcases orientation with ⟨_, second_zero | first_lt_second⟩
    · exact second_ne second_zero
    · omega

end MatrixMortality.ParabolicBlade
