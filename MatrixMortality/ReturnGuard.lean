import MatrixMortality.ProjectiveLine
import MatrixMortality.ReturnFamily

/-!
# Amalgamated valuation-guard returns

Three geometric modes carry a rank-one zero return, invertible positive returns, and the
cross-multiplied verifier identity used by the valuation dynamics. This file owns only the
linear algebra and the exact arbitrary-word mortality reduction.
-/

namespace MatrixMortality.ReturnGuard

open scoped Matrix

noncomputable section

/-- Difference between reset and center parameters. -/
def drift {R : Type*} [Ring R] (center reset : R) : R :=
  reset - center

/-- Three-mode ambient action with reciprocal, constant, and expanding modes. -/
def ambient {K : Type*} [Field K] (prime : K) (depth : Nat) : Square (Fin 3) K :=
  Matrix.diagonal ![1, prime⁻¹, prime ^ (depth - 1)]

/-- Split inclusion of the two-dimensional return interface. -/
def input {R : Type*} [CommRing R] : Matrix (Fin 3) (Fin 2) R :=
  !![0, 1;
     1, 0;
     1, -1]

/-- Parameterized split projection. -/
def output {R : Type*} [CommRing R] (center reset : R) :
    Matrix (Fin 2) (Fin 3) R :=
  !![-center, center, drift center reset;
     -1, 1, 0]

/-- Rank-two physical cut. -/
def cut {R : Type*} [CommRing R] (center reset : R) : Square (Fin 3) R :=
  input * output center reset

/-- Closed return with reciprocal scale `low` and expanding scale `high`. -/
def transfer {R : Type*} [CommRing R]
    (center reset low high : R) : Square (Fin 2) R :=
  !![center * low + drift center reset * high,
      -center - drift center reset * high;
     low, -1]

/-- Exact ambient return after `wait` steps. -/
def returnAt (prime : ℚ) (depth : Nat) (center reset : ℚ) (wait : Nat) :
    Square (Fin 2) ℚ :=
  ReturnFamily.returnMatrix (ambient prime depth) input (output center reset) wait

/-- Positive returns, indexed by physical wait `wait+1`. -/
def positiveTransfer (prime : ℚ) (depth : Nat) (center reset : ℚ) (wait : Nat) :
    Square (Fin 2) ℚ :=
  returnAt prime depth center reset (wait + 1)

/-- Scalar bridge between two zero-wait returns. -/
def positiveBridge (prime : ℚ) (depth : Nat) (center reset : ℚ)
    (waits : List Nat) : ℚ :=
  bridgeScalar ![reset, 1] ![1, -1]
    (wordProduct (positiveTransfer prime depth center reset) waits)

/-- Return rescaled by `prime^wait`; it has the same projective action and zero behavior. -/
def guardTransfer (prime : ℚ) (depth : Nat) (center reset : ℚ) (wait : Nat) :
    Square (Fin 2) ℚ :=
  prime ^ wait • returnAt prime depth center reset wait

/-- Affine numerator of the rescaled guard return. -/
def projectiveNumerator
    (prime : ℚ) (depth : Nat) (center reset : ℚ) (wait : Nat) (z : ℚ) : ℚ :=
  (center + drift center reset * prime ^ (depth * wait)) * z -
    center * prime ^ wait - drift center reset * prime ^ (depth * wait)

/-- Affine denominator of the rescaled guard return. -/
def projectiveDenominator (prime : ℚ) (wait : Nat) (z : ℚ) : ℚ :=
  z - prime ^ wait

/-- Total projective guard step, including its pole and infinity. -/
def projectiveStep
    (prime : ℚ) (depth : Nat) (center reset : ℚ) (wait : Nat) :
    ProjectiveLine.Point ℚ → ProjectiveLine.Point ℚ :=
  ProjectiveLine.act (guardTransfer prime depth center reset wait)

/-- Left inverse of `input`. -/
def inputLeftInverse {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 3) R :=
  !![0, 1, 0;
     1, 0, 0]

/-- Right inverse of `output` away from zero drift. -/
def outputRightInverse (center reset : ℚ) : Matrix (Fin 3) (Fin 2) ℚ :=
  !![0, 0;
     0, 1;
     (drift center reset)⁻¹, -center * (drift center reset)⁻¹]

/-- Reachable coefficient columns witnessing all three ambient modes. -/
def reachableCertificate (prime : ℚ) (depth : Nat) : Square (Fin 3) ℚ :=
  !![0, 0, 1;
     1, prime⁻¹, 0;
     1, prime ^ (depth - 1), -1]

/-- Observable coefficient rows witnessing all three ambient modes. -/
def observableCertificate (prime : ℚ) (depth : Nat) (center reset : ℚ) :
    Square (Fin 3) ℚ :=
  !![-center, center, drift center reset;
     -center, center * prime⁻¹,
       drift center reset * prime ^ (depth - 1);
     -1, 1, 0]

/-- Coefficient rows: first output coordinate at waits zero and one, then the second output
coordinate at wait zero. -/
def leftIndex : Fin 3 → Nat × Fin 2 :=
  ![(0, 0), (1, 0), (0, 1)]

/-- Coefficient columns: first input coordinate at waits zero and one, then the second input
coordinate at wait zero. -/
def rightIndex : Fin 3 → Nat × Fin 2 :=
  ![(0, 0), (1, 0), (0, 1)]

theorem inputLeftInverse_mul_input {R : Type*} [CommRing R] :
    (inputLeftInverse : Matrix (Fin 2) (Fin 3) R) *
      (input : Matrix (Fin 3) (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [inputLeftInverse, input, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ]

theorem output_mul_outputRightInverse
    (center reset : ℚ) (drift_ne_zero : drift center reset ≠ 0) :
    output center reset * outputRightInverse center reset = 1 := by
  have difference_ne : reset - center ≠ 0 := by
    simpa [drift] using drift_ne_zero
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [output, outputRightInverse, drift, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ]
  all_goals field_simp [difference_ne]
  all_goals ring

/-- Nonzero drift gives the return output full row rank. -/
theorem output_rank
    (center reset : ℚ) (drift_ne_zero : drift center reset ≠ 0) :
    (output center reset).rank = 2 := by
  apply le_antisymm
  · exact Matrix.rank_le_height (output center reset)
  · have rank_bound :=
      Matrix.rank_mul_le_left
        (output center reset) (outputRightInverse center reset)
    rw [output_mul_outputRightInverse center reset drift_ne_zero,
      Matrix.rank_one] at rank_bound
    norm_num at rank_bound ⊢
    exact rank_bound

/-- The physical cut has rank exactly two whenever its two projective parameters differ. -/
theorem cut_rank
    (center reset : ℚ) (drift_ne_zero : drift center reset ≠ 0) :
    (cut center reset).rank = 2 := by
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left input (output center reset)).trans
      (Matrix.rank_le_width input)
  · have output_factor :
        output center reset =
          inputLeftInverse * cut center reset := by
      calc
        output center reset =
            (1 : Square (Fin 2) ℚ) * output center reset := by simp
        _ = (inputLeftInverse * input) * output center reset :=
          (congrArg (fun matrix : Square (Fin 2) ℚ => matrix * output center reset)
            inputLeftInverse_mul_input).symm
        _ = inputLeftInverse * (input * output center reset) := Matrix.mul_assoc _ _ _
        _ = inputLeftInverse * cut center reset := rfl
    have lower : (output center reset).rank ≤ (cut center reset).rank := by
      rw [output_factor]
      exact Matrix.rank_mul_le_right inputLeftInverse (cut center reset)
    rw [output_rank center reset drift_ne_zero] at lower
    exact lower

/-- Every ambient return has the three-mode closed form. -/
theorem returnMatrix_eq_transfer
    (prime : ℚ) (depth : Nat) (center reset : ℚ) (wait : Nat) :
    returnAt prime depth center reset wait =
      transfer center reset ((prime⁻¹) ^ wait) ((prime ^ (depth - 1)) ^ wait) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [returnAt, ReturnFamily.returnMatrix, ambient, input, output, transfer,
      Matrix.diagonal_pow, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.diagonal_apply, Fin.sum_univ_succ]
  all_goals ring

/-- Determinant of one two-scale return. -/
theorem transfer_det {R : Type*} [CommRing R]
    (center reset low high : R) :
    (transfer center reset low high).det =
      drift center reset * high * (low - 1) := by
  rw [Matrix.det_fin_two]
  simp [transfer, drift]
  ring

/-- Zero wait is the internal rank-one separator. -/
theorem transfer_one {R : Type*} [CommRing R] (center reset : R) :
    transfer center reset 1 1 =
      Matrix.vecMulVec ![reset, 1] ![1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transfer, drift, Matrix.vecMulVec_apply]
  all_goals ring

/-- The zero return squares by its self-incidence scalar. -/
theorem transfer_one_sq {R : Type*} [CommRing R] (center reset : R) :
    transfer center reset 1 1 ^ 2 =
      (reset - 1) • transfer center reset 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transfer, drift, pow_two, Matrix.mul_apply,
      Matrix.smul_apply, Fin.sum_univ_succ]
  all_goals ring

/-- Nonzero base makes the ambient generator a unit. -/
theorem ambient_isUnit
    (prime : ℚ) (depth : Nat) (prime_ne_zero : prime ≠ 0) :
    IsUnit (ambient prime depth) := by
  apply (ambient prime depth).isUnit_iff_isUnit_det.mpr
  rw [ambient, Matrix.det_diagonal]
  apply isUnit_iff_ne_zero.mpr
  simp [Fin.prod_univ_succ, prime_ne_zero]

/-- Positive returns are units under the arithmetic nondegeneracy conditions. -/
theorem positiveTransfer_isUnit
    (prime : ℕ) (depth : Nat) (center reset : ℚ)
    (prime_two : 2 ≤ prime)
    (drift_ne_zero : drift center reset ≠ 0) (wait : Nat) :
    IsUnit (positiveTransfer (prime : ℚ) depth center reset wait) := by
  apply (positiveTransfer (prime : ℚ) depth center reset wait).isUnit_iff_isUnit_det.mpr
  rw [positiveTransfer, returnMatrix_eq_transfer, transfer_det]
  apply isUnit_iff_ne_zero.mpr
  refine mul_ne_zero (mul_ne_zero drift_ne_zero ?_) ?_
  · positivity
  · have power_gt_one : (1 : ℚ) < (prime : ℚ) ^ (wait + 1) := by
      have prime_gt_one : (1 : ℚ) < prime := by exact_mod_cast prime_two
      exact one_lt_pow₀ prime_gt_one (by omega)
    have inverse_power_lt_one :
        ((prime : ℚ)⁻¹) ^ (wait + 1) < 1 := by
      simpa [inv_pow] using inv_lt_one_of_one_lt₀ power_gt_one
    linarith

/-- Complete arbitrary-word normal form for the physical amalgamated pair. -/
theorem physical_isMortal_iff_positiveBridge
    (prime : ℕ) (depth : Nat) (center reset : ℚ)
    (prime_two : 2 ≤ prime)
    (drift_ne_zero : drift center reset ≠ 0) :
    IsMortal
        (ReturnFamily.pairGenerator
          (ambient (prime : ℚ) depth) (cut center reset)) ↔
      ∃ waits, positiveBridge (prime : ℚ) depth center reset waits = 0 := by
  change
    IsMortal
        (ReturnFamily.pairGenerator
          (ambient (prime : ℚ) depth) (input * output center reset)) ↔
      ∃ waits,
        bridgeScalar ![reset, 1] ![1, -1]
          (wordProduct
            (fun wait => ReturnFamily.returnMatrix
              (ambient (prime : ℚ) depth) input (output center reset) (wait + 1))
            waits) = 0
  exact ReturnFamily.pairGenerator_isMortal_iff_positiveBridge
      (ambient (prime : ℚ) depth) input (output center reset)
      inputLeftInverse (outputRightInverse center reset)
      ![reset, 1] ![1, -1]
      (ambient_isUnit (prime : ℚ) depth (by positivity))
      inputLeftInverse_mul_input
      (output_mul_outputRightInverse center reset drift_ne_zero)
      (by
        change returnAt (prime : ℚ) depth center reset 0 =
          Matrix.vecMulVec ![reset, 1] ![1, -1]
        rw [returnMatrix_eq_transfer]
        simpa using transfer_one (R := ℚ) center reset)
      (positiveTransfer_isUnit prime depth center reset
        prime_two drift_ne_zero)
      (by simp)
      (by simp)

/-- Closed rescaled return used by the projective guard. -/
theorem guardTransfer_eq
    (prime : ℚ) (depth : Nat) (center reset : ℚ) (wait : Nat)
    (prime_ne_zero : prime ≠ 0) (depth_positive : 0 < depth) :
    guardTransfer prime depth center reset wait =
      !![center + drift center reset * prime ^ (depth * wait),
          -center * prime ^ wait - drift center reset * prime ^ (depth * wait);
         1, -prime ^ wait] := by
  have reciprocal_power :
      prime ^ wait * (prime ^ wait)⁻¹ = 1 :=
    mul_inv_cancel₀ (pow_ne_zero wait prime_ne_zero)
  have prime_mul_expanding :
      prime * prime ^ (depth - 1) = prime ^ depth := by
    obtain ⟨tail, rfl⟩ := Nat.exists_eq_succ_of_ne_zero depth_positive.ne'
    simp [pow_succ']
  have expanding_power :
      prime ^ wait * (prime ^ (depth - 1)) ^ wait =
        prime ^ (depth * wait) := by
    calc
      prime ^ wait * (prime ^ (depth - 1)) ^ wait =
          (prime * prime ^ (depth - 1)) ^ wait := (mul_pow prime _ wait).symm
      _ = (prime ^ depth) ^ wait := by rw [prime_mul_expanding]
      _ = prime ^ (depth * wait) := (pow_mul prime depth wait).symm
  rw [guardTransfer, returnMatrix_eq_transfer]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transfer, Matrix.smul_apply]
  · calc
      prime ^ wait *
          (center * (prime ^ wait)⁻¹ +
            drift center reset * (prime ^ (depth - 1)) ^ wait) =
          center * (prime ^ wait * (prime ^ wait)⁻¹) +
            drift center reset *
              (prime ^ wait * (prime ^ (depth - 1)) ^ wait) := by ring
      _ = center + drift center reset * prime ^ (depth * wait) := by
        rw [reciprocal_power, expanding_power]
        ring
  · calc
      prime ^ wait *
          (-center - drift center reset * (prime ^ (depth - 1)) ^ wait) =
          -(center * prime ^ wait) -
            drift center reset *
              (prime ^ wait * (prime ^ (depth - 1)) ^ wait) := by ring
      _ = -(center * prime ^ wait) -
          drift center reset * prime ^ (depth * wait) := by rw [expanding_power]
  · exact reciprocal_power

theorem guardTransfer_det
    (prime : ℚ) (depth : Nat) (center reset : ℚ) (wait : Nat)
    (prime_ne_zero : prime ≠ 0) (depth_positive : 0 < depth) :
    (guardTransfer prime depth center reset wait).det =
      drift center reset * prime ^ (depth * wait) * (1 - prime ^ wait) := by
  rw [guardTransfer_eq prime depth center reset wait prime_ne_zero depth_positive,
    Matrix.det_fin_two]
  simp
  ring

/-- Rescaling a return by a nonzero power preserves its projective action. -/
theorem guardTransfer_isUnit
    (prime : ℕ) (depth : Nat) (center reset : ℚ)
    (prime_two : 2 ≤ prime) (depth_two : 2 ≤ depth)
    (drift_ne_zero : drift center reset ≠ 0) (wait : Nat) (wait_positive : 0 < wait) :
    IsUnit (guardTransfer (prime : ℚ) depth center reset wait) := by
  apply (guardTransfer (prime : ℚ) depth center reset wait).isUnit_iff_isUnit_det.mpr
  rw [guardTransfer_det (prime : ℚ) depth center reset wait
    (by positivity) (by omega)]
  apply isUnit_iff_ne_zero.mpr
  refine mul_ne_zero (mul_ne_zero drift_ne_zero (by positivity)) ?_
  have power_gt_one : (1 : ℚ) < (prime : ℚ) ^ wait := by
    exact one_lt_pow₀ (by exact_mod_cast prime_two) wait_positive.ne'
  linarith

/-- The affine chart of the guard return has the displayed numerator and denominator. -/
theorem guardTransfer_affine_coordinates
    (prime : ℚ) (depth : Nat) (center reset z : ℚ) (wait : Nat)
    (prime_ne_zero : prime ≠ 0) (depth_positive : 0 < depth) :
    guardTransfer prime depth center reset wait *ᵥ ProjectiveLine.ray (some z) =
      ![projectiveNumerator prime depth center reset wait z,
        projectiveDenominator prime wait z] := by
  rw [ProjectiveLine.mulVec_ray_some,
    guardTransfer_eq prime depth center reset wait prime_ne_zero depth_positive]
  ext i
  fin_cases i <;>
    simp [ProjectiveLine.numerator, ProjectiveLine.denominator,
      projectiveNumerator, projectiveDenominator]
  all_goals ring

/-- The verifier identity compares the center, target, and selected wait without division. -/
theorem projective_center_defect
    (prime : ℚ) (depth : Nat) (center reset z : ℚ) (wait : Nat) :
    projectiveNumerator prime depth center reset wait z -
        center * projectiveDenominator prime wait z =
      drift center reset * prime ^ (depth * wait) * (z - 1) := by
  simp [projectiveNumerator, projectiveDenominator]
  ring

/-- Away from the pole, the guard step is the center plus its exact verifier defect. -/
theorem projectiveValue_eq_center_add_defect
    (prime : ℚ) (depth : Nat) (center reset z : ℚ) (wait : Nat)
    (denominator_ne_zero : projectiveDenominator prime wait z ≠ 0) :
    projectiveNumerator prime depth center reset wait z /
        projectiveDenominator prime wait z =
      center +
        drift center reset * prime ^ (depth * wait) * (z - 1) /
          (z - prime ^ wait) := by
  have denominator_ne : z - prime ^ wait ≠ 0 := by
    simpa [projectiveDenominator] using denominator_ne_zero
  rw [projectiveDenominator] at denominator_ne_zero ⊢
  field_simp [denominator_ne]
  simp [projectiveNumerator]
  ring

/-- Away from the affine pole, the total projective action is the displayed rational map. -/
theorem projectiveStep_some
    (prime : ℚ) (depth : Nat) (center reset z : ℚ) (wait : Nat)
    (prime_ne_zero : prime ≠ 0) (depth_positive : 0 < depth)
    (denominator_ne_zero : projectiveDenominator prime wait z ≠ 0) :
    projectiveStep prime depth center reset wait (some z) =
      some
        (projectiveNumerator prime depth center reset wait z /
          projectiveDenominator prime wait z) := by
  have denominator_ne : z - prime ^ wait ≠ 0 := by
    simpa [projectiveDenominator] using denominator_ne_zero
  rw [projectiveStep, guardTransfer_eq
    prime depth center reset wait prime_ne_zero depth_positive]
  simp [ProjectiveLine.act, ProjectiveLine.denominator, ProjectiveLine.numerator,
    projectiveDenominator, projectiveNumerator]
  ring_nf
  simp [denominator_ne]

/-- The selected power of the base is exactly the affine pole. -/
theorem projectiveStep_pole
    (prime : ℚ) (depth : Nat) (center reset : ℚ) (wait : Nat)
    (prime_ne_zero : prime ≠ 0) (depth_positive : 0 < depth) :
    projectiveStep prime depth center reset wait (some (prime ^ wait)) = none := by
  rw [projectiveStep, guardTransfer_eq
    prime depth center reset wait prime_ne_zero depth_positive]
  simp [ProjectiveLine.act, ProjectiveLine.denominator]

/-- Infinity enters the finite residue ball centered at `center`. -/
theorem projectiveStep_infinity
    (prime : ℚ) (depth : Nat) (center reset : ℚ) (wait : Nat)
    (prime_ne_zero : prime ≠ 0) (depth_positive : 0 < depth) :
    projectiveStep prime depth center reset wait none =
      some (center + drift center reset * prime ^ (depth * wait)) := by
  rw [projectiveStep, guardTransfer_eq
    prime depth center reset wait prime_ne_zero depth_positive]
  simp [ProjectiveLine.act]

theorem reachableCertificate_det (prime : ℚ) (depth : Nat) :
    (reachableCertificate prime depth).det =
      prime ^ (depth - 1) - prime⁻¹ := by
  rw [Matrix.det_fin_three]
  simp [reachableCertificate]

theorem observableCertificate_det
    (prime : ℚ) (depth : Nat) (center reset : ℚ) :
    (observableCertificate prime depth center reset).det =
      center * drift center reset * (prime⁻¹ - 1) := by
  rw [Matrix.det_fin_three]
  simp [observableCertificate]
  ring

theorem coefficientPrefixRows_eq
    (prime : ℚ) (depth : Nat) (center reset : ℚ) :
    ReturnFamily.coefficientPrefixRows
        (ambient prime depth) (output center reset) leftIndex =
      observableCertificate prime depth center reset := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ReturnFamily.coefficientPrefixRows, leftIndex, ambient, output,
      observableCertificate, Matrix.diagonal_pow, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem coefficientSuffixColumns_eq (prime : ℚ) (depth : Nat) :
    ReturnFamily.coefficientSuffixColumns (ambient prime depth) input rightIndex =
      reachableCertificate prime depth := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ReturnFamily.coefficientSuffixColumns, rightIndex, ambient, input,
      reachableCertificate, Matrix.diagonal_pow, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.one_apply, Fin.sum_univ_succ]

/-- Nonsingular three-state coefficient Hankel certificate. -/
theorem coefficientHankel_det
    (prime : ℚ) (depth : Nat) (center reset : ℚ) :
    (ReturnFamily.finiteCoefficientHankel
      (ReturnFamily.returnMatrix (ambient prime depth) input (output center reset))
      leftIndex rightIndex).det =
        center * drift center reset * (prime⁻¹ - 1) *
          (prime ^ (depth - 1) - prime⁻¹) := by
  rw [ReturnFamily.finiteCoefficientHankel_factor,
    coefficientPrefixRows_eq, coefficientSuffixColumns_eq, Matrix.det_mul,
    observableCertificate_det, reachableCertificate_det]

/-- Every exact realization of this return series has at least three states. -/
theorem three_le_card_of_exact_realization
    {Big : Type*} [Fintype Big] [DecidableEq Big]
    (prime : ℚ) (depth : Nat) (center reset : ℚ)
    (otherAmbient : Square Big ℚ)
    (otherInput : Matrix Big (Fin 2) ℚ)
    (otherOutput : Matrix (Fin 2) Big ℚ)
    (exact :
      ∀ wait,
        ReturnFamily.returnMatrix otherAmbient otherInput otherOutput wait =
          returnAt prime depth center reset wait)
    (center_ne_zero : center ≠ 0)
    (drift_ne_zero : drift center reset ≠ 0)
    (prime_inv_ne_one : prime⁻¹ - 1 ≠ 0)
    (modes_distinct : prime ^ (depth - 1) - prime⁻¹ ≠ 0) :
    3 ≤ Fintype.card Big := by
  apply ReturnFamily.coefficientHankel_card_le
    otherAmbient otherInput otherOutput leftIndex rightIndex
  have section_eq :
      ReturnFamily.finiteCoefficientHankel
          (ReturnFamily.returnMatrix otherAmbient otherInput otherOutput)
          leftIndex rightIndex =
        ReturnFamily.finiteCoefficientHankel
          (ReturnFamily.returnMatrix
            (ambient prime depth) input (output center reset))
          leftIndex rightIndex := by
    ext i j
    simp only [ReturnFamily.finiteCoefficientHankel]
    rw [exact]
    rfl
  rw [section_eq, coefficientHankel_det]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero center_ne_zero drift_ne_zero) prime_inv_ne_one)
    modes_distinct

end

end MatrixMortality.ReturnGuard
