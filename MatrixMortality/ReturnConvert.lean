import MatrixMortality.ReturnSquare

/-!
# Two-scale return conversion

Replacing ReturnSquare's modes `(1,q,q²)` by independent modes `(1,p,q)` yields a return pencil
which converts the verified rail `pⁿ` to `qⁿ`. The zero-wait return remains an internal
rank-one separator, while two positive returns already exhibit zeros not explained by a
single-return resonance.
-/

namespace MatrixMortality.ReturnConvert

open scoped Matrix

/-- Three independent geometric modes. -/
def ambient {R : Type*} [CommRing R] (p q : R) : Square (Fin 3) R :=
  Matrix.diagonal ![1, p, q]

/-- ReturnSquare's split interface is independent of its ambient scales. -/
abbrev input {R : Type*} [CommRing R] : Matrix (Fin 3) (Fin 2) R :=
  ReturnSquare.input

/-- ReturnSquare's parameterized output interface. -/
abbrev output {R : Type*} [CommRing R] (c : R) : Matrix (Fin 2) (Fin 3) R :=
  ReturnSquare.output c

/-- Rank-at-most-two physical cut. -/
def cut {R : Type*} [CommRing R] (c : R) : Square (Fin 3) R :=
  input * output c

/-- Two-scale return with independent payload and verification scales. -/
def transfer {R : Type*} [CommRing R] (c p q : R) : Square (Fin 2) R :=
  !![(c + 1) * q - 1, p;
     c, p]

/-- Positive waits, indexed with physical wait `n+1`. -/
def positiveTransfer {R : Type*} [CommRing R]
    (p q c : R) (n : Nat) : Square (Fin 2) R :=
  transfer c (p ^ (n + 1)) (q ^ (n + 1))

/-- Scalar bridge between two zero-wait separators. -/
def positiveBridge (p q c : ℚ) (waits : List Nat) : ℚ :=
  bridgeScalar ![1, 1] ![c, 1] (wordProduct (positiveTransfer p q c) waits)

/-- Projective numerator on the affine chart `[z:1]`. -/
def projectiveNumerator {R : Type*} [CommRing R] (c p q z : R) : R :=
  ((c + 1) * q - 1) * z + p

/-- Projective denominator on the affine chart `[z:1]`. -/
def projectiveDenominator {R : Type*} [CommRing R] (c p z : R) : R :=
  c * z + p

/-- Three reachable columns: `input e₀`, its ambient image, and `input e₁`. -/
def reachableCertificate {R : Type*} [CommRing R] (q : R) : Square (Fin 3) R :=
  !![1, 1, 0;
     0, 0, 1;
     1, q, 0]

/-- Three observable rows: the first output row at waits zero, one, and two. -/
def observableCertificate {R : Type*} [CommRing R] (p q c : R) :
    Square (Fin 3) R :=
  !![-1, 1, c + 1;
     -1, p, q * (c + 1);
     -1, p ^ 2, q ^ 2 * (c + 1)]

/-- Coefficient rows selecting the first output coordinate at waits `0,1,2`. -/
def leftIndex : Fin 3 → Nat × Fin 2 :=
  ![(0, 0), (1, 0), (2, 0)]

/-- Coefficient columns selecting the first input coordinate at waits `0,1`, then the second
input coordinate at wait zero. -/
def rightIndex : Fin 3 → Nat × Fin 2 :=
  ![(0, 0), (1, 0), (0, 1)]

theorem cut_eq {R : Type*} [CommRing R] (c : R) :
    cut c = ReturnSquare.cut c := rfl

/-- Every ambient return has the two-scale closed form. -/
theorem returnMatrix_eq_transfer {R : Type*} [CommRing R]
    (p q c : R) (n : Nat) :
    ReturnFamily.returnMatrix (ambient p q) input (output c) n =
      transfer c (p ^ n) (q ^ n) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [ReturnFamily.returnMatrix, ambient, input, output, transfer,
      ReturnSquare.input, ReturnSquare.output,
      Matrix.diagonal_pow, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.diagonal_apply, Fin.sum_univ_succ]
  all_goals ring

/-- Determinant of one return. -/
theorem transfer_det {R : Type*} [CommRing R] (c p q : R) :
    (transfer c p q).det = (c + 1) * p * (q - 1) := by
  rw [Matrix.det_fin_two]
  simp [transfer]
  ring

/-- Every nondegenerate positive return is a unit. -/
theorem transfer_isUnit {K : Type*} [Field K] (c p q : K)
    (hc : c + 1 ≠ 0) (hp : p ≠ 0) (hq : q - 1 ≠ 0) :
    IsUnit (transfer c p q) := by
  apply (transfer c p q).isUnit_iff_isUnit_det.mpr
  rw [transfer_det]
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero hc hp) hq)

/-- Zero wait is the same rank-one separator as in ReturnSquare. -/
theorem transfer_one (R : Type*) [CommRing R] (c : R) :
    transfer c 1 1 = Matrix.vecMulVec ![1, 1] ![c, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transfer, Matrix.vecMulVec_apply]

/-- Separating wait zero from positive waits is the usual `Nat ≃ Option Nat` relabelling. -/
theorem separatedPositiveTransfer_comp_natEquivOption
    {R : Type*} [CommRing R] (p q c : R) :
    separatedGenerator (transfer c 1 1) (positiveTransfer p q c) ∘ natEquivOption =
      fun n => transfer c (p ^ n) (q ^ n) := by
  funext n
  cases n with
  | zero => simp [separatedGenerator]
  | succ n => simp [separatedGenerator, positiveTransfer]

private theorem two_le_pow_succ {q : ℤ} (hq : 2 ≤ q) (n : Nat) :
    2 ≤ q ^ (n + 1) := by
  rw [pow_succ]
  have one_le_power : 1 ≤ q ^ n := by
    have : 0 < q ^ n := pow_pos (by omega) n
    omega
  nlinarith [mul_le_mul_of_nonneg_right one_le_power (by omega : 0 ≤ q)]

/-- Every positive return is invertible at integral scales at least two. -/
theorem positiveTransfer_isUnit
    (p q : ℤ) (c : ℚ) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hc : c + 1 ≠ 0) (n : Nat) :
    IsUnit (positiveTransfer (p : ℚ) (q : ℚ) c n) := by
  apply transfer_isUnit
  · exact hc
  · positivity
  · have q_power : (2 : ℚ) ≤ (q : ℚ) ^ (n + 1) := by
      exact_mod_cast two_le_pow_succ hq n
    linarith

/-- Mortality of the complete return family is exactly one scalar bridge between zero waits. -/
theorem transferFamily_isMortal_iff_positiveBridge
    (p q : ℤ) (c : ℚ) :
    IsMortal (fun n => transfer c ((p : ℚ) ^ n) ((q : ℚ) ^ n)) ↔
      ∃ waits, positiveBridge (p : ℚ) (q : ℚ) c waits = 0 := by
  rw [← separatedPositiveTransfer_comp_natEquivOption]
  rw [isMortal_comp_equiv]
  rw [transfer_one]
  simpa [positiveBridge] using
    mortal_adjoin_outer_iff
      (positiveTransfer (p : ℚ) (q : ℚ) c) ![1, 1] ![c, 1]

/-- Determinant of the physical ambient matrix. -/
theorem ambient_det {K : Type*} [Field K] (p q : K) :
    (ambient p q).det = p * q := by
  simp [ambient, Matrix.det_diagonal, Fin.prod_univ_succ]

/-- Nonzero scales make the physical ambient generator a unit. -/
theorem ambient_isUnit {K : Type*} [Field K] (p q : K)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    IsUnit (ambient p q) := by
  apply (ambient p q).isUnit_iff_isUnit_det.mpr
  rw [ambient_det]
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero hp hq)

/-- Complete arbitrary-word normal form for the physical two-scale pair. -/
theorem physical_isMortal_iff_positiveBridge
    (p q : ℤ) (c : ℚ) (hp : p ≠ 0) (hq : q ≠ 0) (hc : c + 1 ≠ 0) :
    IsMortal (ReturnFamily.pairGenerator (ambient (p : ℚ) (q : ℚ)) (cut c)) ↔
      ∃ waits, positiveBridge (p : ℚ) (q : ℚ) c waits = 0 := by
  change
    IsMortal
        (ReturnFamily.pairGenerator (ambient (p : ℚ) (q : ℚ)) (input * output c)) ↔
      ∃ waits,
        bridgeScalar ![1, 1] ![c, 1]
          (wordProduct
            (fun wait => transfer c ((p : ℚ) ^ (wait + 1)) ((q : ℚ) ^ (wait + 1)))
            waits) = 0
  have reduction := ReturnFamily.pairGenerator_isMortal_iff_positiveBridge
      (ambient (p : ℚ) (q : ℚ)) input (output c)
      ReturnSquare.inputLeftInverse (ReturnSquare.outputRightInverse c)
      ![1, 1] ![c, 1]
      (ambient_isUnit (p : ℚ) (q : ℚ)
        (by exact_mod_cast hp) (by exact_mod_cast hq))
      ReturnSquare.inputLeftInverse_mul_input
      (ReturnSquare.output_mul_outputRightInverse c hc)
      (by
        rw [returnMatrix_eq_transfer]
        simpa using transfer_one ℚ c)
  constructor
  · intro mortal
    obtain ⟨waits, vanishes⟩ := reduction.mp mortal
    refine ⟨waits, ?_⟩
    simpa only [returnMatrix_eq_transfer] using vanishes
  · rintro ⟨waits, vanishes⟩
    apply reduction.mpr
    refine ⟨waits, ?_⟩
    simpa only [returnMatrix_eq_transfer] using vanishes

/-- Exact defect from the conversion rail `p ↦ q`. -/
theorem projective_rail_defect {R : Type*} [CommRing R] (c p q z : R) :
    projectiveNumerator c p q z - q * projectiveDenominator c p z =
      (q - 1) * (z - p) := by
  simp [projectiveNumerator, projectiveDenominator]
  ring

/-- The moving point `p` maps projectively to `q`. -/
theorem projective_rail {R : Type*} [CommRing R] (c p q : R) :
    projectiveNumerator c p q p = q * projectiveDenominator c p p := by
  exact sub_eq_zero.mp (by simpa using projective_rail_defect c p q p)

/-- Pullback of the terminal point is the two-scale incidence `c q z + p = 0`. -/
theorem projective_target_defect {R : Type*} [CommRing R] (c p q z : R) :
    c * projectiveNumerator c p q z + projectiveDenominator c p z =
      (c + 1) * (c * q * z + p) := by
  simp [projectiveNumerator, projectiveDenominator]
  ring

theorem reachableCertificate_det {R : Type*} [CommRing R] (q : R) :
    (reachableCertificate q).det = -(q - 1) := by
  rw [Matrix.det_fin_three]
  simp [reachableCertificate]
  ring

theorem observableCertificate_det {R : Type*} [CommRing R] (p q c : R) :
    (observableCertificate p q c).det =
      -(c + 1) * (p - 1) * (q - 1) * (q - p) := by
  rw [Matrix.det_fin_three]
  simp [observableCertificate]
  ring

theorem coefficientPrefixRows_eq {R : Type*} [CommRing R] (p q c : R) :
    ReturnFamily.coefficientPrefixRows (ambient p q) (output c) leftIndex =
      observableCertificate p q c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ReturnFamily.coefficientPrefixRows, leftIndex, ambient, output,
      observableCertificate, ReturnSquare.output, Matrix.diagonal_pow,
      Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply,
      Fin.sum_univ_succ]
  all_goals ring

theorem coefficientSuffixColumns_eq {R : Type*} [CommRing R] (p q : R) :
    ReturnFamily.coefficientSuffixColumns (ambient p q) input rightIndex =
      reachableCertificate q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ReturnFamily.coefficientSuffixColumns, rightIndex, ambient, input,
      reachableCertificate, ReturnSquare.input, Matrix.diagonal_pow,
      Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply,
      Fin.sum_univ_succ]

/-- A `3 × 3` coefficient Hankel section is nonsingular exactly under the expected
nondegeneracy factors. -/
theorem coefficientHankel_det {R : Type*} [CommRing R] (p q c : R) :
    (ReturnFamily.finiteCoefficientHankel
      (ReturnFamily.returnMatrix (ambient p q) input (output c))
      leftIndex rightIndex).det =
        (c + 1) * (p - 1) * (q - 1) ^ 2 * (q - p) := by
  rw [ReturnFamily.finiteCoefficientHankel_factor,
    coefficientPrefixRows_eq, coefficientSuffixColumns_eq, Matrix.det_mul,
    observableCertificate_det, reachableCertificate_det]
  ring

/-- Every exact realization of the two-scale return series has at least three states. -/
theorem three_le_card_of_exact_realization
    {K Big : Type*} [Field K] [Fintype Big] [DecidableEq Big]
    (p q c : K)
    (otherAmbient : Square Big K)
    (otherInput : Matrix Big (Fin 2) K)
    (otherOutput : Matrix (Fin 2) Big K)
    (exact :
      ∀ n,
        ReturnFamily.returnMatrix otherAmbient otherInput otherOutput n =
          transfer c (p ^ n) (q ^ n))
    (hc : c + 1 ≠ 0) (hp : p - 1 ≠ 0)
    (hq : q - 1 ≠ 0) (scales_distinct : q - p ≠ 0) :
    3 ≤ Fintype.card Big := by
  apply ReturnFamily.coefficientHankel_card_le
    otherAmbient otherInput otherOutput leftIndex rightIndex
  have section_eq :
      ReturnFamily.finiteCoefficientHankel
          (ReturnFamily.returnMatrix otherAmbient otherInput otherOutput)
          leftIndex rightIndex =
        ReturnFamily.finiteCoefficientHankel
          (ReturnFamily.returnMatrix (ambient p q) input (output c))
          leftIndex rightIndex := by
    ext i j
    simp only [ReturnFamily.finiteCoefficientHankel]
    rw [exact, returnMatrix_eq_transfer]
  rw [section_eq, coefficientHankel_det]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero hc hp) (pow_ne_zero 2 hq))
    scales_distinct

/-- Closed form of the scalar bridge across two arbitrary positive scales. -/
theorem twoReturn_coefficient {R : Type*} [CommRing R]
    (c p₁ q₁ p₂ q₂ : R) :
    ![c, 1] ⬝ᵥ transfer c p₁ q₁ *ᵥ (transfer c p₂ q₂ *ᵥ ![1, 1]) =
      (c + 1) *
        (q₁ * q₂ * c ^ 2 +
          (q₁ * q₂ + q₁ * p₂ - q₁ + p₁) * c +
          p₁ * p₂) := by
  simp [transfer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- Two physical waits `n,m` produce the displayed quadratic bridge polynomial. -/
theorem twoWait_coefficient {R : Type*} [CommRing R]
    (c p q : R) (n m : Nat) :
    ![c, 1] ⬝ᵥ transfer c (p ^ n) (q ^ n) *ᵥ
        (transfer c (p ^ m) (q ^ m) *ᵥ ![1, 1]) =
      (c + 1) *
        (q ^ (n + m) * c ^ 2 +
          (q ^ (n + m) + q ^ n * p ^ m - q ^ n + p ^ n) * c +
          p ^ (n + m)) := by
  rw [twoReturn_coefficient]
  ring_nf

/-- The concrete two-scale family found by the search. -/
def exampleAmbient : Square (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 3, 0;
     0, 0, 6]

/-- Integral scaling of the cut at `c=-1/9`. -/
def exampleCut : Square (Fin 3) ℤ :=
  !![-9, 9, 8;
     -1, 9, 0;
     -9, 9, 8]

/-- A genuine two-return zero: neither positive return is itself singular. -/
theorem example_zero :
    exampleCut ^ 2 * exampleAmbient * exampleCut *
        exampleAmbient ^ 2 * exampleCut ^ 2 =
      0 := by
  simp only [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [exampleAmbient, exampleCut, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The example's central positive returns are invertible over `ℚ`. -/
theorem example_positive_returns_are_units :
    IsUnit (transfer (-1 / 9 : ℚ) 3 6) ∧
      IsUnit (transfer (-1 / 9 : ℚ) (3 ^ 2) (6 ^ 2)) := by
  constructor <;> apply transfer_isUnit <;> norm_num

/-- The two-return zero is not a one-return resonance. -/
theorem example_nonresonant (n : Nat) :
    (-1 / 9 : ℚ) ≠ -(3 / 6 : ℚ) ^ n := by
  intro resonance
  rw [show (3 / 6 : ℚ) = 1 / 2 by norm_num] at resonance
  have positive : (1 / 9 : ℚ) = (1 / 2) ^ n := by linarith
  have inverse_eq : (9 : ℚ)⁻¹ = ((2 : ℚ) ^ n)⁻¹ := by
    simpa only [one_div, inv_pow] using positive
  have power_eq : (2 : ℚ) ^ n = 9 := (inv_injective inverse_eq).symm
  have power_eq_nat : (2 : ℕ) ^ n = 9 := by
    exact_mod_cast power_eq
  cases n with
  | zero => norm_num at power_eq_nat
  | succ n =>
      have even_power : 2 ∣ (2 : ℕ) ^ (n + 1) := by
        refine ⟨2 ^ n, ?_⟩
        simp [pow_succ, Nat.mul_comm]
      have : 2 ∣ (9 : ℕ) := by
        rw [← power_eq_nat]
        exact even_power
      norm_num at this

end MatrixMortality.ReturnConvert
