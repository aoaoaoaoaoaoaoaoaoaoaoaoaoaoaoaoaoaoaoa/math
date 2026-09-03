import MatrixMortality.ReturnFamily
import MatrixMortality.TerminalTile
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# ReturnSquare

This file owns the exact algebra of the rank-`(3,2)` ReturnSquare family. The parameterized
identities are proved over the weakest useful scalar structures; mortality statements add field,
nondegeneracy, and order hypotheses only where they are used.
-/

namespace MatrixMortality

open scoped Matrix

/-- An integral quadratic with nonsquare discriminant has no rational root. -/
theorem rationalQuadratic_ne_zero_of_discriminant_not_isSquare
    (a b d : ℤ) (h : ¬IsSquare (discrim a b d)) (x : ℚ) :
    (a : ℚ) * x ^ 2 + (b : ℚ) * x + (d : ℚ) ≠ 0 := by
  have hnonsquare :
      ∀ s : ℚ, discrim (a : ℚ) (b : ℚ) (d : ℚ) ≠ s ^ 2 := by
    intro s hs
    apply h
    rw [← Rat.isSquare_intCast_iff]
    refine ⟨s, ?_⟩
    simpa [discrim, pow_two] using hs
  intro hzero
  apply quadratic_ne_zero_of_discrim_ne_sq hnonsquare x
  simpa [pow_two, mul_assoc] using hzero

namespace ReturnSquare

/-- Invertible ambient generator with three geometric modes. -/
def ambient {R : Type*} [CommRing R] (q : R) : Square (Fin 3) R :=
  Matrix.diagonal ![1, q, q ^ 2]

/-- Split inclusion of the two-dimensional return interface. -/
def input {R : Type*} [CommRing R] : Matrix (Fin 3) (Fin 2) R :=
  !![1, 0;
     0, 1;
     1, 0]

/-- Split projection carrying the ReturnSquare parameter. -/
def output {R : Type*} [CommRing R] (c : R) : Matrix (Fin 2) (Fin 3) R :=
  !![-1, 1, c + 1;
     c, 1, 0]

/-- The rank-at-most-two physical cut. -/
def cut {R : Type*} [CommRing R] (c : R) : Square (Fin 3) R :=
  input * output c

/-- Closed form of the return `output c * ambient q ^ n * input`, with `t=q^n`. -/
def transfer {R : Type*} [CommRing R] (c t : R) : Square (Fin 2) R :=
  !![(c + 1) * t ^ 2 - 1, t;
     c, t]

/-- Positive-wait return family, indexed with wait `n+1` at label `n`. -/
def positiveTransfer {R : Type*} [CommRing R] (q c : R) (n : Nat) : Square (Fin 2) R :=
  transfer c (q ^ (n + 1))

/-- Scalar bridge cut out by two zero-wait returns. -/
def positiveBridge (q c : ℚ) (waits : List Nat) : ℚ :=
  bridgeScalar ![1, 1] ![c, 1] (wordProduct (positiveTransfer q c) waits)

/-- Numerator of the projective action of one return on the affine chart `[z:1]`. -/
def projectiveNumerator {R : Type*} [CommRing R] (c t z : R) : R :=
  ((c + 1) * t ^ 2 - 1) * z + t

/-- Denominator of the projective action of one return on the affine chart `[z:1]`. -/
def projectiveDenominator {R : Type*} [CommRing R] (c t z : R) : R :=
  c * z + t

/-- Partial affine-chart action of a return matrix. Cross-multiplied theorems below remain valid
at its pole and should be preferred whenever division is unnecessary. -/
def projectiveStep {K : Type*} [Field K] (c t z : K) : K :=
  projectiveNumerator c t z / projectiveDenominator c t z

/-- Scale appearing in the negative-parameter projective chart. -/
def trapScale {R : Type*} [Ring R] (d t : R) : R :=
  (d - 1) * t ^ 2 + 1

/-- Uniform projective trap bound for all return scales at least `q`. -/
def trapBound {K : Type*} [Field K] (d q : K) : K :=
  q / trapScale d q

/-- Projective action of `transfer (-d) t`, exposed without the sign substitution. -/
def negativeStep {K : Type*} [Field K] (d t z : K) : K :=
  (t - trapScale d t * z) / (t - d * z)

/-- The scale-invariant double cone represented by the affine interval `(0, β]`. -/
def signedTrap (β x y : ℚ) : Prop :=
  (0 < x ∧ 0 < y ∧ x ≤ β * y) ∨
    (x < 0 ∧ y < 0 ∧ β * y ≤ x)

/-- Left inverse of `input`. -/
def inputLeftInverse {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 3) R :=
  !![1, 0, 0;
     0, 1, 0]

/-- Right inverse of `output c` when `c+1` is invertible. -/
def outputRightInverse {K : Type*} [Field K] (c : K) : Matrix (Fin 3) (Fin 2) K :=
  !![-(c + 1)⁻¹, (c + 1)⁻¹;
     c * (c + 1)⁻¹, (c + 1)⁻¹;
     0, 0]

/-- Three reachable columns: the first input column, its ambient image, and the second input
column. -/
def reachableCertificate {R : Type*} [CommRing R] (q : R) : Square (Fin 3) R :=
  !![1, 1, 0;
     0, 0, 1;
     1, q ^ 2, 0]

/-- Three observable rows: the first output row after zero, one, and two ambient steps. -/
def observableCertificate {R : Type*} [CommRing R] (q c : R) : Square (Fin 3) R :=
  !![-1, 1, c + 1;
     -1, q, q ^ 2 * (c + 1);
     -1, q ^ 2, q ^ 4 * (c + 1)]

/-- The physical cut has the advertised closed form. -/
theorem cut_eq {R : Type*} [CommRing R] (c : R) :
    cut c =
      !![-1, 1, c + 1;
         c, 1, 0;
         -1, 1, c + 1] := by
  ext i j
  change (∑ index, input i index * output c index j) = _
  fin_cases i <;> fin_cases j <;>
    simp [input, output, Fin.sum_univ_succ]

/-- `input` is split over every commutative ring. -/
theorem inputLeftInverse_mul_input {R : Type*} [CommRing R] :
    (inputLeftInverse : Matrix (Fin 2) (Fin 3) R) *
      (input : Matrix (Fin 3) (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [inputLeftInverse, input, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ]

/-- The displayed rational right inverse splits `output c` away from `c=-1`. -/
theorem output_mul_outputRightInverse {K : Type*} [Field K]
    (c : K) (c_add_one_ne : c + 1 ≠ 0) :
    output c * outputRightInverse c = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [output, outputRightInverse, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ]
  all_goals field_simp
  all_goals ring

/-- Reachability witness determinant. -/
theorem reachableCertificate_det {R : Type*} [CommRing R] (q : R) :
    (reachableCertificate q).det = -(q - 1) * (q + 1) := by
  rw [Matrix.det_fin_three]
  simp [reachableCertificate]
  ring

/-- Observability witness determinant. -/
theorem observableCertificate_det {R : Type*} [CommRing R] (q c : R) :
    (observableCertificate q c).det =
      -q * (c + 1) * (q - 1) ^ 3 * (q + 1) := by
  rw [Matrix.det_fin_three]
  simp [observableCertificate]
  ring

/-- Every ambient return has the two-state closed form `transfer c (q^n)`. -/
theorem returnMatrix_eq_transfer {R : Type*} [CommRing R]
    (q c : R) (n : Nat) :
    ReturnFamily.returnMatrix (ambient q) input (output c) n =
      transfer c (q ^ n) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [ReturnFamily.returnMatrix, ambient, input, output, transfer,
      Matrix.diagonal_pow, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.diagonal_apply, Fin.sum_univ_succ]
  all_goals ring

/-- Determinant of one return. -/
theorem transfer_det {R : Type*} [CommRing R] (c t : R) :
    (transfer c t).det = (c + 1) * t * (t ^ 2 - 1) := by
  rw [Matrix.det_fin_two]
  simp [transfer]
  ring

/-- A nondegenerate return is a unit. -/
theorem transfer_isUnit {K : Type*} [Field K] (c t : K)
    (hc : c + 1 ≠ 0) (ht : t ≠ 0) (ht_sq : t ^ 2 - 1 ≠ 0) :
    IsUnit (transfer c t) := by
  apply (transfer c t).isUnit_iff_isUnit_det.mpr
  rw [transfer_det]
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero hc ht) ht_sq)

/-- The zero-wait return is rank-one algebraically. -/
theorem transfer_one (R : Type*) [CommRing R] (c : R) :
    transfer c 1 = Matrix.vecMulVec ![1, 1] ![c, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transfer, Matrix.vecMulVec_apply]

/-- Any return whose scale squares to one collapses to rank at most one. This is the algebraic
core of every cyclotomic finite-quotient wall. -/
theorem transfer_eq_outer_of_sq_eq_one {R : Type*} [CommRing R] (c t : R)
    (ht : t ^ 2 = 1) :
    transfer c t = Matrix.vecMulVec ![1, 1] ![c, t] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transfer, Matrix.vecMulVec_apply, ht]

/-- Separating wait zero from positive waits merely relabels the return family. -/
theorem separatedPositiveTransfer_comp_natEquivOption
    {R : Type*} [CommRing R] (q c : R) :
    separatedGenerator (transfer c 1) (positiveTransfer q c) ∘ natEquivOption =
      fun n => transfer c (q ^ n) := by
  funext n
  cases n with
  | zero => simp [separatedGenerator]
  | succ n => simp [separatedGenerator, positiveTransfer]

/-- Every return sends projective zero to projective one, before division. -/
theorem projective_reset {R : Type*} [CommRing R] (c t : R) :
    projectiveNumerator c t 0 = projectiveDenominator c t 0 := by
  simp [projectiveNumerator, projectiveDenominator]

/-- The moving point `t` lies on the squaring rail: its image is `t²`. -/
theorem projective_rail {R : Type*} [CommRing R] (c t : R) :
    projectiveNumerator c t t = t ^ 2 * projectiveDenominator c t t := by
  simp [projectiveNumerator, projectiveDenominator]
  ring

/-- Exact defect from the squaring rail, independent of the parameter `c`. -/
theorem projective_rail_defect {R : Type*} [CommRing R] (c t z : R) :
    projectiveNumerator c t z - t ^ 2 * projectiveDenominator c t z =
      (z - t) * (t ^ 2 - 1) := by
  simp [projectiveNumerator, projectiveDenominator]
  ring

/-- Pulling back the target `-1/c` leaves the one-dimensional strip `ctz+1=0`. -/
theorem projective_target_defect {R : Type*} [CommRing R] (c t z : R) :
    c * projectiveNumerator c t z + projectiveDenominator c t z =
      t * (c + 1) * (c * t * z + 1) := by
  simp [projectiveNumerator, projectiveDenominator]
  ring

/-- Negative parameters expose the projective action as `negativeStep`. -/
theorem projectiveStep_neg (d t z : ℚ) :
    projectiveStep (-d) t z = negativeStep d t z := by
  simp [projectiveStep, projectiveNumerator, projectiveDenominator, negativeStep,
    trapScale]
  ring

/-- Arithmetic specification of the uniform negative-parameter trap. -/
theorem trapBound_spec (d q t : ℚ) (q_at_least_two : 2 ≤ q)
    (scale_at_least_base : q ≤ t)
    (beyond_wall : 1 + (q - 1) / q ^ 2 < d) :
    0 < trapBound d q ∧
      trapBound d q < 1 ∧
      d < trapScale d t ∧
      0 < trapScale d t ∧
      t / trapScale d t ≤ trapBound d q ∧
      1 < trapBound d q * d * t := by
  have q_pos : 0 < q := by linarith
  have q_sq_pos : 0 < q ^ 2 := sq_pos_of_pos q_pos
  have d_gt_one : 1 < d := by
    have ratio_nonneg : 0 ≤ (q - 1) / q ^ 2 :=
      div_nonneg (by linarith) (sq_nonneg q)
    linarith
  have d_pos : 0 < d := by linarith
  have threshold : q - 1 < (d - 1) * q ^ 2 := by
    have shifted_wall : (q - 1) / q ^ 2 < d - 1 := by linarith
    exact (div_lt_iff₀ q_sq_pos).mp shifted_wall
  have scale_q_pos : 0 < trapScale d q := by
    unfold trapScale
    nlinarith [sq_nonneg q]
  have scale_t_pos : 0 < trapScale d t := by
    unfold trapScale
    nlinarith [sq_nonneg t]
  have bound_pos : 0 < trapBound d q := div_pos q_pos scale_q_pos
  have bound_lt_one : trapBound d q < 1 := by
    rw [trapBound, div_lt_one scale_q_pos]
    unfold trapScale
    linarith
  have t_sq_ge : q ^ 2 ≤ t ^ 2 := by nlinarith
  have scale_mono : trapScale d q ≤ trapScale d t := by
    unfold trapScale
    nlinarith [t_sq_ge]
  have scale_q_gt_d : d < trapScale d q := by
    unfold trapScale
    have q_sq_gt_one : 1 < q ^ 2 := by nlinarith
    nlinarith
  have scale_t_gt_d : d < trapScale d t :=
    lt_of_lt_of_le scale_q_gt_d scale_mono
  have zero_le_bound : t / trapScale d t ≤ trapBound d q := by
    rw [trapBound]
    apply (div_le_div_iff₀ scale_t_pos scale_q_pos).mpr
    have factorization :
        q * trapScale d t - t * trapScale d q =
          (t - q) * ((d - 1) * q * t - 1) := by
      unfold trapScale
      ring
    have first_factor_nonneg : 0 ≤ t - q := by linarith
    have second_factor_nonneg : 0 ≤ (d - 1) * q * t - 1 := by
      have : 1 < (d - 1) * q * t := by
        nlinarith [threshold]
      linarith
    nlinarith [factorization, mul_nonneg first_factor_nonneg second_factor_nonneg]
  have bound_dt_gt_one : 1 < trapBound d q * d * t := by
    have q_sq_lt_qdt : trapScale d q < q * d * t := by
      have q_sq_le_qt : q ^ 2 ≤ q * t := by nlinarith
      have d_q_sq_le : d * q ^ 2 ≤ d * (q * t) :=
        mul_le_mul_of_nonneg_left q_sq_le_qt d_pos.le
      have d_qt_eq : d * (q * t) = q * d * t := by ring
      rw [d_qt_eq] at d_q_sq_le
      have q_sq_gt_one : 1 < q ^ 2 := by nlinarith
      calc
        trapScale d q = d * q ^ 2 - (q ^ 2 - 1) := by
          unfold trapScale
          ring
        _ < d * q ^ 2 := sub_lt_self _ (sub_pos.mpr q_sq_gt_one)
        _ ≤ q * d * t := d_q_sq_le
    have normalize :
        trapBound d q * d * t = (q * d * t) / trapScale d q := by
      unfold trapBound
      ring
    rw [normalize, one_lt_div scale_q_pos]
    exact q_sq_lt_qdt
  exact ⟨bound_pos, bound_lt_one, scale_t_gt_d, scale_t_pos, zero_le_bound,
    bound_dt_gt_one⟩

/-- The interval `(0, trapBound d q]` is backward invariant under every negative-parameter
return whose scale is at least `q`. -/
theorem negativeStep_preimage_trap (d q t z : ℚ) (q_at_least_two : 2 ≤ q)
    (scale_at_least_base : q ≤ t)
    (beyond_wall : 1 + (q - 1) / q ^ 2 < d)
    (image_pos : 0 < negativeStep d t z)
    (image_bounded : negativeStep d t z ≤ trapBound d q) :
    0 < z ∧ z ≤ trapBound d q := by
  have t_pos : 0 < t := by linarith
  have d_gt_one : 1 < d := by
    have ratio_nonneg : 0 ≤ (q - 1) / q ^ 2 :=
      div_nonneg (by linarith) (sq_nonneg q)
    linarith
  have d_pos : 0 < d := by linarith
  obtain ⟨_, bound_lt_one, scale_t_gt_d, scale_t_pos, zero_le_bound, _⟩ :=
    trapBound_spec d q t q_at_least_two scale_at_least_base beyond_wall
  let denominator := t - d * z
  let numerator := t - trapScale d t * z
  have image_eq : negativeStep d t z = numerator / denominator := by rfl
  rw [image_eq] at image_pos image_bounded
  rcases (div_pos_iff.mp image_pos) with signs | signs
  · have numerator_pos : 0 < numerator := signs.1
    have denominator_pos : 0 < denominator := signs.2
    have z_upper : z < t / trapScale d t := by
      rw [lt_div_iff₀ scale_t_pos]
      have : trapScale d t * z < t := sub_pos.mp numerator_pos
      simpa [mul_comm] using this
    have z_bounded : z ≤ trapBound d q := z_upper.le.trans zero_le_bound
    have cross :
        numerator ≤ trapBound d q * denominator :=
      (div_le_iff₀ denominator_pos).mp image_bounded
    have coefficient_pos :
        0 < trapScale d t - d * trapBound d q := by
      have : d * trapBound d q < d := by
        simpa using mul_lt_mul_of_pos_left bound_lt_one d_pos
      linarith
    have left_pos : 0 < t * (1 - trapBound d q) :=
      mul_pos t_pos (sub_pos.mpr bound_lt_one)
    have z_pos : 0 < z := by
      have identity :
          t * (1 - trapBound d q) -
                (trapScale d t - d * trapBound d q) * z =
              numerator - trapBound d q * denominator := by
        dsimp [numerator, denominator]
        ring
      by_contra not_pos
      have z_nonpos : z ≤ 0 := le_of_not_gt not_pos
      have right_nonpos :
          (trapScale d t - d * trapBound d q) * z ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos coefficient_pos.le z_nonpos
      linarith
    exact ⟨z_pos, z_bounded⟩
  · have denominator_neg : denominator < 0 := signs.2
    have z_pos : 0 < z := by
      by_contra not_pos
      have z_nonpos : z ≤ 0 := le_of_not_gt not_pos
      have dz_nonpos : d * z ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos d_pos.le z_nonpos
      dsimp [denominator] at denominator_neg
      linarith
    have numerator_lt_denominator : numerator < denominator := by
      have identity :
          numerator - denominator = -(trapScale d t - d) * z := by
        dsimp [numerator, denominator]
        ring
      apply sub_neg.mp
      rw [identity]
      have coefficient_neg : -(trapScale d t - d) < 0 :=
        neg_neg_of_pos (sub_pos.mpr scale_t_gt_d)
      exact mul_neg_of_neg_of_pos coefficient_neg z_pos
    have one_lt_image : 1 < numerator / denominator :=
      (lt_div_iff_of_neg denominator_neg).mpr (by
        simpa using numerator_lt_denominator)
    linarith

/-- Oriented cone form of the projective trap: positivity and the uniform slope bound pull back
through one negative-parameter return. -/
theorem positiveTrap_preimage
    (d q t x y : ℚ) (q_at_least_two : 2 ≤ q) (scale_at_least_base : q ≤ t)
    (beyond_wall : 1 + (q - 1) / q ^ 2 < d)
    (first_image_pos : 0 < t * y - trapScale d t * x)
    (second_image_pos : 0 < t * y - d * x)
    (image_bounded :
      t * y - trapScale d t * x ≤
        trapBound d q * (t * y - d * x)) :
    0 < x ∧ 0 < y ∧ x ≤ trapBound d q * y := by
  obtain ⟨_, bound_lt_one, scale_gt_d, scale_pos, scale_ratio_bounded, _⟩ :=
    trapBound_spec d q t q_at_least_two scale_at_least_base beyond_wall
  have first_lt_second :
      t * y - trapScale d t * x < t * y - d * x := by
    have :
        trapBound d q * (t * y - d * x) <
          t * y - d * x := by
      simpa using mul_lt_mul_of_pos_right bound_lt_one second_image_pos
    exact lt_of_le_of_lt image_bounded this
  have x_pos : 0 < x := by
    have gap :
        (t * y - d * x) - (t * y - trapScale d t * x) =
          (trapScale d t - d) * x := by ring
    have product_pos : 0 < (trapScale d t - d) * x := by
      rw [← gap]
      linarith
    rcases mul_pos_iff.mp product_pos with ⟨_, positive⟩ | ⟨scale_neg, _⟩
    · exact positive
    · exact (not_lt_of_ge (sub_nonneg.mpr scale_gt_d.le) scale_neg).elim
  have y_pos : 0 < y := by
    have d_pos : 0 < d := by
      have ratio_nonneg : 0 ≤ (q - 1) / q ^ 2 :=
        div_nonneg (by linarith) (sq_nonneg q)
      nlinarith
    have dx_pos : 0 < d * x := mul_pos d_pos x_pos
    have dx_lt_ty : d * x < t * y := sub_pos.mp second_image_pos
    have t_pos : 0 < t := by linarith
    have ty_pos : 0 < t * y := dx_pos.trans dx_lt_ty
    rcases mul_pos_iff.mp ty_pos with ⟨_, positive⟩ | ⟨t_neg, _⟩
    · exact positive
    · exact (not_lt_of_ge t_pos.le t_neg).elim
  have x_lt_scale_ratio : x < (t / trapScale d t) * y := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ scale_pos]
    nlinarith
  have scale_ratio_le_bound :
      (t / trapScale d t) * y ≤ trapBound d q * y :=
    mul_le_mul_of_nonneg_right scale_ratio_bounded y_pos.le
  exact ⟨x_pos, y_pos, (x_lt_scale_ratio.trans_le scale_ratio_le_bound).le⟩

/-- The double projective trap is backward invariant, independently of homogeneous sign. -/
theorem transfer_neg_preimage_signedTrap
    (d q t x y : ℚ) (q_at_least_two : 2 ≤ q) (scale_at_least_base : q ≤ t)
    (beyond_wall : 1 + (q - 1) / q ^ 2 < d)
    (image_trapped :
      signedTrap (trapBound d q)
        (t * y - trapScale d t * x)
        (t * y - d * x)) :
    signedTrap (trapBound d q) x y := by
  rcases image_trapped with positive | negative
  · exact Or.inl (positiveTrap_preimage d q t x y q_at_least_two scale_at_least_base
      beyond_wall positive.1 positive.2.1 positive.2.2)
  · right
    have pulled := positiveTrap_preimage d q t (-x) (-y) q_at_least_two
      scale_at_least_base beyond_wall
      (by linarith [negative.1])
      (by linarith [negative.2.1])
      (by linarith [negative.2.2])
    rcases pulled with ⟨x_neg, y_neg, bounded⟩
    exact ⟨by linarith, by linarith, by linarith⟩

/-- The affine-chart action really is the ratio of `transfer c t * [z,1]`. -/
theorem transfer_mulVec_chart {R : Type*} [CommRing R] (c t z : R) :
    transfer c t *ᵥ ![z, 1] =
      ![projectiveNumerator c t z, projectiveDenominator c t z] := by
  ext i
  fin_cases i <;>
    simp [transfer, projectiveNumerator, projectiveDenominator, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]

/-- Matrix form of backward invariance of the signed trap. -/
theorem transfer_neg_preimage_signedTrap_mulVec
    (d q t : ℚ) (v : Fin 2 → ℚ) (q_at_least_two : 2 ≤ q)
    (scale_at_least_base : q ≤ t)
    (beyond_wall : 1 + (q - 1) / q ^ 2 < d)
    (image_trapped :
      signedTrap (trapBound d q)
        (Matrix.mulVec (transfer (-d) t) v 0)
        (Matrix.mulVec (transfer (-d) t) v 1)) :
    signedTrap (trapBound d q) (v 0) (v 1) := by
  have first_coordinate :
      Matrix.mulVec (transfer (-d) t) v 0 =
        t * v 1 - trapScale d t * v 0 := by
    simp [transfer, trapScale, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  have second_coordinate :
      Matrix.mulVec (transfer (-d) t) v 1 = t * v 1 - d * v 0 := by
    simp [transfer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  rw [first_coordinate, second_coordinate] at image_trapped
  exact transfer_neg_preimage_signedTrap d q t (v 0) (v 1) q_at_least_two
    scale_at_least_base beyond_wall image_trapped

/-- Row collapse responsible for the family's rigid one-dimensional target strip. -/
theorem covector_collapse {R : Type*} [CommRing R] (c t : R) :
    ![c, 1] ᵥ* transfer c t = ((c + 1) * t) • ![c * t, 1] := by
  ext i
  fin_cases i <;>
    simp [transfer, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;>
    ring

/-- One positive return has a completely factored acceptance coefficient. -/
theorem oneReturn_coefficient {R : Type*} [CommRing R] (c t : R) :
    ![c, 1] ⬝ᵥ transfer c t *ᵥ ![1, 1] =
      (c + 1) * t * (c * t + 1) := by
  simp [transfer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- The irreducible quadratic core of a two-return acceptance coefficient. -/
def twoReturnCore {R : Type*} [CommRing R] (c x y : R) : R :=
  x ^ 2 * y * c ^ 2 + (x ^ 2 * y + x * y - y + 1) * c + x

/-- Leading coefficient of the two-return quadratic. -/
def twoReturnLeading {R : Type*} [CommRing R] (x y : R) : R :=
  x ^ 2 * y

/-- Linear coefficient of the two-return quadratic. -/
def twoReturnLinear {R : Type*} [CommRing R] (x y : R) : R :=
  x ^ 2 * y + x * y - y + 1

/-- Discriminant of the two-return quadratic. -/
def twoReturnDiscriminant {R : Type*} [CommRing R] (x y : R) : R :=
  discrim (twoReturnLeading x y) (twoReturnLinear x y) x

/-- Lower endpoint of the two-return discriminant's two-square cage. -/
def twoReturnFence {R : Type*} [CommRing R] (x y : R) : R :=
  twoReturnLinear x y - 2 * x

/-- Two positive returns reduce to one quadratic Diophantine obstruction. -/
theorem twoReturn_coefficient {R : Type*} [CommRing R] (c x y : R) :
    ![c, 1] ⬝ᵥ transfer c y *ᵥ (transfer c x *ᵥ ![1, 1]) =
      y * (c + 1) * twoReturnCore c x y := by
  simp [transfer, twoReturnCore, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- Exact gap above the lower square in the discriminant cage. -/
theorem twoReturnDiscriminant_sub_fence_sq {R : Type*} [CommRing R] (x y : R) :
    twoReturnDiscriminant x y - twoReturnFence x y ^ 2 =
      4 * x * (x - 1) * (y - 1) := by
  simp [twoReturnDiscriminant, twoReturnFence, twoReturnLeading, twoReturnLinear,
    discrim]
  ring

/-- Exact gap below the upper square in the discriminant cage. -/
theorem fence_add_two_sq_sub_twoReturnDiscriminant
    {R : Type*} [CommRing R] (x y : R) :
    (twoReturnFence x y + 2) ^ 2 - twoReturnDiscriminant x y =
      4 * (x ^ 2 + 2 * x * y - 3 * x - y + 2) := by
  simp [twoReturnDiscriminant, twoReturnFence, twoReturnLeading, twoReturnLinear,
    discrim]
  ring

/-- The middle-square gap is odd over the integers. -/
theorem twoReturnDiscriminant_sub_middle_sq (x y : ℤ) :
    twoReturnDiscriminant x y - (twoReturnFence x y + 1) ^ 2 =
      2 * (x ^ 2 * y - 2 * x ^ 2 - 3 * x * y + 4 * x + y) - 3 := by
  simp [twoReturnDiscriminant, twoReturnFence, twoReturnLeading, twoReturnLinear,
    discrim]
  ring

/-- For integral return scales at least two, the discriminant is trapped between two squares
two units apart, while parity excludes the middle square. -/
theorem twoReturnDiscriminant_not_isSquare (x y : ℤ) (hx : 2 ≤ x) (hy : 2 ≤ y) :
    ¬IsSquare (twoReturnDiscriminant x y) := by
  let N := twoReturnFence x y
  let D := twoReturnDiscriminant x y
  have hN : 0 ≤ N := by
    dsimp [N, twoReturnFence, twoReturnLinear]
    nlinarith [mul_nonneg (show 0 ≤ x - 1 by omega) (show 0 ≤ y - 1 by omega)]
  have hDN : N ^ 2 < D := by
    have hpos : 0 < 4 * x * (x - 1) * (y - 1) := by
      exact mul_pos (mul_pos (mul_pos (by norm_num) (by omega)) (by omega)) (by omega)
    have hid : D - N ^ 2 = 4 * x * (x - 1) * (y - 1) := by
      exact twoReturnDiscriminant_sub_fence_sq x y
    omega
  have hND : D < (N + 2) ^ 2 := by
    have hxy : 0 < x ^ 2 + 2 * x * y - 3 * x - y + 2 := by
      have h₁ : 0 ≤ (x - 1) * (x - 2) := mul_nonneg (by omega) (by omega)
      have h₂ : 0 < (2 * x - 1) * y := mul_pos (by omega) (by omega)
      nlinarith
    have hid : (N + 2) ^ 2 - D =
        4 * (x ^ 2 + 2 * x * y - 3 * x - y + 2) := by
      exact fence_add_two_sq_sub_twoReturnDiscriminant x y
    nlinarith
  have hmid : D ≠ (N + 1) ^ 2 := by
    intro h
    have hid : D - (N + 1) ^ 2 =
        2 * (x ^ 2 * y - 2 * x ^ 2 - 3 * x * y + 4 * x + y) - 3 := by
      exact twoReturnDiscriminant_sub_middle_sq x y
    omega
  rintro ⟨z, hz⟩
  have hzsq : z ^ 2 = D := by simpa [pow_two] using hz.symm
  by_cases hz_nonneg : 0 ≤ z
  · have hNz : N < z := by nlinarith
    have hzN : z < N + 2 := by nlinarith
    have : z = N + 1 := by omega
    subst z
    exact hmid hzsq.symm
  · have hNz : N < -z := by nlinarith
    have hzN : -z < N + 2 := by nlinarith
    apply hmid
    rw [← hzsq]
    nlinarith

/-- The two-return quadratic has no rational root at positive integral scales at least two. -/
theorem twoReturnCore_ne_zero (c : ℚ) (x y : ℤ) (hx : 2 ≤ x) (hy : 2 ≤ y) :
    twoReturnCore c x y ≠ 0 := by
  simpa [twoReturnCore, twoReturnLeading, twoReturnLinear] using
    rationalQuadratic_ne_zero_of_discriminant_not_isSquare
      (twoReturnLeading x y) (twoReturnLinear x y) x
      (twoReturnDiscriminant_not_isSquare x y hx hy) c

private theorem two_le_pow_of_two_le {q : ℤ} (hq : 2 ≤ q) {n : Nat} (hn : 0 < n) :
    2 ≤ q ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ]
  have hp : 1 ≤ q ^ k := by
    have : 0 < q ^ k := pow_pos (by omega) k
    omega
  nlinarith

/-- Every positive-wait return is invertible at an integral base at least two. -/
theorem positiveTransfer_isUnit (q : ℤ) (c : ℚ) (hq : 2 ≤ q) (hc : c + 1 ≠ 0)
    (n : Nat) :
    IsUnit (positiveTransfer (q : ℚ) c n) := by
  have hpow : 2 ≤ q ^ (n + 1) := two_le_pow_of_two_le hq (by omega)
  apply transfer_isUnit c ((q : ℚ) ^ (n + 1)) hc
  · positivity
  · norm_cast at hpow ⊢
    nlinarith

/-- Zero wait is an internal rank-one punctuation mark: mortality of the full return family is
exactly vanishing of one scalar bridge over positive returns. -/
theorem transferFamily_isMortal_iff_positiveBridge (q : ℤ) (c : ℚ) :
    IsMortal (fun n => transfer c ((q : ℚ) ^ n)) ↔
      ∃ waits, positiveBridge (q : ℚ) c waits = 0 := by
  rw [← separatedPositiveTransfer_comp_natEquivOption]
  rw [isMortal_comp_equiv]
  rw [transfer_one]
  simpa [positiveBridge] using
    mortal_adjoin_outer_iff (positiveTransfer (q : ℚ) c) ![1, 1] ![c, 1]

/-- Empty positive bridge is the separator's self-incidence scalar. -/
theorem positiveBridge_nil (q c : ℚ) :
    positiveBridge q c [] = c + 1 := by
  simp [positiveBridge, bridgeScalar, dotProduct, Fin.sum_univ_succ]

/-- Closed form of a bridge containing one positive return. -/
theorem positiveBridge_singleton (q c : ℚ) (n : Nat) :
    positiveBridge q c [n] =
      (c + 1) * q ^ (n + 1) * (c * q ^ (n + 1) + 1) := by
  simp only [positiveBridge, bridgeScalar, wordProduct, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, positiveTransfer]
  exact oneReturn_coefficient c (q ^ (n + 1))

/-- Peeling the first positive return moves the target covector to the strip
`[c q^(n+1), 1]`. -/
theorem positiveBridge_cons (q c : ℚ) (wait : Nat) (waits : List Nat) :
    positiveBridge q c (wait :: waits) =
      (c + 1) * q ^ (wait + 1) *
        dotProduct ![c * q ^ (wait + 1), 1]
          (Matrix.mulVec (wordProduct (positiveTransfer q c) waits) ![1, 1]) := by
  simp only [positiveBridge, bridgeScalar, wordProduct_cons, positiveTransfer]
  rw [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec]
  rw [covector_collapse]
  simp
  ring

/-- Closed form of a bridge containing two positive returns. -/
theorem positiveBridge_pair (q c : ℚ) (m n : Nat) :
    positiveBridge q c [m, n] = q ^ (m + 1) * (c + 1) *
      twoReturnCore c (q ^ (n + 1)) (q ^ (m + 1)) := by
  simp only [positiveBridge, bridgeScalar, wordProduct, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, positiveTransfer]
  rw [← Matrix.mulVec_mulVec]
  exact twoReturn_coefficient c (q ^ (n + 1)) (q ^ (m + 1))

/-- No two positive returns kill the rank-one strip, for any integral base at least two and any
nondegenerate rational parameter. Thus every nontrivial ReturnSquare zero needs at least three
positive returns. -/
theorem twoReturn_coefficient_ne_zero (q : ℤ) (c : ℚ) (m n : Nat)
    (hq : 2 ≤ q) (hm : 0 < m) (hn : 0 < n) (hc : c + 1 ≠ 0) :
    ![c, 1] ⬝ᵥ transfer c ((q : ℚ) ^ n) *ᵥ
        (transfer c ((q : ℚ) ^ m) *ᵥ ![1, 1]) ≠ 0 := by
  rw [twoReturn_coefficient]
  have hcore : twoReturnCore c ((q : ℚ) ^ m) ((q : ℚ) ^ n) ≠ 0 := by
    simpa using
      twoReturnCore_ne_zero c (q ^ m) (q ^ n)
        (two_le_pow_of_two_le hq hm) (two_le_pow_of_two_le hq hn)
  exact mul_ne_zero (mul_ne_zero (by positivity) hc) hcore

/-- In bridge coordinates, no word of exactly two positive returns can vanish. -/
theorem positiveBridge_pair_ne_zero (q : ℤ) (c : ℚ) (m n : Nat)
    (hq : 2 ≤ q) (hc : c + 1 ≠ 0) :
    positiveBridge (q : ℚ) c [m, n] ≠ 0 := by
  rw [positiveBridge_pair]
  have hcore :
      twoReturnCore c ((q : ℚ) ^ (n + 1)) ((q : ℚ) ^ (m + 1)) ≠ 0 := by
    simpa using
      twoReturnCore_ne_zero c (q ^ (n + 1)) (q ^ (m + 1))
        (two_le_pow_of_two_le hq (by omega)) (two_le_pow_of_two_le hq (by omega))
  exact mul_ne_zero (mul_ne_zero (by positivity) hc) hcore

/-- Every vanishing bridge is either the explicit one-return exceptional parameter or contains
at least three positive returns. -/
theorem positiveBridge_zero_shape (q : ℤ) (c : ℚ) (waits : List Nat)
    (hq : 2 ≤ q) (hc : c + 1 ≠ 0)
    (bridge_zero : positiveBridge (q : ℚ) c waits = 0) :
    (∃ n, waits = [n] ∧ c * (q : ℚ) ^ (n + 1) + 1 = 0) ∨ 3 ≤ waits.length := by
  rcases waits with _ | ⟨first, waits⟩
  · rw [positiveBridge_nil] at bridge_zero
    exact (hc bridge_zero).elim
  · rcases waits with _ | ⟨second, waits⟩
    · left
      refine ⟨first, rfl, ?_⟩
      rw [positiveBridge_singleton] at bridge_zero
      rcases mul_eq_zero.mp bridge_zero with prefix_zero | factor_zero
      · exact ((mul_ne_zero hc (by positivity)) prefix_zero).elim
      · exact factor_zero
    · rcases waits with _ | ⟨third, waits⟩
      · exact (positiveBridge_pair_ne_zero q c first second hq hc bridge_zero).elim
      · right
        simp

/-- Positive-return matrices preserve the strict positive cone when `c≥0`. -/
theorem positiveTransfer_mulVec_pos (q : ℤ) (c : ℚ) (hq : 2 ≤ q) (hc : 0 ≤ c)
    (n : Nat) (v : Fin 2 → ℚ) (hv : ∀ i, 0 < v i) :
    ∀ i, 0 < (positiveTransfer (q : ℚ) c n *ᵥ v) i := by
  have hpowZ : 2 ≤ q ^ (n + 1) := two_le_pow_of_two_le hq (by omega)
  have ht : (2 : ℚ) ≤ (q : ℚ) ^ (n + 1) := by exact_mod_cast hpowZ
  have hlead : 0 < (c + 1) * ((q : ℚ) ^ (n + 1)) ^ 2 - 1 := by
    nlinarith [sq_nonneg ((q : ℚ) ^ (n + 1))]
  intro i
  fin_cases i
  · simp [positiveTransfer, transfer, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    exact add_pos (mul_pos hlead (hv 0)) (mul_pos (by positivity) (hv 1))
  · simp [positiveTransfer, transfer, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg hc (hv 0).le) (mul_pos (by positivity) (hv 1))

/-- Every positive bridge is strictly positive when `c≥0`. -/
theorem positiveBridge_pos_of_nonneg (q : ℤ) (c : ℚ) (waits : List Nat)
    (hq : 2 ≤ q) (hc : 0 ≤ c) :
    0 < positiveBridge (q : ℚ) c waits := by
  have vector_pos :
      ∀ i, 0 <
        (wordProduct (positiveTransfer (q : ℚ) c) waits *ᵥ ![1, 1]) i := by
    induction waits with
    | nil =>
      intro i
      fin_cases i <;> norm_num [wordProduct]
    | cons n waits induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec]
      exact positiveTransfer_mulVec_pos q c hq hc n _ induction
  rw [positiveBridge, bridgeScalar]
  rw [show
    ![c, 1] ⬝ᵥ wordProduct (positiveTransfer (q : ℚ) c) waits *ᵥ ![1, 1] =
      c * (wordProduct (positiveTransfer (q : ℚ) c) waits *ᵥ ![1, 1]) 0 +
        (wordProduct (positiveTransfer (q : ℚ) c) waits *ᵥ ![1, 1]) 1 by
          simp [dotProduct, Fin.sum_univ_succ]]
  exact add_pos_of_nonneg_of_pos (mul_nonneg hc (vector_pos 0).le) (vector_pos 1)

/-- Determinant of the diagonal ambient generator. -/
theorem ambient_det {K : Type*} [Field K] (q : K) :
    (ambient q).det = q ^ 3 := by
  simp [ambient, Matrix.det_diagonal, Fin.prod_univ_succ]
  ring

/-- A nonzero geometric base makes the ambient generator a unit. -/
theorem ambient_isUnit {K : Type*} [Field K] (q : K) (q_ne_zero : q ≠ 0) :
    IsUnit (ambient q) := by
  apply (ambient q).isUnit_iff_isUnit_det.mpr
  rw [ambient_det]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero 3 q_ne_zero)

/-- The output has full row rank away from the degenerate parameter `c=-1`. -/
theorem output_rank {K : Type*} [Field K] (c : K) (c_add_one_ne : c + 1 ≠ 0) :
    (output c).rank = 2 := by
  apply le_antisymm
  · exact Matrix.rank_le_height (output c)
  · have rank_bound :=
      Matrix.rank_mul_le_left (output c) (outputRightInverse c)
    rw [output_mul_outputRightInverse c c_add_one_ne, Matrix.rank_one] at rank_bound
    norm_num at rank_bound ⊢
    exact rank_bound

/-- The physical cut has rank exactly two away from `c=-1`. -/
theorem cut_rank {K : Type*} [Field K] (c : K) (c_add_one_ne : c + 1 ≠ 0) :
    (cut c).rank = 2 := by
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left
      (input : Matrix (Fin 3) (Fin 2) K) (output c)).trans
        (Matrix.rank_le_width input)
  · have output_factor :
        output c = inputLeftInverse * cut c := by
      calc
        output c = (1 : Square (Fin 2) K) * output c := by simp
        _ = ((inputLeftInverse : Matrix (Fin 2) (Fin 3) K) * input) * output c :=
          (congrArg (fun matrix : Square (Fin 2) K => matrix * output c)
            inputLeftInverse_mul_input).symm
        _ = inputLeftInverse * (input * output c) := Matrix.mul_assoc _ _ _
        _ = inputLeftInverse * cut c := rfl
    have lower : (output c).rank ≤ (cut c).rank := by
      rw [output_factor]
      exact Matrix.rank_mul_le_right
        (inputLeftInverse : Matrix (Fin 2) (Fin 3) K) (cut c)
    rw [output_rank c c_add_one_ne] at lower
    exact lower

/-- The excluded parameter is not a hard rank-`(3,2)` instance: its cut squares to zero. -/
theorem cut_neg_one_sq {R : Type*} [CommRing R] :
    cut (-1 : R) * cut (-1 : R) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cut_eq, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The physical pair is exactly the finite-return mortality problem. -/
theorem physical_isMortal_iff_returnProduct {K : Type*} [Field K]
    (q c : K) (q_ne_zero : q ≠ 0) :
    IsMortal (ReturnFamily.pairGenerator (ambient q) (cut c)) ↔
      ∃ waits,
        ReturnFamily.returnProduct (ambient q) input (output c) waits = 0 := by
  exact ReturnFamily.pairGenerator_isMortal_iff
    (ambient q) input (output c) (ambient_isUnit q q_ne_zero)

/-- Complete ReturnSquare normal form: physical mortality is exactly one scalar bridge between
two internal zero-wait punctuation returns, with every intervening return positive and invertible.
-/
theorem physical_isMortal_iff_positiveBridge
    (q : ℤ) (c : ℚ) (q_ne_zero : q ≠ 0) :
    IsMortal (ReturnFamily.pairGenerator (ambient (q : ℚ)) (cut c)) ↔
      ∃ waits, positiveBridge (q : ℚ) c waits = 0 := by
  change
    IsMortal (ReturnFamily.pairGenerator (ambient (q : ℚ)) (input * output c)) ↔
      ∃ waits,
        bridgeScalar ![1, 1] ![c, 1]
          (wordProduct (fun wait => transfer c ((q : ℚ) ^ (wait + 1))) waits) = 0
  have reduction := ReturnFamily.pairGenerator_isMortal_iff_positiveBridge
      (ambient (q : ℚ)) input (output c) ![1, 1] ![c, 1]
      (ambient_isUnit (q : ℚ) (by exact_mod_cast q_ne_zero))
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

/-- The exact first research frontier for ReturnSquare: mortality is either a classified
one-return resonance or a bridge with at least three positive returns. Two returns are impossible.
-/
theorem physical_isMortal_iff_oneReturn_or_longBridge (q : ℤ) (c : ℚ)
    (hq : 2 ≤ q) (hc : c + 1 ≠ 0) :
    IsMortal (ReturnFamily.pairGenerator (ambient (q : ℚ)) (cut c)) ↔
      (∃ n, c * (q : ℚ) ^ (n + 1) + 1 = 0) ∨
        ∃ waits, 3 ≤ waits.length ∧ positiveBridge (q : ℚ) c waits = 0 := by
  rw [physical_isMortal_iff_positiveBridge q c (by omega)]
  constructor
  · rintro ⟨waits, bridge_zero⟩
    rcases positiveBridge_zero_shape q c waits hq hc bridge_zero with short | long
    · obtain ⟨n, _, resonance⟩ := short
      exact Or.inl ⟨n, resonance⟩
    · exact Or.inr ⟨waits, long, bridge_zero⟩
  · rintro (resonance | long)
    · obtain ⟨n, resonance⟩ := resonance
      refine ⟨[n], ?_⟩
      rw [positiveBridge_singleton, resonance]
      ring
    · obtain ⟨waits, _, bridge_zero⟩ := long
      exact ⟨waits, bridge_zero⟩

/-- Nonnegative ReturnSquare parameters are immortal. This includes the valid rank-two boundary
case `c=0`, which a strict-positivity statement would miss. -/
theorem not_physical_isMortal_of_nonneg (q : ℤ) (c : ℚ)
    (hq : 2 ≤ q) (hc : 0 ≤ c) :
    ¬IsMortal (ReturnFamily.pairGenerator (ambient (q : ℚ)) (cut c)) := by
  rw [physical_isMortal_iff_positiveBridge q c (by omega)]
  rintro ⟨waits, bridge_zero⟩
  exact (positiveBridge_pos_of_nonneg q c waits hq hc).ne' bridge_zero

end ReturnSquare

end MatrixMortality
