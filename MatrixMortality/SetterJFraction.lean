import Mathlib.Tactic

/-!
# Decimal setter J-fraction obstruction

The decimal setter sends each regular side block to a J-fraction map
`t ↦ u + v - v / t`.  The individual maps in the proposed decimal family are
strictly hyperbolic.  This file isolates the exact two-block obstruction: the
coefficient boxes forced by a leading encoded `b` contain two hyperbolic maps
whose product is elliptic.
-/

namespace MatrixMortality.SetterJFraction

/-- Discriminant of the projective matrix `[[u + v, -v], [1, 0]]`. -/
def discriminant (u v : ℚ) : ℚ := (u + v) ^ 2 - 4 * v

/-- Discriminant of the product of two J-fraction matrices. -/
def productDiscriminant (u₁ v₁ u₂ v₂ : ℚ) : ℚ :=
  ((u₁ + v₁) * (u₂ + v₂) - v₁ - v₂) ^ 2 - 4 * v₁ * v₂

private def lowerU : ℚ := 9653846153 / 10000000000

private def upperU : ℚ := 9653846155 / 10000000000

private def lowerHighV : ℚ := 2692350428 / 100000000

private def upperHighV : ℚ := 2692350429 / 100000000

private def lowerLowV : ℚ := 3378846155 / 10000000000000000000

private def upperLowV : ℚ := 3378846156 / 10000000000000000000

private def productTrace (highU highV lowU lowV : ℚ) : ℚ :=
  (highU + highV) * (lowU + lowV) - highV - lowV

private theorem productTrace_bounds
    (highU highV lowU lowV : ℚ)
    (highU_mem : lowerU ≤ highU ∧ highU ≤ upperU)
    (highV_mem : lowerHighV ≤ highV ∧ highV ≤ upperHighV)
    (lowU_mem : lowerU ≤ lowU ∧ lowU ≤ upperU)
    (lowV_mem : lowerLowV ≤ lowV ∧ lowV ≤ upperLowV) :
    0 < productTrace highU highV lowU lowV ∧
      productTrace highU highV lowU lowV < 1 / 10000000 := by
  have low_sum_nonneg : 0 ≤ lowU + lowV := by
    norm_num [lowerU, lowerLowV] at lowU_mem lowV_mem ⊢
    linarith
  have high_lower_sum_nonneg : 0 ≤ lowerU + highV := by
    norm_num [lowerU, lowerHighV] at highV_mem ⊢
    linarith
  have high_upper_sum_nonneg : 0 ≤ upperU + highV := by
    norm_num [upperU, lowerHighV] at highV_mem ⊢
    linarith
  have low_high_coefficient_nonpos : lowerU + lowV - 1 ≤ 0 := by
    norm_num [lowerU, upperLowV] at lowV_mem ⊢
    linarith
  have high_high_coefficient_nonpos : upperU + lowV - 1 ≤ 0 := by
    norm_num [upperU, upperLowV] at lowV_mem ⊢
    linarith
  have lower_low_coefficient_nonneg : 0 ≤ lowerU + upperHighV - 1 := by
    norm_num [lowerU, upperHighV]
  have upper_low_coefficient_nonneg : 0 ≤ upperU + lowerHighV - 1 := by
    norm_num [upperU, lowerHighV]
  have highU_lower_step :
      productTrace lowerU highV lowU lowV ≤
        productTrace highU highV lowU lowV := by
    have product_nonneg : 0 ≤ (highU - lowerU) * (lowU + lowV) :=
      mul_nonneg (sub_nonneg.mpr highU_mem.1) low_sum_nonneg
    unfold productTrace
    nlinarith
  have highU_upper_step :
      productTrace highU highV lowU lowV ≤
        productTrace upperU highV lowU lowV := by
    have product_nonneg : 0 ≤ (upperU - highU) * (lowU + lowV) :=
      mul_nonneg (sub_nonneg.mpr highU_mem.2) low_sum_nonneg
    unfold productTrace
    nlinarith
  have lowU_lower_step :
      productTrace lowerU highV lowerU lowV ≤
        productTrace lowerU highV lowU lowV := by
    have product_nonneg : 0 ≤ (lowU - lowerU) * (lowerU + highV) :=
      mul_nonneg (sub_nonneg.mpr lowU_mem.1) high_lower_sum_nonneg
    unfold productTrace
    nlinarith
  have lowU_upper_step :
      productTrace upperU highV lowU lowV ≤
        productTrace upperU highV upperU lowV := by
    have product_nonneg : 0 ≤ (upperU - lowU) * (upperU + highV) :=
      mul_nonneg (sub_nonneg.mpr lowU_mem.2) high_upper_sum_nonneg
    unfold productTrace
    nlinarith
  have highV_lower_step :
      productTrace lowerU upperHighV lowerU lowV ≤
        productTrace lowerU highV lowerU lowV := by
    have product_nonneg :
        0 ≤ (upperHighV - highV) * (-(lowerU + lowV - 1)) :=
      mul_nonneg (sub_nonneg.mpr highV_mem.2) (neg_nonneg.mpr low_high_coefficient_nonpos)
    unfold productTrace
    nlinarith
  have highV_upper_step :
      productTrace upperU highV upperU lowV ≤
        productTrace upperU lowerHighV upperU lowV := by
    have product_nonneg :
        0 ≤ (highV - lowerHighV) * (-(upperU + lowV - 1)) :=
      mul_nonneg (sub_nonneg.mpr highV_mem.1) (neg_nonneg.mpr high_high_coefficient_nonpos)
    unfold productTrace
    nlinarith
  have lowV_lower_step :
      productTrace lowerU upperHighV lowerU lowerLowV ≤
        productTrace lowerU upperHighV lowerU lowV := by
    have product_nonneg :
        0 ≤ (lowV - lowerLowV) * (lowerU + upperHighV - 1) :=
      mul_nonneg (sub_nonneg.mpr lowV_mem.1) lower_low_coefficient_nonneg
    unfold productTrace
    nlinarith
  have lowV_upper_step :
      productTrace upperU lowerHighV upperU lowV ≤
        productTrace upperU lowerHighV upperU upperLowV := by
    have product_nonneg :
        0 ≤ (upperLowV - lowV) * (upperU + lowerHighV - 1) :=
      mul_nonneg (sub_nonneg.mpr lowV_mem.2) upper_low_coefficient_nonneg
    unfold productTrace
    nlinarith
  have lower_corner :
      0 < productTrace lowerU upperHighV lowerU lowerLowV := by
    norm_num [productTrace, lowerU, upperHighV, lowerLowV]
  have upper_corner :
      productTrace upperU lowerHighV upperU upperLowV < 1 / 10000000 := by
    norm_num [productTrace, upperU, lowerHighV, upperLowV]
  exact
    ⟨lower_corner.trans_le
        (lowV_lower_step.trans
          (highV_lower_step.trans (lowU_lower_step.trans highU_lower_step))),
      (highU_upper_step.trans
        (lowU_upper_step.trans (highV_upper_step.trans lowV_upper_step))).trans_lt
          upper_corner⟩

/-- The decimal setter's emitted-body coefficient boxes contain two individually
hyperbolic blocks whose two-block product is elliptic. -/
theorem emittedBody_elliptic_pair
    (highU highV lowU lowV : ℚ)
    (highU_mem : lowerU ≤ highU ∧ highU ≤ upperU)
    (highV_mem : lowerHighV ≤ highV ∧ highV ≤ upperHighV)
    (lowU_mem : lowerU ≤ lowU ∧ lowU ≤ upperU)
    (lowV_mem : lowerLowV ≤ lowV ∧ lowV ≤ upperLowV) :
    0 < discriminant highU highV ∧
      0 < discriminant lowU lowV ∧
      productDiscriminant highU highV lowU lowV < 0 := by
  have high_sum_gt : 27 < highU + highV := by
    norm_num [lowerU, lowerHighV] at highU_mem highV_mem ⊢
    linarith
  have highV_lt : highV < 27 := by
    norm_num [upperHighV] at highV_mem ⊢
    linarith
  have high_discriminant : 0 < discriminant highU highV := by
    unfold discriminant
    nlinarith [sq_nonneg (highU + highV - 27)]
  have low_sum_gt : 9 / 10 < lowU + lowV := by
    norm_num [lowerU, lowerLowV] at lowU_mem lowV_mem ⊢
    linarith
  have lowV_lt : lowV < 1 / 1000000000 := by
    norm_num [upperLowV] at lowV_mem ⊢
    linarith
  have low_discriminant : 0 < discriminant lowU lowV := by
    unfold discriminant
    nlinarith [sq_nonneg (lowU + lowV - 9 / 10)]
  obtain ⟨trace_pos, trace_lt⟩ :=
    productTrace_bounds highU highV lowU lowV
      highU_mem highV_mem lowU_mem lowV_mem
  have trace_product_nonneg :
      0 ≤ productTrace highU highV lowU lowV *
        (1 / 10000000 - productTrace highU highV lowU lowV) :=
    mul_nonneg trace_pos.le (sub_nonneg.mpr trace_lt.le)
  have trace_sq_lt :
      (productTrace highU highV lowU lowV) ^ 2 < 1 / 100000000000000 := by
    nlinarith
  have highV_pos : 0 ≤ highV := by
    norm_num [lowerHighV] at highV_mem ⊢
    linarith
  have lower_product_step :
      lowerHighV * lowerLowV ≤ highV * lowV := by
    have high_step :
        lowerHighV * lowV ≤ highV * lowV :=
      mul_le_mul_of_nonneg_right highV_mem.1 (by
        norm_num [lowerLowV] at lowV_mem ⊢
        linarith)
    have low_step :
        lowerHighV * lowerLowV ≤ lowerHighV * lowV :=
      mul_le_mul_of_nonneg_left lowV_mem.1 (by norm_num [lowerHighV])
    exact low_step.trans high_step
  have determinant_gap :
      1 / 100000000000000 < 4 * highV * lowV := by
    have exact_gap :
        1 / 100000000000000 < 4 * lowerHighV * lowerLowV := by
      norm_num [lowerHighV, lowerLowV]
    nlinarith
  have product_discriminant :
      productDiscriminant highU highV lowU lowV < 0 := by
    unfold productTrace at trace_sq_lt
    unfold productDiscriminant
    nlinarith
  exact ⟨high_discriminant, low_discriminant, product_discriminant⟩

/-! ## Exact decimal coefficients -/

private def decimalRho : ℚ := 10000000000

private def decimalMarker : ℚ := (52 * decimalRho - 7) / 9

private def decimalRatio : ℚ := 10 * decimalRho / decimalMarker

private def decimalL : ℚ :=
  (502 * decimalRho - 7) / (9 * (2 * decimalRho - 7))

private def decimalC : ℚ := decimalL / decimalMarker

/-- The `D_c` coefficient `u` in the `β=10` decimal setter. -/
def lowU10 : ℚ := (1 + 5 * decimalRatio) / 10

/-- The `D_c` coefficient `v` in the `β=10` decimal setter. -/
def lowV10 : ℚ := 7 * decimalC / 10

private def bTransform10 (x : ℚ) : ℚ :=
  1 + (5 * decimalRatio + x) / 1000000000000

private def bFixed10 : ℚ :=
  (1000000000000 + 5 * decimalRatio) / (1000000000000 - 1)

private def bTail10 : Nat → ℚ
  | 0 => 1
  | n + 1 => bTransform10 (bTail10 n)

private theorem bTransform10_fixed : bTransform10 bFixed10 = bFixed10 := by
  norm_num [bTransform10, bFixed10, decimalRatio, decimalMarker, decimalRho]

private theorem bTail10_mem (n : Nat) : 1 ≤ bTail10 n ∧ bTail10 n ≤ bFixed10 := by
  induction n with
  | zero =>
      norm_num [bTail10, bFixed10, decimalRatio, decimalMarker, decimalRho]
  | succ n induction =>
      have fixed_gt_one : 1 ≤ bFixed10 := by
        norm_num [bFixed10, decimalRatio, decimalMarker, decimalRho]
      have lower_step : 1 ≤ bTransform10 (bTail10 n) := by
        norm_num [bTransform10, decimalRatio, decimalMarker, decimalRho] at induction ⊢
        linarith
      have upper_step : bTransform10 (bTail10 n) ≤ bTransform10 bFixed10 := by
        norm_num [bTransform10] at induction ⊢
        linarith
      rw [bTransform10_fixed] at upper_step
      exact ⟨by simpa [bTail10] using lower_step, by simpa [bTail10] using upper_step⟩

/-- The coefficient `u` of a block whose upper word is `c b^n`. -/
def highU10 (n : Nat) : ℚ :=
  5 * decimalRatio / 10 + bTail10 n / 10

private theorem highU10_mem (n : Nat) : lowerU ≤ highU10 n ∧ highU10 n ≤ upperU := by
  have tail_mem := bTail10_mem n
  norm_num [highU10, lowerU, upperU, bFixed10, decimalRatio,
    decimalMarker, decimalRho] at tail_mem ⊢
  constructor <;> linarith

private def prefixLower10 : ℚ := 5577777777775 / 10000000000000

private def prefixUpper10 : ℚ :=
  prefixLower10 + 7 / (9 * 10000000000000)

/-- Base-ten fractional value of a finite digit word. -/
def decimalFraction : List ℚ → ℚ
  | [] => 0
  | digit :: digits => digit / 10 + decimalFraction digits / 10

private theorem decimalFraction_mem (digits : List ℚ)
    (digit_mem : ∀ digit ∈ digits, 0 ≤ digit ∧ digit ≤ 7) :
    0 ≤ decimalFraction digits ∧ decimalFraction digits ≤ 7 / 9 := by
  induction digits with
  | nil => norm_num [decimalFraction]
  | cons digit digits induction =>
      have head_mem := digit_mem digit (by simp)
      have tail_mem : ∀ tail ∈ digits, 0 ≤ tail ∧ tail ≤ 7 := by
        intro tail member
        exact digit_mem tail (by simp [member])
      obtain ⟨tail_nonneg, tail_bound⟩ := induction tail_mem
      simp only [decimalFraction]
      constructor <;> nlinarith

/-- Normalized lower value after the forced decimal prefix `55 7^10 5`. -/
def prefixedLowerFraction10 (tail : List ℚ) : ℚ :=
  prefixLower10 + decimalFraction tail / 10000000000000

private theorem prefixedLowerFraction10_mem (tail : List ℚ)
    (digit_mem : ∀ digit ∈ tail, 0 ≤ digit ∧ digit ≤ 7) :
    prefixLower10 ≤ prefixedLowerFraction10 tail ∧
      prefixedLowerFraction10 tail ≤ prefixUpper10 := by
  obtain ⟨fraction_nonneg, fraction_bound⟩ := decimalFraction_mem tail digit_mem
  norm_num [prefixedLowerFraction10, prefixUpper10] at fraction_nonneg fraction_bound ⊢
  constructor <;> nlinarith

/-- The coefficient `v` of a defect-`11` block with normalized lower value `fraction`. -/
def highV10 (fraction : ℚ) : ℚ :=
  decimalC * 100000000000 * fraction

private theorem highV10_mem (fraction : ℚ)
    (fraction_mem : prefixLower10 ≤ fraction ∧ fraction ≤ prefixUpper10) :
    lowerHighV ≤ highV10 fraction ∧ highV10 fraction ≤ upperHighV := by
  norm_num [highV10, decimalC, decimalL, decimalMarker, decimalRho,
    prefixLower10, prefixUpper10, lowerHighV, upperHighV] at fraction_mem ⊢
  constructor <;> nlinarith

private theorem lowU10_mem : lowerU ≤ lowU10 ∧ lowU10 ≤ upperU := by
  norm_num [lowU10, decimalRatio, decimalMarker, decimalRho, lowerU, upperU]

private theorem lowV10_mem : lowerLowV ≤ lowV10 ∧ lowV10 ≤ upperLowV := by
  norm_num [lowV10, decimalC, decimalL, decimalMarker, decimalRho,
    lowerLowV, upperLowV]

/-- Any defect-`11` block with upper word `c b^n` and the emitted body's
leading-`b` lower prefix forms an elliptic pair with `D_c`, although both
individual block maps are hyperbolic. -/
theorem leadingB_elliptic_pair (n : Nat) (tail : List ℚ)
    (digit_mem : ∀ digit ∈ tail, 0 ≤ digit ∧ digit ≤ 7) :
    0 < discriminant (highU10 n) (highV10 (prefixedLowerFraction10 tail)) ∧
      0 < discriminant lowU10 lowV10 ∧
      productDiscriminant
          (highU10 n) (highV10 (prefixedLowerFraction10 tail)) lowU10 lowV10 < 0 := by
  have fraction_mem := prefixedLowerFraction10_mem tail digit_mem
  exact emittedBody_elliptic_pair
    (highU10 n) (highV10 (prefixedLowerFraction10 tail)) lowU10 lowV10
    (highU10_mem n) (highV10_mem _ fraction_mem) lowU10_mem lowV10_mem

end MatrixMortality.SetterJFraction
