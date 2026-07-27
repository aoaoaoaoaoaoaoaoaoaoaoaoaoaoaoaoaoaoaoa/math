import MatrixMortality.CHHNPacking
import MatrixMortality.PairedRank

/-!
# Exact rank of every Neary CHHN placement

The five three-state Neary generators may occupy the five CHHN packing slots in any order.  A
six-row and six-column certificate exposes every packed state for every such placement.
-/

namespace MatrixMortality

open scoped Matrix

/-- The boundary row used by the side-normal Neary representation. -/
def chhnNearyRow : Fin 3 → ℚ := ![1, 0, 0]

/-- The fixed-boundary column used by the side-normal Neary representation. -/
def chhnNearyColumn (β : Nat) : Fin 3 → ℚ :=
  sideTerminalColumn ℚ (nearyMarker β)

/-- One ordinary side-normal Neary role matrix. -/
def chhnNearyRole (β : Nat) (body : List TagLetter) (tile : NearyTile) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  sidePcpMatrix ℚ (nearyUpper β tile) (nearyLower β body tile)

/-- Positional value of the long upper word carried by the letter `b`. -/
def chhnNearyUpperB (β : Nat) : ℚ :=
  ternaryCode (tagCode β .b)

/-- Positional value of the body-dependent lower rule word carried by `c`. -/
def chhnNearyLowerC (β : Nat) (body : List TagLetter) : ℚ :=
  ternaryCode (nearyLower β body (.rule .c))

/-- Base-three scale of the fixed right marker. -/
def chhnNearyMarkerScale (β : Nat) : ℚ :=
  (3 : ℚ) ^ (nearyMarker β).length

/-- Positional value of the fixed right marker. -/
def chhnNearyMarkerValue (β : Nat) : ℚ :=
  ternaryCode (nearyMarker β)

/-- Base-three scale of the long upper word carried by `b`. -/
def chhnNearyUpperBScale (β : Nat) : ℚ :=
  (3 : ℚ) ^ (tagCode β .b).length

/-- Base-three scale of the body-dependent lower rule word carried by `c`. -/
def chhnNearyLowerCScale (β : Nat) (body : List TagLetter) : ℚ :=
  (3 : ℚ) ^ (nearyLower β body (.rule .c)).length

/-- The terminal `10` of the rule-`c` lower word fixes its two least significant ternary
digits. -/
theorem chhnNearyLowerC_eq_nine_mul_add_seven (β : Nat) (body : List TagLetter) :
    chhnNearyLowerC β body =
      9 * ternaryCode (true :: tagEncode β body) + 7 := by
  simp [chhnNearyLowerC, nearyLower, ternaryCode_append, ternaryCode_cons,
    ternaryDigit]
  ring

/-- The rule-`c` lower scale contains the same terminal two-digit factor. -/
theorem chhnNearyLowerCScale_eq_nine_mul (β : Nat) (body : List TagLetter) :
    chhnNearyLowerCScale β body =
      9 * (3 : ℚ) ^ (tagEncode β body).length.succ := by
  simp [chhnNearyLowerCScale, nearyLower, pow_add]
  ring

/-- The fixed right column after evaluating its marker. -/
def chhnNearyNativeColumn (β : Nat) : Fin 3 → ℚ :=
  ![chhnNearyMarkerValue β, -1, chhnNearyMarkerScale β]

/-- Closed semantic normal form of the fixed right column. -/
theorem chhnNearyColumn_eq_native (β : Nat) :
    chhnNearyColumn β = chhnNearyNativeColumn β := by
  ext coordinate
  fin_cases coordinate <;>
    simp [chhnNearyColumn, chhnNearyNativeColumn, chhnNearyMarkerValue,
      chhnNearyMarkerScale, sideTerminalColumn, sidePcpMatrix, sideTailBasis,
      Matrix.mulVec, Matrix.dotProduct, Matrix.vecHead, Matrix.vecTail,
      Fin.sum_univ_succ]

/-- The four Neary matrices after all fixed words have been evaluated. -/
def chhnNearyNativeRole (β : Nat) (body : List TagLetter) :
    NearyTile → Matrix (Fin 3) (Fin 3) ℚ
  | .rule .c =>
      !![1, chhnNearyLowerC β body, 2;
         0, chhnNearyLowerCScale β body, 0;
         0, 0, 3]
  | .rule .b =>
      !![1, 25, chhnNearyUpperB β;
         0, 27, 0;
         0, 0, chhnNearyUpperBScale β]
  | .erase .c =>
      !![1, 1, 2;
         0, 3, 0;
         0, 0, 3]
  | .erase .b =>
      !![1, 1, chhnNearyUpperB β;
         0, 3, 0;
         0, 0, chhnNearyUpperBScale β]

/-- Closed semantic normal form of each Neary role matrix. -/
theorem chhnNearyRole_eq_native (β : Nat) (body : List TagLetter) (tile : NearyTile) :
    chhnNearyRole β body tile = chhnNearyNativeRole β body tile := by
  ext row column
  cases tile with
  | rule letter =>
      cases letter <;> fin_cases row <;> fin_cases column <;>
        simp [chhnNearyRole, chhnNearyNativeRole, chhnNearyUpperB,
          chhnNearyLowerC, chhnNearyMarkerScale, chhnNearyUpperBScale,
          chhnNearyLowerCScale, sidePcpMatrix, nearyUpper, nearyLower,
          Matrix.vecHead, Matrix.vecTail, ternaryDigit]
      all_goals norm_num [tagCode, ternaryCode, ternaryDigit, Nat.ofDigits]
  | erase letter =>
      cases letter <;> fin_cases row <;> fin_cases column <;>
        simp [chhnNearyRole, chhnNearyNativeRole, chhnNearyUpperB,
          chhnNearyLowerC, chhnNearyMarkerScale, chhnNearyUpperBScale,
          chhnNearyLowerCScale, sidePcpMatrix, nearyUpper, nearyLower,
          Matrix.vecHead, Matrix.vecTail, ternaryDigit]
      all_goals norm_num [tagCode, ternaryCode, ternaryDigit, Nat.ofDigits]

/-- Closed semantic normal form of the four reachable Neary rows. -/
def chhnNearyNativeRow (β : Nat) (body : List TagLetter) : NearyTile → Fin 3 → ℚ
  | .rule .c => ![1, chhnNearyLowerC β body, 2]
  | .rule .b => ![1, 25, chhnNearyUpperB β]
  | .erase .c => ![1, 1, 2]
  | .erase .b => ![1, 1, chhnNearyUpperB β]

/-- Multiplication by the boundary row selects the native affine row. -/
theorem chhnNearyRow_vecMul_role (β : Nat) (body : List TagLetter) (tile : NearyTile) :
    chhnNearyRow ᵥ* chhnNearyRole β body tile =
      chhnNearyNativeRow β body tile := by
  rw [chhnNearyRole_eq_native]
  cases tile with
  | rule letter =>
      cases letter <;> ext coordinate <;> fin_cases coordinate <;>
        simp [chhnNearyRow, chhnNearyNativeRow, chhnNearyNativeRole,
          Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_succ]
  | erase letter =>
      cases letter <;> ext coordinate <;> fin_cases coordinate <;>
        simp [chhnNearyRow, chhnNearyNativeRow, chhnNearyNativeRole,
          Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_succ]

/-- The four ordinary roles and their rank-one fixed-boundary separator. -/
def chhnNearySource (β : Nat) (body : List TagLetter) :
    Option NearyTile → Matrix (Fin 3) (Fin 3) ℚ
  | none => Matrix.vecMulVec (chhnNearyColumn β) chhnNearyRow
  | some tile => chhnNearyRole β body tile

/-- A placement bijects the five semantic source matrices with the five packing slots. -/
abbrev CHHNPlacement := CHHNSlot ≃ Option NearyTile

/-- Source matrices occupying one concrete placement. -/
def chhnPlacedSource (β : Nat) (body : List TagLetter) (placement : CHHNPlacement) :
    CHHNSlot → Matrix (Fin 3) (Fin 3) ℚ :=
  chhnNearySource β body ∘ placement

/-- Three independent rows follow from a nonzero `3 × 3` row determinant. -/
theorem finThree_rows_linearIndependent_of_det_ne_zero
    {K : Type*} [Field K] (matrix : Matrix (Fin 3) (Fin 3) K)
    (det_ne_zero : matrix.det ≠ 0) :
    LinearIndependent K fun index => matrix index := by
  apply Matrix.linearIndependent_rows_iff_isUnit.mpr
  apply matrix.isUnit_iff_isUnit_det.mpr
  exact isUnit_iff_ne_zero.mpr det_ne_zero

@[simp] theorem ternaryCode_tagCode_c (β : Nat) :
    ternaryCode (tagCode β .c) = 2 := by
  norm_num [tagCode, ternaryCode_singleton, ternaryDigit]

theorem ternaryCode_tagCode_b_gt_two (β : Nat) :
    2 < ternaryCode (tagCode β .b) := by
  have code_bound := ternaryCode_lower_bound (tagCode β .b) (tagCode_ne_nil β .b)
  have exponent_positive : 1 ≤ (tagCode β .b).length - 1 := by
    simp
  have three_le : 3 ≤ 3 ^ ((tagCode β .b).length - 1) := by
    change 3 ^ 1 ≤ 3 ^ ((tagCode β .b).length - 1)
    exact Nat.pow_le_pow_right (by norm_num) exponent_positive
  omega

theorem ternaryCode_tagCode_b_gt_fifty (β : Nat) (three_le : 3 ≤ β) :
    50 < ternaryCode (tagCode β .b) := by
  have code_bound := ternaryCode_lower_bound (tagCode β .b) (tagCode_ne_nil β .b)
  have exponent_bound : 4 ≤ (tagCode β .b).length - 1 := by
    simp
    omega
  have eighty_one_le : 81 ≤ 3 ^ ((tagCode β .b).length - 1) := by
    change 3 ^ 4 ≤ 3 ^ ((tagCode β .b).length - 1)
    exact Nat.pow_le_pow_right (by norm_num) exponent_bound
  omega

theorem ternaryCode_neary_rule_c_gt_twenty_five
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ []) :
    25 < ternaryCode (nearyLower β body (.rule .c)) := by
  have encoded_nonempty : tagEncode β body ≠ [] :=
    (tagEncode_eq_nil_iff β body).not.mpr body_nonempty
  have lower_length : 4 ≤ (nearyLower β body (.rule .c)).length := by
    simp only [nearyLower, nearyBody, List.length_append, List.length_cons, List.length_nil]
    have encoded_length := List.length_pos.mpr encoded_nonempty
    omega
  have lower_nonempty : nearyLower β body (.rule .c) ≠ [] := by
    simp [nearyLower, nearyBody]
  have code_bound :=
    ternaryCode_lower_bound (nearyLower β body (.rule .c)) lower_nonempty
  have exponent_bound : 3 ≤ (nearyLower β body (.rule .c)).length - 1 := by
    omega
  have twenty_seven_le :
      27 ≤ 3 ^ ((nearyLower β body (.rule .c)).length - 1) := by
    change 3 ^ 3 ≤ 3 ^ ((nearyLower β body (.rule .c)).length - 1)
    exact Nat.pow_le_pow_right (by norm_num) exponent_bound
  omega

theorem neary_rule_c_scale_lt_three_code
    (β : Nat) (body : List TagLetter) :
    3 ^ (nearyLower β body (.rule .c)).length <
      3 * ternaryCode (nearyLower β body (.rule .c)) := by
  rw [show nearyLower β body (.rule .c) =
      true :: (tagEncode β body ++ [true, false]) by rfl]
  rw [ternaryCode_cons]
  simp only [List.length_cons, pow_succ, ternaryDigit]
  have scale_positive :
      0 < 3 ^ (tagEncode β body ++ [true, false]).length :=
    pow_pos (by norm_num) _
  nlinarith

/-- The long upper value and marker scale satisfy `2u = 5t + 1`. -/
theorem chhnNearyUpperB_relation (β : Nat) :
    2 * chhnNearyUpperB β = 5 * chhnNearyMarkerScale β + 1 := by
  have marker_relation :
      (2 : ℚ) * pairedMarkerValue β + 1 = 5 * (3 : ℚ) ^ β := by
    have casted :
        (2 : ℚ) * pairedMarkerValue β + 1 = 5 * pairedWidthScale β := by
      exact_mod_cast pairedMarkerValue_relation β
    simpa [pairedWidthScale] using casted
  have upper_relation :
      chhnNearyUpperB β = 3 * pairedMarkerValue β + 2 := by
    have casted :
        (ternaryCode (tagCode β .b) : ℚ) = 3 * pairedMarkerValue β + 2 := by
      exact_mod_cast ternaryCode_tagCode_b β
    simpa [chhnNearyUpperB] using casted
  rw [upper_relation]
  simp only [chhnNearyMarkerScale, nearyMarker_length, pairedWidthScale, pow_succ]
  nlinarith

/-- The long upper scale is three times the marker scale. -/
theorem chhnNearyUpperBScale_relation (β : Nat) :
    chhnNearyUpperBScale β = 3 * chhnNearyMarkerScale β := by
  simp only [chhnNearyUpperBScale, tagCode_b_length, chhnNearyMarkerScale,
    nearyMarker_length]
  rw [show β + 2 = (β + 1) + 1 by omega, pow_succ]
  ring

/-- Closed base-three scale of the fixed right marker. -/
theorem chhnNearyMarkerScale_eq (β : Nat) :
    chhnNearyMarkerScale β = 3 * (3 : ℚ) ^ β := by
  simp only [chhnNearyMarkerScale, nearyMarker_length, pow_succ]
  ring

/-- Closed positional value of the fixed right marker. -/
theorem chhnNearyMarkerValue_eq (β : Nat) :
    chhnNearyMarkerValue β = (5 * (3 : ℚ) ^ β - 1) / 2 := by
  have casted :
      (2 : ℚ) * pairedMarkerValue β + 1 = 5 * pairedWidthScale β := by
    exact_mod_cast pairedMarkerValue_relation β
  simp only [chhnNearyMarkerValue, pairedMarkerValue, pairedWidthScale] at casted ⊢
  norm_num at casted
  linarith

/-- Closed positional value of the long upper word. -/
theorem chhnNearyUpperB_eq (β : Nat) :
    chhnNearyUpperB β = (15 * (3 : ℚ) ^ β + 1) / 2 := by
  rw [show (15 : ℚ) * 3 ^ β = 5 * (3 * 3 ^ β) by ring,
    ← chhnNearyMarkerScale_eq]
  nlinarith [chhnNearyUpperB_relation β]

/-- Closed base-three scale of the long upper word. -/
theorem chhnNearyUpperBScale_eq (β : Nat) :
    chhnNearyUpperBScale β = 9 * (3 : ℚ) ^ β := by
  rw [chhnNearyUpperBScale_relation, chhnNearyMarkerScale_eq]
  ring

/-- Every admissible marker scale exceeds the constants used by the certificates. -/
theorem chhnNearyMarkerScale_gt_twenty_five (β : Nat) (three_le : 3 ≤ β) :
    (25 : ℚ) < chhnNearyMarkerScale β := by
  rw [chhnNearyMarkerScale, nearyMarker_length]
  calc
    (25 : ℚ) < 3 ^ 4 := by norm_num
    _ ≤ 3 ^ (β + 1) := pow_le_pow_right (by norm_num) (by omega)

theorem chhnNeary_row_pair_linearIndependent
    (β : Nat) (body : List TagLetter) (first second : NearyTile)
    (three_le : 3 ≤ β) (body_nonempty : body ≠ []) (distinct : first ≠ second) :
    LinearIndependent ℚ
      ![chhnNearyRow,
        chhnNearyRow ᵥ* chhnNearyRole β body first,
        chhnNearyRow ᵥ* chhnNearyRole β body second] := by
  have upper_b_large_q :
      (50 : ℚ) < chhnNearyUpperB β := by
    simpa [chhnNearyUpperB] using
      (show (50 : ℚ) < ternaryCode (tagCode β .b) by
        exact_mod_cast ternaryCode_tagCode_b_gt_fifty β three_le)
  have lower_c_large_q :
      (25 : ℚ) < chhnNearyLowerC β body := by
    simpa [chhnNearyLowerC] using
      (show (25 : ℚ) < ternaryCode (nearyLower β body (.rule .c)) by
        exact_mod_cast
          ternaryCode_neary_rule_c_gt_twenty_five β body body_nonempty)
  have upper_b_large_raw :
      (50 : ℚ) < ternaryCode (tagCode β .b) := by
    simpa [chhnNearyUpperB] using upper_b_large_q
  have lower_c_large_raw :
      (25 : ℚ) < ternaryCode (nearyLower β body (.rule .c)) := by
    simpa [chhnNearyLowerC] using lower_c_large_q
  have upper_b_positive :
      (0 : ℚ) < ternaryCode (tagCode β .b) := by
    linarith [upper_b_large_raw]
  have lower_c_gt_one :
      (1 : ℚ) < ternaryCode (nearyLower β body (.rule .c)) := by
    linarith [lower_c_large_raw]
  have upper_lower_product_large :
      (50 : ℚ) <
        ternaryCode (tagCode β .b) *
          ternaryCode (nearyLower β body (.rule .c)) := by
    nlinarith [mul_pos upper_b_positive (sub_pos.mpr lower_c_gt_one)]
  have upper_b_above_fifty :
      (50 : ℚ) - ternaryCode (tagCode β .b) ≠ 0 := by
    linarith
  have upper_b_below_fifty :
      (-50 : ℚ) + ternaryCode (tagCode β .b) ≠ 0 := by
    linarith
  have upper_b_above_two :
      (2 : ℚ) - ternaryCode (tagCode β .b) ≠ 0 := by
    linarith
  have upper_b_below_two :
      (-2 : ℚ) + ternaryCode (tagCode β .b) ≠ 0 := by
    linarith
  have twice_lower_c_above_two :
      (2 : ℚ) - ternaryCode (nearyLower β body (.rule .c)) * 2 ≠ 0 := by
    linarith
  have twice_lower_c_below_two :
      (-2 : ℚ) + ternaryCode (nearyLower β body (.rule .c)) * 2 ≠ 0 := by
    linarith
  rw [chhnNearyRow_vecMul_role β body first,
    chhnNearyRow_vecMul_role β body second]
  rcases first with ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    rcases second with ⟨_ | _⟩ | ⟨_ | _⟩
  all_goals simp at distinct
  all_goals apply finThree_rows_linearIndependent_of_det_ne_zero
  all_goals rw [Matrix.det_fin_three]
  all_goals
    simp [chhnNearyRow, chhnNearyNativeRow, chhnNearyUpperB,
      chhnNearyLowerC, Matrix.vecHead, Matrix.vecTail]
  all_goals ring_nf
  all_goals first | assumption | nlinarith

theorem chhnNeary_row_triple_linearIndependent
    (β : Nat) (body : List TagLetter) (first second third : NearyTile)
    (three_le : 3 ≤ β) (body_nonempty : body ≠ [])
    (first_second : first ≠ second) (first_third : first ≠ third)
    (second_third : second ≠ third) :
    LinearIndependent ℚ
      ![chhnNearyRow ᵥ* chhnNearyRole β body first,
        chhnNearyRow ᵥ* chhnNearyRole β body second,
        chhnNearyRow ᵥ* chhnNearyRole β body third] := by
  have upper_b_large_q :
      (50 : ℚ) < chhnNearyUpperB β := by
    simpa [chhnNearyUpperB] using
      (show (50 : ℚ) < ternaryCode (tagCode β .b) by
        exact_mod_cast ternaryCode_tagCode_b_gt_fifty β three_le)
  have lower_c_large_q :
      (25 : ℚ) < chhnNearyLowerC β body := by
    simpa [chhnNearyLowerC] using
      (show (25 : ℚ) < ternaryCode (nearyLower β body (.rule .c)) by
        exact_mod_cast
          ternaryCode_neary_rule_c_gt_twenty_five β body body_nonempty)
  have upper_b_large_raw :
      (50 : ℚ) < ternaryCode (tagCode β .b) := by
    simpa [chhnNearyUpperB] using upper_b_large_q
  have lower_c_large_raw :
      (25 : ℚ) < ternaryCode (nearyLower β body (.rule .c)) := by
    simpa [chhnNearyLowerC] using lower_c_large_q
  have product_positive :
      (0 : ℚ) <
        (ternaryCode (tagCode β .b) - 2) *
          (ternaryCode (nearyLower β body (.rule .c)) - 1) := by
    exact mul_pos (by linarith [upper_b_large_raw]) (by linarith [lower_c_large_raw])
  ring_nf at product_positive
  rw [chhnNearyRow_vecMul_role β body first,
    chhnNearyRow_vecMul_role β body second,
    chhnNearyRow_vecMul_role β body third]
  rcases first with ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    rcases second with ⟨_ | _⟩ | ⟨_ | _⟩ <;>
      rcases third with ⟨_ | _⟩ | ⟨_ | _⟩
  all_goals simp at first_second first_third second_third
  all_goals apply finThree_rows_linearIndependent_of_det_ne_zero
  all_goals rw [Matrix.det_fin_three]
  all_goals
    simp [chhnNearyNativeRow, chhnNearyUpperB, chhnNearyLowerC,
      Matrix.vecHead, Matrix.vecTail]
  all_goals ring_nf
  all_goals linarith

theorem chhnNeary_composite_row_linearIndependent
    (β : Nat) (body : List TagLetter) (root leading : NearyTile)
    (three_le : 3 ≤ β) (body_nonempty : body ≠ []) (distinct : root ≠ leading) :
    LinearIndependent ℚ
      ![chhnNearyRow,
        chhnNearyRow ᵥ* chhnNearyRole β body root,
        chhnNearyRow ᵥ*
          (chhnNearyRole β body leading * chhnNearyRole β body root)] := by
  have upper_b_large_q :
      (50 : ℚ) < chhnNearyUpperB β := by
    simpa [chhnNearyUpperB] using
      (show (50 : ℚ) < ternaryCode (tagCode β .b) by
        exact_mod_cast ternaryCode_tagCode_b_gt_fifty β three_le)
  have lower_c_large_q :
      (25 : ℚ) < chhnNearyLowerC β body := by
    simpa [chhnNearyLowerC] using
      (show (25 : ℚ) < ternaryCode (nearyLower β body (.rule .c)) by
        exact_mod_cast
          ternaryCode_neary_rule_c_gt_twenty_five β body body_nonempty)
  have lower_c_scale_dominated :
      chhnNearyLowerCScale β body < 3 * chhnNearyLowerC β body := by
    have casted :
        ((3 ^ (nearyLower β body (.rule .c)).length : Nat) : ℚ) <
          3 * ternaryCode (nearyLower β body (.rule .c)) := by
      exact_mod_cast neary_rule_c_scale_lt_three_code β body
    simpa [chhnNearyLowerCScale, chhnNearyLowerC] using casted
  have marker_scale_large :=
    chhnNearyMarkerScale_gt_twenty_five β three_le
  have upper_b_relation := chhnNearyUpperB_relation β
  have upper_b_scale_relation := chhnNearyUpperBScale_relation β
  have upper_b_positive : (0 : ℚ) < chhnNearyUpperB β := by
    linarith
  have lower_c_positive : (0 : ℚ) < chhnNearyLowerC β body := by
    linarith
  have upper_gap_product_positive :
      0 < (chhnNearyUpperB β - 50) * chhnNearyLowerC β body :=
    mul_pos (sub_pos.mpr upper_b_large_q) lower_c_positive
  have lower_gap_product_positive :
      0 < chhnNearyUpperB β * (chhnNearyLowerC β body - 25) :=
    mul_pos upper_b_positive (sub_pos.mpr lower_c_large_q)
  have upper_b_three_ne_six :
      -6 + chhnNearyUpperB β * 3 ≠ 0 := by
    nlinarith
  have upper_b_scale_large :
      (75 : ℚ) < chhnNearyUpperBScale β := by
    nlinarith
  have upper_b_scale_gap_product_positive :
      0 < chhnNearyUpperB β * (chhnNearyUpperBScale β - 75) :=
    mul_pos upper_b_positive (sub_pos.mpr upper_b_scale_large)
  ring_nf at upper_gap_product_positive lower_gap_product_positive
  ring_nf at upper_b_scale_gap_product_positive
  rw [chhnNearyRole_eq_native β body root,
    chhnNearyRole_eq_native β body leading]
  rcases root with ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    rcases leading with ⟨_ | _⟩ | ⟨_ | _⟩
  all_goals simp at distinct
  all_goals apply finThree_rows_linearIndependent_of_det_ne_zero
  all_goals rw [Matrix.det_fin_three]
  all_goals
    simp [chhnNearyRow, chhnNearyNativeRole,
      Matrix.vecHead, Matrix.vecTail, Matrix.vecMul, Matrix.dotProduct,
      Fin.sum_univ_succ, Matrix.mul_apply]
  all_goals ring_nf
  all_goals first
    | exact upper_b_three_ne_six
    | linarith

theorem chhnNeary_rule_c_erase_c_columns_linearIndependent
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ []) :
    LinearIndependent ℚ
      ![chhnNearyColumn β,
        chhnNearyRole β body (.rule .c) *ᵥ chhnNearyColumn β,
        chhnNearyRole β body (.erase .c) *ᵥ chhnNearyColumn β] := by
  have lower_length : 4 ≤ (nearyLower β body (.rule .c)).length := by
    simp only [nearyLower, nearyBody, List.length_append, List.length_cons, List.length_nil]
    have encoded_nonempty : tagEncode β body ≠ [] :=
      (tagEncode_eq_nil_iff β body).not.mpr body_nonempty
    have encoded_length := List.length_pos.mpr encoded_nonempty
    omega
  have lower_scale_large :
      (3 : ℚ) < chhnNearyLowerCScale β body := by
    have exponent_large :
        (1 : Nat) < (nearyLower β body (.rule .c)).length := by
      omega
    exact pow_lt_pow_right (R := ℚ) (a := (3 : ℚ)) (by norm_num) exponent_large
  have marker_scale_positive : (0 : ℚ) < chhnNearyMarkerScale β := by
    exact pow_pos (by norm_num) _
  rw [chhnNearyColumn_eq_native,
    chhnNearyRole_eq_native β body (.rule .c),
    chhnNearyRole_eq_native β body (.erase .c)]
  apply finThree_rows_linearIndependent_of_det_ne_zero
  rw [show Matrix.det
      ((![chhnNearyNativeColumn β,
          chhnNearyNativeRole β body (.rule .c) *ᵥ chhnNearyNativeColumn β,
          chhnNearyNativeRole β body (.erase .c) *ᵥ chhnNearyNativeColumn β] :
        Matrix (Fin 3) (Fin 3) ℚ)) =
      chhnNearyMarkerScale β ^ 2 *
        (chhnNearyLowerCScale β body - 3) / 3 by
    rw [Matrix.det_fin_three]
    simp [chhnNearyNativeColumn, chhnNearyNativeRole,
      chhnNearyMarkerScale_eq, chhnNearyMarkerValue_eq,
      Matrix.mulVec, Matrix.dotProduct, Matrix.vecHead, Matrix.vecTail,
      Fin.sum_univ_succ]
    ring]
  exact div_ne_zero
    (mul_ne_zero (pow_ne_zero 2 (ne_of_gt marker_scale_positive))
      (sub_ne_zero.mpr (ne_of_gt lower_scale_large)))
    (by norm_num)

theorem chhnNeary_rule_b_erase_b_columns_linearIndependent
    (β : Nat) (body : List TagLetter) (three_le : 3 ≤ β) :
    LinearIndependent ℚ
      ![chhnNearyColumn β,
        chhnNearyRole β body (.rule .b) *ᵥ chhnNearyColumn β,
        chhnNearyRole β body (.erase .b) *ᵥ chhnNearyColumn β] := by
  have marker_scale_large :
      (9 : ℚ) < chhnNearyMarkerScale β := by
    rw [chhnNearyMarkerScale, nearyMarker_length]
    have exponent_large : (2 : Nat) < β + 1 := by
      omega
    exact pow_lt_pow_right (R := ℚ) (a := (3 : ℚ)) (by norm_num) exponent_large
  have marker_scale_ne_zero : chhnNearyMarkerScale β ≠ 0 := by
    exact ne_of_gt (pow_pos (by norm_num) _)
  rw [chhnNearyColumn_eq_native,
    chhnNearyRole_eq_native β body (.rule .b),
    chhnNearyRole_eq_native β body (.erase .b)]
  apply finThree_rows_linearIndependent_of_det_ne_zero
  rw [show Matrix.det
      ((![chhnNearyNativeColumn β,
          chhnNearyNativeRole β body (.rule .b) *ᵥ chhnNearyNativeColumn β,
          chhnNearyNativeRole β body (.erase .b) *ᵥ chhnNearyNativeColumn β] :
        Matrix (Fin 3) (Fin 3) ℚ)) =
      -4 * chhnNearyMarkerScale β *
        (chhnNearyMarkerScale β - 9) by
    rw [Matrix.det_fin_three]
    simp [chhnNearyNativeColumn, chhnNearyNativeRole,
      chhnNearyMarkerScale_eq, chhnNearyMarkerValue_eq,
      chhnNearyUpperB_eq, chhnNearyUpperBScale_eq,
      Matrix.mulVec, Matrix.dotProduct, Matrix.vecHead, Matrix.vecTail,
      Fin.sum_univ_succ]
    ring]
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) marker_scale_ne_zero)
    (sub_ne_zero.mpr (ne_of_gt marker_scale_large))

theorem chhnNeary_pairing_ne_zero (β : Nat) :
    chhnNearyRow ⬝ᵥ chhnNearyColumn β ≠ 0 := by
  have marker_ne_zero :
      (ternaryCode (nearyMarker β) : ℚ) ≠ 0 := by
    exact_mod_cast ternaryCode_nearyMarker_ne_zero β
  simpa [chhnNearyRow, chhnNearyColumn, sideTerminalColumn, sidePcpMatrix,
    sideTailBasis, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ] using
    marker_ne_zero

theorem chhnPlacement_semantic_at_nonseparator
    (placement : CHHNPlacement) (separator slot : CHHNSlot)
    (separator_value : placement separator = none) (slot_ne : slot ≠ separator) :
    ∃ tile, placement slot = some tile := by
  cases value_eq : placement slot with
  | none =>
      exfalso
      apply slot_ne
      apply placement.injective
      simpa [separator_value] using value_eq
  | some tile =>
      exact ⟨tile, rfl⟩

theorem chhnPlacement_distinct_semantics
    (placement : CHHNPlacement) (firstSlot secondSlot : CHHNSlot)
    (firstTile secondTile : NearyTile)
    (first_value : placement firstSlot = some firstTile)
    (second_value : placement secondSlot = some secondTile)
    (slots_ne : firstSlot ≠ secondSlot) :
    firstTile ≠ secondTile := by
  intro tiles_eq
  apply slots_ne
  apply placement.injective
  simpa [first_value, second_value] using congrArg some tiles_eq

theorem chhnPlacement_payload_slot
    (placement : CHHNPlacement) (tile : NearyTile)
    (root_ne : placement .root ≠ some tile) :
    ∃ slot : CHHNPayloadSlot, placement slot.toSlot = some tile := by
  cases source_eq : placement.symm (some tile) with
  | root =>
      apply False.elim
      apply root_ne
      simpa [source_eq] using placement.apply_symm_apply (some tile)
  | leftLeading =>
      refine ⟨.leftLeading, ?_⟩
      simpa [source_eq, CHHNPayloadSlot.toSlot] using
        placement.apply_symm_apply (some tile)
  | leftTrailing =>
      refine ⟨.leftTrailing, ?_⟩
      simpa [source_eq, CHHNPayloadSlot.toSlot] using
        placement.apply_symm_apply (some tile)
  | rightLeading =>
      refine ⟨.rightLeading, ?_⟩
      simpa [source_eq, CHHNPayloadSlot.toSlot] using
        placement.apply_symm_apply (some tile)
  | rightTrailing =>
      refine ⟨.rightTrailing, ?_⟩
      simpa [source_eq, CHHNPayloadSlot.toSlot] using
        placement.apply_symm_apply (some tile)

theorem chhnNeary_payload_column_pair
    (β : Nat) (body : List TagLetter) (placement : CHHNPlacement)
    (three_le : 3 ≤ β) (body_nonempty : body ≠ []) :
    ∃ first second : CHHNPayloadSlot,
      LinearIndependent ℚ
        ![chhnNearyColumn β,
          chhnSlotColumn (chhnPlacedSource β body placement)
            (chhnNearyColumn β) first.toSlot,
          chhnSlotColumn (chhnPlacedSource β body placement)
            (chhnNearyColumn β) second.toSlot] := by
  cases root_value : placement .root with
  | none =>
      obtain ⟨first, first_value⟩ :=
        chhnPlacement_payload_slot placement (.rule .c) (by simp [root_value])
      obtain ⟨second, second_value⟩ :=
        chhnPlacement_payload_slot placement (.erase .c) (by simp [root_value])
      refine ⟨first, second, ?_⟩
      simpa [chhnSlotColumn, chhnPlacedSource, chhnNearySource,
        first_value, second_value] using
        chhnNeary_rule_c_erase_c_columns_linearIndependent β body body_nonempty
  | some rootTile =>
      rcases rootTile with ⟨_ | _⟩ | ⟨_ | _⟩
      · obtain ⟨first, first_value⟩ :=
          chhnPlacement_payload_slot placement (.rule .c) (by simp [root_value])
        obtain ⟨second, second_value⟩ :=
          chhnPlacement_payload_slot placement (.erase .c) (by simp [root_value])
        refine ⟨first, second, ?_⟩
        simpa [chhnSlotColumn, chhnPlacedSource, chhnNearySource,
          first_value, second_value] using
          chhnNeary_rule_c_erase_c_columns_linearIndependent β body body_nonempty
      · obtain ⟨first, first_value⟩ :=
          chhnPlacement_payload_slot placement (.rule .b) (by simp [root_value])
        obtain ⟨second, second_value⟩ :=
          chhnPlacement_payload_slot placement (.erase .b) (by simp [root_value])
        refine ⟨first, second, ?_⟩
        simpa [chhnSlotColumn, chhnPlacedSource, chhnNearySource,
          first_value, second_value] using
          chhnNeary_rule_b_erase_b_columns_linearIndependent β body three_le
      · obtain ⟨first, first_value⟩ :=
          chhnPlacement_payload_slot placement (.rule .c) (by simp [root_value])
        obtain ⟨second, second_value⟩ :=
          chhnPlacement_payload_slot placement (.erase .c) (by simp [root_value])
        refine ⟨first, second, ?_⟩
        simpa [chhnSlotColumn, chhnPlacedSource, chhnNearySource,
          first_value, second_value] using
          chhnNeary_rule_c_erase_c_columns_linearIndependent β body body_nonempty
      · obtain ⟨first, first_value⟩ :=
          chhnPlacement_payload_slot placement (.rule .b) (by simp [root_value])
        obtain ⟨second, second_value⟩ :=
          chhnPlacement_payload_slot placement (.erase .b) (by simp [root_value])
        refine ⟨first, second, ?_⟩
        simpa [chhnSlotColumn, chhnPlacedSource, chhnNearySource,
          first_value, second_value] using
          chhnNeary_rule_b_erase_b_columns_linearIndependent β body three_le

theorem chhnNeary_prefix_certificate
    (β : Nat) (body : List TagLetter) (placement : CHHNPlacement)
    (three_le : 3 ≤ β) (body_nonempty : body ≠ []) :
    ∃ prefixes : CHHNPackedState → List CHHNControl,
      LinearIndependent ℚ fun index =>
        finitePrefixStates
          (chhnPackedGenerator (chhnPlacedSource β body placement))
          (chhnPackedRow chhnNearyRow) prefixes index := by
  generalize separator_eq : placement.symm none = separator
  have separator_value : placement separator = none := by
    rw [← separator_eq]
    exact placement.apply_symm_apply none
  cases separator with
  | root =>
      obtain ⟨leftTile, left_value⟩ :=
        chhnPlacement_semantic_at_nonseparator placement .root .leftTrailing
          separator_value (by decide)
      obtain ⟨rightTile, right_value⟩ :=
        chhnPlacement_semantic_at_nonseparator placement .root .rightTrailing
          separator_value (by decide)
      have tiles_ne : leftTile ≠ rightTile :=
        chhnPlacement_distinct_semantics placement .leftTrailing .rightTrailing
          leftTile rightTile left_value right_value (by decide)
      refine ⟨chhnRootPrefixes,
        chhnRootPrefixStates_linearIndependent
          (chhnPlacedSource β body placement) chhnNearyRow (chhnNearyColumn β)
          ?_ (chhnNeary_pairing_ne_zero β) ?_⟩
      · simp [chhnPlacedSource, chhnNearySource, separator_value]
      · simpa [chhnSlotRow, chhnPlacedSource, chhnNearySource,
          left_value, right_value] using
          chhnNeary_row_pair_linearIndependent β body leftTile rightTile
            three_le body_nonempty tiles_ne
  | leftLeading =>
      obtain ⟨rootTile, root_value⟩ :=
        chhnPlacement_semantic_at_nonseparator placement .leftLeading .root
          separator_value (by decide)
      obtain ⟨sameTile, same_value⟩ :=
        chhnPlacement_semantic_at_nonseparator placement .leftLeading .leftTrailing
          separator_value (by decide)
      obtain ⟨otherTile, other_value⟩ :=
        chhnPlacement_semantic_at_nonseparator placement .leftLeading .rightTrailing
          separator_value (by decide)
      have root_same : rootTile ≠ sameTile :=
        chhnPlacement_distinct_semantics placement .root .leftTrailing
          rootTile sameTile root_value same_value (by decide)
      have root_other : rootTile ≠ otherTile :=
        chhnPlacement_distinct_semantics placement .root .rightTrailing
          rootTile otherTile root_value other_value (by decide)
      have same_other : sameTile ≠ otherTile :=
        chhnPlacement_distinct_semantics placement .leftTrailing .rightTrailing
          sameTile otherTile same_value other_value (by decide)
      refine ⟨chhnLeftLeadingPrefixes,
        chhnLeftLeadingPrefixStates_linearIndependent
          (chhnPlacedSource β body placement) chhnNearyRow (chhnNearyColumn β)
          ?_ ?_ ?_⟩
      · simp [chhnPlacedSource, chhnNearySource, separator_value]
      · simpa [chhnSlotRow, chhnPlacedSource, chhnNearySource,
          root_value, same_value] using
          chhnNeary_row_pair_linearIndependent β body rootTile sameTile
            three_le body_nonempty root_same
      · simpa [chhnSlotRow, chhnPlacedSource, chhnNearySource,
          root_value, same_value, other_value] using
          chhnNeary_row_triple_linearIndependent β body rootTile sameTile otherTile
            three_le body_nonempty root_same root_other same_other
  | leftTrailing =>
      obtain ⟨rootTile, root_value⟩ :=
        chhnPlacement_semantic_at_nonseparator placement .leftTrailing .root
          separator_value (by decide)
      obtain ⟨leadingTile, leading_value⟩ :=
        chhnPlacement_semantic_at_nonseparator placement .leftTrailing .leftLeading
          separator_value (by decide)
      have tiles_ne : rootTile ≠ leadingTile :=
        chhnPlacement_distinct_semantics placement .root .leftLeading
          rootTile leadingTile root_value leading_value (by decide)
      refine ⟨chhnLeftTrailingPrefixes,
        chhnLeftTrailingPrefixStates_linearIndependent
          (chhnPlacedSource β body placement) chhnNearyRow (chhnNearyColumn β)
          ?_ (chhnNeary_pairing_ne_zero β) ?_⟩
      · simp [chhnPlacedSource, chhnNearySource, separator_value]
      · simpa [chhnSlotRow, chhnPlacedSource, chhnNearySource,
          root_value, leading_value] using
          chhnNeary_composite_row_linearIndependent β body rootTile leadingTile
            three_le body_nonempty tiles_ne
  | rightLeading =>
      obtain ⟨rootTile, root_value⟩ :=
        chhnPlacement_semantic_at_nonseparator placement .rightLeading .root
          separator_value (by decide)
      obtain ⟨sameTile, same_value⟩ :=
        chhnPlacement_semantic_at_nonseparator placement .rightLeading .rightTrailing
          separator_value (by decide)
      obtain ⟨otherTile, other_value⟩ :=
        chhnPlacement_semantic_at_nonseparator placement .rightLeading .leftTrailing
          separator_value (by decide)
      have root_same : rootTile ≠ sameTile :=
        chhnPlacement_distinct_semantics placement .root .rightTrailing
          rootTile sameTile root_value same_value (by decide)
      have root_other : rootTile ≠ otherTile :=
        chhnPlacement_distinct_semantics placement .root .leftTrailing
          rootTile otherTile root_value other_value (by decide)
      have same_other : sameTile ≠ otherTile :=
        chhnPlacement_distinct_semantics placement .rightTrailing .leftTrailing
          sameTile otherTile same_value other_value (by decide)
      refine ⟨chhnRightLeadingPrefixes,
        chhnRightLeadingPrefixStates_linearIndependent
          (chhnPlacedSource β body placement) chhnNearyRow (chhnNearyColumn β)
          ?_ ?_ ?_⟩
      · simp [chhnPlacedSource, chhnNearySource, separator_value]
      · simpa [chhnSlotRow, chhnPlacedSource, chhnNearySource,
          root_value, same_value] using
          chhnNeary_row_pair_linearIndependent β body rootTile sameTile
            three_le body_nonempty root_same
      · simpa [chhnSlotRow, chhnPlacedSource, chhnNearySource,
          root_value, same_value, other_value] using
          chhnNeary_row_triple_linearIndependent β body rootTile sameTile otherTile
            three_le body_nonempty root_same root_other same_other
  | rightTrailing =>
      obtain ⟨rootTile, root_value⟩ :=
        chhnPlacement_semantic_at_nonseparator placement .rightTrailing .root
          separator_value (by decide)
      obtain ⟨leadingTile, leading_value⟩ :=
        chhnPlacement_semantic_at_nonseparator placement .rightTrailing .rightLeading
          separator_value (by decide)
      have tiles_ne : rootTile ≠ leadingTile :=
        chhnPlacement_distinct_semantics placement .root .rightLeading
          rootTile leadingTile root_value leading_value (by decide)
      refine ⟨chhnRightTrailingPrefixes,
        chhnRightTrailingPrefixStates_linearIndependent
          (chhnPlacedSource β body placement) chhnNearyRow (chhnNearyColumn β)
          ?_ (chhnNeary_pairing_ne_zero β) ?_⟩
      · simp [chhnPlacedSource, chhnNearySource, separator_value]
      · simpa [chhnSlotRow, chhnPlacedSource, chhnNearySource,
          root_value, leading_value] using
          chhnNeary_composite_row_linearIndependent β body rootTile leadingTile
            three_le body_nonempty tiles_ne

theorem chhnNeary_exactRepresentation_six_le_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : Nat) (body : List TagLetter) (placement : CHHNPlacement)
    (three_le : 3 ≤ β) (body_nonempty : body ≠ [])
    (generators : CHHNControl → Matrix ι ι ℚ) (left right : ι → ℚ)
    (exact : RepresentsSeries
      (linearCoefficient
        (chhnPackedGenerator (chhnPlacedSource β body placement))
        (chhnPackedRow chhnNearyRow) (chhnPackedColumn (chhnNearyColumn β)))
      generators left right) :
    6 ≤ Fintype.card ι := by
  obtain ⟨prefixes, prefix_independent⟩ :=
    chhnNeary_prefix_certificate β body placement three_le body_nonempty
  obtain ⟨first, second, column_basis⟩ :=
    chhnNeary_payload_column_pair β body placement three_le body_nonempty
  have suffix_independent :=
    chhnReachableSuffixStates_linearIndependent
      (chhnPlacedSource β body placement) (chhnNearyColumn β)
      first second column_basis
  exact chhnExactRepresentation_six_le_card
    (chhnPlacedSource β body placement) chhnNearyRow (chhnNearyColumn β)
    prefixes (chhnReachableSuffixes first second)
    prefix_independent suffix_independent generators left right exact

end MatrixMortality
