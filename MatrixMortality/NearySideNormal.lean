import MatrixMortality.SideNormal

/-!
# Evaluated side-normal Neary matrices

This file owns the arithmetic shared by the CHHN, paired-binary, and prefix certificates:
Neary's marker and role words evaluated in the side-normal ternary representation.
-/

namespace MatrixMortality

open scoped Matrix

/-! ## Integer marker arithmetic -/

/-- Positional value of the Neary marker, viewed as an integer. -/
def nearyMarkerValueInt (β : Nat) : ℤ := ternaryCode (nearyMarker β)

/-- Base-three scale at deletion width `β`. -/
def nearyWidthScaleInt (β : Nat) : ℤ := (3 : ℤ) ^ β

/-- Appending one zero triples the marker value and adds one. -/
theorem nearyMarkerValueInt_succ (β : Nat) :
    nearyMarkerValueInt (β + 1) = 3 * nearyMarkerValueInt β + 1 := by
  have marker_succ :
      nearyMarker (β + 1) = nearyMarker β ++ [false] := by
    simp [nearyMarker, List.replicate_succ']
  rw [nearyMarkerValueInt, marker_succ, ternaryCode_append]
  norm_num [nearyMarkerValueInt, ternaryCode_singleton, ternaryDigit]

/-- The marker value satisfies `2m+1=5·3^β`. -/
theorem nearyMarkerValueInt_relation (β : Nat) :
    2 * nearyMarkerValueInt β + 1 = 5 * nearyWidthScaleInt β := by
  induction β with
  | zero =>
      norm_num [nearyMarkerValueInt, nearyWidthScaleInt, nearyMarker, ternaryCode, ternaryDigit]
  | succ β induction =>
      rw [nearyMarkerValueInt_succ]
      change 2 * (3 * nearyMarkerValueInt β + 1) + 1 =
        5 * nearyWidthScaleInt (β + 1)
      rw [nearyWidthScaleInt, pow_succ, ← nearyWidthScaleInt]
      nlinarith

/-- Positional value of the encoded tag letter `b`. -/
theorem ternaryCode_tagCode_b (β : Nat) :
    (ternaryCode (tagCode β .b) : ℤ) = 3 * nearyMarkerValueInt β + 2 := by
  have code_eq : tagCode β .b = nearyMarker β ++ [true] := by
    simp [tagCode, nearyMarker]
  rw [code_eq, ternaryCode_append]
  norm_num [nearyMarkerValueInt, ternaryCode, ternaryDigit]

@[simp] theorem nearyMarker_length (β : Nat) : (nearyMarker β).length = β + 1 := by
  simp [nearyMarker]

@[simp] theorem tagCode_b_length (β : Nat) : (tagCode β .b).length = β + 2 := by
  simp [tagCode]

@[simp] theorem ternaryCode_neary_rule_b (β : Nat) (body : List TagLetter) :
    ternaryCode (nearyLower β body (.rule .b)) = 25 := by
  norm_num [nearyLower, ternaryCode_cons, ternaryDigit]

@[simp] theorem ternaryCode_neary_erase (β : Nat) (body : List TagLetter)
    (letter : TagLetter) :
    ternaryCode (nearyLower β body (.erase letter)) = 1 := by
  norm_num [nearyLower, ternaryCode_singleton, ternaryDigit]

/-! ## Rational side-normal forms -/

/-- The boundary row used by the side-normal Neary representation. -/
def nearySideRow : Fin 3 → ℚ := ![1, 0, 0]

/-- The fixed-boundary column used by the side-normal Neary representation. -/
def nearySideColumn (β : Nat) : Fin 3 → ℚ :=
  sideTerminalColumn ℚ (nearyMarker β)

/-- One ordinary side-normal Neary role matrix. -/
def nearySideRole (β : Nat) (body : List TagLetter) (tile : NearyTile) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  sidePcpMatrix ℚ (nearyUpper β tile) (nearyLower β body tile)

/-- Positional value of the long upper word carried by the letter `b`. -/
def nearySideUpperB (β : Nat) : ℚ :=
  ternaryCode (tagCode β .b)

/-- Positional value of the body-dependent lower rule word carried by `c`. -/
def nearySideLowerC (β : Nat) (body : List TagLetter) : ℚ :=
  ternaryCode (nearyLower β body (.rule .c))

/-- Base-three scale of the fixed right marker. -/
def nearySideMarkerScale (β : Nat) : ℚ :=
  (3 : ℚ) ^ (nearyMarker β).length

/-- Positional value of the fixed right marker. -/
def nearySideMarkerValue (β : Nat) : ℚ :=
  ternaryCode (nearyMarker β)

/-- Base-three scale of the long upper word carried by `b`. -/
def nearySideUpperBScale (β : Nat) : ℚ :=
  (3 : ℚ) ^ (tagCode β .b).length

/-- Base-three scale of the body-dependent lower rule word carried by `c`. -/
def nearySideLowerCScale (β : Nat) (body : List TagLetter) : ℚ :=
  (3 : ℚ) ^ (nearyLower β body (.rule .c)).length

/-- The terminal `10` of the rule-`c` lower word fixes its two least significant ternary
digits. -/
theorem nearySideLowerC_eq_nine_mul_add_seven (β : Nat) (body : List TagLetter) :
    nearySideLowerC β body =
      9 * ternaryCode (true :: tagEncode β body) + 7 := by
  simp [nearySideLowerC, nearyLower, ternaryCode_append, ternaryCode_cons,
    ternaryDigit]
  ring

/-- The rule-`c` lower scale contains the same terminal two-digit factor. -/
theorem nearySideLowerCScale_eq_nine_mul (β : Nat) (body : List TagLetter) :
    nearySideLowerCScale β body =
      9 * (3 : ℚ) ^ (tagEncode β body).length.succ := by
  simp [nearySideLowerCScale, nearyLower, pow_add]
  ring

/-- The fixed right column after evaluating its marker. -/
def nearySideNativeColumn (β : Nat) : Fin 3 → ℚ :=
  ![nearySideMarkerValue β, -1, nearySideMarkerScale β]

/-- Closed semantic normal form of the fixed right column. -/
theorem nearySideColumn_eq_native (β : Nat) :
    nearySideColumn β = nearySideNativeColumn β := by
  ext coordinate
  fin_cases coordinate <;>
    simp [nearySideColumn, nearySideNativeColumn, nearySideMarkerValue,
      nearySideMarkerScale, sideTerminalColumn, sidePcpMatrix, sideTailBasis,
      Matrix.mulVec, Matrix.dotProduct, Matrix.vecHead, Matrix.vecTail,
      Fin.sum_univ_succ]

/-- The four Neary matrices after all fixed words have been evaluated. -/
def nearySideNativeRole (β : Nat) (body : List TagLetter) :
    NearyTile → Matrix (Fin 3) (Fin 3) ℚ
  | .rule .c =>
      !![1, nearySideLowerC β body, 2;
         0, nearySideLowerCScale β body, 0;
         0, 0, 3]
  | .rule .b =>
      !![1, 25, nearySideUpperB β;
         0, 27, 0;
         0, 0, nearySideUpperBScale β]
  | .erase .c =>
      !![1, 1, 2;
         0, 3, 0;
         0, 0, 3]
  | .erase .b =>
      !![1, 1, nearySideUpperB β;
         0, 3, 0;
         0, 0, nearySideUpperBScale β]

/-- Closed semantic normal form of each Neary role matrix. -/
theorem nearySideRole_eq_native (β : Nat) (body : List TagLetter) (tile : NearyTile) :
    nearySideRole β body tile = nearySideNativeRole β body tile := by
  ext row column
  cases tile with
  | rule letter =>
      cases letter <;> fin_cases row <;> fin_cases column <;>
        simp [nearySideRole, nearySideNativeRole, nearySideUpperB,
          nearySideLowerC, nearySideMarkerScale, nearySideUpperBScale,
          nearySideLowerCScale, sidePcpMatrix, nearyUpper, nearyLower,
          Matrix.vecHead, Matrix.vecTail, ternaryDigit]
      all_goals norm_num [tagCode, ternaryCode, ternaryDigit, Nat.ofDigits]
  | erase letter =>
      cases letter <;> fin_cases row <;> fin_cases column <;>
        simp [nearySideRole, nearySideNativeRole, nearySideUpperB,
          nearySideLowerC, nearySideMarkerScale, nearySideUpperBScale,
          nearySideLowerCScale, sidePcpMatrix, nearyUpper, nearyLower,
          Matrix.vecHead, Matrix.vecTail, ternaryDigit]
      all_goals norm_num [tagCode, ternaryCode, ternaryDigit, Nat.ofDigits]

/-- Closed semantic normal form of the four reachable Neary rows. -/
def nearySideNativeRow (β : Nat) (body : List TagLetter) : NearyTile → Fin 3 → ℚ
  | .rule .c => ![1, nearySideLowerC β body, 2]
  | .rule .b => ![1, 25, nearySideUpperB β]
  | .erase .c => ![1, 1, 2]
  | .erase .b => ![1, 1, nearySideUpperB β]

/-- Multiplication by the boundary row selects the native affine row. -/
theorem nearySideRow_vecMul_role (β : Nat) (body : List TagLetter) (tile : NearyTile) :
    nearySideRow ᵥ* nearySideRole β body tile =
      nearySideNativeRow β body tile := by
  rw [nearySideRole_eq_native]
  cases tile with
  | rule letter =>
      cases letter <;> ext coordinate <;> fin_cases coordinate <;>
        simp [nearySideRow, nearySideNativeRow, nearySideNativeRole,
          Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_succ]
  | erase letter =>
      cases letter <;> ext coordinate <;> fin_cases coordinate <;>
        simp [nearySideRow, nearySideNativeRow, nearySideNativeRole,
          Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_succ]

@[simp] theorem ternaryCode_tagCode_c (β : Nat) :
    ternaryCode (tagCode β .c) = 2 := by
  norm_num [tagCode, ternaryCode_singleton, ternaryDigit]

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
theorem nearySideUpperB_relation (β : Nat) :
    2 * nearySideUpperB β = 5 * nearySideMarkerScale β + 1 := by
  have marker_relation :
      (2 : ℚ) * nearyMarkerValueInt β + 1 = 5 * (3 : ℚ) ^ β := by
    have casted :
        (2 : ℚ) * nearyMarkerValueInt β + 1 = 5 * nearyWidthScaleInt β := by
      exact_mod_cast nearyMarkerValueInt_relation β
    simpa [nearyWidthScaleInt] using casted
  have upper_relation :
      nearySideUpperB β = 3 * nearyMarkerValueInt β + 2 := by
    have casted :
        (ternaryCode (tagCode β .b) : ℚ) = 3 * nearyMarkerValueInt β + 2 := by
      exact_mod_cast ternaryCode_tagCode_b β
    simpa [nearySideUpperB] using casted
  rw [upper_relation]
  simp only [nearySideMarkerScale, nearyMarker_length, nearyWidthScaleInt, pow_succ]
  nlinarith

/-- The long upper scale is three times the marker scale. -/
theorem nearySideUpperBScale_relation (β : Nat) :
    nearySideUpperBScale β = 3 * nearySideMarkerScale β := by
  simp only [nearySideUpperBScale, tagCode_b_length, nearySideMarkerScale,
    nearyMarker_length]
  rw [show β + 2 = (β + 1) + 1 by omega, pow_succ]
  ring

/-- Closed base-three scale of the fixed right marker. -/
theorem nearySideMarkerScale_eq (β : Nat) :
    nearySideMarkerScale β = 3 * (3 : ℚ) ^ β := by
  simp only [nearySideMarkerScale, nearyMarker_length, pow_succ]
  ring

/-- Closed positional value of the fixed right marker. -/
theorem nearySideMarkerValue_eq (β : Nat) :
    nearySideMarkerValue β = (5 * (3 : ℚ) ^ β - 1) / 2 := by
  have casted :
      (2 : ℚ) * nearyMarkerValueInt β + 1 = 5 * nearyWidthScaleInt β := by
    exact_mod_cast nearyMarkerValueInt_relation β
  simp only [nearySideMarkerValue, nearyMarkerValueInt, nearyWidthScaleInt] at casted ⊢
  norm_num at casted
  linarith

/-- Closed positional value of the long upper word. -/
theorem nearySideUpperB_eq (β : Nat) :
    nearySideUpperB β = (15 * (3 : ℚ) ^ β + 1) / 2 := by
  rw [show (15 : ℚ) * 3 ^ β = 5 * (3 * 3 ^ β) by ring,
    ← nearySideMarkerScale_eq]
  nlinarith [nearySideUpperB_relation β]

/-- Closed base-three scale of the long upper word. -/
theorem nearySideUpperBScale_eq (β : Nat) :
    nearySideUpperBScale β = 9 * (3 : ℚ) ^ β := by
  rw [nearySideUpperBScale_relation, nearySideMarkerScale_eq]
  ring

/-- Every admissible marker scale exceeds the constants used by the certificates. -/
theorem nearySideMarkerScale_gt_twenty_five (β : Nat) (three_le : 3 ≤ β) :
    (25 : ℚ) < nearySideMarkerScale β := by
  rw [nearySideMarkerScale, nearyMarker_length]
  calc
    (25 : ℚ) < 3 ^ 4 := by norm_num
    _ ≤ 3 ^ (β + 1) := pow_le_pow_right (by norm_num) (by omega)

end MatrixMortality
