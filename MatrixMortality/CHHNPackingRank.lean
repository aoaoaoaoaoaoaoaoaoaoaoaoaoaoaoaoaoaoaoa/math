import MatrixMortality.CHHNPacking
import MatrixMortality.NearySideNormal

/-!
# Exact rank of every Neary CHHN placement

The five three-state Neary generators may occupy the five CHHN packing slots in any order.  A
six-row and six-column certificate exposes every packed state for every such placement.
-/

namespace MatrixMortality

open scoped Matrix
open CHHNPacking.Certificate

/-- The four ordinary roles and their rank-one fixed-boundary separator. -/
def chhnNearySource (β : Nat) (body : List TagLetter) :
    Option NearyTile → Matrix (Fin 3) (Fin 3) ℚ
  | none => Matrix.vecMulVec (nearySideColumn β) nearySideRow
  | some tile => nearySideRole β body tile

/-- A placement bijects the five semantic source matrices with the five packing slots. -/
abbrev CHHNPlacement := CHHNSlot ≃ Option NearyTile

/-- Source matrices occupying one concrete placement. -/
def chhnPlacedSource (β : Nat) (body : List TagLetter) (placement : CHHNPlacement) :
    CHHNSlot → Matrix (Fin 3) (Fin 3) ℚ :=
  chhnNearySource β body ∘ placement

/-- Three independent rows follow from a nonzero `3 × 3` row determinant. -/
private theorem finThree_rows_linearIndependent_of_det_ne_zero
    {K : Type*} [Field K] (matrix : Matrix (Fin 3) (Fin 3) K)
    (det_ne_zero : matrix.det ≠ 0) :
    LinearIndependent K fun index => matrix index := by
  apply Matrix.linearIndependent_rows_iff_isUnit.mpr
  apply matrix.isUnit_iff_isUnit_det.mpr
  exact isUnit_iff_ne_zero.mpr det_ne_zero

private theorem chhnNeary_row_pair_linearIndependent
    (β : Nat) (body : List TagLetter) (first second : NearyTile)
    (three_le : 3 ≤ β) (body_nonempty : body ≠ []) (distinct : first ≠ second) :
    LinearIndependent ℚ
      ![nearySideRow,
        nearySideRow ᵥ* nearySideRole β body first,
        nearySideRow ᵥ* nearySideRole β body second] := by
  have upper_b_large_q :
      (50 : ℚ) < nearySideUpperB β := by
    simpa [nearySideUpperB] using
      (show (50 : ℚ) < ternaryCode (tagCode β .b) by
        exact_mod_cast ternaryCode_tagCode_b_gt_fifty β three_le)
  have lower_c_large_q :
      (25 : ℚ) < nearySideLowerC β body := by
    simpa [nearySideLowerC] using
      (show (25 : ℚ) < ternaryCode (nearyLower β body (.rule .c)) by
        exact_mod_cast
          ternaryCode_neary_rule_c_gt_twenty_five β body body_nonempty)
  have upper_b_large_raw :
      (50 : ℚ) < ternaryCode (tagCode β .b) := by
    simpa [nearySideUpperB] using upper_b_large_q
  have lower_c_large_raw :
      (25 : ℚ) < ternaryCode (nearyLower β body (.rule .c)) := by
    simpa [nearySideLowerC] using lower_c_large_q
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
  rw [nearySideRow_vecMul_role β body first,
    nearySideRow_vecMul_role β body second]
  rcases first with ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    rcases second with ⟨_ | _⟩ | ⟨_ | _⟩
  all_goals simp at distinct
  all_goals apply finThree_rows_linearIndependent_of_det_ne_zero
  all_goals rw [Matrix.det_fin_three]
  all_goals
    simp [nearySideRow, nearySideNativeRow, nearySideUpperB,
      nearySideLowerC, Matrix.vecHead, Matrix.vecTail]
  all_goals ring_nf
  all_goals first | assumption | nlinarith

private theorem chhnNeary_row_triple_linearIndependent
    (β : Nat) (body : List TagLetter) (first second third : NearyTile)
    (three_le : 3 ≤ β) (body_nonempty : body ≠ [])
    (first_second : first ≠ second) (first_third : first ≠ third)
    (second_third : second ≠ third) :
    LinearIndependent ℚ
      ![nearySideRow ᵥ* nearySideRole β body first,
        nearySideRow ᵥ* nearySideRole β body second,
        nearySideRow ᵥ* nearySideRole β body third] := by
  have upper_b_large_q :
      (50 : ℚ) < nearySideUpperB β := by
    simpa [nearySideUpperB] using
      (show (50 : ℚ) < ternaryCode (tagCode β .b) by
        exact_mod_cast ternaryCode_tagCode_b_gt_fifty β three_le)
  have lower_c_large_q :
      (25 : ℚ) < nearySideLowerC β body := by
    simpa [nearySideLowerC] using
      (show (25 : ℚ) < ternaryCode (nearyLower β body (.rule .c)) by
        exact_mod_cast
          ternaryCode_neary_rule_c_gt_twenty_five β body body_nonempty)
  have upper_b_large_raw :
      (50 : ℚ) < ternaryCode (tagCode β .b) := by
    simpa [nearySideUpperB] using upper_b_large_q
  have lower_c_large_raw :
      (25 : ℚ) < ternaryCode (nearyLower β body (.rule .c)) := by
    simpa [nearySideLowerC] using lower_c_large_q
  have product_positive :
      (0 : ℚ) <
        (ternaryCode (tagCode β .b) - 2) *
          (ternaryCode (nearyLower β body (.rule .c)) - 1) := by
    exact mul_pos (by linarith [upper_b_large_raw]) (by linarith [lower_c_large_raw])
  ring_nf at product_positive
  rw [nearySideRow_vecMul_role β body first,
    nearySideRow_vecMul_role β body second,
    nearySideRow_vecMul_role β body third]
  rcases first with ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    rcases second with ⟨_ | _⟩ | ⟨_ | _⟩ <;>
      rcases third with ⟨_ | _⟩ | ⟨_ | _⟩
  all_goals simp at first_second first_third second_third
  all_goals apply finThree_rows_linearIndependent_of_det_ne_zero
  all_goals rw [Matrix.det_fin_three]
  all_goals
    simp [nearySideNativeRow, nearySideUpperB, nearySideLowerC,
      Matrix.vecHead, Matrix.vecTail]
  all_goals ring_nf
  all_goals linarith

private theorem chhnNeary_composite_row_linearIndependent
    (β : Nat) (body : List TagLetter) (root leading : NearyTile)
    (three_le : 3 ≤ β) (body_nonempty : body ≠ []) (distinct : root ≠ leading) :
    LinearIndependent ℚ
      ![nearySideRow,
        nearySideRow ᵥ* nearySideRole β body root,
        nearySideRow ᵥ*
          (nearySideRole β body leading * nearySideRole β body root)] := by
  have upper_b_large_q :
      (50 : ℚ) < nearySideUpperB β := by
    simpa [nearySideUpperB] using
      (show (50 : ℚ) < ternaryCode (tagCode β .b) by
        exact_mod_cast ternaryCode_tagCode_b_gt_fifty β three_le)
  have lower_c_large_q :
      (25 : ℚ) < nearySideLowerC β body := by
    simpa [nearySideLowerC] using
      (show (25 : ℚ) < ternaryCode (nearyLower β body (.rule .c)) by
        exact_mod_cast
          ternaryCode_neary_rule_c_gt_twenty_five β body body_nonempty)
  have lower_c_scale_dominated :
      nearySideLowerCScale β body < 3 * nearySideLowerC β body := by
    have casted :
        ((3 ^ (nearyLower β body (.rule .c)).length : Nat) : ℚ) <
          3 * ternaryCode (nearyLower β body (.rule .c)) := by
      exact_mod_cast neary_rule_c_scale_lt_three_code β body
    simpa [nearySideLowerCScale, nearySideLowerC] using casted
  have marker_scale_large :=
    nearySideMarkerScale_gt_twenty_five β three_le
  have upper_b_relation := nearySideUpperB_relation β
  have upper_b_scale_relation := nearySideUpperBScale_relation β
  have upper_b_positive : (0 : ℚ) < nearySideUpperB β := by
    linarith
  have lower_c_positive : (0 : ℚ) < nearySideLowerC β body := by
    linarith
  have upper_gap_product_positive :
      0 < (nearySideUpperB β - 50) * nearySideLowerC β body :=
    mul_pos (sub_pos.mpr upper_b_large_q) lower_c_positive
  have lower_gap_product_positive :
      0 < nearySideUpperB β * (nearySideLowerC β body - 25) :=
    mul_pos upper_b_positive (sub_pos.mpr lower_c_large_q)
  have upper_b_three_ne_six :
      -6 + nearySideUpperB β * 3 ≠ 0 := by
    nlinarith
  have upper_b_scale_large :
      (75 : ℚ) < nearySideUpperBScale β := by
    nlinarith
  have upper_b_scale_gap_product_positive :
      0 < nearySideUpperB β * (nearySideUpperBScale β - 75) :=
    mul_pos upper_b_positive (sub_pos.mpr upper_b_scale_large)
  ring_nf at upper_gap_product_positive lower_gap_product_positive
  ring_nf at upper_b_scale_gap_product_positive
  rw [nearySideRole_eq_native β body root,
    nearySideRole_eq_native β body leading]
  rcases root with ⟨_ | _⟩ | ⟨_ | _⟩ <;>
    rcases leading with ⟨_ | _⟩ | ⟨_ | _⟩
  all_goals simp at distinct
  all_goals apply finThree_rows_linearIndependent_of_det_ne_zero
  all_goals rw [Matrix.det_fin_three]
  all_goals
    simp [nearySideRow, nearySideNativeRole,
      Matrix.vecHead, Matrix.vecTail, Matrix.vecMul, Matrix.dotProduct,
      Fin.sum_univ_succ, Matrix.mul_apply]
  all_goals ring_nf
  all_goals first
    | exact upper_b_three_ne_six
    | linarith

private theorem chhnNeary_rule_c_erase_c_columns_linearIndependent
    (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ []) :
    LinearIndependent ℚ
      ![nearySideColumn β,
        nearySideRole β body (.rule .c) *ᵥ nearySideColumn β,
        nearySideRole β body (.erase .c) *ᵥ nearySideColumn β] := by
  have lower_length : 4 ≤ (nearyLower β body (.rule .c)).length := by
    simp only [nearyLower, nearyBody, List.length_append, List.length_cons, List.length_nil]
    have encoded_nonempty : tagEncode β body ≠ [] :=
      (tagEncode_eq_nil_iff β body).not.mpr body_nonempty
    have encoded_length := List.length_pos.mpr encoded_nonempty
    omega
  have lower_scale_large :
      (3 : ℚ) < nearySideLowerCScale β body := by
    have exponent_large :
        (1 : Nat) < (nearyLower β body (.rule .c)).length := by
      omega
    exact pow_lt_pow_right (R := ℚ) (a := (3 : ℚ)) (by norm_num) exponent_large
  have marker_scale_positive : (0 : ℚ) < nearySideMarkerScale β := by
    exact pow_pos (by norm_num) _
  rw [nearySideColumn_eq_native,
    nearySideRole_eq_native β body (.rule .c),
    nearySideRole_eq_native β body (.erase .c)]
  apply finThree_rows_linearIndependent_of_det_ne_zero
  rw [show Matrix.det
      ((![nearySideNativeColumn β,
          nearySideNativeRole β body (.rule .c) *ᵥ nearySideNativeColumn β,
          nearySideNativeRole β body (.erase .c) *ᵥ nearySideNativeColumn β] :
        Matrix (Fin 3) (Fin 3) ℚ)) =
      nearySideMarkerScale β ^ 2 *
        (nearySideLowerCScale β body - 3) / 3 by
    rw [Matrix.det_fin_three]
    simp [nearySideNativeColumn, nearySideNativeRole,
      nearySideMarkerScale_eq, nearySideMarkerValue_eq,
      Matrix.mulVec, Matrix.dotProduct, Matrix.vecHead, Matrix.vecTail,
      Fin.sum_univ_succ]
    ring]
  exact div_ne_zero
    (mul_ne_zero (pow_ne_zero 2 (ne_of_gt marker_scale_positive))
      (sub_ne_zero.mpr (ne_of_gt lower_scale_large)))
    (by norm_num)

private theorem chhnNeary_rule_b_erase_b_columns_linearIndependent
    (β : Nat) (body : List TagLetter) (three_le : 3 ≤ β) :
    LinearIndependent ℚ
      ![nearySideColumn β,
        nearySideRole β body (.rule .b) *ᵥ nearySideColumn β,
        nearySideRole β body (.erase .b) *ᵥ nearySideColumn β] := by
  have marker_scale_large :
      (9 : ℚ) < nearySideMarkerScale β := by
    rw [nearySideMarkerScale, nearyMarker_length]
    have exponent_large : (2 : Nat) < β + 1 := by
      omega
    exact pow_lt_pow_right (R := ℚ) (a := (3 : ℚ)) (by norm_num) exponent_large
  have marker_scale_ne_zero : nearySideMarkerScale β ≠ 0 := by
    exact ne_of_gt (pow_pos (by norm_num) _)
  rw [nearySideColumn_eq_native,
    nearySideRole_eq_native β body (.rule .b),
    nearySideRole_eq_native β body (.erase .b)]
  apply finThree_rows_linearIndependent_of_det_ne_zero
  rw [show Matrix.det
      ((![nearySideNativeColumn β,
          nearySideNativeRole β body (.rule .b) *ᵥ nearySideNativeColumn β,
          nearySideNativeRole β body (.erase .b) *ᵥ nearySideNativeColumn β] :
        Matrix (Fin 3) (Fin 3) ℚ)) =
      -4 * nearySideMarkerScale β *
        (nearySideMarkerScale β - 9) by
    rw [Matrix.det_fin_three]
    simp [nearySideNativeColumn, nearySideNativeRole,
      nearySideMarkerScale_eq, nearySideMarkerValue_eq,
      nearySideUpperB_eq, nearySideUpperBScale_eq,
      Matrix.mulVec, Matrix.dotProduct, Matrix.vecHead, Matrix.vecTail,
      Fin.sum_univ_succ]
    ring]
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) marker_scale_ne_zero)
    (sub_ne_zero.mpr (ne_of_gt marker_scale_large))

private theorem chhnNeary_pairing_ne_zero (β : Nat) :
    nearySideRow ⬝ᵥ nearySideColumn β ≠ 0 := by
  have marker_ne_zero :
      (ternaryCode (nearyMarker β) : ℚ) ≠ 0 := by
    exact_mod_cast ternaryCode_nearyMarker_ne_zero β
  simpa [nearySideRow, nearySideColumn, sideTerminalColumn, sidePcpMatrix,
    sideTailBasis, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ] using
    marker_ne_zero

private theorem chhnPlacement_semantic_at_nonseparator
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

private theorem chhnPlacement_distinct_semantics
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

private theorem chhnPlacement_payload_slot
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

private theorem chhnNeary_payload_column_pair
    (β : Nat) (body : List TagLetter) (placement : CHHNPlacement)
    (three_le : 3 ≤ β) (body_nonempty : body ≠ []) :
    ∃ first second : CHHNPayloadSlot,
      LinearIndependent ℚ
        ![nearySideColumn β,
          chhnSlotColumn (chhnPlacedSource β body placement)
            (nearySideColumn β) first.toSlot,
          chhnSlotColumn (chhnPlacedSource β body placement)
            (nearySideColumn β) second.toSlot] := by
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

private theorem chhnNeary_prefix_certificate
    (β : Nat) (body : List TagLetter) (placement : CHHNPlacement)
    (three_le : 3 ≤ β) (body_nonempty : body ≠ []) :
    ∃ prefixes : CHHNPackedState → List CHHNControl,
      LinearIndependent ℚ fun index =>
        finitePrefixStates
          (chhnPackedGenerator (chhnPlacedSource β body placement))
          (chhnPackedRow nearySideRow) prefixes index := by
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
          (chhnPlacedSource β body placement) nearySideRow (nearySideColumn β)
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
          (chhnPlacedSource β body placement) nearySideRow (nearySideColumn β)
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
          (chhnPlacedSource β body placement) nearySideRow (nearySideColumn β)
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
          (chhnPlacedSource β body placement) nearySideRow (nearySideColumn β)
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
          (chhnPlacedSource β body placement) nearySideRow (nearySideColumn β)
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
        (chhnPackedRow nearySideRow) (chhnPackedColumn (nearySideColumn β)))
      generators left right) :
    6 ≤ Fintype.card ι := by
  obtain ⟨prefixes, prefix_independent⟩ :=
    chhnNeary_prefix_certificate β body placement three_le body_nonempty
  obtain ⟨first, second, column_basis⟩ :=
    chhnNeary_payload_column_pair β body placement three_le body_nonempty
  have suffix_independent :=
    chhnReachableSuffixStates_linearIndependent
      (chhnPlacedSource β body placement) (nearySideColumn β)
      first second column_basis
  exact chhnExactRepresentation_six_le_card
    (chhnPlacedSource β body placement) nearySideRow (nearySideColumn β)
    prefixes (chhnReachableSuffixes first second)
    prefix_independent suffix_independent generators left right exact

end MatrixMortality
