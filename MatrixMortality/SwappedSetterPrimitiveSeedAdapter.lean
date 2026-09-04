import MatrixMortality.SwappedSetterPrimitivePullback

set_option autoImplicit false

/-!
# Primitive empty-front seed coordinates

This module converts the signed empty-front antecedent into exact positive primitive natural
coordinates. It identifies every half-head factor in the raw content with one target-code gcd,
then instantiates the raw and post-cancellation pullback criteria from `MM-S106`. It does not
classify physical predecessor words, prove entry reachability, or assert a pole.
-/

namespace MatrixMortality.SwappedSetterPrimitiveSeedAdapter

open SwappedSetterMultitransfer SwappedSetterEmptyFrontChamber
  SwappedSetterDeletionCContraction SwappedSetterPrimitivePullback
  SwappedSetterEmptyFrontRay SwappedSetterThresholdCarry

private theorem natCoprime_of_isCoprime_int {left right : Nat}
    (coprime : IsCoprime (left : ℤ) (right : ℤ)) : left.Coprime right := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have integer_gcd := Int.isCoprime_iff_gcd_eq_one.mp coprime
  simpa [Int.gcd_eq_natAbs] using integer_gcd

private theorem halfHead_coprime_five (width : Nat) :
    (deletionCHalfHead width).Coprime 5 := by
  apply natCoprime_of_isCoprime_int
  refine ⟨-2, (3 : ℤ) ^ width, ?_⟩
  have doubled := deletionCHead_eq_twice_halfHead width
  have head_cast : (deletionCHead width : ℤ) =
      2 * deletionCHalfHead width := by
    exact_mod_cast doubled
  rw [show (-2 : ℤ) * deletionCHalfHead width =
      -(2 * deletionCHalfHead width) by ring, ← head_cast]
  simp only [deletionCHead]
  have power_pos : 0 < 3 ^ width := pow_pos (by omega) width
  rw [Nat.cast_sub (show 1 ≤ 5 * 3 ^ width by omega)]
  push_cast
  ring

private theorem denominatorCore_target_identity (scale upperPrefix : ℤ) :
    625 * emptyFrontSeedDenominatorCore scale upperPrefix -
        162 * (upperPrefix - 4) =
      (15 * scale - 1) *
        ((5625 * scale ^ 4 - 8250 * scale ^ 3 + 6450 * scale ^ 2 -
              2570 * scale + 162) * upperPrefix -
            4500 * scale ^ 3 + 22950 * scale ^ 2 -
              12220 * scale + 1852) := by
  simp only [emptyFrontSeedDenominatorCore]
  ring

private theorem headGapCore_denominatorCore_identity (scale upperPrefix : ℤ) :
    25 * emptyFrontSeedHeadGapCore scale upperPrefix +
        27 * emptyFrontSeedDenominatorCore scale upperPrefix =
      2 * (15 * scale - 1) *
        (18225 * scale ^ 6 * upperPrefix -
          43605 * scale ^ 5 * upperPrefix - 14580 * scale ^ 5 +
          38187 * scale ^ 4 * upperPrefix + 29538 * scale ^ 4 -
          15438 * scale ^ 3 * upperPrefix - 26658 * scale ^ 3 +
          2952 * scale ^ 2 * upperPrefix + 10470 * scale ^ 2 -
          208 * scale * upperPrefix - 1754 * scale + 104) := by
  simp only [emptyFrontSeedHeadGapCore, emptyFrontSeedDenominatorCore]
  ring

private theorem gcd_affine_numerator
    (head denominatorCore headGapCore : Nat) :
    Nat.gcd (2 * head * denominatorCore + headGapCore)
        (2 * denominatorCore) =
      Nat.gcd headGapCore (2 * denominatorCore) := by
  rw [show 2 * head * denominatorCore + headGapCore =
      headGapCore + (2 * denominatorCore) * head by ac_rfl]
  exact Nat.gcd_add_mul_left_left (2 * denominatorCore) headGapCore head

private theorem gcd_eq_of_common_divisor_equivalence
    {modulus left right : Nat}
    (equiv : ∀ divisor, divisor ∣ modulus → (divisor ∣ left ↔ divisor ∣ right)) :
    Nat.gcd modulus left = Nat.gcd modulus right := by
  apply dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    exact (equiv _ (Nat.gcd_dvd_left _ _)).mp (Nat.gcd_dvd_right _ _)
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    exact (equiv _ (Nat.gcd_dvd_left _ _)).mpr (Nat.gcd_dvd_right _ _)

private theorem gcd_denominatorCore_eq_target
    {halfHead head denominatorCore upperPrefix : Nat} {quotient : ℤ}
    (head_eq : head = 2 * halfHead)
    (halfHead_coprime_three : halfHead.Coprime 3)
    (halfHead_coprime_five : halfHead.Coprime 5)
    (identity :
      (625 * denominatorCore : Nat) - (162 * (upperPrefix - 4) : Nat) =
        (head : ℤ) * quotient) :
    Nat.gcd halfHead denominatorCore =
      Nat.gcd halfHead (2 * (upperPrefix - 4)) := by
  apply gcd_eq_of_common_divisor_equivalence
  intro divisor divisor_dvd_halfHead
  have divisor_dvd_head : divisor ∣ head := by
    rw [head_eq]
    exact dvd_mul_of_dvd_right divisor_dvd_halfHead 2
  have divisor_coprime_three : divisor.Coprime 3 :=
    Nat.Coprime.of_dvd_left divisor_dvd_halfHead halfHead_coprime_three
  have divisor_coprime_five : divisor.Coprime 5 :=
    Nat.Coprime.of_dvd_left divisor_dvd_halfHead halfHead_coprime_five
  have divisor_coprime_eightyOne : divisor.Coprime 81 := by
    simpa using divisor_coprime_three.pow_right 4
  have divisor_coprime_sixTwentyFive : divisor.Coprime 625 := by
    simpa using divisor_coprime_five.pow_right 4
  have divisor_dvd_head_int : (divisor : ℤ) ∣ (head : ℤ) := by
    exact_mod_cast divisor_dvd_head
  constructor
  · intro divisor_dvd_denominatorCore
    have divisor_dvd_left : (divisor : ℤ) ∣ (625 * denominatorCore : Nat) := by
      exact_mod_cast dvd_mul_of_dvd_right divisor_dvd_denominatorCore 625
    have divisor_dvd_head_product :
        (divisor : ℤ) ∣ (head : ℤ) * quotient :=
      dvd_mul_of_dvd_left divisor_dvd_head_int quotient
    have divisor_dvd_right_int :
        (divisor : ℤ) ∣ (162 * (upperPrefix - 4) : Nat) := by
      have right_eq :
          ((162 * (upperPrefix - 4) : Nat) : ℤ) =
            (625 * denominatorCore : Nat) - (head : ℤ) * quotient := by
        linear_combination -identity
      rw [right_eq]
      exact dvd_sub divisor_dvd_left divisor_dvd_head_product
    have divisor_dvd_right : divisor ∣ 162 * (upperPrefix - 4) := by
      exact_mod_cast divisor_dvd_right_int
    rw [show 162 * (upperPrefix - 4) =
        81 * (2 * (upperPrefix - 4)) by ring] at divisor_dvd_right
    exact divisor_coprime_eightyOne.dvd_of_dvd_mul_left divisor_dvd_right
  · intro divisor_dvd_target
    have divisor_dvd_right : divisor ∣ 162 * (upperPrefix - 4) := by
      rw [show 162 * (upperPrefix - 4) =
        81 * (2 * (upperPrefix - 4)) by ring]
      exact dvd_mul_of_dvd_right divisor_dvd_target 81
    have divisor_dvd_right_int :
        (divisor : ℤ) ∣ (162 * (upperPrefix - 4) : Nat) := by
      exact_mod_cast divisor_dvd_right
    have divisor_dvd_head_product :
        (divisor : ℤ) ∣ (head : ℤ) * quotient :=
      dvd_mul_of_dvd_left divisor_dvd_head_int quotient
    have divisor_dvd_left_int :
        (divisor : ℤ) ∣ (625 * denominatorCore : Nat) := by
      have left_eq :
          ((625 * denominatorCore : Nat) : ℤ) =
            (162 * (upperPrefix - 4) : Nat) + (head : ℤ) * quotient := by
        linear_combination identity
      rw [left_eq]
      exact dvd_add divisor_dvd_right_int divisor_dvd_head_product
    have divisor_dvd_left : divisor ∣ 625 * denominatorCore := by
      exact_mod_cast divisor_dvd_left_int
    rw [show 625 * denominatorCore = 625 * denominatorCore by rfl] at divisor_dvd_left
    exact divisor_coprime_sixTwentyFive.dvd_of_dvd_mul_left divisor_dvd_left

private theorem gcd_headGapCore_eq_denominatorCore
    {halfHead head denominatorCore headGapCore : Nat} {quotient : ℤ}
    (head_eq : head = 2 * halfHead)
    (halfHead_coprime_three : halfHead.Coprime 3)
    (halfHead_coprime_five : halfHead.Coprime 5)
    (identity :
      (25 * headGapCore + 27 * denominatorCore : Nat) =
        2 * (head : ℤ) * quotient) :
    Nat.gcd halfHead headGapCore = Nat.gcd halfHead denominatorCore := by
  push_cast at identity
  apply gcd_eq_of_common_divisor_equivalence
  intro divisor divisor_dvd_halfHead
  have divisor_dvd_head : divisor ∣ head := by
    rw [head_eq]
    exact dvd_mul_of_dvd_right divisor_dvd_halfHead 2
  have divisor_coprime_twentyFive : divisor.Coprime 25 := by
    have divisor_coprime_five : divisor.Coprime 5 :=
      Nat.Coprime.of_dvd_left divisor_dvd_halfHead halfHead_coprime_five
    simpa using divisor_coprime_five.pow_right 2
  have divisor_coprime_twentySeven : divisor.Coprime 27 := by
    have divisor_coprime_three : divisor.Coprime 3 :=
      Nat.Coprime.of_dvd_left divisor_dvd_halfHead halfHead_coprime_three
    simpa using divisor_coprime_three.pow_right 3
  have divisor_dvd_right_int :
      (divisor : ℤ) ∣ 2 * (head : ℤ) * quotient := by
    have divisor_dvd_head_int : (divisor : ℤ) ∣ (head : ℤ) := by
      exact_mod_cast divisor_dvd_head
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right divisor_dvd_head_int 2) quotient
  constructor
  · intro divisor_dvd_headGapCore
    have divisor_dvd_headGapProduct : divisor ∣ 25 * headGapCore :=
      dvd_mul_of_dvd_right divisor_dvd_headGapCore 25
    have divisor_dvd_headGapProduct_int :
        (divisor : ℤ) ∣ (25 * headGapCore : Nat) := by
      exact_mod_cast divisor_dvd_headGapProduct
    have divisor_dvd_denominatorProduct_int :
        (divisor : ℤ) ∣ (27 * denominatorCore : Nat) := by
      have product_eq :
          ((27 * denominatorCore : Nat) : ℤ) =
            2 * (head : ℤ) * quotient - (25 * headGapCore : Nat) := by
        push_cast
        linear_combination identity
      rw [product_eq]
      exact dvd_sub divisor_dvd_right_int divisor_dvd_headGapProduct_int
    have divisor_dvd_denominatorProduct : divisor ∣ 27 * denominatorCore := by
      exact_mod_cast divisor_dvd_denominatorProduct_int
    exact divisor_coprime_twentySeven.dvd_of_dvd_mul_left
      divisor_dvd_denominatorProduct
  · intro divisor_dvd_denominatorCore
    have divisor_dvd_denominatorProduct : divisor ∣ 27 * denominatorCore :=
      dvd_mul_of_dvd_right divisor_dvd_denominatorCore 27
    have divisor_dvd_denominatorProduct_int :
        (divisor : ℤ) ∣ (27 * denominatorCore : Nat) := by
      exact_mod_cast divisor_dvd_denominatorProduct
    have divisor_dvd_headGapProduct_int :
        (divisor : ℤ) ∣ (25 * headGapCore : Nat) := by
      have product_eq :
          ((25 * headGapCore : Nat) : ℤ) =
            2 * (head : ℤ) * quotient - (27 * denominatorCore : Nat) := by
        push_cast
        linear_combination identity
      rw [product_eq]
      exact dvd_sub divisor_dvd_right_int divisor_dvd_denominatorProduct_int
    have divisor_dvd_headGapProduct : divisor ∣ 25 * headGapCore := by
      exact_mod_cast divisor_dvd_headGapProduct_int
    exact divisor_coprime_twentyFive.dvd_of_dvd_mul_left
      divisor_dvd_headGapProduct

private theorem halfHead_gcd_content
    {halfHead denominatorCore headGapCore targetDivisor : Nat}
    (headGap_gcd :
      Nat.gcd halfHead headGapCore = Nat.gcd halfHead denominatorCore)
    (denominator_gcd :
      Nat.gcd halfHead denominatorCore = Nat.gcd halfHead targetDivisor) :
    Nat.gcd halfHead (Nat.gcd headGapCore (2 * denominatorCore)) =
      Nat.gcd halfHead targetDivisor := by
  let common := Nat.gcd halfHead targetDivisor
  have common_eq_headGap : common = Nat.gcd halfHead headGapCore := by
    rw [headGap_gcd, denominator_gcd]
  have common_dvd_halfHead : common ∣ halfHead := Nat.gcd_dvd_left _ _
  have common_dvd_headGapCore : common ∣ headGapCore := by
    rw [common_eq_headGap]
    exact Nat.gcd_dvd_right _ _
  have common_eq_denominator : common = Nat.gcd halfHead denominatorCore := by
    rw [denominator_gcd]
  have common_dvd_denominatorCore : common ∣ denominatorCore := by
    rw [common_eq_denominator]
    exact Nat.gcd_dvd_right _ _
  apply dvd_antisymm
  · have outer_dvd_halfHead := Nat.gcd_dvd_left halfHead
      (Nat.gcd headGapCore (2 * denominatorCore))
    have outer_dvd_inner := Nat.gcd_dvd_right halfHead
      (Nat.gcd headGapCore (2 * denominatorCore))
    have outer_dvd_headGap := dvd_trans outer_dvd_inner
      (Nat.gcd_dvd_left headGapCore (2 * denominatorCore))
    change Nat.gcd halfHead (Nat.gcd headGapCore (2 * denominatorCore)) ∣ common
    rw [common_eq_headGap]
    exact Nat.dvd_gcd outer_dvd_halfHead outer_dvd_headGap
  · apply Nat.dvd_gcd common_dvd_halfHead
    apply Nat.dvd_gcd common_dvd_headGapCore
    exact dvd_mul_of_dvd_right common_dvd_denominatorCore 2

/-- Natural-number form of the lower bound supplied by every physical empty target code. -/
theorem emptyTarget_upperPrefix_lower_nat
    {offset : Nat} {letters : List TagLetter}
    (letters_length : letters.length = offset + 1) :
    3 ^ (offset + 2) ≤
      2 * ternaryCode ((tagEncode (offset + 1) letters ++ [true]).map not) + 1 := by
  have lower := emptyTarget_upperPrefix_lower letters_length
  change (3 : ℤ) ^ (offset + 2) ≤
    2 * (ternaryCode ((tagEncode (offset + 1) letters ++ [true]).map not) : ℤ) + 1 at lower
  exact_mod_cast lower

/-- The half-head part of both seed cores and of their normalization content is exactly the
target-code resonance `gcd(h, 2(U-4))`. -/
theorem emptyFrontSeed_core_halfHead_gcds
    {offset upperPrefix : Nat} (offset_pos : 0 < offset)
    (prefix_lower : 3 ^ (offset + 2) ≤ 2 * upperPrefix + 1) :
    let scale : ℤ := 3 ^ offset
    let denominatorCore :=
      (emptyFrontSeedDenominatorCore scale upperPrefix).toNat
    let headGapCore :=
      (emptyFrontSeedHeadGapCore scale upperPrefix).toNat
    let halfHead := deletionCHalfHead (offset + 1)
    let targetDivisor := Nat.gcd halfHead (2 * (upperPrefix - 4))
    Nat.gcd halfHead denominatorCore = targetDivisor ∧
      Nat.gcd halfHead headGapCore = targetDivisor ∧
      Nat.gcd halfHead (Nat.gcd headGapCore (2 * denominatorCore)) =
        targetDivisor := by
  dsimp only
  let scale : ℤ := 3 ^ offset
  let denominatorCoreInt := emptyFrontSeedDenominatorCore scale upperPrefix
  let headGapCoreInt := emptyFrontSeedHeadGapCore scale upperPrefix
  let denominatorCore := denominatorCoreInt.toNat
  let headGapCore := headGapCoreInt.toNat
  let width := offset + 1
  let head := deletionCHead width
  let halfHead := deletionCHalfHead width
  have width_two : 2 ≤ width := by simp only [width]; omega
  have scale_three : 3 ≤ scale := by
    obtain ⟨predecessor, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt offset_pos)
    simp only [scale, pow_succ]
    have power_pos : (0 : ℤ) < 3 ^ predecessor := by positivity
    nlinarith
  have prefix_lower_int : 9 * scale ≤ 2 * (upperPrefix : ℤ) + 1 := by
    have prefix_lower_cast :
        ((3 ^ (offset + 2) : Nat) : ℤ) ≤
          ((2 * upperPrefix + 1 : Nat) : ℤ) := by
      exact_mod_cast prefix_lower
    simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul,
      Nat.cast_one] at prefix_lower_cast
    calc
      9 * scale = (3 : ℤ) ^ (offset + 2) := by
        simp only [scale, pow_add]
        ring
      _ ≤ 2 * (upperPrefix : ℤ) + 1 := prefix_lower_cast
  have denominatorCoreInt_pos : 0 < denominatorCoreInt :=
    emptyFrontSeedDenominatorCore_pos scale_three prefix_lower_int
  have headGapCoreInt_pos : 0 < headGapCoreInt :=
    emptyFrontSeedHeadGapCore_pos scale_three prefix_lower_int
  have denominatorCore_cast : (denominatorCore : ℤ) = denominatorCoreInt := by
    exact Int.toNat_of_nonneg denominatorCoreInt_pos.le
  have headGapCore_cast : (headGapCore : ℤ) = headGapCoreInt := by
    exact Int.toNat_of_nonneg headGapCoreInt_pos.le
  have upperPrefix_four : 4 ≤ upperPrefix := by
    have power_lower : 27 ≤ 3 ^ (offset + 2) := by
      have exponent_three : 3 ≤ offset + 2 := by omega
      calc
        27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ (offset + 2) :=
          Nat.pow_le_pow_right (by norm_num) exponent_three
    omega
  have upperPrefix_sub_cast :
      ((upperPrefix - 4 : Nat) : ℤ) = (upperPrefix : ℤ) - 4 := by
    rw [Nat.cast_sub upperPrefix_four]
    norm_num
  have head_cast : (head : ℤ) = 15 * scale - 1 := by
    simp only [head, deletionCHead, width, scale, pow_succ]
    have product_pos : 0 < 5 * (3 ^ offset * 3) := by positivity
    rw [Nat.cast_sub (show 1 ≤ 5 * (3 ^ offset * 3) by omega)]
    push_cast
    ring
  have head_eq : head = 2 * halfHead := by
    exact deletionCHead_eq_twice_halfHead width
  have halfHead_coprime_three : halfHead.Coprime 3 :=
    deletionCHalfHead_coprime_three width_two
  have halfHead_coprime_five' : halfHead.Coprime 5 :=
    halfHead_coprime_five width
  let denominatorQuotient : ℤ :=
    (5625 * scale ^ 4 - 8250 * scale ^ 3 + 6450 * scale ^ 2 -
          2570 * scale + 162) * upperPrefix -
      4500 * scale ^ 3 + 22950 * scale ^ 2 - 12220 * scale + 1852
  have denominator_identity :
      (625 * denominatorCore : Nat) -
          (162 * (upperPrefix - 4) : Nat) =
        (head : ℤ) * denominatorQuotient := by
    push_cast
    rw [denominatorCore_cast, upperPrefix_sub_cast, head_cast]
    exact denominatorCore_target_identity scale upperPrefix
  have denominator_gcd :
      Nat.gcd halfHead denominatorCore =
        Nat.gcd halfHead (2 * (upperPrefix - 4)) :=
    gcd_denominatorCore_eq_target head_eq halfHead_coprime_three
      halfHead_coprime_five' denominator_identity
  let linkageQuotient : ℤ :=
    18225 * scale ^ 6 * upperPrefix -
      43605 * scale ^ 5 * upperPrefix - 14580 * scale ^ 5 +
      38187 * scale ^ 4 * upperPrefix + 29538 * scale ^ 4 -
      15438 * scale ^ 3 * upperPrefix - 26658 * scale ^ 3 +
      2952 * scale ^ 2 * upperPrefix + 10470 * scale ^ 2 -
      208 * scale * upperPrefix - 1754 * scale + 104
  have linkage_identity :
      (25 * headGapCore + 27 * denominatorCore : Nat) =
        2 * (head : ℤ) * linkageQuotient := by
    push_cast
    rw [headGapCore_cast, denominatorCore_cast, head_cast]
    exact headGapCore_denominatorCore_identity scale upperPrefix
  have headGap_gcd :
      Nat.gcd halfHead headGapCore = Nat.gcd halfHead denominatorCore :=
    gcd_headGapCore_eq_denominatorCore head_eq halfHead_coprime_three
      halfHead_coprime_five' linkage_identity
  refine ⟨denominator_gcd, headGap_gcd.trans denominator_gcd, ?_⟩
  exact halfHead_gcd_content headGap_gcd denominator_gcd

private theorem primitiveSeed_normalization
    {head denominatorCore headGapCore : Nat}
    (denominatorCore_pos : 0 < denominatorCore) :
    let rawNumerator := 2 * head * denominatorCore + headGapCore
    let rawDenominator := 2 * denominatorCore
    let content := Nat.gcd headGapCore rawDenominator
    let numerator := rawNumerator / content
    let denominator := rawDenominator / content
    0 < content ∧
      Nat.gcd rawNumerator rawDenominator = content ∧
      content * numerator = rawNumerator ∧
      content * denominator = rawDenominator ∧
      numerator.Coprime denominator ∧
      (numerator : ℚ) / denominator =
        (rawNumerator : ℚ) / rawDenominator := by
  dsimp only
  let rawNumerator := 2 * head * denominatorCore + headGapCore
  let rawDenominator := 2 * denominatorCore
  let content := Nat.gcd headGapCore rawDenominator
  let numerator := rawNumerator / content
  let denominator := rawDenominator / content
  have rawDenominator_pos : 0 < rawDenominator := by
    simp only [rawDenominator]
    positivity
  have content_pos : 0 < content :=
    Nat.gcd_pos_of_pos_right headGapCore rawDenominator_pos
  have raw_gcd : Nat.gcd rawNumerator rawDenominator = content := by
    exact gcd_affine_numerator head denominatorCore headGapCore
  have content_dvd_rawNumerator : content ∣ rawNumerator := by
    rw [← raw_gcd]
    exact Nat.gcd_dvd_left _ _
  have content_dvd_rawDenominator : content ∣ rawDenominator := by
    exact Nat.gcd_dvd_right _ _
  have numerator_reconstitution : content * numerator = rawNumerator := by
    exact Nat.mul_div_cancel' content_dvd_rawNumerator
  have denominator_reconstitution : content * denominator = rawDenominator := by
    exact Nat.mul_div_cancel' content_dvd_rawDenominator
  have primitive : numerator.Coprime denominator := by
    simpa only [numerator, denominator, ← raw_gcd] using
      Nat.coprime_div_gcd_div_gcd (show 0 < Nat.gcd rawNumerator rawDenominator by
        rw [raw_gcd]
        exact content_pos)
  have ratio :
      (numerator : ℚ) / denominator =
        (rawNumerator : ℚ) / rawDenominator := by
    have content_ne : (content : ℚ) ≠ 0 := by exact_mod_cast content_pos.ne'
    have denominator_ne : (denominator : ℚ) ≠ 0 := by
      have denominator_pos : 0 < denominator := by
        exact Nat.div_pos (Nat.le_of_dvd rawDenominator_pos
          content_dvd_rawDenominator) content_pos
      exact_mod_cast denominator_pos.ne'
    have rawDenominator_ne : (rawDenominator : ℚ) ≠ 0 := by
      exact_mod_cast rawDenominator_pos.ne'
    have numerator_reconstitution_rat :
        (content : ℚ) * numerator = rawNumerator := by
      exact_mod_cast numerator_reconstitution
    have denominator_reconstitution_rat :
        (content : ℚ) * denominator = rawDenominator := by
      exact_mod_cast denominator_reconstitution
    calc
      (numerator : ℚ) / denominator =
          ((content : ℚ) * numerator) / ((content : ℚ) * denominator) := by
            field_simp [denominator_ne, content_ne]
      _ = (rawNumerator : ℚ) / rawDenominator := by
        rw [numerator_reconstitution_rat, denominator_reconstitution_rat]
  exact ⟨content_pos, raw_gcd, numerator_reconstitution,
    denominator_reconstitution, primitive, ratio⟩

private theorem emptyFrontSeed_denominator_eq_core
    (offset : Nat) (upperPrefix : ℤ) :
    let scale : ℤ := 3 ^ offset
    deletionBInverseDenominator offset upperPrefix =
      -2 * terminalDiscrepancy (offset + 1) *
        emptyFrontSeedDenominatorCore scale upperPrefix := by
  dsimp only
  let scale : ℤ := 3 ^ offset
  have width_scale_eq : widthScale (offset + 1) = 3 * scale := by
    simp only [widthScale, scale, pow_succ]
    ring
  simp only [deletionBInverseDenominator, setterMarker,
    secondDeletionInverseNumerator, firstDeletionInverseNumerator,
    firstDeletionInverseDenominator, firstDeletionResidual,
    secondDeletionGapCore, terminalDiscrepancy, centeredCoefficient,
    width_scale_eq, emptyFrontSeedDenominatorCore]
  ring

private theorem emptyFrontSeed_headGap_eq_core
    (offset : Nat) (upperPrefix : ℤ) :
    let scale : ℤ := 3 ^ offset
    deletionBInverseNumerator offset upperPrefix -
        terminalDiscrepancy (offset + 1) *
          deletionBInverseDenominator offset upperPrefix =
      -terminalDiscrepancy (offset + 1) *
        emptyFrontSeedHeadGapCore scale upperPrefix := by
  dsimp only
  let scale : ℤ := 3 ^ offset
  have width_scale_eq : widthScale (offset + 1) = 3 * scale := by
    simp only [widthScale, scale, pow_succ]
    ring
  simp only [deletionBInverseNumerator, deletionBCofactor,
    deletionBInverseDenominator, setterMarker,
    secondDeletionInverseNumerator, firstDeletionInverseNumerator,
    firstDeletionInverseDenominator, firstDeletionResidual,
    secondDeletionGapCore, terminalDiscrepancy, centeredCoefficient,
    width_scale_eq, emptyFrontSeedHeadGapCore]
  ring

/-- The sign-normalized empty-front seed is the positive core ratio
`(2HB+C)/(2B)`. -/
theorem emptyFrontSeed_eq_coreRatio
    {offset upperPrefix : Nat} (offset_pos : 0 < offset)
    (prefix_lower : 3 ^ (offset + 2) ≤ 2 * upperPrefix + 1) :
    let scale : ℤ := 3 ^ offset
    let denominatorCore :=
      (emptyFrontSeedDenominatorCore scale upperPrefix).toNat
    let headGapCore :=
      (emptyFrontSeedHeadGapCore scale upperPrefix).toNat
    let head := deletionCHead (offset + 1)
    emptyFrontSeed offset upperPrefix =
      ((2 * head * denominatorCore + headGapCore : Nat) : ℚ) /
        (2 * denominatorCore) := by
  dsimp only
  let scale : ℤ := 3 ^ offset
  let denominatorCoreInt := emptyFrontSeedDenominatorCore scale upperPrefix
  let headGapCoreInt := emptyFrontSeedHeadGapCore scale upperPrefix
  let denominatorCore := denominatorCoreInt.toNat
  let headGapCore := headGapCoreInt.toNat
  let width := offset + 1
  let head := deletionCHead width
  have scale_three : 3 ≤ scale := by
    obtain ⟨predecessor, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt offset_pos)
    simp only [scale, pow_succ]
    have power_pos : (0 : ℤ) < 3 ^ predecessor := by positivity
    nlinarith
  have prefix_lower_int : 9 * scale ≤ 2 * (upperPrefix : ℤ) + 1 := by
    have prefix_lower_cast :
        ((3 ^ (offset + 2) : Nat) : ℤ) ≤
          ((2 * upperPrefix + 1 : Nat) : ℤ) := by
      exact_mod_cast prefix_lower
    simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul,
      Nat.cast_one] at prefix_lower_cast
    calc
      9 * scale = (3 : ℤ) ^ (offset + 2) := by
        simp only [scale, pow_add]
        ring
      _ ≤ 2 * (upperPrefix : ℤ) + 1 := prefix_lower_cast
  have denominatorCoreInt_pos : 0 < denominatorCoreInt :=
    emptyFrontSeedDenominatorCore_pos scale_three prefix_lower_int
  have headGapCoreInt_pos : 0 < headGapCoreInt :=
    emptyFrontSeedHeadGapCore_pos scale_three prefix_lower_int
  have denominatorCore_cast : (denominatorCore : ℤ) = denominatorCoreInt := by
    exact Int.toNat_of_nonneg denominatorCoreInt_pos.le
  have headGapCore_cast : (headGapCore : ℤ) = headGapCoreInt := by
    exact Int.toNat_of_nonneg headGapCoreInt_pos.le
  have head_cast : (head : ℤ) = terminalDiscrepancy width := by
    simp only [head, deletionCHead, terminalDiscrepancy, widthScale]
    have power_pos : 0 < 3 ^ width := pow_pos (by omega) width
    rw [Nat.cast_sub (show 1 ≤ 5 * 3 ^ width by omega)]
    norm_num
  have head_pos : 0 < (head : ℤ) := by
    simp only [head, deletionCHead]
    have power_pos : 0 < 3 ^ width := pow_pos (by omega) width
    omega
  have denominatorCore_pos : 0 < (denominatorCore : ℤ) := by
    rw [denominatorCore_cast]
    exact denominatorCoreInt_pos
  have seedDenominator_eq := emptyFrontSeed_denominator_eq_core offset upperPrefix
  have seedHeadGap_eq := emptyFrontSeed_headGap_eq_core offset upperPrefix
  have seedDenominator_eq' :
      deletionBInverseDenominator offset upperPrefix =
        -2 * terminalDiscrepancy width * denominatorCoreInt := by
    simpa only [width, scale, denominatorCoreInt] using seedDenominator_eq
  have seedHeadGap_eq' :
      deletionBInverseNumerator offset upperPrefix -
          terminalDiscrepancy width *
            deletionBInverseDenominator offset upperPrefix =
        -terminalDiscrepancy width * headGapCoreInt := by
    simpa only [width, scale, headGapCoreInt] using seedHeadGap_eq
  have seedNumerator_eq :
      deletionBInverseNumerator offset upperPrefix =
        -terminalDiscrepancy width *
          (2 * terminalDiscrepancy width * denominatorCoreInt +
            headGapCoreInt) := by
    rw [seedDenominator_eq'] at seedHeadGap_eq'
    linear_combination seedHeadGap_eq'
  change deletionBInverseNumerator offset upperPrefix /
      deletionBInverseDenominator offset upperPrefix =
    ((2 * head * denominatorCore + headGapCore : Nat) : ℚ) /
      (2 * denominatorCore)
  rw [seedNumerator_eq, seedDenominator_eq']
  rw [← head_cast, ← denominatorCore_cast, ← headGapCore_cast]
  push_cast
  have head_ne : (head : ℚ) ≠ 0 := by exact_mod_cast head_pos.ne'
  have denominatorCore_ne : (denominatorCore : ℚ) ≠ 0 := by
    exact_mod_cast denominatorCore_pos.ne'
  field_simp [head_ne, denominatorCore_ne]

/-- Exact primitive coordinates of a physical empty-front seed. The only possible half-head
factor left in the primitive numerator is supported on `gcd(h, 2(U-4))`. -/
theorem emptyFrontSeed_primitiveCoordinates
    {offset upperPrefix : Nat} (offset_pos : 0 < offset)
    (prefix_lower : 3 ^ (offset + 2) ≤ 2 * upperPrefix + 1) :
    let scale : ℤ := 3 ^ offset
    let denominatorCore :=
      (emptyFrontSeedDenominatorCore scale upperPrefix).toNat
    let headGapCore :=
      (emptyFrontSeedHeadGapCore scale upperPrefix).toNat
    let head := deletionCHead (offset + 1)
    let halfHead := deletionCHalfHead (offset + 1)
    let rawNumerator := 2 * head * denominatorCore + headGapCore
    let rawDenominator := 2 * denominatorCore
    let content := Nat.gcd headGapCore rawDenominator
    let numerator := rawNumerator / content
    let denominator := rawDenominator / content
    let targetDivisor := Nat.gcd halfHead (2 * (upperPrefix - 4))
    0 < denominatorCore ∧
      0 < headGapCore ∧
      0 < content ∧
      Nat.gcd rawNumerator rawDenominator = content ∧
      content * numerator = rawNumerator ∧
      content * denominator = rawDenominator ∧
      numerator.Coprime denominator ∧
      emptyFrontSeed offset upperPrefix = (numerator : ℚ) / denominator ∧
      Nat.gcd halfHead content = targetDivisor ∧
      Nat.gcd halfHead numerator ∣ targetDivisor := by
  dsimp only
  let scale : ℤ := 3 ^ offset
  let denominatorCoreInt := emptyFrontSeedDenominatorCore scale upperPrefix
  let headGapCoreInt := emptyFrontSeedHeadGapCore scale upperPrefix
  let denominatorCore := denominatorCoreInt.toNat
  let headGapCore := headGapCoreInt.toNat
  let width := offset + 1
  let head := deletionCHead width
  let halfHead := deletionCHalfHead width
  let rawNumerator := 2 * head * denominatorCore + headGapCore
  let rawDenominator := 2 * denominatorCore
  let content := Nat.gcd headGapCore rawDenominator
  let numerator := rawNumerator / content
  let denominator := rawDenominator / content
  let targetDivisor := Nat.gcd halfHead (2 * (upperPrefix - 4))
  have scale_three : 3 ≤ scale := by
    obtain ⟨predecessor, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt offset_pos)
    simp only [scale, pow_succ]
    have power_pos : (0 : ℤ) < 3 ^ predecessor := by positivity
    nlinarith
  have prefix_lower_int : 9 * scale ≤ 2 * (upperPrefix : ℤ) + 1 := by
    have prefix_lower_cast :
        ((3 ^ (offset + 2) : Nat) : ℤ) ≤
          ((2 * upperPrefix + 1 : Nat) : ℤ) := by
      exact_mod_cast prefix_lower
    simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul,
      Nat.cast_one] at prefix_lower_cast
    calc
      9 * scale = (3 : ℤ) ^ (offset + 2) := by
        simp only [scale, pow_add]
        ring
      _ ≤ 2 * (upperPrefix : ℤ) + 1 := prefix_lower_cast
  have denominatorCoreInt_pos : 0 < denominatorCoreInt :=
    emptyFrontSeedDenominatorCore_pos scale_three prefix_lower_int
  have headGapCoreInt_pos : 0 < headGapCoreInt :=
    emptyFrontSeedHeadGapCore_pos scale_three prefix_lower_int
  have denominatorCore_pos : 0 < denominatorCore := by
    rw [show denominatorCore = denominatorCoreInt.toNat by rfl]
    omega
  have headGapCore_pos : 0 < headGapCore := by
    rw [show headGapCore = headGapCoreInt.toNat by rfl]
    omega
  obtain ⟨content_pos, raw_gcd, numerator_reconstitution,
      denominator_reconstitution, primitive, normalized_ratio⟩ :=
    primitiveSeed_normalization (head := head)
      (headGapCore := headGapCore) denominatorCore_pos
  have seed_ratio := emptyFrontSeed_eq_coreRatio offset_pos prefix_lower
  have seed_eq_primitive :
      emptyFrontSeed offset upperPrefix = (numerator : ℚ) / denominator := by
    calc
      emptyFrontSeed offset upperPrefix =
          (rawNumerator : ℚ) / rawDenominator := by
            simpa only [scale, denominatorCoreInt, headGapCoreInt,
              denominatorCore, headGapCore, width, head, rawNumerator,
              rawDenominator, Nat.cast_mul, Nat.cast_ofNat] using seed_ratio
      _ = (numerator : ℚ) / denominator := normalized_ratio.symm
  obtain ⟨_, _, content_gcd⟩ :=
    emptyFrontSeed_core_halfHead_gcds offset_pos prefix_lower
  have content_gcd' : Nat.gcd halfHead content = targetDivisor := by
    simpa only [scale, denominatorCoreInt, headGapCoreInt,
      denominatorCore, headGapCore, width, halfHead, rawDenominator,
      content, targetDivisor] using content_gcd
  let numeratorHeadCommon := Nat.gcd halfHead numerator
  have numeratorHeadCommon_dvd_halfHead : numeratorHeadCommon ∣ halfHead :=
    Nat.gcd_dvd_left _ _
  have numeratorHeadCommon_dvd_numerator : numeratorHeadCommon ∣ numerator :=
    Nat.gcd_dvd_right _ _
  have numeratorHeadCommon_dvd_head : numeratorHeadCommon ∣ head := by
    have head_eq : head = 2 * halfHead :=
      deletionCHead_eq_twice_halfHead width
    rw [head_eq]
    exact dvd_mul_of_dvd_right numeratorHeadCommon_dvd_halfHead 2
  have numeratorHeadCommon_dvd_rawNumerator : numeratorHeadCommon ∣ rawNumerator := by
    have common_dvd_product : numeratorHeadCommon ∣ content * numerator :=
      dvd_mul_of_dvd_right numeratorHeadCommon_dvd_numerator content
    rw [numerator_reconstitution] at common_dvd_product
    simpa only [rawNumerator] using common_dvd_product
  have numeratorHeadCommon_dvd_headTerm :
      numeratorHeadCommon ∣ 2 * head * denominatorCore := by
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right numeratorHeadCommon_dvd_head 2) denominatorCore
  have numeratorHeadCommon_dvd_headGapCore :
      numeratorHeadCommon ∣ headGapCore := by
    have sum_dvd : numeratorHeadCommon ∣
        2 * head * denominatorCore + headGapCore := by
      simpa only [rawNumerator] using numeratorHeadCommon_dvd_rawNumerator
    exact (Nat.dvd_add_right numeratorHeadCommon_dvd_headTerm).mp sum_dvd
  have numeratorHeadCommon_dvd_targetDivisor :
      numeratorHeadCommon ∣ targetDivisor := by
    have common_dvd_coreGcd : numeratorHeadCommon ∣
        Nat.gcd halfHead headGapCore :=
      Nat.dvd_gcd numeratorHeadCommon_dvd_halfHead
        numeratorHeadCommon_dvd_headGapCore
    have core_gcd :=
      (emptyFrontSeed_core_halfHead_gcds offset_pos prefix_lower).2.1
    have core_gcd' : Nat.gcd halfHead headGapCore = targetDivisor := by
      simpa only [scale, denominatorCoreInt, headGapCoreInt,
        denominatorCore, headGapCore, width, halfHead, targetDivisor] using core_gcd
    rwa [core_gcd'] at common_dvd_coreGcd
  exact ⟨denominatorCore_pos, headGapCore_pos, content_pos, raw_gcd,
    numerator_reconstitution, denominator_reconstitution, primitive,
    seed_eq_primitive, content_gcd', numeratorHeadCommon_dvd_targetDivisor⟩

private theorem quotient_dvd_quotient_of_dvd
    {small large modulus : Nat} (small_pos : 0 < small) (modulus_pos : 0 < modulus)
    (small_dvd_large : small ∣ large) (large_dvd_modulus : large ∣ modulus) :
    modulus / large ∣ modulus / small := by
  have large_pos : 0 < large :=
    Nat.pos_of_dvd_of_pos large_dvd_modulus modulus_pos
  obtain ⟨factor, large_eq⟩ := small_dvd_large
  obtain ⟨cofactor, modulus_eq⟩ := large_dvd_modulus
  have modulus_div_large : modulus / large = cofactor := by
    rw [modulus_eq]
    exact Nat.mul_div_cancel_left cofactor large_pos
  have modulus_div_small : modulus / small = factor * cofactor := by
    rw [modulus_eq, large_eq]
    calc
      small * factor * cofactor / small =
          small * (factor * cofactor) / small := by ring_nf
      _ = factor * cofactor := Nat.mul_div_cancel_left _ small_pos
  rw [modulus_div_large, modulus_div_small]
  exact dvd_mul_left cofactor factor

/-- The raw half-head channel for an empty-front seed, with its primitive coordinates expanded
directly from the target code. -/
theorem emptyFrontSeed_pullbackRaw_halfHead_iff
    {offset upperPrefix punctuated upperPower : Nat}
    (offset_pos : 0 < offset)
    (correction_le :
      let scale : ℤ := 3 ^ offset
      let denominatorCore :=
        (emptyFrontSeedDenominatorCore scale upperPrefix).toNat
      let headGapCore :=
        (emptyFrontSeedHeadGapCore scale upperPrefix).toNat
      let width := offset + 1
      let head := deletionCHead width
      let content := Nat.gcd headGapCore (2 * denominatorCore)
      let numerator :=
        (2 * head * denominatorCore + headGapCore) / content
      let denominator := 2 * denominatorCore / content
      deletionCHead width * deletionCMarker width * upperPower * denominator ≤
        punctuated * pullbackTime width numerator denominator) :
    let scale : ℤ := 3 ^ offset
    let denominatorCore :=
      (emptyFrontSeedDenominatorCore scale upperPrefix).toNat
    let headGapCore :=
      (emptyFrontSeedHeadGapCore scale upperPrefix).toNat
    let width := offset + 1
    let head := deletionCHead width
    let halfHead := deletionCHalfHead width
    let content := Nat.gcd headGapCore (2 * denominatorCore)
    let numerator :=
      (2 * head * denominatorCore + headGapCore) / content
    let denominator := 2 * denominatorCore / content
    halfHead ∣
        pullbackRawNumerator width punctuated upperPower numerator denominator ↔
      halfHead / Nat.gcd halfHead numerator ∣ punctuated := by
  dsimp only at correction_le ⊢
  apply deletionCHalfHead_dvd_pullbackRawNumerator_iff
  · omega
  · exact correction_le

/-- Any raw half-head pullback from an empty-front seed forces the target-code modulus
`h/gcd(h,2(U-4))` into the physical upper code. -/
theorem emptyFrontSeed_pullbackRaw_targetModulus_dvd
    {offset upperPrefix punctuated upperPower : Nat}
    (offset_pos : 0 < offset)
    (prefix_lower : 3 ^ (offset + 2) ≤ 2 * upperPrefix + 1)
    (correction_le :
      let scale : ℤ := 3 ^ offset
      let denominatorCore :=
        (emptyFrontSeedDenominatorCore scale upperPrefix).toNat
      let headGapCore :=
        (emptyFrontSeedHeadGapCore scale upperPrefix).toNat
      let width := offset + 1
      let head := deletionCHead width
      let content := Nat.gcd headGapCore (2 * denominatorCore)
      let numerator :=
        (2 * head * denominatorCore + headGapCore) / content
      let denominator := 2 * denominatorCore / content
      deletionCHead width * deletionCMarker width * upperPower * denominator ≤
        punctuated * pullbackTime width numerator denominator)
    (raw_dvd :
      let scale : ℤ := 3 ^ offset
      let denominatorCore :=
        (emptyFrontSeedDenominatorCore scale upperPrefix).toNat
      let headGapCore :=
        (emptyFrontSeedHeadGapCore scale upperPrefix).toNat
      let width := offset + 1
      let head := deletionCHead width
      let halfHead := deletionCHalfHead width
      let content := Nat.gcd headGapCore (2 * denominatorCore)
      let numerator :=
        (2 * head * denominatorCore + headGapCore) / content
      let denominator := 2 * denominatorCore / content
      halfHead ∣
        pullbackRawNumerator width punctuated upperPower numerator denominator) :
    let halfHead := deletionCHalfHead (offset + 1)
    let targetDivisor := Nat.gcd halfHead (2 * (upperPrefix - 4))
    halfHead / targetDivisor ∣ punctuated := by
  dsimp only at correction_le raw_dvd ⊢
  let scale : ℤ := 3 ^ offset
  let denominatorCore :=
    (emptyFrontSeedDenominatorCore scale upperPrefix).toNat
  let headGapCore :=
    (emptyFrontSeedHeadGapCore scale upperPrefix).toNat
  let width := offset + 1
  let head := deletionCHead width
  let halfHead := deletionCHalfHead width
  let content := Nat.gcd headGapCore (2 * denominatorCore)
  let numerator :=
    (2 * head * denominatorCore + headGapCore) / content
  let denominator := 2 * denominatorCore / content
  let numeratorCommon := Nat.gcd halfHead numerator
  let targetDivisor := Nat.gcd halfHead (2 * (upperPrefix - 4))
  have exact_channel := emptyFrontSeed_pullbackRaw_halfHead_iff
    offset_pos correction_le
  have exact_modulus_dvd : halfHead / numeratorCommon ∣ punctuated := by
    exact exact_channel.mp raw_dvd
  have numeratorCommon_dvd_target : numeratorCommon ∣ targetDivisor := by
    have coordinates := emptyFrontSeed_primitiveCoordinates offset_pos prefix_lower
    exact coordinates.2.2.2.2.2.2.2.2.2
  have target_dvd_halfHead : targetDivisor ∣ halfHead := Nat.gcd_dvd_left _ _
  have numeratorCommon_pos : 0 < numeratorCommon :=
    Nat.gcd_pos_of_pos_left numerator
      (deletionCHalfHead_pos width)
  exact dvd_trans
    (quotient_dvd_quotient_of_dvd numeratorCommon_pos
      (deletionCHalfHead_pos width) numeratorCommon_dvd_target
      target_dvd_halfHead)
    exact_modulus_dvd

/-- Post-cancellation survival of the half-head for an empty-front seed, with both primitive
coordinates expanded directly from the target code. -/
theorem emptyFrontSeed_primitivePullback_halfHead_iff
    {offset upperPrefix punctuated lower upperPower residual : Nat}
    (raw_eq :
      let scale : ℤ := 3 ^ offset
      let denominatorCore :=
        (emptyFrontSeedDenominatorCore scale upperPrefix).toNat
      let headGapCore :=
        (emptyFrontSeedHeadGapCore scale upperPrefix).toNat
      let width := offset + 1
      let head := deletionCHead width
      let halfHead := deletionCHalfHead width
      let content := Nat.gcd headGapCore (2 * denominatorCore)
      let numerator :=
        (2 * head * denominatorCore + headGapCore) / content
      let denominator := 2 * denominatorCore / content
      pullbackRawNumerator width punctuated upperPower numerator denominator =
        halfHead * residual)
    (raw_denominator_pos :
      let scale : ℤ := 3 ^ offset
      let denominatorCore :=
        (emptyFrontSeedDenominatorCore scale upperPrefix).toNat
      let headGapCore :=
        (emptyFrontSeedHeadGapCore scale upperPrefix).toNat
      let width := offset + 1
      let head := deletionCHead width
      let content := Nat.gcd headGapCore (2 * denominatorCore)
      let numerator :=
        (2 * head * denominatorCore + headGapCore) / content
      let denominator := 2 * denominatorCore / content
      0 < pullbackRawDenominator width lower numerator denominator) :
    let scale : ℤ := 3 ^ offset
    let denominatorCore :=
      (emptyFrontSeedDenominatorCore scale upperPrefix).toNat
    let headGapCore :=
      (emptyFrontSeedHeadGapCore scale upperPrefix).toNat
    let width := offset + 1
    let head := deletionCHead width
    let halfHead := deletionCHalfHead width
    let content := Nat.gcd headGapCore (2 * denominatorCore)
    let numerator :=
      (2 * head * denominatorCore + headGapCore) / content
    let denominator := 2 * denominatorCore / content
    halfHead ∣
        primitiveNumerator
          (pullbackRawNumerator width punctuated upperPower numerator denominator)
          (pullbackRawDenominator width lower numerator denominator) ↔
      halfHead.Coprime
        (pullbackRawDenominator width lower numerator denominator /
          Nat.gcd residual
            (pullbackRawDenominator width lower numerator denominator)) := by
  dsimp only at raw_eq raw_denominator_pos ⊢
  exact deletionCHalfHead_dvd_primitivePullback_iff raw_eq raw_denominator_pos

end MatrixMortality.SwappedSetterPrimitiveSeedAdapter
