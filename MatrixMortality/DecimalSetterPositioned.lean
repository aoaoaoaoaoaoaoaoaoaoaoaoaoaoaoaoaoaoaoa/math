import MatrixMortality.DecimalSetterAncestry

/-!
# Positioned `D_b` decimal entry obstructions

A one-`D_b` all-erasure block preserves the all-zero lower word. Its punctuated upper code
differs from the all-`D_c` code only above an exact suffix. The suffix depth excludes every
`D_b` among the first `β+1` roles at the distinguished two-`c` raw head.
-/

namespace MatrixMortality.DecimalSetterAncestry

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterChamber
open MatrixMortality.DecimalSetterDepth

@[simp] private theorem tagEncode_replicate_c (β width : Nat) :
    tagEncode β (List.replicate width .c) = List.replicate width true := by
  induction width with
  | zero => rfl
  | succ width induction =>
      rw [List.replicate_succ, tagEncode_cons, tagCode, induction,
        List.replicate_succ]
      rfl

/-- An all-erasure word with one `D_b`, preceded and followed by specified numbers of `D_c`
tiles. -/
def positionedBEraseBlock (prefixWidth tailWidth : Nat) : List NearyTile :=
  List.replicate prefixWidth (.erase .c) ++
    .erase .b :: List.replicate tailWidth (.erase .c)

/-- Every lower side in a one-`D_b` erasure block is the one-digit zero word. -/
@[simp] theorem spell_positionedBEraseBlock_lower
    (β : Nat) (body : List TagLetter) (prefixWidth tailWidth : Nat) :
    spell (nearyLower β body) (positionedBEraseBlock prefixWidth tailWidth) =
      List.replicate (prefixWidth + tailWidth + 1) false := by
  have prefix_spell :
      spell (nearyLower β body) (List.replicate prefixWidth (.erase .c)) =
        List.replicate prefixWidth false := by
    simpa only [allEraseBlock] using spell_allEraseBlock β body prefixWidth
  have tail_spell :
      spell (nearyLower β body) (List.replicate tailWidth (.erase .c)) =
        List.replicate tailWidth false := by
    simpa only [allEraseBlock] using spell_allEraseBlock β body tailWidth
  rw [positionedBEraseBlock, spell_append, prefix_spell]
  rw [show spell (nearyLower β body)
      (.erase .b :: List.replicate tailWidth (.erase .c)) =
        false :: spell (nearyLower β body)
          (List.replicate tailWidth (.erase .c)) by rfl, tail_spell]
  rw [show prefixWidth + tailWidth + 1 = prefixWidth + (tailWidth + 1) by omega,
    List.replicate_add, List.replicate_succ]

private theorem positionedB_punctuatedUpper_eq_append
    (β prefixWidth tailWidth : Nat) :
    punctuatedUpper β
        (List.replicate prefixWidth .c ++ .b :: List.replicate tailWidth .c) =
      (List.replicate prefixWidth true ++ markerWord β) ++
        (List.replicate (tailWidth + 1) true ++ markerWord β) := by
  simp [punctuatedUpper, tagEncode_append, tagEncode_cons, tagCode, markerWord,
    List.replicate_succ, List.append_assoc]

private theorem sameWidthAllC_positioned_punctuatedUpper_eq_append
    (β prefixWidth tailWidth : Nat) :
    punctuatedUpper β (List.replicate (prefixWidth + tailWidth + 1) .c) =
      List.replicate prefixWidth true ++
        (List.replicate (tailWidth + 1) true ++ markerWord β) := by
  rw [show prefixWidth + tailWidth + 1 = prefixWidth + (tailWidth + 1) by omega,
    List.replicate_add]
  simp only [punctuatedUpper, tagEncode_append, tagEncode_replicate_c]
  exact List.append_assoc _ _ _

/-- Coefficient left after removing the exact common suffix from a positioned `D_b` upper
perturbation. -/
def positionedBUpperCoefficient (β prefixWidth : Nat) : ℤ :=
  code (List.replicate prefixWidth true ++ markerWord β) -
    code (List.replicate prefixWidth true)

/-- Exact common-suffix factorization of a positioned one-`D_b` upper perturbation. -/
theorem positionedB_punctuatedUpper_code_sub_eq
    (β prefixWidth tailWidth : Nat) :
    (code (punctuatedUpper β
        (List.replicate prefixWidth .c ++ .b :: List.replicate tailWidth .c)) : ℤ) -
      code (punctuatedUpper β
        (List.replicate (prefixWidth + tailWidth + 1) .c)) =
      positionedBUpperCoefficient β prefixWidth * 10 ^ (tailWidth + β + 2) := by
  let suffix := List.replicate (tailWidth + 1) true ++ markerWord β
  have suffix_length : suffix.length = tailWidth + β + 2 := by
    simp [suffix, markerWord]
    omega
  rw [positionedB_punctuatedUpper_eq_append,
    sameWidthAllC_positioned_punctuatedUpper_eq_append]
  change (code ((List.replicate prefixWidth true ++ markerWord β) ++ suffix) : ℤ) -
      code (List.replicate prefixWidth true ++ suffix) = _
  have positioned_code :=
    code_append (List.replicate prefixWidth true ++ markerWord β) suffix
  have allC_code := code_append (List.replicate prefixWidth true) suffix
  rw [positioned_code, allC_code]
  push_cast
  rw [suffix_length]
  dsimp only [positionedBUpperCoefficient]
  ring

/-- Replacing one `D_c` after `prefixWidth` roles by `D_b` changes the punctuated upper code
only above the common suffix of decimal length `tailWidth+β+2`. -/
theorem tenPower_dvd_positionedB_punctuatedUpper_code_sub
    (β prefixWidth tailWidth : Nat) :
    (10 : ℤ) ^ (tailWidth + β + 2) ∣
      (code (punctuatedUpper β
        (List.replicate prefixWidth .c ++ .b :: List.replicate tailWidth .c)) : ℤ) -
        code (punctuatedUpper β
          (List.replicate (prefixWidth + tailWidth + 1) .c)) := by
  rw [positionedB_punctuatedUpper_code_sub_eq]
  refine ⟨positionedBUpperCoefficient β prefixWidth, ?_⟩
  ring

private theorem five_dvd_replicateTrue_code (width : Nat) :
    (5 : ℤ) ∣ code (List.replicate width true) := by
  induction width with
  | zero => simp
  | succ width induction =>
      rw [List.replicate_succ, code_cons, digit_true, List.length_replicate]
      push_cast
      exact dvd_add (dvd_mul_right 5 _) induction

/-- The coefficient of every positioned one-`D_b` upper perturbation is congruent to `2`
modulo `5`; the displayed common suffix is therefore its exact five-adic depth. -/
theorem positionedBUpperCoefficient_sub_two_dvd_five
    {β : Nat} (β_positive : 0 < β) (prefixWidth : Nat) :
    (5 : ℤ) ∣ positionedBUpperCoefficient β prefixWidth - 2 := by
  let prefixCode : ℤ := code (List.replicate prefixWidth true)
  let markerCode : ℤ := code (markerWord β)
  have prefix_dvd : (5 : ℤ) ∣ prefixCode := by
    exact five_dvd_replicateTrue_code prefixWidth
  have marker_identity : 9 * markerCode + 7 = 52 * 10 ^ β := by
    dsimp only [markerCode]
    exact_mod_cast markerWord_code_identity β
  have marker_scaled_dvd : (5 : ℤ) ∣ 9 * (markerCode - 2) := by
    rw [show 9 * (markerCode - 2) = (9 * markerCode + 7) - 25 by ring,
      marker_identity]
    have five_dvd_ten : (5 : ℤ) ∣ 10 ^ β :=
      (pow_dvd_pow (5 : ℤ) β_positive).trans
        (pow_dvd_pow_of_dvd (by norm_num : (5 : ℤ) ∣ 10) β)
    exact dvd_sub (five_dvd_ten.mul_left 52) (by norm_num)
  have marker_sub_two_dvd : (5 : ℤ) ∣ markerCode - 2 :=
    (by norm_num : IsCoprime (5 : ℤ) 9).dvd_of_dvd_mul_left marker_scaled_dvd
  have coefficient_eq : positionedBUpperCoefficient β prefixWidth =
      prefixCode * 10 ^ (β + 1) + markerCode - prefixCode := by
    dsimp only [positionedBUpperCoefficient, prefixCode, markerCode]
    rw [code_append]
    push_cast
    simp only [markerWord, List.length_cons, List.length_replicate]
  rw [coefficient_eq]
  rw [show prefixCode * 10 ^ (β + 1) + markerCode - prefixCode - 2 =
    prefixCode * 10 ^ (β + 1) + (markerCode - 2) - prefixCode by ring]
  exact dvd_sub (dvd_add (prefix_dvd.mul_right _) marker_sub_two_dvd) prefix_dvd

/-- Decimal lower code emitted by a one-`D_b` erasure block. -/
def positionedBEraseLowerCode
    (β : Nat) (body : List TagLetter) (prefixWidth tailWidth : Nat) : ℤ :=
  code (spell (nearyLower β body) (positionedBEraseBlock prefixWidth tailWidth))

/-- A one-`D_b` erasure block has the same lower code as the same-role-count all-`D_c` block. -/
theorem positionedBEraseLowerCode_eq_allEraseLowerCode
    (β : Nat) (body : List TagLetter) (prefixWidth tailWidth : Nat) :
    positionedBEraseLowerCode β body prefixWidth tailWidth =
      allEraseLowerCode β body (prefixWidth + tailWidth + 1) := by
  simp only [positionedBEraseLowerCode, allEraseLowerCode,
    spell_positionedBEraseBlock_lower, spell_allEraseBlock]

/-- A full-gap all-erasure lower code retains full support after replacing any one role by
`D_b`. -/
theorem gapFactor_dvd_positionedBEraseLowerCode_of_width_eq_entry
    {β prefixWidth tailWidth : Nat} (β_positive : 0 < β) (body : List TagLetter)
    (width_eq : prefixWidth + tailWidth + 1 = entrySaturationWidth β) :
    gapFactor β ∣ positionedBEraseLowerCode β body prefixWidth tailWidth := by
  rw [positionedBEraseLowerCode_eq_allEraseLowerCode, width_eq]
  exact gapFactor_dvd_entrySaturationLowerCode β_positive body

/-- If the sole `D_b` occurs among the first `β+1` roles, no such all-erasure block can be the
first transition from a lawful two-`c` raw head to another multi-role pole. -/
theorem positionedBErase_rawHead_shell_impossible
    {β prefixWidth tailWidth : Nat} (body headTail : List TagLetter) {μ E G : ℤ}
    (β_large : 2 ≤ β) (prefix_le : prefixWidth ≤ β)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: headTail)) : ℚ) 0 0)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (shell :
      HasDecimalShell
        (((code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) *
          (E * code (punctuatedUpper β
              (List.replicate prefixWidth .c ++
                .b :: List.replicate tailWidth .c)) +
            G * positionedBEraseLowerCode β body prefixWidth tailWidth) -
          10 * μ * G * positionedBEraseLowerCode β body prefixWidth tailWidth : ℤ) : ℚ)
        ((prefixWidth + tailWidth + 1 + β : Nat) : ℤ)
        ((prefixWidth + tailWidth + 1 + β : Nat) : ℤ)) :
    False := by
  let n := prefixWidth + tailWidth + 1
  let H : ℤ := code (peeledHeadWord β (.c :: .c :: headTail))
  let PAll : ℤ := code (punctuatedUpper β (List.replicate n .c))
  let P : ℤ := code (punctuatedUpper β
    (List.replicate prefixWidth .c ++ .b :: List.replicate tailWidth .c))
  let V := positionedBEraseLowerCode β body prefixWidth tailWidth
  let RAll := H * (E * PAll + G * V) - 10 * μ * G * V
  let R := H * (E * P + G * V) - 10 * μ * G * V
  have n_positive : 1 ≤ n := by omega
  have allC_upper_eq : 9 * PAll =
      50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7 := by
    exact allC_punctuatedUpper_code_identity β n
  have V_eq : V = allEraseLowerCode β body n := by
    dsimp only [V, n]
    exact positionedBEraseLowerCode_eq_allEraseLowerCode
      β body prefixWidth tailWidth
  have lower_eq : 9 * V = 7 * 10 ^ n - 7 := by
    have identity := allEraseLowerCode_identity β body n
    rw [V_eq]
    linear_combination identity
  refine aboveWidthUpperPerturbation_peeledDoubleCHead_shell_impossible
    (PAll := PAll) (P := P) (RAll := RAll) (R := R) headTail β_large n_positive
      head_unit mu_eq gap_eq lift_eq allC_upper_eq lower_eq ?_ ?_ ?_ ?_
  · rfl
  · dsimp only [P, PAll, n]
    have five_to_ten : (5 : ℤ) ^ (prefixWidth + tailWidth + 2) ∣
        10 ^ (tailWidth + β + 2) := by
      exact (pow_dvd_pow (5 : ℤ) (by omega)).trans
        (pow_dvd_pow_of_dvd (by norm_num : (5 : ℤ) ∣ 10) _)
    exact five_to_ten.trans
      (tenPower_dvd_positionedB_punctuatedUpper_code_sub β prefixWidth tailWidth)
  · rfl
  · simpa only [n, H, P, V, R, Nat.cast_add] using shell

/-- At a regular raw head, a sole `D_b` is impossible in every all-erasure position. -/
theorem positionedBErase_regularRawHead_shell_impossible
    {β s prefixWidth tailWidth : Nat} (body : List TagLetter) {H μ E G : ℤ}
    (s_positive : 1 ≤ s) (suffix_below : s + 2 ≤ β)
    (head_eq : 9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ s - 7)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (shell :
      HasDecimalShell
        ((H *
          (E * code (punctuatedUpper β
              (List.replicate prefixWidth .c ++
                .b :: List.replicate tailWidth .c)) +
            G * positionedBEraseLowerCode β body prefixWidth tailWidth) -
          10 * μ * G * positionedBEraseLowerCode β body prefixWidth tailWidth : ℤ) : ℚ)
        ((prefixWidth + tailWidth + 1 + β : Nat) : ℤ)
        ((prefixWidth + tailWidth + 1 + β : Nat) : ℤ)) :
    False := by
  let n := prefixWidth + tailWidth + 1
  let PAll : ℤ := code (punctuatedUpper β (List.replicate n .c))
  let P : ℤ := code (punctuatedUpper β
    (List.replicate prefixWidth .c ++ .b :: List.replicate tailWidth .c))
  let V := positionedBEraseLowerCode β body prefixWidth tailWidth
  let RAll := H * (E * PAll + G * V) - 10 * μ * G * V
  let R := H * (E * P + G * V) - 10 * μ * G * V
  have n_positive : 1 ≤ n := by omega
  have allC_upper_eq : 9 * PAll =
      50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7 := by
    exact allC_punctuatedUpper_code_identity β n
  have V_eq : V = allEraseLowerCode β body n := by
    dsimp only [V, n]
    exact positionedBEraseLowerCode_eq_allEraseLowerCode
      β body prefixWidth tailWidth
  have lower_eq : 9 * V = 7 * 10 ^ n - 7 := by
    have identity := allEraseLowerCode_identity β body n
    rw [V_eq]
    linear_combination identity
  refine betaDeepUpperPerturbation_regularRawHead_shell_impossible
    (PAll := PAll) (P := P) (RAll := RAll) (R := R) s_positive suffix_below n_positive
      head_eq mu_eq gap_eq lift_eq allC_upper_eq lower_eq ?_ ?_ ?_ ?_
  · rfl
  · dsimp only [P, PAll]
    have five_to_ten : (5 : ℤ) ^ β ∣ 10 ^ (tailWidth + β + 2) := by
      exact (pow_dvd_pow (5 : ℤ) (by omega)).trans
        (pow_dvd_pow_of_dvd (by norm_num : (5 : ℤ) ∣ 10) _)
    exact five_to_ten.trans
      (tenPower_dvd_positionedB_punctuatedUpper_code_sub β prefixWidth tailWidth)
  · rfl
  · simpa only [n, P, V, R, Nat.cast_add] using shell

/-- Any one-`D_b` all-erasure raw-head shell must use both exceptional features left by the
previous obstructions: the `D_b` lies after position `β+1`, and the raw head has terminal run
`β-1`. -/
theorem positionedBErase_shell_forces_exceptionalLate
    {β prefixWidth tailWidth : Nat} (body headTail : List TagLetter) {μ E G : ℤ}
    (β_large : 2 ≤ β)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: headTail)) : ℚ) 0 0)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (shell :
      HasDecimalShell
        (((code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) *
          (E * code (punctuatedUpper β
              (List.replicate prefixWidth .c ++
                .b :: List.replicate tailWidth .c)) +
            G * positionedBEraseLowerCode β body prefixWidth tailWidth) -
          10 * μ * G * positionedBEraseLowerCode β body prefixWidth tailWidth : ℤ) : ℚ)
        ((prefixWidth + tailWidth + 1 + β : Nat) : ℤ)
        ((prefixWidth + tailWidth + 1 + β : Nat) : ℤ)) :
    β < prefixWidth ∧
      9 * (code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) =
        5 * 10 ^ (β + 2) + 2 * 10 ^ (β - 1) - 7 := by
  obtain ⟨suffix, suffix_positive, suffix_le, _, head_eq⟩ :=
    peeledDoubleCHead_unit_shape headTail (by omega) head_unit
  have prefix_late : β < prefixWidth := by
    by_contra prefix_not_late
    exact positionedBErase_rawHead_shell_impossible body headTail β_large
      (Nat.le_of_not_gt prefix_not_late) head_unit mu_eq gap_eq lift_eq shell
  have suffix_eq : suffix = β - 1 := by
    by_contra suffix_ne
    have suffix_below : suffix + 2 ≤ β := by omega
    exact positionedBErase_regularRawHead_shell_impossible body suffix_positive suffix_below
      head_eq mu_eq gap_eq lift_eq shell
  constructor
  · exact prefix_late
  · simpa only [suffix_eq] using head_eq

/-- The exceptional raw head cannot survive a late one-`D_b` all-erasure block. Exact
five-adic coefficients exclude the two resonance arms and their corner. -/
theorem positionedBErase_exceptionalRawHead_shell_impossible
    {β prefixWidth tailWidth : Nat} (body : List TagLetter) {H μ E G : ℤ}
    (β_large : 2 ≤ β) (prefix_late : β < prefixWidth)
    (head_eq : 9 * H = 5 * 10 ^ (β + 2) + 2 * 10 ^ (β - 1) - 7)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (shell :
      HasDecimalShell
        ((H *
          (E * code (punctuatedUpper β
              (List.replicate prefixWidth .c ++
                .b :: List.replicate tailWidth .c)) +
            G * positionedBEraseLowerCode β body prefixWidth tailWidth) -
          10 * μ * G * positionedBEraseLowerCode β body prefixWidth tailWidth : ℤ) : ℚ)
        ((prefixWidth + tailWidth + 1 + β : Nat) : ℤ)
        ((prefixWidth + tailWidth + 1 + β : Nat) : ℤ)) :
    False := by
  let n := prefixWidth + tailWidth + 1
  let PAll : ℤ := code (punctuatedUpper β (List.replicate n .c))
  let P : ℤ := code (punctuatedUpper β
    (List.replicate prefixWidth .c ++ .b :: List.replicate tailWidth .c))
  let V := positionedBEraseLowerCode β body prefixWidth tailWidth
  let RAll := H * (E * PAll + G * V) - 10 * μ * G * V
  let R := H * (E * P + G * V) - 10 * μ * G * V
  let D := positionedBUpperCoefficient β prefixWidth
  have allC_upper_eq : 9 * PAll =
      50 * 10 ^ β * 10 ^ n + 2 * 10 ^ β - 7 := by
    exact allC_punctuatedUpper_code_identity β n
  have V_eq : V = allEraseLowerCode β body n := by
    dsimp only [V, n]
    exact positionedBEraseLowerCode_eq_allEraseLowerCode
      β body prefixWidth tailWidth
  have lower_eq : 9 * V = 7 * 10 ^ n - 7 := by
    have identity := allEraseLowerCode_identity β body n
    rw [V_eq]
    linear_combination identity
  refine exceptionalRawHead_lateUpperPerturbation_shell_impossible
    (PAll := PAll) (P := P) (V := V) (RAll := RAll) (R := R) (D := D)
      β_large prefix_late head_eq mu_eq gap_eq lift_eq
      (by simpa only [n] using allC_upper_eq)
      (by simpa only [n] using lower_eq) ?_ ?_ ?_ ?_ ?_
  · rfl
  · dsimp only [P, PAll, D]
    exact positionedB_punctuatedUpper_code_sub_eq β prefixWidth tailWidth
  · exact positionedBUpperCoefficient_sub_two_dvd_five (by omega) prefixWidth
  · rfl
  · simpa only [n, P, V, R, Nat.cast_add, Nat.cast_one] using shell

/-- No one-`D_b` all-erasure block carries a lawful two-`c` raw head into another multi-role
pole, regardless of the marker position. -/
theorem positionedBErase_rawHead_shell_impossible_allPositions
    {β prefixWidth tailWidth : Nat} (body headTail : List TagLetter) {μ E G : ℤ}
    (β_large : 2 ≤ β)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: headTail)) : ℚ) 0 0)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (shell :
      HasDecimalShell
        (((code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) *
          (E * code (punctuatedUpper β
              (List.replicate prefixWidth .c ++
                .b :: List.replicate tailWidth .c)) +
            G * positionedBEraseLowerCode β body prefixWidth tailWidth) -
          10 * μ * G * positionedBEraseLowerCode β body prefixWidth tailWidth : ℤ) : ℚ)
        ((prefixWidth + tailWidth + 1 + β : Nat) : ℤ)
        ((prefixWidth + tailWidth + 1 + β : Nat) : ℤ)) :
    False := by
  obtain ⟨prefix_late, head_eq⟩ := positionedBErase_shell_forces_exceptionalLate
    body headTail β_large head_unit mu_eq gap_eq lift_eq shell
  exact positionedBErase_exceptionalRawHead_shell_impossible
    body β_large prefix_late head_eq mu_eq gap_eq lift_eq shell

/-- An all-erasure word whose second tile is `D_b`. -/
def secondBEraseBlock (tailWidth : Nat) : List NearyTile :=
  positionedBEraseBlock 1 tailWidth

@[simp] theorem spell_secondBEraseBlock_lower
    (β : Nat) (body : List TagLetter) (tailWidth : Nat) :
    spell (nearyLower β body) (secondBEraseBlock tailWidth) =
      List.replicate (tailWidth + 2) false := by
  rw [secondBEraseBlock, spell_positionedBEraseBlock_lower]
  congr 1
  omega

theorem tenPower_dvd_secondB_punctuatedUpper_code_sub (β tailWidth : Nat) :
    (10 : ℤ) ^ (tailWidth + β + 2) ∣
      (code (punctuatedUpper β (.c :: .b :: List.replicate tailWidth .c)) : ℤ) -
        code (punctuatedUpper β (List.replicate (tailWidth + 2) .c)) := by
  have general := tenPower_dvd_positionedB_punctuatedUpper_code_sub β 1 tailWidth
  have letters_eq :
      List.replicate 1 TagLetter.c ++ .b :: List.replicate tailWidth .c =
        .c :: .b :: List.replicate tailWidth .c := by rfl
  have width_eq : 1 + tailWidth + 1 = tailWidth + 2 := by omega
  rw [letters_eq, width_eq] at general
  exact general

theorem fivePower_dvd_secondB_punctuatedUpper_code_sub (β tailWidth : Nat) :
    (5 : ℤ) ^ (tailWidth + 2 + β) ∣
      (code (punctuatedUpper β (.c :: .b :: List.replicate tailWidth .c)) : ℤ) -
        code (punctuatedUpper β (List.replicate (tailWidth + 2) .c)) := by
  have power_dvd : (5 : ℤ) ^ (tailWidth + 2 + β) ∣
      10 ^ (tailWidth + β + 2) := by
    simpa only [show tailWidth + 2 + β = tailWidth + β + 2 by omega] using
      pow_dvd_pow_of_dvd (by norm_num : (5 : ℤ) ∣ 10) (tailWidth + β + 2)
  exact power_dvd.trans (tenPower_dvd_secondB_punctuatedUpper_code_sub β tailWidth)

/-- Decimal lower code emitted by a second-position `D_b` erasure block. -/
def secondBEraseLowerCode
    (β : Nat) (body : List TagLetter) (tailWidth : Nat) : ℤ :=
  positionedBEraseLowerCode β body 1 tailWidth

theorem secondBEraseLowerCode_eq_allEraseLowerCode
    (β : Nat) (body : List TagLetter) (tailWidth : Nat) :
    secondBEraseLowerCode β body tailWidth =
      allEraseLowerCode β body (tailWidth + 2) := by
  simpa [secondBEraseLowerCode, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    positionedBEraseLowerCode_eq_allEraseLowerCode β body 1 tailWidth

theorem gapFactor_dvd_entrySecondBEraseLowerCode
    {β : Nat} (β_positive : 0 < β) (body : List TagLetter) :
    gapFactor β ∣ secondBEraseLowerCode β body (entrySaturationWidth β - 2) := by
  rw [secondBEraseLowerCode_eq_allEraseLowerCode,
    Nat.sub_add_cancel (show 2 ≤ entrySaturationWidth β by
      exact (entrySaturationWidth_three_le β_positive).trans' (by norm_num))]
  exact gapFactor_dvd_entrySaturationLowerCode β_positive body

theorem secondBErase_rawHead_shell_impossible
    {β tailWidth : Nat} (body headTail : List TagLetter) {μ E G : ℤ}
    (β_large : 2 ≤ β)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: headTail)) : ℚ) 0 0)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (shell :
      HasDecimalShell
        (((code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) *
          (E * code (punctuatedUpper β
              (.c :: .b :: List.replicate tailWidth .c)) +
            G * secondBEraseLowerCode β body tailWidth) -
          10 * μ * G * secondBEraseLowerCode β body tailWidth : ℤ) : ℚ)
        ((tailWidth + 2 + β : Nat) : ℤ)
        ((tailWidth + 2 + β : Nat) : ℤ)) :
    False := by
  apply positionedBErase_rawHead_shell_impossible
    (prefixWidth := 1) body headTail β_large (by omega) head_unit mu_eq gap_eq lift_eq
  simpa [secondBEraseLowerCode, List.replicate_succ, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using shell


end MatrixMortality.DecimalSetterAncestry
