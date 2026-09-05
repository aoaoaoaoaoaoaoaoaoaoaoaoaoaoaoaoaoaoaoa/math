import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.ModEq
import MatrixMortality.SwappedSetterCompiler
import MatrixMortality.PadicValuation

/-!
# First multi-transfer gate for the swapped setter

Closing the distinguished-boundary positive depth-one fringe does not close the setter's
arbitrary-word converse. A malformed projective bridge may contain several square-run transfers.
This file isolates the first such branch. The exact `3`-adic balance and Neary upper-length
grammar reduce every expected-shell two-transfer pole to three block shapes.
-/

namespace MatrixMortality.SwappedSetterMultitransfer

open MatrixMortality.PadicValuation

private instance factPrimeThree : Fact (Nat.Prime 3) :=
  ⟨by norm_num⟩

/-- Upper spelling length of one regular Neary role block. -/
def upperLength (β : Nat) (block : List NearyTile) : Nat :=
  (spell (nearyUpper β) block).length

@[simp] theorem upperLength_singleton_erase_c (width : Nat) :
    upperLength width [.erase .c] = 1 := rfl

@[simp] theorem upperLength_singleton_erase_b (width : Nat) :
    upperLength width [.erase .b] = width + 2 := by
  rw [upperLength, spell_nearyUpper]
  simp [tagEncode_cons, tagCode, NearyTile.letter]

/-- A square-run role block is nonempty and ends in an erasure. -/
def IsRoleBlock (block : List NearyTile) : Prop :=
  ∃ front letter, block = front ++ [.erase letter]

/-- Exact pole-shell grammar from `MM-S02`: singleton erasures have depth `β`, while every
multi-role block has depth one. -/
def HasPoleShell (β : Nat) (block : List NearyTile) (depth : Nat) : Prop :=
  IsRoleBlock block ∧
    ((block.length = 1 ∧ depth = β) ∨ (2 ≤ block.length ∧ depth = 1))

/-- One centered setter step. -/
def nextX (scale y : ℚ) : ℚ :=
  scale * y

/-- Denominator coordinate of one centered setter step. -/
def nextY (coefficient coupling lower x y : ℚ) : ℚ :=
  coefficient * y + coupling * lower * x

/-! ## The resonant singleton unit -/

/-- Swapped setter scale `ρ=3^β`. -/
def widthScale (width : Nat) : ℤ :=
  3 ^ width

/-- Swapped marker value `μ=2ρ-1`. -/
def setterMarker (width : Nat) : ℤ :=
  2 * widthScale width - 1

/-- Swapped terminal discrepancy `H=5ρ-1`. -/
def terminalDiscrepancy (width : Nat) : ℤ :=
  5 * widthScale width - 1

/-- Swapped centered coefficient `R=2-ρ`. -/
def centeredCoefficient (width : Nat) : ℤ :=
  2 - widthScale width

/-- Common coupling `K=RHμ` in the centered recurrence. -/
def centeredCoupling (width : Nat) : ℤ :=
  centeredCoefficient width * terminalDiscrepancy width * setterMarker width

/-- Unit cofactor in the singleton `b` coefficient. -/
def singletonBCofactor (width : Nat) : ℤ :=
  18 * widthScale width ^ 2 - 40 * widthScale width + 17

/-- Exact centered coefficient of either singleton erasure. -/
def singletonCoefficient (width : Nat) : TagLetter → ℤ
  | .b => -widthScale width * singletonBCofactor width
  | .c => -widthScale width * terminalDiscrepancy width

/-- Swapped ternary code of a punctuated upper role block. -/
def swappedUpperCode (width : Nat) (block : List NearyTile) : ℤ :=
  ternaryCode ((spell (nearyUpper width) block ++ nearyMarker width).map not)

/-- Swapped ternary code of a lower role block. -/
def swappedLowerCode (width : Nat) (body : List TagLetter)
    (block : List NearyTile) : ℤ :=
  ternaryCode ((spell (nearyLower width body) block).map not)

/-- Centered coefficient `C=RP-HV` of an actual swapped role block. -/
def blockCoefficient (width : Nat) (body : List TagLetter)
    (block : List NearyTile) : ℤ :=
  centeredCoefficient width * swappedUpperCode width block -
    terminalDiscrepancy width * swappedLowerCode width body block

private theorem ternaryCode_replicate_true (length : Nat) :
    ternaryCode (List.replicate length true) = 3 ^ length - 1 := by
  induction length with
  | zero => simp
  | succ length induction =>
      rw [List.replicate_succ, ternaryCode_cons, List.length_replicate, induction,
        pow_succ]
      simp only [ternaryDigit]
      have power_pos : 0 < 3 ^ length := pow_pos (by omega) length
      omega

theorem swappedCode_nearyMarker (width : Nat) :
    ternaryCode ((nearyMarker width).map not) = 2 * 3 ^ width - 1 := by
  simp only [nearyMarker, List.map_cons, Bool.not_true, List.map_replicate,
    Bool.not_false, ternaryCode_cons, List.length_replicate, ternaryDigit]
  rw [ternaryCode_replicate_true]
  have power_pos : 0 < 3 ^ width := pow_pos (by omega) width
  omega

theorem swappedUpperCode_singleton_c (width : Nat) :
    swappedUpperCode width [.erase .c] = terminalDiscrepancy width := by
  change
    (ternaryCode (([true, true] ++ List.replicate width false).map not) : ℤ) =
      terminalDiscrepancy width
  have natural_eq := (swappedCode_terminalFringes width).1
  have cast_sub :
      ((5 * 3 ^ width - 1 : Nat) : ℤ) = 5 * (3 : ℤ) ^ width - 1 := by
    have power_pos : 0 < 3 ^ width := pow_pos (by omega) width
    have one_le : 1 ≤ 5 * 3 ^ width := by omega
    rw [Nat.cast_sub one_le]
    norm_num
  rw [terminalDiscrepancy, widthScale, ← cast_sub]
  exact_mod_cast natural_eq

theorem swappedUpperCode_singleton_b (width : Nat) :
    swappedUpperCode width [.erase .b] =
      18 * widthScale width ^ 2 - 4 * widthScale width - 1 := by
  rw [swappedUpperCode, spell_nearyUpper]
  change
    (ternaryCode ((tagEncode width [.b] ++ nearyMarker width).map not) : ℤ) =
      18 * widthScale width ^ 2 - 4 * widthScale width - 1
  rw [show tagEncode width [.b] = tagCode width .b by simp [tagEncode_cons]]
  rw [List.map_append, ternaryCode_append, List.length_map]
  have tag_eq :
      (ternaryCode ((tagCode width .b).map not) : ℤ) =
        6 * (3 : ℤ) ^ width - 2 := by
    have power_pos : 0 < 3 ^ width := pow_pos (by omega) width
    have two_le : 2 ≤ 6 * 3 ^ width := by omega
    calc
      (ternaryCode ((tagCode width .b).map not) : ℤ) =
          ((6 * 3 ^ width - 2 : Nat) : ℤ) := by
            exact_mod_cast swappedCode_tagCode_b width
      _ = 6 * (3 : ℤ) ^ width - 2 := by
        rw [Nat.cast_sub two_le]
        norm_num
  have marker_eq :
      (ternaryCode ((nearyMarker width).map not) : ℤ) =
        2 * (3 : ℤ) ^ width - 1 := by
    have power_pos : 0 < 3 ^ width := pow_pos (by omega) width
    have one_le : 1 ≤ 2 * 3 ^ width := by omega
    calc
      (ternaryCode ((nearyMarker width).map not) : ℤ) =
          ((2 * 3 ^ width - 1 : Nat) : ℤ) := by
            exact_mod_cast swappedCode_nearyMarker width
      _ = 2 * (3 : ℤ) ^ width - 1 := by
        rw [Nat.cast_sub one_le]
        norm_num
  push_cast
  rw [tag_eq, marker_eq]
  simp [nearyMarker, widthScale, pow_succ]
  ring

theorem swappedLowerCode_singleton (width : Nat) (body : List TagLetter)
    (letter : TagLetter) :
    swappedLowerCode width body [.erase letter] = 2 := by
  cases letter <;>
    norm_num [swappedLowerCode, spell, nearyLower, ternaryCode, ternaryDigit]

/-- The closed singleton coefficients used by the resonant calculation are exactly the
coefficients of the physical swapped blocks. -/
theorem blockCoefficient_singleton (width : Nat) (body : List TagLetter)
    (letter : TagLetter) :
    blockCoefficient width body [.erase letter] = singletonCoefficient width letter := by
  cases letter with
  | c =>
      rw [blockCoefficient, swappedUpperCode_singleton_c,
        swappedLowerCode_singleton]
      simp [singletonCoefficient, centeredCoefficient, terminalDiscrepancy]
      ring
  | b =>
      rw [blockCoefficient, swappedUpperCode_singleton_b,
        swappedLowerCode_singleton]
      simp [singletonCoefficient, singletonBCofactor, centeredCoefficient,
        terminalDiscrepancy]
      ring

/-- Unit left after factoring the common `3^β` from a resonant singleton step. -/
def resonantUnit (width : Nat) (punctuated : ℤ) : TagLetter → ℤ
  | .b => centeredCoefficient width *
      (-singletonBCofactor width * punctuated +
        2 * terminalDiscrepancy width * setterMarker width)
  | .c => centeredCoefficient width * terminalDiscrepancy width *
      (2 * setterMarker width - punctuated)

private theorem widthScale_mod_three {width : Nat} (width_pos : 0 < width) :
    widthScale width ≡ 0 [ZMOD 3] := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
  simpa [widthScale, pow_succ, mul_comm] using
    (Int.ModEq.refl ((3 : ℤ) ^ offset)).mul
      (by norm_num : (3 : ℤ) ≡ 0 [ZMOD 3])

private theorem centeredCoefficient_mod_three {width : Nat} (width_pos : 0 < width) :
    centeredCoefficient width ≡ 2 [ZMOD 3] := by
  have scale_mod := widthScale_mod_three width_pos
  simpa [centeredCoefficient] using
    (Int.ModEq.refl (2 : ℤ)).sub scale_mod

private theorem terminalDiscrepancy_mod_three {width : Nat} (width_pos : 0 < width) :
    terminalDiscrepancy width ≡ 2 [ZMOD 3] := by
  have raw :=
    ((Int.ModEq.refl (5 : ℤ)).mul (widthScale_mod_three width_pos)).sub
      (Int.ModEq.refl (1 : ℤ))
  exact raw.trans (by norm_num)

private theorem setterMarker_mod_three {width : Nat} (width_pos : 0 < width) :
    setterMarker width ≡ 2 [ZMOD 3] := by
  have raw :=
    ((Int.ModEq.refl (2 : ℤ)).mul (widthScale_mod_three width_pos)).sub
      (Int.ModEq.refl (1 : ℤ))
  exact raw.trans (by norm_num)

private theorem singletonBCofactor_mod_three {width : Nat} (width_pos : 0 < width) :
    singletonBCofactor width ≡ 2 [ZMOD 3] := by
  have scale_mod := widthScale_mod_three width_pos
  have square_mod := scale_mod.mul scale_mod
  have raw :=
    (((Int.ModEq.refl (18 : ℤ)).mul square_mod).sub
      ((Int.ModEq.refl (40 : ℤ)).mul scale_mod)).add
        (Int.ModEq.refl (17 : ℤ))
  simpa [singletonBCofactor, pow_two] using raw.trans (by norm_num)

private theorem resonantUnit_mod_three
    {width : Nat} (width_pos : 0 < width) {punctuated : ℤ}
    (punctuated_mod : punctuated ≡ 2 [ZMOD 3]) (letter : TagLetter) :
    resonantUnit width punctuated letter ≡ 2 [ZMOD 3] := by
  have centered_mod := centeredCoefficient_mod_three width_pos
  have terminal_mod := terminalDiscrepancy_mod_three width_pos
  have marker_mod := setterMarker_mod_three width_pos
  cases letter with
  | c =>
      have raw := centered_mod.mul <|
        terminal_mod.mul <|
          ((Int.ModEq.refl (2 : ℤ)).mul marker_mod).sub punctuated_mod
      simpa [resonantUnit, mul_assoc] using raw.trans
        (by norm_num : (2 * (2 * (2 * 2 - 2)) : ℤ) ≡ 2 [ZMOD 3])
  | b =>
      have cofactor_mod := singletonBCofactor_mod_three width_pos
      have negative_product :=
        (Int.ModEq.refl (0 : ℤ)).sub (cofactor_mod.mul punctuated_mod)
      have terminal_product :=
        ((Int.ModEq.refl (2 : ℤ)).mul terminal_mod).mul marker_mod
      simpa [resonantUnit] using
        (centered_mod.mul (negative_product.add terminal_product)).trans
        (by norm_num : (2 * ((0 - 2 * 2) + 2 * 2 * 2) : ℤ) ≡ 2 [ZMOD 3])

private theorem resonantUnit_not_dvd_three
    {width : Nat} (width_pos : 0 < width) {punctuated : ℤ}
    (punctuated_mod : punctuated ≡ 2 [ZMOD 3]) (letter : TagLetter) :
    ¬(3 : ℤ) ∣ resonantUnit width punctuated letter := by
  intro divides
  have unit_zero : resonantUnit width punctuated letter ≡ 0 [ZMOD 3] :=
    divides.modEq_zero_int
  have two_zero : (2 : ℤ) ≡ 0 [ZMOD 3] :=
    (resonantUnit_mod_three width_pos punctuated_mod letter).symm.trans unit_zero
  norm_num [Int.ModEq] at two_zero

private theorem not_dvd_three_of_mod_two {value : ℤ}
    (value_mod : value ≡ 2 [ZMOD 3]) : ¬(3 : ℤ) ∣ value := by
  intro divides
  have value_zero : value ≡ 0 [ZMOD 3] := divides.modEq_zero_int
  have two_zero : (2 : ℤ) ≡ 0 [ZMOD 3] := value_mod.symm.trans value_zero
  norm_num [Int.ModEq] at two_zero

/-- The common centered coupling is a `3`-adic unit. -/
theorem centeredCoupling_isUnit {width : Nat} (width_pos : 0 < width) :
    IsUnit 3 (centeredCoupling width) := by
  have coupling_mod : centeredCoupling width ≡ 2 [ZMOD 3] := by
    have raw :=
      (centeredCoefficient_mod_three width_pos).mul <|
        (terminalDiscrepancy_mod_three width_pos).mul (setterMarker_mod_three width_pos)
    simpa [centeredCoupling, mul_assoc] using raw.trans
      (by norm_num : (2 * (2 * 2) : ℤ) ≡ 2 [ZMOD 3])
  exact intCast_isUnit_of_not_dvd (not_dvd_three_of_mod_two coupling_mod)

/-- A punctuated swapped code ending in digit two is a `3`-adic unit after multiplication by
the centered coefficient. -/
theorem centeredPunctuated_isUnit
    {width : Nat} (width_pos : 0 < width) {punctuated : ℤ}
    (punctuated_mod : punctuated ≡ 2 [ZMOD 3]) :
    IsUnit 3 (centeredCoefficient width * punctuated) :=
  mul_hasValue
    (intCast_isUnit_of_not_dvd <|
      not_dvd_three_of_mod_two (centeredCoefficient_mod_three width_pos))
    (intCast_isUnit_of_not_dvd <| not_dvd_three_of_mod_two punctuated_mod)

private theorem resonant_nextY_factor
    (width : Nat) (punctuated : ℤ) (letter : TagLetter) :
    nextY (singletonCoefficient width letter) (centeredCoupling width) 2
        ((3 : ℚ) ^ width) (centeredCoefficient width * punctuated) =
      (3 : ℚ) ^ width * resonantUnit width punctuated letter := by
  cases letter <;>
    norm_num [nextY, singletonCoefficient, centeredCoupling, resonantUnit,
      widthScale, singletonBCofactor, centeredCoefficient, terminalDiscrepancy,
      setterMarker] <;>
    ring

/-- The equal-depth singleton branch creates no extra `3`-adic carry. Its next denominator
remains in shell `β`, so the same length balance used off resonance applies. -/
theorem resonantSingleton_nextY_hasValue
    {width : Nat} (width_pos : 0 < width) {punctuated : ℤ}
    (punctuated_mod : punctuated ≡ 2 [ZMOD 3]) (letter : TagLetter) :
    HasValue 3
      (nextY (singletonCoefficient width letter) (centeredCoupling width) 2
        ((3 : ℚ) ^ width) (centeredCoefficient width * punctuated)) width := by
  rw [resonant_nextY_factor]
  exact mul_hasValue (primePower_hasValue width)
    (intCast_isUnit_of_not_dvd
      (resonantUnit_not_dvd_three width_pos punctuated_mod letter))

private def bCount : List TagLetter → Nat
  | [] => 0
  | .b :: letters => bCount letters + 1
  | .c :: letters => bCount letters

private theorem tagEncode_length (width : Nat) (letters : List TagLetter) :
    (tagEncode width letters).length =
      letters.length + (width + 1) * bCount letters := by
  induction letters with
  | nil => rfl
  | cons letter letters induction =>
      cases letter with
      | b =>
          simp only [tagEncode_cons, tagCode, List.length_append, List.length_cons,
            List.length_replicate, List.length_nil, bCount, induction,
            Nat.mul_succ]
          omega
      | c =>
          simp only [tagEncode_cons, tagCode, List.singleton_append, List.length_cons,
            bCount, induction]
          omega

theorem upperLength_eq (width : Nat) (block : List NearyTile) :
    upperLength width block =
      block.length + (width + 1) * bCount (block.map NearyTile.letter) := by
  rw [upperLength, spell_nearyUpper, tagEncode_length, List.length_map]

private theorem IsRoleBlock.nonempty {block : List NearyTile}
    (role_block : IsRoleBlock block) : block ≠ [] := by
  obtain ⟨front, letter, rfl⟩ := role_block
  simp

private theorem letters_eq_c_of_bCount_eq_zero
    (letters : List TagLetter) (count_zero : bCount letters = 0) :
    letters = List.replicate letters.length .c := by
  induction letters with
  | nil => rfl
  | cons letter letters induction =>
      cases letter with
      | b => simp [bCount] at count_zero
      | c =>
          have tail_zero : bCount letters = 0 := by simpa [bCount] using count_zero
          calc
            .c :: letters = .c :: List.replicate letters.length .c :=
              congrArg (TagLetter.c :: ·) (induction tail_zero)
            _ = List.replicate (.c :: letters).length .c := by
              rw [List.length_cons, List.replicate_succ]

private theorem bCount_replicate_c (length : Nat) :
    bCount (List.replicate length .c) = 0 := by
  induction length with
  | zero => rfl
  | succ length induction =>
      rw [List.replicate_succ]
      simpa [bCount] using induction

/-- Any role block shorter than one `b` code consists entirely of `c` roles. -/
theorem IsRoleBlock.letters_eq_replicate_c_of_upperLength_lt
    {width : Nat} {block : List NearyTile} (role_block : IsRoleBlock block)
    (short : upperLength width block < width + 2) :
    block.map NearyTile.letter = List.replicate block.length .c := by
  have count_zero : bCount (block.map NearyTile.letter) = 0 := by
    by_contra count_ne
    have count_pos : 0 < bCount (block.map NearyTile.letter) := Nat.pos_of_ne_zero count_ne
    have block_pos : 0 < block.length := List.length_pos_iff.mpr role_block.nonempty
    rw [upperLength_eq] at short
    nlinarith
  simpa using letters_eq_c_of_bCount_eq_zero _ count_zero

/-- Below the `b`-code threshold, upper length is the number of roles. -/
theorem IsRoleBlock.length_eq_upperLength_of_upperLength_lt
    {width : Nat} {block : List NearyTile} (role_block : IsRoleBlock block)
    (short : upperLength width block < width + 2) :
    block.length = upperLength width block := by
  have letters := role_block.letters_eq_replicate_c_of_upperLength_lt short
  rw [upperLength_eq]
  have count_zero : bCount (block.map NearyTile.letter) = 0 := by
    rw [letters]
    exact bCount_replicate_c block.length
  rw [count_zero]
  simp

/-- Unequal incoming and coefficient depths force the expected denominator shell after the
second transfer. -/
theorem nextY_hasValue_min_of_ne
    {firstX firstY coefficient coupling lower : ℚ}
    {firstDepth coefficientDepth : Nat}
    (firstX_shell : HasValue 3 firstX firstDepth)
    (firstY_unit : IsUnit 3 firstY)
    (coefficient_shell : HasValue 3 coefficient coefficientDepth)
    (coupling_unit : IsUnit 3 coupling) (lower_unit : IsUnit 3 lower)
    (depth_ne : coefficientDepth ≠ firstDepth) :
    HasValue 3 (nextY coefficient coupling lower firstX firstY)
      ((min coefficientDepth firstDepth : Nat) : ℤ) := by
  have left_shell :
      HasValue 3 (coefficient * firstY) coefficientDepth := by
    simpa using mul_hasValue coefficient_shell firstY_unit
  have right_shell :
      HasValue 3 (coupling * lower * firstX) firstDepth := by
    simpa using mul_hasValue (mul_hasValue coupling_unit lower_unit) firstX_shell
  unfold nextY
  rcases lt_or_gt_of_ne depth_ne with depth_lt | depth_gt
  · rw [min_eq_left depth_lt.le]
    exact
      add_hasValue_left left_shell right_shell (by exact_mod_cast depth_lt)
  · rw [min_eq_right depth_gt.le]
    exact
      add_hasValue_right left_shell right_shell (by exact_mod_cast depth_gt)

/-- A following pole equates the current upper length with the target shell plus the current
denominator shell. -/
theorem pole_length_balance
    {firstX firstY coefficient coupling lower targetCoefficient targetLower : ℚ}
    {firstDepth middleLength middleDepth targetDepth : Nat}
    (firstY_unit : IsUnit 3 firstY)
    (currentY_shell :
      HasValue 3 (nextY coefficient coupling lower firstX firstY)
        ((min middleDepth firstDepth : Nat) : ℤ))
    (coupling_unit : IsUnit 3 coupling) (targetLower_unit : IsUnit 3 targetLower)
    (targetCoefficient_shell : HasValue 3 targetCoefficient targetDepth)
    (pole :
      targetCoefficient * nextY coefficient coupling lower firstX firstY +
          coupling * targetLower * nextX (3 ^ middleLength) firstY = 0) :
    middleLength = targetDepth + min middleDepth firstDepth := by
  have left_shell :
      HasValue 3
        (targetCoefficient * nextY coefficient coupling lower firstX firstY)
        ((targetDepth + min middleDepth firstDepth : Nat) : ℤ) := by
    simpa using mul_hasValue targetCoefficient_shell currentY_shell
  have currentX_shell :
      HasValue 3 (nextX (3 ^ middleLength) firstY) middleLength := by
    simpa [nextX] using mul_hasValue (primePower_hasValue middleLength) firstY_unit
  have right_shell :
      HasValue 3
        (coupling * targetLower * nextX (3 ^ middleLength) firstY) middleLength := by
    simpa using mul_hasValue (mul_hasValue coupling_unit targetLower_unit) currentX_shell
  have sides_eq :
      targetCoefficient * nextY coefficient coupling lower firstX firstY =
        -(coupling * targetLower * nextX (3 ^ middleLength) firstY) :=
    eq_neg_of_add_eq_zero_left pole
  have valuation_eq := congrArg (padicValRat 3) sides_eq
  rw [left_shell.2, padicValRat.neg, right_shell.2] at valuation_eq
  exact_mod_cast valuation_eq.symm

/-- The sole equal-depth branch in the first multi-transfer gate cannot reach a later pole.
After factoring the common `3^β`, its denominator remains at depth `β`; neither singleton
upper length can balance a target depth in `{1,β}`. -/
theorem resonantSingleton_pole_false
    {width targetDepth : Nat} {target : List NearyTile} {punctuated : ℤ}
    {targetCoefficient targetLower : ℚ}
    (width_large : 3 ≤ width)
    (target_shell : HasPoleShell width target targetDepth)
    (punctuated_mod : punctuated ≡ 2 [ZMOD 3])
    (letter : TagLetter)
    (targetCoefficient_shell : HasValue 3 targetCoefficient targetDepth)
    (targetLower_unit : IsUnit 3 targetLower)
    (pole :
      targetCoefficient *
          nextY (singletonCoefficient width letter) (centeredCoupling width) 2
            ((3 : ℚ) ^ width) (centeredCoefficient width * punctuated) +
        centeredCoupling width * targetLower *
          nextX (3 ^ upperLength width [.erase letter])
            (centeredCoefficient width * punctuated) = 0) : False := by
  have width_pos : 0 < width := by omega
  have firstY_unit := centeredPunctuated_isUnit width_pos punctuated_mod
  have currentY_shell :=
    resonantSingleton_nextY_hasValue width_pos punctuated_mod letter
  have balance :
      upperLength width [.erase letter] = targetDepth + min width width :=
    pole_length_balance firstY_unit (by simpa using currentY_shell)
      (centeredCoupling_isUnit width_pos) targetLower_unit targetCoefficient_shell pole
  rw [min_self] at balance
  rcases target_shell.2 with target_single | target_multi
  · rw [target_single.2] at balance
    cases letter with
    | b => rw [upperLength_singleton_erase_b] at balance; omega
    | c => rw [upperLength_singleton_erase_c] at balance; omega
  · rw [target_multi.2] at balance
    cases letter with
    | b => rw [upperLength_singleton_erase_b] at balance; omega
    | c => rw [upperLength_singleton_erase_c] at balance; omega

/-- The exact first multi-transfer trichotomy. The middle and target shell hypotheses are the
pole-shell theorem of `MM-S02`; `denominator_shell` is automatic off resonance and is the one
unit calculation required on resonance. -/
theorem firstMultiTransfer_trichotomy
    {width firstDepth middleDepth targetDepth : Nat}
    {first middle target : List NearyTile}
    (width_large : 3 ≤ width)
    (first_block : IsRoleBlock first)
    (middle_shell : HasPoleShell width middle middleDepth)
    (target_shell : HasPoleShell width target targetDepth)
    (first_nontrivial : 1 < firstDepth)
    (firstDepth_eq : firstDepth = upperLength width first)
    (balance :
      upperLength width middle = targetDepth + min middleDepth firstDepth) :
    (middle.map NearyTile.letter = [.c, .c] ∧ targetDepth = 1) ∨
      (middle.map NearyTile.letter = List.replicate (width + 1) .c ∧
        targetDepth = width) ∨
      (first.map NearyTile.letter = [.c, .c] ∧
        middle = [.erase .b] ∧ targetDepth = width) := by
  rcases middle_shell with ⟨middle_block, middle_single | middle_multi⟩
  · obtain ⟨middle_length, middleDepth_eq⟩ := middle_single
    obtain ⟨front, letter, middle_eq⟩ := middle_block
    have front_nil : front = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa [middle_eq] using middle_length
    subst front
    simp only [List.nil_append] at middle_eq
    subst middle
    rcases target_shell.2 with target_single | target_multi
    · obtain ⟨_, targetDepth_eq⟩ := target_single
      rw [middleDepth_eq, targetDepth_eq] at balance
      rw [targetDepth_eq]
      have minimum_two_le : 2 ≤ min width firstDepth :=
        Nat.le_min.mpr ⟨by omega, by omega⟩
      cases letter with
      | c =>
          rw [upperLength_singleton_erase_c] at balance
          omega
      | b =>
          have minimum_eq_two : min width firstDepth = 2 := by
            rw [upperLength_singleton_erase_b] at balance
            omega
          have firstDepth_two : firstDepth = 2 := by
            by_cases first_le : firstDepth ≤ width
            · rwa [min_eq_right first_le] at minimum_eq_two
            · have width_le : width ≤ firstDepth := Nat.le_of_not_ge first_le
              rw [min_eq_left width_le] at minimum_eq_two
              omega
          have first_short : upperLength width first < width + 2 := by omega
          have first_letters :=
            first_block.letters_eq_replicate_c_of_upperLength_lt first_short
          have first_length :=
            first_block.length_eq_upperLength_of_upperLength_lt first_short
          rw [← firstDepth_eq, firstDepth_two] at first_length
          rw [first_letters, first_length]
          exact Or.inr <| Or.inr ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, targetDepth_eq⟩ := target_multi
      rw [middleDepth_eq, targetDepth_eq] at balance
      rw [targetDepth_eq]
      have minimum_two_le : 2 ≤ min width firstDepth :=
        Nat.le_min.mpr ⟨by omega, by omega⟩
      have minimum_le_width : min width firstDepth ≤ width := min_le_left _ _
      cases letter with
      | b => rw [upperLength_singleton_erase_b] at balance; omega
      | c => rw [upperLength_singleton_erase_c] at balance; omega
  · obtain ⟨_, middleDepth_eq⟩ := middle_multi
    rw [middleDepth_eq] at balance
    have minimum_eq : min 1 firstDepth = 1 := min_eq_left (by omega)
    rw [minimum_eq] at balance
    rcases target_shell.2 with target_single | target_multi
    · obtain ⟨_, targetDepth_eq⟩ := target_single
      rw [targetDepth_eq] at balance ⊢
      have middle_length_eq : upperLength width middle = width + 1 := by omega
      have middle_short : upperLength width middle < width + 2 := by omega
      have middle_letters :=
        middle_block.letters_eq_replicate_c_of_upperLength_lt middle_short
      have middle_length :=
        middle_block.length_eq_upperLength_of_upperLength_lt middle_short
      rw [middle_length_eq] at middle_length
      rw [middle_letters, middle_length]
      exact Or.inr <| Or.inl ⟨rfl, rfl⟩
    · obtain ⟨_, targetDepth_eq⟩ := target_multi
      rw [targetDepth_eq] at balance ⊢
      have middle_length_eq : upperLength width middle = 2 := by omega
      have middle_short : upperLength width middle < width + 2 := by omega
      have middle_letters :=
        middle_block.letters_eq_replicate_c_of_upperLength_lt middle_short
      have middle_length :=
        middle_block.length_eq_upperLength_of_upperLength_lt middle_short
      rw [middle_length_eq] at middle_length
      rw [middle_letters, middle_length]
      exact Or.inl ⟨rfl, rfl⟩

/-- Off resonance, an actual centered pole is already in the three-shape first multi-transfer
frontier. -/
theorem firstMultiTransfer_trichotomy_of_nonresonant_pole
    {width firstDepth middleDepth targetDepth : Nat}
    {first middle target : List NearyTile}
    {firstX firstY coefficient coupling lower targetCoefficient targetLower : ℚ}
    (width_large : 3 ≤ width)
    (first_block : IsRoleBlock first)
    (middle_shell : HasPoleShell width middle middleDepth)
    (target_shell : HasPoleShell width target targetDepth)
    (first_nontrivial : 1 < firstDepth)
    (firstDepth_eq : firstDepth = upperLength width first)
    (firstX_shell : HasValue 3 firstX firstDepth)
    (firstY_unit : IsUnit 3 firstY)
    (coefficient_shell : HasValue 3 coefficient middleDepth)
    (coupling_unit : IsUnit 3 coupling) (lower_unit : IsUnit 3 lower)
    (targetCoefficient_shell : HasValue 3 targetCoefficient targetDepth)
    (targetLower_unit : IsUnit 3 targetLower)
    (nonresonant : middleDepth ≠ firstDepth)
    (pole :
      targetCoefficient * nextY coefficient coupling lower firstX firstY +
          coupling * targetLower *
            nextX (3 ^ upperLength width middle) firstY = 0) :
    (middle.map NearyTile.letter = [.c, .c] ∧ targetDepth = 1) ∨
      (middle.map NearyTile.letter = List.replicate (width + 1) .c ∧
        targetDepth = width) ∨
      (first.map NearyTile.letter = [.c, .c] ∧
        middle = [.erase .b] ∧ targetDepth = width) := by
  have denominator_shell :=
    nextY_hasValue_min_of_ne firstX_shell firstY_unit coefficient_shell coupling_unit
      lower_unit nonresonant
  have balance := pole_length_balance firstY_unit denominator_shell coupling_unit
    targetLower_unit targetCoefficient_shell pole
  exact firstMultiTransfer_trichotomy width_large first_block middle_shell target_shell
    first_nontrivial firstDepth_eq balance

/-- Every physical first multi-transfer pole in the expected shells belongs to the three-shape
frontier. The only possible equal-depth case is a singleton middle block at depth `β`; its
normalized unit calculation is contradictory, so the nonresonant length balance is exhaustive. -/
theorem firstMultiTransfer_trichotomy_of_pole
    {width firstDepth middleDepth targetDepth : Nat}
    {body : List TagLetter} {first middle target : List NearyTile}
    {punctuated : ℤ} {targetCoefficient targetLower : ℚ}
    (width_large : 3 ≤ width)
    (first_block : IsRoleBlock first)
    (middle_shell : HasPoleShell width middle middleDepth)
    (target_shell : HasPoleShell width target targetDepth)
    (first_nontrivial : 1 < firstDepth)
    (firstDepth_eq : firstDepth = upperLength width first)
    (punctuated_mod : punctuated ≡ 2 [ZMOD 3])
    (middleCoefficient_shell :
      HasValue 3 (blockCoefficient width body middle : ℚ) middleDepth)
    (middleLower_unit : IsUnit 3 (swappedLowerCode width body middle : ℚ))
    (targetCoefficient_shell : HasValue 3 targetCoefficient targetDepth)
    (targetLower_unit : IsUnit 3 targetLower)
    (pole :
      targetCoefficient *
          nextY (blockCoefficient width body middle) (centeredCoupling width)
            (swappedLowerCode width body middle) ((3 : ℚ) ^ firstDepth)
            (centeredCoefficient width * punctuated) +
        centeredCoupling width * targetLower *
          nextX (3 ^ upperLength width middle)
            (centeredCoefficient width * punctuated) = 0) :
    (middle.map NearyTile.letter = [.c, .c] ∧ targetDepth = 1) ∨
      (middle.map NearyTile.letter = List.replicate (width + 1) .c ∧
        targetDepth = width) ∨
      (first.map NearyTile.letter = [.c, .c] ∧
        middle = [.erase .b] ∧ targetDepth = width) := by
  have width_pos : 0 < width := by omega
  by_cases nonresonant : middleDepth ≠ firstDepth
  · exact firstMultiTransfer_trichotomy_of_nonresonant_pole width_large first_block
      middle_shell target_shell first_nontrivial firstDepth_eq (primePower_hasValue firstDepth)
      (centeredPunctuated_isUnit width_pos punctuated_mod) middleCoefficient_shell
      (centeredCoupling_isUnit width_pos) middleLower_unit targetCoefficient_shell
      targetLower_unit nonresonant pole
  · have depths_eq : middleDepth = firstDepth := not_ne_iff.mp nonresonant
    rcases middle_shell with ⟨middle_block, middle_single | middle_multi⟩
    · obtain ⟨middle_length, middleDepth_eq⟩ := middle_single
      obtain ⟨front, letter, middle_eq⟩ := middle_block
      have front_nil : front = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa [middle_eq] using middle_length
      subst front
      simp only [List.nil_append] at middle_eq
      subst middle
      have firstDepth_width : firstDepth = width := by omega
      have resonant_pole := pole
      rw [firstDepth_width, blockCoefficient_singleton, swappedLowerCode_singleton]
        at resonant_pole
      exact False.elim <| resonantSingleton_pole_false width_large target_shell punctuated_mod
        letter targetCoefficient_shell targetLower_unit resonant_pole
    · obtain ⟨_, middleDepth_eq⟩ := middle_multi
      omega

/-! ## Extinction of the two-`c`, singleton-`b`, singleton branch -/

/-- The punctuated swapped upper code depends only on role letters. Two `c` roles give the
closed value `14ρ-1`, independently of their rule/erasure phases. -/
theorem swappedUpperCode_double_c
    {width : Nat} {block : List NearyTile}
    (letters : block.map NearyTile.letter = [.c, .c]) :
    swappedUpperCode width block = 14 * widthScale width - 1 := by
  rw [swappedUpperCode, spell_nearyUpper, letters]
  change
    (ternaryCode ((true :: ([true, true] ++ List.replicate width false)).map not) : ℤ) =
      14 * widthScale width - 1
  have tail :
      (ternaryCode (([true, true] ++ List.replicate width false).map not) : ℤ) =
        terminalDiscrepancy width := by
    exact swappedUpperCode_singleton_c width
  rw [List.map_cons, ternaryCode_cons, List.length_map, List.length_append,
    List.length_replicate]
  push_cast
  rw [tail]
  norm_num [ternaryDigit]
  simp [terminalDiscrepancy, widthScale]
  ring

/-- Two `c` roles have upper length two, independently of their phases. -/
theorem upperLength_double_c
    {width : Nat} {block : List NearyTile}
    (letters : block.map NearyTile.letter = [.c, .c]) :
    upperLength width block = 2 := by
  rw [upperLength, spell_nearyUpper, letters]
  simp [tagEncode_cons, tagCode]

/-- The third shape in the first multi-transfer trichotomy is empty. After a two-`c` first
block, the literal singleton `D_b` middle block misses both singleton target poles. The exact
pole expressions factor into strictly negative polynomials for every `β≥3`. -/
theorem twoC_then_singletonB_avoids_singleton_pole
    {width : Nat} (width_large : 3 ≤ width) (body : List TagLetter)
    {first : List NearyTile}
    (first_letters : first.map NearyTile.letter = [.c, .c])
    (target : TagLetter)
    (pole :
      (singletonCoefficient width target : ℚ) *
          nextY (blockCoefficient width body [.erase .b]) (centeredCoupling width) 2
            ((3 : ℚ) ^ upperLength width first)
            (centeredCoefficient width * swappedUpperCode width first) +
        centeredCoupling width * 2 *
          nextX (3 ^ upperLength width [.erase .b])
            (centeredCoefficient width * swappedUpperCode width first) = 0) : False := by
  have scale_ge_nat : 3 ^ 3 ≤ 3 ^ width :=
    Nat.pow_le_pow_right (by omega) width_large
  have scale_ge_int : (27 : ℤ) ≤ widthScale width := by
    have casted : ((3 ^ 3 : Nat) : ℤ) ≤ ((3 ^ width : Nat) : ℤ) := by
      exact_mod_cast scale_ge_nat
    simpa [widthScale] using casted
  have scale_ge : (27 : ℚ) ≤ (widthScale width : ℚ) := by
    exact_mod_cast scale_ge_int
  have cubic_pos :
      (0 : ℚ) <
        252 * (widthScale width : ℚ) ^ 3 -
          578 * (widthScale width : ℚ) ^ 2 +
          238 * (widthScale width : ℚ) - 9 := by
    have shifted_pos :
        (0 : ℚ) <
          252 * ((widthScale width : ℚ) - 27) ^ 3 +
            19834 * ((widthScale width : ℚ) - 27) ^ 2 +
            520150 * ((widthScale width : ℚ) - 27) + 4545171 := by
      positivity
    nlinarith [shifted_pos]
  have quintic_pos :
      (0 : ℚ) <
        4536 * (widthScale width : ℚ) ^ 5 -
          11412 * (widthScale width : ℚ) ^ 4 +
          3824 * (widthScale width : ℚ) ^ 3 +
          2848 * (widthScale width : ℚ) ^ 2 -
          1588 * (widthScale width : ℚ) + 171 := by
    have shifted_pos :
        (0 : ℚ) <
          4536 * ((widthScale width : ℚ) - 27) ^ 5 +
            600948 * ((widthScale width : ℚ) - 27) ^ 4 +
            31838768 * ((widthScale width : ℚ) - 27) ^ 3 +
            843217384 * ((widthScale width : ℚ) - 27) ^ 2 +
            11163107588 * ((widthScale width : ℚ) - 27) + 59099138739 := by
      positivity
    nlinarith [shifted_pos]
  rw [upperLength_double_c first_letters, upperLength_singleton_erase_b,
    swappedUpperCode_double_c first_letters, blockCoefficient_singleton] at pole
  have punctuated_cast :
      (((14 * widthScale width - 1 : ℤ) : ℚ)) =
        14 * (widthScale width : ℚ) - 1 := by
    push_cast
    ring
  rw [punctuated_cast] at pole
  have scale_pos : (0 : ℚ) < (widthScale width : ℚ) := by linarith
  have scale_minus_two_pos : (0 : ℚ) < (widthScale width : ℚ) - 2 := by
    linarith
  have head_pos : (0 : ℚ) < 5 * (widthScale width : ℚ) - 1 := by
    linarith
  cases target with
  | c =>
      have expression_eq :
          (singletonCoefficient width .c : ℚ) *
                nextY (singletonCoefficient width .b) (centeredCoupling width) 2
                  ((3 : ℚ) ^ 2)
                  (centeredCoefficient width * (14 * widthScale width - 1)) +
              centeredCoupling width * 2 *
                nextX (3 ^ (width + 2))
                  (centeredCoefficient width * (14 * widthScale width - 1)) =
            -(widthScale width : ℚ) * ((widthScale width : ℚ) - 2) ^ 2 *
              (5 * (widthScale width : ℚ) - 1) *
              (252 * (widthScale width : ℚ) ^ 3 -
                578 * (widthScale width : ℚ) ^ 2 +
                238 * (widthScale width : ℚ) - 9) := by
        norm_num [nextX, nextY, singletonCoefficient, singletonBCofactor,
          centeredCoefficient, centeredCoupling, terminalDiscrepancy, setterMarker,
          widthScale, pow_succ]
        ring
      rw [expression_eq] at pole
      have expression_neg :
          -(widthScale width : ℚ) * ((widthScale width : ℚ) - 2) ^ 2 *
              (5 * (widthScale width : ℚ) - 1) *
              (252 * (widthScale width : ℚ) ^ 3 -
                578 * (widthScale width : ℚ) ^ 2 +
                238 * (widthScale width : ℚ) - 9) < 0 := by
        have product_pos :
            (0 : ℚ) <
              (widthScale width : ℚ) * ((widthScale width : ℚ) - 2) ^ 2 *
                (5 * (widthScale width : ℚ) - 1) *
                (252 * (widthScale width : ℚ) ^ 3 -
                  578 * (widthScale width : ℚ) ^ 2 +
                  238 * (widthScale width : ℚ) - 9) := by
          positivity
        nlinarith
      linarith
  | b =>
      have expression_eq :
          (singletonCoefficient width .b : ℚ) *
                nextY (singletonCoefficient width .b) (centeredCoupling width) 2
                  ((3 : ℚ) ^ 2)
                  (centeredCoefficient width * (14 * widthScale width - 1)) +
              centeredCoupling width * 2 *
                nextX (3 ^ (width + 2))
                  (centeredCoefficient width * (14 * widthScale width - 1)) =
            -(widthScale width : ℚ) * ((widthScale width : ℚ) - 2) ^ 2 *
              (4536 * (widthScale width : ℚ) ^ 5 -
                11412 * (widthScale width : ℚ) ^ 4 +
                3824 * (widthScale width : ℚ) ^ 3 +
                2848 * (widthScale width : ℚ) ^ 2 -
                1588 * (widthScale width : ℚ) + 171) := by
        norm_num [nextX, nextY, singletonCoefficient, singletonBCofactor,
          centeredCoefficient, centeredCoupling, terminalDiscrepancy, setterMarker,
          widthScale, pow_succ]
        ring
      rw [expression_eq] at pole
      have expression_neg :
          -(widthScale width : ℚ) * ((widthScale width : ℚ) - 2) ^ 2 *
              (4536 * (widthScale width : ℚ) ^ 5 -
                11412 * (widthScale width : ℚ) ^ 4 +
                3824 * (widthScale width : ℚ) ^ 3 +
                2848 * (widthScale width : ℚ) ^ 2 -
                1588 * (widthScale width : ℚ) + 171) < 0 := by
        have product_pos :
            (0 : ℚ) <
              (widthScale width : ℚ) * ((widthScale width : ℚ) - 2) ^ 2 *
                (4536 * (widthScale width : ℚ) ^ 5 -
                  11412 * (widthScale width : ℚ) ^ 4 +
                  3824 * (widthScale width : ℚ) ^ 3 +
                  2848 * (widthScale width : ℚ) ^ 2 -
                  1588 * (widthScale width : ℚ) + 171) := by
          positivity
        nlinarith
      linarith

end MatrixMortality.SwappedSetterMultitransfer
