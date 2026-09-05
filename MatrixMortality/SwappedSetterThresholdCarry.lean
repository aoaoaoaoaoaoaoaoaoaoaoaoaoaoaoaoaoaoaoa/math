import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Int.Interval
import MatrixMortality.SwappedSetterHistory

/-!
# Multiplicative suffix carry for swapped-setter thresholds

A later centered carrier is generally not a difference of two raw Neary codes.  At a physical
target, however, its projective numerator and denominator cross-multiply the target's two codes.
Reading that product equality from the least significant ternary digit gives an exact balanced
carry with a finite state window for each fixed carrier.  This is the multiplicative replacement
for the raw common-suffix discrepancy used at the distinguished boundary.
-/

namespace MatrixMortality.SwappedSetterThresholdCarry

open SwappedSetterHistory SwappedSetterMultitransfer

/-- Signed swapped ternary value of a binary word. -/
def signedSwappedCode (word : List Bool) : ℤ :=
  ternaryCode (word.map not)

/-- Swapped ternary value of one binary digit. -/
def signedSwappedDigit (bit : Bool) : ℤ :=
  ternaryDigit (!bit)

/-- Swapped ternary value with the least significant digit first. -/
def littleSwappedCode : List Bool → ℤ
  | [] => 0
  | bit :: bits => signedSwappedDigit bit + 3 * littleSwappedCode bits

theorem signedSwappedCode_append (left right : List Bool) :
    signedSwappedCode (left ++ right) =
      (3 : ℤ) ^ right.length * signedSwappedCode left + signedSwappedCode right := by
  simp [signedSwappedCode, List.map_append, ternaryCode_append]

theorem signedSwappedCode_reverse (word : List Bool) :
    littleSwappedCode word.reverse = signedSwappedCode word := by
  induction word using List.reverseRecOn with
  | nil => rfl
  | append_singleton word bit induction =>
      rw [List.reverse_append, List.reverse_singleton, List.singleton_append,
        littleSwappedCode, signedSwappedCode_append, induction]
      simp [signedSwappedCode, signedSwappedDigit, ternaryCode, ternaryDigit]
      ring

/-- One least-significant-digit balanced multiplication carry. -/
def CarryStep (left right incoming : ℤ) (upper lower : Bool) (outgoing : ℤ) : Prop :=
  incoming + left * signedSwappedDigit upper - right * signedSwappedDigit lower =
    3 * outgoing

/-- Exact least-to-most-significant carry path for `left·upper = right·lower`. -/
inductive CarryRun (left right : ℤ) : ℤ → List Bool → List Bool → ℤ → Prop
  | nil (carry : ℤ) : CarryRun left right carry [] [] carry
  | cons {incoming outgoing final : ℤ} {upper lower : Bool}
      {upperTail lowerTail : List Bool}
      (step : CarryStep left right incoming upper lower outgoing)
      (tail : CarryRun left right outgoing upperTail lowerTail final) :
      CarryRun left right incoming (upper :: upperTail) (lower :: lowerTail) final

theorem CarryRun.length_eq
    {left right incoming final : ℤ} {upper lower : List Bool}
    (run : CarryRun left right incoming upper lower final) :
    upper.length = lower.length := by
  induction run with
  | nil => rfl
  | cons _ _ induction => simp [induction]

/-- A carry path is exactly its accumulated product equation. -/
theorem carryRun_iff
    (left right incoming final : ℤ) (upper lower : List Bool) :
    CarryRun left right incoming upper lower final ↔
      upper.length = lower.length ∧
        left * littleSwappedCode upper - right * littleSwappedCode lower + incoming =
          (3 : ℤ) ^ upper.length * final := by
  constructor
  · intro run
    constructor
    · exact run.length_eq
    · induction run with
      | nil => simp [littleSwappedCode]
      | @cons incoming outgoing final upper lower upperTail lowerTail step tail induction =>
          rw [CarryStep] at step
          simp only [littleSwappedCode, List.length_cons]
          rw [pow_succ]
          linear_combination 3 * induction + step
  · rintro ⟨lengths, equation⟩
    induction upper generalizing lower incoming with
    | nil =>
        have lower_nil : lower = [] :=
          List.eq_nil_of_length_eq_zero (by simpa using lengths.symm)
        subst lower
        simp [littleSwappedCode] at equation
        subst final
        exact CarryRun.nil incoming
    | cons upper upperTail induction =>
        have lower_nonempty : lower ≠ [] := by
          intro lower_nil
          subst lower
          simp at lengths
        obtain ⟨lower, lowerTail, rfl⟩ := List.exists_cons_of_ne_nil lower_nonempty
        have tail_lengths : upperTail.length = lowerTail.length := by simpa using lengths
        let outgoing : ℤ :=
          (3 : ℤ) ^ upperTail.length * final -
            (left * littleSwappedCode upperTail -
              right * littleSwappedCode lowerTail)
        have step : CarryStep left right incoming upper lower outgoing := by
          rw [CarryStep]
          dsimp [outgoing]
          simp only [littleSwappedCode, List.length_cons] at equation
          rw [pow_succ] at equation
          linear_combination equation
        have tail_equation :
            left * littleSwappedCode upperTail -
                right * littleSwappedCode lowerTail + outgoing =
              (3 : ℤ) ^ upperTail.length * final := by
          simp [outgoing]
        exact CarryRun.cons step <|
          induction outgoing lowerTail tail_lengths tail_equation

/-- Aggregate carry left after equal-length suffixes have been consumed. -/
def SuffixCarry (left right : ℤ) (upper lower : List Bool) (carry : ℤ) : Prop :=
  upper.length = lower.length ∧
    left * signedSwappedCode upper - right * signedSwappedCode lower =
      (3 : ℤ) ^ upper.length * carry

/-- The aggregate suffix equation is equivalent to an exact digit-by-digit carry run. -/
theorem suffixCarry_iff_run
    (left right carry : ℤ) (upper lower : List Bool) :
    SuffixCarry left right upper lower carry ↔
      CarryRun left right 0 upper.reverse lower.reverse carry := by
  rw [carryRun_iff]
  simp only [List.length_reverse, add_zero]
  rw [signedSwappedCode_reverse, signedSwappedCode_reverse]
  rfl

/-- One reversed erasure block is the affine contraction
`c ↦ (c+2(left-right))/3`. -/
theorem erasureCarry_iff (left right incoming outgoing : ℤ) :
    CarryRun left right incoming [false] [false] outgoing ↔
      incoming + 2 * (left - right) = 3 * outgoing := by
  rw [carryRun_iff]
  norm_num [littleSwappedCode, signedSwappedDigit, ternaryDigit]
  ring_nf

/-- One reversed rule block `011` is the affine contraction
`c ↦ (c+26·left-14·right)/27`. -/
theorem ruleCarry_iff (left right incoming outgoing : ℤ) :
    CarryRun left right incoming [false, false, false] [false, true, true] outgoing ↔
      incoming + 26 * left - 14 * right = 27 * outgoing := by
  rw [carryRun_iff]
  norm_num [littleSwappedCode, signedSwappedDigit, ternaryDigit]
  ring_nf

private theorem signedSwappedDigit_abs_le_two (bit : Bool) :
    |signedSwappedDigit bit| ≤ 2 := by
  cases bit <;> norm_num [signedSwappedDigit, ternaryDigit]

/-- The balanced carry interval is forward invariant.  Thus fixed carrier coefficients give a
finite exact automaton, independent of the suffix length. -/
theorem carryStep_abs_le
    {left right incoming outgoing : ℤ} {upper lower : Bool}
    (incoming_bound : |incoming| ≤ |left| + |right|)
    (step : CarryStep left right incoming upper lower outgoing) :
    |outgoing| ≤ |left| + |right| := by
  have upper_digit := signedSwappedDigit_abs_le_two upper
  have lower_digit := signedSwappedDigit_abs_le_two lower
  have left_product :
      |left * signedSwappedDigit upper| ≤ 2 * |left| := by
    rw [abs_mul]
    nlinarith [abs_nonneg left]
  have right_product :
      |right * signedSwappedDigit lower| ≤ 2 * |right| := by
    rw [abs_mul]
    nlinarith [abs_nonneg right]
  have triangle :
      |incoming + left * signedSwappedDigit upper -
          right * signedSwappedDigit lower| ≤
        |incoming| + |left * signedSwappedDigit upper| +
          |right * signedSwappedDigit lower| := by
    calc
      |incoming + left * signedSwappedDigit upper -
          right * signedSwappedDigit lower| ≤
          |incoming + left * signedSwappedDigit upper| +
            |right * signedSwappedDigit lower| := abs_sub _ _
      _ ≤ (|incoming| + |left * signedSwappedDigit upper|) +
            |right * signedSwappedDigit lower| :=
          add_le_add (abs_add_le incoming (left * signedSwappedDigit upper)) le_rfl
  rw [CarryStep] at step
  have triple_abs :
      |incoming + left * signedSwappedDigit upper -
          right * signedSwappedDigit lower| = 3 * |outgoing| := by
    rw [step, abs_mul]
    norm_num
  rw [triple_abs] at triangle
  nlinarith [abs_nonneg outgoing, abs_nonneg left, abs_nonneg right]

/-- Every state in a fixed-carrier carry run lies in the finite interval determined by the two
primitive carrier coefficients. -/
theorem CarryRun.final_abs_le
    {left right incoming final : ℤ} {upper lower : List Bool}
    (run : CarryRun left right incoming upper lower final)
    (incoming_bound : |incoming| ≤ |left| + |right|) :
    |final| ≤ |left| + |right| := by
  induction run with
  | nil => exact incoming_bound
  | cons step tail induction =>
      exact induction (carryStep_abs_le incoming_bound step)

/-- A threshold suffix carry belongs to the explicit finite state interval. -/
theorem SuffixCarry.carry_mem
    {left right carry : ℤ} {upper lower : List Bool}
    (suffix : SuffixCarry left right upper lower carry) :
    carry ∈ Finset.Icc (-(|left| + |right|)) (|left| + |right|) := by
  have run := (suffixCarry_iff_run left right carry upper lower).mp suffix
  have bound := run.final_abs_le <| add_nonneg (abs_nonneg left) (abs_nonneg right)
  simpa [abs_le] using bound

/-- Cross-multiplication of complete codes supplies the exact carry on any aligned suffix pair.
The carry is the corresponding difference of the discarded prefixes. -/
theorem suffixCarry_of_crossProduct
    {left right : ℤ} {upperPrefix lowerPrefix upperSuffix lowerSuffix : List Bool}
    (suffix_length : upperSuffix.length = lowerSuffix.length)
    (cross :
      left * signedSwappedCode (upperPrefix ++ upperSuffix) =
        right * signedSwappedCode (lowerPrefix ++ lowerSuffix)) :
    SuffixCarry left right upperSuffix lowerSuffix
      (right * signedSwappedCode lowerPrefix - left * signedSwappedCode upperPrefix) := by
  constructor
  · exact suffix_length
  · rw [signedSwappedCode_append, signedSwappedCode_append, suffix_length] at cross
    rw [suffix_length]
    linear_combination cross

private theorem signedSwappedCode_replicate_false (length : Nat) :
    signedSwappedCode (List.replicate length false) = (3 : ℤ) ^ length - 1 := by
  induction length with
  | zero => rfl
  | succ length induction =>
      rw [List.replicate_succ', signedSwappedCode_append, induction, pow_succ]
      norm_num [signedSwappedCode, ternaryCode, ternaryDigit]
      ring

/-- When both aligned suffixes are the marker's all-erasure run, the carrier numerator and
denominator are congruent modulo the full run power. -/
theorem matchedFalseSuffix_dvd_gap
    {left right carry : ℤ} {length : Nat}
    (suffix : SuffixCarry left right
      (List.replicate length false) (List.replicate length false) carry) :
    (3 : ℤ) ^ length ∣ left - right := by
  have equation := suffix.2
  rw [signedSwappedCode_replicate_false] at equation
  simp only [List.length_replicate] at equation
  refine ⟨left - right - carry, ?_⟩
  have factored :
      (left - right) * ((3 : ℤ) ^ length - 1) = (3 : ℤ) ^ length * carry := by
    calc
      (left - right) * ((3 : ℤ) ^ length - 1) =
          left * ((3 : ℤ) ^ length - 1) -
            right * ((3 : ℤ) ^ length - 1) := by ring
      _ = (3 : ℤ) ^ length * carry := equation
  calc
    left - right =
        (3 : ℤ) ^ length * (left - right) -
          (left - right) * ((3 : ℤ) ^ length - 1) := by ring
    _ = (3 : ℤ) ^ length * (left - right) - (3 : ℤ) ^ length * carry := by
      rw [factored]
    _ = (3 : ℤ) ^ length * (left - right - carry) := by ring

/-- A matched all-erasure suffix longer than the carrier gap forces the carrier to be the
distinguished ratio one. -/
theorem matchedFalseSuffix_eq
    {left right carry : ℤ} {length : Nat}
    (suffix : SuffixCarry left right
      (List.replicate length false) (List.replicate length false) carry)
    (gap_small : |left - right| < (3 : ℤ) ^ length) :
    left = right := by
  have gap_zero := Int.eq_zero_of_abs_lt_dvd
    (matchedFalseSuffix_dvd_gap suffix) gap_small
  exact sub_eq_zero.mp gap_zero

/-- A physical target has an erasure tail of the stated number of tiles. -/
def HasErasureTail (length : Nat) (block : List NearyTile) : Prop :=
  ∃ (front : List NearyTile) (letters : List TagLetter),
    letters.length = length ∧ block = front ++ letters.map NearyTile.erase

private theorem spell_nearyLower_erase_map
    (width : Nat) (body letters : List TagLetter) :
    spell (nearyLower width body) (letters.map NearyTile.erase) =
      List.replicate letters.length false := by
  induction letters with
  | nil => rfl
  | cons letter letters induction =>
      change nearyLower width body (.erase letter) ++
          spell (nearyLower width body) (letters.map NearyTile.erase) = _
      rw [induction]
      cases letter <;> simp [nearyLower, List.replicate_succ]

/-- A threshold equality against a target ending in `width` erasures forces the primitive
carrier gap to contain the full marker power. -/
theorem erasureTail_threshold_dvd_gap
    {width : Nat} (body : List TagLetter) {target : List NearyTile}
    (target_tail : HasErasureTail width target)
    {numerator denominator : ℤ}
    (threshold :
      denominator * swappedUpperCode width target =
        numerator * swappedLowerCode width body target) :
    (3 : ℤ) ^ width ∣ denominator - numerator := by
  obtain ⟨front, letters, letters_length, target_eq⟩ := target_tail
  have upper_factorization :
      spell (nearyUpper width) target ++ nearyMarker width =
        (spell (nearyUpper width) target ++ [true]) ++
          List.replicate width false := by
    simp [nearyMarker, List.append_assoc]
  have lower_factorization :
      spell (nearyLower width body) target =
        spell (nearyLower width body) front ++ List.replicate width false := by
    rw [target_eq, spell_append, spell_nearyLower_erase_map, letters_length]
  have cross :
      denominator * signedSwappedCode
          ((spell (nearyUpper width) target ++ [true]) ++
            List.replicate width false) =
        numerator * signedSwappedCode
          (spell (nearyLower width body) front ++ List.replicate width false) := by
    rw [← upper_factorization, ← lower_factorization]
    simpa [signedSwappedCode, swappedUpperCode, swappedLowerCode] using threshold
  have suffix := suffixCarry_of_crossProduct (left := denominator) (right := numerator)
    (upperPrefix := spell (nearyUpper width) target ++ [true])
    (lowerPrefix := spell (nearyLower width body) front)
    (upperSuffix := List.replicate width false)
    (lowerSuffix := List.replicate width false) (by simp) cross
  exact matchedFalseSuffix_dvd_gap suffix

/-- Any threshold equality against a target ending in `width` erasures is terminal whenever the
primitive carrier gap is smaller than `3^width`. -/
theorem erasureTail_threshold_terminal
    {width : Nat} (body : List TagLetter) {target : List NearyTile}
    (target_tail : HasErasureTail width target)
    {numerator denominator : ℤ} (denominator_ne : denominator ≠ 0)
    (gap_small : |denominator - numerator| < (3 : ℤ) ^ width)
    (threshold :
      denominator * swappedUpperCode width target =
        numerator * swappedLowerCode width body target) :
    swappedUpperCode width target = swappedLowerCode width body target := by
  have gap_dvd := erasureTail_threshold_dvd_gap body target_tail threshold
  have gap_zero := Int.eq_zero_of_abs_lt_dvd gap_dvd gap_small
  have carrier_eq := sub_eq_zero.mp gap_zero
  subst numerator
  exact mul_left_cancel₀ denominator_ne threshold

/-- Homogeneous assertion that a centered state has projective defect ratio
`numerator/denominator`. -/
def RepresentsDefectRatio (width : Nat) (state : CenteredState)
    (numerator denominator : ℤ) : Prop :=
  (terminalDiscrepancy width : ℚ) * ordinaryDefect width state * denominator =
    (centeredCoefficient width : ℚ) * state.y * numerator

private theorem centeredCoefficient_ne_zero
    {width : Nat} (width_two : 2 ≤ width) :
    (centeredCoefficient width : ℚ) ≠ 0 := by
  have power_le : 3 ^ 2 ≤ 3 ^ width :=
    Nat.pow_le_pow_right (by norm_num) width_two
  have scale_ge : (9 : ℤ) ≤ widthScale width := by
    have casted : ((3 ^ 2 : Nat) : ℤ) ≤ ((3 ^ width : Nat) : ℤ) := by
      exact_mod_cast power_le
    simpa [widthScale] using casted
  exact_mod_cast (by simp [centeredCoefficient]; omega : centeredCoefficient width ≠ 0)

/-- A physical pole hit by a represented centered carrier is exactly the multiplicative target
cross-product consumed by the suffix carry. -/
theorem threshold_crossProduct_of_pole
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    (target : List NearyTile) (state : CenteredState) (state_y_ne : state.y ≠ 0)
    {numerator denominator : ℤ}
    (represented : RepresentsDefectRatio width state numerator denominator)
    (pole : poleResidual width body target state = 0) :
    denominator * swappedUpperCode width target =
      numerator * swappedLowerCode width body target := by
  have centered_ne := centeredCoefficient_ne_zero width_two
  have scale_ne : (centeredCoefficient width : ℚ) * state.y ≠ 0 :=
    mul_ne_zero centered_ne state_y_ne
  have pole_eq :
      (centeredCoefficient width : ℚ) * swappedUpperCode width target * state.y =
        terminalDiscrepancy width * swappedLowerCode width body target *
          ordinaryDefect width state := by
    rw [poleResidual_eq_ordinaryDefect] at pole
    linarith
  have product_zero :
      ((centeredCoefficient width : ℚ) * state.y) *
        ((denominator : ℚ) * swappedUpperCode width target -
          numerator * swappedLowerCode width body target) = 0 := by
    rw [RepresentsDefectRatio] at represented
    calc
      ((centeredCoefficient width : ℚ) * state.y) *
          ((denominator : ℚ) * swappedUpperCode width target -
            numerator * swappedLowerCode width body target) =
          denominator *
              ((centeredCoefficient width : ℚ) *
                swappedUpperCode width target * state.y) -
            swappedLowerCode width body target *
              ((centeredCoefficient width : ℚ) * state.y * numerator) := by ring
      _ = denominator *
              (terminalDiscrepancy width * swappedLowerCode width body target *
                ordinaryDefect width state) -
            swappedLowerCode width body target *
              (terminalDiscrepancy width * ordinaryDefect width state * denominator) := by
          rw [pole_eq, represented]
      _ = 0 := by ring
  have cross_rat :
      (denominator : ℚ) * swappedUpperCode width target =
        numerator * swappedLowerCode width body target := by
    exact sub_eq_zero.mp <| (mul_eq_zero.mp product_zero).resolve_left scale_ne
  exact_mod_cast cross_rat

/-- Every represented physical pole supplies an exact finite-state carry on each pair of
equally long target suffixes.  The discarded prefixes determine the outgoing carry. -/
theorem suffixCarry_of_pole
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    (target : List NearyTile) (state : CenteredState) (state_y_ne : state.y ≠ 0)
    {numerator denominator : ℤ}
    (represented : RepresentsDefectRatio width state numerator denominator)
    (pole : poleResidual width body target state = 0)
    {upperPrefix lowerPrefix upperSuffix lowerSuffix : List Bool}
    (upper_factorization :
      spell (nearyUpper width) target ++ nearyMarker width =
        upperPrefix ++ upperSuffix)
    (lower_factorization :
      spell (nearyLower width body) target = lowerPrefix ++ lowerSuffix)
    (suffix_length : upperSuffix.length = lowerSuffix.length) :
    SuffixCarry denominator numerator upperSuffix lowerSuffix
      (numerator * signedSwappedCode lowerPrefix -
        denominator * signedSwappedCode upperPrefix) := by
  have threshold := threshold_crossProduct_of_pole width_two body target state state_y_ne
    represented pole
  have cross :
      denominator * signedSwappedCode (upperPrefix ++ upperSuffix) =
        numerator * signedSwappedCode (lowerPrefix ++ lowerSuffix) := by
    rw [← upper_factorization, ← lower_factorization]
    simpa [signedSwappedCode, swappedUpperCode, swappedLowerCode] using threshold
  exact suffixCarry_of_crossProduct suffix_length cross

/-- A nonterminal pole with a full target erasure tail requires carrier height at least the
marker scale.  Below that height the pole is a genuine Neary terminal match. -/
theorem erasureTail_pole_halts
    {width : Nat} (width_two : 2 ≤ width) (body : List TagLetter)
    (body_long : width - 1 ≤ body.length)
    {target : List NearyTile} (target_tail : HasErasureTail width target)
    (state : CenteredState) (state_y_ne : state.y ≠ 0)
    {numerator denominator : ℤ} (denominator_ne : denominator ≠ 0)
    (represented : RepresentsDefectRatio width state numerator denominator)
    (gap_small : |denominator - numerator| < (3 : ℤ) ^ width)
    (pole : poleResidual width body target state = 0) :
    TagHaltsFrom width (tagOutput body) (body.drop (width - 1) ++ [.b]) := by
  have threshold := threshold_crossProduct_of_pole width_two body target state state_y_ne
    represented pole
  have terminal := erasureTail_threshold_terminal body target_tail denominator_ne gap_small
    threshold
  apply tagHaltsFrom_of_swappedTernaryCode_eq width body (by omega) body_long target
  change
    (ternaryCode ((spell (nearyUpper width) target ++ nearyMarker width).map not) : ℤ) =
      (ternaryCode ((spell (nearyLower width body) target).map not) : ℤ) at terminal
  exact_mod_cast terminal

end MatrixMortality.SwappedSetterThresholdCarry
