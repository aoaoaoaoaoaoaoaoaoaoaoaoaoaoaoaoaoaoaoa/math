import MatrixMortality.MixedPrimeNormalization

/-!
# Parikh obstruction for the mixed-prime odd kernel family

A contextual fork whose shorter macro is both a prefix and a suffix of the longer macro forces
the two relation tails after the aligned short-macro square to have the same Parikh vector. The
odd mixed-prime kernel family violates this condition at every possible aligned square.
-/

set_option autoImplicit false

namespace MatrixMortality.GuardedMixedPrimeFork

open MixedPrimeKernel
open MixedPrimeNormalization

/-- Removing one common suffix from two conjugate-border decompositions preserves the Parikh
count of the exposed tails. -/
theorem alignedTail_count_eq
    {α : Type*} [DecidableEq α] (letter : α)
    {short leftBorder rightBorder leftTail rightTail commonSuffix : List α}
    (border : short ++ leftBorder = rightBorder ++ short)
    (left_decomposition : leftBorder = leftTail ++ commonSuffix)
    (right_decomposition : rightBorder = rightTail ++ commonSuffix) :
    leftTail.count letter = rightTail.count letter := by
  have border_count := congrArg (List.count letter) border
  have border_counts :
      short.count letter + leftBorder.count letter =
        rightBorder.count letter + short.count letter := by
    simpa only [List.count_append] using border_count
  have borders_equal : leftBorder.count letter = rightBorder.count letter := by
    omega
  have left_count := congrArg (List.count letter) left_decomposition
  have right_count := congrArg (List.count letter) right_decomposition
  simp only [List.count_append] at left_count right_count
  omega

/-- An unequal exposed-tail count forbids a same-shorter contextual fork decomposition. -/
theorem no_alignedTail_of_count_ne
    {α : Type*} [DecidableEq α] (letter : α)
    {short leftBorder rightBorder leftTail rightTail commonSuffix : List α}
    (border : short ++ leftBorder = rightBorder ++ short)
    (left_decomposition : leftBorder = leftTail ++ commonSuffix)
    (right_decomposition : rightBorder = rightTail ++ commonSuffix)
    (tail_count_ne : leftTail.count letter ≠ rightTail.count letter) : False := by
  exact tail_count_ne <|
    alignedTail_count_eq letter border left_decomposition right_decomposition

/-- Fixed length-`25` head of the left odd-family relation word. -/
def oddFamilyLeftHead : List Letter :=
  [.dilate] ++ List.replicate 10 .translate ++ List.replicate 2 .dilate ++
    [.translate] ++ List.replicate 2 .dilate ++ [.translate] ++
    List.replicate 8 .dilate

/-- Fixed length-`25` head of the right odd-family relation word. -/
def oddFamilyRightHead : List Letter :=
  List.replicate 2 .translate ++ List.replicate 6 .dilate ++
    List.replicate 2 .translate ++ List.replicate 2 .dilate ++
    [.translate, .dilate, .translate, .dilate, .translate] ++
    List.replicate 2 .dilate ++ List.replicate 2 .translate ++
    List.replicate 2 .dilate ++ List.replicate 2 .translate

theorem pumpWord_append_block (depth : ℕ) :
    pumpWord depth ++ [.dilate, .translate] =
      [.dilate, .translate] ++ pumpWord depth := by
  induction depth with
  | zero => rfl
  | succ depth induction =>
      simp only [pumpWord]
      rw [List.append_assoc, induction]

/-- The odd-family pair has fixed heads, one common pump, and two four-letter tails. -/
theorem kernelOddFamily_headPump_factorization (depth : ℕ) :
    kernelOddFamilyLeft depth =
        oddFamilyLeftHead ++ pumpWord depth ++
          [.dilate, .translate, .dilate, .dilate] ∧
      kernelOddFamilyRight depth =
        oddFamilyRightHead ++ pumpWord depth ++
          [.dilate, .dilate, .translate, .translate] := by
  constructor
  · norm_num [kernelOddFamilyLeft, oddFamilyLeftHead, List.replicate_succ]
    have commuted := congrArg (fun word => word ++ [.dilate, .dilate])
      (pumpWord_append_block depth).symm
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using commuted
  · norm_num [kernelOddFamilyRight, oddFamilyRightHead, List.replicate_succ]

@[simp]
theorem oddFamilyLeftHead_length : oddFamilyLeftHead.length = 25 := by
  norm_num [oddFamilyLeftHead]

@[simp]
theorem oddFamilyRightHead_length : oddFamilyRightHead.length = 25 := by
  norm_num [oddFamilyRightHead]

/-- The complete fixed-head dilation count differs by one. -/
theorem oddFamilyHead_dilateCount_gap :
    oddFamilyLeftHead.count .dilate + 1 = oddFamilyRightHead.count .dilate := by
  have translate_ne : Letter.translate ≠ Letter.dilate := by decide
  norm_num [oddFamilyLeftHead, oddFamilyRightHead, List.count_append,
    List.count_replicate, List.replicate_succ, List.count_cons, List.count_nil,
    translate_ne]

/-- Among positive prefixes of the two fixed heads, only length `3` has equal dilation count. -/
theorem oddFamilyHead_prefix_dilateCount_eq
    (prefixLength : ℕ) (prefix_pos : 0 < prefixLength) (prefix_le : prefixLength ≤ 25)
    (counts_eq :
      (oddFamilyLeftHead.take prefixLength).count .dilate =
        (oddFamilyRightHead.take prefixLength).count .dilate) :
    prefixLength = 3 := by
  have translate_ne : Letter.translate ≠ Letter.dilate := by decide
  interval_cases prefixLength <;>
    norm_num [oddFamilyLeftHead, oddFamilyRightHead, List.count_append,
      List.count_replicate, List.replicate_succ, List.count_cons,
      List.count_nil, translate_ne] at counts_eq
  rfl

/-- No proper prefix of the pumped four-letter tails compensates for the fixed-head count gap. -/
theorem oddFamilyPump_prefix_dilateCount_ne
    (depth prefixLength : ℕ) (prefix_lt : prefixLength < 2 * depth + 4) :
    ((pumpWord depth ++
          [Letter.dilate, Letter.translate, Letter.dilate, Letter.dilate]).take
        prefixLength).count .dilate ≠
      ((pumpWord depth ++
          [Letter.dilate, Letter.dilate, Letter.translate, Letter.translate]).take
        prefixLength).count .dilate + 1 := by
  by_cases prefix_within : prefixLength ≤ 2 * depth
  · have prefix_within_pump : prefixLength ≤ (pumpWord depth).length := by
      simpa only [pumpWord_length] using prefix_within
    rw [List.take_append_of_le_length prefix_within_pump,
      List.take_append_of_le_length prefix_within_pump]
    omega
  · let tailLength := prefixLength - 2 * depth
    have tail_pos : 0 < tailLength := by
      simp only [tailLength]
      omega
    have tail_le : tailLength ≤ 3 := by
      simp only [tailLength]
      omega
    have prefix_eq : prefixLength = 2 * depth + tailLength := by
      simp only [tailLength]
      omega
    rw [prefix_eq]
    simp only [List.take_append, pumpWord_length, Nat.add_sub_cancel_left,
      List.count_append]
    interval_cases tailLength <;>
      simp

/-- The unique positive proper prefix with equal dilation count in an odd-family relation is the
three-letter prefix. -/
theorem kernelOddFamily_prefix_dilateCount_eq
    (depth prefixLength : ℕ) (prefix_pos : 0 < prefixLength)
    (prefix_lt : prefixLength < 29 + 2 * depth)
    (counts_eq :
      ((kernelOddFamilyLeft depth).take prefixLength).count .dilate =
        ((kernelOddFamilyRight depth).take prefixLength).count .dilate) :
    prefixLength = 3 := by
  have factorization := kernelOddFamily_headPump_factorization depth
  have left_grouped :
      kernelOddFamilyLeft depth = oddFamilyLeftHead ++
        (pumpWord depth ++ [Letter.dilate, Letter.translate, Letter.dilate, Letter.dilate]) := by
    simpa only [List.append_assoc] using factorization.1
  have right_grouped :
      kernelOddFamilyRight depth = oddFamilyRightHead ++
        (pumpWord depth ++ [Letter.dilate, Letter.dilate, Letter.translate, Letter.translate]) := by
    simpa only [List.append_assoc] using factorization.2
  by_cases prefix_le : prefixLength ≤ 25
  · have left_prefix_le : prefixLength ≤ oddFamilyLeftHead.length := by
      simpa only [oddFamilyLeftHead_length] using prefix_le
    have right_prefix_le : prefixLength ≤ oddFamilyRightHead.length := by
      simpa only [oddFamilyRightHead_length] using prefix_le
    rw [left_grouped, right_grouped,
      List.take_append_of_le_length left_prefix_le,
      List.take_append_of_le_length right_prefix_le] at counts_eq
    exact oddFamilyHead_prefix_dilateCount_eq prefixLength prefix_pos prefix_le counts_eq
  · have heads_le :
        oddFamilyLeftHead.length ≤ prefixLength ∧
          oddFamilyRightHead.length ≤ prefixLength := by
      simp only [oddFamilyLeftHead_length, oddFamilyRightHead_length]
      omega
    have tailPrefix_lt : prefixLength - 25 < 2 * depth + 4 := by omega
    have left_take :
        (oddFamilyLeftHead ++
            (pumpWord depth ++
              [Letter.dilate, Letter.translate, Letter.dilate, Letter.dilate])).take
          prefixLength =
        oddFamilyLeftHead ++
          (pumpWord depth ++
              [Letter.dilate, Letter.translate, Letter.dilate, Letter.dilate]).take
            (prefixLength - 25) := by
      calc
        _ = oddFamilyLeftHead.take prefixLength ++
              (pumpWord depth ++
                  [Letter.dilate, Letter.translate, Letter.dilate, Letter.dilate]).take
                (prefixLength - oddFamilyLeftHead.length) := List.take_append
        _ = _ := by
          rw [(List.take_eq_self_iff oddFamilyLeftHead).2 heads_le.1,
            oddFamilyLeftHead_length]
    have right_take :
        (oddFamilyRightHead ++
            (pumpWord depth ++
              [Letter.dilate, Letter.dilate, Letter.translate, Letter.translate])).take
          prefixLength =
        oddFamilyRightHead ++
          (pumpWord depth ++
              [Letter.dilate, Letter.dilate, Letter.translate, Letter.translate]).take
            (prefixLength - 25) := by
      calc
        _ = oddFamilyRightHead.take prefixLength ++
              (pumpWord depth ++
                  [Letter.dilate, Letter.dilate, Letter.translate, Letter.translate]).take
                (prefixLength - oddFamilyRightHead.length) := List.take_append
        _ = _ := by
          rw [(List.take_eq_self_iff oddFamilyRightHead).2 heads_le.2,
            oddFamilyRightHead_length]
    rw [left_grouped, right_grouped, left_take, right_take] at counts_eq
    simp only [List.count_append] at counts_eq
    have tail_counts :
        ((pumpWord depth ++
              [Letter.dilate, Letter.translate, Letter.dilate, Letter.dilate]).take
            (prefixLength - 25)).count .dilate =
          ((pumpWord depth ++
              [Letter.dilate, Letter.dilate, Letter.translate, Letter.translate]).take
            (prefixLength - 25)).count .dilate + 1 := by
      have head_gap := oddFamilyHead_dilateCount_gap
      omega
    exact False.elim <|
      oddFamilyPump_prefix_dilateCount_ne depth (prefixLength - 25) tailPrefix_lt tail_counts

/-- Both sides of an odd-family relation have the same total dilation count. -/
theorem kernelOddFamily_dilateCount_eq (depth : ℕ) :
    (kernelOddFamilyLeft depth).count .dilate =
      (kernelOddFamilyRight depth).count .dilate := by
  have counts := kernelOddFamily_count depth
  exact counts.1.trans counts.2.2.1.symm

/-- The unique positive proper suffix with equal dilation count in an odd-family relation has
length three less than the relation. -/
theorem kernelOddFamily_suffix_dilateCount_eq
    (depth suffixLength : ℕ) (suffix_pos : 0 < suffixLength)
    (suffix_lt : suffixLength < 29 + 2 * depth)
    (counts_eq :
      ((kernelOddFamilyLeft depth).drop (29 + 2 * depth - suffixLength)).count .dilate =
        ((kernelOddFamilyRight depth).drop (29 + 2 * depth - suffixLength)).count .dilate) :
    suffixLength = 29 + 2 * depth - 3 := by
  let prefixLength := 29 + 2 * depth - suffixLength
  have prefix_pos : 0 < prefixLength := by
    simp only [prefixLength]
    omega
  have prefix_lt : prefixLength < 29 + 2 * depth := by
    simp only [prefixLength]
    omega
  have left_split := congrArg (List.count Letter.dilate)
    (List.take_append_drop prefixLength (kernelOddFamilyLeft depth))
  have right_split := congrArg (List.count Letter.dilate)
    (List.take_append_drop prefixLength (kernelOddFamilyRight depth))
  simp only [List.count_append] at left_split right_split
  have prefix_counts :
      ((kernelOddFamilyLeft depth).take prefixLength).count .dilate =
        ((kernelOddFamilyRight depth).take prefixLength).count .dilate := by
    have total_counts := kernelOddFamily_dilateCount_eq depth
    change
      ((kernelOddFamilyLeft depth).drop prefixLength).count .dilate =
        ((kernelOddFamilyRight depth).drop prefixLength).count .dilate at counts_eq
    omega
  have prefix_eq := kernelOddFamily_prefix_dilateCount_eq
    depth prefixLength prefix_pos prefix_lt prefix_counts
  simp only [prefixLength] at prefix_eq
  omega

/-- The letters immediately after the unique balanced prefix cut disagree. -/
theorem kernelOddFamily_after_balancedPrefix_ne (depth : ℕ) :
    ((kernelOddFamilyLeft depth).drop 3).head? ≠
      ((kernelOddFamilyRight depth).drop 3).head? := by
  have translate_ne : Letter.translate ≠ Letter.dilate := by decide
  norm_num [kernelOddFamilyLeft, kernelOddFamilyRight, List.replicate_succ, translate_ne]

/-- The length-two blocks beginning one letter into the relation disagree. -/
theorem kernelOddFamily_one_two_block_ne (depth : ℕ) :
    ((kernelOddFamilyLeft depth).drop 1).take 2 ≠
      ((kernelOddFamilyRight depth).drop 1).take 2 := by
  have translate_ne : Letter.translate ≠ Letter.dilate := by decide
  norm_num [kernelOddFamilyLeft, kernelOddFamilyRight, List.replicate_succ, translate_ne]

/-- The one-letter blocks beginning two letters into the relation disagree. -/
theorem kernelOddFamily_two_one_block_ne (depth : ℕ) :
    ((kernelOddFamilyLeft depth).drop 2).take 1 ≠
      ((kernelOddFamilyRight depth).drop 2).take 1 := by
  have translate_ne : Letter.translate ≠ Letter.dilate := by decide
  norm_num [kernelOddFamilyLeft, kernelOddFamilyRight, List.replicate_succ, translate_ne]

/-- An internal/internal contextual placement is arithmetically impossible once its balanced
prefix cut has been extracted from the literal fork words. -/
theorem no_kernelOddFamily_internal_internal_cut
    (depth xLength yLength zLength contextPrefixLength : ℕ)
    (x_pos : 0 < xLength) (z_pos : 0 < zLength)
    (prefix_internal_x : contextPrefixLength < xLength)
    (prefix_internal_y : contextPrefixLength < yLength)
    (core_le_fork : 29 + 2 * depth ≤ 2 * xLength + 2 * yLength + zLength)
    (cut_lt : xLength + yLength + zLength - contextPrefixLength < 29 + 2 * depth)
    (counts_eq :
      ((kernelOddFamilyLeft depth).take
          (xLength + yLength + zLength - contextPrefixLength)).count .dilate =
        ((kernelOddFamilyRight depth).take
          (xLength + yLength + zLength - contextPrefixLength)).count .dilate) : False := by
  have cut_pos : 0 < xLength + yLength + zLength - contextPrefixLength := by omega
  have cut_eq := kernelOddFamily_prefix_dilateCount_eq depth
    (xLength + yLength + zLength - contextPrefixLength) cut_pos cut_lt counts_eq
  omega

/-- An internal-prefix/comparable-suffix placement is impossible off its full-suffix
centralizer exit: the first aligned letter would cross the unique balanced prefix cut. -/
theorem no_kernelOddFamily_internalPrefix_comparableSuffix_cut
    (depth cutLength : ℕ) (cut_pos : 0 < cutLength)
    (cut_lt : cutLength < 29 + 2 * depth)
    (counts_eq :
      ((kernelOddFamilyLeft depth).take cutLength).count .dilate =
        ((kernelOddFamilyRight depth).take cutLength).count .dilate)
    (aligned_next :
      ((kernelOddFamilyLeft depth).drop cutLength).head? =
        ((kernelOddFamilyRight depth).drop cutLength).head?) : False := by
  have cut_eq := kernelOddFamily_prefix_dilateCount_eq
    depth cutLength cut_pos cut_lt counts_eq
  rw [cut_eq] at aligned_next
  exact kernelOddFamily_after_balancedPrefix_ne depth aligned_next

/-- The preceding cut obstruction is invariant under reversing the relation orientation. -/
theorem no_kernelOddFamily_internalPrefix_comparableSuffix_cut_reverse
    (depth cutLength : ℕ) (cut_pos : 0 < cutLength)
    (cut_lt : cutLength < 29 + 2 * depth)
    (counts_eq :
      ((kernelOddFamilyRight depth).take cutLength).count .dilate =
        ((kernelOddFamilyLeft depth).take cutLength).count .dilate)
    (aligned_next :
      ((kernelOddFamilyRight depth).drop cutLength).head? =
        ((kernelOddFamilyLeft depth).drop cutLength).head?) : False := by
  exact no_kernelOddFamily_internalPrefix_comparableSuffix_cut
    depth cutLength cut_pos cut_lt counts_eq.symm aligned_next.symm

/-- A comparable-prefix/internal-suffix placement is impossible off its full-prefix centralizer
exit: suffix balance leaves only the two short blocks which visibly disagree. -/
theorem no_kernelOddFamily_comparablePrefix_internalSuffix_cut
    (depth prefixRemainder shortLength suffixLength : ℕ)
    (prefixRemainder_pos : 0 < prefixRemainder) (short_pos : 0 < shortLength)
    (suffix_pos : 0 < suffixLength) (suffix_lt : suffixLength < 29 + 2 * depth)
    (core_decomposition :
      29 + 2 * depth = prefixRemainder + shortLength + suffixLength)
    (suffix_counts_eq :
      ((kernelOddFamilyLeft depth).drop (29 + 2 * depth - suffixLength)).count .dilate =
        ((kernelOddFamilyRight depth).drop
          (29 + 2 * depth - suffixLength)).count .dilate)
    (aligned_short :
      ((kernelOddFamilyLeft depth).drop prefixRemainder).take shortLength =
        ((kernelOddFamilyRight depth).drop prefixRemainder).take shortLength) : False := by
  have suffix_eq := kernelOddFamily_suffix_dilateCount_eq
    depth suffixLength suffix_pos suffix_lt suffix_counts_eq
  have short_sum : prefixRemainder + shortLength = 3 := by omega
  have short_cases :
      (prefixRemainder = 1 ∧ shortLength = 2) ∨
        (prefixRemainder = 2 ∧ shortLength = 1) := by
    omega
  rcases short_cases with first_case | second_case
  · rw [first_case.1, first_case.2] at aligned_short
    exact kernelOddFamily_one_two_block_ne depth aligned_short
  · rw [second_case.1, second_case.2] at aligned_short
    exact kernelOddFamily_two_one_block_ne depth aligned_short

/-- The preceding suffix obstruction is invariant under reversing the relation orientation. -/
theorem no_kernelOddFamily_comparablePrefix_internalSuffix_cut_reverse
    (depth prefixRemainder shortLength suffixLength : ℕ)
    (prefixRemainder_pos : 0 < prefixRemainder) (short_pos : 0 < shortLength)
    (suffix_pos : 0 < suffixLength) (suffix_lt : suffixLength < 29 + 2 * depth)
    (core_decomposition :
      29 + 2 * depth = prefixRemainder + shortLength + suffixLength)
    (suffix_counts_eq :
      ((kernelOddFamilyRight depth).drop (29 + 2 * depth - suffixLength)).count .dilate =
        ((kernelOddFamilyLeft depth).drop
          (29 + 2 * depth - suffixLength)).count .dilate)
    (aligned_short :
      ((kernelOddFamilyRight depth).drop prefixRemainder).take shortLength =
        ((kernelOddFamilyLeft depth).drop prefixRemainder).take shortLength) : False := by
  exact no_kernelOddFamily_comparablePrefix_internalSuffix_cut
    depth prefixRemainder shortLength suffixLength prefixRemainder_pos short_pos
    suffix_pos suffix_lt core_decomposition suffix_counts_eq.symm aligned_short.symm

/-- A same-shorter placement is impossible off both full centralizer exits: its Parikh-balanced
tail forces the aligned square to be the unequal blocks `TT` and `TD`. -/
theorem no_kernelOddFamily_sameShorter_cut
    (depth prefixRemainder shortLength suffixLength : ℕ)
    (prefixRemainder_pos : 0 < prefixRemainder) (short_pos : 0 < shortLength)
    (suffix_pos : 0 < suffixLength) (suffix_lt : suffixLength < 29 + 2 * depth)
    (core_decomposition :
      29 + 2 * depth = prefixRemainder + 2 * shortLength + suffixLength)
    (suffix_counts_eq :
      ((kernelOddFamilyLeft depth).drop (29 + 2 * depth - suffixLength)).count .dilate =
        ((kernelOddFamilyRight depth).drop
          (29 + 2 * depth - suffixLength)).count .dilate)
    (aligned_square :
      ((kernelOddFamilyLeft depth).drop prefixRemainder).take (2 * shortLength) =
        ((kernelOddFamilyRight depth).drop prefixRemainder).take (2 * shortLength)) : False := by
  have suffix_eq := kernelOddFamily_suffix_dilateCount_eq
    depth suffixLength suffix_pos suffix_lt suffix_counts_eq
  have remainder_eq : prefixRemainder = 1 := by omega
  have short_eq : shortLength = 1 := by omega
  rw [remainder_eq, short_eq] at aligned_square
  exact kernelOddFamily_one_two_block_ne depth (by simpa using aligned_square)

/-- The same-shorter obstruction is invariant under reversing the relation orientation. -/
theorem no_kernelOddFamily_sameShorter_cut_reverse
    (depth prefixRemainder shortLength suffixLength : ℕ)
    (prefixRemainder_pos : 0 < prefixRemainder) (short_pos : 0 < shortLength)
    (suffix_pos : 0 < suffixLength) (suffix_lt : suffixLength < 29 + 2 * depth)
    (core_decomposition :
      29 + 2 * depth = prefixRemainder + 2 * shortLength + suffixLength)
    (suffix_counts_eq :
      ((kernelOddFamilyRight depth).drop (29 + 2 * depth - suffixLength)).count .dilate =
        ((kernelOddFamilyLeft depth).drop
          (29 + 2 * depth - suffixLength)).count .dilate)
    (aligned_square :
      ((kernelOddFamilyRight depth).drop prefixRemainder).take (2 * shortLength) =
        ((kernelOddFamilyLeft depth).drop prefixRemainder).take (2 * shortLength)) : False := by
  exact no_kernelOddFamily_sameShorter_cut
    depth prefixRemainder shortLength suffixLength prefixRemainder_pos short_pos
    suffix_pos suffix_lt core_decomposition suffix_counts_eq.symm aligned_square.symm

/-- The exact finite interface between the audited contextual-word decomposition and the formal
Parikh obstruction. Its constructors are the seven unequal-length, off-centralizer cells in the
`3 × 3` prefix/suffix partition. -/
inductive OddFamilyOffCentralizerCutCertificate (depth : ℕ) : Prop
  | internalInternal
      (xLength yLength zLength contextPrefixLength : ℕ)
      (x_pos : 0 < xLength) (z_pos : 0 < zLength)
      (prefix_internal_x : contextPrefixLength < xLength)
      (prefix_internal_y : contextPrefixLength < yLength)
      (core_le_fork : 29 + 2 * depth ≤ 2 * xLength + 2 * yLength + zLength)
      (cut_lt : xLength + yLength + zLength - contextPrefixLength < 29 + 2 * depth)
      (counts_eq :
        ((kernelOddFamilyLeft depth).take
            (xLength + yLength + zLength - contextPrefixLength)).count .dilate =
          ((kernelOddFamilyRight depth).take
            (xLength + yLength + zLength - contextPrefixLength)).count .dilate)
  | internalPrefixComparableSuffix
      (cutLength : ℕ) (cut_pos : 0 < cutLength) (cut_lt : cutLength < 29 + 2 * depth)
      (counts_eq :
        ((kernelOddFamilyLeft depth).take cutLength).count .dilate =
          ((kernelOddFamilyRight depth).take cutLength).count .dilate)
      (aligned_next :
        ((kernelOddFamilyLeft depth).drop cutLength).head? =
          ((kernelOddFamilyRight depth).drop cutLength).head?)
  | internalPrefixComparableSuffixReverse
      (cutLength : ℕ) (cut_pos : 0 < cutLength) (cut_lt : cutLength < 29 + 2 * depth)
      (counts_eq :
        ((kernelOddFamilyRight depth).take cutLength).count .dilate =
          ((kernelOddFamilyLeft depth).take cutLength).count .dilate)
      (aligned_next :
        ((kernelOddFamilyRight depth).drop cutLength).head? =
          ((kernelOddFamilyLeft depth).drop cutLength).head?)
  | comparablePrefixInternalSuffix
      (prefixRemainder shortLength suffixLength : ℕ)
      (prefixRemainder_pos : 0 < prefixRemainder) (short_pos : 0 < shortLength)
      (suffix_pos : 0 < suffixLength) (suffix_lt : suffixLength < 29 + 2 * depth)
      (core_decomposition :
        29 + 2 * depth = prefixRemainder + shortLength + suffixLength)
      (suffix_counts_eq :
        ((kernelOddFamilyLeft depth).drop
            (29 + 2 * depth - suffixLength)).count .dilate =
          ((kernelOddFamilyRight depth).drop
            (29 + 2 * depth - suffixLength)).count .dilate)
      (aligned_short :
        ((kernelOddFamilyLeft depth).drop prefixRemainder).take shortLength =
          ((kernelOddFamilyRight depth).drop prefixRemainder).take shortLength)
  | comparablePrefixInternalSuffixReverse
      (prefixRemainder shortLength suffixLength : ℕ)
      (prefixRemainder_pos : 0 < prefixRemainder) (short_pos : 0 < shortLength)
      (suffix_pos : 0 < suffixLength) (suffix_lt : suffixLength < 29 + 2 * depth)
      (core_decomposition :
        29 + 2 * depth = prefixRemainder + shortLength + suffixLength)
      (suffix_counts_eq :
        ((kernelOddFamilyRight depth).drop
            (29 + 2 * depth - suffixLength)).count .dilate =
          ((kernelOddFamilyLeft depth).drop
            (29 + 2 * depth - suffixLength)).count .dilate)
      (aligned_short :
        ((kernelOddFamilyRight depth).drop prefixRemainder).take shortLength =
          ((kernelOddFamilyLeft depth).drop prefixRemainder).take shortLength)
  | sameShorter
      (prefixRemainder shortLength suffixLength : ℕ)
      (prefixRemainder_pos : 0 < prefixRemainder) (short_pos : 0 < shortLength)
      (suffix_pos : 0 < suffixLength) (suffix_lt : suffixLength < 29 + 2 * depth)
      (core_decomposition :
        29 + 2 * depth = prefixRemainder + 2 * shortLength + suffixLength)
      (suffix_counts_eq :
        ((kernelOddFamilyLeft depth).drop
            (29 + 2 * depth - suffixLength)).count .dilate =
          ((kernelOddFamilyRight depth).drop
            (29 + 2 * depth - suffixLength)).count .dilate)
      (aligned_square :
        ((kernelOddFamilyLeft depth).drop prefixRemainder).take (2 * shortLength) =
          ((kernelOddFamilyRight depth).drop prefixRemainder).take (2 * shortLength))
  | sameShorterReverse
      (prefixRemainder shortLength suffixLength : ℕ)
      (prefixRemainder_pos : 0 < prefixRemainder) (short_pos : 0 < shortLength)
      (suffix_pos : 0 < suffixLength) (suffix_lt : suffixLength < 29 + 2 * depth)
      (core_decomposition :
        29 + 2 * depth = prefixRemainder + 2 * shortLength + suffixLength)
      (suffix_counts_eq :
        ((kernelOddFamilyRight depth).drop
            (29 + 2 * depth - suffixLength)).count .dilate =
          ((kernelOddFamilyLeft depth).drop
            (29 + 2 * depth - suffixLength)).count .dilate)
      (aligned_square :
        ((kernelOddFamilyRight depth).drop prefixRemainder).take (2 * shortLength) =
          ((kernelOddFamilyLeft depth).drop prefixRemainder).take (2 * shortLength))

/-- No unequal-length odd-family contextual fork survives outside the full centralizer exits once
the audited literal decomposition supplies its cut certificate. -/
theorem no_kernelOddFamily_offCentralizer_cutCertificate (depth : ℕ) :
    ¬OddFamilyOffCentralizerCutCertificate depth := by
  intro certificate
  cases certificate with
  | internalInternal xLength yLength zLength contextPrefixLength x_pos z_pos
      prefix_internal_x prefix_internal_y core_le_fork cut_lt counts_eq =>
      exact no_kernelOddFamily_internal_internal_cut depth xLength yLength zLength
        contextPrefixLength x_pos z_pos prefix_internal_x prefix_internal_y core_le_fork
        cut_lt counts_eq
  | internalPrefixComparableSuffix cutLength cut_pos cut_lt counts_eq aligned_next =>
      exact no_kernelOddFamily_internalPrefix_comparableSuffix_cut
        depth cutLength cut_pos cut_lt counts_eq aligned_next
  | internalPrefixComparableSuffixReverse cutLength cut_pos cut_lt counts_eq aligned_next =>
      exact no_kernelOddFamily_internalPrefix_comparableSuffix_cut_reverse
        depth cutLength cut_pos cut_lt counts_eq aligned_next
  | comparablePrefixInternalSuffix prefixRemainder shortLength suffixLength
      prefixRemainder_pos short_pos suffix_pos suffix_lt core_decomposition
      suffix_counts_eq aligned_short =>
      exact no_kernelOddFamily_comparablePrefix_internalSuffix_cut depth prefixRemainder
        shortLength suffixLength prefixRemainder_pos short_pos suffix_pos suffix_lt
        core_decomposition suffix_counts_eq aligned_short
  | comparablePrefixInternalSuffixReverse prefixRemainder shortLength suffixLength
      prefixRemainder_pos short_pos suffix_pos suffix_lt core_decomposition
      suffix_counts_eq aligned_short =>
      exact no_kernelOddFamily_comparablePrefix_internalSuffix_cut_reverse depth prefixRemainder
        shortLength suffixLength prefixRemainder_pos short_pos suffix_pos suffix_lt
        core_decomposition suffix_counts_eq aligned_short
  | sameShorter prefixRemainder shortLength suffixLength prefixRemainder_pos short_pos
      suffix_pos suffix_lt core_decomposition suffix_counts_eq aligned_square =>
      exact no_kernelOddFamily_sameShorter_cut depth prefixRemainder shortLength suffixLength
        prefixRemainder_pos short_pos suffix_pos suffix_lt core_decomposition suffix_counts_eq
        aligned_square
  | sameShorterReverse prefixRemainder shortLength suffixLength prefixRemainder_pos short_pos
      suffix_pos suffix_lt core_decomposition suffix_counts_eq aligned_square =>
      exact no_kernelOddFamily_sameShorter_cut_reverse depth prefixRemainder shortLength
        suffixLength prefixRemainder_pos short_pos suffix_pos suffix_lt core_decomposition
        suffix_counts_eq aligned_square

end MatrixMortality.GuardedMixedPrimeFork
