import MatrixMortality.MixedPrimeOddFamilyCloakNoGo
import MatrixMortality.PadicValuation

/-!
# Single-cut collapse for mixed-prime address interleaving

Inserting the free `{DT,TD}` address at one fixed cut does not create a new uniform comparator
geometry. Equality for the empty address and the two one-digit addresses already forces the
prefix pieces to have one affine action and the suffix pieces to have one affine action. Thus a
nontrivial uniformly interleaved cloak contains a genuine kernel pair on at least one side of the
address cut.
-/

set_option autoImplicit false

namespace MatrixMortality.MixedPrimeAddressInterleavingCollapse

open GuardedMixedPrimeFork
open GuardedMixedPrimeBridge
open BranchingHistory
open MixedPrimeKernel
open MixedPrimeMacroAddress

/-- A mixed-prime word slope is one common translation scale per letter times one `10/9` ratio
per dilation. -/
theorem wordScale_eq_length_mul_dilateCount (word : List Letter) :
    wordScale word =
      (3 / 5 : ℚ) ^ word.length * (10 / 9 : ℚ) ^ word.count .dilate := by
  induction word with
  | nil => norm_num [wordScale]
  | cons letter tail induction =>
      rw [show wordScale (letter :: tail) = actionScale letter * wordScale tail by
        simp [wordScale], induction]
      cases letter <;> simp [actionScale, pow_succ] <;> ring

/-- The two-adic valuation of a mixed-prime slope is its dilation count. -/
theorem padicValRat_two_wordScale (word : List Letter) :
    padicValRat 2 (wordScale word) = (word.count .dilate : ℤ) := by
  have three_value : padicValRat 2 (3 : ℚ) = 0 := by
    norm_num [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd]
  have five_value : padicValRat 2 (5 : ℚ) = 0 := by
    norm_num [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd]
  have ten_value : padicValRat 2 (10 : ℚ) = 1 := by
    have two_value : padicValRat 2 (2 : ℚ) = 1 :=
      padicValRat.self (p := 2) (by norm_num)
    rw [show (10 : ℚ) = 2 * 5 by norm_num,
      padicValRat.mul (p := 2) (by norm_num) (by norm_num), two_value, five_value]
    norm_num
  have nine_value : padicValRat 2 (9 : ℚ) = 0 := by
    norm_num [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd]
  rw [wordScale_eq_length_mul_dilateCount,
    padicValRat.mul (by positivity) (by positivity), padicValRat.pow, padicValRat.pow]
  rw [padicValRat.div (by norm_num) (by norm_num),
    padicValRat.div (by norm_num) (by norm_num),
    three_value, five_value, ten_value, nine_value]
  omega

/-- The five-adic valuation of a mixed-prime slope is dilation count minus total length. -/
theorem padicValRat_five_wordScale (word : List Letter) :
    padicValRat 5 (wordScale word) =
      (word.count .dilate : ℤ) - word.length := by
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have three_value : padicValRat 5 (3 : ℚ) = 0 := by
    norm_num [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd]
  have five_value : padicValRat 5 (5 : ℚ) = 1 := by
    norm_num [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd,
      padicValNat.self]
  have ten_value : padicValRat 5 (10 : ℚ) = 1 := by
    have two_value : padicValRat 5 (2 : ℚ) = 0 := by
      norm_num [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd]
    rw [show (10 : ℚ) = 2 * 5 by norm_num,
      padicValRat.mul (p := 5) (by norm_num) (by norm_num), two_value, five_value]
    norm_num
  have nine_value : padicValRat 5 (9 : ℚ) = 0 := by
    norm_num [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd]
  rw [wordScale_eq_length_mul_dilateCount,
    padicValRat.mul (by positivity) (by positivity), padicValRat.pow, padicValRat.pow]
  rw [padicValRat.div (by norm_num) (by norm_num),
    padicValRat.div (by norm_num) (by norm_num),
    three_value, five_value, ten_value, nine_value]
  omega

/-- Equal mixed-prime slopes force equal raw lengths and equal Parikh vectors. -/
theorem length_eq_and_dilateCount_eq_of_wordScale_eq
    (left right : List Letter) (scales_eq : wordScale left = wordScale right) :
    left.length = right.length ∧ left.count .dilate = right.count .dilate := by
  have two_values_eq := congrArg (padicValRat 2) scales_eq
  rw [padicValRat_two_wordScale, padicValRat_two_wordScale] at two_values_eq
  have counts_eq : left.count .dilate = right.count .dilate := by
    exact_mod_cast two_values_eq
  have five_values_eq := congrArg (padicValRat 5) scales_eq
  rw [padicValRat_five_wordScale, padicValRat_five_wordScale] at five_values_eq
  have lengths_eq : left.length = right.length := by
    rw [counts_eq] at five_values_eq
    omega
  exact ⟨lengths_eq, counts_eq⟩

/-- Equality of two complete mixed-prime affine actions forces equality of their slopes. -/
theorem wordScale_eq_of_wordActions_eq
    (left right : List Letter)
    (actions_eq : ∀ state : ℚ, wordAction left state = wordAction right state) :
    wordScale left = wordScale right := by
  have at_one := actions_eq 1
  have at_zero := actions_eq 0
  linarith [wordAction_sub left 1 0, wordAction_sub right 1 0]

/-- The empty address and the two one-digit addresses force a single-cut interleaving to split
into equal-action prefix and suffix pairs. -/
theorem piecewise_actions_eq_of_empty_false_true
    (leftPrefix rightPrefix leftSuffix rightSuffix : List Letter)
    (empty_actions_eq : ∀ state : ℚ,
      wordAction (leftPrefix ++ leftSuffix) state =
        wordAction (rightPrefix ++ rightSuffix) state)
    (false_actions_eq : ∀ state : ℚ,
      wordAction (leftPrefix ++ addressMacro false ++ leftSuffix) state =
        wordAction (rightPrefix ++ addressMacro false ++ rightSuffix) state)
    (true_actions_eq : ∀ state : ℚ,
      wordAction (leftPrefix ++ addressMacro true ++ leftSuffix) state =
        wordAction (rightPrefix ++ addressMacro true ++ rightSuffix) state) :
    (∀ state : ℚ, wordAction leftPrefix state = wordAction rightPrefix state) ∧
      (∀ state : ℚ, wordAction leftSuffix state = wordAction rightSuffix state) := by
  have false_at_zero := false_actions_eq 0
  have true_at_zero := true_actions_eq 0
  simp only [List.append_assoc, wordAction_append, wordAction_addressMacro] at false_at_zero
  simp only [List.append_assoc, wordAction_append, wordAction_addressMacro] at true_at_zero
  have prefix_difference :
      wordAction leftPrefix
            (2 / 5 * wordAction leftSuffix 0 + addressDigit false / 3) -
          wordAction leftPrefix
            (2 / 5 * wordAction leftSuffix 0 + addressDigit true / 3) =
        wordAction rightPrefix
            (2 / 5 * wordAction rightSuffix 0 + addressDigit false / 3) -
          wordAction rightPrefix
            (2 / 5 * wordAction rightSuffix 0 + addressDigit true / 3) := by
    rw [false_at_zero, true_at_zero]
  rw [wordAction_sub, wordAction_sub] at prefix_difference
  have prefix_scales_eq : wordScale leftPrefix = wordScale rightPrefix := by
    norm_num [addressDigit] at prefix_difference
    linarith
  have suffix_actions_eq : ∀ state : ℚ,
      wordAction leftSuffix state = wordAction rightSuffix state := by
    intro state
    have empty_at_state := empty_actions_eq state
    have false_at_state := false_actions_eq state
    simp only [wordAction_append] at empty_at_state
    simp only [List.append_assoc, wordAction_append, wordAction_addressMacro] at false_at_state
    have scaled_difference :
        wordAction leftPrefix
              (2 / 5 * wordAction leftSuffix state + addressDigit false / 3) -
            wordAction leftPrefix (wordAction leftSuffix state) =
          wordAction rightPrefix
              (2 / 5 * wordAction rightSuffix state + addressDigit false / 3) -
            wordAction rightPrefix (wordAction rightSuffix state) := by
      rw [false_at_state, empty_at_state]
    rw [wordAction_sub, wordAction_sub, prefix_scales_eq] at scaled_difference
    have prefix_scale_pos := wordScale_pos rightPrefix
    norm_num [addressDigit] at scaled_difference
    rcases scaled_difference with values_eq | prefix_scale_zero
    · linarith
    · exact False.elim (ne_of_gt prefix_scale_pos prefix_scale_zero)
  have prefix_actions_eq : ∀ state : ℚ,
      wordAction leftPrefix state = wordAction rightPrefix state := by
    intro state
    obtain ⟨source, source_eq⟩ := wordAction_surjective leftSuffix state
    calc
      wordAction leftPrefix state =
          wordAction leftPrefix (wordAction leftSuffix source) := by rw [source_eq]
      _ = wordAction rightPrefix (wordAction rightSuffix source) := by
        simpa only [wordAction_append] using empty_actions_eq source
      _ = wordAction rightPrefix (wordAction leftSuffix source) := by
        rw [suffix_actions_eq source]
      _ = wordAction rightPrefix state := by rw [source_eq]
  exact ⟨prefix_actions_eq, suffix_actions_eq⟩

/-- Uniform equal-address action equality at one fixed cut is already determined by three
addresses and forces the two sides of the cut to be kernel pairs separately. -/
theorem interleavedAddress_piecewise_actions_eq
    (leftPrefix rightPrefix leftSuffix rightSuffix : List Letter)
    (same_address_actions_eq : ∀ address state,
      wordAction (leftPrefix ++ expandAddress address ++ leftSuffix) state =
        wordAction (rightPrefix ++ expandAddress address ++ rightSuffix) state) :
    (∀ state : ℚ, wordAction leftPrefix state = wordAction rightPrefix state) ∧
      (∀ state : ℚ, wordAction leftSuffix state = wordAction rightSuffix state) := by
  apply piecewise_actions_eq_of_empty_false_true
  · intro state
    simpa [expandAddress] using same_address_actions_eq [] state
  · intro state
    simpa [expandAddress] using same_address_actions_eq [false] state
  · intro state
    simpa [expandAddress] using same_address_actions_eq [true] state

/-- No positive proper cut of the odd kernel relation has equal-action prefixes. The unique
Parikh-balanced cut is at length three, where direct evaluation separates the affine offsets. -/
theorem kernelOddFamily_no_proper_prefix_actions_eq
    (depth cut : ℕ) (cut_pos : 0 < cut) (cut_lt : cut < 29 + 2 * depth) :
    ¬ ∀ state : ℚ,
      wordAction ((kernelOddFamilyLeft depth).take cut) state =
        wordAction ((kernelOddFamilyRight depth).take cut) state := by
  intro prefix_actions_eq
  have relation_lengths := kernelOddFamily_length depth
  have prefix_scales_eq := wordScale_eq_of_wordActions_eq
    ((kernelOddFamilyLeft depth).take cut) ((kernelOddFamilyRight depth).take cut)
      prefix_actions_eq
  have prefix_counts_eq := (length_eq_and_dilateCount_eq_of_wordScale_eq
    ((kernelOddFamilyLeft depth).take cut) ((kernelOddFamilyRight depth).take cut)
      prefix_scales_eq).2
  have cut_eq_three := kernelOddFamily_prefix_dilateCount_eq
    depth cut cut_pos cut_lt prefix_counts_eq
  subst cut
  have at_zero := prefix_actions_eq 0
  norm_num [kernelOddFamilyLeft, kernelOddFamilyRight, wordAction, action,
    List.replicate_succ] at at_zero

private theorem kernelOddFamily_cuts_eq_boundary_of_sameAddressActions
    (depth leftCut rightCut : ℕ)
    (leftCut_le : leftCut ≤ 29 + 2 * depth)
    (rightCut_le : rightCut ≤ 29 + 2 * depth)
    (same_address_actions_eq : ∀ address state,
      wordAction
            ((kernelOddFamilyLeft depth).take leftCut ++ expandAddress address ++
              (kernelOddFamilyLeft depth).drop leftCut) state =
        wordAction
            ((kernelOddFamilyRight depth).take rightCut ++ expandAddress address ++
              (kernelOddFamilyRight depth).drop rightCut) state) :
    leftCut = rightCut ∧
      (leftCut = 0 ∨ leftCut = 29 + 2 * depth) := by
  have piecewise := interleavedAddress_piecewise_actions_eq
    ((kernelOddFamilyLeft depth).take leftCut)
      ((kernelOddFamilyRight depth).take rightCut)
      ((kernelOddFamilyLeft depth).drop leftCut)
      ((kernelOddFamilyRight depth).drop rightCut) same_address_actions_eq
  have prefix_scales_eq := wordScale_eq_of_wordActions_eq
    ((kernelOddFamilyLeft depth).take leftCut)
      ((kernelOddFamilyRight depth).take rightCut) piecewise.1
  have prefix_lengths_eq :=
    (length_eq_and_dilateCount_eq_of_wordScale_eq
      ((kernelOddFamilyLeft depth).take leftCut)
        ((kernelOddFamilyRight depth).take rightCut) prefix_scales_eq).1
  have relation_lengths := kernelOddFamily_length depth
  have left_take_length :
      ((kernelOddFamilyLeft depth).take leftCut).length = leftCut := by
    simp only [List.length_take, relation_lengths.1]
    omega
  have right_take_length :
      ((kernelOddFamilyRight depth).take rightCut).length = rightCut := by
    simp only [List.length_take, relation_lengths.2]
    omega
  have cuts_eq : leftCut = rightCut := by
    rw [left_take_length, right_take_length] at prefix_lengths_eq
    exact prefix_lengths_eq
  subst rightCut
  refine ⟨rfl, ?_⟩
  by_cases cut_zero : leftCut = 0
  · exact Or.inl cut_zero
  · right
    by_contra cut_ne_full
    have cut_pos : 0 < leftCut := Nat.pos_of_ne_zero cut_zero
    have cut_lt : leftCut < 29 + 2 * depth := lt_of_le_of_ne leftCut_le cut_ne_full
    exact kernelOddFamily_no_proper_prefix_actions_eq
      depth leftCut cut_pos cut_lt piecewise.1

/-- Any uniform single-cut comparator obtained from the odd relation puts the same cut on both
sides, at one of the two endpoints. -/
theorem kernelOddFamily_interleavedAddress_cuts_eq_boundary
    (depth leftCut rightCut : ℕ)
    (leftCut_le : leftCut ≤ 29 + 2 * depth)
    (rightCut_le : rightCut ≤ 29 + 2 * depth)
    (address_comparator : ∀ leftAddress rightAddress,
      (∀ state : ℚ,
        wordAction
              ((kernelOddFamilyLeft depth).take leftCut ++ expandAddress leftAddress ++
                (kernelOddFamilyLeft depth).drop leftCut) state =
          wordAction
              ((kernelOddFamilyRight depth).take rightCut ++ expandAddress rightAddress ++
                (kernelOddFamilyRight depth).drop rightCut) state) ↔
        leftAddress = rightAddress) :
    leftCut = rightCut ∧
      (leftCut = 0 ∨ leftCut = 29 + 2 * depth) := by
  apply kernelOddFamily_cuts_eq_boundary_of_sameAddressActions
    depth leftCut rightCut leftCut_le rightCut_le
  intro address state
  exact (address_comparator address address).2 rfl state

/-- The same endpoint-cut dichotomy holds after reversing the odd relation. -/
theorem kernelOddFamily_interleavedAddress_cuts_eq_boundary_reverse
    (depth leftCut rightCut : ℕ)
    (leftCut_le : leftCut ≤ 29 + 2 * depth)
    (rightCut_le : rightCut ≤ 29 + 2 * depth)
    (address_comparator : ∀ leftAddress rightAddress,
      (∀ state : ℚ,
        wordAction
              ((kernelOddFamilyRight depth).take leftCut ++ expandAddress leftAddress ++
                (kernelOddFamilyRight depth).drop leftCut) state =
          wordAction
              ((kernelOddFamilyLeft depth).take rightCut ++ expandAddress rightAddress ++
                (kernelOddFamilyLeft depth).drop rightCut) state) ↔
        leftAddress = rightAddress) :
    leftCut = rightCut ∧
      (leftCut = 0 ∨ leftCut = 29 + 2 * depth) := by
  have forward := kernelOddFamily_cuts_eq_boundary_of_sameAddressActions
    depth rightCut leftCut rightCut_le leftCut_le (by
      intro address state
      exact ((address_comparator address address).2 rfl state).symm)
  exact ⟨forward.1.symm, forward.1 ▸ forward.2⟩

/-- Any nontrivial uniform single-cut cloak contains a genuine kernel pair wholly before or
wholly after the address. -/
theorem interleavedAddress_exists_genuine_piece
    (leftPrefix rightPrefix leftSuffix rightSuffix : List Letter)
    (witnessAddress : List Bool)
    (same_address_words_ne :
      leftPrefix ++ expandAddress witnessAddress ++ leftSuffix ≠
        rightPrefix ++ expandAddress witnessAddress ++ rightSuffix)
    (same_address_actions_eq : ∀ address state,
      wordAction (leftPrefix ++ expandAddress address ++ leftSuffix) state =
        wordAction (rightPrefix ++ expandAddress address ++ rightSuffix) state) :
    (leftPrefix ≠ rightPrefix ∧
        ∀ state : ℚ, wordAction leftPrefix state = wordAction rightPrefix state) ∨
      (leftSuffix ≠ rightSuffix ∧
        ∀ state : ℚ, wordAction leftSuffix state = wordAction rightSuffix state) := by
  have piecewise := interleavedAddress_piecewise_actions_eq
    leftPrefix rightPrefix leftSuffix rightSuffix same_address_actions_eq
  by_cases prefixes_eq : leftPrefix = rightPrefix
  · right
    refine ⟨?_, piecewise.2⟩
    intro suffixes_eq
    exact same_address_words_ne (by rw [prefixes_eq, suffixes_eq])
  · exact Or.inl ⟨prefixes_eq, piecewise.1⟩

/-- A uniform single-cut comparator used as the exact reduced `bcbc` fork must contain a genuine
kernel pair entirely on one side of its address cut. -/
theorem bcbc_interleavedAddress_exists_genuine_piece
    (code : PairedControl → List Letter) (source target : ℚ)
    (leftPrefix rightPrefix leftSuffix rightSuffix : List Letter)
    (witnessAddress : List Bool)
    (flat_factor :
      flatForkKernelWord code =
        leftPrefix ++ expandAddress witnessAddress ++ leftSuffix)
    (nested_factor :
      nestedForkKernelWord code =
        rightPrefix ++ expandAddress witnessAddress ++ rightSuffix)
    (address_comparator : ∀ leftAddress rightAddress,
      (∀ state : ℚ,
        wordAction (leftPrefix ++ expandAddress leftAddress ++ leftSuffix) state =
          wordAction (rightPrefix ++ expandAddress rightAddress ++ rightSuffix) state) ↔
        leftAddress = rightAddress)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0) :
    (leftPrefix ≠ rightPrefix ∧
        ∀ state : ℚ, wordAction leftPrefix state = wordAction rightPrefix state) ∨
      (leftSuffix ≠ rightSuffix ∧
        ∀ state : ℚ, wordAction leftSuffix state = wordAction rightSuffix state) := by
  have interleaved_words_ne :
      leftPrefix ++ expandAddress witnessAddress ++ leftSuffix ≠
        rightPrefix ++ expandAddress witnessAddress ++ rightSuffix := by
    intro words_eq
    exact bcbc_reducedFork_words_ne code source target endpoint_exact <| by
      calc
        flatForkKernelWord code =
            leftPrefix ++ expandAddress witnessAddress ++ leftSuffix := flat_factor
        _ = rightPrefix ++ expandAddress witnessAddress ++ rightSuffix := words_eq
        _ = nestedForkKernelWord code := nested_factor.symm
  have same_address_actions_eq : ∀ address state,
      wordAction (leftPrefix ++ expandAddress address ++ leftSuffix) state =
        wordAction (rightPrefix ++ expandAddress address ++ rightSuffix) state := by
    intro address state
    exact (address_comparator address address).2 rfl state
  exact interleavedAddress_exists_genuine_piece
    leftPrefix rightPrefix leftSuffix rightSuffix witnessAddress interleaved_words_ne
      same_address_actions_eq

end MatrixMortality.MixedPrimeAddressInterleavingCollapse
