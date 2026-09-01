import MatrixMortality.MixedPrimeKernelCloakedAddress

/-!
# Prefix-cloak size obstruction for the mixed-prime terminal fork

If a reduced `bcbc` fork is a genuine equal-action kernel pair followed by one common aligned
`{DT,TD}` address, that address cannot reach the final data-macro boundary. Otherwise the common
suffix contains both `yx` and `xy`; equal suffix lengths then force the two data words to commute,
contrary to exact endpoint semantics. The toggle is nonempty, so the data boundary is in turn
strictly shorter than either prefix cloak. Every fixed prefix cloak therefore permits only
finitely many address depths.
-/

set_option autoImplicit false

namespace MatrixMortality.MixedPrimePrefixCloakNoGo

open BranchingHistory
open GuardedMixedPrimeBridge
open GuardedMixedPrimeFork
open MixedPrimeKernel
open MixedPrimeMacroAddress

private theorem exists_common_suffix_factor_of_length_le
    {α : Type*} (leftPrefix rightPrefix suffix common : List α)
    (words_eq : leftPrefix ++ suffix = rightPrefix ++ common)
    (length_le : suffix.length ≤ common.length) :
    ∃ middle, common = middle ++ suffix := by
  rcases List.append_eq_append_iff.mp words_eq with
    ⟨middle, _, suffix_eq⟩ | ⟨middle, _, common_eq⟩
  · have middle_length_zero : middle.length = 0 := by
      have lengths_eq := congrArg List.length suffix_eq
      simp only [List.length_append] at lengths_eq
      omega
    have middle_nil := List.eq_nil_of_length_eq_zero middle_length_zero
    refine ⟨[], ?_⟩
    simpa [middle_nil] using suffix_eq.symm
  · exact ⟨middle, common_eq⟩

private theorem equal_length_suffixes_eq
    {α : Type*} (common leftPrefix rightPrefix leftSuffix rightSuffix : List α)
    (left_factor : common = leftPrefix ++ leftSuffix)
    (right_factor : common = rightPrefix ++ rightSuffix)
    (length_eq : leftSuffix.length = rightSuffix.length) :
    leftSuffix = rightSuffix := by
  have factorizations_eq :
      leftPrefix ++ leftSuffix = rightPrefix ++ rightSuffix :=
    left_factor.symm.trans right_factor
  rcases List.append_eq_append_iff.mp factorizations_eq with
    ⟨middle, _, leftSuffix_eq⟩ | ⟨middle, _, rightSuffix_eq⟩
  · have middle_length_zero : middle.length = 0 := by
      have lengths_eq := congrArg List.length leftSuffix_eq
      simp only [List.length_append] at lengths_eq
      omega
    simpa [List.eq_nil_of_length_eq_zero middle_length_zero] using leftSuffix_eq
  · have middle_length_zero : middle.length = 0 := by
      have lengths_eq := congrArg List.length rightSuffix_eq
      simp only [List.length_append] at lengths_eq
      omega
    simpa [List.eq_nil_of_length_eq_zero middle_length_zero] using rightSuffix_eq.symm

/-- If a common suffix of the two reduced fork words reaches across their final two data blocks,
then those two data words commute literally. -/
theorem forkWords_data_commute_of_commonSuffix_long
    (x y z leftPrefix rightPrefix common : List Letter)
    (left_factor : y ++ z ++ x ++ y ++ x = leftPrefix ++ common)
    (right_factor : x ++ z ++ y ++ x ++ y = rightPrefix ++ common)
    (common_long : x.length + y.length ≤ common.length) :
    x ++ y = y ++ x := by
  have yx_factor : ∃ middle, common = middle ++ (y ++ x) := by
    apply exists_common_suffix_factor_of_length_le
      (y ++ z ++ x) leftPrefix (y ++ x) common
    · simpa only [List.append_assoc] using left_factor
    · simp only [List.length_append]
      omega
  have xy_factor : ∃ middle, common = middle ++ (x ++ y) := by
    apply exists_common_suffix_factor_of_length_le
      (x ++ z ++ y) rightPrefix (x ++ y) common
    · simpa only [List.append_assoc] using right_factor
    · simp only [List.length_append]
      omega
  obtain ⟨leftMiddle, leftMiddle_eq⟩ := yx_factor
  obtain ⟨rightMiddle, rightMiddle_eq⟩ := xy_factor
  exact equal_length_suffixes_eq common rightMiddle leftMiddle
    (x ++ y) (y ++ x) rightMiddle_eq leftMiddle_eq (by simp only [List.length_append]; omega)

/-- The two data words of an exact endpoint code cannot commute in the raw free monoid. -/
theorem bcbc_data_macro_words_not_commute
    (code : PairedControl → List Letter) (source target : ℚ)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0) :
    code (.data .b) ++ code (.data .c) ≠
      code (.data .c) ++ code (.data .b) := by
  intro words_commute
  have macro_words_ne := bcbc_macro_words_ne_nil code source target endpoint_exact
  have actions_commute : ∀ state,
      wordAction (code (.data .b)) (wordAction (code (.data .c)) state) =
        wordAction (code (.data .c)) (wordAction (code (.data .b)) state) := by
    intro state
    simpa only [wordAction_append] using
      congrArg (fun word => wordAction word state) words_commute
  have data_c_fixes_data_b_fixedPoint :
      wordAction (code (.data .c)) (wordFixedPoint (code (.data .b))) =
        wordFixedPoint (code (.data .b)) :=
    wordAction_wordFixedPoint_of_actions_commute
      (code (.data .b)) (code (.data .c)) macro_words_ne.1 actions_commute
  have fixedPoints_eq :
      wordFixedPoint (code (.data .b)) = wordFixedPoint (code (.data .c)) :=
    wordAction_fixedPoint_unique_of_ne_nil
      (code (.data .c)) macro_words_ne.2.1 data_c_fixes_data_b_fixedPoint
        (wordAction_wordFixedPoint_of_ne_nil (code (.data .c)) macro_words_ne.2.1)
  exact bcbc_data_macro_fixedPoints_ne code source target endpoint_exact fixedPoints_eq

/-- A genuine reduced fork followed on both branches by one common aligned address obeys the
strict size chain `2|u| < |x|+|y| < |L|`. This is a word-theoretic bound: it uses only data
noncommutation, a nonempty toggle, and the two displayed factorizations. -/
theorem prefixCloak_strict_size
    (x y z leftCloak rightCloak : List Letter) (address : List Bool)
    (z_ne : z ≠ []) (data_words_not_commute : x ++ y ≠ y ++ x)
    (left_factor : y ++ z ++ x ++ y ++ x = leftCloak ++ expandAddress address)
    (right_factor : x ++ z ++ y ++ x ++ y = rightCloak ++ expandAddress address) :
    2 * address.length < x.length + y.length ∧
      x.length + y.length < leftCloak.length := by
  have address_short :
      (expandAddress address).length < x.length + y.length := by
    by_contra address_not_short
    apply data_words_not_commute
    apply forkWords_data_commute_of_commonSuffix_long
      x y z leftCloak rightCloak (expandAddress address) left_factor right_factor
    omega
  have toggle_length_pos : 0 < z.length := List.length_pos_of_ne_nil z_ne
  have total_lengths := congrArg List.length left_factor
  simp only [List.length_append, expandAddress_length] at address_short total_lengths
  constructor
  · exact address_short
  · omega

/-- Exact endpoint semantics specializes the generic prefix-cloak bound to the physical data and
toggle macros. Hence every fixed cloak has a finite, source-independent address-depth window. -/
theorem bcbc_prefixCloak_strict_size
    (code : PairedControl → List Letter) (source target : ℚ)
    (leftCloak rightCloak : List Letter) (address : List Bool)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0)
    (flat_factor : flatForkKernelWord code = leftCloak ++ expandAddress address)
    (nested_factor : nestedForkKernelWord code = rightCloak ++ expandAddress address) :
    2 * address.length < (code (.data .b)).length + (code (.data .c)).length ∧
      (code (.data .b)).length + (code (.data .c)).length < leftCloak.length := by
  apply prefixCloak_strict_size
    (code (.data .b)) (code (.data .c)) (code .toggle)
      leftCloak rightCloak address
    (bcbc_toggle_macro_ne code source target endpoint_exact)
    (bcbc_data_macro_words_not_commute code source target endpoint_exact)
  · simpa [flatForkKernelWord, List.append_assoc] using flat_factor
  · simpa [nestedForkKernelWord, List.append_assoc] using nested_factor

end MatrixMortality.MixedPrimePrefixCloakNoGo
