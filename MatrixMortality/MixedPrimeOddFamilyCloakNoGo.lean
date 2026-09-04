import MatrixMortality.GuardedMixedPrimeOddFamilyParikh
import MatrixMortality.MixedPrimePrefixPumpSuffixNoGo

/-!
# Prefix-cloak obstruction for the mixed-prime odd kernel family

The physical `bcbc` fork forces every exact odd-family prefix cloak to retain a nonempty,
Parikh-balanced suffix after deleting the common address. The odd family has only one such proper
suffix: all but its first three letters. This suffix is too long for the strict physical cloak
gate, so no member of the family realizes a prefix-cloaked fork at any address depth.
-/

set_option autoImplicit false

namespace MatrixMortality.MixedPrimeOddFamilyCloakNoGo

open BranchingHistory
open GuardedMixedPrimeBridge
open GuardedMixedPrimeFork
open MixedPrimeKernel
open MixedPrimeMacroAddress
open MixedPrimePrefixPumpSuffixNoGo

private theorem no_bcbc_endpoint_of_unique_long_balanced_suffix
    (code : PairedControl → List Letter) (source target : ℚ)
    (leftCloak rightCloak : List Letter) (relationLength : ℕ) (address : List Bool)
    (relationLength_ge : 6 ≤ relationLength)
    (left_length : leftCloak.length = relationLength)
    (right_length : rightCloak.length = relationLength)
    (unique_balanced_suffix : ∀ suffixLength,
      0 < suffixLength → suffixLength < relationLength →
      (leftCloak.drop (relationLength - suffixLength)).count .dilate =
        (rightCloak.drop (relationLength - suffixLength)).count .dilate →
      suffixLength = relationLength - 3)
    (flat_factor : flatForkKernelWord code = leftCloak ++ expandAddress address)
    (nested_factor : nestedForkKernelWord code = rightCloak ++ expandAddress address) :
    ¬ ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0 := by
  intro endpoint_exact
  obtain ⟨leftSuffix, rightSuffix, leftCloak_eq, rightCloak_eq,
      _terminal_left, _terminal_right, leftSuffix_ne, _rightSuffix_ne,
      suffix_lengths_eq, suffix_counts_eq, depth_gate⟩ :=
    bcbc_prefixCloak_exists_balanced_suffixes
      code source target leftCloak rightCloak address endpoint_exact flat_factor nested_factor
  let suffixLength := leftSuffix.length
  have suffix_pos : 0 < suffixLength := by
    exact List.length_pos_of_ne_nil leftSuffix_ne
  have suffix_lt : suffixLength < relationLength := by
    simp only [suffixLength]
    rw [left_length] at depth_gate
    omega
  have left_prefix_length :
      (code (.data .c) ++ code .toggle ++ code (.data .b)).length =
        relationLength - suffixLength := by
    change
      (code (.data .c) ++ code .toggle ++ code (.data .b)).length =
        relationLength - leftSuffix.length
    have lengths_eq := congrArg List.length leftCloak_eq
    simp only [List.length_append] at lengths_eq
    rw [left_length] at lengths_eq
    simp only [List.length_append]
    omega
  have right_prefix_length :
      (code (.data .b) ++ code .toggle ++ code (.data .c)).length =
        relationLength - suffixLength := by
    change
      (code (.data .b) ++ code .toggle ++ code (.data .c)).length =
        relationLength - leftSuffix.length
    have lengths_eq := congrArg List.length rightCloak_eq
    simp only [List.length_append] at lengths_eq
    rw [right_length] at lengths_eq
    rw [← suffix_lengths_eq] at lengths_eq
    simp only [List.length_append]
    omega
  have left_drop :
      leftCloak.drop (relationLength - suffixLength) = leftSuffix := by
    rw [leftCloak_eq, ← left_prefix_length]
    exact List.drop_left
  have right_drop :
      rightCloak.drop (relationLength - suffixLength) = rightSuffix := by
    rw [rightCloak_eq, ← right_prefix_length]
    exact List.drop_left
  have balanced_suffix :
      (leftCloak.drop (relationLength - suffixLength)).count .dilate =
        (rightCloak.drop (relationLength - suffixLength)).count .dilate := by
    rw [left_drop, right_drop]
    exact suffix_counts_eq .dilate
  have suffixLength_eq := unique_balanced_suffix
    suffixLength suffix_pos suffix_lt balanced_suffix
  simp only [suffixLength] at depth_gate suffixLength_eq
  rw [left_length] at depth_gate
  omega

/-- No odd-family kernel relation can occur as the prefix cloak of a physical exact-endpoint
`bcbc` fork, at any pump or address depth. -/
theorem no_bcbc_endpoint_of_kernelOddFamily_prefixCloak
    (code : PairedControl → List Letter) (source target : ℚ)
    (depth : ℕ) (address : List Bool)
    (flat_factor :
      flatForkKernelWord code = kernelOddFamilyLeft depth ++ expandAddress address)
    (nested_factor :
      nestedForkKernelWord code = kernelOddFamilyRight depth ++ expandAddress address) :
    ¬ ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0 := by
  have relation_lengths := kernelOddFamily_length depth
  exact no_bcbc_endpoint_of_unique_long_balanced_suffix
    code source target (kernelOddFamilyLeft depth) (kernelOddFamilyRight depth)
      (29 + 2 * depth) address (by omega) relation_lengths.1 relation_lengths.2
      (kernelOddFamily_suffix_dilateCount_eq depth) flat_factor nested_factor

/-- Reversing the two sides of the odd-family relation cannot produce a prefix cloak either. -/
theorem no_bcbc_endpoint_of_kernelOddFamily_prefixCloak_reverse
    (code : PairedControl → List Letter) (source target : ℚ)
    (depth : ℕ) (address : List Bool)
    (flat_factor :
      flatForkKernelWord code = kernelOddFamilyRight depth ++ expandAddress address)
    (nested_factor :
      nestedForkKernelWord code = kernelOddFamilyLeft depth ++ expandAddress address) :
    ¬ ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0 := by
  have relation_lengths := kernelOddFamily_length depth
  refine no_bcbc_endpoint_of_unique_long_balanced_suffix
    code source target (kernelOddFamilyRight depth) (kernelOddFamilyLeft depth)
      (29 + 2 * depth) address (by omega) relation_lengths.2 relation_lengths.1 ?_
        flat_factor nested_factor
  intro suffixLength suffix_pos suffix_lt counts_eq
  exact kernelOddFamily_suffix_dilateCount_eq
    depth suffixLength suffix_pos suffix_lt counts_eq.symm

end MatrixMortality.MixedPrimeOddFamilyCloakNoGo
