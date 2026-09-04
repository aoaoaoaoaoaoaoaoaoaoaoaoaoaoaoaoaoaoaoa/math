import MatrixMortality.MixedPrimeAddressForkNoGo

/-!
# Common-wrapper obstruction for mixed-prime address comparison

Breaking the two-letter address phase with one shared prefix or suffix does not evade the aligned
fork obstruction. Mixed-prime word actions are bijective, so a common two-sided wrapper cancels
from the forced flat/nested action equality. Scalar address injectivity then identifies the two
interiors, making the complete raw fork words equal and contradicting endpoint exactness.
-/

set_option autoImplicit false

namespace MatrixMortality.MixedPrimeAddressWrapperNoGo

open BranchingHistory
open GuardedMixedPrimeBridge
open GuardedMixedPrimeFork
open MixedPrimeKernel
open MixedPrimeMacroAddress
open MixedPrimeMacroComparator
open TransverseSeparatedForkNoGo

/-- Exact `bcbc` endpoint semantics is impossible when the two forced fork words differ only in
aligned address interiors inside one common literal two-sided wrapper. The addresses may have
unequal lengths, and either wrapper may be empty. -/
theorem no_bcbc_endpoint_of_commonContext_address_words
    (code : PairedControl → List Letter) (source target : ℚ)
    (before after : List Letter) (flatAddress nestedAddress : List Bool)
    (flat_word :
      encodedWord code flatForkControl =
        before ++ expandAddress flatAddress ++ after)
    (nested_word :
      encodedWord code nestedForkControl =
        before ++ expandAddress nestedAddress ++ after) :
    ¬∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0 := by
  intro endpoint_exact
  have kernel := bcbc_fork_macro_kernel code source target endpoint_exact
  have contextual_actions_eq : ∀ state,
      wordAction (before ++ expandAddress flatAddress ++ after) state =
        wordAction (before ++ expandAddress nestedAddress ++ after) state := by
    intro state
    rw [← flat_word, ← nested_word]
    exact kernel.2 state
  have address_actions_eq : ∀ state,
      wordAction (expandAddress flatAddress) state =
        wordAction (expandAddress nestedAddress) state :=
    wordAction_cancel_context before (expandAddress flatAddress)
      (expandAddress nestedAddress) after contextual_actions_eq
  have addresses_eq : flatAddress = nestedAddress :=
    expandAddress_at_zero_injective (address_actions_eq 0)
  apply kernel.1
  calc
    encodedWord code flatForkControl =
        before ++ expandAddress flatAddress ++ after := flat_word
    _ = before ++ expandAddress nestedAddress ++ after := by rw [addresses_eq]
    _ = encodedWord code nestedForkControl := nested_word.symm

end MatrixMortality.MixedPrimeAddressWrapperNoGo
