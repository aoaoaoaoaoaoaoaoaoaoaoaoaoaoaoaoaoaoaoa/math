import MatrixMortality.GuardedMixedPrimeReducedKernel
import MatrixMortality.MixedPrimeMacroComparator

/-!
# Aligned-address obstruction for the mixed-prime terminal fork

The free `{DT,TD}` address stack cannot itself carry the complete `bcbc` endpoint fork. Exact
endpoint semantics forces the flat and nested fork words to be distinct but equal as affine
actions, whereas evaluation at zero is injective on the address stack. Consequently at least one
fork branch must leave the aligned address submonoid. In particular, coding every control by a
whole address is impossible, as is coding the two data controls by equal-length addresses.
-/

set_option autoImplicit false

namespace MatrixMortality.MixedPrimeAddressForkNoGo

open BranchingHistory
open GuardedMixedPrimeBridge
open GuardedMixedPrimeFork
open MixedPrimeKernel
open MixedPrimeMacroAddress
open MixedPrimeMacroComparator
open TransverseSeparatedForkNoGo

/-- Expansion from binary macro addresses preserves concatenation. -/
theorem expandAddress_append (left right : List Bool) :
    expandAddress (left ++ right) = expandAddress left ++ expandAddress right := by
  induction left with
  | nil => rfl
  | cons bit tail induction =>
      simp only [List.cons_append, expandAddress, induction, List.append_assoc]

/-- A block code whose every control macro is an aligned address maps every control word to the
concatenated binary address. -/
theorem encodedWord_addressCode
    (macroAddress : PairedControl → List Bool) (word : List PairedControl) :
    encodedWord (fun control => expandAddress (macroAddress control)) word =
      expandAddress (word.flatMap macroAddress) := by
  induction word with
  | nil => rfl
  | cons control tail induction =>
      rw [encodedWord, List.flatMap_cons, List.flatMap_cons, expandAddress_append]
      simpa only [encodedWord] using congrArg
        (fun suffix => expandAddress (macroAddress control) ++ suffix) induction

/-- Exact `bcbc` endpoint semantics is impossible whenever both forced fork branches lie in the
free aligned address submonoid. The two address witnesses need not have equal length a priori. -/
theorem no_bcbc_endpoint_of_fork_address_words
    (code : PairedControl → List Letter) (source target : ℚ)
    (flatAddress nestedAddress : List Bool)
    (flat_word : encodedWord code flatForkControl = expandAddress flatAddress)
    (nested_word : encodedWord code nestedForkControl = expandAddress nestedAddress) :
    ¬∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0 := by
  intro endpoint_exact
  have kernel := bcbc_fork_macro_kernel code source target endpoint_exact
  have address_values_eq :
      wordAction (expandAddress flatAddress) 0 =
        wordAction (expandAddress nestedAddress) 0 := by
    rw [← flat_word, ← nested_word]
    exact kernel.2 0
  have addresses_eq : flatAddress = nestedAddress :=
    expandAddress_at_zero_injective address_values_eq
  apply kernel.1
  calc
    encodedWord code flatForkControl = expandAddress flatAddress := flat_word
    _ = expandAddress nestedAddress := by rw [addresses_eq]
    _ = encodedWord code nestedForkControl := nested_word.symm

/-- No exact endpoint code can assign all three paired controls whole aligned `{DT,TD}`
addresses. Some control boundary must break address phase. -/
theorem no_bcbc_endpoint_address_macro_code
    (macroAddress : PairedControl → List Bool) (source target : ℚ) :
    ¬∀ word,
      wordAction
          (encodedWord (fun control => expandAddress (macroAddress control)) word) source =
          target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0 := by
  apply no_bcbc_endpoint_of_fork_address_words
    (fun control => expandAddress (macroAddress control)) source target
    (flatForkControl.flatMap macroAddress) (nestedForkControl.flatMap macroAddress)
  · exact encodedWord_addressCode macroAddress flatForkControl
  · exact encodedWord_addressCode macroAddress nestedForkControl

/-- Even without address alignment for the toggle, exact endpoint semantics forbids the two data
controls from being equal-length aligned addresses: their physical slopes would coincide. -/
theorem no_bcbc_endpoint_of_equalLength_address_data
    (code : PairedControl → List Letter) (source target : ℚ)
    (dataBAddress dataCAddress : List Bool)
    (data_b_word : code (.data .b) = expandAddress dataBAddress)
    (data_c_word : code (.data .c) = expandAddress dataCAddress)
    (length_eq : dataBAddress.length = dataCAddress.length) :
    ¬∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0 := by
  intro endpoint_exact
  have scales_ne := bcbc_data_macro_scales_ne code source target endpoint_exact
  apply scales_ne
  rw [data_b_word, data_c_word, wordScale_expandAddress, wordScale_expandAddress, length_eq]

end MatrixMortality.MixedPrimeAddressForkNoGo
