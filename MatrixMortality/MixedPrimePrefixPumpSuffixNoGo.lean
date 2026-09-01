import MatrixMortality.MixedPrimePrefixCloakNoGo

/-!
# Balanced-suffix gate for pumped mixed-prime prefix cloaks

A physical prefix-cloaked reduced fork leaves a nonempty piece of each cloak inside its terminal
data blocks. The two pieces have equal length and equal Parikh vectors, because deleting the
common aligned address suffix leaves the cyclic pair `yx,xy`. If the common suffix has address
depth `n` and the retained cloak suffix has length `q`, the nonempty toggle sharpens the gate to
`2(n+q)<|L|`. This is the finite-periodic invariant used to classify the pumped kernel cloaks.
-/

set_option autoImplicit false

namespace MatrixMortality.MixedPrimePrefixPumpSuffixNoGo

open BranchingHistory
open GuardedMixedPrimeBridge
open GuardedMixedPrimeFork
open MixedPrimeKernel
open MixedPrimeMacroAddress
open MixedPrimePrefixCloakNoGo

private theorem exists_boundary_tail_of_common_length_le
    {α : Type*} (head terminal cloak common : List α)
    (factorization : head ++ terminal = cloak ++ common)
    (common_length_le : common.length ≤ terminal.length) :
    ∃ tail, cloak = head ++ tail ∧ terminal = tail ++ common := by
  rcases List.append_eq_append_iff.mp factorization with
    ⟨tail, cloak_eq, terminal_eq⟩ | ⟨residue, head_eq, common_eq⟩
  · exact ⟨tail, cloak_eq, terminal_eq⟩
  · have residue_length_zero : residue.length = 0 := by
      have lengths_eq := congrArg List.length common_eq
      simp only [List.length_append] at lengths_eq
      omega
    have residue_nil := List.eq_nil_of_length_eq_zero residue_length_zero
    refine ⟨[], ?_, ?_⟩
    · simpa [residue_nil] using head_eq.symm
    · simpa [residue_nil] using common_eq.symm

/-- Once a common suffix is strictly shorter than the terminal data pair, deleting it exposes
equal-length, Parikh-balanced nonempty suffixes of the two cloaks. -/
theorem forkWords_exists_balanced_cloakSuffixes
    (x y z leftCloak rightCloak common : List Letter)
    (left_factor : y ++ z ++ x ++ y ++ x = leftCloak ++ common)
    (right_factor : x ++ z ++ y ++ x ++ y = rightCloak ++ common)
    (common_short : common.length < x.length + y.length) :
    ∃ leftSuffix rightSuffix,
      leftCloak = (y ++ z ++ x) ++ leftSuffix ∧
      rightCloak = (x ++ z ++ y) ++ rightSuffix ∧
      y ++ x = leftSuffix ++ common ∧
      x ++ y = rightSuffix ++ common ∧
      leftSuffix ≠ [] ∧
      rightSuffix ≠ [] ∧
      leftSuffix.length = rightSuffix.length ∧
      (∀ letter, leftSuffix.count letter = rightSuffix.count letter) := by
  have common_length_le_yx : common.length ≤ (y ++ x).length := by
    simp only [List.length_append]
    omega
  have common_length_le_xy : common.length ≤ (x ++ y).length := by
    simp only [List.length_append]
    omega
  obtain ⟨leftSuffix, leftCloak_eq, yx_eq⟩ :=
    exists_boundary_tail_of_common_length_le
      (y ++ z ++ x) (y ++ x) leftCloak common
        (by simpa only [List.append_assoc] using left_factor) common_length_le_yx
  obtain ⟨rightSuffix, rightCloak_eq, xy_eq⟩ :=
    exists_boundary_tail_of_common_length_le
      (x ++ z ++ y) (x ++ y) rightCloak common
        (by simpa only [List.append_assoc] using right_factor) common_length_le_xy
  have leftSuffix_ne : leftSuffix ≠ [] := by
    intro leftSuffix_nil
    have lengths_eq := congrArg List.length yx_eq
    simp only [leftSuffix_nil, List.nil_append, List.length_append] at lengths_eq
    omega
  have rightSuffix_ne : rightSuffix ≠ [] := by
    intro rightSuffix_nil
    have lengths_eq := congrArg List.length xy_eq
    simp only [rightSuffix_nil, List.nil_append, List.length_append] at lengths_eq
    omega
  have suffix_lengths_eq : leftSuffix.length = rightSuffix.length := by
    have left_lengths := congrArg List.length yx_eq
    have right_lengths := congrArg List.length xy_eq
    simp only [List.length_append] at left_lengths right_lengths
    omega
  have suffix_counts_eq : ∀ letter,
      leftSuffix.count letter = rightSuffix.count letter := by
    intro letter
    have left_counts := congrArg (List.count letter) yx_eq
    have right_counts := congrArg (List.count letter) xy_eq
    simp only [List.count_append] at left_counts right_counts
    have terminal_counts :
        (y ++ x).count letter = (x ++ y).count letter := by
      simp only [List.count_append]
      omega
    omega
  exact ⟨leftSuffix, rightSuffix, leftCloak_eq, rightCloak_eq, yx_eq, xy_eq,
    leftSuffix_ne, rightSuffix_ne, suffix_lengths_eq, suffix_counts_eq⟩

/-- A physical exact-endpoint prefix cloak exposes balanced nonempty cloak suffixes. If their
common length is `q` and the aligned address has depth `n`, then `2(n+q)<|L|`. -/
theorem bcbc_prefixCloak_exists_balanced_suffixes
    (code : PairedControl → List Letter) (source target : ℚ)
    (leftCloak rightCloak : List Letter) (address : List Bool)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0)
    (flat_factor : flatForkKernelWord code = leftCloak ++ expandAddress address)
    (nested_factor : nestedForkKernelWord code = rightCloak ++ expandAddress address) :
    ∃ leftSuffix rightSuffix,
      leftCloak =
          (code (.data .c) ++ code .toggle ++ code (.data .b)) ++ leftSuffix ∧
      rightCloak =
          (code (.data .b) ++ code .toggle ++ code (.data .c)) ++ rightSuffix ∧
      code (.data .c) ++ code (.data .b) =
        leftSuffix ++ expandAddress address ∧
      code (.data .b) ++ code (.data .c) =
        rightSuffix ++ expandAddress address ∧
      leftSuffix ≠ [] ∧
      rightSuffix ≠ [] ∧
      leftSuffix.length = rightSuffix.length ∧
      (∀ letter, leftSuffix.count letter = rightSuffix.count letter) ∧
      2 * (address.length + leftSuffix.length) < leftCloak.length := by
  have physical_left :
      code (.data .c) ++ code .toggle ++ code (.data .b) ++
          code (.data .c) ++ code (.data .b) =
        leftCloak ++ expandAddress address := by
    simpa [flatForkKernelWord, List.append_assoc] using flat_factor
  have physical_right :
      code (.data .b) ++ code .toggle ++ code (.data .c) ++
          code (.data .b) ++ code (.data .c) =
        rightCloak ++ expandAddress address := by
    simpa [nestedForkKernelWord, List.append_assoc] using nested_factor
  have strict_size := bcbc_prefixCloak_strict_size
    code source target leftCloak rightCloak address endpoint_exact flat_factor nested_factor
  have common_short :
      (expandAddress address).length <
        (code (.data .b)).length + (code (.data .c)).length := by
    simpa only [expandAddress_length] using strict_size.1
  obtain ⟨leftSuffix, rightSuffix, leftCloak_eq, rightCloak_eq,
      terminal_left, terminal_right, leftSuffix_ne, rightSuffix_ne,
      suffix_lengths_eq, suffix_counts_eq⟩ :=
    forkWords_exists_balanced_cloakSuffixes
      (code (.data .b)) (code (.data .c)) (code .toggle)
        leftCloak rightCloak (expandAddress address)
        physical_left physical_right common_short
  have toggle_length_pos : 0 < (code .toggle).length :=
    List.length_pos_of_ne_nil (bcbc_toggle_macro_ne code source target endpoint_exact)
  have total_lengths := congrArg List.length physical_left
  have terminal_lengths := congrArg List.length terminal_left
  simp only [List.length_append, expandAddress_length] at total_lengths terminal_lengths
  have depth_gate :
      2 * (address.length + leftSuffix.length) < leftCloak.length := by
    omega
  exact ⟨leftSuffix, rightSuffix, leftCloak_eq, rightCloak_eq,
    terminal_left, terminal_right, leftSuffix_ne, rightSuffix_ne,
    suffix_lengths_eq, suffix_counts_eq, depth_gate⟩

end MatrixMortality.MixedPrimePrefixPumpSuffixNoGo
