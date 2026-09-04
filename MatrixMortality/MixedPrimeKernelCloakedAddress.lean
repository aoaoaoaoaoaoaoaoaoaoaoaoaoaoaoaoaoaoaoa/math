import MatrixMortality.MixedPrimeAddressWrapperNoGo

/-!
# Kernel-cloaked mixed-prime address comparison

Every genuine mixed-prime kernel pair can cloak the free `{DT,TD}` address comparator. Placing
the two kernel words on opposite branches preserves raw-word distinctness while their common
affine action cancels, leaving exact address equality. Both prefix and suffix cloaks work; the
remaining problem is to realize either factorization through the physical three-control fork.
-/

set_option autoImplicit false

namespace MatrixMortality.MixedPrimeKernelCloakedAddress

open GuardedMixedPrimeFork
open MixedPrimeKernel
open MixedPrimeMacroAddress

/-- Equal-action prefix cloaks turn equality of the wrapped affine actions into exact equality of
arbitrary address interiors. No address-length synchronization is required. -/
theorem prefixCloakedAddress_actions_eq_iff
    (leftCloak rightCloak : List Letter)
    (cloak_actions_eq : ∀ state : ℚ,
      wordAction leftCloak state = wordAction rightCloak state)
    (leftAddress rightAddress : List Bool) :
    (∀ state : ℚ,
      wordAction (leftCloak ++ expandAddress leftAddress) state =
        wordAction (rightCloak ++ expandAddress rightAddress) state) ↔
      leftAddress = rightAddress := by
  constructor
  · intro wrapped_actions_eq
    apply expandAddress_wordAction_injective
    intro state
    apply wordAction_injective leftCloak
    calc
      wordAction leftCloak (wordAction (expandAddress leftAddress) state) =
          wordAction (leftCloak ++ expandAddress leftAddress) state := by
        rw [wordAction_append]
      _ = wordAction (rightCloak ++ expandAddress rightAddress) state :=
        wrapped_actions_eq state
      _ = wordAction rightCloak (wordAction (expandAddress rightAddress) state) := by
        rw [wordAction_append]
      _ = wordAction leftCloak (wordAction (expandAddress rightAddress) state) :=
        (cloak_actions_eq _).symm
  · rintro rfl
    intro state
    rw [wordAction_append, wordAction_append]
    exact cloak_actions_eq _

/-- A nontrivial prefix kernel cloak keeps the two matched raw words distinct. -/
theorem prefixCloakedAddress_words_ne
    (leftCloak rightCloak : List Letter) (cloak_words_ne : leftCloak ≠ rightCloak)
    (address : List Bool) :
    leftCloak ++ expandAddress address ≠ rightCloak ++ expandAddress address := by
  intro wrapped_words_eq
  exact cloak_words_ne
    (List.append_left_injective (expandAddress address) wrapped_words_eq)

/-- A genuine prefix kernel pair yields a raw-distinct comparator for every pair of addresses. -/
theorem prefixCloakedAddress_genuineComparator
    (leftCloak rightCloak : List Letter) (cloak_words_ne : leftCloak ≠ rightCloak)
    (cloak_actions_eq : ∀ state : ℚ,
      wordAction leftCloak state = wordAction rightCloak state)
    (leftAddress rightAddress : List Bool) :
    (leftCloak ++ expandAddress leftAddress ≠
        rightCloak ++ expandAddress rightAddress) ∧
      ((∀ state : ℚ,
        wordAction (leftCloak ++ expandAddress leftAddress) state =
          wordAction (rightCloak ++ expandAddress rightAddress) state) ↔
        leftAddress = rightAddress) := by
  have actions_iff := prefixCloakedAddress_actions_eq_iff
    leftCloak rightCloak cloak_actions_eq leftAddress rightAddress
  constructor
  · intro wrapped_words_eq
    have wrapped_actions_eq : ∀ state : ℚ,
        wordAction (leftCloak ++ expandAddress leftAddress) state =
          wordAction (rightCloak ++ expandAddress rightAddress) state := by
      intro state
      rw [wrapped_words_eq]
    have addresses_eq := actions_iff.mp wrapped_actions_eq
    subst rightAddress
    exact prefixCloakedAddress_words_ne leftCloak rightCloak cloak_words_ne leftAddress
      wrapped_words_eq
  · exact actions_iff

/-- Equal-action suffix cloaks also compare arbitrary addresses exactly. Surjectivity of the
common cloak action replaces the prefix form's injective cancellation. -/
theorem suffixCloakedAddress_actions_eq_iff
    (leftCloak rightCloak : List Letter)
    (cloak_actions_eq : ∀ state : ℚ,
      wordAction leftCloak state = wordAction rightCloak state)
    (leftAddress rightAddress : List Bool) :
    (∀ state : ℚ,
      wordAction (expandAddress leftAddress ++ leftCloak) state =
        wordAction (expandAddress rightAddress ++ rightCloak) state) ↔
      leftAddress = rightAddress := by
  constructor
  · intro wrapped_actions_eq
    apply expandAddress_wordAction_injective
    intro state
    obtain ⟨source, source_eq⟩ := wordAction_surjective leftCloak state
    have wrapped_eq := wrapped_actions_eq source
    rw [wordAction_append, wordAction_append] at wrapped_eq
    calc
      wordAction (expandAddress leftAddress) state =
          wordAction (expandAddress leftAddress) (wordAction leftCloak source) := by
        rw [source_eq]
      _ = wordAction (expandAddress rightAddress) (wordAction rightCloak source) := wrapped_eq
      _ = wordAction (expandAddress rightAddress) (wordAction leftCloak source) := by
        rw [cloak_actions_eq source]
      _ = wordAction (expandAddress rightAddress) state := by rw [source_eq]
  · rintro rfl
    intro state
    rw [wordAction_append, wordAction_append, cloak_actions_eq state]

/-- A nontrivial suffix kernel cloak keeps the two matched raw words distinct. -/
theorem suffixCloakedAddress_words_ne
    (leftCloak rightCloak : List Letter) (cloak_words_ne : leftCloak ≠ rightCloak)
    (address : List Bool) :
    expandAddress address ++ leftCloak ≠ expandAddress address ++ rightCloak := by
  intro wrapped_words_eq
  exact cloak_words_ne
    (List.append_right_injective (expandAddress address) wrapped_words_eq)

/-- A genuine suffix kernel pair yields a raw-distinct comparator for every pair of addresses. -/
theorem suffixCloakedAddress_genuineComparator
    (leftCloak rightCloak : List Letter) (cloak_words_ne : leftCloak ≠ rightCloak)
    (cloak_actions_eq : ∀ state : ℚ,
      wordAction leftCloak state = wordAction rightCloak state)
    (leftAddress rightAddress : List Bool) :
    (expandAddress leftAddress ++ leftCloak ≠
        expandAddress rightAddress ++ rightCloak) ∧
      ((∀ state : ℚ,
        wordAction (expandAddress leftAddress ++ leftCloak) state =
          wordAction (expandAddress rightAddress ++ rightCloak) state) ↔
        leftAddress = rightAddress) := by
  have actions_iff := suffixCloakedAddress_actions_eq_iff
    leftCloak rightCloak cloak_actions_eq leftAddress rightAddress
  constructor
  · intro wrapped_words_eq
    have wrapped_actions_eq : ∀ state : ℚ,
        wordAction (expandAddress leftAddress ++ leftCloak) state =
          wordAction (expandAddress rightAddress ++ rightCloak) state := by
      intro state
      rw [wrapped_words_eq]
    have addresses_eq := actions_iff.mp wrapped_actions_eq
    subst rightAddress
    exact suffixCloakedAddress_words_ne leftCloak rightCloak cloak_words_ne leftAddress
      wrapped_words_eq
  · exact actions_iff

/-- Every member of the explicit odd mixed-prime kernel family gives a concrete prefix-cloaked
raw-distinct address comparator. -/
theorem kernelOddFamily_prefixCloakedAddress_genuineComparator
    (pump : ℕ) (leftAddress rightAddress : List Bool) :
    (kernelOddFamilyLeft pump ++ expandAddress leftAddress ≠
        kernelOddFamilyRight pump ++ expandAddress rightAddress) ∧
      ((∀ state : ℚ,
        wordAction (kernelOddFamilyLeft pump ++ expandAddress leftAddress) state =
          wordAction (kernelOddFamilyRight pump ++ expandAddress rightAddress) state) ↔
        leftAddress = rightAddress) :=
  prefixCloakedAddress_genuineComparator
    (kernelOddFamilyLeft pump) (kernelOddFamilyRight pump) (kernelOddFamily_ne pump)
    (wordAction_kernelOddFamily pump) leftAddress rightAddress

/-- Every member of the explicit odd mixed-prime kernel family also gives a concrete
suffix-cloaked raw-distinct address comparator. -/
theorem kernelOddFamily_suffixCloakedAddress_genuineComparator
    (pump : ℕ) (leftAddress rightAddress : List Bool) :
    (expandAddress leftAddress ++ kernelOddFamilyLeft pump ≠
        expandAddress rightAddress ++ kernelOddFamilyRight pump) ∧
      ((∀ state : ℚ,
        wordAction (expandAddress leftAddress ++ kernelOddFamilyLeft pump) state =
          wordAction (expandAddress rightAddress ++ kernelOddFamilyRight pump) state) ↔
        leftAddress = rightAddress) :=
  suffixCloakedAddress_genuineComparator
    (kernelOddFamilyLeft pump) (kernelOddFamilyRight pump) (kernelOddFamily_ne pump)
    (wordAction_kernelOddFamily pump) leftAddress rightAddress

end MatrixMortality.MixedPrimeKernelCloakedAddress
