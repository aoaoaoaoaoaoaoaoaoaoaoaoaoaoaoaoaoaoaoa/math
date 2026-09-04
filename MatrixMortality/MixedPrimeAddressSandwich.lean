import MatrixMortality.MixedPrimeAddressInterleavingCollapse

/-!
# Two-cut collapse and the mixed-prime address sandwich

Five probes split a uniform double insertion of one macro address into three independent affine
kernel pairs. For a genuine kernel pair `L ∼ R`, the surviving central placement
`W · L · W ∼ W · R · W` is an exact address comparator: its slope recovers address length and
its offset then recovers the free radix address.
-/

set_option autoImplicit false

namespace MatrixMortality.MixedPrimeAddressSandwich

open GuardedMixedPrimeFork
open MixedPrimeKernel
open MixedPrimeMacroAddress
open MixedPrimeMacroComparator
open MixedPrimeAddressInterleavingCollapse

private theorem wordAction_affine (word : List Letter) (state : ℚ) :
    wordAction word state = wordScale word * state + wordAction word 0 := by
  linarith [wordAction_sub word state 0]

/-- Closed affine formula for inserting the same macro address twice among three raw contexts. -/
theorem wordAction_doubleInterleave
    (before center after : List Letter) (address : List Bool) (state : ℚ) :
    wordAction
          (before ++ expandAddress address ++ center ++ expandAddress address ++ after) state =
      wordAction before 0 +
        wordScale before * (2 / 5 : ℚ) ^ address.length * wordAction center 0 +
        wordScale before * (2 / 5 : ℚ) ^ (2 * address.length) *
          wordScale center * wordAction after 0 +
        wordScale before *
          (1 + (2 / 5 : ℚ) ^ address.length * wordScale center) *
          addressOffset address +
        wordScale before * (2 / 5 : ℚ) ^ (2 * address.length) *
          wordScale center * wordScale after * state := by
  simp only [List.append_assoc, wordAction_append, wordAction_expandAddress]
  rw [wordAction_affine before, wordAction_affine center, wordAction_affine after]
  ring

/-- The empty address and two constant addresses at depths one and two force every fixed piece
of a double insertion to have the same affine action on both sides. -/
theorem doubleInterleaved_piecewise_actions_eq_of_fiveProbes
    (leftPrefix rightPrefix leftMiddle rightMiddle leftSuffix rightSuffix : List Letter)
    (empty_actions_eq : ∀ state,
      wordAction
            (leftPrefix ++ expandAddress [] ++ leftMiddle ++
              expandAddress [] ++ leftSuffix) state =
        wordAction
            (rightPrefix ++ expandAddress [] ++ rightMiddle ++
              expandAddress [] ++ rightSuffix) state)
    (false_one_actions_eq : ∀ state,
      wordAction
            (leftPrefix ++ expandAddress [false] ++ leftMiddle ++
              expandAddress [false] ++ leftSuffix) state =
        wordAction
            (rightPrefix ++ expandAddress [false] ++ rightMiddle ++
              expandAddress [false] ++ rightSuffix) state)
    (true_one_actions_eq : ∀ state,
      wordAction
            (leftPrefix ++ expandAddress [true] ++ leftMiddle ++
              expandAddress [true] ++ leftSuffix) state =
        wordAction
            (rightPrefix ++ expandAddress [true] ++ rightMiddle ++
              expandAddress [true] ++ rightSuffix) state)
    (false_two_actions_eq : ∀ state,
      wordAction
            (leftPrefix ++ expandAddress [false, false] ++ leftMiddle ++
              expandAddress [false, false] ++ leftSuffix) state =
        wordAction
            (rightPrefix ++ expandAddress [false, false] ++ rightMiddle ++
              expandAddress [false, false] ++ rightSuffix) state)
    (true_two_actions_eq : ∀ state,
      wordAction
            (leftPrefix ++ expandAddress [true, true] ++ leftMiddle ++
              expandAddress [true, true] ++ leftSuffix) state =
        wordAction
            (rightPrefix ++ expandAddress [true, true] ++ rightMiddle ++
              expandAddress [true, true] ++ rightSuffix) state) :
    (∀ state : ℚ, wordAction leftPrefix state = wordAction rightPrefix state) ∧
      (∀ state : ℚ, wordAction leftMiddle state = wordAction rightMiddle state) ∧
      (∀ state : ℚ, wordAction leftSuffix state = wordAction rightSuffix state) := by
  have false_one := false_one_actions_eq 0
  have true_one := true_one_actions_eq 0
  have false_two := false_two_actions_eq 0
  have true_two := true_two_actions_eq 0
  rw [wordAction_doubleInterleave, wordAction_doubleInterleave] at false_one true_one
  rw [wordAction_doubleInterleave, wordAction_doubleInterleave] at false_two true_two
  norm_num [addressOffset, addressDigit] at false_one true_one false_two true_two
  have prefix_middle_scales_eq :
      wordScale leftPrefix * wordScale leftMiddle =
        wordScale rightPrefix * wordScale rightMiddle := by
    nlinarith [false_one, true_one, false_two, true_two]
  have prefix_scales_eq : wordScale leftPrefix = wordScale rightPrefix := by
    nlinarith [false_one, true_one, false_two, true_two,
      prefix_middle_scales_eq]
  have middle_scales_eq : wordScale leftMiddle = wordScale rightMiddle := by
    have prefix_scale_ne : wordScale leftPrefix ≠ 0 :=
      ne_of_gt (wordScale_pos leftPrefix)
    apply (mul_left_cancel₀ prefix_scale_ne)
    simpa only [prefix_scales_eq] using prefix_middle_scales_eq
  have composite_actions_eq : ∀ state : ℚ,
      wordAction (leftPrefix ++ leftMiddle ++ leftSuffix) state =
        wordAction (rightPrefix ++ rightMiddle ++ rightSuffix) state := by
    intro state
    simpa [expandAddress] using empty_actions_eq state
  have composite_scales_eq := wordScale_eq_of_wordActions_eq
    (leftPrefix ++ leftMiddle ++ leftSuffix)
      (rightPrefix ++ rightMiddle ++ rightSuffix) composite_actions_eq
  simp only [wordScale_append] at composite_scales_eq
  have suffix_scales_eq : wordScale leftSuffix = wordScale rightSuffix := by
    have prefix_middle_scale_ne :
        wordScale leftPrefix * wordScale leftMiddle ≠ 0 :=
      mul_ne_zero (ne_of_gt (wordScale_pos leftPrefix))
        (ne_of_gt (wordScale_pos leftMiddle))
    apply (mul_left_cancel₀ prefix_middle_scale_ne)
    simpa only [prefix_scales_eq, middle_scales_eq] using composite_scales_eq

  have empty_zero := empty_actions_eq 0
  have false_zero := false_one_actions_eq 0
  have false_false_zero := false_two_actions_eq 0
  rw [wordAction_doubleInterleave, wordAction_doubleInterleave] at empty_zero
  rw [wordAction_doubleInterleave, wordAction_doubleInterleave] at false_zero
  rw [wordAction_doubleInterleave, wordAction_doubleInterleave] at false_false_zero
  norm_num [addressOffset, addressDigit, prefix_scales_eq, middle_scales_eq,
    suffix_scales_eq] at empty_zero false_zero false_false_zero
  ring_nf at empty_zero false_zero false_false_zero
  have prefix_offsets_eq : wordAction leftPrefix 0 = wordAction rightPrefix 0 := by
    linarith [empty_zero, false_zero, false_false_zero]
  have scaled_middle_offsets_eq :
      wordScale rightPrefix * wordAction leftMiddle 0 =
        wordScale rightPrefix * wordAction rightMiddle 0 := by
    linarith [empty_zero, false_zero, false_false_zero]
  have middle_offsets_eq : wordAction leftMiddle 0 = wordAction rightMiddle 0 := by
    exact (mul_left_cancel₀ (ne_of_gt (wordScale_pos rightPrefix)))
      scaled_middle_offsets_eq
  have scaled_suffix_offsets_eq :
      (wordScale rightPrefix * wordScale rightMiddle) * wordAction leftSuffix 0 =
        (wordScale rightPrefix * wordScale rightMiddle) * wordAction rightSuffix 0 := by
    linarith [empty_zero, false_zero, false_false_zero]
  have suffix_offsets_eq : wordAction leftSuffix 0 = wordAction rightSuffix 0 := by
    exact (mul_left_cancel₀
      (mul_ne_zero (ne_of_gt (wordScale_pos rightPrefix))
        (ne_of_gt (wordScale_pos rightMiddle)))) scaled_suffix_offsets_eq

  refine ⟨?_, ?_, ?_⟩
  · intro state
    calc
      wordAction leftPrefix state =
          wordScale leftPrefix * state + wordAction leftPrefix 0 :=
        wordAction_affine leftPrefix state
      _ = wordScale rightPrefix * state + wordAction rightPrefix 0 := by
        rw [prefix_scales_eq, prefix_offsets_eq]
      _ = wordAction rightPrefix state := (wordAction_affine rightPrefix state).symm
  · intro state
    calc
      wordAction leftMiddle state =
          wordScale leftMiddle * state + wordAction leftMiddle 0 :=
        wordAction_affine leftMiddle state
      _ = wordScale rightMiddle * state + wordAction rightMiddle 0 := by
        rw [middle_scales_eq, middle_offsets_eq]
      _ = wordAction rightMiddle state := (wordAction_affine rightMiddle state).symm
  · intro state
    calc
      wordAction leftSuffix state =
          wordScale leftSuffix * state + wordAction leftSuffix 0 :=
        wordAction_affine leftSuffix state
      _ = wordScale rightSuffix * state + wordAction rightSuffix 0 := by
        rw [suffix_scales_eq, suffix_offsets_eq]
      _ = wordAction rightSuffix state := (wordAction_affine rightSuffix state).symm

/-- Uniform equal-address equality at two fixed cuts splits into three independent affine kernel
pairs. The proof is witnessed by the five finite probes in the preceding theorem. -/
theorem doubleInterleavedAddress_piecewise_actions_eq
    (leftPrefix rightPrefix leftMiddle rightMiddle leftSuffix rightSuffix : List Letter)
    (same_address_actions_eq : ∀ address state,
      wordAction
            (leftPrefix ++ expandAddress address ++ leftMiddle ++
              expandAddress address ++ leftSuffix) state =
        wordAction
            (rightPrefix ++ expandAddress address ++ rightMiddle ++
              expandAddress address ++ rightSuffix) state) :
    (∀ state : ℚ, wordAction leftPrefix state = wordAction rightPrefix state) ∧
      (∀ state : ℚ, wordAction leftMiddle state = wordAction rightMiddle state) ∧
      (∀ state : ℚ, wordAction leftSuffix state = wordAction rightSuffix state) := by
  exact doubleInterleaved_piecewise_actions_eq_of_fiveProbes
    leftPrefix rightPrefix leftMiddle rightMiddle leftSuffix rightSuffix
      (same_address_actions_eq []) (same_address_actions_eq [false])
      (same_address_actions_eq [true]) (same_address_actions_eq [false, false])
      (same_address_actions_eq [true, true])

/-- A raw affine kernel pair placed between two copies of one macro address is an exact address
comparator, without an equal-length hypothesis on the two addresses. -/
theorem sandwichAddress_actions_eq_iff
    (leftKernel rightKernel : List Letter)
    (kernel_actions_eq : ∀ state : ℚ,
      wordAction leftKernel state = wordAction rightKernel state)
    (leftAddress rightAddress : List Bool) :
    (∀ state : ℚ,
      wordAction
            (expandAddress leftAddress ++ leftKernel ++ expandAddress leftAddress) state =
        wordAction
            (expandAddress rightAddress ++ rightKernel ++ expandAddress rightAddress) state) ↔
      leftAddress = rightAddress := by
  constructor
  · intro sandwich_actions_eq
    have kernel_scales_eq := wordScale_eq_of_wordActions_eq
      leftKernel rightKernel kernel_actions_eq
    have kernel_lengths_eq :=
      (length_eq_and_dilateCount_eq_of_wordScale_eq
        leftKernel rightKernel kernel_scales_eq).1
    have sandwich_scales_eq := wordScale_eq_of_wordActions_eq
      (expandAddress leftAddress ++ leftKernel ++ expandAddress leftAddress)
        (expandAddress rightAddress ++ rightKernel ++ expandAddress rightAddress)
        sandwich_actions_eq
    have sandwich_lengths_eq :=
      (length_eq_and_dilateCount_eq_of_wordScale_eq
        (expandAddress leftAddress ++ leftKernel ++ expandAddress leftAddress)
          (expandAddress rightAddress ++ rightKernel ++ expandAddress rightAddress)
          sandwich_scales_eq).1
    have address_lengths_eq : leftAddress.length = rightAddress.length := by
      simp only [List.length_append, expandAddress_length] at sandwich_lengths_eq
      omega
    have at_zero := sandwich_actions_eq 0
    have left_formula := wordAction_doubleInterleave
      [] leftKernel [] leftAddress 0
    have right_formula := wordAction_doubleInterleave
      [] rightKernel [] rightAddress 0
    have empty_scale : wordScale ([] : List Letter) = 1 := rfl
    simp only [List.nil_append, List.append_nil, wordAction, empty_scale, mul_zero,
      add_zero, one_mul] at left_formula right_formula
    rw [left_formula, right_formula] at at_zero
    rw [address_lengths_eq, kernel_scales_eq, kernel_actions_eq 0] at at_zero
    have coefficient_pos :
        0 < 1 + (2 / 5 : ℚ) ^ rightAddress.length * wordScale rightKernel := by
      have product_pos :
          0 < (2 / 5 : ℚ) ^ rightAddress.length * wordScale rightKernel :=
        mul_pos (by positivity) (wordScale_pos rightKernel)
      linarith
    have offsets_eq : addressOffset leftAddress = addressOffset rightAddress := by
      nlinarith
    exact addressOffset_injective offsets_eq
  · rintro rfl
    intro state
    exact wordAction_context kernel_actions_eq
      (expandAddress leftAddress) (expandAddress leftAddress) state

/-- A genuine raw kernel pair yields sandwich words that remain distinct for every two
addresses, while their affine actions agree exactly on the diagonal. -/
theorem sandwichAddress_genuineComparator
    (leftKernel rightKernel : List Letter) (kernel_words_ne : leftKernel ≠ rightKernel)
    (kernel_actions_eq : ∀ state : ℚ,
      wordAction leftKernel state = wordAction rightKernel state)
    (leftAddress rightAddress : List Bool) :
    (expandAddress leftAddress ++ leftKernel ++ expandAddress leftAddress ≠
        expandAddress rightAddress ++ rightKernel ++ expandAddress rightAddress) ∧
      ((∀ state : ℚ,
        wordAction
              (expandAddress leftAddress ++ leftKernel ++ expandAddress leftAddress) state =
          wordAction
              (expandAddress rightAddress ++ rightKernel ++ expandAddress rightAddress) state) ↔
        leftAddress = rightAddress) := by
  have comparator := sandwichAddress_actions_eq_iff
    leftKernel rightKernel kernel_actions_eq leftAddress rightAddress
  refine ⟨?_, comparator⟩
  intro words_eq
  have addresses_eq : leftAddress = rightAddress := comparator.mp (by
    intro state
    rw [words_eq])
  subst rightAddress
  have prefixed_kernels_eq :
      expandAddress leftAddress ++ leftKernel =
        expandAddress leftAddress ++ rightKernel :=
    List.append_left_injective (expandAddress leftAddress) words_eq
  exact kernel_words_ne
    (List.append_right_injective (expandAddress leftAddress) prefixed_kernels_eq)

/-- For a prefix-kernel-free equal-length relation, the two cut positions of a uniform double
insertion agree across the relation and reduce to the two endpoints or the central sandwich. -/
theorem doubleInterleavedAddress_cuts_eq_trichotomy_of_prefixKernelFree
    (left right : List Letter) (length_eq : left.length = right.length)
    (leftFirst leftSecond rightFirst rightSecond : ℕ)
    (left_order : leftFirst ≤ leftSecond) (right_order : rightFirst ≤ rightSecond)
    (leftSecond_le : leftSecond ≤ left.length)
    (rightSecond_le : rightSecond ≤ right.length)
    (prefix_kernel_free : ∀ cut,
      0 < cut → cut < left.length →
      ¬ ∀ state : ℚ,
        wordAction (left.take cut) state = wordAction (right.take cut) state)
    (same_address_actions_eq : ∀ address state,
      wordAction
            (left.take leftFirst ++ expandAddress address ++
              (left.drop leftFirst).take (leftSecond - leftFirst) ++
              expandAddress address ++ left.drop leftSecond) state =
        wordAction
            (right.take rightFirst ++ expandAddress address ++
              (right.drop rightFirst).take (rightSecond - rightFirst) ++
              expandAddress address ++ right.drop rightSecond) state) :
    leftFirst = rightFirst ∧ leftSecond = rightSecond ∧
      ((leftFirst = 0 ∧ leftSecond = 0) ∨
        (leftFirst = 0 ∧ leftSecond = left.length) ∨
        (leftFirst = left.length ∧ leftSecond = left.length)) := by
  have leftFirst_le : leftFirst ≤ left.length := left_order.trans leftSecond_le
  have rightFirst_le : rightFirst ≤ right.length := right_order.trans rightSecond_le
  have piecewise := doubleInterleavedAddress_piecewise_actions_eq
    (left.take leftFirst) (right.take rightFirst)
      ((left.drop leftFirst).take (leftSecond - leftFirst))
      ((right.drop rightFirst).take (rightSecond - rightFirst))
      (left.drop leftSecond) (right.drop rightSecond) same_address_actions_eq
  have first_scales_eq := wordScale_eq_of_wordActions_eq
    (left.take leftFirst) (right.take rightFirst) piecewise.1
  have first_lengths_eq :=
    (length_eq_and_dilateCount_eq_of_wordScale_eq
      (left.take leftFirst) (right.take rightFirst) first_scales_eq).1
  have left_first_length : (left.take leftFirst).length = leftFirst := by
    simp only [List.length_take]
    omega
  have right_first_length : (right.take rightFirst).length = rightFirst := by
    simp only [List.length_take]
    omega
  have first_cuts_eq : leftFirst = rightFirst := by
    rw [left_first_length, right_first_length] at first_lengths_eq
    exact first_lengths_eq
  have suffix_scales_eq := wordScale_eq_of_wordActions_eq
    (left.drop leftSecond) (right.drop rightSecond) piecewise.2.2
  have suffix_lengths_eq :=
    (length_eq_and_dilateCount_eq_of_wordScale_eq
      (left.drop leftSecond) (right.drop rightSecond) suffix_scales_eq).1
  have second_cuts_eq : leftSecond = rightSecond := by
    simp only [List.length_drop] at suffix_lengths_eq
    omega
  subst rightFirst
  subst rightSecond

  have second_prefix_actions_eq : ∀ state : ℚ,
      wordAction (left.take leftSecond) state =
        wordAction (right.take leftSecond) state := by
    intro state
    have left_split :
        left.take leftSecond =
          left.take leftFirst ++
            (left.drop leftFirst).take (leftSecond - leftFirst) := by
      conv_lhs => rw [show leftSecond = leftFirst + (leftSecond - leftFirst) by omega]
      exact List.take_add
    have right_split :
        right.take leftSecond =
          right.take leftFirst ++
            (right.drop leftFirst).take (leftSecond - leftFirst) := by
      conv_lhs => rw [show leftSecond = leftFirst + (leftSecond - leftFirst) by omega]
      exact List.take_add
    rw [left_split, right_split, wordAction_append, wordAction_append]
    calc
      wordAction (left.take leftFirst)
          (wordAction
            ((left.drop leftFirst).take (leftSecond - leftFirst)) state) =
        wordAction (right.take leftFirst)
          (wordAction
            ((left.drop leftFirst).take (leftSecond - leftFirst)) state) :=
        piecewise.1 _
      _ = wordAction (right.take leftFirst)
          (wordAction
            ((right.drop leftFirst).take (leftSecond - leftFirst)) state) := by
        rw [piecewise.2.1 state]

  have first_boundary : leftFirst = 0 ∨ leftFirst = left.length := by
    by_cases first_zero : leftFirst = 0
    · exact Or.inl first_zero
    · right
      by_contra first_ne_full
      have first_pos : 0 < leftFirst := Nat.pos_of_ne_zero first_zero
      have first_lt : leftFirst < left.length :=
        lt_of_le_of_ne leftFirst_le first_ne_full
      exact prefix_kernel_free leftFirst first_pos first_lt piecewise.1
  have second_boundary : leftSecond = 0 ∨ leftSecond = left.length := by
    by_cases second_zero : leftSecond = 0
    · exact Or.inl second_zero
    · right
      by_contra second_ne_full
      have second_pos : 0 < leftSecond := Nat.pos_of_ne_zero second_zero
      have second_lt : leftSecond < left.length :=
        lt_of_le_of_ne leftSecond_le second_ne_full
      exact prefix_kernel_free leftSecond second_pos second_lt second_prefix_actions_eq
  refine ⟨rfl, rfl, ?_⟩
  rcases first_boundary with first_zero | first_full
  · rcases second_boundary with second_zero | second_full
    · exact Or.inl ⟨first_zero, second_zero⟩
    · exact Or.inr (Or.inl ⟨first_zero, second_full⟩)
  · have second_full : leftSecond = left.length := by omega
    exact Or.inr (Or.inr ⟨first_full, second_full⟩)

private theorem isSuffix_of_isSuffix_of_length_le
    {α : Type*} {short long whole : List α}
    (short_suffix : short <:+ whole) (long_suffix : long <:+ whole)
    (length_le : short.length ≤ long.length) :
    short <:+ long := by
  rcases short_suffix with ⟨shortPrefix, short_eq⟩
  rcases long_suffix with ⟨longPrefix, long_eq⟩
  have appended_eq : shortPrefix ++ short = longPrefix ++ long :=
    short_eq.trans long_eq.symm
  rcases List.append_eq_append_iff.mp appended_eq with
    ⟨bridge, _, short_bridge⟩ | ⟨bridge, _, long_bridge⟩
  · have bridge_length_zero : bridge.length = 0 := by
      have lengths_eq := congrArg List.length short_bridge
      simp only [List.length_append] at lengths_eq
      omega
    have bridge_eq_nil := List.eq_nil_of_length_eq_zero bridge_length_zero
    subst bridge
    have short_eq_long : short = long := by simpa using short_bridge
    exact short_eq_long ▸ List.suffix_refl long
  · exact ⟨bridge, long_bridge.symm⟩

/-- A noncommuting reduced `bcbc` fork can contain a common sandwich address only when the
address is shorter than the two data macros together. -/
theorem bcbc_sandwich_address_length_lt
    {α : Type*} (dataB dataC toggle address leftKernel rightKernel : List α)
    (data_noncommute : dataB ++ dataC ≠ dataC ++ dataB)
    (flat_factor :
      dataC ++ toggle ++ dataB ++ dataC ++ dataB =
        address ++ leftKernel ++ address)
    (nested_factor :
      dataB ++ toggle ++ dataC ++ dataB ++ dataC =
        address ++ rightKernel ++ address) :
    address.length < dataB.length + dataC.length := by
  by_contra address_not_short
  have data_length_le : (dataC ++ dataB).length ≤ address.length := by
    simp only [List.length_append]
    omega
  have flat_data_suffix :
      dataC ++ dataB <:+ dataC ++ toggle ++ dataB ++ dataC ++ dataB := by
    refine ⟨dataC ++ toggle ++ dataB, ?_⟩
    simp only [List.append_assoc]
  have flat_address_suffix :
      address <:+ dataC ++ toggle ++ dataB ++ dataC ++ dataB := by
    refine ⟨address ++ leftKernel, ?_⟩
    exact flat_factor.symm
  have flat_tail_suffix : dataC ++ dataB <:+ address :=
    isSuffix_of_isSuffix_of_length_le
      flat_data_suffix flat_address_suffix data_length_le
  have nested_data_suffix :
      dataB ++ dataC <:+ dataB ++ toggle ++ dataC ++ dataB ++ dataC := by
    refine ⟨dataB ++ toggle ++ dataC, ?_⟩
    simp only [List.append_assoc]
  have nested_address_suffix :
      address <:+ dataB ++ toggle ++ dataC ++ dataB ++ dataC := by
    refine ⟨address ++ rightKernel, ?_⟩
    exact nested_factor.symm
  have nested_tail_suffix : dataB ++ dataC <:+ address :=
    isSuffix_of_isSuffix_of_length_le nested_data_suffix nested_address_suffix <| by
      simp only [List.length_append]
      omega
  have tails_suffix : dataC ++ dataB <:+ dataB ++ dataC :=
    isSuffix_of_isSuffix_of_length_le flat_tail_suffix nested_tail_suffix <| by
      simp only [List.length_append]
      omega
  have tails_eq : dataC ++ dataB = dataB ++ dataC :=
    tails_suffix.eq_of_length <| by simp only [List.length_append]; omega
  exact data_noncommute tails_eq.symm

/-- The same physical sandwich factorization forces the kernel relation to be longer than the
toggle macro. -/
theorem bcbc_sandwich_toggle_length_lt_kernel
    {α : Type*} (dataB dataC toggle address leftKernel rightKernel : List α)
    (data_noncommute : dataB ++ dataC ≠ dataC ++ dataB)
    (flat_factor :
      dataC ++ toggle ++ dataB ++ dataC ++ dataB =
        address ++ leftKernel ++ address)
    (nested_factor :
      dataB ++ toggle ++ dataC ++ dataB ++ dataC =
        address ++ rightKernel ++ address) :
    toggle.length < leftKernel.length := by
  have address_lt := bcbc_sandwich_address_length_lt
    dataB dataC toggle address leftKernel rightKernel
      data_noncommute flat_factor nested_factor
  have factor_lengths := congrArg List.length flat_factor
  simp only [List.length_append] at factor_lengths
  omega

end MatrixMortality.MixedPrimeAddressSandwich
