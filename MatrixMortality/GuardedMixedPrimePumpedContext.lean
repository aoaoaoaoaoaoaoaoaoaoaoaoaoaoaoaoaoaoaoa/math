import MatrixMortality.GuardedMixedPrimePumpedCuts

/-!
# Literal contextual obstructions for pumped mixed-prime relations

This module applies the uniform pumped-word calculus to the seven certified length-`31 + 2k`
kernel families. It classifies every balanced cut and rejects the moving internal fork cell, then
isolates the finite family-six residue left by the two exceptional static cuts.
-/

set_option autoImplicit false

namespace MatrixMortality.GuardedMixedPrimeFork

open MixedPrimeKernel

/-- The four-letter left prefix is common to every certified pump family and is untouched by
all pump insertions. -/
theorem PumpedKernelFamily.left_take_four (family : PumpedKernelFamily) (power : ℕ) :
    (family.left power).take 4 =
      [Letter.dilate, Letter.translate, Letter.translate, Letter.translate] := by
  have stable : (family.left power).take 4 = (family.left 0).take 4 := by
    simpa only [PumpedKernelFamily.left, Nat.zero_add] using
      pumpAt_add_take_eq family.leftBase family.block family.leftCut 0 power 4
        family.leftCut_le (by cases family <;> decide)
  rw [stable]
  cases family <;> decide

/-- The four-letter right prefix is common to every certified pump family and is untouched by
all pump insertions. -/
theorem PumpedKernelFamily.right_take_four (family : PumpedKernelFamily) (power : ℕ) :
    (family.right power).take 4 =
      [Letter.translate, Letter.translate, Letter.dilate, Letter.dilate] := by
  have stable : (family.right power).take 4 = (family.right 0).take 4 := by
    simpa only [PumpedKernelFamily.right, Nat.zero_add] using
      pumpAt_add_take_eq family.rightBase family.block family.rightCut 0 power 4
        family.rightCut_le (by cases family <;> decide)
  rw [stable]
  cases family <;> decide

private theorem take_drop_eq_of_take_four
    {α : Type*} (word prefixWord : List α) (offset width : ℕ)
    (slice_le : offset + width ≤ 4) (prefix_eq : word.take 4 = prefixWord) :
    (word.drop offset).take width = (prefixWord.drop offset).take width := by
  calc
    (word.drop offset).take width = (word.take (offset + width)).drop offset :=
      List.take_drop
    _ = ((word.take 4).take (offset + width)).drop offset := by
      rw [List.take_take, Nat.min_eq_left slice_le]
    _ = ((prefixWord.take (offset + width)).drop offset) := by rw [prefix_eq]
    _ = (prefixWord.drop offset).take width := List.take_drop.symm

private theorem PumpedKernelFamily.left_drop_one_take_two
    (family : PumpedKernelFamily) (power : ℕ) :
    ((family.left power).drop 1).take 2 = [Letter.translate, Letter.translate] := by
  calc
    _ = ([Letter.dilate, Letter.translate, Letter.translate, Letter.translate].drop 1).take 2 :=
      take_drop_eq_of_take_four _ _ 1 2 (by decide) (family.left_take_four power)
    _ = _ := by decide

private theorem PumpedKernelFamily.left_drop_two_take_two
    (family : PumpedKernelFamily) (power : ℕ) :
    ((family.left power).drop 2).take 2 = [Letter.translate, Letter.translate] := by
  calc
    _ = ([Letter.dilate, Letter.translate, Letter.translate, Letter.translate].drop 2).take 2 :=
      take_drop_eq_of_take_four _ _ 2 2 (by decide) (family.left_take_four power)
    _ = _ := by decide

private theorem PumpedKernelFamily.left_drop_one_take_one
    (family : PumpedKernelFamily) (power : ℕ) :
    ((family.left power).drop 1).take 1 = [Letter.translate] := by
  calc
    _ = ([Letter.dilate, Letter.translate, Letter.translate, Letter.translate].drop 1).take 1 :=
      take_drop_eq_of_take_four _ _ 1 1 (by decide) (family.left_take_four power)
    _ = _ := by decide

private theorem PumpedKernelFamily.right_drop_one_take_two
    (family : PumpedKernelFamily) (power : ℕ) :
    ((family.right power).drop 1).take 2 = [Letter.translate, Letter.dilate] := by
  calc
    _ = ([Letter.translate, Letter.translate, Letter.dilate, Letter.dilate].drop 1).take 2 :=
      take_drop_eq_of_take_four _ _ 1 2 (by decide) (family.right_take_four power)
    _ = _ := by decide

private theorem PumpedKernelFamily.right_drop_two_take_one
    (family : PumpedKernelFamily) (power : ℕ) :
    ((family.right power).drop 2).take 1 = [Letter.dilate] := by
  calc
    _ = ([Letter.translate, Letter.translate, Letter.dilate, Letter.dilate].drop 2).take 1 :=
      take_drop_eq_of_take_four _ _ 2 1 (by decide) (family.right_take_four power)
    _ = _ := by decide

private theorem middle_take_of_contextual_eq
    {α : Type*} (initial middle leftTail context relation rightTail : List α) (width : ℕ)
    (context_le_initial : context.length ≤ initial.length)
    (width_le_middle : width ≤ middle.length)
    (relation_slice_le : initial.length - context.length + width ≤ relation.length)
    (equation : initial ++ middle ++ leftTail = context ++ relation ++ rightTail) :
    middle.take width = (relation.drop (initial.length - context.length)).take width := by
  have sliced := congrArg (fun word => (word.drop initial.length).take width) equation
  have left_slice :
      ((initial ++ middle ++ leftTail).drop initial.length).take width =
        middle.take width := by
    rw [List.append_assoc, List.drop_left,
      List.take_append_of_le_length width_le_middle]
  have relation_offset_le : initial.length - context.length ≤ relation.length := by omega
  have width_le_relation_tail :
      width ≤ (relation.drop (initial.length - context.length)).length := by
    simp only [List.length_drop]
    omega
  have right_slice :
      ((context ++ relation ++ rightTail).drop initial.length).take width =
        (relation.drop (initial.length - context.length)).take width := by
    rw [List.append_assoc, List.drop_append]
    have context_drop : context.drop initial.length = [] := by
      rw [List.drop_eq_nil_iff]
      exact context_le_initial
    rw [context_drop, List.nil_append]
    rw [List.drop_append_of_le_length relation_offset_le]
    rw [List.take_append_of_le_length width_le_relation_tail]
  exact left_slice.symm.trans (sliced.trans right_slice)

private theorem certified_seed_census (family : PumpedKernelFamily) (index : Fin 31) :
    family.PrefixCountEq 0 index ↔
      index.1 = 0 ∨ family.AdmissibleBalancedPrefix 0 index := by
  cases family <;> fin_cases index <;>
    simp [PumpedKernelFamily.AdmissibleBalancedPrefix,
      PumpedKernelFamily.HasPumpedCuts, IsPumpedCut] <;>
    decide

private theorem certified_one_pump_census (family : PumpedKernelFamily) (index : Fin 32) :
    family.PrefixCountEq 1 index ↔
      index.1 = 0 ∨ family.AdmissibleBalancedPrefix 1 index := by
  cases family <;> fin_cases index <;>
    simp [PumpedKernelFamily.AdmissibleBalancedPrefix,
      PumpedKernelFamily.HasPumpedCuts, IsPumpedCut] <;>
    decide

private theorem certified_base_census
    (family : PumpedKernelFamily) (prefixLength : ℕ)
    (prefix_pos : 0 < prefixLength) (prefix_lt : prefixLength < 31) :
    family.PrefixCountEq 0 prefixLength ↔
      family.AdmissibleBalancedPrefix 0 prefixLength := by
  have census := certified_seed_census family ⟨prefixLength, prefix_lt⟩
  constructor
  · intro counts_eq
    rcases census.mp counts_eq with prefix_zero | admissible
    · change prefixLength = 0 at prefix_zero
      omega
    · exact admissible
  · exact fun admissible => census.mpr (Or.inr admissible)

private theorem admissible_positive_iff_one_of_lt_thirtyTwo
    (family : PumpedKernelFamily) (power prefixLength : ℕ) (prefix_lt : prefixLength < 32) :
    family.AdmissibleBalancedPrefix (power + 1) prefixLength ↔
      family.AdmissibleBalancedPrefix 1 prefixLength := by
  constructor
  · intro admissible
    rcases admissible with prefix_three | static | pumped
    · exact Or.inl prefix_three
    · exact Or.inr <| Or.inl static
    · rcases pumped with ⟨has_pumped, index, prefix_eq⟩
      have index_zero : index.1 = 0 := by omega
      exact Or.inr <| Or.inr ⟨has_pumped, ⟨0, by omega⟩, by omega⟩
  · intro admissible
    rcases admissible with prefix_three | static | pumped
    · exact Or.inl prefix_three
    · exact Or.inr <| Or.inl static
    · rcases pumped with ⟨has_pumped, index, prefix_eq⟩
      exact Or.inr <| Or.inr ⟨has_pumped, ⟨index.1, by omega⟩, prefix_eq⟩

private theorem certified_small_census_of_one
    (family : PumpedKernelFamily) (power prefixLength : ℕ)
    (prefix_pos : 0 < prefixLength) (prefix_lt : prefixLength < 32)
    (left_prefix_le : prefixLength ≤ family.leftCut + family.block.length)
    (right_prefix_le : prefixLength ≤ family.rightCut + family.block.length) :
    family.PrefixCountEq (power + 1) prefixLength ↔
      family.AdmissibleBalancedPrefix (power + 1) prefixLength := by
  have left_stable :
      (family.left (power + 1)).take prefixLength =
        (family.left 1).take prefixLength := by
    exact pumpAt_succ_take_eq_one _ _ _ _ _ family.leftCut_le left_prefix_le
  have right_stable :
      (family.right (power + 1)).take prefixLength =
        (family.right 1).take prefixLength := by
    exact pumpAt_succ_take_eq_one _ _ _ _ _ family.rightCut_le right_prefix_le
  have count_stable :
      family.PrefixCountEq (power + 1) prefixLength ↔
        family.PrefixCountEq 1 prefixLength := by
    unfold PumpedKernelFamily.PrefixCountEq
    rw [left_stable, right_stable]
  have one_census := certified_one_pump_census family ⟨prefixLength, prefix_lt⟩
  have admissible_stable :=
    admissible_positive_iff_one_of_lt_thirtyTwo family power prefixLength prefix_lt
  constructor
  · intro counts_eq
    rcases one_census.mp (count_stable.mp counts_eq) with prefix_zero | admissible
    · change prefixLength = 0 at prefix_zero
      omega
    · exact admissible_stable.mpr admissible
  · intro admissible
    exact count_stable.mpr <| one_census.mpr <| Or.inr <| admissible_stable.mp admissible

private theorem fifth_two_thirtyOne_count_ne :
    ¬PumpedKernelFamily.fifth.PrefixCountEq 2 31 := by
  decide

private theorem certified_small_census
    (family : PumpedKernelFamily) (power prefixLength : ℕ)
    (prefix_pos : 0 < prefixLength) (prefix_small : prefixLength < family.shiftBoundary)
    (_prefix_proper : prefixLength < 31 + 2 * (power + 1)) :
    family.PrefixCountEq (power + 1) prefixLength ↔
      family.AdmissibleBalancedPrefix (power + 1) prefixLength := by
  cases family with
  | first =>
      change prefixLength < 32 at prefix_small
      exact certified_small_census_of_one .first power prefixLength prefix_pos
        (by omega) (by
          norm_num [PumpedKernelFamily.leftCut, PumpedKernelFamily.block]
          omega) (by
            norm_num [PumpedKernelFamily.rightCut, PumpedKernelFamily.block]
            omega)

  | second =>
      change prefixLength < 31 at prefix_small
      exact certified_small_census_of_one .second power prefixLength prefix_pos
        (by omega) (by
          norm_num [PumpedKernelFamily.leftCut, PumpedKernelFamily.block]
          omega) (by
            norm_num [PumpedKernelFamily.rightCut, PumpedKernelFamily.block]
            omega)
  | third =>
      change prefixLength < 27 at prefix_small
      exact certified_small_census_of_one .third power prefixLength prefix_pos
        (by omega) (by
          norm_num [PumpedKernelFamily.leftCut, PumpedKernelFamily.block]
          omega) (by
            norm_num [PumpedKernelFamily.rightCut, PumpedKernelFamily.block]
            omega)
  | fourth =>
      change prefixLength < 31 at prefix_small
      exact certified_small_census_of_one .fourth power prefixLength prefix_pos
        (by omega) (by
          norm_num [PumpedKernelFamily.leftCut, PumpedKernelFamily.block]
          omega) (by
            norm_num [PumpedKernelFamily.rightCut, PumpedKernelFamily.block]
            omega)
  | fifth =>
      change prefixLength < 32 at prefix_small
      by_cases below_thirtyOne : prefixLength < 31
      · exact certified_small_census_of_one .fifth power prefixLength prefix_pos
          (by omega) (by
            norm_num [PumpedKernelFamily.leftCut, PumpedKernelFamily.block]
            omega) (by
              norm_num [PumpedKernelFamily.rightCut, PumpedKernelFamily.block]
              omega)
      · have prefix_eq : prefixLength = 31 := by omega
        subst prefixLength
        cases power with
        | zero =>
            have census := certified_one_pump_census .fifth ⟨31, by omega⟩
            constructor
            · intro counts_eq
              rcases census.mp counts_eq with prefix_zero | admissible
              · change (31 : ℕ) = 0 at prefix_zero
                omega
              · exact admissible
            · exact fun admissible => census.mpr (Or.inr admissible)
        | succ power =>
            have left_stable :
                (PumpedKernelFamily.fifth.left (power + 2)).take 31 =
                  (PumpedKernelFamily.fifth.left 2).take 31 := by
              simpa only [PumpedKernelFamily.left, Nat.add_comm] using
                pumpAt_add_take_eq PumpedKernelFamily.fifth.leftBase
                  PumpedKernelFamily.fifth.block PumpedKernelFamily.fifth.leftCut 2 power 31
                  PumpedKernelFamily.fifth.leftCut_le (by decide)
            have right_stable :
                (PumpedKernelFamily.fifth.right (power + 2)).take 31 =
                  (PumpedKernelFamily.fifth.right 2).take 31 := by
              simpa only [PumpedKernelFamily.right, Nat.add_comm] using
                pumpAt_add_take_eq PumpedKernelFamily.fifth.rightBase
                  PumpedKernelFamily.fifth.block PumpedKernelFamily.fifth.rightCut 2 power 31
                  PumpedKernelFamily.fifth.rightCut_le (by decide)
            constructor
            · intro counts_eq
              apply False.elim
              apply fifth_two_thirtyOne_count_ne
              unfold PumpedKernelFamily.PrefixCountEq at counts_eq ⊢
              rwa [left_stable, right_stable] at counts_eq
            · intro admissible
              have admissible_one :=
                (admissible_positive_iff_one_of_lt_thirtyTwo .fifth (power + 1) 31
                  (by omega)).mp admissible
              have one_census := certified_one_pump_census .fifth ⟨31, by omega⟩
              exact False.elim <|
                (by decide : ¬PumpedKernelFamily.fifth.PrefixCountEq 1 31)
                  (one_census.mpr (Or.inr admissible_one))
  | sixth =>
      change prefixLength < 30 at prefix_small
      exact certified_small_census_of_one .sixth power prefixLength prefix_pos
        (by omega) (by
          norm_num [PumpedKernelFamily.leftCut, PumpedKernelFamily.block]
          omega) (by
            norm_num [PumpedKernelFamily.rightCut, PumpedKernelFamily.block]
            omega)
  | seventh =>
      change prefixLength < 30 at prefix_small
      exact certified_small_census_of_one .seventh power prefixLength prefix_pos
        (by omega) (by
          norm_num [PumpedKernelFamily.leftCut, PumpedKernelFamily.block]
          omega) (by
            norm_num [PumpedKernelFamily.rightCut, PumpedKernelFamily.block]
            omega)

private theorem cutThirty_next_ne_of_twoSeed
    (family : PumpedKernelFamily) (power : ℕ) (power_pos : 0 < power)
    (left_prefix_le : 31 ≤ family.leftCut + 2 * family.block.length)
    (right_prefix_le : 31 ≤ family.rightCut + 2 * family.block.length)
    (one_ne : ((family.left 1).drop 30).head? ≠ ((family.right 1).drop 30).head?)
    (two_ne : ((family.left 2).drop 30).head? ≠ ((family.right 2).drop 30).head?) :
    ((family.left power).drop 30).head? ≠ ((family.right power).drop 30).head? := by
  cases power with
  | zero => omega
  | succ predecessor =>
      cases predecessor with
      | zero => exact one_ne
      | succ extraPower =>
          have left_stable :
              (family.left (extraPower + 2)).take 31 =
                (family.left 2).take 31 := by
            simpa only [PumpedKernelFamily.left, Nat.add_comm] using
              pumpAt_add_take_eq family.leftBase family.block family.leftCut 2 extraPower 31
                family.leftCut_le left_prefix_le
          have right_stable :
              (family.right (extraPower + 2)).take 31 =
                (family.right 2).take 31 := by
            simpa only [PumpedKernelFamily.right, Nat.add_comm] using
              pumpAt_add_take_eq family.rightBase family.block family.rightCut 2 extraPower 31
                family.rightCut_le right_prefix_le
          have left_head := head?_drop_eq_of_take_succ_eq 30 left_stable
          have right_head := head?_drop_eq_of_take_succ_eq 30 right_stable
          intro current_eq
          exact two_ne (left_head.symm.trans (current_eq.trans right_head))

private theorem dynamicFamily_cutThirty_next_ne
    (family : PumpedKernelFamily) (power : ℕ)
    (has_pumped : family.HasPumpedCuts) (power_pos : 0 < power) :
    ((family.left power).drop 30).head? ≠ ((family.right power).drop 30).head? := by
  cases family with
  | first =>
      exact cutThirty_next_ne_of_twoSeed .first power power_pos
        (by decide) (by decide) (by decide) (by decide)
  | second =>
      exact cutThirty_next_ne_of_twoSeed .second power power_pos
        (by decide) (by decide) (by decide) (by decide)
  | third => simp [PumpedKernelFamily.HasPumpedCuts] at has_pumped
  | fourth =>
      exact cutThirty_next_ne_of_twoSeed .fourth power power_pos
        (by decide) (by decide) (by decide) (by decide)
  | fifth => simp [PumpedKernelFamily.HasPumpedCuts] at has_pumped
  | sixth =>
      exact cutThirty_next_ne_of_twoSeed .sixth power power_pos
        (by decide) (by decide) (by decide) (by decide)
  | seventh => simp [PumpedKernelFamily.HasPumpedCuts] at has_pumped

private theorem dynamicFamily_leftCut_le_thirty
    (family : PumpedKernelFamily) (has_pumped : family.HasPumpedCuts) :
    family.leftCut ≤ 30 := by
  cases family <;>
    simp [PumpedKernelFamily.HasPumpedCuts, PumpedKernelFamily.leftCut] at has_pumped ⊢

private theorem dynamicFamily_rightCut_le_thirty
    (family : PumpedKernelFamily) (has_pumped : family.HasPumpedCuts) :
    family.rightCut ≤ 30 := by
  cases family <;>
    simp [PumpedKernelFamily.HasPumpedCuts, PumpedKernelFamily.rightCut] at has_pumped ⊢

/-- The letters immediately following every dynamic balanced cut disagree. -/
theorem PumpedKernelFamily.pumpedCut_next_ne
    (family : PumpedKernelFamily) (has_pumped : family.HasPumpedCuts)
    (power : ℕ) (index : Fin power) :
    ((family.left power).drop (30 + 2 * index.1)).head? ≠
      ((family.right power).drop (30 + 2 * index.1)).head? := by
  induction power with
  | zero => exact Fin.elim0 index
  | succ power induction =>
      by_cases index_zero : index.1 = 0
      · simpa only [index_zero, Nat.mul_zero, Nat.add_zero] using
          dynamicFamily_cutThirty_next_ne family (power + 1) has_pumped (by omega)
      · obtain ⟨previous, previous_eq⟩ := Nat.exists_eq_succ_of_ne_zero index_zero
        have previous_lt : previous < power := by omega
        let previousIndex : Fin power := ⟨previous, previous_lt⟩
        have left_shift :
            (family.left (power + 1)).drop ((30 + 2 * previous) + 2) =
              (family.left power).drop (30 + 2 * previous) := by
          simpa only [PumpedKernelFamily.left, PumpedKernelFamily.block_length] using
            pumpAt_succ_drop family.leftBase family.block family.leftCut power
              (30 + 2 * previous) family.leftCut_le
              (by
                have cut_le := dynamicFamily_leftCut_le_thirty family has_pumped
                omega)
        have right_shift :
            (family.right (power + 1)).drop ((30 + 2 * previous) + 2) =
              (family.right power).drop (30 + 2 * previous) := by
          simpa only [PumpedKernelFamily.right, PumpedKernelFamily.block_length] using
            pumpAt_succ_drop family.rightBase family.block family.rightCut power
              (30 + 2 * previous) family.rightCut_le
              (by
                have cut_le := dynamicFamily_rightCut_le_thirty family has_pumped
                omega)
        intro aligned
        apply induction previousIndex
        rw [← left_shift, ← right_shift]
        have cut_eq : 30 + 2 * index.1 = (30 + 2 * previous) + 2 := by omega
        simpa only [cut_eq] using aligned

/-- The letters immediately following the universal balanced cut `3` disagree in every family. -/
theorem PumpedKernelFamily.cutThree_next_ne
    (family : PumpedKernelFamily) (power : ℕ) :
    ((family.left power).drop 3).head? ≠ ((family.right power).drop 3).head? := by
  have left_stable :
      (family.left power).take 4 = (family.left 0).take 4 := by
    simpa only [PumpedKernelFamily.left, Nat.zero_add] using
      pumpAt_add_take_eq family.leftBase family.block family.leftCut 0 power 4
        family.leftCut_le (by
          cases family <;> decide)
  have right_stable :
      (family.right power).take 4 = (family.right 0).take 4 := by
    simpa only [PumpedKernelFamily.right, Nat.zero_add] using
      pumpAt_add_take_eq family.rightBase family.block family.rightCut 0 power 4
        family.rightCut_le (by
          cases family <;> decide)
  have left_head := head?_drop_eq_of_take_succ_eq 3 left_stable
  have right_head := head?_drop_eq_of_take_succ_eq 3 right_stable
  have base_ne :
      ((family.left 0).drop 3).head? ≠ ((family.right 0).drop 3).head? := by
    cases family <;> decide
  intro aligned
  exact base_ne (left_head.symm.trans (aligned.trans right_head))

private theorem sixthFamily_cutTwentyEight_next_ne (power : ℕ) :
    ((PumpedKernelFamily.sixth.left power).drop 28).head? ≠
      ((PumpedKernelFamily.sixth.right power).drop 28).head? := by
  cases power with
  | zero => decide
  | succ power =>
      have left_stable :
          (PumpedKernelFamily.sixth.left (power + 1)).take 29 =
            (PumpedKernelFamily.sixth.left 1).take 29 := by
        exact pumpAt_succ_take_eq_one _ _ _ _ _
          PumpedKernelFamily.sixth.leftCut_le (by decide)
      have right_stable :
          (PumpedKernelFamily.sixth.right (power + 1)).take 29 =
            (PumpedKernelFamily.sixth.right 1).take 29 := by
        exact pumpAt_succ_take_eq_one _ _ _ _ _
          PumpedKernelFamily.sixth.rightCut_le (by decide)
      have left_head := head?_drop_eq_of_take_succ_eq 28 left_stable
      have right_head := head?_drop_eq_of_take_succ_eq 28 right_stable
      have one_ne :
          ((PumpedKernelFamily.sixth.left 1).drop 28).head? ≠
            ((PumpedKernelFamily.sixth.right 1).drop 28).head? := by
        decide
      intro aligned
      exact one_ne (left_head.symm.trans (aligned.trans right_head))

private theorem cutTwentyNine_ne_of_twoSeed
    (family : PumpedKernelFamily) (power : ℕ) (power_pos : 0 < power)
    (left_prefix_le : 30 ≤ family.leftCut + 2 * family.block.length)
    (right_prefix_le : 30 ≤ family.rightCut + 2 * family.block.length)
    (one_ne : ((family.left 1).drop 29).head? ≠ ((family.right 1).drop 29).head?)
    (two_ne : ((family.left 2).drop 29).head? ≠ ((family.right 2).drop 29).head?) :
    ((family.left power).drop 29).head? ≠ ((family.right power).drop 29).head? := by
  cases power with
  | zero => omega
  | succ predecessor =>
      cases predecessor with
      | zero => exact one_ne
      | succ extraPower =>
          have left_stable :
              (family.left (extraPower + 2)).take 30 =
                (family.left 2).take 30 := by
            simpa only [PumpedKernelFamily.left, Nat.add_comm] using
              pumpAt_add_take_eq family.leftBase family.block family.leftCut 2 extraPower 30
                family.leftCut_le left_prefix_le
          have right_stable :
              (family.right (extraPower + 2)).take 30 =
                (family.right 2).take 30 := by
            simpa only [PumpedKernelFamily.right, Nat.add_comm] using
              pumpAt_add_take_eq family.rightBase family.block family.rightCut 2 extraPower 30
                family.rightCut_le right_prefix_le
          have left_head := head?_drop_eq_of_take_succ_eq 29 left_stable
          have right_head := head?_drop_eq_of_take_succ_eq 29 right_stable
          intro current_eq
          exact two_ne (left_head.symm.trans (current_eq.trans right_head))

private theorem dynamicFamily_cutTwentyNine_ne
    (family : PumpedKernelFamily) (power : ℕ)
    (has_pumped : family.HasPumpedCuts) (power_pos : 0 < power) :
    ((family.left power).drop 29).head? ≠ ((family.right power).drop 29).head? := by
  cases family with
  | first =>
      exact cutTwentyNine_ne_of_twoSeed .first power power_pos
        (by decide) (by decide) (by decide) (by decide)
  | second =>
      exact cutTwentyNine_ne_of_twoSeed .second power power_pos
        (by decide) (by decide) (by decide) (by decide)
  | third => simp [PumpedKernelFamily.HasPumpedCuts] at has_pumped
  | fourth =>
      exact cutTwentyNine_ne_of_twoSeed .fourth power power_pos
        (by decide) (by decide) (by decide) (by decide)
  | fifth => simp [PumpedKernelFamily.HasPumpedCuts] at has_pumped
  | sixth =>
      exact cutTwentyNine_ne_of_twoSeed .sixth power power_pos
        (by decide) (by decide) (by decide) (by decide)
  | seventh => simp [PumpedKernelFamily.HasPumpedCuts] at has_pumped

private theorem firstFamily_cutIndexOne_previous_ne (extraPower : ℕ) :
    ((PumpedKernelFamily.first.left (extraPower + 2)).drop 31).head? ≠
      ((PumpedKernelFamily.first.right (extraPower + 2)).drop 31).head? := by
  have left_stable :
      (PumpedKernelFamily.first.left (extraPower + 2)).take 32 =
        (PumpedKernelFamily.first.left 2).take 32 := by
    simpa only [PumpedKernelFamily.left, Nat.add_comm] using
      pumpAt_add_take_eq PumpedKernelFamily.first.leftBase
        PumpedKernelFamily.first.block PumpedKernelFamily.first.leftCut 2 extraPower 32
        PumpedKernelFamily.first.leftCut_le (by decide)
  have right_stable :
      (PumpedKernelFamily.first.right (extraPower + 2)).take 32 =
        (PumpedKernelFamily.first.right 2).take 32 := by
    simpa only [PumpedKernelFamily.right, Nat.add_comm] using
      pumpAt_add_take_eq PumpedKernelFamily.first.rightBase
        PumpedKernelFamily.first.block PumpedKernelFamily.first.rightCut 2 extraPower 32
        PumpedKernelFamily.first.rightCut_le (by decide)
  have left_head := head?_drop_eq_of_take_succ_eq 31 left_stable
  have right_head := head?_drop_eq_of_take_succ_eq 31 right_stable
  have two_ne :
      ((PumpedKernelFamily.first.left 2).drop 31).head? ≠
        ((PumpedKernelFamily.first.right 2).drop 31).head? := by
    decide
  intro aligned
  exact two_ne (left_head.symm.trans (aligned.trans right_head))

/-- The letters immediately preceding every dynamic balanced cut disagree. -/
theorem PumpedKernelFamily.pumpedCut_previous_ne
    (family : PumpedKernelFamily) (has_pumped : family.HasPumpedCuts)
    (power : ℕ) (index : Fin power) :
    ((family.left power).drop (29 + 2 * index.1)).head? ≠
      ((family.right power).drop (29 + 2 * index.1)).head? := by
  induction power with
  | zero => exact Fin.elim0 index
  | succ power induction =>
      by_cases index_zero : index.1 = 0
      · simpa only [index_zero, Nat.mul_zero, Nat.add_zero] using
          dynamicFamily_cutTwentyNine_ne family (power + 1) has_pumped (by omega)
      · obtain ⟨previous, previous_eq⟩ := Nat.exists_eq_succ_of_ne_zero index_zero
        have previous_lt : previous < power := by omega
        let previousIndex : Fin power := ⟨previous, previous_lt⟩
        by_cases exceptional : family = .first ∧ previous = 0
        · rcases exceptional with ⟨family_eq, previous_zero⟩
          subst family
          subst previous
          obtain ⟨extraPower, power_eq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : power ≠ 0)
          subst power
          simpa only [previous_eq, Nat.mul_one, Nat.add_assoc] using
            firstFamily_cutIndexOne_previous_ne extraPower
        · have left_cut_le : family.leftCut ≤ 29 + 2 * previous := by
            cases family <;>
              simp [PumpedKernelFamily.HasPumpedCuts,
                PumpedKernelFamily.leftCut] at has_pumped exceptional ⊢ <;>
              omega
          have right_cut_le : family.rightCut ≤ 29 + 2 * previous := by
            cases family <;>
              simp [PumpedKernelFamily.HasPumpedCuts,
                PumpedKernelFamily.rightCut] at has_pumped ⊢ <;>
              omega
          have left_shift :
              (family.left (power + 1)).drop ((29 + 2 * previous) + 2) =
                (family.left power).drop (29 + 2 * previous) := by
            simpa only [PumpedKernelFamily.left, PumpedKernelFamily.block_length] using
              pumpAt_succ_drop family.leftBase family.block family.leftCut power
                (29 + 2 * previous) family.leftCut_le left_cut_le
          have right_shift :
              (family.right (power + 1)).drop ((29 + 2 * previous) + 2) =
                (family.right power).drop (29 + 2 * previous) := by
            simpa only [PumpedKernelFamily.right, PumpedKernelFamily.block_length] using
              pumpAt_succ_drop family.rightBase family.block family.rightCut power
                (29 + 2 * previous) family.rightCut_le right_cut_le
          intro aligned
          apply induction previousIndex
          rw [← left_shift, ← right_shift]
          have cut_eq : 29 + 2 * index.1 = (29 + 2 * previous) + 2 := by omega
          simpa only [cut_eq] using aligned

/-- The letters immediately preceding the universal balanced cut `3` disagree in every family. -/
theorem PumpedKernelFamily.cutThree_previous_ne
    (family : PumpedKernelFamily) (power : ℕ) :
    ((family.left power).drop 2).head? ≠ ((family.right power).drop 2).head? := by
  have left_stable : (family.left power).take 3 = (family.left 0).take 3 := by
    simpa only [PumpedKernelFamily.left, Nat.zero_add] using
      pumpAt_add_take_eq family.leftBase family.block family.leftCut 0 power 3
        family.leftCut_le (by
          cases family <;> decide)
  have right_stable : (family.right power).take 3 = (family.right 0).take 3 := by
    simpa only [PumpedKernelFamily.right, Nat.zero_add] using
      pumpAt_add_take_eq family.rightBase family.block family.rightCut 0 power 3
        family.rightCut_le (by
          cases family <;> decide)
  have left_head := head?_drop_eq_of_take_succ_eq 2 left_stable
  have right_head := head?_drop_eq_of_take_succ_eq 2 right_stable
  have base_ne :
      ((family.left 0).drop 2).head? ≠ ((family.right 0).drop 2).head? := by
    cases family <;> decide
  intro aligned
  exact base_ne (left_head.symm.trans (aligned.trans right_head))

private theorem sixthFamily_cutTwentySeven_previous_ne (power : ℕ) :
    ((PumpedKernelFamily.sixth.left power).drop 26).head? ≠
      ((PumpedKernelFamily.sixth.right power).drop 26).head? := by
  have left_stable :
      (PumpedKernelFamily.sixth.left power).take 27 =
        (PumpedKernelFamily.sixth.left 0).take 27 := by
    simpa only [PumpedKernelFamily.left, Nat.zero_add] using
      pumpAt_add_take_eq PumpedKernelFamily.sixth.leftBase
        PumpedKernelFamily.sixth.block PumpedKernelFamily.sixth.leftCut 0 power 27
        PumpedKernelFamily.sixth.leftCut_le (by decide)
  have right_stable :
      (PumpedKernelFamily.sixth.right power).take 27 =
        (PumpedKernelFamily.sixth.right 0).take 27 := by
    simpa only [PumpedKernelFamily.right, Nat.zero_add] using
      pumpAt_add_take_eq PumpedKernelFamily.sixth.rightBase
        PumpedKernelFamily.sixth.block PumpedKernelFamily.sixth.rightCut 0 power 27
        PumpedKernelFamily.sixth.rightCut_le (by decide)
  have left_head := head?_drop_eq_of_take_succ_eq 26 left_stable
  have right_head := head?_drop_eq_of_take_succ_eq 26 right_stable
  have base_ne :
      ((PumpedKernelFamily.sixth.left 0).drop 26).head? ≠
        ((PumpedKernelFamily.sixth.right 0).drop 26).head? := by
    decide
  intro aligned
  exact base_ne (left_head.symm.trans (aligned.trans right_head))

private theorem sixthLeftBase_drop_twentyEight :
    PumpedKernelFamily.sixth.leftBase.drop 28 =
      [Letter.dilate, Letter.dilate, Letter.translate] := by
  decide

private theorem sixthRightBase_drop_twentySeven :
    PumpedKernelFamily.sixth.rightBase.drop 27 =
      [Letter.dilate, Letter.translate, Letter.dilate, Letter.dilate] := by
  decide

private theorem sixthFamily_left_drop_twentyEight (power : ℕ) :
    (PumpedKernelFamily.sixth.left power).drop 28 =
      repeatBlock [Letter.dilate, Letter.translate] power ++
        [Letter.dilate, Letter.dilate, Letter.translate] := by
  have dropped := pumpAt_drop_cut PumpedKernelFamily.sixth.leftBase
    PumpedKernelFamily.sixth.block PumpedKernelFamily.sixth.leftCut power
    PumpedKernelFamily.sixth.leftCut_le
  simpa only [PumpedKernelFamily.left, PumpedKernelFamily.leftCut,
    PumpedKernelFamily.block, sixthLeftBase_drop_twentyEight] using dropped

private theorem drop_one_repeatBlock_append_tail (power : ℕ) :
    (repeatBlock [Letter.dilate, Letter.translate] power ++
        [Letter.dilate, Letter.translate, Letter.dilate, Letter.dilate]).drop 1 =
      [Letter.translate] ++ repeatBlock [Letter.dilate, Letter.translate] power ++
        [Letter.dilate, Letter.dilate] := by
  cases power with
  | zero => rfl
  | succ power =>
      simp only [repeatBlock, List.cons_append, List.nil_append, List.drop_succ_cons,
        List.drop_zero]
      have block_commutes :=
        repeatBlock_append_block [Letter.dilate, Letter.translate] power
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        congrArg
          (fun word => [Letter.translate] ++ word ++ [Letter.dilate, Letter.dilate])
          block_commutes

private theorem sixthFamily_right_drop_twentyEight (power : ℕ) :
    (PumpedKernelFamily.sixth.right power).drop 28 =
      [Letter.translate] ++ repeatBlock [Letter.dilate, Letter.translate] power ++
        [Letter.dilate, Letter.dilate] := by
  have at_cut :
      (PumpedKernelFamily.sixth.right power).drop 27 =
        repeatBlock [Letter.dilate, Letter.translate] power ++
          [Letter.dilate, Letter.translate, Letter.dilate, Letter.dilate] := by
    have dropped := pumpAt_drop_cut PumpedKernelFamily.sixth.rightBase
      PumpedKernelFamily.sixth.block PumpedKernelFamily.sixth.rightCut power
      PumpedKernelFamily.sixth.rightCut_le
    simpa only [PumpedKernelFamily.right, PumpedKernelFamily.rightCut,
      PumpedKernelFamily.block, sixthRightBase_drop_twentySeven] using dropped
  calc
    (PumpedKernelFamily.sixth.right power).drop 28 =
        ((PumpedKernelFamily.sixth.right power).drop 27).drop 1 := by
      rw [List.drop_drop]
    _ = _ := by rw [at_cut, drop_one_repeatBlock_append_tail]

/-- The one-letter conjugacy orientation forced by the weak cut-`28` comparable cell is
impossible for either letter. -/
theorem sixthFamily_cutTwentyEight_no_rightConjugacy
    (power : ℕ) (letter : Letter) :
    (PumpedKernelFamily.sixth.left power).drop 28 ++ [letter] ≠
      [letter] ++ (PumpedKernelFamily.sixth.right power).drop 28 := by
  rw [sixthFamily_left_drop_twentyEight, sixthFamily_right_drop_twentyEight]
  cases letter with
  | dilate =>
      intro conjugacy
      have normalized :
          repeatBlock [Letter.dilate, Letter.translate] power ++
              [Letter.dilate, Letter.dilate, Letter.translate, Letter.dilate] =
            repeatBlock [Letter.dilate, Letter.translate] power ++
              [Letter.dilate, Letter.translate, Letter.dilate, Letter.dilate] := by
        calc
          _ = [Letter.dilate, Letter.translate] ++
                repeatBlock [Letter.dilate, Letter.translate] power ++
                  [Letter.dilate, Letter.dilate] := by
              simpa only [List.append_assoc, List.cons_append, List.nil_append] using conjugacy
          _ = repeatBlock [Letter.dilate, Letter.translate] power ++
                [Letter.dilate, Letter.translate] ++
                  [Letter.dilate, Letter.dilate] := by
              simpa only [List.append_assoc] using congrArg
                (fun word => word ++ [Letter.dilate, Letter.dilate])
                (repeatBlock_append_block
                  [Letter.dilate, Letter.translate] power).symm
          _ = _ := by
            simp only [List.append_assoc, List.cons_append, List.nil_append]
      have tail_eq :=
        List.append_right_injective
          (repeatBlock [Letter.dilate, Letter.translate] power) normalized
      exact (by decide :
        [Letter.dilate, Letter.dilate, Letter.translate, Letter.dilate] ≠
          [Letter.dilate, Letter.translate, Letter.dilate, Letter.dilate]) tail_eq
  | translate =>
      cases power with
      | zero => decide
      | succ power =>
          simp [repeatBlock]

private theorem shiftBoundary_ge_three (family : PumpedKernelFamily) :
    3 ≤ family.shiftBoundary := by
  cases family <;> decide

private theorem leftCut_before_shift
    (family : PumpedKernelFamily) (prefixLength : ℕ)
    (boundary_le : family.shiftBoundary ≤ prefixLength) :
    family.leftCut ≤ prefixLength - 2 := by
  cases family <;>
    norm_num [PumpedKernelFamily.shiftBoundary, PumpedKernelFamily.leftCut] at boundary_le ⊢ <;>
    omega

private theorem rightCut_before_shift
    (family : PumpedKernelFamily) (prefixLength : ℕ)
    (boundary_le : family.shiftBoundary ≤ prefixLength) :
    family.rightCut ≤ prefixLength - 2 := by
  cases family <;>
    norm_num [PumpedKernelFamily.shiftBoundary, PumpedKernelFamily.rightCut] at boundary_le ⊢ <;>
    omega

private theorem pumpedCut_shift
    (power prefixLength : ℕ) (prefix_ge : 31 ≤ prefixLength) :
    (prefixLength = 3 ∨ IsPumpedCut (power + 1) prefixLength) ↔
      (prefixLength - 2 = 3 ∨ IsPumpedCut power (prefixLength - 2)) := by
  constructor
  · intro admissible
    rcases admissible with prefix_three | pumped
    · omega
    · rcases pumped with ⟨index, prefix_eq⟩
      by_cases index_zero : index.1 = 0
      · omega
      · obtain ⟨previous, previous_eq⟩ := Nat.exists_eq_succ_of_ne_zero index_zero
        have previous_lt : previous < power := by omega
        refine Or.inr ⟨⟨previous, previous_lt⟩, ?_⟩
        change prefixLength - 2 = 30 + 2 * previous
        omega
  · intro admissible
    rcases admissible with shifted_three | pumped
    · omega
    · rcases pumped with ⟨index, prefix_eq⟩
      have successor_lt : index.1 + 1 < power + 1 := by omega
      refine Or.inr ⟨⟨index.1 + 1, successor_lt⟩, ?_⟩
      change prefixLength = 30 + 2 * (index.1 + 1)
      omega

private theorem sixth_admissible_shift
    (power prefixLength : ℕ) (prefix_ge : 30 ≤ prefixLength) :
    PumpedKernelFamily.sixth.AdmissibleBalancedPrefix (power + 1) prefixLength ↔
      PumpedKernelFamily.sixth.AdmissibleBalancedPrefix power (prefixLength - 2) := by
  simp only [PumpedKernelFamily.AdmissibleBalancedPrefix,
    PumpedKernelFamily.HasPumpedCuts, true_and]
  constructor
  · intro admissible
    rcases admissible with prefix_three | static | pumped
    · omega
    · rcases static with prefix_twenty_seven | prefix_twenty_eight <;> omega
    · rcases pumped with ⟨index, prefix_eq⟩
      by_cases index_zero : index.1 = 0
      · exact Or.inr <| Or.inl <| Or.inr (by omega)
      · obtain ⟨previous, previous_eq⟩ := Nat.exists_eq_succ_of_ne_zero index_zero
        have previous_lt : previous < power := by omega
        refine Or.inr <| Or.inr ⟨⟨previous, previous_lt⟩, ?_⟩
        change prefixLength - 2 = 30 + 2 * previous
        omega
  · intro admissible
    rcases admissible with shifted_three | static | pumped
    · omega
    · rcases static with shifted_twenty_seven | shifted_twenty_eight
      · omega
      · have zero_lt : 0 < power + 1 := by omega
        refine Or.inr <| Or.inr ⟨⟨0, zero_lt⟩, ?_⟩
        change prefixLength = 30
        omega
    · rcases pumped with ⟨index, prefix_eq⟩
      have successor_lt : index.1 + 1 < power + 1 := by omega
      refine Or.inr <| Or.inr ⟨⟨index.1 + 1, successor_lt⟩, ?_⟩
      change prefixLength = 30 + 2 * (index.1 + 1)
      omega

private theorem certified_admissible_shift
    (family : PumpedKernelFamily) (power prefixLength : ℕ)
    (boundary_le : family.shiftBoundary ≤ prefixLength)
    (_prefix_lt : prefixLength < 31 + 2 * (power + 1)) :
    family.AdmissibleBalancedPrefix (power + 1) prefixLength ↔
      family.AdmissibleBalancedPrefix power (prefixLength - 2) := by
  cases family with
  | first =>
      change 32 ≤ prefixLength at boundary_le
      simpa [PumpedKernelFamily.AdmissibleBalancedPrefix,
        PumpedKernelFamily.HasPumpedCuts] using
        pumpedCut_shift power prefixLength (by omega)
  | second =>
      change 31 ≤ prefixLength at boundary_le
      simpa [PumpedKernelFamily.AdmissibleBalancedPrefix,
        PumpedKernelFamily.HasPumpedCuts] using
        pumpedCut_shift power prefixLength boundary_le
  | third =>
      change 27 ≤ prefixLength at boundary_le
      have core : (prefixLength = 3) ↔ prefixLength - 2 = 3 := by omega
      simpa [PumpedKernelFamily.AdmissibleBalancedPrefix,
        PumpedKernelFamily.HasPumpedCuts] using core
  | fourth =>
      change 31 ≤ prefixLength at boundary_le
      simpa [PumpedKernelFamily.AdmissibleBalancedPrefix,
        PumpedKernelFamily.HasPumpedCuts] using
        pumpedCut_shift power prefixLength boundary_le
  | fifth =>
      change 32 ≤ prefixLength at boundary_le
      have core : (prefixLength = 3) ↔ prefixLength - 2 = 3 := by omega
      simpa [PumpedKernelFamily.AdmissibleBalancedPrefix,
        PumpedKernelFamily.HasPumpedCuts] using core
  | sixth =>
      change 30 ≤ prefixLength at boundary_le
      exact sixth_admissible_shift power prefixLength boundary_le
  | seventh =>
      change 30 ≤ prefixLength at boundary_le
      have core : (prefixLength = 3) ↔ prefixLength - 2 = 3 := by omega
      simpa [PumpedKernelFamily.AdmissibleBalancedPrefix,
        PumpedKernelFamily.HasPumpedCuts] using core

/-- Exact dilation-balanced prefix census for all seven certified pump families and every pump
power. The only positive proper cuts are `3`; additionally `27,28` in family six; and
`30,32,...,30+2(k-1)` in families one, two, four, and six. -/
theorem PumpedKernelFamily.balancedPrefix_iff_admissible
    (family : PumpedKernelFamily) (power prefixLength : ℕ) :
    family.BalancedPrefix power prefixLength ↔
      family.AdmissibleBalancedPrefix power prefixLength := by
  exact family.balancedPrefix_iff_of_shift family.shiftBoundary
    (shiftBoundary_ge_three family) (certified_base_census family)
    (certified_small_census family) (leftCut_before_shift family)
    (rightCut_before_shift family) (certified_admissible_shift family)
    power prefixLength

/-- Disjoint semantic cases left by the exact Parikh census. -/
inductive PumpedBalancedCutCase
    (family : PumpedKernelFamily) (power prefixLength : ℕ) : Prop
  | three (prefix_eq : prefixLength = 3)
  | sixthTwentySeven
      (family_eq : family = .sixth) (prefix_eq : prefixLength = 27)
  | sixthTwentyEight
      (family_eq : family = .sixth) (prefix_eq : prefixLength = 28)
  | pumped
      (has_pumped : family.HasPumpedCuts) (index : Fin power)
      (prefix_eq : prefixLength = 30 + 2 * index.1)

/-- Every positive proper dilation-balanced prefix belongs to one of the explicit census cases. -/
theorem PumpedKernelFamily.balancedPrefix_cases
    (family : PumpedKernelFamily) (power prefixLength : ℕ)
    (balanced : family.BalancedPrefix power prefixLength) :
    PumpedBalancedCutCase family power prefixLength := by
  have admissible := (family.balancedPrefix_iff_admissible power prefixLength).mp balanced
  rcases admissible with prefix_three | static | pumped
  · exact .three prefix_three
  · rcases static with ⟨family_eq, prefix_twenty_seven | prefix_twenty_eight⟩
    · exact .sixthTwentySeven family_eq prefix_twenty_seven
    · exact .sixthTwentyEight family_eq prefix_twenty_eight
  · rcases pumped with ⟨has_pumped, index, prefix_eq⟩
    exact .pumped has_pumped index prefix_eq

/-- If the next letters agree at a positive proper balanced cut, the cut is necessarily the
exceptional family-six cut `27`. All universal, dynamic, and cut-`28` cases disagree locally. -/
theorem PumpedKernelFamily.alignedNext_of_balancedPrefix
    (family : PumpedKernelFamily) (power prefixLength : ℕ)
    (balanced : family.BalancedPrefix power prefixLength)
    (aligned_next :
      ((family.left power).drop prefixLength).head? =
        ((family.right power).drop prefixLength).head?) :
    family = .sixth ∧ prefixLength = 27 := by
  have cut_case := family.balancedPrefix_cases power prefixLength balanced
  cases cut_case with
  | three prefix_eq =>
      subst prefixLength
      exact False.elim (family.cutThree_next_ne power aligned_next)
  | sixthTwentySeven family_eq prefix_eq => exact ⟨family_eq, prefix_eq⟩
  | sixthTwentyEight family_eq prefix_eq =>
      subst family
      subst prefixLength
      exact False.elim (sixthFamily_cutTwentyEight_next_ne power aligned_next)
  | pumped has_pumped index prefix_eq =>
      subst prefixLength
      exact False.elim (family.pumpedCut_next_ne has_pumped power index aligned_next)

/-- If the immediately preceding letters agree at a positive proper balanced cut, the cut is
necessarily family six's static cut `28`. -/
theorem PumpedKernelFamily.alignedPrevious_of_balancedPrefix
    (family : PumpedKernelFamily) (power prefixLength : ℕ)
    (balanced : family.BalancedPrefix power prefixLength)
    (aligned_previous :
      ((family.left power).drop (prefixLength - 1)).head? =
        ((family.right power).drop (prefixLength - 1)).head?) :
    family = .sixth ∧ prefixLength = 28 := by
  have cut_case := family.balancedPrefix_cases power prefixLength balanced
  cases cut_case with
  | three prefix_eq =>
      subst prefixLength
      exact False.elim (family.cutThree_previous_ne power (by simpa using aligned_previous))
  | sixthTwentySeven family_eq prefix_eq =>
      subst family
      subst prefixLength
      exact False.elim (sixthFamily_cutTwentySeven_previous_ne power
        (by simpa using aligned_previous))
  | sixthTwentyEight family_eq prefix_eq => exact ⟨family_eq, prefix_eq⟩
  | pumped has_pumped index prefix_eq =>
      have previous_eq : prefixLength - 1 = 29 + 2 * index.1 := by omega
      rw [previous_eq] at aligned_previous
      exact False.elim
        (family.pumpedCut_previous_ne has_pumped power index aligned_previous)

/-- No balanced cut can align both of its two immediately preceding letters. At the only cut
where the last letters agree (family six, cut `28`), the penultimate letters disagree. -/
theorem PumpedKernelFamily.no_twoPreviousAligned_balancedPrefix
    (family : PumpedKernelFamily) (power prefixLength : ℕ)
    (balanced : family.BalancedPrefix power prefixLength)
    (aligned_previous :
      ((family.left power).drop (prefixLength - 1)).head? =
        ((family.right power).drop (prefixLength - 1)).head?)
    (aligned_two_previous :
      ((family.left power).drop (prefixLength - 2)).head? =
        ((family.right power).drop (prefixLength - 2)).head?) : False := by
  have exceptional :=
    family.alignedPrevious_of_balancedPrefix power prefixLength balanced aligned_previous
  rcases exceptional with ⟨family_eq, prefix_eq⟩
  subst family
  subst prefixLength
  exact sixthFamily_cutTwentySeven_previous_ne power (by simpa using aligned_two_previous)

/-- The internal/internal arithmetic cell is impossible when a family's census has only the
universal cut `3`. This closes that cell for families three, five, and seven. -/
theorem no_internalInternal_of_noPumpedCuts
    (family : PumpedKernelFamily) (power xLength yLength zLength contextPrefixLength : ℕ)
    (no_pumped : ¬family.HasPumpedCuts) (not_sixth : family ≠ .sixth)
    (z_pos : 0 < zLength)
    (prefix_internal_x : contextPrefixLength < xLength)
    (prefix_internal_y : contextPrefixLength < yLength)
    (core_le_fork : 31 + 2 * power ≤ 2 * xLength + 2 * yLength + zLength)
    (balanced : family.BalancedPrefix power
      (xLength + yLength + zLength - contextPrefixLength)) : False := by
  have cut_case := family.balancedPrefix_cases power
    (xLength + yLength + zLength - contextPrefixLength) balanced
  cases cut_case with
  | three prefix_eq => omega
  | sixthTwentySeven family_eq _ => exact not_sixth family_eq
  | sixthTwentyEight family_eq _ => exact not_sixth family_eq
  | pumped has_pumped _ _ => exact no_pumped has_pumped

/-- Family three has no internal/internal contextual placement. -/
theorem no_thirdFamily_internalInternal
    (power xLength yLength zLength contextPrefixLength : ℕ)
    (z_pos : 0 < zLength)
    (prefix_internal_x : contextPrefixLength < xLength)
    (prefix_internal_y : contextPrefixLength < yLength)
    (core_le_fork : 31 + 2 * power ≤ 2 * xLength + 2 * yLength + zLength)
    (balanced : PumpedKernelFamily.third.BalancedPrefix power
      (xLength + yLength + zLength - contextPrefixLength)) : False := by
  exact no_internalInternal_of_noPumpedCuts .third power xLength yLength zLength
    contextPrefixLength (by simp [PumpedKernelFamily.HasPumpedCuts]) (by decide) z_pos
    prefix_internal_x prefix_internal_y core_le_fork balanced

/-- Family five has no internal/internal contextual placement. -/
theorem no_fifthFamily_internalInternal
    (power xLength yLength zLength contextPrefixLength : ℕ)
    (z_pos : 0 < zLength)
    (prefix_internal_x : contextPrefixLength < xLength)
    (prefix_internal_y : contextPrefixLength < yLength)
    (core_le_fork : 31 + 2 * power ≤ 2 * xLength + 2 * yLength + zLength)
    (balanced : PumpedKernelFamily.fifth.BalancedPrefix power
      (xLength + yLength + zLength - contextPrefixLength)) : False := by
  exact no_internalInternal_of_noPumpedCuts .fifth power xLength yLength zLength
    contextPrefixLength (by simp [PumpedKernelFamily.HasPumpedCuts]) (by decide) z_pos
    prefix_internal_x prefix_internal_y core_le_fork balanced

/-- Family seven has no internal/internal contextual placement. -/
theorem no_seventhFamily_internalInternal
    (power xLength yLength zLength contextPrefixLength : ℕ)
    (z_pos : 0 < zLength)
    (prefix_internal_x : contextPrefixLength < xLength)
    (prefix_internal_y : contextPrefixLength < yLength)
    (core_le_fork : 31 + 2 * power ≤ 2 * xLength + 2 * yLength + zLength)
    (balanced : PumpedKernelFamily.seventh.BalancedPrefix power
      (xLength + yLength + zLength - contextPrefixLength)) : False := by
  exact no_internalInternal_of_noPumpedCuts .seventh power xLength yLength zLength
    contextPrefixLength (by simp [PumpedKernelFamily.HasPumpedCuts]) (by decide) z_pos
    prefix_internal_x prefix_internal_y core_le_fork balanced

/-- Exact length classification for a moving internal/internal cut and complementary cut `3`.
Writing the moving cut as `30 + 2i` in a word of length `31 + 2k`, the complementary suffix gap
is `31 + 2k - (30 + 2i)`. If both contexts end strictly inside both nonempty macros, the cut is
terminal (`i + 1 = k`) and the macro/context lengths are one of three explicit assignments. -/
theorem dynamicInternal_length_classification
    (power index xLength yLength contextPrefixLength contextSuffixLength : ℕ)
    (index_lt : index < power)
    (prefix_balance : contextPrefixLength + 3 = xLength + yLength)
    (suffix_balance :
      contextSuffixLength + (31 + 2 * power - (30 + 2 * index)) =
        xLength + yLength)
    (prefix_internal_x : contextPrefixLength < xLength)
    (prefix_internal_y : contextPrefixLength < yLength)
    (suffix_internal_x : contextSuffixLength < xLength)
    (suffix_internal_y : contextSuffixLength < yLength) :
    index + 1 = power ∧
      ((xLength = 1 ∧ yLength = 2 ∧
          contextPrefixLength = 0 ∧ contextSuffixLength = 0) ∨
        (xLength = 2 ∧ yLength = 1 ∧
          contextPrefixLength = 0 ∧ contextSuffixLength = 0) ∨
        (xLength = 2 ∧ yLength = 2 ∧
          contextPrefixLength = 1 ∧ contextSuffixLength = 1)) := by
  omega

/-- At family six's exceptional cut `27`, the exact tail-length classification makes every
internal/internal candidate arithmetically empty above pump power `11`. The remaining powers
`0 ≤ k ≤ 11` are the finite residue requiring a separate assignment certificate. -/
theorem sixthFamily_cutTwentySeven_power_le_eleven
    (power xLength yLength zLength contextPrefixLength : ℕ)
    (tail_lengths :
      (xLength = 2 * power + 3 ∧ yLength = 2 * power + 2) ∨
        (xLength = 2 * power + 2 ∧ yLength = 2 * power + 3))
    (z_pos : 0 < zLength)
    (prefix_internal_x : contextPrefixLength < xLength)
    (prefix_internal_y : contextPrefixLength < yLength)
    (cut_eq : xLength + yLength + zLength - contextPrefixLength = 27) :
    power ≤ 11 := by
  rcases tail_lengths with forward | reverse
  · omega
  · omega

/-- The weak comparable family-six cut `27` is likewise empty above power `11` once its exact
suffix arithmetic gives `2k + q = 23`. -/
theorem sixthFamily_weakCutTwentySeven_power_le_eleven
    (power suffixLength : ℕ) (suffix_eq : 2 * power + suffixLength = 23) :
    power ≤ 11 := by
  omega

/-- The fixed `25`-letter block adjacent to family six's weak cut `27` disagrees for every pump
power. Both compared blocks lie strictly before their respective pump insertion sites, so the
claim reduces to the audited length-`31` seed. -/
theorem sixthFamily_weakCutTwentySeven_block_ne (power : ℕ) :
    ((PumpedKernelFamily.sixth.left power).drop 3).take 25 ≠
      (PumpedKernelFamily.sixth.right power).take 25 := by
  have left_stable :
      (PumpedKernelFamily.sixth.left power).take 28 =
        (PumpedKernelFamily.sixth.left 0).take 28 := by
    simpa only [PumpedKernelFamily.left, Nat.zero_add] using
      pumpAt_add_take_eq PumpedKernelFamily.sixth.leftBase
        PumpedKernelFamily.sixth.block PumpedKernelFamily.sixth.leftCut 0 power 28
        PumpedKernelFamily.sixth.leftCut_le (by decide)
  have left_slice_stable :
      ((PumpedKernelFamily.sixth.left power).drop 3).take 25 =
        ((PumpedKernelFamily.sixth.left 0).drop 3).take 25 := by
    have dropped := congrArg (List.drop 3) left_stable
    simpa only [List.drop_take] using dropped
  have right_stable :
      (PumpedKernelFamily.sixth.right power).take 25 =
        (PumpedKernelFamily.sixth.right 0).take 25 := by
    simpa only [PumpedKernelFamily.right, Nat.zero_add] using
      pumpAt_add_take_eq PumpedKernelFamily.sixth.rightBase
        PumpedKernelFamily.sixth.block PumpedKernelFamily.sixth.rightCut 0 power 25
        PumpedKernelFamily.sixth.rightCut_le (by decide)
  have base_ne :
      ((PumpedKernelFamily.sixth.left 0).drop 3).take 25 ≠
        (PumpedKernelFamily.sixth.right 0).take 25 := by
    decide
  intro aligned
  exact base_ne (left_slice_stable.symm.trans (aligned.trans right_stable))

/-- One literal two-sided context realization of the macro fork equation around a certified
pump-family relation. No quotient closure or multi-rewrite inference is present. -/
structure LiteralPumpedContextFork (family : PumpedKernelFamily) (power : ℕ) where
  /-- First data macro in the reduced fork. -/
  x : List Letter
  /-- Second data macro in the reduced fork. -/
  y : List Letter
  /-- Toggle macro between the two data occurrences. -/
  z : List Letter
  /-- Common literal context before the pumped relation. -/
  contextPrefix : List Letter
  /-- Common literal context after the pumped relation. -/
  contextSuffix : List Letter
  x_nonempty : x ≠ []
  y_nonempty : y ≠ []
  z_nonempty : z ≠ []
  leftEquation :
    y ++ z ++ x ++ y ++ x = contextPrefix ++ family.left power ++ contextSuffix
  rightEquation :
    x ++ z ++ y ++ x ++ y = contextPrefix ++ family.right power ++ contextSuffix

/-- A moving balanced cut paired with the universal complementary cut `3` cannot occur in a
literal internal/internal contextual fork. Length arithmetic leaves three terminal assignments;
the common fixed prefixes `DTTT` and `TTDD` give a contradictory one- or two-letter slice of
`z` in each assignment. -/
theorem no_dynamicInternal_literalPumpedContextFork
    {family : PumpedKernelFamily} {power index : ℕ}
    (fork : LiteralPumpedContextFork family power)
    (index_lt : index < power)
    (prefix_balance :
      fork.contextPrefix.length + 3 = fork.x.length + fork.y.length)
    (suffix_balance :
      fork.contextSuffix.length + (31 + 2 * power - (30 + 2 * index)) =
        fork.x.length + fork.y.length)
    (z_balance : fork.z.length + 3 = 30 + 2 * index)
    (prefix_internal_x : fork.contextPrefix.length < fork.x.length)
    (prefix_internal_y : fork.contextPrefix.length < fork.y.length)
    (suffix_internal_x : fork.contextSuffix.length < fork.x.length)
    (suffix_internal_y : fork.contextSuffix.length < fork.y.length) : False := by
  have classified := dynamicInternal_length_classification power index fork.x.length
    fork.y.length fork.contextPrefix.length fork.contextSuffix.length index_lt prefix_balance
    suffix_balance prefix_internal_x prefix_internal_y suffix_internal_x suffix_internal_y
  have z_two : 2 ≤ fork.z.length := by omega
  have left_equation :
      fork.y ++ fork.z ++ (fork.x ++ fork.y ++ fork.x) =
        fork.contextPrefix ++ family.left power ++ fork.contextSuffix := by
    simpa only [List.append_assoc] using fork.leftEquation
  have right_equation :
      fork.x ++ fork.z ++ (fork.y ++ fork.x ++ fork.y) =
        fork.contextPrefix ++ family.right power ++ fork.contextSuffix := by
    simpa only [List.append_assoc] using fork.rightEquation
  rcases classified.2 with forward | reverse | equal
  · rcases forward with ⟨x_length, y_length, prefix_length, _suffix_length⟩
    have left_slice := middle_take_of_contextual_eq fork.y fork.z
      (fork.x ++ fork.y ++ fork.x) fork.contextPrefix (family.left power)
      fork.contextSuffix 2 (by omega) z_two (by simp; omega) left_equation
    have right_slice := middle_take_of_contextual_eq fork.x fork.z
      (fork.y ++ fork.x ++ fork.y) fork.contextPrefix (family.right power)
      fork.contextSuffix 2 (by omega) z_two (by simp; omega) right_equation
    have z_left :
        fork.z.take 2 = ((family.left power).drop 2).take 2 := by
      simpa only [y_length, prefix_length] using left_slice
    have z_right :
        fork.z.take 2 = ((family.right power).drop 1).take 2 := by
      simpa only [x_length, prefix_length] using right_slice
    have fixed_left := z_left.trans (family.left_drop_two_take_two power)
    have fixed_right := z_right.trans (family.right_drop_one_take_two power)
    exact (by decide : [Letter.translate, Letter.translate] ≠
      [Letter.translate, Letter.dilate]) (fixed_left.symm.trans fixed_right)
  · rcases reverse with ⟨x_length, y_length, prefix_length, _suffix_length⟩
    have z_one : 1 ≤ fork.z.length := by omega
    have left_slice := middle_take_of_contextual_eq fork.y fork.z
      (fork.x ++ fork.y ++ fork.x) fork.contextPrefix (family.left power)
      fork.contextSuffix 1 (by omega) z_one (by simp; omega) left_equation
    have right_slice := middle_take_of_contextual_eq fork.x fork.z
      (fork.y ++ fork.x ++ fork.y) fork.contextPrefix (family.right power)
      fork.contextSuffix 1 (by omega) z_one (by simp; omega) right_equation
    have z_left :
        fork.z.take 1 = ((family.left power).drop 1).take 1 := by
      simpa only [y_length, prefix_length] using left_slice
    have z_right :
        fork.z.take 1 = ((family.right power).drop 2).take 1 := by
      simpa only [x_length, prefix_length] using right_slice
    have fixed_left := z_left.trans (family.left_drop_one_take_one power)
    have fixed_right := z_right.trans (family.right_drop_two_take_one power)
    exact (by decide : [Letter.translate] ≠ [Letter.dilate])
      (fixed_left.symm.trans fixed_right)
  · rcases equal with ⟨x_length, y_length, prefix_length, _suffix_length⟩
    have left_slice := middle_take_of_contextual_eq fork.y fork.z
      (fork.x ++ fork.y ++ fork.x) fork.contextPrefix (family.left power)
      fork.contextSuffix 2 (by omega) z_two (by simp; omega) left_equation
    have right_slice := middle_take_of_contextual_eq fork.x fork.z
      (fork.y ++ fork.x ++ fork.y) fork.contextPrefix (family.right power)
      fork.contextSuffix 2 (by omega) z_two (by simp; omega) right_equation
    have z_left :
        fork.z.take 2 = ((family.left power).drop 1).take 2 := by
      simpa only [y_length, prefix_length] using left_slice
    have z_right :
        fork.z.take 2 = ((family.right power).drop 1).take 2 := by
      simpa only [x_length, prefix_length] using right_slice
    have fixed_left := z_left.trans (family.left_drop_one_take_two power)
    have fixed_right := z_right.trans (family.right_drop_one_take_two power)
    exact (by decide : [Letter.translate, Letter.translate] ≠
      [Letter.translate, Letter.dilate]) (fixed_left.symm.trans fixed_right)

/-- Exact finite residue isolated by the family-six cut-`27` tail classification. The structure
contains the literal fork equations and both internality inequalities; its numerical fields are
the assignment solver's proved tail classification, not an assertion that such a fork exists. -/
structure SixthFamilyCutTwentySevenResidue (power : ℕ)
    extends LiteralPumpedContextFork .sixth power where
  prefix_internal_x : contextPrefix.length < x.length
  prefix_internal_y : contextPrefix.length < y.length
  suffix_internal_x : contextSuffix.length < x.length
  suffix_internal_y : contextSuffix.length < y.length
  cut_eq : x.length + y.length + z.length - contextPrefix.length = 27
  suffix_length_eq : contextSuffix.length = 2 * power + 1
  tail_lengths :
    (x.length = 2 * power + 3 ∧ y.length = 2 * power + 2) ∨
      (x.length = 2 * power + 2 ∧ y.length = 2 * power + 3)

/-- Every literal cut-`27` residue lies in the twelve-power finite audit window. -/
theorem SixthFamilyCutTwentySevenResidue.power_le_eleven
    {power : ℕ} (residue : SixthFamilyCutTwentySevenResidue power) :
    power ≤ 11 := by
  exact sixthFamily_cutTwentySeven_power_le_eleven power residue.x.length residue.y.length
    residue.z.length residue.contextPrefix.length residue.tail_lengths
    (List.length_pos_of_ne_nil residue.z_nonempty) residue.prefix_internal_x
    residue.prefix_internal_y residue.cut_eq

/-- Separately auditable finite premise: reject the twelve literal residue powers `0 ≤ k ≤ 11`.
The infinite argument depends on no larger assignment enumeration. -/
def SixthFamilyCutTwentySevenFiniteRejection : Prop :=
  ∀ power, power ≤ 11 → SixthFamilyCutTwentySevenResidue power → False

/-- A finite rejection certificate closes the sole cut-`27` residue left by the uniform
arithmetic reduction. -/
theorem no_sixthFamily_cutTwentySeven_residue
    (finite_rejection : SixthFamilyCutTwentySevenFiniteRejection)
    {power : ℕ} (residue : SixthFamilyCutTwentySevenResidue power) : False := by
  exact finite_rejection power residue.power_le_eleven residue

end MatrixMortality.GuardedMixedPrimeFork
