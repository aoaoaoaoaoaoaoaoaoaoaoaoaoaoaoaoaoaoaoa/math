import MatrixMortality.AsymmetricSeparatorLanguage

/-!
# The finite periodic-prefix obstruction

The first three source letters exclude every possible length of a competing period.
The only two lengths not contradicted by commutation itself would begin a lower word with
`0*10` or `0*111`, which the lower-tile language forbids.
-/

namespace MatrixMortality.AsymmetricSeparatorRealization

private theorem prefixes_eq_of_commute {α : Type*}
    (left right first second : List α) (commuting : left ++ right = right ++ left)
    (first_prefix : first <+: left) (second_prefix : second <+: right)
    (lengths : first.length = second.length) : first = second := by
  have first_common := first_prefix.trans (List.prefix_append left right)
  have second_common : second <+: left ++ right := by
    rw [commuting]
    exact second_prefix.trans (List.prefix_append right left)
  exact (List.prefix_of_prefix_length_le first_common second_common lengths.le).eq_of_length lengths

/-- No capped prefix of a lower word supplies a period of a body beginning `bcb`. -/
theorem no_asymmetric_period (zeros : Nat) (tail middle lower : List Bool)
    (avoid_10 : ¬List.replicate zeros false ++ [true, false] <+: lower)
    (avoid_111 : ¬List.replicate zeros false ++ [true, true, true] <+: lower)
    (lower_prefix : middle ++ [false] <+: lower) :
    let block := [true, false] ++ List.replicate zeros false ++ [true]
    let whole := block ++ [true] ++ block ++ tail
    let period := [true, false] ++ middle ++ [true]
    whole ++ period ≠ period ++ whole := by
  let block := [true, false] ++ List.replicate zeros false ++ [true]
  let whole := block ++ [true] ++ block ++ tail
  let period := [true, false] ++ middle ++ [true]
  change whole ++ period ≠ period ++ whole
  intro commuting
  have block_prefix : block <+: whole :=
    ⟨[true] ++ block ++ tail, by simp [whole, List.append_assoc]⟩
  have block_10 : [true, false] <+: block := by simp [block]
  have double_prefix : block ++ [true, true] <+: whole := by
    refine ⟨false :: (List.replicate zeros false ++ [true] ++ tail), ?_⟩
    simp [whole, block, List.append_assoc]
  by_cases short : middle.length < zeros
  · let stem := [true, false] ++ List.replicate (middle.length + 1) false
    have run_prefix : List.replicate (middle.length + 1) false <+:
        List.replicate zeros false := by
      refine List.prefix_replicate_iff.mpr ⟨?_, ?_⟩
      · simp only [List.length_replicate]
        omega
      · simp
    have stem_prefix : stem <+: block := by
      change [true, false] ++ List.replicate (middle.length + 1) false <+:
        [true, false] ++ (List.replicate zeros false ++ [true])
      exact (List.prefix_append_right_inj _).mpr
        (run_prefix.trans (List.prefix_append _ _))
    have equal := prefixes_eq_of_commute whole period stem period commuting
      (stem_prefix.trans block_prefix) (List.prefix_refl _) (by
        simp [stem, period, Nat.add_comm, Nat.add_left_comm])
    have last_equal : (some false : Option Bool) = some true := by
      simpa only [stem, period, List.getLast?_append, List.getLast?_replicate,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
        List.getLast?_singleton, Option.some_or] using congrArg List.getLast? equal
    cases last_equal
  · by_cases same : middle.length = zeros
    · have period_eq : period = block :=
        (prefixes_eq_of_commute whole period block period commuting block_prefix
          (List.prefix_refl _) (by simp [block, period, same])).symm
      have prefixed :
          block ++ (([true] ++ block ++ tail) ++ block) =
            block ++ (block ++ ([true] ++ block ++ tail)) := by
        simpa only [period_eq, whole, List.append_assoc] using commuting
      have shortened := List.append_cancel_left prefixed
      have first_prefix : [true, true] <+: [true] ++ block ++ tail := by simp [block]
      have equal := prefixes_eq_of_commute _ _ [true, true] [true, false]
        shortened first_prefix block_10 rfl
      exact (by decide : ([true, true] : List Bool) ≠ [true, false]) equal
    · by_cases one_more : middle.length = zeros + 1
      · have single_prefix : block ++ [true] <+: whole :=
          ⟨block ++ tail, by simp [whole, List.append_assoc]⟩
        have period_eq : period = block ++ [true] :=
          (prefixes_eq_of_commute whole period (block ++ [true]) period commuting
            single_prefix (List.prefix_refl _) (by
              simp [block, period, one_more, Nat.add_comm, Nat.add_left_comm])).symm
        have expanded : [true, false] ++ (middle ++ [true]) =
            [true, false] ++ (List.replicate zeros false ++ [true, true]) := by
          simpa [period, block, List.append_assoc] using period_eq
        have middle_eq : middle = List.replicate zeros false ++ [true] := by
          simpa using congrArg List.dropLast (List.append_cancel_left expanded)
        exact avoid_10 (by simpa [middle_eq, List.append_assoc] using lower_prefix)
      · by_cases two_more : middle.length = zeros + 2
        · have period_eq : period = block ++ [true, true] :=
            (prefixes_eq_of_commute whole period (block ++ [true, true]) period commuting
              double_prefix (List.prefix_refl _) (by
                simp [block, period, two_more, Nat.add_comm, Nat.add_left_comm])).symm
          let remaining := false :: (List.replicate zeros false ++ [true] ++ tail)
          have whole_eq : whole = period ++ remaining := by
            rw [period_eq]
            simp [whole, block, remaining, List.append_assoc]
          have prefixed : period ++ (remaining ++ period) =
              period ++ (period ++ remaining) := by
            simpa only [whole_eq, List.append_assoc] using commuting
          have shortened := List.append_cancel_left prefixed
          have first_prefix : [false] <+: remaining := by simp [remaining]
          have second_prefix : [true] <+: period := by simp [period]
          have equal := prefixes_eq_of_commute _ _ [false] [true] shortened
            first_prefix second_prefix rfl
          exact (by decide : ([false] : List Bool) ≠ [true]) equal
        · have long : zeros + 3 ≤ middle.length := by omega
          let initial := middle.take (zeros + 3)
          have initial_length : initial.length = zeros + 3 := by
            simp [initial, Nat.min_eq_left long]
          have period_prefix : [true, false] ++ initial <+: period := by
            refine ⟨middle.drop (zeros + 3) ++ [true], ?_⟩
            change ([true, false] ++ middle.take (zeros + 3)) ++
              (middle.drop (zeros + 3) ++ [true]) =
                ([true, false] ++ middle) ++ [true]
            rw [← List.append_assoc, List.append_assoc [true, false], List.take_append_drop]
          have equal := prefixes_eq_of_commute whole period
            (block ++ [true, true]) ([true, false] ++ initial) commuting
            double_prefix period_prefix (by
              simp [block, initial_length, Nat.add_comm, Nat.add_left_comm])
          have expanded : [true, false] ++ (List.replicate zeros false ++ [true, true, true]) =
              [true, false] ++ initial := by simpa [block, List.append_assoc] using equal
          have initial_eq : initial = List.replicate zeros false ++ [true, true, true] :=
            (List.append_cancel_left expanded).symm
          have bad_prefix : List.replicate zeros false ++ [true, true, true] <+: middle := by
            rw [← initial_eq]
            exact List.take_prefix _ _
          exact avoid_111
            ((bad_prefix.trans (List.prefix_append middle [false])).trans lower_prefix)

end MatrixMortality.AsymmetricSeparatorRealization
