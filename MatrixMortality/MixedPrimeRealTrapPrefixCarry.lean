import MatrixMortality.MixedPrimeRealTrapDeterminant

/-!
# Prefix-carry expansion for same-length shell collisions

The cleared fixed-source equation is a weighted suffix balance, while the cleared target
determinant is a sum of complementary prefix carries. A unique lowest prefix carry fixes the
determinant below the accepted depth; acceptance therefore forces a later bounded cancellation.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation
open PeriodicShell

private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The cleared offset is the weighted sum of all proper suffix gains. -/
theorem shellOffset_eq_sum_dropGain :
    ∀ waits : List ℕ,
      shellOffset waits =
        ∑ cut ∈ Finset.range waits.length,
          (5 : ℚ) ^ cut * shellGain (waits.drop (cut + 1))
  | [] => by
      have run_nil : shellRun [] (0 : ℚ) = 0 := rfl
      rw [shellOffset, shellIntercept, run_nil]
      simp
  | wait :: waits => by
      rw [shellOffset_cons]
      simp only [List.length_cons]
      rw [Finset.sum_range_succ']
      simp only [List.drop_succ_cons, pow_zero, one_mul]
      rw [shellOffset_eq_sum_dropGain waits]
      calc
        shellGain waits +
            5 * ∑ cut ∈ Finset.range waits.length,
              5 ^ cut * shellGain (waits.drop (cut + 1)) =
            5 * ∑ cut ∈ Finset.range waits.length,
              5 ^ cut * shellGain (waits.drop (cut + 1)) + shellGain waits :=
          add_comm _ _
        _ = ∑ cut ∈ Finset.range waits.length,
              5 ^ (cut + 1) * shellGain (waits.drop (cut + 1)) + shellGain waits := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro cut cut_mem
          rw [pow_succ']
          ring

/-- Cleared gains multiply under schedule concatenation. -/
theorem shellGain_append (left right : List ℕ) :
    shellGain (left ++ right) = shellGain left * shellGain right := by
  simp only [shellGain, List.length_append, List.sum_append, pow_add]
  ring

/-- The `cut`-indexed summand in the cleared determinant expansion. -/
def shellPrefixDeterminantTerm (left right : List ℕ) (cut : ℕ) : ℚ :=
  5 ^ cut *
    (shellGain left * shellGain (right.drop (cut + 1)) -
      shellGain right * shellGain (left.drop (cut + 1)))

/-- The `cut`-indexed summand in the cleared fixed-source balance. -/
def shellSuffixBalanceTerm (left right : List ℕ) (cut : ℕ) : ℚ :=
  5 ^ cut *
    (shellGain (left.drop (cut + 1)) - shellGain (right.drop (cut + 1)))

/-- Equal-length endpoint equality is one exact weighted balance over aligned suffix gains. -/
theorem shellRun_eq_iff_weightedSuffixBalance
    {left right : List ℕ} (length_eq : left.length = right.length) (source : ℚ) :
    shellRun left source = shellRun right source ↔
      source * (shellGain left - shellGain right) +
          ∑ cut ∈ Finset.range left.length,
            shellSuffixBalanceTerm left right cut = 0 := by
  rw [shellRun_eq_iff_clearedRun_eq_of_length_eq length_eq source,
    shellOffset_eq_sum_dropGain, shellOffset_eq_sum_dropGain, ← length_eq]
  simp only [shellSuffixBalanceTerm, mul_sub, Finset.sum_sub_distrib]
  constructor
  · intro equality
    linear_combination equality
  · intro equality
    linear_combination equality

private theorem shellGain_lt_of_sum_gt
    {left right : List ℕ} (length_eq : left.length = right.length)
    (sum_gt : right.sum < left.sum) :
    shellGain left < shellGain right := by
  rw [shellGain, shellGain, ← length_eq]
  exact mul_lt_mul_of_pos_left
    (pow_right_strictAnti₀ (show 0 < (2 / 3 : ℚ) by norm_num)
      (show (2 / 3 : ℚ) < 1 by norm_num) sum_gt)
    (by positivity)

/-- The cross-grade collision source is the ratio of the cleared offset and gain gaps. -/
theorem collisionSource_eq_clearedBalance
    {left right : List ℕ} (length_eq : left.length = right.length)
    (sum_ne : left.sum ≠ right.sum) :
    collisionSource left right =
      (shellOffset left - shellOffset right) / (shellGain right - shellGain left) := by
  have slope_ne : shellSlope left ≠ shellSlope right := by
    intro slope_eq
    exact sum_ne ((shellSlope_eq_iff_length_sum left right).1 slope_eq).2
  have power_ne : (5 : ℚ) ^ left.length ≠ 0 := by positivity
  have left_intercept_eq :
      shellIntercept left = shellOffset left / 5 ^ left.length := by
    rw [shellOffset]
    exact (mul_div_cancel_left₀ (shellIntercept left) power_ne).symm
  have right_intercept_eq :
      shellIntercept right = shellOffset right / 5 ^ left.length := by
    rw [shellOffset, ← length_eq]
    exact (mul_div_cancel_left₀ (shellIntercept right) power_ne).symm
  rw [collisionSource, left_intercept_eq, right_intercept_eq,
    shellSlope_eq_gain_div, shellSlope_eq_gain_div, ← length_eq]
  have gain_difference_ne : shellGain left - shellGain right ≠ 0 := by
    intro gain_difference_zero
    have gain_eq : shellGain left = shellGain right := sub_eq_zero.mp gain_difference_zero
    apply slope_ne
    rw [shellSlope_eq_gain_div, shellSlope_eq_gain_div, ← length_eq, gain_eq]
  have gain_reverse_ne : shellGain right - shellGain left ≠ 0 := by
    intro gain_reverse_zero
    apply gain_difference_ne
    linarith
  field_simp [power_ne, gain_difference_ne, gain_reverse_ne]
  ring

/-- The cleared offset gap lies in one exact corridor precisely when the oriented collision
source lies in the closed real trap. -/
theorem collisionSource_mem_realTrap_iff_weightedBalanceCorridor
    {left right : List ℕ} (length_eq : left.length = right.length)
    (sum_gt : right.sum < left.sum) :
    collisionSource left right ∈ Set.Icc (1 / 5) (1 / 2) ↔
      (shellGain right - shellGain left) / 5 ≤ shellOffset left - shellOffset right ∧
        shellOffset left - shellOffset right ≤
          (shellGain right - shellGain left) / 2 := by
  have sum_ne : left.sum ≠ right.sum := ne_of_gt sum_gt
  rw [collisionSource_eq_clearedBalance length_eq sum_ne]
  have denominator_positive : 0 < shellGain right - shellGain left := by
    have gain_lt := shellGain_lt_of_sum_gt length_eq sum_gt
    linarith
  constructor
  · rintro ⟨lower, upper⟩
    constructor
    · have cleared := (le_div_iff₀ denominator_positive).mp lower
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using cleared
    · have cleared := (div_le_iff₀ denominator_positive).mp upper
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using cleared
  · rintro ⟨lower, upper⟩
    constructor
    · apply (le_div_iff₀ denominator_positive).2
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using lower
    · apply (div_le_iff₀ denominator_positive).2
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using upper

/-- Every determinant summand factors into two suffix units and one prefix-gain gap. -/
theorem shellPrefixDeterminantTerm_eq_factored (left right : List ℕ) (cut : ℕ) :
    shellPrefixDeterminantTerm left right cut =
      5 ^ cut * shellGain (left.drop (cut + 1)) *
        shellGain (right.drop (cut + 1)) *
          (shellGain (left.take (cut + 1)) - shellGain (right.take (cut + 1))) := by
  have left_split := List.take_append_drop (cut + 1) left
  have right_split := List.take_append_drop (cut + 1) right
  have left_gain_split :
      shellGain left =
        shellGain (left.take (cut + 1)) * shellGain (left.drop (cut + 1)) := by
    calc
      shellGain left =
          shellGain (left.take (cut + 1) ++ left.drop (cut + 1)) :=
        congrArg shellGain left_split.symm
      _ = shellGain (left.take (cut + 1)) * shellGain (left.drop (cut + 1)) :=
        shellGain_append _ _
  have right_gain_split :
      shellGain right =
        shellGain (right.take (cut + 1)) * shellGain (right.drop (cut + 1)) := by
    calc
      shellGain right =
          shellGain (right.take (cut + 1) ++ right.drop (cut + 1)) :=
        congrArg shellGain right_split.symm
      _ = shellGain (right.take (cut + 1)) * shellGain (right.drop (cut + 1)) :=
        shellGain_append _ _
  rw [shellPrefixDeterminantTerm, left_gain_split, right_gain_split]
  ring

/-- Absolute wait-sum gap in the prefixes ending at `cut`. -/
def shellPrefixSumGap (left right : List ℕ) (cut : ℕ) : ℕ :=
  shellSlopeSumGap (left.take (cut + 1)) (right.take (cut + 1))

private theorem shellPrefixSumGap_eq_crossSumGap (left right : List ℕ) (cut : ℕ) :
    shellPrefixSumGap left right cut =
      shellSlopeSumGap
        (left ++ right.drop (cut + 1))
        (right ++ left.drop (cut + 1)) := by
  have left_split := List.sum_take_add_sum_drop left (cut + 1)
  have right_split := List.sum_take_add_sum_drop right (cut + 1)
  simp only [shellPrefixSumGap, shellSlopeSumGap, List.sum_append]
  omega

/-- A nonzero prefix term has its index plus its parity/LTE carry as exact five-adic value. -/
theorem shellPrefixDeterminantTerm_hasValue
    {left right : List ℕ} (length_eq : left.length = right.length)
    {cut : ℕ} (gap_ne : shellPrefixSumGap left right cut ≠ 0) :
    HasValue 5 (shellPrefixDeterminantTerm left right cut)
      ((cut : ℤ) + shellSlopeGapFiveDepth (shellPrefixSumGap left right cut)) := by
  let leftCross := left ++ right.drop (cut + 1)
  let rightCross := right ++ left.drop (cut + 1)
  have cross_length_eq : leftCross.length = rightCross.length := by
    simp only [leftCross, rightCross, List.length_append, List.length_drop]
    omega
  have cross_gap_eq :
      shellSlopeSumGap leftCross rightCross = shellPrefixSumGap left right cut := by
    exact (shellPrefixSumGap_eq_crossSumGap left right cut).symm
  have cross_sum_ne : leftCross.sum ≠ rightCross.sum := by
    intro sum_eq
    apply gap_ne
    rw [← cross_gap_eq, shellSlopeSumGap, sum_eq]
    omega
  have slope_value :=
    shellSlope_sub_hasValue_five_of_sameLength cross_length_eq cross_sum_ne
  have denominator_value :
      HasValue 5 ((5 : ℚ) ^ leftCross.length) leftCross.length :=
    primePower_hasValue leftCross.length
  have gain_value := mul_hasValue denominator_value slope_value
  have gain_eq :
      5 ^ leftCross.length * (shellSlope leftCross - shellSlope rightCross) =
        shellGain leftCross - shellGain rightCross := by
    rw [shellSlope_eq_gain_div, shellSlope_eq_gain_div, ← cross_length_eq]
    have denominator_ne : (5 : ℚ) ^ leftCross.length ≠ 0 := by positivity
    field_simp
  rw [gain_eq] at gain_value
  have normalized_gain_value :
      HasValue 5 (shellGain leftCross - shellGain rightCross)
        (shellSlopeGapFiveDepth (shellPrefixSumGap left right cut)) := by
    rw [cross_gap_eq] at gain_value
    convert gain_value using 1
    ring
  have cut_value : HasValue 5 ((5 : ℚ) ^ cut) cut := primePower_hasValue cut
  have term_value := mul_hasValue cut_value normalized_gain_value
  convert term_value using 1
  dsimp only [leftCross, rightCross]
  rw [shellPrefixDeterminantTerm, shellGain_append, shellGain_append]

private theorem shellPrefixDeterminantTerm_eq_zero_of_gap_eq_zero
    {left right : List ℕ} (length_eq : left.length = right.length)
    {cut : ℕ} (gap_eq : shellPrefixSumGap left right cut = 0) :
    shellPrefixDeterminantTerm left right cut = 0 := by
  have prefix_sum_eq :
      (left.take (cut + 1)).sum = (right.take (cut + 1)).sum := by
    rw [shellPrefixSumGap, shellSlopeSumGap] at gap_eq
    omega
  have left_split := List.sum_take_add_sum_drop left (cut + 1)
  have right_split := List.sum_take_add_sum_drop right (cut + 1)
  have cross_sum_eq :
      (left ++ right.drop (cut + 1)).sum =
        (right ++ left.drop (cut + 1)).sum := by
    simp only [List.sum_append]
    omega
  have cross_length_eq :
      (left ++ right.drop (cut + 1)).length =
        (right ++ left.drop (cut + 1)).length := by
    simp only [List.length_append, List.length_drop]
    omega
  have cross_gain_eq :
      shellGain (left ++ right.drop (cut + 1)) =
        shellGain (right ++ left.drop (cut + 1)) := by
    simp only [shellGain]
    rw [cross_length_eq, cross_sum_eq]
  rw [shellPrefixDeterminantTerm, ← shellGain_append, ← shellGain_append,
    cross_gain_eq, sub_self, mul_zero]

/-- Five-adic height assigned to a nonzero prefix determinant term. -/
def shellPrefixCarryHeight (left right : List ℕ) (cut : ℕ) : ℤ :=
  cut + shellSlopeGapFiveDepth (shellPrefixSumGap left right cut)

/-- The cleared determinant is the sum of its complementary prefix-carry terms. -/
theorem shellClearedDeterminant_eq_sum_prefixTerms
    {left right : List ℕ} (length_eq : left.length = right.length) :
    shellClearedDeterminant left right =
      ∑ cut ∈ Finset.range left.length, shellPrefixDeterminantTerm left right cut := by
  rw [shellClearedDeterminant, shellOffset_eq_sum_dropGain,
    shellOffset_eq_sum_dropGain, ← length_eq, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro cut cut_mem
  rw [shellPrefixDeterminantTerm]
  ring

/-- Appending two possibly different waits gives a closed paired determinant recurrence. -/
theorem shellClearedDeterminant_append_pair
    {left right : List ℕ} (length_eq : left.length = right.length)
    (leftWait rightWait : ℕ) :
    shellClearedDeterminant (left ++ [leftWait]) (right ++ [rightWait]) =
      shellScale leftWait * shellScale rightWait * shellClearedDeterminant left right +
        5 ^ left.length *
          (shellGain (left ++ [leftWait]) - shellGain (right ++ [rightWait])) := by
  simp only [shellClearedDeterminant, shellGain_append_singleton,
    shellOffset_append_singleton, ← length_eq]
  ring

private theorem sum_hasValue_of_unique_low
    {prime : ℕ} [Fact prime.Prime] {α : Type*} [DecidableEq α]
    (indices : Finset α) (term : α → ℚ) {pivot : α} {valuation : ℤ}
    (pivot_mem : pivot ∈ indices)
    (pivot_value : HasValue prime (term pivot) valuation)
    (other_high : ∀ index ∈ indices, index ≠ pivot →
      term index = 0 ∨
        (term index ≠ 0 ∧ valuation < padicValRat prime (term index))) :
    HasValue prime (∑ index ∈ indices, term index) valuation := by
  have high_sum_or_zero :
      ∀ remainder : Finset α,
        (∀ index ∈ remainder,
          term index = 0 ∨
            (term index ≠ 0 ∧ valuation < padicValRat prime (term index))) →
        (∑ index ∈ remainder, term index) = 0 ∨
          ((∑ index ∈ remainder, term index) ≠ 0 ∧
            valuation < padicValRat prime (∑ index ∈ remainder, term index)) := by
    intro remainder
    induction remainder using Finset.induction_on with
    | empty =>
        intro remainder_high
        left
        simp
    | @insert index remainder index_not_mem induction =>
        intro remainder_high
        have index_high := remainder_high index (by simp)
        have tail_high :
            ∀ item ∈ remainder,
              term item = 0 ∨
                (term item ≠ 0 ∧ valuation < padicValRat prime (term item)) := by
          intro item item_mem
          exact remainder_high item (by simp [item_mem])
        rcases induction tail_high with tail_zero | tail_value
        · rw [Finset.sum_insert index_not_mem, tail_zero, add_zero]
          exact index_high
        · rcases index_high with index_zero | index_value
          · rw [Finset.sum_insert index_not_mem, index_zero, zero_add]
            exact Or.inr tail_value
          · rw [Finset.sum_insert index_not_mem]
            by_cases total_zero :
                term index + ∑ item ∈ remainder, term item = 0
            · exact Or.inl total_zero
            · right
              exact ⟨total_zero, lt_of_lt_of_le (lt_min index_value.2 tail_value.2)
                (padicValRat.min_le_padicValRat_add total_zero)⟩
  let remainder := indices.erase pivot
  have remainder_high :
      ∀ index ∈ remainder,
        term index = 0 ∨
          (term index ≠ 0 ∧ valuation < padicValRat prime (term index)) := by
    intro index index_mem
    have index_data := Finset.mem_erase.mp index_mem
    exact other_high index index_data.2 index_data.1
  have decomposition := Finset.sum_erase_add indices term pivot_mem
  rcases high_sum_or_zero remainder remainder_high with remainder_zero | remainder_value
  · rw [← decomposition, remainder_zero, zero_add]
    exact pivot_value
  · have remainder_hasValue :
        HasValue prime (∑ index ∈ remainder, term index)
          (padicValRat prime (∑ index ∈ remainder, term index)) :=
      ⟨remainder_value.1, rfl⟩
    rw [← decomposition]
    exact add_hasValue_right remainder_hasValue pivot_value remainder_value.2

/-- A unique lowest nonzero prefix carry fixes the exact value of the cleared determinant. -/
theorem shellClearedDeterminant_hasValue_of_uniquePrefixCarryMinimum
    {left right : List ℕ} (length_eq : left.length = right.length)
    {pivot : ℕ} (pivot_mem : pivot < left.length)
    (pivot_gap_ne : shellPrefixSumGap left right pivot ≠ 0)
    (unique_minimum : ∀ cut < left.length, cut ≠ pivot →
      shellPrefixSumGap left right cut = 0 ∨
        shellPrefixCarryHeight left right pivot < shellPrefixCarryHeight left right cut) :
    HasValue 5 (shellClearedDeterminant left right)
      (shellPrefixCarryHeight left right pivot) := by
  rw [shellClearedDeterminant_eq_sum_prefixTerms length_eq]
  apply sum_hasValue_of_unique_low (Finset.range left.length)
      (shellPrefixDeterminantTerm left right) (Finset.mem_range.mpr pivot_mem)
  · simpa only [shellPrefixCarryHeight] using
      shellPrefixDeterminantTerm_hasValue length_eq pivot_gap_ne
  · intro cut cut_mem cut_ne
    have cut_lt := Finset.mem_range.mp cut_mem
    by_cases gap_zero : shellPrefixSumGap left right cut = 0
    · exact Or.inl (shellPrefixDeterminantTerm_eq_zero_of_gap_eq_zero length_eq gap_zero)
    · right
      have term_value := shellPrefixDeterminantTerm_hasValue length_eq gap_zero
      exact ⟨term_value.1, by
        rw [term_value.2]
        exact (unique_minimum cut cut_lt cut_ne).resolve_left gap_zero⟩

private theorem shellPrefixSumGap_last
    {left right : List ℕ} (length_eq : left.length = right.length)
    (length_positive : 0 < left.length) :
    shellPrefixSumGap left right (left.length - 1) =
      shellSlopeSumGap left right := by
  have sub_add : left.length - 1 + 1 = left.length := by omega
  have right_take : right.take left.length = right := by
    rw [length_eq]
    exact List.take_length
  rw [shellPrefixSumGap, sub_add, List.take_length, right_take]

/-- An accepted same-length cross-grade collision cannot have a unique lowest nonzero prefix
carry. -/
theorem acceptedCollision_not_uniquePrefixCarryMinimum
    {left right : List ℕ} (length_eq : left.length = right.length)
    (sum_ne : left.sum ≠ right.sum)
    (target_unit : IsUnit 5 (shellRun left (collisionSource left right)))
    {pivot : ℕ} (pivot_mem : pivot < left.length)
    (pivot_gap_ne : shellPrefixSumGap left right pivot ≠ 0) :
    ¬(∀ cut < left.length, cut ≠ pivot →
      shellPrefixSumGap left right cut = 0 ∨
        shellPrefixCarryHeight left right pivot < shellPrefixCarryHeight left right cut) := by
  intro unique_minimum
  have determinant_minimum :=
    shellClearedDeterminant_hasValue_of_uniquePrefixCarryMinimum length_eq pivot_mem
      pivot_gap_ne unique_minimum
  have determinant_accepted :=
    (sameLengthCollisionClearedDeterminant_fiveUnit_iff length_eq sum_ne).1 target_unit
  have length_positive : 0 < left.length := by
    by_contra length_not_positive
    have left_nil : left = [] := List.eq_nil_of_length_eq_zero (by omega)
    have right_nil : right = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact sum_ne (by rw [left_nil, right_nil])
  let last := left.length - 1
  have last_mem : last < left.length := by
    dsimp only [last]
    omega
  have total_gap_ne : shellSlopeSumGap left right ≠ 0 := by
    intro gap_zero
    rw [shellSlopeSumGap] at gap_zero
    exact sum_ne (by omega)
  have last_gap :
      shellPrefixSumGap left right last = shellSlopeSumGap left right := by
    exact shellPrefixSumGap_last length_eq length_positive
  have last_gap_ne : shellPrefixSumGap left right last ≠ 0 := by
    rw [last_gap]
    exact total_gap_ne
  have last_height_lt :
      shellPrefixCarryHeight left right last <
        (left.length : ℤ) +
          shellSlopeGapFiveDepth (shellSlopeSumGap left right) := by
    rw [shellPrefixCarryHeight, last_gap]
    dsimp only [last]
    omega
  have minimum_lt_accepted :
      shellPrefixCarryHeight left right pivot <
        (left.length : ℤ) +
          shellSlopeGapFiveDepth (shellSlopeSumGap left right) := by
    by_cases pivot_last : pivot = last
    · rw [pivot_last]
      exact last_height_lt
    · exact lt_trans
        ((unique_minimum last last_mem (Ne.symm pivot_last)).resolve_left last_gap_ne)
        last_height_lt
  have valuation_eq :
      shellPrefixCarryHeight left right pivot =
        (left.length : ℤ) +
          shellSlopeGapFiveDepth (shellSlopeSumGap left right) := by
    rw [← determinant_minimum.2, determinant_accepted.2]
  exact (ne_of_lt minimum_lt_accepted) valuation_eq

/-- The first nonzero prefix gap of an accepted same-length cross-grade collision is even. -/
theorem acceptedCollision_firstNonzeroPrefixGap_even
    {left right : List ℕ} (length_eq : left.length = right.length)
    (sum_ne : left.sum ≠ right.sum)
    (target_unit : IsUnit 5 (shellRun left (collisionSource left right)))
    {first : ℕ} (first_mem : first < left.length)
    (first_gap_ne : shellPrefixSumGap left right first ≠ 0)
    (previous_gaps_zero : ∀ cut < first, shellPrefixSumGap left right cut = 0) :
    Even (shellPrefixSumGap left right first) := by
  rw [← Nat.not_odd_iff_even]
  intro gap_odd
  apply acceptedCollision_not_uniquePrefixCarryMinimum length_eq sum_ne target_unit
    first_mem first_gap_ne
  intro cut cut_mem cut_ne
  by_cases cut_lt : cut < first
  · exact Or.inl (previous_gaps_zero cut cut_lt)
  · right
    have first_lt_cut : first < cut := by omega
    rw [shellPrefixCarryHeight, shellPrefixCarryHeight, shellSlopeGapFiveDepth,
      if_pos gap_odd]
    have carry_nonnegative :
        0 ≤ (shellSlopeGapFiveDepth (shellPrefixSumGap left right cut) : ℤ) := by
      positivity
    omega

/-- Acceptance forces a later nonzero prefix gap to cancel the first carry minimum within its
available five-adic depth. -/
theorem acceptedCollision_exists_prefixCarryPartner
    {left right : List ℕ} (length_eq : left.length = right.length)
    (sum_ne : left.sum ≠ right.sum)
    (target_unit : IsUnit 5 (shellRun left (collisionSource left right)))
    {first : ℕ} (first_mem : first < left.length)
    (first_gap_ne : shellPrefixSumGap left right first ≠ 0)
    (previous_gaps_zero : ∀ cut < first, shellPrefixSumGap left right cut = 0) :
    ∃ cut, first < cut ∧ cut < left.length ∧
      shellPrefixSumGap left right cut ≠ 0 ∧
      cut - first + shellSlopeGapFiveDepth (shellPrefixSumGap left right cut) ≤
        shellSlopeGapFiveDepth (shellPrefixSumGap left right first) := by
  have no_unique :=
    acceptedCollision_not_uniquePrefixCarryMinimum length_eq sum_ne target_unit
      first_mem first_gap_ne
  have partner :
      ∃ cut, first < cut ∧ cut < left.length ∧
        shellPrefixSumGap left right cut ≠ 0 ∧
        shellPrefixCarryHeight left right cut ≤
          shellPrefixCarryHeight left right first := by
    by_contra no_partner
    apply no_unique
    intro cut cut_mem cut_ne
    by_cases gap_zero : shellPrefixSumGap left right cut = 0
    · exact Or.inl gap_zero
    · right
      have first_lt_cut : first < cut := by
        by_contra not_lt
        have cut_lt_first : cut < first := by omega
        exact gap_zero (previous_gaps_zero cut cut_lt_first)
      have not_le :
          ¬shellPrefixCarryHeight left right cut ≤
            shellPrefixCarryHeight left right first := by
        intro carry_le
        apply no_partner
        exact ⟨cut, first_lt_cut, cut_mem, gap_zero, carry_le⟩
      omega
  obtain ⟨cut, first_lt_cut, cut_mem, gap_ne, carry_le⟩ := partner
  refine ⟨cut, first_lt_cut, cut_mem, gap_ne, ?_⟩
  rw [shellPrefixCarryHeight, shellPrefixCarryHeight] at carry_le
  norm_cast at carry_le
  omega

/-- In the generic even first-gap case, acceptance forces the next prefix gap to be odd. -/
theorem acceptedCollision_nextPrefixGap_odd_of_firstCarryDepth_one
    {left right : List ℕ} (length_eq : left.length = right.length)
    (sum_ne : left.sum ≠ right.sum)
    (target_unit : IsUnit 5 (shellRun left (collisionSource left right)))
    {first : ℕ} (first_mem : first < left.length)
    (first_gap_ne : shellPrefixSumGap left right first ≠ 0)
    (previous_gaps_zero : ∀ cut < first, shellPrefixSumGap left right cut = 0)
    (first_depth :
      shellSlopeGapFiveDepth (shellPrefixSumGap left right first) = 1) :
    first + 1 < left.length ∧
      shellPrefixSumGap left right (first + 1) ≠ 0 ∧
      Odd (shellPrefixSumGap left right (first + 1)) := by
  obtain ⟨cut, first_lt_cut, cut_mem, gap_ne, carry_bound⟩ :=
    acceptedCollision_exists_prefixCarryPartner length_eq sum_ne target_unit first_mem
      first_gap_ne previous_gaps_zero
  rw [first_depth] at carry_bound
  have carry_nonnegative :
      0 ≤ shellSlopeGapFiveDepth (shellPrefixSumGap left right cut) := by
    positivity
  have cut_eq : cut = first + 1 := by omega
  subst cut
  have next_depth_zero :
      shellSlopeGapFiveDepth (shellPrefixSumGap left right (first + 1)) = 0 := by
    omega
  have next_gap_odd : Odd (shellPrefixSumGap left right (first + 1)) := by
    by_contra gap_not_odd
    rw [shellSlopeGapFiveDepth, if_neg gap_not_odd] at next_depth_zero
    omega
  exact ⟨cut_mem, gap_ne, next_gap_odd⟩

/-- A boundary collision realizes the minimal two-term carry tie. -/
theorem prefixCarryBoundaryAcceptedCollision :
    collisionSource [0, 2] [2, 1] = 1 / 2 ∧
      shellRun [0, 2] (1 / 2) = 1 / 3 ∧
      shellRun [2, 1] (1 / 2) = 1 / 3 ∧
      IsUnit 5 (1 / 2 : ℚ) ∧
      IsUnit 5 (1 / 3 : ℚ) ∧
      shellPrefixCarryHeight [0, 2] [2, 1] 0 = 1 ∧
      shellPrefixCarryHeight [0, 2] [2, 1] 1 = 1 := by
  have left_run : shellRun [0, 2] (1 / 2) = 1 / 3 := by
    rw [shellRun_cons, shellRun_singleton]
    norm_num [shellStep]
  have right_run : shellRun [2, 1] (1 / 2) = 1 / 3 := by
    rw [shellRun_cons, shellRun_singleton]
    norm_num [shellStep]
  have slope_ne : shellSlope [0, 2] ≠ shellSlope [2, 1] := by
    intro slope_eq
    have sum_eq := (shellSlope_eq_iff_length_sum [0, 2] [2, 1]).1 slope_eq
    norm_num at sum_eq
  have source_eq :=
    collisionSource_eq_of_shellRun_eq [0, 2] [2, 1] slope_ne (left_run.trans right_run.symm)
  refine ⟨source_eq, left_run, right_run, ?_, ?_, ?_, ?_⟩
  · exact div_hasValue
      (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 1))
      (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 2))
  · exact div_hasValue
      (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 1))
      (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 3))
  · norm_num [shellPrefixCarryHeight, shellPrefixSumGap, shellSlopeSumGap,
      shellSlopeGapFiveDepth]
  · norm_num [shellPrefixCarryHeight, shellPrefixSumGap, shellSlopeSumGap,
      shellSlopeGapFiveDepth]

/-- The same signed suffix-gap walk and source can fail target acceptance. -/
theorem prefixCarrySameGapRejectedCollision :
    collisionSource [0, 6] [2, 5] = 1 / 2 ∧
      shellRun [0, 6] (1 / 2) = 55 / 243 ∧
      shellRun [2, 5] (1 / 2) = 55 / 243 ∧
      IsUnit 5 (1 / 2 : ℚ) ∧
      HasValue 5 (55 / 243 : ℚ) 1 := by
  have left_run : shellRun [0, 6] (1 / 2) = 55 / 243 := by
    rw [shellRun_cons, shellRun_singleton]
    norm_num [shellStep]
  have right_run : shellRun [2, 5] (1 / 2) = 55 / 243 := by
    rw [shellRun_cons, shellRun_singleton]
    norm_num [shellStep]
  have slope_ne : shellSlope [0, 6] ≠ shellSlope [2, 5] := by
    intro slope_eq
    have sum_eq := (shellSlope_eq_iff_length_sum [0, 6] [2, 5]).1 slope_eq
    norm_num at sum_eq
  have source_eq :=
    collisionSource_eq_of_shellRun_eq [0, 6] [2, 5] slope_ne
      (left_run.trans right_run.symm)
  refine ⟨source_eq, left_run, right_run, ?_, ?_⟩
  · exact div_hasValue
      (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 1))
      (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 2))
  · convert primePower_mul_int_div_int_hasValue (prime := 5) 1
      (by norm_num : ¬(5 : ℤ) ∣ 11) (by norm_num : ¬(5 : ℤ) ∣ 243) using 1
    · norm_num
    · norm_num

/-- A strict-interior real-trap collision also realizes a two-term carry tie. -/
theorem prefixCarryInteriorAcceptedCollision :
    collisionSource [1, 1] [9, 0] = 2187 / 8236 ∧
      shellRun [1, 1] (2187 / 8236) = 664 / 2059 ∧
      shellRun [9, 0] (2187 / 8236) = 664 / 2059 ∧
      (2187 / 8236 : ℚ) ∈ Set.Ioo (1 / 5) (1 / 2) ∧
      (664 / 2059 : ℚ) ∈ Set.Ioo (1 / 5) (1 / 2) ∧
      IsUnit 5 (2187 / 8236 : ℚ) ∧
      IsUnit 5 (664 / 2059 : ℚ) ∧
      shellPrefixCarryHeight [1, 1] [9, 0] 0 = 1 ∧
      shellPrefixCarryHeight [1, 1] [9, 0] 1 = 1 := by
  have left_run : shellRun [1, 1] (2187 / 8236) = 664 / 2059 := by
    rw [shellRun_cons, shellRun_singleton]
    norm_num [shellStep]
  have right_run : shellRun [9, 0] (2187 / 8236) = 664 / 2059 := by
    rw [shellRun_cons, shellRun_singleton]
    norm_num [shellStep]
  have slope_ne : shellSlope [1, 1] ≠ shellSlope [9, 0] := by
    intro slope_eq
    have sum_eq := (shellSlope_eq_iff_length_sum [1, 1] [9, 0]).1 slope_eq
    norm_num at sum_eq
  have source_eq :=
    collisionSource_eq_of_shellRun_eq [1, 1] [9, 0] slope_ne (left_run.trans right_run.symm)
  refine ⟨source_eq, left_run, right_run, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · exact div_hasValue
      (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 2187))
      (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 8236))
  · exact div_hasValue
      (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 664))
      (intCast_isUnit_of_not_dvd (prime := 5) (by norm_num : ¬(5 : ℤ) ∣ 2059))
  · norm_num [shellPrefixCarryHeight, shellPrefixSumGap, shellSlopeSumGap,
      shellSlopeGapFiveDepth]
  · norm_num [shellPrefixCarryHeight, shellPrefixSumGap, shellSlopeSumGap,
      shellSlopeGapFiveDepth]

end MatrixMortality.MixedPrimeDebt
