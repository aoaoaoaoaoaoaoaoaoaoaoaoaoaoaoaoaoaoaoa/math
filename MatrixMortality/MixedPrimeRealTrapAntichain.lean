import MatrixMortality.MixedPrimeRealTrapCentralizer

/-!
# Suffix-sum order on shell schedules

Positive-source endpoint fibres are antichains for the reverse cumulative-wait order.
-/

namespace MatrixMortality.MixedPrimeDebt

open PeriodicShell

/-- Reverse cumulative-wait order on schedules of equal length. -/
def SuffixSumLE : List ℕ → List ℕ → Prop
  | [], [] => True
  | left :: leftTail, right :: rightTail =>
      left + leftTail.sum ≤ right + rightTail.sum ∧
        SuffixSumLE leftTail rightTail
  | _, _ => False

/-- The numerator of a schedule slope after clearing its forced five-power denominator. -/
def shellGain (waits : List ℕ) : ℚ :=
  3 ^ waits.length * (2 / 3 : ℚ) ^ waits.sum

theorem shellSlope_eq_gain_div (waits : List ℕ) :
    shellSlope waits = shellGain waits / 5 ^ waits.length := by
  exact shellSlope_eq_length_sum waits

theorem shellClearedRun (waits : List ℕ) (source : ℚ) :
    5 ^ waits.length * shellRun waits source =
      shellGain waits * source + shellOffset waits := by
  rw [shellRun_eq_slope_mul_add_intercept, shellSlope_eq_gain_div, shellOffset]
  have denominator_ne : (5 : ℚ) ^ waits.length ≠ 0 := by positivity
  field_simp

/-- At equal length, endpoint equality is exactly equality of the two cleared gain-offset
forms. -/
theorem shellRun_eq_iff_clearedRun_eq_of_length_eq
    {left right : List ℕ} (length_eq : left.length = right.length) (source : ℚ) :
    shellRun left source = shellRun right source ↔
      shellGain left * source + shellOffset left =
        shellGain right * source + shellOffset right := by
  constructor
  · intro collision
    calc
      shellGain left * source + shellOffset left =
          5 ^ left.length * shellRun left source := (shellClearedRun left source).symm
      _ = 5 ^ right.length * shellRun right source := by rw [length_eq, collision]
      _ = shellGain right * source + shellOffset right := shellClearedRun right source
  · intro cleared_eq
    have scaled_eq :
        5 ^ left.length * shellRun left source =
          5 ^ right.length * shellRun right source := by
      rw [shellClearedRun, shellClearedRun]
      exact cleared_eq
    rw [← length_eq] at scaled_eq
    exact mul_left_cancel₀ (show (5 : ℚ) ^ left.length ≠ 0 by positivity) scaled_eq

theorem suffixSumLE_length_eq :
    ∀ {left right : List ℕ}, SuffixSumLE left right → left.length = right.length
  | [], [], _ => rfl
  | [], _ :: _, ordered => by
      simp only [SuffixSumLE] at ordered
  | _ :: _, [], ordered => by
      simp only [SuffixSumLE] at ordered
  | _ :: leftTail, _ :: rightTail, ordered => by
      simp only [SuffixSumLE] at ordered
      simp only [List.length_cons, suffixSumLE_length_eq ordered.2]

theorem suffixSumLE_sum_le :
    ∀ {left right : List ℕ}, SuffixSumLE left right → left.sum ≤ right.sum
  | [], [], _ => Nat.le_refl 0
  | [], _ :: _, ordered => by
      simp only [SuffixSumLE] at ordered
  | _ :: _, [], ordered => by
      simp only [SuffixSumLE] at ordered
  | _ :: _, _ :: _, ordered => by
      simpa only [List.sum_cons] using ordered.1

/-- Coordinatewise wait comparison implies suffix-sum comparison. -/
theorem suffixSumLE_of_forall₂ :
    ∀ {left right : List ℕ}, List.Forall₂ (· ≤ ·) left right → SuffixSumLE left right
  | [], [], _ => by simp only [SuffixSumLE]
  | _ :: _, _ :: _, pointwise => by
      cases pointwise with
      | cons head_le tail_le =>
          have tail_order := suffixSumLE_of_forall₂ tail_le
          simp only [SuffixSumLE]
          exact ⟨Nat.add_le_add head_le (suffixSumLE_sum_le tail_order), tail_order⟩

/-- The recursive suffix-sum order is exactly pointwise comparison of all aligned suffix
sums. -/
theorem suffixSumLE_iff_forall_drop_sum_le
    {left right : List ℕ} (length_eq : left.length = right.length) :
    SuffixSumLE left right ↔
      ∀ cut, (left.drop cut).sum ≤ (right.drop cut).sum := by
  induction left generalizing right with
  | nil =>
      have right_nil : right = [] := List.eq_nil_of_length_eq_zero length_eq.symm
      subst right
      simp [SuffixSumLE]
  | cons left leftTail induction =>
      cases right with
      | nil => simp at length_eq
      | cons right rightTail =>
          have tail_length_eq : leftTail.length = rightTail.length := by
            simpa only [List.length_cons, Nat.succ_inj] using length_eq
          rw [show SuffixSumLE (left :: leftTail) (right :: rightTail) ↔
              left + leftTail.sum ≤ right + rightTail.sum ∧
                SuffixSumLE leftTail rightTail by rfl,
            induction tail_length_eq]
          constructor
          · rintro ⟨total_le, tails_le⟩ cut
            cases cut with
            | zero => simpa only [List.drop_zero, List.sum_cons] using total_le
            | succ cut => simpa only [List.drop_succ_cons] using tails_le cut
          · intro suffixes_le
            constructor
            · simpa only [List.drop_zero, List.sum_cons] using suffixes_le 0
            · intro cut
              simpa only [List.drop_succ_cons] using suffixes_le (cut + 1)

private theorem shellRatio_pow_anti {left right : ℕ} (ordered : left ≤ right) :
    (2 / 3 : ℚ) ^ right ≤ (2 / 3 : ℚ) ^ left := by
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) ordered

theorem shellGain_anti {left right : List ℕ} (ordered : SuffixSumLE left right) :
    shellGain right ≤ shellGain left := by
  have length_eq := suffixSumLE_length_eq ordered
  have sum_le := suffixSumLE_sum_le ordered
  rw [shellGain, shellGain, ← length_eq]
  exact mul_le_mul_of_nonneg_left (shellRatio_pow_anti sum_le) (by positivity)

theorem shellOffset_anti :
    ∀ {left right : List ℕ}, SuffixSumLE left right →
      shellOffset right ≤ shellOffset left
  | [], [], _ => by simp [shellOffset, shellIntercept]
  | [], _ :: _, ordered => by
      simp only [SuffixSumLE] at ordered
  | _ :: _, [], ordered => by
      simp only [SuffixSumLE] at ordered
  | left :: leftTail, right :: rightTail, ordered => by
      simp only [SuffixSumLE] at ordered
      have gain_le := shellGain_anti ordered.2
      have offset_le := shellOffset_anti ordered.2
      rw [shellOffset_cons left leftTail, shellOffset_cons right rightTail]
      change shellGain rightTail + 5 * shellOffset rightTail ≤
        shellGain leftTail + 5 * shellOffset leftTail
      linarith

private theorem suffixSumLE_eq_of_gain_offset_eq :
    ∀ {left right : List ℕ}, SuffixSumLE left right →
      shellGain left = shellGain right →
      shellOffset left = shellOffset right →
      left = right
  | [], [], _, _, _ => rfl
  | [], _ :: _, ordered, _, _ => by
      simp only [SuffixSumLE] at ordered
  | _ :: _, [], ordered, _, _ => by
      simp only [SuffixSumLE] at ordered
  | left :: leftTail, right :: rightTail, ordered, gain_eq, offset_eq => by
      simp only [SuffixSumLE] at ordered
      have tail_gain_le := shellGain_anti ordered.2
      have tail_offset_le := shellOffset_anti ordered.2
      have expanded_offset_eq :
          shellGain leftTail + 5 * shellOffset leftTail =
            shellGain rightTail + 5 * shellOffset rightTail := by
        simpa only [shellOffset_cons, shellGain] using offset_eq
      have tail_gain_eq : shellGain leftTail = shellGain rightTail := by
        linarith
      have tail_offset_eq : shellOffset leftTail = shellOffset rightTail := by
        linarith
      have tail_eq :=
        suffixSumLE_eq_of_gain_offset_eq ordered.2 tail_gain_eq tail_offset_eq
      subst rightTail
      have power_eq :
          (2 / 3 : ℚ) ^ (left + leftTail.sum) =
            (2 / 3 : ℚ) ^ (right + leftTail.sum) := by
        apply mul_left_cancel₀ (show (3 : ℚ) ^ (leftTail.length + 1) ≠ 0 by positivity)
        simpa only [shellGain, List.length_cons, List.sum_cons, Nat.add_comm] using gain_eq
      have sum_eq : left + leftTail.sum = right + leftTail.sum :=
        (pow_right_injective₀ (show 0 < (2 / 3 : ℚ) by norm_num)
          (show (2 / 3 : ℚ) ≠ 1 by norm_num)) power_eq
      have head_eq : left = right := by omega
      subst right
      rfl

/-- Increasing every reverse cumulative wait strictly decreases the endpoint of every positive
source unless the schedules coincide. -/
theorem shellRun_strictAnti_of_suffixSumLE
    {left right : List ℕ} (ordered : SuffixSumLE left right)
    (distinct : left ≠ right) {source : ℚ} (source_positive : 0 < source) :
    shellRun right source < shellRun left source := by
  have gain_le := shellGain_anti ordered
  have offset_le := shellOffset_anti ordered
  have cleared_le :
      shellGain right * source + shellOffset right ≤
        shellGain left * source + shellOffset left := by
    exact add_le_add (mul_le_mul_of_nonneg_right gain_le source_positive.le) offset_le
  have cleared_ne :
      shellGain right * source + shellOffset right ≠
        shellGain left * source + shellOffset left := by
    intro cleared_eq
    have gain_eq : shellGain left = shellGain right := by
      nlinarith
    have offset_eq : shellOffset left = shellOffset right := by
      nlinarith
    exact distinct (suffixSumLE_eq_of_gain_offset_eq ordered gain_eq offset_eq)
  have cleared_lt := lt_of_le_of_ne cleared_le cleared_ne
  have scaled_lt :
      5 ^ right.length * shellRun right source <
        5 ^ left.length * shellRun left source := by
    rw [shellClearedRun, shellClearedRun]
    exact cleared_lt
  have length_eq := suffixSumLE_length_eq ordered
  rw [← length_eq] at scaled_lt
  exact lt_of_mul_lt_mul_left scaled_lt (by positivity)

/-- Every positive-source endpoint fibre is an antichain in the suffix-sum order. -/
theorem positiveSource_collision_suffixSum_incomparable
    {left right : List ℕ} (distinct : left ≠ right)
    {source : ℚ} (source_positive : 0 < source)
    (collision : shellRun left source = shellRun right source) :
    ¬SuffixSumLE left right ∧ ¬SuffixSumLE right left := by
  constructor
  · intro ordered
    have strict := shellRun_strictAnti_of_suffixSumLE ordered distinct source_positive
    exact strict.ne collision.symm
  · intro ordered
    have strict := shellRun_strictAnti_of_suffixSumLE ordered distinct.symm source_positive
    exact strict.ne collision

/-- Two distinct equal-length schedules meeting at a positive source have suffix-sum gaps of
both signs. -/
theorem sameLength_positiveSource_collision_suffixSums_cross
    {left right : List ℕ} (length_eq : left.length = right.length)
    (distinct : left ≠ right) {source : ℚ} (source_positive : 0 < source)
    (collision : shellRun left source = shellRun right source) :
    (∃ cut, (right.drop cut).sum < (left.drop cut).sum) ∧
      ∃ cut, (left.drop cut).sum < (right.drop cut).sum := by
  have incomparable :=
    positiveSource_collision_suffixSum_incomparable distinct source_positive collision
  rw [suffixSumLE_iff_forall_drop_sum_le length_eq] at incomparable
  rw [suffixSumLE_iff_forall_drop_sum_le length_eq.symm] at incomparable
  push Not at incomparable
  exact incomparable

/-- A same-length cross-grade collision whose suffix sums are ordered cannot occur at a positive
source. -/
theorem collisionSource_nonpos_of_suffixSumLE
    {left right : List ℕ} (ordered : SuffixSumLE left right)
    (sum_ne : left.sum ≠ right.sum) :
    collisionSource left right ≤ 0 := by
  have slope_ne : shellSlope left ≠ shellSlope right := by
    intro slope_eq
    exact sum_ne ((shellSlope_eq_iff_length_sum left right).1 slope_eq).2
  have distinct : left ≠ right := by
    intro waits_eq
    exact sum_ne (congrArg List.sum waits_eq)
  by_contra source_not_nonpos
  have source_positive : 0 < collisionSource left right := lt_of_not_ge source_not_nonpos
  have strict := shellRun_strictAnti_of_suffixSumLE ordered distinct source_positive
  have collision := shellRun_collisionSource left right slope_ne
  exact strict.ne collision.symm

end MatrixMortality.MixedPrimeDebt
