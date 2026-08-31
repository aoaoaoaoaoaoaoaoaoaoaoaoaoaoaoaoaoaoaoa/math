import MatrixMortality.MixedPrimeDebt

/-!
# Mixed-prime exit suffixes

Every critical-shell exit has one of three exact five-adic forms. A fixed target then permits at
most two nonempty suffix lengths. The accepted fixed-source collision ray has only the
valuation-minus-one form, so its entire controlled continuation cone has one candidate length.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation
open PeriodicShell

private local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private theorem exitScale_fiveUnit (wait : ℕ) :
    IsUnit 5 (3 * (2 / 3 : ℚ) ^ wait) := by
  have two_unit : IsUnit 5 (2 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have three_unit : IsUnit 5 (3 : ℚ) := intCast_isUnit_of_not_dvd (by norm_num)
  have ratio_unit : IsUnit 5 (2 / 3 : ℚ) := div_hasValue two_unit three_unit
  have power_unit : IsUnit 5 ((2 / 3 : ℚ) ^ wait) := by
    refine ⟨pow_ne_zero wait ratio_unit.1, ?_⟩
    rw [padicValRat.pow, ratio_unit.2]
    simp
  exact mul_hasValue three_unit power_unit

/-- The tail length forced by a target reached from a valuation-minus-one exit. -/
def negativeExitTailLengthCandidate (target : ℚ) : ℕ :=
  Int.toNat (-padicValRat 5 target - 1)

/-- The nonempty tail length forced by a target reached from a zero or positive exit. -/
def nonnegativeExitTailLengthCandidate (target : ℚ) : ℕ :=
  Int.toNat (-padicValRat 5 target)

/-- A positive five-adic state enters valuation minus one after one shell block. -/
private theorem shellStep_fivePositive
    (wait : ℕ) {state : ℚ} (state_positive : IsPositive 5 state) :
    HasValue 5 (shellStep wait state) (-1) := by
  have scale_unit := exitScale_fiveUnit wait
  have state_value : HasValue 5 state (padicValRat 5 state) :=
    ⟨state_positive.1, rfl⟩
  have leading_value := mul_hasValue scale_unit state_value
  have leading_positive : IsPositive 5 (3 * (2 / 3 : ℚ) ^ wait * state) :=
    ⟨leading_value.1, by rw [leading_value.2]; simpa using state_positive.2⟩
  have one_unit : IsUnit 5 (1 : ℚ) := ⟨one_ne_zero, padicValRat.one⟩
  have numerator_unit : IsUnit 5 (3 * (2 / 3 : ℚ) ^ wait * state + 1) := by
    rw [add_comm]
    exact unit_add_positive one_unit leading_positive
  have five_value : HasValue 5 (5 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 5) 1)
  simpa [shellStep] using div_hasValue numerator_unit five_value

/-- Zero also enters valuation minus one after one shell block. -/
private theorem shellStep_fiveZero (wait : ℕ) :
    HasValue 5 (shellStep wait 0) (-1) := by
  have one_unit : IsUnit 5 (1 : ℚ) := ⟨one_ne_zero, padicValRat.one⟩
  have five_value : HasValue 5 (5 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 5) 1)
  simpa [shellStep] using div_hasValue one_unit five_value

/-- A nonzero step from a unit state is a unit, a valuation-minus-one exit, or a positive exit. -/
private theorem shellStep_fiveUnit_cases
    (wait : ℕ) {state : ℚ} (state_unit : IsUnit 5 state)
    (output_ne : shellStep wait state ≠ 0) :
    HasValue 5 (shellStep wait state) (-1) ∨
      IsUnit 5 (shellStep wait state) ∨
        IsPositive 5 (shellStep wait state) := by
  let output := shellStep wait state
  have scale_unit := exitScale_fiveUnit wait
  have leading_unit : IsUnit 5 (3 * (2 / 3 : ℚ) ^ wait * state) :=
    mul_hasValue scale_unit state_unit
  have five_value : HasValue 5 (5 : ℚ) 1 := by
    simpa using (primePower_hasValue (prime := 5) 1)
  have product_eq :
      5 * output = 3 * (2 / 3 : ℚ) ^ wait * state + 1 := by
    simp only [output, shellStep]
    field_simp
  rcases lt_trichotomy (padicValRat 5 output) 0 with negative | unit_or_positive
  · left
    have numerator_ne : 3 * (2 / 3 : ℚ) ^ wait * state + 1 ≠ 0 := by
      rw [← product_eq]
      exact mul_ne_zero five_value.1 output_ne
    have lower := padicValRat.min_le_padicValRat_add (p := 5) numerator_ne
    rw [leading_unit.2, padicValRat.one, min_self] at lower
    have output_value : HasValue 5 output (padicValRat 5 output) := ⟨output_ne, rfl⟩
    have product_value := mul_hasValue five_value output_value
    have numerator_value :
        padicValRat 5 (3 * (2 / 3 : ℚ) ^ wait * state + 1) =
          1 + padicValRat 5 output := by
      rw [← product_eq]
      exact product_value.2
    have lower' : 0 ≤ 1 + padicValRat 5 output := lower.trans_eq numerator_value
    have valuation_lower : (-1 : ℤ) ≤ padicValRat 5 output := by omega
    have valuation_upper : padicValRat 5 output ≤ (-1 : ℤ) := by omega
    exact ⟨output_ne, le_antisymm valuation_upper valuation_lower⟩
  · rcases unit_or_positive with unit | positive
    · exact Or.inr (Or.inl ⟨output_ne, unit⟩)
    · exact Or.inr (Or.inr ⟨output_ne, positive⟩)

/-- A step that leaves the five-adic unit shell is zero, has valuation minus one, or has
positive valuation. -/
theorem shellStep_fiveUnit_exit_cases
    (wait : ℕ) {state : ℚ} (state_unit : IsUnit 5 state)
    (exits : ¬ IsUnit 5 (shellStep wait state)) :
    shellStep wait state = 0 ∨
      HasValue 5 (shellStep wait state) (-1) ∨
        IsPositive 5 (shellStep wait state) := by
  by_cases output_zero : shellStep wait state = 0
  · exact Or.inl output_zero
  · rcases shellStep_fiveUnit_cases wait state_unit output_zero with
      output_negative | output_unit | output_positive
    · exact Or.inr (Or.inl output_negative)
    · exact False.elim (exits output_unit)
    · exact Or.inr (Or.inr output_positive)

/-- After a positive exit, every nonempty tail has valuation equal to minus its length. -/
private theorem shellRun_fivePositive_cons
    (wait : ℕ) (tail : List ℕ) {state : ℚ} (state_positive : IsPositive 5 state) :
    HasValue 5 (shellRun (wait :: tail) state) (-((wait :: tail).length : ℤ)) := by
  rw [shellRun_cons]
  have first_value := shellStep_fivePositive wait state_positive
  have tail_value := shellRun_fiveNegative tail first_value (by omega)
  have valuation_eq :
      (-1 : ℤ) - tail.length = -((wait :: tail).length : ℤ) := by
    simp
    ring
  rw [← valuation_eq]
  exact tail_value

/-- After a zero exit, every nonempty tail has valuation equal to minus its length. -/
private theorem shellRun_fiveZero_cons (wait : ℕ) (tail : List ℕ) :
    HasValue 5 (shellRun (wait :: tail) 0) (-((wait :: tail).length : ℤ)) := by
  rw [shellRun_cons]
  have first_value := shellStep_fiveZero wait
  have tail_value := shellRun_fiveNegative tail first_value (by omega)
  have valuation_eq :
      (-1 : ℤ) - tail.length = -((wait :: tail).length : ℤ) := by
    simp
    ring
  rw [← valuation_eq]
  exact tail_value

/-- A target reached from a valuation-minus-one exit recovers the whole tail length. -/
private theorem shellRun_fiveNegativeOne_tail_length
    (tail : List ℕ) {state target : ℚ} (state_value : HasValue 5 state (-1))
    (reaches : shellRun tail state = target) :
    tail.length = negativeExitTailLengthCandidate target := by
  have target_value := shellRun_fiveNegative tail state_value (by norm_num)
  rw [negativeExitTailLengthCandidate, ← reaches, target_value.2]
  simp

/-- Once a step exits the five-adic unit shell, a nonempty continuation has one of two exact
five-adic valuations. -/
theorem shellRun_fiveUnit_exit_nonempty_tail_value_cases
    (exitWait : ℕ) {tail : List ℕ} {state target : ℚ}
    (state_unit : IsUnit 5 state) (exits : ¬ IsUnit 5 (shellStep exitWait state))
    (tail_ne : tail ≠ []) (reaches : shellRun tail (shellStep exitWait state) = target) :
    HasValue 5 target (-1 - (tail.length : ℤ)) ∨
      HasValue 5 target (-((tail.length : ℤ))) := by
  rcases shellStep_fiveUnit_exit_cases exitWait state_unit exits with
      output_zero | output_negative | output_positive
  · right
    obtain ⟨wait, rest, tail_eq⟩ := List.exists_cons_of_ne_nil tail_ne
    subst tail
    rw [← reaches, output_zero]
    exact shellRun_fiveZero_cons wait rest
  · left
    rw [← reaches]
    exact shellRun_fiveNegative tail output_negative (by norm_num)
  · right
    obtain ⟨wait, rest, tail_eq⟩ := List.exists_cons_of_ne_nil tail_ne
    subst tail
    rw [← reaches]
    exact shellRun_fivePositive_cons wait rest output_positive

/-- Once a step exits the five-adic unit shell, a nonempty continuation to a fixed target has
one of two target-derived lengths. -/
theorem shellRun_fiveUnit_exit_nonempty_tail_length_cases
    (exitWait : ℕ) {tail : List ℕ} {state target : ℚ}
    (state_unit : IsUnit 5 state) (exits : ¬ IsUnit 5 (shellStep exitWait state))
    (tail_ne : tail ≠ []) (reaches : shellRun tail (shellStep exitWait state) = target) :
    tail.length = negativeExitTailLengthCandidate target ∨
      tail.length = nonnegativeExitTailLengthCandidate target := by
  rcases shellRun_fiveUnit_exit_nonempty_tail_value_cases exitWait state_unit exits tail_ne
      reaches with target_negative | target_nonnegative_exit
  · left
    rw [negativeExitTailLengthCandidate, target_negative.2]
    simp
  · right
    rw [nonnegativeExitTailLengthCandidate, target_nonnegative_exit.2]
    simp

/-- The controlled short-side schedule from the fixed source through one forced exit. -/
def fixedSourceAdjacentContinuationSchedule
    (period nextWait : ℕ) (tail : List ℕ) : List ℕ :=
  [1, 10 * period + 2] ++ nextWait :: tail

/-- A controlled continuation has three fixed blocks before its arbitrary post-exit tail. -/
theorem fixedSourceAdjacentContinuationSchedule_length
    (period nextWait : ℕ) (tail : List ℕ) :
    (fixedSourceAdjacentContinuationSchedule period nextWait tail).length = tail.length + 3 := by
  simp [fixedSourceAdjacentContinuationSchedule]

/-- The controlled schedule from `43/24` is exactly the exit target followed by its tail. -/
theorem fixedSourceAdjacentContinuationSchedule_run
    (period nextWait : ℕ) (tail : List ℕ) :
    shellRun (fixedSourceAdjacentContinuationSchedule period nextWait tail) (43 / 24) =
      shellRun tail (fixedSourceAdjacentExitTarget period nextWait) := by
  obtain ⟨_, _, _, _, _, _, short_target, _⟩ :=
    fixedSourceAdjacentFamily (10 * period)
  rw [fixedSourceAdjacentContinuationSchedule, shellRun_append, short_target, shellRun_cons]
  rfl

/-- Any prescribed target reached after the forced exit recovers the tail length from its
five-adic valuation. -/
theorem fixedSourceAdjacentExitTarget_tail_length
    (period nextWait : ℕ) (tail : List ℕ) {target : ℚ}
    (reaches : shellRun tail (fixedSourceAdjacentExitTarget period nextWait) = target) :
    tail.length = negativeExitTailLengthCandidate target := by
  exact shellRun_fiveNegativeOne_tail_length tail
    (fixedSourceAdjacentExitTarget_fiveNegative period nextWait) reaches

/-- The complete continuation cone reduces to schedules with one target-derived block count. -/
theorem fixedSourceAdjacentContinuation_exists_iff_lengthCandidate (target : ℚ) :
    (∃ period nextWait tail,
        shellRun (fixedSourceAdjacentContinuationSchedule period nextWait tail) (43 / 24) =
          target) ↔
      ∃ period nextWait tail,
        (fixedSourceAdjacentContinuationSchedule period nextWait tail).length =
            negativeExitTailLengthCandidate target + 3 ∧
          shellRun (fixedSourceAdjacentContinuationSchedule period nextWait tail) (43 / 24) =
            target := by
  constructor
  · rintro ⟨period, nextWait, tail, reaches⟩
    have tail_reaches :
        shellRun tail (fixedSourceAdjacentExitTarget period nextWait) = target := by
      rw [← fixedSourceAdjacentContinuationSchedule_run]
      exact reaches
    have tail_length :=
      fixedSourceAdjacentExitTarget_tail_length period nextWait tail tail_reaches
    exact ⟨period, nextWait, tail,
      by rw [fixedSourceAdjacentContinuationSchedule_length, tail_length], reaches⟩
  · rintro ⟨period, nextWait, tail, _, reaches⟩
    exact ⟨period, nextWait, tail, reaches⟩

/-- Every controlled continuation witness has the target-derived translated-letter count in raw
coordinates. -/
theorem fixedSourceAdjacentContinuation_translate_count
    (period nextWait : ℕ) (tail : List ℕ) {target : ℚ}
    (reaches :
      shellRun (fixedSourceAdjacentContinuationSchedule period nextWait tail) (43 / 24) =
        target) :
    (shellRawWord (fixedSourceAdjacentContinuationSchedule period nextWait tail)).count
        .translate = negativeExitTailLengthCandidate target + 3 := by
  rw [shellRawWord_count_translate, fixedSourceAdjacentContinuationSchedule_length]
  have tail_reaches :
      shellRun tail (fixedSourceAdjacentExitTarget period nextWait) = target := by
    rw [← fixedSourceAdjacentContinuationSchedule_run]
    exact reaches
  rw [fixedSourceAdjacentExitTarget_tail_length period nextWait tail tail_reaches]

end MatrixMortality.MixedPrimeDebt
