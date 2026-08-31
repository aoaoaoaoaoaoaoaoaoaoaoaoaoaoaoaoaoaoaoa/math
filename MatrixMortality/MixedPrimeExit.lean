import MatrixMortality.MixedPrimeDebt

/-!
# Fixed-source mixed-prime exit cone

The five-adic target valuation fixes the number of blocks after the forced exit. Combined with
the prescribed-translation-count algorithm, this makes the entire controlled continuation cone
from the accepted fixed-source collision ray decidable.
-/

namespace MatrixMortality.MixedPrimeDebt

open PadicValuation
open PeriodicShell

/-- The only possible number of shell blocks after a forced exit reaching `target`. -/
def fixedSourceAdjacentExitTailLengthCandidate (target : ℚ) : ℕ :=
  Int.toNat (-padicValRat 5 target - 1)

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
    tail.length = fixedSourceAdjacentExitTailLengthCandidate target := by
  have target_value := fixedSourceAdjacentExitTarget_tail_fiveNegative period nextWait tail
  rw [fixedSourceAdjacentExitTailLengthCandidate, ← reaches, target_value.2]
  simp

/-- The complete continuation cone reduces to schedules with one target-derived block count. -/
theorem fixedSourceAdjacentContinuation_exists_iff_lengthCandidate (target : ℚ) :
    (∃ period nextWait tail,
        shellRun (fixedSourceAdjacentContinuationSchedule period nextWait tail) (43 / 24) =
          target) ↔
      ∃ period nextWait tail,
        (fixedSourceAdjacentContinuationSchedule period nextWait tail).length =
            fixedSourceAdjacentExitTailLengthCandidate target + 3 ∧
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
        .translate = fixedSourceAdjacentExitTailLengthCandidate target + 3 := by
  rw [shellRawWord_count_translate, fixedSourceAdjacentContinuationSchedule_length]
  have tail_reaches :
      shellRun tail (fixedSourceAdjacentExitTarget period nextWait) = target := by
    rw [← fixedSourceAdjacentContinuationSchedule_run]
    exact reaches
  rw [fixedSourceAdjacentExitTarget_tail_length period nextWait tail tail_reaches]

end MatrixMortality.MixedPrimeDebt
