import MatrixMortality.CubicContinuantSelectedComparator
import MatrixMortality.CubicContinuantSelfBalance

/-!
# Self-balancing cleanup for the selected cubic comparator

The fixed `00` selector rejects every complete clock schedule with too few or too many cleanup
readers.  The proof uses the bounded signed radix and the large exact selector-row offset.
-/

namespace MatrixMortality.CubicReturn.NonPure

open scoped Matrix

/-- Ratio left after the clocked checks and an arbitrary true-reader cleanup suffix. -/
def falseWaitFirstHitSelectedCleanupRatio
    (checks : List (Bool × Bool)) (cleanup : ℕ) : ℚ :=
  continuantMismatchClockRatio ^ checks.length *
    continuantMismatchClockRatio⁻¹ ^ cleanup

/-- Affine shift left after the clocked checks and an arbitrary cleanup suffix. -/
def falseWaitFirstHitSelectedCleanupShift
    (checks : List (Bool × Bool)) (cleanup : ℕ) : ℚ :=
  149 / 252 * (1 - falseWaitFirstHitSelectedCleanupRatio checks cleanup) +
    125 / 48 * falseWaitFirstHitSelectedComparatorDefect checks

/-- Terminal-chart row fixed by the original singleton selector middle. -/
def falseWaitFirstHitSelectedCleanupAnchor : ℚ :=
  -4222765589 / 11070

/-- Exact scalar obstruction to preserving the selected row. -/
def falseWaitFirstHitSelectedCleanupBalance
    (checks : List (Bool × Bool)) (cleanup : ℕ) : ℚ :=
  125 / 48 * falseWaitFirstHitSelectedComparatorDefect checks +
    (falseWaitFirstHitSelectedCleanupAnchor + 149 / 252) *
      (1 - falseWaitFirstHitSelectedCleanupRatio checks cleanup)

/-- Complete clock blocks followed by an arbitrary number of true-reader cleanup blocks. -/
def falseWaitFirstHitSelectedComparatorMiddleWithCleanup
    (checks : List (Bool × Bool)) (cleanup : ℕ) : List Nat :=
  falseWaitFirstHitSingletonMiddle ++ continuantReadWordWithCleanup checks cleanup

/-- Selected comparison word with arbitrary true-reader cleanup multiplicity. -/
def falseWaitFirstHitSelectedComparatorWordWithCleanup
    (checks : List (Bool × Bool)) (cleanup : ℕ) : List Nat :=
  falseWaitFirstHitSingletonPrefix ++
    falseWaitFirstHitRayTransportWord
      (falseWaitFirstHitSelectedComparatorMiddleWithCleanup checks cleanup)

/-- At the prescribed cleanup count, the arbitrary-cleanup word is exactly the balanced selected
comparator from `R32-S71`. -/
theorem falseWaitFirstHitSelectedComparatorWordWithCleanup_balanced
    (checks : List (Bool × Bool)) :
    falseWaitFirstHitSelectedComparatorWordWithCleanup checks checks.length =
      falseWaitFirstHitSelectedComparatorWord checks := by
  simp [falseWaitFirstHitSelectedComparatorWordWithCleanup,
    falseWaitFirstHitSelectedComparatorMiddleWithCleanup,
    falseWaitFirstHitSelectedComparatorWord,
    falseWaitFirstHitSelectedComparatorMiddle,
    continuantReadWordWithCleanup, continuantBalancedReadWord]

/-- Terminal affine product presented to the common-ray connector. -/
def falseWaitFirstHitSelectedComparatorTerminalWithCleanup
    (checks : List (Bool × Bool)) (cleanup : ℕ) : Square (Fin 2) ℚ :=
  continuantMismatchAffine
    (falseWaitFirstHitSelectedCleanupRatio checks cleanup)
    (-762919 / 2 + falseWaitFirstHitSelectedCleanupShift checks cleanup)

/-- Common-ray connector produced by the arbitrary-cleanup terminal product. -/
def falseWaitFirstHitSelectedComparatorLoopWithCleanup
    (checks : List (Bool × Bool)) (cleanup : ℕ) : Square (Fin 2) ℚ :=
  falseWaitFirstHitRayTransportNormalized
    (falseWaitFirstHitSelectedCleanupRatio checks cleanup)
    (-762919 / 2 + falseWaitFirstHitSelectedCleanupShift checks cleanup) 1

/-- Selected common-ray row, with its complete cleanup imbalance exposed as one scalar. -/
def falseWaitFirstHitSelectedComparatorRowWithCleanup
    (checks : List (Bool × Bool)) (cleanup : ℕ) : Fin 2 → ℚ :=
  ![1,
    falseWaitFirstHitBinarySourceCoordinate falseWaitFirstHitSingletonTarget +
      (15 / 68) / falseWaitFirstHitSelectedCleanupRatio checks cleanup *
        falseWaitFirstHitSelectedCleanupBalance checks cleanup]

private theorem selectedMismatchDefect_abs_lt (digits : List ℤ)
    (range : ContinuantMismatchDigits digits) :
    |continuantMismatchDefect digits| < 25 / 21 := by
  induction digits with
  | nil => norm_num [continuantMismatchDefect]
  | cons digit digits induction =>
      have head_range := range digit (by simp)
      have tail_range : ContinuantMismatchDigits digits := by
        intro tail membership
        exact range tail (by simp [membership])
      have tail_bound := induction tail_range
      have digit_bound : |(digit : ℚ)| ≤ 1 := by
        rcases head_range with rfl | rfl | rfl <;> norm_num
      calc
        |continuantMismatchDefect (digit :: digits)| =
            |(digit : ℚ) + (4 / 25) * continuantMismatchDefect digits| := by
              rw [continuantMismatchDefect]
        _ ≤ |(digit : ℚ)| + |(4 / 25) * continuantMismatchDefect digits| :=
          abs_add_le _ _
        _ = |(digit : ℚ)| + (4 / 25) * |continuantMismatchDefect digits| := by
          rw [abs_mul]
          norm_num
        _ ≤ 1 + (4 / 25) * |continuantMismatchDefect digits| := by linarith
        _ < 1 + (4 / 25) * (25 / 21) := by linarith
        _ = 25 / 21 := by norm_num

private theorem selectedMismatchBalanceEquation_forces
    (digits : List ℤ) (cleanup : ℕ) (range : ContinuantMismatchDigits digits)
    (equation :
      continuantMismatchDefect digits =
        (236474506444 / 1614375) *
          (1 - continuantMismatchClockRatio ^ digits.length *
            continuantMismatchClockRatio⁻¹ ^ cleanup)) :
    cleanup = digits.length ∧ ∀ digit ∈ digits, digit = 0 := by
  have defect_bound := selectedMismatchDefect_abs_lt digits range
  rcases lt_trichotomy cleanup digits.length with cleanup_lt | cleanup_eq | count_lt
  · have ratio_eq :
        continuantMismatchClockRatio ^ digits.length *
            continuantMismatchClockRatio⁻¹ ^ cleanup =
          continuantMismatchClockRatio ^ (digits.length - cleanup) :=
      continuantMismatchClock_pow_mul_inverse_pow_of_le
        (Nat.le_of_lt cleanup_lt)
    rw [ratio_eq] at equation
    have exponent_positive : 0 < digits.length - cleanup := by omega
    have power_le :
        continuantMismatchClockRatio ^ (digits.length - cleanup) ≤
          continuantMismatchClockRatio := by
      simpa using
        (pow_le_pow_of_le_one (by norm_num [continuantMismatchClockRatio] :
            (0 : ℚ) ≤ continuantMismatchClockRatio)
          (by norm_num [continuantMismatchClockRatio] :
            continuantMismatchClockRatio ≤ 1)
          (show 1 ≤ digits.length - cleanup by omega))
    have defect_upper : continuantMismatchDefect digits < 25 / 21 :=
      lt_of_le_of_lt (le_abs_self _) defect_bound
    rw [equation] at defect_upper
    have lower_bound :
        (25 / 21 : ℚ) <
          (236474506444 / 1614375) *
            (1 - continuantMismatchClockRatio ^ (digits.length - cleanup)) := by
      have difference_lower :
          (21 / 25 : ℚ) ≤
            1 - continuantMismatchClockRatio ^ (digits.length - cleanup) := by
        norm_num [continuantMismatchClockRatio] at power_le ⊢
        linarith
      have constant_positive : (0 : ℚ) < 236474506444 / 1614375 := by norm_num
      have scaled := mul_le_mul_of_nonneg_left difference_lower constant_positive.le
      have strict :
          (25 / 21 : ℚ) < (236474506444 / 1614375) * (21 / 25) := by
        norm_num
      exact lt_of_lt_of_le strict scaled
    exact (not_lt_of_ge (le_of_lt lower_bound) defect_upper).elim
  · subst cleanup
    have ratio_eq :
        continuantMismatchClockRatio ^ digits.length *
            continuantMismatchClockRatio⁻¹ ^ digits.length = 1 := by
      simpa using
        continuantMismatchClock_pow_mul_inverse_pow_of_le
          (count := digits.length) (cleanup := digits.length) (le_refl digits.length)
    rw [ratio_eq, sub_self, mul_zero] at equation
    exact ⟨rfl, (continuantMismatchDefect_eq_zero_iff digits range).mp equation⟩
  · have ratio_eq :
        continuantMismatchClockRatio ^ digits.length *
            continuantMismatchClockRatio⁻¹ ^ cleanup =
          continuantMismatchClockRatio⁻¹ ^ (cleanup - digits.length) :=
      continuantMismatchClock_pow_mul_inverse_pow_of_le_reverse
        (Nat.le_of_lt count_lt)
    rw [ratio_eq] at equation
    have exponent_positive : 0 < cleanup - digits.length := by omega
    have power_lower :
        continuantMismatchClockRatio⁻¹ ≤
          continuantMismatchClockRatio⁻¹ ^ (cleanup - digits.length) := by
      simpa using
        (pow_le_pow_right₀
          (by norm_num [continuantMismatchClockRatio] :
            (1 : ℚ) ≤ continuantMismatchClockRatio⁻¹)
          (show 1 ≤ cleanup - digits.length by omega))
    have defect_lower : -(25 / 21 : ℚ) < continuantMismatchDefect digits :=
      (abs_lt.mp defect_bound).1
    rw [equation] at defect_lower
    have upper_bound :
        (236474506444 / 1614375) *
            (1 - continuantMismatchClockRatio⁻¹ ^ (cleanup - digits.length)) <
          -(25 / 21 : ℚ) := by
      have difference_upper :
          1 - continuantMismatchClockRatio⁻¹ ^ (cleanup - digits.length) ≤
            -(21 / 4 : ℚ) := by
        norm_num [continuantMismatchClockRatio] at power_lower ⊢
        linarith
      have constant_positive : (0 : ℚ) < 236474506444 / 1614375 := by norm_num
      have scaled := mul_le_mul_of_nonneg_left difference_upper constant_positive.le
      have strict :
          (236474506444 / 1614375 : ℚ) * (-(21 / 4)) < -(25 / 21) := by
        norm_num
      exact lt_of_le_of_lt scaled strict
    exact (not_lt_of_ge (le_of_lt defect_lower) upper_bound).elim

private theorem falseWaitFirstHitSelectedCleanupRatio_ne_zero
    (checks : List (Bool × Bool)) (cleanup : ℕ) :
    falseWaitFirstHitSelectedCleanupRatio checks cleanup ≠ 0 := by
  apply mul_ne_zero <;>
    apply pow_ne_zero <;>
      norm_num [continuantMismatchClockRatio]

/-- The selector-row balance scalar vanishes exactly for the prescribed cleanup count and a
matching comparison schedule. -/
theorem falseWaitFirstHitSelectedCleanupBalance_zero_iff
    (checks : List (Bool × Bool)) (cleanup : ℕ) :
    falseWaitFirstHitSelectedCleanupBalance checks cleanup = 0 ↔
      cleanup = checks.length ∧ ∀ check ∈ checks, check.1 = check.2 := by
  let digits := checks.map continuantReadError
  have range : ContinuantMismatchDigits digits := continuantReadErrors_range checks
  constructor
  · intro balance_zero
    have balance_zero' :
        125 / 48 * continuantMismatchDefect (checks.map continuantReadError) +
          (falseWaitFirstHitSelectedCleanupAnchor + 149 / 252) *
            (1 - continuantMismatchClockRatio ^ checks.length *
              continuantMismatchClockRatio⁻¹ ^ cleanup) = 0 := by
      simpa [falseWaitFirstHitSelectedCleanupBalance,
        falseWaitFirstHitSelectedComparatorDefect,
        falseWaitFirstHitSelectedCleanupRatio] using balance_zero
    have equation' :
        continuantMismatchDefect (checks.map continuantReadError) =
          (236474506444 / 1614375) *
            (1 - continuantMismatchClockRatio ^ checks.length *
              continuantMismatchClockRatio⁻¹ ^ cleanup) := by
      norm_num [falseWaitFirstHitSelectedCleanupAnchor] at balance_zero' ⊢
      linarith
    have equation :
        continuantMismatchDefect digits =
          (236474506444 / 1614375) *
            (1 - continuantMismatchClockRatio ^ digits.length *
              continuantMismatchClockRatio⁻¹ ^ cleanup) := by
      simpa [digits] using equation'
    rcases selectedMismatchBalanceEquation_forces digits cleanup range equation with
      ⟨cleanup_eq, all_zero⟩
    refine ⟨by simpa [digits] using cleanup_eq, ?_⟩
    exact (continuantReadDefect_eq_zero_iff checks).mp
      ((continuantMismatchDefect_eq_zero_iff digits range).mpr all_zero)
  · rintro ⟨cleanup_eq, matching⟩
    have defect_zero : falseWaitFirstHitSelectedComparatorDefect checks = 0 :=
      (continuantReadDefect_eq_zero_iff checks).mpr matching
    have ratio_eq : falseWaitFirstHitSelectedCleanupRatio checks cleanup = 1 := by
      rw [falseWaitFirstHitSelectedCleanupRatio, cleanup_eq,
        continuantMismatchClock_pow_mul_inverse_pow_of_le
          (count := checks.length) (cleanup := checks.length) (le_refl checks.length)]
      simp
    rw [falseWaitFirstHitSelectedCleanupBalance, defect_zero, ratio_eq]
    ring

private theorem falseWaitFirstHitSelectedComparatorResidual_affine
    (checks : List (Bool × Bool)) (cleanup : ℕ) :
    continuantMismatchClockProduct (checks.map continuantReadError) *
        continuantMismatchClockReader ^ cleanup =
      continuantMismatchAffine
        (falseWaitFirstHitSelectedCleanupRatio checks cleanup)
        (falseWaitFirstHitSelectedCleanupShift checks cleanup) := by
  simpa [falseWaitFirstHitSelectedCleanupRatio,
    falseWaitFirstHitSelectedCleanupShift,
    falseWaitFirstHitSelectedComparatorDefect, List.length_map] using
    continuantMismatchClockProduct_cleanup_affine
      (checks.map continuantReadError) cleanup

/-- The arbitrary-cleanup physical middle realizes its exact terminal affine product. -/
theorem falseWaitFirstHitSelectedComparatorMiddleWithCleanup_projectivelyRealizes
    (checks : List (Bool × Bool)) (cleanup : ℕ) :
    continuantProjectivelyRealizes
      (falseWaitFirstHitSelectedComparatorMiddleWithCleanup checks cleanup)
      (falseWaitFirstHitSelectedComparatorTerminalWithCleanup checks cleanup) := by
  have selector := falseWaitFirstHitSingletonMiddle_projectivelyRealizes
  have comparator := continuantReadWordWithCleanup_projectivelyRealizes checks cleanup
  have combined := continuantProjectivelyRealizes_append selector comparator
  rw [falseWaitFirstHitSelectedComparatorResidual_affine] at combined
  have terminal_product :
      falseWaitFirstHitSingletonTranslation *
          continuantMismatchAffine
            (falseWaitFirstHitSelectedCleanupRatio checks cleanup)
            (falseWaitFirstHitSelectedCleanupShift checks cleanup) =
        falseWaitFirstHitSelectedComparatorTerminalWithCleanup checks cleanup := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [falseWaitFirstHitSingletonTranslation, continuantMismatchAffine,
          falseWaitFirstHitSelectedComparatorTerminalWithCleanup,
          Matrix.mul_apply, Fin.sum_univ_succ] <;>
        ring)
  rw [terminal_product] at combined
  simpa only [falseWaitFirstHitSelectedComparatorMiddleWithCleanup] using combined

/-- The transported arbitrary-cleanup comparison has its displayed common-ray chart. -/
theorem falseWaitFirstHitSelectedComparatorConnectorWithCleanup_chart
    (checks : List (Bool × Bool)) (cleanup : ℕ) :
    ∃ scale : ℚ, scale ≠ 0 ∧
      falseWaitFirstHitBinaryBasisInverse *
            wordProduct falseWaitReturn
              (falseWaitFirstHitRayTransportWord
                (falseWaitFirstHitSelectedComparatorMiddleWithCleanup checks cleanup)) *
        falseWaitFirstHitBinaryBasis =
          scale • falseWaitFirstHitSelectedComparatorLoopWithCleanup checks cleanup := by
  have transported :=
    falseWaitFirstHitRayTransport_projectivelyRealizes
      (falseWaitFirstHitSelectedCleanupRatio_ne_zero checks cleanup)
      (falseWaitFirstHitSelectedComparatorMiddleWithCleanup_projectivelyRealizes
        checks cleanup)
  simpa [falseWaitFirstHitSelectedComparatorTerminalWithCleanup,
    continuantMismatchAffine,
    falseWaitFirstHitSelectedComparatorLoopWithCleanup] using transported

/-- The fixed selector prefix exposes exactly the cleanup-balance scalar in its row chart. -/
theorem falseWaitFirstHitSelectedComparatorLoopWithCleanup_row
    (checks : List (Bool × Bool)) (cleanup : ℕ) :
    ![1, 937 / 3321] ᵥ*
        falseWaitFirstHitSelectedComparatorLoopWithCleanup checks cleanup =
      falseWaitFirstHitSelectedComparatorRowWithCleanup checks cleanup := by
  have ratio_ne := falseWaitFirstHitSelectedCleanupRatio_ne_zero checks cleanup
  unfold falseWaitFirstHitSelectedComparatorLoopWithCleanup
  unfold falseWaitFirstHitSelectedComparatorRowWithCleanup
  rw [falseWaitFirstHitSingletonTarget_coordinate]
  ext coordinate
  fin_cases coordinate
  · simp [falseWaitFirstHitRayTransportNormalized, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]
  · simp [falseWaitFirstHitSelectedCleanupBalance,
      falseWaitFirstHitSelectedCleanupShift,
      falseWaitFirstHitSelectedCleanupAnchor,
      falseWaitFirstHitRayTransportNormalized, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ]
    field_simp [ratio_ne]
    ring

/-- The complete physical arbitrary-cleanup comparator has its displayed selected row chart. -/
theorem falseWaitFirstHitSelectedComparatorWordWithCleanup_row
    (checks : List (Bool × Bool)) (cleanup : ℕ) :
    ∃ scale : ℚ, scale ≠ 0 ∧
      (falseWaitSeparatorRow ᵥ*
            wordProduct falseWaitReturn
              (falseWaitFirstHitSelectedComparatorWordWithCleanup checks cleanup)) ᵥ*
          falseWaitFirstHitBinaryBasis =
        scale • falseWaitFirstHitSelectedComparatorRowWithCleanup checks cleanup := by
  rcases falseWaitFirstHitSelectedComparatorConnectorWithCleanup_chart checks cleanup with
    ⟨connectorScale, connectorScale_ne, connectorChart⟩
  refine ⟨(-2905210800 : ℚ) * connectorScale,
    mul_ne_zero (by norm_num) connectorScale_ne, ?_⟩
  rw [falseWaitFirstHitSelectedComparatorWordWithCleanup, wordProduct_append,
    falseWaitFirstHitChart_conjugatedRow,
    falseWaitFirstHitSingletonPrefix_row, connectorChart,
    falseWaitFirstHitChart_vecMul_smul,
    falseWaitFirstHitSelectedComparatorLoopWithCleanup_row]

/-- Every wait in the arbitrary-cleanup selected comparator is strictly positive. -/
theorem falseWaitFirstHitSelectedComparatorWordWithCleanup_positive
    (checks : List (Bool × Bool)) (cleanup : ℕ) :
    ∀ wait ∈ falseWaitFirstHitSelectedComparatorWordWithCleanup checks cleanup, 0 < wait := by
  have middle :
      ∀ wait ∈ falseWaitFirstHitSelectedComparatorMiddleWithCleanup checks cleanup,
        0 < wait := by
    intro wait membership
    rw [falseWaitFirstHitSelectedComparatorMiddleWithCleanup,
      List.mem_append] at membership
    exact membership.elim
      (falseWaitFirstHitSingletonMiddle_positive wait)
      (continuantReadWordWithCleanup_positive checks cleanup wait)
  intro wait membership
  rw [falseWaitFirstHitSelectedComparatorWordWithCleanup,
    List.mem_append] at membership
  rcases membership with prefix_mem | connector_mem
  · simp only [falseWaitFirstHitSingletonPrefix, List.mem_cons,
      List.not_mem_nil, or_false] at prefix_mem
    omega
  · exact falseWaitFirstHitRayTransportWord_positive middle wait connector_mem

private theorem falseWaitFirstHitSelectedComparatorRowWithCleanup_zero_iff
    (checks : List (Bool × Bool)) (cleanup : ℕ) :
    falseWaitFirstHitSelectedComparatorRowWithCleanup checks cleanup ⬝ᵥ
          (wordProduct falseWaitFirstHitBinaryNormalizedLoop
              falseWaitFirstHitSingletonTarget *ᵥ
            falseWaitFirstHitBinarySourceChartVector) = 0 ↔
      cleanup = checks.length ∧ ∀ check ∈ checks, check.1 = check.2 := by
  let source :=
    wordProduct falseWaitFirstHitBinaryNormalizedLoop
        falseWaitFirstHitSingletonTarget *ᵥ
      falseWaitFirstHitBinarySourceChartVector
  have source_lower :
      source 1 =
        -123 *
          (falseWaitFirstHitSingletonTarget.map falseWaitFirstHitBinaryRatio).prod := by
    dsimp [source]
    rw [falseWaitFirstHitBinaryNormalizedLoop_source]
    rfl
  have source_lower_ne : source 1 ≠ 0 := by
    rw [source_lower]
    exact mul_ne_zero (by norm_num)
      (falseWaitFirstHitBinaryRatioProduct_ne_zero falseWaitFirstHitSingletonTarget)
  have base_zero :
      ![1,
          falseWaitFirstHitBinarySourceCoordinate falseWaitFirstHitSingletonTarget] ⬝ᵥ
        source = 0 := by
    exact (falseWaitFirstHitBinarySourceRow_zero_iff
      falseWaitFirstHitSingletonTarget falseWaitFirstHitSingletonTarget).2 rfl
  have ratio_ne := falseWaitFirstHitSelectedCleanupRatio_ne_zero checks cleanup
  have incidence :
      falseWaitFirstHitSelectedComparatorRowWithCleanup checks cleanup ⬝ᵥ source =
        ((15 / 68) / falseWaitFirstHitSelectedCleanupRatio checks cleanup *
          falseWaitFirstHitSelectedCleanupBalance checks cleanup) * source 1 := by
    rw [falseWaitFirstHitSelectedComparatorRowWithCleanup]
    simp [dotProduct, Fin.sum_univ_succ] at base_zero
    simp [dotProduct, Fin.sum_univ_succ]
    linarith
  change falseWaitFirstHitSelectedComparatorRowWithCleanup checks cleanup ⬝ᵥ source = 0 ↔ _
  rw [incidence, mul_eq_zero, or_iff_left source_lower_ne,
    mul_eq_zero,
    or_iff_right (div_ne_zero (by norm_num : (15 / 68 : ℚ) ≠ 0) ratio_ne)]
  exact falseWaitFirstHitSelectedCleanupBalance_zero_iff checks cleanup

/-- Physical arbitrary-cleanup selected incidence is a nonzero scale times its normalized
incidence. -/
theorem falseWaitFirstHitSelectedComparatorWordWithCleanup_incidence
    (checks : List (Bool × Bool)) (cleanup : ℕ) :
    ∃ scale : ℚ, scale ≠ 0 ∧
      falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn
            (falseWaitFirstHitSelectedComparatorWordWithCleanup checks cleanup ++
              falseWaitFirstHitBinaryEncoding falseWaitFirstHitSingletonTarget) *ᵥ
            falseWaitSeparatorColumn) =
        scale *
          (falseWaitFirstHitSelectedComparatorRowWithCleanup checks cleanup ⬝ᵥ
            (wordProduct falseWaitFirstHitBinaryNormalizedLoop
                falseWaitFirstHitSingletonTarget *ᵥ
              falseWaitFirstHitBinarySourceChartVector)) := by
  rcases falseWaitFirstHitSelectedComparatorWordWithCleanup_row checks cleanup with
    ⟨rowScale, rowScale_ne, rowChart⟩
  exact falseWaitFirstHitChartRow_incidence
    (falseWaitFirstHitSelectedComparatorWordWithCleanup checks cleanup)
    (falseWaitFirstHitSelectedComparatorRowWithCleanup checks cleanup)
    rowScale rowScale_ne rowChart falseWaitFirstHitSingletonTarget

/-- The physical selected incidence self-enforces cleanup count and every bit comparison. -/
theorem falseWaitFirstHitSelectedComparatorWordWithCleanup_zero_iff
    (checks : List (Bool × Bool)) (cleanup : ℕ) :
    falseWaitSeparatorRow ⬝ᵥ
          (wordProduct falseWaitReturn
            (falseWaitFirstHitSelectedComparatorWordWithCleanup checks cleanup ++
              falseWaitFirstHitBinaryEncoding falseWaitFirstHitSingletonTarget) *ᵥ
            falseWaitSeparatorColumn) = 0 ↔
      cleanup = checks.length ∧ ∀ check ∈ checks, check.1 = check.2 := by
  rcases falseWaitFirstHitSelectedComparatorWordWithCleanup_incidence checks cleanup with
    ⟨scale, scale_ne, incidence⟩
  rw [incidence, mul_eq_zero, or_iff_right scale_ne]
  exact falseWaitFirstHitSelectedComparatorRowWithCleanup_zero_iff checks cleanup

end MatrixMortality.CubicReturn.NonPure
