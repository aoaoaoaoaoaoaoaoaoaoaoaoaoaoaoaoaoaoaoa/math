import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Complex.ExponentialBounds

namespace Frankl

open Finset Real

/-- The first `terms` Taylor terms for `log x`, expanded at `x = 1`. -/
noncomputable def logSeries (terms : ℕ) (x : ℝ) : ℝ :=
  -∑ i ∈ range terms, (1 - x) ^ (i + 1) / (i + 1)

/-- The geometric remainder bound for `logSeries`. -/
noncomputable def logSeriesError (terms : ℕ) (x : ℝ) : ℝ :=
  |1 - x| ^ (terms + 1) / (1 - |1 - x|)

theorem abs_log_sub_logSeries_le {terms : ℕ} {x : ℝ} (hx : |1 - x| < 1) :
    |log x - logSeries terms x| ≤ logSeriesError terms x := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 1 - x) hx terms
  rw [show 1 - (1 - x) = x by ring] at h
  simpa only [logSeries, logSeriesError, sub_neg_eq_add, abs_sub_comm, add_comm] using h

/-- A logarithm approximation after scaling its argument by `2 ^ scale` into the Taylor
window around one. -/
noncomputable def scaledLogSeries (terms scale : ℕ) (x : ℝ) : ℝ :=
  logSeries terms ((2 : ℝ) ^ scale * x) + scale * logSeries terms (1 / 2)

/-- Error accumulated by the scaled approximation, including its reused approximation to
`log (1 / 2)`. -/
noncomputable def scaledLogSeriesError (terms scale : ℕ) (x : ℝ) : ℝ :=
  logSeriesError terms ((2 : ℝ) ^ scale * x)
    + scale * logSeriesError terms (1 / 2)

theorem abs_log_sub_scaledLogSeries_le {terms scale : ℕ} {x : ℝ} (hx : 0 < x)
    (hscaled : |1 - (2 : ℝ) ^ scale * x| < 1) :
    |log x - scaledLogSeries terms scale x| ≤
      scaledLogSeriesError terms scale x := by
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hxne : x ≠ 0 := hx.ne'
  have hscaledApprox := abs_log_sub_logSeries_le (terms := terms) hscaled
  have hhalfApprox := abs_log_sub_logSeries_le (terms := terms)
    (x := (1 : ℝ) / 2) (by norm_num [abs_of_nonneg])
  have hlogScaled :
      log ((2 : ℝ) ^ scale * x) = scale * log 2 + log x := by
    rw [log_mul (pow_ne_zero scale htwo) hxne, log_pow]
  have hlogHalf : log ((1 : ℝ) / 2) = -log 2 := by
    rw [one_div, log_inv]
  have hidentity :
      log x - scaledLogSeries terms scale x =
        (log ((2 : ℝ) ^ scale * x)
            - logSeries terms ((2 : ℝ) ^ scale * x))
          + scale * (log ((1 : ℝ) / 2) - logSeries terms (1 / 2)) := by
    rw [hlogScaled, hlogHalf]
    simp only [scaledLogSeries]
    ring
  rw [hidentity, scaledLogSeriesError]
  calc
    |(log ((2 : ℝ) ^ scale * x) - logSeries terms ((2 : ℝ) ^ scale * x))
        + scale * (log ((1 : ℝ) / 2) - logSeries terms (1 / 2))| ≤
        |log ((2 : ℝ) ^ scale * x)
            - logSeries terms ((2 : ℝ) ^ scale * x)|
          + |scale * (log ((1 : ℝ) / 2) - logSeries terms (1 / 2))| :=
      abs_add _ _
    _ = |log ((2 : ℝ) ^ scale * x)
            - logSeries terms ((2 : ℝ) ^ scale * x)|
          + scale * |log ((1 : ℝ) / 2) - logSeries terms (1 / 2)| := by
      have hscaleAbs : |(scale : ℝ)| = scale :=
        abs_of_nonneg (Nat.cast_nonneg scale)
      rw [abs_mul, hscaleAbs]
    _ ≤ logSeriesError terms ((2 : ℝ) ^ scale * x)
          + scale * logSeriesError terms (1 / 2) := by
      gcongr

/-- Four odd terms of the inverse-hyperbolic-tangent expansion of a logarithm. -/
noncomputable def atanhLogFour (z : ℝ) : ℝ :=
  2 * (z + z ^ 3 / 3 + z ^ 5 / 5 + z ^ 7 / 7)

/-- A deliberately elementary remainder bound for `atanhLogFour`. -/
noncomputable def atanhLogFourError (z : ℝ) : ℝ :=
  2 * |z| ^ 9 / (1 - |z|)

/-- The paired Taylor expansions at `1-z` and `1+z` leave only four odd terms. -/
theorem abs_log_ratio_sub_atanhLogFour_le {z : ℝ} (hz : |z| < 1) :
    |log ((1 + z) / (1 - z)) - atanhLogFour z| ≤ atanhLogFourError z := by
  have hplus := abs_log_sub_logSeries_le (terms := 8) (x := 1 + z) (by simpa)
  have hminus := abs_log_sub_logSeries_le (terms := 8) (x := 1 - z) (by simpa)
  have hplusPos : 0 < 1 + z := by
    rw [abs_lt] at hz
    linarith
  have hminusPos : 0 < 1 - z := by
    rw [abs_lt] at hz
    linarith
  have hlog : log ((1 + z) / (1 - z)) = log (1 + z) - log (1 - z) := by
    exact log_div hplusPos.ne' hminusPos.ne'
  have hseries :
      logSeries 8 (1 + z) - logSeries 8 (1 - z) = atanhLogFour z := by
    norm_num [logSeries, atanhLogFour, sum_range_succ]
    ring
  rw [hlog, ← hseries, show atanhLogFourError z =
      logSeriesError 8 (1 + z) + logSeriesError 8 (1 - z) by
        simp only [atanhLogFourError, logSeriesError]
        rw [show 1 - (1 + z) = -z by ring, show 1 - (1 - z) = z by ring, abs_neg]
        ring]
  rw [show log (1 + z) - log (1 - z) -
      (logSeries 8 (1 + z) - logSeries 8 (1 - z)) =
      (log (1 + z) - logSeries 8 (1 + z)) -
        (log (1 - z) - logSeries 8 (1 - z)) by ring]
  exact (abs_sub _ _).trans (add_le_add hplus hminus)

/-- Exact rational center of the standard ten-digit enclosure of `log 2`. -/
noncomputable def logTwoCenter : ℝ := 13862943611 / 20000000000

/-- Radius of the standard ten-digit enclosure of `log 2`. -/
noncomputable def logTwoRadius : ℝ := 1 / 4000000000

theorem abs_log_two_sub_center_le :
    |log 2 - logTwoCenter| ≤ logTwoRadius := by
  have hlower : (6931471803 : ℝ) / 10000000000 < log 2 := by
    rw [show (6931471803 : ℝ) / 10000000000 = 0.6931471803 by norm_num]
    exact log_two_gt_d9
  have hupper : log 2 < (6931471808 : ℝ) / 10000000000 := by
    rw [show (6931471808 : ℝ) / 10000000000 = 0.6931471808 by norm_num]
    exact log_two_lt_d9
  rw [abs_le]
  dsimp [logTwoCenter, logTwoRadius]
  constructor <;> linarith

/-- Fast scaled logarithm approximation: four odd terms plus the fixed enclosure of `log 2`. -/
noncomputable def fastScaledLog (scale : ℕ) (x : ℝ) : ℝ :=
  let scaled := (2 : ℝ) ^ scale * x
  let z := (scaled - 1) / (scaled + 1)
  atanhLogFour z - scale * logTwoCenter

/-- Error radius of `fastScaledLog`. -/
noncomputable def fastScaledLogError (scale : ℕ) (x : ℝ) : ℝ :=
  let scaled := (2 : ℝ) ^ scale * x
  let z := (scaled - 1) / (scaled + 1)
  atanhLogFourError z + scale * logTwoRadius

theorem abs_log_sub_fastScaledLog_le {scale : ℕ} {x : ℝ} (hx : 0 < x)
    (hz : let scaled := (2 : ℝ) ^ scale * x
      |(scaled - 1) / (scaled + 1)| < 1) :
    |log x - fastScaledLog scale x| ≤ fastScaledLogError scale x := by
  let scaled := (2 : ℝ) ^ scale * x
  let z := (scaled - 1) / (scaled + 1)
  have hdenominator : scaled + 1 ≠ 0 := by positivity
  have hratio : (1 + z) / (1 - z) = scaled := by
    dsimp [z]
    field_simp [hdenominator]
    ring
  have hatanh := abs_log_ratio_sub_atanhLogFour_le (show |z| < 1 by exact hz)
  rw [hratio] at hatanh
  have hscaledLog : log scaled = scale * log 2 + log x := by
    dsimp [scaled]
    rw [log_mul (pow_ne_zero scale (by norm_num)) hx.ne', log_pow]
  have htwo := abs_log_two_sub_center_le
  dsimp [fastScaledLog, fastScaledLogError]
  change |log x - (atanhLogFour z - scale * logTwoCenter)| ≤
    atanhLogFourError z + scale * logTwoRadius
  rw [show log x = log scaled - scale * log 2 by rw [hscaledLog]; ring]
  have hidentity :
      log scaled - scale * log 2 - (atanhLogFour z - scale * logTwoCenter) =
        (log scaled - atanhLogFour z) - scale * (log 2 - logTwoCenter) := by ring
  rw [hidentity]
  calc
    |(log scaled - atanhLogFour z) - scale * (log 2 - logTwoCenter)| ≤
        |log scaled - atanhLogFour z| + |scale * (log 2 - logTwoCenter)| :=
      abs_sub _ _
    _ = |log scaled - atanhLogFour z| + scale * |log 2 - logTwoCenter| := by
      have hscaleAbs : |(scale : ℝ)| = scale :=
        abs_of_nonneg (Nat.cast_nonneg scale)
      rw [abs_mul (scale : ℝ) (log 2 - logTwoCenter),
        hscaleAbs]
    _ ≤ atanhLogFourError z + scale * logTwoRadius := by
      gcongr

end Frankl
