import Frankl.Interval
import Frankl.Entropy

namespace Frankl

open Real Set

namespace RatBall

private theorem cast_le_half {x : ℚ} (hx : x ≤ 1 / 2) :
    (x : ℝ) ≤ (2 : ℝ)⁻¹ := by
  rw [← show (((1 / 2 : ℚ) : ℝ)) = (2 : ℝ)⁻¹ by norm_num]
  exact_mod_cast hx

private theorem half_le_cast {x : ℚ} (hx : 1 / 2 ≤ x) :
    (2 : ℝ)⁻¹ ≤ (x : ℝ) := by
  rw [← show (((1 / 2 : ℚ) : ℝ)) = (2 : ℝ)⁻¹ by norm_num]
  exact_mod_cast hx

/-- A rounded pointwise logarithm enclosure. -/
def roundedRationalLogBall (terms fuel bits : ℕ) (x : ℚ) : Option RatBall :=
  (rationalLogBall terms fuel x).map (round bits)

/-- A rounded monotone logarithm enclosure. -/
def roundedIntervalLogBall (terms fuel bits : ℕ) (ball : RatBall) : Option RatBall :=
  (intervalLogBall terms fuel ball).map (round bits)

theorem roundedRationalLogBall_contains {terms fuel bits : ℕ} {x : ℚ} {ball : RatBall}
    (hball : roundedRationalLogBall terms fuel bits x = some ball) :
    ball.Contains (log x) := by
  unfold roundedRationalLogBall at hball
  cases hresult : rationalLogBall terms fuel x with
  | none => simp [hresult] at hball
  | some raw =>
    simp [hresult] at hball
    subst ball
    exact round_contains (rationalLogBall_contains hresult)

theorem roundedIntervalLogBall_contains {terms fuel bits : ℕ} {source ball : RatBall}
    {x : ℝ} (hx : source.Contains x)
    (hball : roundedIntervalLogBall terms fuel bits source = some ball) :
    ball.Contains (log x) := by
  unfold roundedIntervalLogBall at hball
  cases hresult : intervalLogBall terms fuel source with
  | none => simp [hresult] at hball
  | some raw =>
    simp [hresult] at hball
    subst ball
    exact round_contains (intervalLogBall_contains hx hresult)

/-- A rounded enclosure of `log 2`, obtained from `-log (1/2)`. -/
def logTwoBall (terms fuel bits : ℕ) : Option RatBall :=
  (roundedRationalLogBall terms fuel bits (1 / 2)).map neg

theorem logTwoBall_contains {terms fuel bits : ℕ} {ball : RatBall}
    (hball : logTwoBall terms fuel bits = some ball) : ball.Contains (log 2) := by
  simp only [logTwoBall, Option.map_eq_some'] at hball
  rcases hball with ⟨halfLog, hhalfLog, rfl⟩
  have hhalf := roundedRationalLogBall_contains hhalfLog
  have hneg := neg_contains hhalf
  simpa [show (((1 / 2 : ℚ) : ℝ)) = (1 : ℝ) / 2 by norm_num,
    one_div, log_inv] using hneg

/-- A rounded point enclosure of binary entropy at a rational argument. -/
def entropyPointBall (terms fuel bits : ℕ) (x : ℚ) : Option RatBall :=
  if x = 0 ∨ x = 1 then
    some (point 0)
  else do
    let leftLog ← roundedRationalLogBall terms fuel bits x
    let rightLog ← roundedRationalLogBall terms fuel bits (1 - x)
    let left := (mul (point (-x)) leftLog).round bits
    let right := (mul (point (x - 1)) rightLog).round bits
    some (add left right |>.round bits)

theorem entropyPointBall_contains {terms fuel bits : ℕ} {x : ℚ} {ball : RatBall}
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1)
    (hball : entropyPointBall terms fuel bits x = some ball) :
    ball.Contains (binEntropy x) := by
  simp only [entropyPointBall] at hball
  split at hball <;> rename_i hendpoint
  · simp only [Option.some.injEq] at hball
    subst ball
    rcases hendpoint with rfl | rfl <;>
      simpa using point_contains 0
  · push_neg at hendpoint
    generalize hleftResult : roundedRationalLogBall terms fuel bits x = leftResult at hball
    cases leftResult with
    | none => simp [hleftResult] at hball
    | some leftLog =>
      generalize hrightResult :
          roundedRationalLogBall terms fuel bits (1 - x) = rightResult at hball
      cases rightResult with
      | none => simp [hleftResult, hrightResult] at hball
      | some rightLog =>
        simp [hleftResult, hrightResult] at hball
        subst ball
        have hleftLog := roundedRationalLogBall_contains hleftResult
        have hrightLog := roundedRationalLogBall_contains hrightResult
        have hleftPoint : (point (-x)).Contains (-x : ℚ) := point_contains _
        have hrightPoint : (point (x - 1)).Contains (x - 1 : ℚ) := point_contains _
        have hleft := round_contains (bits := bits) (mul_contains hleftPoint hleftLog)
        have hright := round_contains (bits := bits) (mul_contains hrightPoint hrightLog)
        have hsum := round_contains (bits := bits) (add_contains hleft hright)
        rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
        simpa only [Real.negMulLog, Rat.cast_neg, Rat.cast_sub, Rat.cast_one,
          neg_sub] using hsum

/-- The sharp monotonicity enclosure of binary entropy on a rational ball. The source ball may
protrude beyond `[0,1]`; soundness requires the enclosed semantic value to remain in that
probability interval. -/
def entropyRangeBall (terms fuel bits : ℕ) (source : RatBall) : Option RatBall := do
  let lower := max source.lower 0
  let upper := min source.upper 1
  let lowerEntropy ← entropyPointBall terms fuel bits lower
  let upperEntropy ← entropyPointBall terms fuel bits upper
  let logTwo ← logTwoBall terms fuel bits
  let range :=
    if upper ≤ 1 / 2 then
      ofBounds lowerEntropy.lower upperEntropy.upper
    else if 1 / 2 ≤ lower then
      ofBounds upperEntropy.lower lowerEntropy.upper
    else
      ofBounds (min lowerEntropy.lower upperEntropy.lower) logTwo.upper
  some (range.round bits)

theorem entropyRangeBall_contains {terms fuel bits : ℕ} {source ball : RatBall} {x : ℝ}
    (hx : source.Contains x) (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1)
    (hball : entropyRangeBall terms fuel bits source = some ball) :
    ball.Contains (binEntropy x) := by
  let lower := max source.lower 0
  let upper := min source.upper 1
  have hsourceBounds := contains_iff_bounds.mp hx
  have hlowerX : (lower : ℝ) ≤ x := by
    dsimp [lower]
    push_cast
    exact max_le hsourceBounds.1 hx₀
  have hxUpper : x ≤ (upper : ℝ) := by
    dsimp [upper]
    push_cast
    exact le_min hsourceBounds.2 hx₁
  have hlowerUpper : lower ≤ upper := by
    exact_mod_cast hlowerX.trans hxUpper
  have hlower₀ : (0 : ℚ) ≤ lower := le_max_right _ _
  have hlower₁ : lower ≤ 1 := by
    exact_mod_cast hlowerX.trans hx₁
  have hupper₀ : (0 : ℚ) ≤ upper := by
    exact_mod_cast hx₀.trans hxUpper
  have hupper₁ : upper ≤ 1 := min_le_right _ _
  unfold entropyRangeBall at hball
  generalize hlowerResult : entropyPointBall terms fuel bits lower = lowerResult at hball
  cases lowerResult with
  | none => simp [lower, upper, hlowerResult] at hball
  | some lowerEntropy =>
    generalize hupperResult : entropyPointBall terms fuel bits upper = upperResult at hball
    cases upperResult with
    | none => simp [lower, upper, hlowerResult, hupperResult] at hball
    | some upperEntropy =>
      generalize htwoResult : logTwoBall terms fuel bits = twoResult at hball
      cases twoResult with
      | none => simp [lower, upper, hlowerResult, hupperResult, htwoResult] at hball
      | some logTwo =>
        simp only [lower, upper, hlowerResult, hupperResult, htwoResult,
          Option.bind_eq_bind] at hball
        split at hball <;> rename_i hupperHalf
        · simp at hball
          subst ball
          have hlowerContains := entropyPointBall_contains hlower₀ hlower₁ hlowerResult
          have hupperContains := entropyPointBall_contains hupper₀ hupper₁ hupperResult
          have hlowerBounds := contains_iff_bounds.mp hlowerContains
          have hupperBounds := contains_iff_bounds.mp hupperContains
          have hxHalf : x ≤ (2 : ℝ)⁻¹ :=
            hxUpper.trans (cast_le_half hupperHalf)
          have hmonoLower : binEntropy (lower : ℝ) ≤ binEntropy x :=
            binEntropy_strictMonoOn.monotoneOn
              ⟨by exact_mod_cast hlower₀, cast_le_half (hlowerUpper.trans hupperHalf)⟩
              ⟨hx₀, hxHalf⟩ hlowerX
          have hmonoUpper : binEntropy x ≤ binEntropy (upper : ℝ) :=
            binEntropy_strictMonoOn.monotoneOn
              ⟨hx₀, hxHalf⟩ ⟨by exact_mod_cast hupper₀, cast_le_half hupperHalf⟩ hxUpper
          exact round_contains (ofBounds_contains
            (hlowerBounds.1.trans hmonoLower) (hmonoUpper.trans hupperBounds.2))
        · split at hball <;> rename_i hhalfLower
          · simp at hball
            subst ball
            have hlowerContains := entropyPointBall_contains hlower₀ hlower₁ hlowerResult
            have hupperContains := entropyPointBall_contains hupper₀ hupper₁ hupperResult
            have hlowerBounds := contains_iff_bounds.mp hlowerContains
            have hupperBounds := contains_iff_bounds.mp hupperContains
            have hhalfX : (2 : ℝ)⁻¹ ≤ x :=
              (half_le_cast hhalfLower).trans hlowerX
            have hantiLower : binEntropy (upper : ℝ) ≤ binEntropy x :=
              binEntropy_strictAntiOn.antitoneOn
                ⟨hhalfX, hx₁⟩ ⟨half_le_cast (hhalfLower.trans hlowerUpper),
                  by exact_mod_cast hupper₁⟩ hxUpper
            have hantiUpper : binEntropy x ≤ binEntropy (lower : ℝ) :=
              binEntropy_strictAntiOn.antitoneOn
                ⟨half_le_cast hhalfLower, by exact_mod_cast hlower₁⟩
                ⟨hhalfX, hx₁⟩ hlowerX
            exact round_contains (ofBounds_contains
              (hupperBounds.1.trans hantiLower) (hantiUpper.trans hlowerBounds.2))
          · simp at hball
            subst ball
            have hlowerContains := entropyPointBall_contains hlower₀ hlower₁ hlowerResult
            have hupperContains := entropyPointBall_contains hupper₀ hupper₁ hupperResult
            have htwoContains := logTwoBall_contains htwoResult
            have hlowerBounds := contains_iff_bounds.mp hlowerContains
            have hupperBounds := contains_iff_bounds.mp hupperContains
            have htwoBounds := contains_iff_bounds.mp htwoContains
            apply round_contains
            apply ofBounds_contains
            · rcases le_total x ((2 : ℝ)⁻¹) with hxHalf | hhalfX
              · have hmono : binEntropy (lower : ℝ) ≤ binEntropy x :=
                  binEntropy_strictMonoOn.monotoneOn
                    ⟨by exact_mod_cast hlower₀,
                      cast_le_half (lt_of_not_ge hhalfLower).le⟩
                    ⟨hx₀, hxHalf⟩ hlowerX
                have hmin :
                    ((min lowerEntropy.lower upperEntropy.lower : ℚ) : ℝ) ≤
                      lowerEntropy.lower := by
                  exact_mod_cast min_le_left lowerEntropy.lower upperEntropy.lower
                exact hmin.trans (hlowerBounds.1.trans hmono)
              · have hanti : binEntropy (upper : ℝ) ≤ binEntropy x :=
                  binEntropy_strictAntiOn.antitoneOn
                    ⟨hhalfX, hx₁⟩ ⟨by
                      exact half_le_cast (lt_of_not_ge hupperHalf).le,
                      by exact_mod_cast hupper₁⟩ hxUpper
                have hmin :
                    ((min lowerEntropy.lower upperEntropy.lower : ℚ) : ℝ) ≤
                      upperEntropy.lower := by
                  exact_mod_cast min_le_right lowerEntropy.lower upperEntropy.lower
                exact hmin.trans (hupperBounds.1.trans hanti)
            · exact binEntropy_le_log_two.trans htwoBounds.2

end RatBall

end Frankl
