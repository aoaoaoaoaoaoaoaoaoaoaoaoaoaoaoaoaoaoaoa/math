import Frankl.LogBounds
import Mathlib.Data.Rat.Floor

namespace Frankl

open Finset Real

/-- An exact rational ball. The checker rejects negative radii at its boundary. -/
structure RatBall where
  /-- Midpoint of the enclosure. -/
  center : ℚ
  /-- Symmetric error radius about the midpoint. -/
  radius : ℚ
deriving DecidableEq, Repr

namespace RatBall

/-- The real value lies in the closed rational ball. -/
def Contains (ball : RatBall) (value : ℝ) : Prop :=
  |value - ball.center| ≤ ball.radius

/-- Lower endpoint of a rational ball. -/
def lower (ball : RatBall) : ℚ := ball.center - ball.radius

/-- Upper endpoint of a rational ball. -/
def upper (ball : RatBall) : ℚ := ball.center + ball.radius

/-- Maximum endpoint magnitude of a rational ball. -/
def absUpper (ball : RatBall) : ℚ := max |ball.lower| |ball.upper|

/-- The least rational ball with the supplied ordered endpoints. -/
def ofBounds (lower upper : ℚ) : RatBall :=
  ⟨(lower + upper) / 2, (upper - lower) / 2⟩

/-- A point ball. -/
def point (value : ℚ) : RatBall := ⟨value, 0⟩

/-- Outward dyadic rounding of a rational ball. -/
def round (bits : ℕ) (ball : RatBall) : RatBall :=
  let scale := (2 : ℚ) ^ bits
  ofBounds (⌊ball.lower * scale⌋ / scale) (⌈ball.upper * scale⌉ / scale)

@[simp]
theorem round_lower (bits : ℕ) (ball : RatBall) :
    (ball.round bits).lower = ⌊ball.lower * (2 : ℚ) ^ bits⌋ / (2 : ℚ) ^ bits := by
  simp only [round, lower, ofBounds]
  ring

@[simp]
theorem round_upper (bits : ℕ) (ball : RatBall) :
    (ball.round bits).upper = ⌈ball.upper * (2 : ℚ) ^ bits⌉ / (2 : ℚ) ^ bits := by
  simp only [round, upper, ofBounds]
  ring

/-- Ball addition. -/
def add (left right : RatBall) : RatBall :=
  ⟨left.center + right.center, left.radius + right.radius⟩

/-- Ball negation. -/
def neg (ball : RatBall) : RatBall := ⟨-ball.center, ball.radius⟩

/-- Ball subtraction. -/
def sub (left right : RatBall) : RatBall := add left (neg right)

/-- Exact-radius ball multiplication. -/
def mul (left right : RatBall) : RatBall :=
  ⟨left.center * right.center,
    |left.center| * right.radius + |right.center| * left.radius
      + left.radius * right.radius⟩

/-- Reciprocal enclosure, defined only when the entire ball is positive. -/
def inv? (ball : RatBall) : Option RatBall :=
  if 0 < ball.lower then
    some (ofBounds (1 / ball.upper) (1 / ball.lower))
  else
    none

/-- Rounded ball addition. -/
def roundedAdd (bits : ℕ) (left right : RatBall) : RatBall :=
  (add left right).round bits

/-- Rounded ball subtraction. -/
def roundedSub (bits : ℕ) (left right : RatBall) : RatBall :=
  (sub left right).round bits

/-- Rounded ball multiplication. -/
def roundedMul (bits : ℕ) (left right : RatBall) : RatBall :=
  (mul left right).round bits

/-- Rounded reciprocal enclosure. -/
def roundedInv? (bits : ℕ) (ball : RatBall) : Option RatBall :=
  (inv? ball).map (round bits)

/-- Lower midpoint half of a rational ball. -/
def lowerHalf (ball : RatBall) : RatBall := ofBounds ball.lower ball.center

/-- Upper midpoint half of a rational ball. -/
def upperHalf (ball : RatBall) : RatBall := ofBounds ball.center ball.upper

/-- Lower piece of a rational ball at a supplied cut. -/
def lowerAt (ball : RatBall) (cut : ℚ) : RatBall := ofBounds ball.lower cut

/-- Upper piece of a rational ball at a supplied cut. -/
def upperAt (ball : RatBall) (cut : ℚ) : RatBall := ofBounds cut ball.upper

theorem contains_iff_bounds {ball : RatBall} {value : ℝ} :
    ball.Contains value ↔ ball.lower ≤ value ∧ value ≤ ball.upper := by
  simp only [Contains, lower, upper]
  push_cast
  rw [abs_le]
  constructor <;> rintro ⟨hlower, hupper⟩ <;> constructor <;>
    linarith

theorem abs_le_absUpper {ball : RatBall} {value : ℝ} (hvalue : ball.Contains value) :
    |value| ≤ ball.absUpper := by
  have hbounds := contains_iff_bounds.mp hvalue
  by_cases hnonnegative : 0 ≤ value
  · rw [abs_of_nonneg hnonnegative]
    calc
      value ≤ ball.upper := hbounds.2
      _ ≤ |(ball.upper : ℝ)| := le_abs_self _
      _ = (|ball.upper| : ℚ) := by norm_cast
      _ ≤ (max |ball.lower| |ball.upper| : ℚ) := by exact_mod_cast le_max_right _ _
  · have hnonpositive : value ≤ 0 := le_of_not_ge hnonnegative
    rw [abs_of_nonpos hnonpositive]
    calc
      -value ≤ -(ball.lower : ℝ) := neg_le_neg hbounds.1
      _ ≤ |(ball.lower : ℝ)| := neg_le_abs _
      _ = (|ball.lower| : ℚ) := by norm_cast
      _ ≤ (max |ball.lower| |ball.upper| : ℚ) := by exact_mod_cast le_max_left _ _

theorem point_contains (value : ℚ) : (point value).Contains value := by
  simp [Contains, point]

theorem round_contains {bits : ℕ} {ball : RatBall} {value : ℝ}
    (hvalue : ball.Contains value) : (ball.round bits).Contains value := by
  have hbounds := contains_iff_bounds.mp hvalue
  have hscale : (0 : ℚ) < (2 : ℚ) ^ bits := by positivity
  rw [contains_iff_bounds, round_lower, round_upper]
  constructor
  · have hlower :
        ((⌊ball.lower * (2 : ℚ) ^ bits⌋ : ℤ) : ℚ) / (2 : ℚ) ^ bits ≤
          ball.lower := by
      rw [div_le_iff₀ hscale]
      exact_mod_cast Int.floor_le (ball.lower * (2 : ℚ) ^ bits)
    have hlowerReal :
        (((⌊ball.lower * (2 : ℚ) ^ bits⌋ : ℤ) : ℚ) / (2 : ℚ) ^ bits : ℚ) ≤
          (ball.lower : ℝ) := by
      exact_mod_cast hlower
    exact hlowerReal.trans hbounds.1
  · have hupper : ball.upper ≤
        ((⌈ball.upper * (2 : ℚ) ^ bits⌉ : ℤ) : ℚ) / (2 : ℚ) ^ bits := by
      rw [le_div_iff₀ hscale]
      exact_mod_cast Int.le_ceil (ball.upper * (2 : ℚ) ^ bits)
    have hupperReal : (ball.upper : ℝ) ≤
        (((⌈ball.upper * (2 : ℚ) ^ bits⌉ : ℤ) : ℚ) / (2 : ℚ) ^ bits : ℚ) := by
      exact_mod_cast hupper
    exact hbounds.2.trans hupperReal

theorem add_contains {left right : RatBall} {x y : ℝ}
    (hx : left.Contains x) (hy : right.Contains y) :
    (add left right).Contains (x + y) := by
  dsimp [Contains, add] at hx hy ⊢
  push_cast at hx hy ⊢
  calc
    |x + y - (↑left.center + ↑right.center)| =
        |(x - left.center) + (y - right.center)| := by
      congr 1
      ring
    _ ≤ |x - left.center| + |y - right.center| := abs_add _ _
    _ ≤ left.radius + right.radius := add_le_add hx hy

theorem neg_contains {ball : RatBall} {x : ℝ} (hx : ball.Contains x) :
    ball.neg.Contains (-x) := by
  dsimp [Contains, neg] at hx ⊢
  push_cast at hx ⊢
  rw [show -x - -↑ball.center = -(x - ball.center) by ring, abs_neg]
  exact hx

theorem sub_contains {left right : RatBall} {x y : ℝ}
    (hx : left.Contains x) (hy : right.Contains y) :
    (sub left right).Contains (x - y) := by
  simpa only [sub_eq_add_neg, sub] using add_contains hx (neg_contains hy)

theorem roundedAdd_contains {bits : ℕ} {left right : RatBall} {x y : ℝ}
    (hx : left.Contains x) (hy : right.Contains y) :
    (roundedAdd bits left right).Contains (x + y) :=
  round_contains (add_contains hx hy)

theorem roundedSub_contains {bits : ℕ} {left right : RatBall} {x y : ℝ}
    (hx : left.Contains x) (hy : right.Contains y) :
    (roundedSub bits left right).Contains (x - y) :=
  round_contains (sub_contains hx hy)

theorem mul_contains {left right : RatBall} {x y : ℝ}
    (hx : left.Contains x) (hy : right.Contains y) :
    (mul left right).Contains (x * y) := by
  have hleftRadius : (0 : ℝ) ≤ left.radius := (abs_nonneg _).trans hx
  have hleftCenter : |(left.center : ℝ)| = (|left.center| : ℚ) := by norm_cast
  have hrightCenter : |(right.center : ℝ)| = (|right.center| : ℚ) := by norm_cast
  dsimp [Contains, mul] at hx hy ⊢
  calc
    |x * y - ↑(left.center * right.center)| =
        |(left.center : ℝ) * (y - right.center)
          + (right.center : ℝ) * (x - left.center)
          + (x - left.center) * (y - right.center)| := by
      congr 1
      push_cast
      ring
    _ ≤ |(left.center : ℝ) * (y - right.center)|
          + |(right.center : ℝ) * (x - left.center)|
          + |(x - left.center) * (y - right.center)| := by
      exact (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
    _ = |(left.center : ℝ)| * |y - right.center|
          + |(right.center : ℝ)| * |x - left.center|
          + |x - left.center| * |y - right.center| := by rw [abs_mul, abs_mul, abs_mul]
    _ ≤ (|left.center| : ℝ) * right.radius
          + (|right.center| : ℝ) * left.radius
          + left.radius * right.radius := by
      rw [hleftCenter, hrightCenter]
      apply add_le_add
      · exact add_le_add
          (mul_le_mul_of_nonneg_left hy (by positivity))
          (mul_le_mul_of_nonneg_left hx (by positivity))
      · exact mul_le_mul hx hy (abs_nonneg _)
          hleftRadius
    _ = ↑(|left.center| * right.radius + |right.center| * left.radius
          + left.radius * right.radius) := by norm_cast

theorem roundedMul_contains {bits : ℕ} {left right : RatBall} {x y : ℝ}
    (hx : left.Contains x) (hy : right.Contains y) :
    (roundedMul bits left right).Contains (x * y) :=
  round_contains (mul_contains hx hy)

theorem ofBounds_contains {lower upper : ℚ} {value : ℝ}
    (hlower : lower ≤ value) (hupper : value ≤ upper) :
    (ofBounds lower upper).Contains value := by
  rw [contains_iff_bounds]
  dsimp [ofBounds, RatBall.lower, RatBall.upper]
  push_cast
  constructor <;> linarith

theorem lowerHalf_radius_nonnegative {ball : RatBall} (hradius : 0 ≤ ball.radius) :
    0 ≤ ball.lowerHalf.radius := by
  dsimp [lowerHalf, ofBounds, lower]
  linarith

theorem upperHalf_radius_nonnegative {ball : RatBall} (hradius : 0 ≤ ball.radius) :
    0 ≤ ball.upperHalf.radius := by
  dsimp [upperHalf, ofBounds, upper]
  linarith

theorem lowerHalf_contains {ball : RatBall} {value : ℝ}
    (hvalue : ball.Contains value) (hupper : value ≤ ball.center) :
    ball.lowerHalf.Contains value := by
  have hbounds := contains_iff_bounds.mp hvalue
  exact ofBounds_contains hbounds.1 hupper

theorem upperHalf_contains {ball : RatBall} {value : ℝ}
    (hvalue : ball.Contains value) (hlower : ball.center ≤ value) :
    ball.upperHalf.Contains value := by
  have hbounds := contains_iff_bounds.mp hvalue
  exact ofBounds_contains hlower hbounds.2

theorem lowerHalf_contains_parent {ball : RatBall} {value : ℝ}
    (hvalue : ball.lowerHalf.Contains value) (hradius : 0 ≤ ball.radius) :
    ball.Contains value := by
  have hbounds := contains_iff_bounds.mp hvalue
  have hradiusReal : (0 : ℝ) ≤ ball.radius := by exact_mod_cast hradius
  rw [contains_iff_bounds]
  dsimp [lowerHalf, ofBounds, lower, upper] at hbounds ⊢
  push_cast at hbounds ⊢
  constructor <;> linarith

theorem upperHalf_contains_parent {ball : RatBall} {value : ℝ}
    (hvalue : ball.upperHalf.Contains value) (hradius : 0 ≤ ball.radius) :
    ball.Contains value := by
  have hbounds := contains_iff_bounds.mp hvalue
  have hradiusReal : (0 : ℝ) ≤ ball.radius := by exact_mod_cast hradius
  rw [contains_iff_bounds]
  dsimp [upperHalf, ofBounds, lower, upper] at hbounds ⊢
  push_cast at hbounds ⊢
  constructor <;> linarith

theorem lowerAt_radius_nonnegative {ball : RatBall} {cut : ℚ}
    (hlower : ball.lower ≤ cut) : 0 ≤ (ball.lowerAt cut).radius := by
  dsimp [lowerAt, ofBounds]
  linarith

theorem upperAt_radius_nonnegative {ball : RatBall} {cut : ℚ}
    (hupper : cut ≤ ball.upper) : 0 ≤ (ball.upperAt cut).radius := by
  dsimp [upperAt, ofBounds]
  linarith

theorem lowerAt_contains {ball : RatBall} {cut : ℚ} {value : ℝ}
    (hvalue : ball.Contains value) (hupper : value ≤ cut) :
    (ball.lowerAt cut).Contains value := by
  exact ofBounds_contains (contains_iff_bounds.mp hvalue).1 hupper

theorem upperAt_contains {ball : RatBall} {cut : ℚ} {value : ℝ}
    (hvalue : ball.Contains value) (hlower : cut ≤ value) :
    (ball.upperAt cut).Contains value := by
  exact ofBounds_contains hlower (contains_iff_bounds.mp hvalue).2

theorem lowerAt_contains_parent {ball : RatBall} {cut : ℚ} {value : ℝ}
    (hvalue : (ball.lowerAt cut).Contains value) (hcut : cut ≤ ball.upper) :
    ball.Contains value := by
  have hbounds := contains_iff_bounds.mp hvalue
  rw [contains_iff_bounds]
  dsimp [lowerAt, ofBounds, lower, upper] at hbounds ⊢
  push_cast at hbounds ⊢
  have hcutReal : (cut : ℝ) ≤ ball.center + ball.radius := by
    exact_mod_cast hcut
  constructor <;> linarith

theorem upperAt_contains_parent {ball : RatBall} {cut : ℚ} {value : ℝ}
    (hvalue : (ball.upperAt cut).Contains value) (hcut : ball.lower ≤ cut) :
    ball.Contains value := by
  have hbounds := contains_iff_bounds.mp hvalue
  rw [contains_iff_bounds]
  dsimp [upperAt, ofBounds, lower, upper] at hbounds ⊢
  push_cast at hbounds ⊢
  have hcutReal : ball.center - ball.radius ≤ (cut : ℝ) := by
    exact_mod_cast hcut
  constructor <;> linarith

theorem inv_contains {ball inverse : RatBall} {x : ℝ}
    (hx : ball.Contains x) (hinverse : ball.inv? = some inverse) :
    inverse.Contains x⁻¹ := by
  have hbounds := (contains_iff_bounds).mp hx
  simp only [inv?, Option.some.injEq] at hinverse
  split at hinverse <;> rename_i hlower
  · simp only [Option.some.injEq] at hinverse
    subst inverse
    have hlowerReal : (0 : ℝ) < ball.lower := by exact_mod_cast hlower
    have hxpos : 0 < x := hlowerReal.trans_le hbounds.1
    apply ofBounds_contains
    · push_cast
      simpa only [one_div] using one_div_le_one_div_of_le hxpos hbounds.2
    · push_cast
      simpa only [one_div] using one_div_le_one_div_of_le hlowerReal hbounds.1
  · contradiction

theorem roundedInv_contains {bits : ℕ} {ball inverse : RatBall} {x : ℝ}
    (hx : ball.Contains x) (hinverse : roundedInv? bits ball = some inverse) :
    inverse.Contains x⁻¹ := by
  unfold roundedInv? at hinverse
  cases hraw : ball.inv? with
  | none => simp [hraw] at hinverse
  | some raw =>
    simp [hraw] at hinverse
    subst inverse
    exact round_contains (inv_contains hx hraw)

end RatBall

/-- Rational Taylor approximation used by the executable logarithm checker. -/
def ratLogSeries (terms : ℕ) (x : ℚ) : ℚ :=
  -∑ i ∈ range terms, (1 - x) ^ (i + 1) / (i + 1)

/-- Rational remainder radius used by the executable logarithm checker. -/
def ratLogSeriesError (terms : ℕ) (x : ℚ) : ℚ :=
  |1 - x| ^ (terms + 1) / (1 - |1 - x|)

/-- Scaled rational logarithm approximation. -/
def ratScaledLogSeries (terms scale : ℕ) (x : ℚ) : ℚ :=
  ratLogSeries terms ((2 : ℚ) ^ scale * x) + scale * ratLogSeries terms (1 / 2)

/-- Scaled rational logarithm error radius. -/
def ratScaledLogSeriesError (terms scale : ℕ) (x : ℚ) : ℚ :=
  ratLogSeriesError terms ((2 : ℚ) ^ scale * x)
    + scale * ratLogSeriesError terms (1 / 2)

theorem coe_ratLogSeries (terms : ℕ) (x : ℚ) :
    (ratLogSeries terms x : ℝ) = logSeries terms x := by
  simp [ratLogSeries, logSeries]

theorem coe_ratLogSeriesError (terms : ℕ) (x : ℚ) :
    (ratLogSeriesError terms x : ℝ) = logSeriesError terms x := by
  simp [ratLogSeriesError, logSeriesError]

theorem coe_ratScaledLogSeries (terms scale : ℕ) (x : ℚ) :
    (ratScaledLogSeries terms scale x : ℝ) = scaledLogSeries terms scale x := by
  simp [ratScaledLogSeries, scaledLogSeries, coe_ratLogSeries]

theorem coe_ratScaledLogSeriesError (terms scale : ℕ) (x : ℚ) :
    (ratScaledLogSeriesError terms scale x : ℝ) =
      scaledLogSeriesError terms scale x := by
  simp [ratScaledLogSeriesError, scaledLogSeriesError, coe_ratLogSeriesError]

/-- A bounded search for a power-of-two scale placing a positive rational near one. -/
def logScale : ℕ → ℚ → ℕ
  | 0, _ => 0
  | fuel + 1, x => if x < 1 / 2 then 1 + logScale fuel (2 * x) else 0

/-- Rational counterpart of the four-term odd logarithm approximation. -/
def ratAtanhLogFour (z : ℚ) : ℚ :=
  2 * (z + z ^ 3 / 3 + z ^ 5 / 5 + z ^ 7 / 7)

/-- Rational remainder radius for `ratAtanhLogFour`. -/
def ratAtanhLogFourError (z : ℚ) : ℚ :=
  2 * |z| ^ 9 / (1 - |z|)

/-- Rational center of the fixed enclosure of `log 2`. -/
def ratLogTwoCenter : ℚ := 13862943611 / 20000000000

/-- Rational radius of the fixed enclosure of `log 2`. -/
def ratLogTwoRadius : ℚ := 1 / 4000000000

/-- Fast rational scaled-logarithm center. -/
def ratFastScaledLog (scale : ℕ) (x : ℚ) : ℚ :=
  let scaled := (2 : ℚ) ^ scale * x
  let z := (scaled - 1) / (scaled + 1)
  ratAtanhLogFour z - scale * ratLogTwoCenter

/-- Fast rational scaled-logarithm error radius. -/
def ratFastScaledLogError (scale : ℕ) (x : ℚ) : ℚ :=
  let scaled := (2 : ℚ) ^ scale * x
  let z := (scaled - 1) / (scaled + 1)
  ratAtanhLogFourError z + scale * ratLogTwoRadius

theorem coe_ratFastScaledLog (scale : ℕ) (x : ℚ) :
    (ratFastScaledLog scale x : ℝ) = fastScaledLog scale x := by
  simp [ratFastScaledLog, fastScaledLog, ratAtanhLogFour, atanhLogFour,
    ratLogTwoCenter, logTwoCenter]

theorem coe_ratFastScaledLogError (scale : ℕ) (x : ℚ) :
    (ratFastScaledLogError scale x : ℝ) = fastScaledLogError scale x := by
  simp [ratFastScaledLogError, fastScaledLogError, ratAtanhLogFourError,
    atanhLogFourError, ratLogTwoRadius, logTwoRadius]

/-- Fast point enclosure used by the certificate. The retained fuel bounds scale search. -/
def fastRationalLogBall (fuel : ℕ) (x : ℚ) : Option RatBall :=
  let scale := logScale fuel x
  let scaled := (2 : ℚ) ^ scale * x
  let z := (scaled - 1) / (scaled + 1)
  if 0 < x ∧ |z| < 1 then
    some ⟨ratFastScaledLog scale x, ratFastScaledLogError scale x⟩
  else
    none

theorem fastRationalLogBall_contains {fuel : ℕ} {x : ℚ} {ball : RatBall}
    (hball : fastRationalLogBall fuel x = some ball) :
    ball.Contains (log x) := by
  simp only [fastRationalLogBall] at hball
  split at hball <;> rename_i hvalid
  · simp only [Option.some.injEq, RatBall.mk.injEq] at hball
    rcases hball with ⟨rfl, rfl⟩
    rw [RatBall.Contains, coe_ratFastScaledLogError, coe_ratFastScaledLog]
    apply abs_log_sub_fastScaledLog_le
    · exact_mod_cast hvalid.1
    · dsimp
      exact_mod_cast hvalid.2
  · contradiction

/-- The point enclosure used for every rational logarithm endpoint. A zero requested order is
rejected, while every positive order selects the proved four-term fast enclosure. -/
def rationalLogBall (terms fuel : ℕ) (x : ℚ) : Option RatBall :=
  if terms = 0 then none else fastRationalLogBall fuel x

theorem rationalLogBall_contains {terms fuel : ℕ} {x : ℚ} {ball : RatBall}
    (hball : rationalLogBall terms fuel x = some ball) :
    ball.Contains (log x) := by
  simp only [rationalLogBall] at hball
  split at hball
  · contradiction
  · exact fastRationalLogBall_contains hball

/-- Monotonic logarithm enclosure of a positive rational ball. -/
def intervalLogBall (terms fuel : ℕ) (ball : RatBall) : Option RatBall := do
  let lowerLog ← rationalLogBall terms fuel ball.lower
  let upperLog ← rationalLogBall terms fuel ball.upper
  let lower := lowerLog.lower
  let upper := upperLog.upper
  some (RatBall.ofBounds lower upper)

theorem intervalLogBall_contains {terms fuel : ℕ} {ball logBall : RatBall} {x : ℝ}
    (hx : ball.Contains x) (hlog : intervalLogBall terms fuel ball = some logBall) :
    logBall.Contains (log x) := by
  have hbounds := (RatBall.contains_iff_bounds).mp hx
  generalize hlowerResult : rationalLogBall terms fuel ball.lower = lowerResult at hlog
  cases lowerResult with
  | none => simp [intervalLogBall, hlowerResult] at hlog
  | some lowerLog =>
    generalize hupperResult : rationalLogBall terms fuel ball.upper = upperResult at hlog
    cases upperResult with
    | none => simp [intervalLogBall, hlowerResult, hupperResult] at hlog
    | some upperLog =>
      simp [intervalLogBall, hlowerResult, hupperResult] at hlog
      subst logBall
      have hlowerContains := rationalLogBall_contains hlowerResult
      have hupperContains := rationalLogBall_contains hupperResult
      have hlowerBounds := (RatBall.contains_iff_bounds).mp hlowerContains
      have hupperBounds := (RatBall.contains_iff_bounds).mp hupperContains
      have hpositive : (0 : ℝ) < ball.lower := by
        have hpoint := hlowerResult
        simp only [rationalLogBall] at hpoint
        split at hpoint
        · contradiction
        · simp only [fastRationalLogBall] at hpoint
          split at hpoint <;> rename_i hvalid
          · exact_mod_cast hvalid.1
          · contradiction
      apply RatBall.ofBounds_contains
      · exact hlowerBounds.1.trans (Real.log_le_log hpositive hbounds.1)
      · exact (Real.log_le_log (hpositive.trans_le hbounds.1) hbounds.2).trans
          hupperBounds.2

end Frankl
