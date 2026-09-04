import MatrixMortality.ParabolicEvenBody

/-!
# The second-first-`b` cylinder

For a residual phase-zero right-`c` body beginning `ccb`, complement normalization eliminates
middle waits zero and one.  Every remaining zero lies between two exact rational root graphs.
The finite root classification leaves one endpoint on the longer prefix `ccbccb`, at waits
`(x, y, z) = (213, 465, 38)`; its required suffix density lies in an impossible grammar gap.
-/

namespace MatrixMortality.ParabolicBlade

/-- Positive denominator of the normalized phase-zero outer-root graph. -/
def parabolicOuterRootDenominator (a d z : ℚ) : ℚ :=
  a * (119911680 * z + 11209824) +
    d * (631601581536 * z + 59048086536)

/-- Numerator of the normalized phase-zero outer-root graph. -/
def parabolicOuterRootNumerator (a d y z : ℚ) : ℚ :=
  a * (25766986436 * z + 2408152393) -
    d * ((620717828832 * y + 422435605080) * z +
      58005064872 * y + 37838186340)

theorem parabolicOuterRootDenominator_pos
    (a d z : ℚ) (a_positive : 0 < a) (d_positive : 0 < d)
    (z_nonnegative : 0 ≤ z) :
    0 < parabolicOuterRootDenominator a d z := by
  unfold parabolicOuterRootDenominator
  positivity

theorem parabolicOuterRoot_increases_a
    (a₁ a₂ d y z : ℚ) (a_order : a₁ ≤ a₂)
    (a₁_positive : 0 < a₁) (d_positive : 0 < d)
    (y_nonnegative : 0 ≤ y) (z_nonnegative : 0 ≤ z) :
    parabolicOuterRootNumerator a₁ d y z / parabolicOuterRootDenominator a₁ d z ≤
      parabolicOuterRootNumerator a₂ d y z / parabolicOuterRootDenominator a₂ d z := by
  have a₂_positive : 0 < a₂ := lt_of_lt_of_le a₁_positive a_order
  have denominator₁_positive :=
    parabolicOuterRootDenominator_pos a₁ d z a₁_positive d_positive z_nonnegative
  have denominator₂_positive :=
    parabolicOuterRootDenominator_pos a₂ d z a₂_positive d_positive z_nonnegative
  rw [div_le_div_iff₀ denominator₁_positive denominator₂_positive]
  have cross_eq :
      parabolicOuterRootNumerator a₂ d y z * parabolicOuterRootDenominator a₁ d z -
          parabolicOuterRootNumerator a₁ d y z * parabolicOuterRootDenominator a₂ d z =
        (a₂ - a₁) * d *
          ((25766986436 * z + 2408152393) *
              (631601581536 * z + 59048086536) +
            (119911680 * z + 11209824) *
              ((620717828832 * y + 422435605080) * z +
                58005064872 * y + 37838186340)) := by
    unfold parabolicOuterRootNumerator parabolicOuterRootDenominator
    ring
  have cross_nonnegative :
      0 ≤ parabolicOuterRootNumerator a₂ d y z * parabolicOuterRootDenominator a₁ d z -
        parabolicOuterRootNumerator a₁ d y z * parabolicOuterRootDenominator a₂ d z := by
    rw [cross_eq]
    positivity
  linarith

theorem parabolicOuterRoot_decreases_d
    (a d₁ d₂ y z : ℚ) (d_order : d₁ ≤ d₂)
    (a_positive : 0 < a) (d₁_positive : 0 < d₁)
    (y_nonnegative : 0 ≤ y) (z_nonnegative : 0 ≤ z) :
    parabolicOuterRootNumerator a d₂ y z / parabolicOuterRootDenominator a d₂ z ≤
      parabolicOuterRootNumerator a d₁ y z / parabolicOuterRootDenominator a d₁ z := by
  have d₂_positive : 0 < d₂ := lt_of_lt_of_le d₁_positive d_order
  have denominator₁_positive :=
    parabolicOuterRootDenominator_pos a d₁ z a_positive d₁_positive z_nonnegative
  have denominator₂_positive :=
    parabolicOuterRootDenominator_pos a d₂ z a_positive d₂_positive z_nonnegative
  rw [div_le_div_iff₀ denominator₂_positive denominator₁_positive]
  have cross_eq :
      parabolicOuterRootNumerator a d₁ y z * parabolicOuterRootDenominator a d₂ z -
          parabolicOuterRootNumerator a d₂ y z * parabolicOuterRootDenominator a d₁ z =
        (d₂ - d₁) * a *
          ((25766986436 * z + 2408152393) *
              (631601581536 * z + 59048086536) +
            (119911680 * z + 11209824) *
              ((620717828832 * y + 422435605080) * z +
                58005064872 * y + 37838186340)) := by
    unfold parabolicOuterRootNumerator parabolicOuterRootDenominator
    ring
  have cross_nonnegative :
      0 ≤ parabolicOuterRootNumerator a d₁ y z * parabolicOuterRootDenominator a d₂ z -
        parabolicOuterRootNumerator a d₂ y z * parabolicOuterRootDenominator a d₁ z := by
    rw [cross_eq]
    positivity
  linarith

theorem parabolicOuterRoot_z_cross (a d y : ℚ) :
    let numeratorSlope := a * 25766986436 - d * (620717828832 * y + 422435605080)
    let numeratorConstant := a * 2408152393 - d * (58005064872 * y + 37838186340)
    let denominatorSlope := a * 119911680 + d * 631601581536
    let denominatorConstant := a * 11209824 + d * 59048086536
    numeratorSlope * denominatorConstant - numeratorConstant * denominatorSlope =
      -139828032 * (14639 * a + 88895355 * d) *
        (-38 * a + 1296 * d * y + 84099 * d) := by
  dsimp only
  ring

theorem parabolicOuterRoot_increases_z
    (a d y z₁ z₂ : ℚ) (z_order : z₁ ≤ z₂)
    (a_positive : 0 < a) (d_positive : 0 < d)
    (z₁_nonnegative : 0 ≤ z₁) (margin : d * (1296 * y + 84099) < 38 * a) :
    parabolicOuterRootNumerator a d y z₁ / parabolicOuterRootDenominator a d z₁ ≤
      parabolicOuterRootNumerator a d y z₂ / parabolicOuterRootDenominator a d z₂ := by
  have z₂_nonnegative : 0 ≤ z₂ := le_trans z₁_nonnegative z_order
  have denominator₁_positive :=
    parabolicOuterRootDenominator_pos a d z₁ a_positive d_positive z₁_nonnegative
  have denominator₂_positive :=
    parabolicOuterRootDenominator_pos a d z₂ a_positive d_positive z₂_nonnegative
  rw [div_le_div_iff₀ denominator₁_positive denominator₂_positive]
  have derivative_positive :
      0 < -139828032 * (14639 * a + 88895355 * d) *
        (-38 * a + 1296 * d * y + 84099 * d) := by
    have first_positive : 0 < 14639 * a + 88895355 * d := by positivity
    have second_negative : -38 * a + 1296 * d * y + 84099 * d < 0 := by
      nlinarith
    exact mul_pos_of_neg_of_neg
      (mul_neg_of_neg_of_pos (by norm_num) first_positive) second_negative
  have cross_eq :
      parabolicOuterRootNumerator a d y z₂ * parabolicOuterRootDenominator a d z₁ -
          parabolicOuterRootNumerator a d y z₁ * parabolicOuterRootDenominator a d z₂ =
        (z₂ - z₁) *
          (-139828032 * (14639 * a + 88895355 * d) *
            (-38 * a + 1296 * d * y + 84099 * d)) := by
    have derivative := parabolicOuterRoot_z_cross a d y
    dsimp only at derivative
    unfold parabolicOuterRootNumerator parabolicOuterRootDenominator
    calc
      _ = (z₂ - z₁) *
          ((a * 25766986436 - d * (620717828832 * y + 422435605080)) *
              (a * 11209824 + d * 59048086536) -
            (a * 2408152393 - d * (58005064872 * y + 37838186340)) *
              (a * 119911680 + d * 631601581536)) := by ring
      _ = _ := by rw [derivative]
  have cross_nonnegative :
      0 ≤ parabolicOuterRootNumerator a d y z₂ * parabolicOuterRootDenominator a d z₁ -
        parabolicOuterRootNumerator a d y z₁ * parabolicOuterRootDenominator a d z₂ := by
    rw [cross_eq]
    positivity
  linarith

/-- Positive denominator of the large-inner asymptote of the outer-root graph. -/
def parabolicOuterAsymptoteDenominator (a d : ℚ) : ℚ :=
  a * 119911680 + d * 631601581536

/-- Numerator of the large-inner asymptote of the outer-root graph. -/
def parabolicOuterAsymptoteNumerator (a d y : ℚ) : ℚ :=
  a * 25766986436 - d * (620717828832 * y + 422435605080)

theorem parabolicOuterAsymptoteDenominator_pos
    (a d : ℚ) (a_positive : 0 < a) (d_positive : 0 < d) :
    0 < parabolicOuterAsymptoteDenominator a d := by
  unfold parabolicOuterAsymptoteDenominator
  positivity

theorem parabolicOuterRoot_lt_asymptote
    (a d y z : ℚ) (a_positive : 0 < a) (d_positive : 0 < d)
    (z_nonnegative : 0 ≤ z) (margin : d * (1296 * y + 84099) < 38 * a) :
    parabolicOuterRootNumerator a d y z / parabolicOuterRootDenominator a d z <
      parabolicOuterAsymptoteNumerator a d y / parabolicOuterAsymptoteDenominator a d := by
  have root_denominator_positive :=
    parabolicOuterRootDenominator_pos a d z a_positive d_positive z_nonnegative
  have asymptote_denominator_positive :=
    parabolicOuterAsymptoteDenominator_pos a d a_positive d_positive
  rw [div_lt_div_iff₀ root_denominator_positive asymptote_denominator_positive]
  have cross_eq :
      parabolicOuterAsymptoteNumerator a d y * parabolicOuterRootDenominator a d z -
          parabolicOuterRootNumerator a d y z * parabolicOuterAsymptoteDenominator a d =
        -139828032 * (14639 * a + 88895355 * d) *
          (-38 * a + 1296 * d * y + 84099 * d) := by
    unfold parabolicOuterAsymptoteNumerator parabolicOuterAsymptoteDenominator
      parabolicOuterRootNumerator parabolicOuterRootDenominator
    ring
  have first_positive : 0 < 14639 * a + 88895355 * d := by positivity
  have second_negative : -38 * a + 1296 * d * y + 84099 * d < 0 := by
    nlinarith
  have cross_positive :
      0 < -139828032 * (14639 * a + 88895355 * d) *
        (-38 * a + 1296 * d * y + 84099 * d) :=
    mul_pos_of_neg_of_neg
      (mul_neg_of_neg_of_pos (by norm_num) first_positive) second_negative
  linarith

theorem parabolicOuterAsymptote_increases_a
    (a₁ a₂ d y : ℚ) (a_order : a₁ ≤ a₂)
    (a₁_positive : 0 < a₁) (d_positive : 0 < d) (y_nonnegative : 0 ≤ y) :
    parabolicOuterAsymptoteNumerator a₁ d y / parabolicOuterAsymptoteDenominator a₁ d ≤
      parabolicOuterAsymptoteNumerator a₂ d y / parabolicOuterAsymptoteDenominator a₂ d := by
  have a₂_positive : 0 < a₂ := lt_of_lt_of_le a₁_positive a_order
  have denominator₁_positive :=
    parabolicOuterAsymptoteDenominator_pos a₁ d a₁_positive d_positive
  have denominator₂_positive :=
    parabolicOuterAsymptoteDenominator_pos a₂ d a₂_positive d_positive
  rw [div_le_div_iff₀ denominator₁_positive denominator₂_positive]
  have cross_eq :
      parabolicOuterAsymptoteNumerator a₂ d y * parabolicOuterAsymptoteDenominator a₁ d -
          parabolicOuterAsymptoteNumerator a₁ d y * parabolicOuterAsymptoteDenominator a₂ d =
        (a₂ - a₁) * d *
          (25766986436 * 631601581536 +
            119911680 * (620717828832 * y + 422435605080)) := by
    unfold parabolicOuterAsymptoteNumerator parabolicOuterAsymptoteDenominator
    ring
  have cross_nonnegative :
      0 ≤ parabolicOuterAsymptoteNumerator a₂ d y * parabolicOuterAsymptoteDenominator a₁ d -
        parabolicOuterAsymptoteNumerator a₁ d y * parabolicOuterAsymptoteDenominator a₂ d := by
    rw [cross_eq]
    positivity
  linarith

theorem parabolicOuterAsymptote_decreases_d
    (a d₁ d₂ y : ℚ) (d_order : d₁ ≤ d₂)
    (a_positive : 0 < a) (d₁_positive : 0 < d₁) (y_nonnegative : 0 ≤ y) :
    parabolicOuterAsymptoteNumerator a d₂ y / parabolicOuterAsymptoteDenominator a d₂ ≤
      parabolicOuterAsymptoteNumerator a d₁ y / parabolicOuterAsymptoteDenominator a d₁ := by
  have d₂_positive : 0 < d₂ := lt_of_lt_of_le d₁_positive d_order
  have denominator₁_positive :=
    parabolicOuterAsymptoteDenominator_pos a d₁ a_positive d₁_positive
  have denominator₂_positive :=
    parabolicOuterAsymptoteDenominator_pos a d₂ a_positive d₂_positive
  rw [div_le_div_iff₀ denominator₂_positive denominator₁_positive]
  have cross_eq :
      parabolicOuterAsymptoteNumerator a d₁ y * parabolicOuterAsymptoteDenominator a d₂ -
          parabolicOuterAsymptoteNumerator a d₂ y * parabolicOuterAsymptoteDenominator a d₁ =
        (d₂ - d₁) * a *
          (25766986436 * 631601581536 +
            119911680 * (620717828832 * y + 422435605080)) := by
    unfold parabolicOuterAsymptoteNumerator parabolicOuterAsymptoteDenominator
    ring
  have cross_nonnegative :
      0 ≤ parabolicOuterAsymptoteNumerator a d₁ y * parabolicOuterAsymptoteDenominator a d₂ -
        parabolicOuterAsymptoteNumerator a d₂ y * parabolicOuterAsymptoteDenominator a d₁ := by
    rw [cross_eq]
    positivity
  linarith

theorem parabolicOuterRoot_eq
    (a d y z : ℚ) (x : Nat) (a_positive : 0 < a) (d_positive : 0 < d)
    (z_nonnegative : 0 ≤ z)
    (root_eq : parabolicOuterRootDenominator a d z * x = parabolicOuterRootNumerator a d y z) :
    parabolicOuterRootNumerator a d y z / parabolicOuterRootDenominator a d z = x := by
  have denominator_positive :=
    parabolicOuterRootDenominator_pos a d z a_positive d_positive z_nonnegative
  rw [div_eq_iff denominator_positive.ne']
  nlinarith

/-- The normalized second-first-`b` root lies between two rational graphs once the middle
wait is at least two and the scale and complement occupy their physical envelope. -/
theorem firstBTwo_root_between_envelopes
    (a d : ℚ) (x y z : Nat) (two_le_y : 2 ≤ y)
    (a_lower :
      2187 * (72 * y - 9) + (9 - 8 * y) / 243 ≤ a)
    (a_upper : a ≤ 2187 * (72 * y - 9))
    (d_lower : 39 ≤ d) (d_upper : d ≤ 9477 / 242)
    (root_eq : parabolicOuterRootDenominator a d z * x = parabolicOuterRootNumerator a d y z) :
    (5541372938576372618 * (y : ℚ) - 718629336347817375) /
          (25950255067173888 * y + 30751845545334654) ≤ (x : ℚ) ∧
      (x : ℚ) < (112032354356496 * y - 14545738406053) /
          (524493688320 * y + 618673335624) := by
  let a₀ : ℚ := 2187 * (72 * y - 9) + (9 - 8 * y) / 243
  let a₁ : ℚ := 2187 * (72 * y - 9)
  let d₀ : ℚ := 39
  let d₁ : ℚ := 9477 / 242
  have y_nonnegative : (0 : ℚ) ≤ y := by positivity
  have y_large : (2 : ℚ) ≤ y := by exact_mod_cast two_le_y
  have a₀_positive : 0 < a₀ := by
    dsimp [a₀]
    linarith
  have a_positive : 0 < a := lt_of_lt_of_le a₀_positive a_lower
  have a₁_positive : 0 < a₁ := by
    dsimp [a₁]
    nlinarith
  have d₀_positive : 0 < d₀ := by norm_num [d₀]
  have d_positive : 0 < d := lt_of_lt_of_le d₀_positive d_lower
  have d₁_positive : 0 < d₁ := by norm_num [d₁]
  have worst_margin : d₁ * (1296 * (y : ℚ) + 84099) < 38 * a₀ := by
    dsimp [a₀, d₁]
    norm_num
    linarith
  have factor_nonnegative : (0 : ℚ) ≤ 1296 * y + 84099 := by positivity
  have scaled_d : d * (1296 * (y : ℚ) + 84099) ≤
      d₁ * (1296 * y + 84099) :=
    mul_le_mul_of_nonneg_right d_upper factor_nonnegative
  have margin : d * (1296 * (y : ℚ) + 84099) < 38 * a := by
    nlinarith
  have z_nonnegative : (0 : ℚ) ≤ z := by positivity
  have root_value :
      parabolicOuterRootNumerator a d y z / parabolicOuterRootDenominator a d z = x :=
    parabolicOuterRoot_eq a d y z x a_positive d_positive z_nonnegative root_eq
  have lower_value :
      (5541372938576372618 * (y : ℚ) - 718629336347817375) /
          (25950255067173888 * y + 30751845545334654) =
        parabolicOuterRootNumerator a₀ d₁ y 0 / parabolicOuterRootDenominator a₀ d₁ 0 := by
    have left_denominator_positive :
        (0 : ℚ) < 25950255067173888 * y + 30751845545334654 := by positivity
    have right_denominator_positive :=
      parabolicOuterRootDenominator_pos a₀ d₁ 0 a₀_positive d₁_positive (by norm_num)
    field_simp [left_denominator_positive.ne', right_denominator_positive.ne']
    dsimp [a₀, d₁]
    norm_num [parabolicOuterRootNumerator, parabolicOuterRootDenominator]
    ring
  have upper_value :
      parabolicOuterAsymptoteNumerator a₁ d₀ y /
          parabolicOuterAsymptoteDenominator a₁ d₀ =
        (112032354356496 * (y : ℚ) - 14545738406053) /
          (524493688320 * y + 618673335624) := by
    have left_denominator_positive :=
      parabolicOuterAsymptoteDenominator_pos a₁ d₀ a₁_positive d₀_positive
    have right_denominator_positive :
        (0 : ℚ) < 524493688320 * y + 618673335624 := by positivity
    field_simp [left_denominator_positive.ne', right_denominator_positive.ne']
    dsimp [a₁, d₀]
    norm_num [parabolicOuterAsymptoteNumerator, parabolicOuterAsymptoteDenominator]
    ring
  constructor
  · rw [lower_value]
    calc
      _ ≤ parabolicOuterRootNumerator a₀ d y 0 /
          parabolicOuterRootDenominator a₀ d 0 :=
        parabolicOuterRoot_decreases_d a₀ d d₁ y 0 d_upper a₀_positive d_positive
          y_nonnegative (by norm_num)
      _ ≤ parabolicOuterRootNumerator a d y 0 / parabolicOuterRootDenominator a d 0 :=
        parabolicOuterRoot_increases_a a₀ a d y 0 a_lower a₀_positive d_positive
          y_nonnegative (by norm_num)
      _ ≤ parabolicOuterRootNumerator a d y z / parabolicOuterRootDenominator a d z :=
        parabolicOuterRoot_increases_z a d y 0 z (by positivity) a_positive d_positive
          (by norm_num) margin
      _ = x := root_value
  · rw [← upper_value, ← root_value]
    calc
      _ < parabolicOuterAsymptoteNumerator a d y / parabolicOuterAsymptoteDenominator a d :=
        parabolicOuterRoot_lt_asymptote a d y z a_positive d_positive z_nonnegative margin
      _ ≤ parabolicOuterAsymptoteNumerator a₁ d y / parabolicOuterAsymptoteDenominator a₁ d :=
        parabolicOuterAsymptote_increases_a a a₁ d y a_upper a_positive d_positive y_nonnegative
      _ ≤ parabolicOuterAsymptoteNumerator a₁ d₀ y /
          parabolicOuterAsymptoteDenominator a₁ d₀ :=
        parabolicOuterAsymptote_decreases_d a₁ d₀ d y d_lower a₁_positive d₀_positive
          y_nonnegative

/-- No integral normalized root exists at middle wait one inside the physical scale and
complement envelope of a second-first-`b` body. -/
theorem firstBTwo_no_root_at_y_one
    (a d : ℚ) (x z : Nat)
    (a_lower : 137781 ≤ a) (a_upper : a ≤ 137781 + 1 / 243)
    (d_lower : 39 ≤ d) (d_upper : d ≤ 9477 / 242)
    (root_eq : parabolicOuterRootDenominator a d z * x = parabolicOuterRootNumerator a d 1 z) :
    False := by
  let a₀ : ℚ := 137781
  let a₁ : ℚ := 137781 + 1 / 243
  let d₀ : ℚ := 39
  let d₁ : ℚ := 9477 / 242
  have a₀_positive : 0 < a₀ := by norm_num [a₀]
  have a_positive : 0 < a := lt_of_lt_of_le a₀_positive a_lower
  have a₁_positive : 0 < a₁ := by norm_num [a₁]
  have d₀_positive : 0 < d₀ := by norm_num [d₀]
  have d_positive : 0 < d := lt_of_lt_of_le d₀_positive d_lower
  have d₁_positive : 0 < d₁ := by norm_num [d₁]
  have worst_margin : d₁ * (1296 + 84099) < 38 * a₀ := by norm_num [a₀, d₁]
  have margin : d * (1296 + 84099) < 38 * a := by
    have scaled_d : d * (1296 + 84099) ≤ d₁ * (1296 + 84099) := by
      exact mul_le_mul_of_nonneg_right d_upper (by norm_num)
    nlinarith
  have normalized_margin : d * (1296 * (1 : ℚ) + 84099) < 38 * a := by
    norm_num at margin ⊢
    exact margin
  have z_nonnegative : (0 : ℚ) ≤ z := by positivity
  have root_value :
      parabolicOuterRootNumerator a d 1 z / parabolicOuterRootDenominator a d z = x :=
    parabolicOuterRoot_eq a d 1 z x a_positive d_positive z_nonnegative root_eq
  have lower_value :
      (18149685314213 / 213390009180 : ℚ) =
        parabolicOuterRootNumerator a₀ d₁ 1 0 / parabolicOuterRootDenominator a₀ d₁ 0 := by
    norm_num [a₀, d₁, parabolicOuterRootNumerator, parabolicOuterRootDenominator]
  have upper_value :
      parabolicOuterAsymptoteNumerator a₁ d₀ 1 /
          parabolicOuterAsymptoteDenominator a₁ d₀ =
        (106601617762682725 / 1250053155671724 : ℚ) := by
    norm_num [a₁, d₀, parabolicOuterAsymptoteNumerator, parabolicOuterAsymptoteDenominator]
  have lower_bound : (18149685314213 / 213390009180 : ℚ) ≤ x := by
    rw [lower_value]
    calc
      _ ≤ parabolicOuterRootNumerator a₀ d 1 0 / parabolicOuterRootDenominator a₀ d 0 :=
        parabolicOuterRoot_decreases_d a₀ d d₁ 1 0 d_upper a₀_positive d_positive
          (by norm_num) (by norm_num)
      _ ≤ parabolicOuterRootNumerator a d 1 0 / parabolicOuterRootDenominator a d 0 :=
        parabolicOuterRoot_increases_a a₀ a d 1 0 a_lower a₀_positive d_positive
          (by norm_num) (by norm_num)
      _ ≤ parabolicOuterRootNumerator a d 1 z / parabolicOuterRootDenominator a d z :=
        parabolicOuterRoot_increases_z a d 1 0 z (by positivity) a_positive d_positive
          (by norm_num) normalized_margin
      _ = x := root_value
  have upper_bound : (x : ℚ) < 106601617762682725 / 1250053155671724 := by
    rw [← upper_value, ← root_value]
    calc
      _ < parabolicOuterAsymptoteNumerator a d 1 / parabolicOuterAsymptoteDenominator a d :=
        parabolicOuterRoot_lt_asymptote a d 1 z a_positive d_positive z_nonnegative
          normalized_margin
      _ ≤ parabolicOuterAsymptoteNumerator a₁ d 1 / parabolicOuterAsymptoteDenominator a₁ d :=
        parabolicOuterAsymptote_increases_a a a₁ d 1 a_upper a_positive d_positive
          (by norm_num)
      _ ≤ parabolicOuterAsymptoteNumerator a₁ d₀ 1 /
          parabolicOuterAsymptoteDenominator a₁ d₀ :=
        parabolicOuterAsymptote_decreases_d a₁ d₀ d 1 d_lower a₁_positive d₀_positive
          (by norm_num)
  have eighty_five_lt : (85 : ℚ) < x := lt_of_lt_of_le (by norm_num) lower_bound
  have lt_eighty_six : (x : ℚ) < 86 := lt_of_lt_of_le upper_bound (by norm_num)
  have eighty_five_lt_nat : 85 < x := by exact_mod_cast eighty_five_lt
  have lt_eighty_six_nat : x < 86 := by exact_mod_cast lt_eighty_six
  omega

private theorem ccb_scale (tail : List TagLetter) :
    3 ^ (tagEncode 3 ([.c, .c, .b] ++ tail)).length =
      2187 * 3 ^ (tagEncode 3 tail).length := by
  rw [tagEncode_append, List.length_append, pow_add]
  norm_num [tagEncode, spell, tagCode]

private theorem ccb_complement (tail : List TagLetter) :
    tagComplementCode ([.c, .c, .b] ++ tail) =
      39 * 3 ^ (tagEncode 3 tail).length + tagComplementCode tail := by
  rw [tagComplementCode_append]
  have stem_complement : tagComplementCode [.c, .c, .b] = 39 := by decide
  rw [stem_complement]

theorem tagEncode_length_five_le_of_mem_b
    (body : List TagLetter) (contains_b : .b ∈ body) :
    5 ≤ (tagEncode 3 body).length := by
  induction body with
  | nil => simp at contains_b
  | cons head tail induction =>
      cases head with
      | b =>
          rw [tagEncode_cons, List.length_append, tagCode_b_length]
          omega
      | c =>
          have tail_contains_b : TagLetter.b ∈ tail := by simpa using contains_b
          have tail_length := induction tail_contains_b
          simp only [tagEncode_cons, tagCode, List.length_append,
            List.length_cons, List.length_nil]
          omega

private theorem firstBTwo_normalized_root_of_core_zero
    (T E x y z : Nat) (scale_positive : 0 < T)
    (core_zero :
      bZeroBDefectCOneCodeCore (2187 * (T : ℚ))
        (2187 * T - 1 - (39 * T + E)) x y z = 0) :
    let a : ℚ := 2187 * (72 * y - 9) + (9 - 8 * y) / T
    let d : ℚ := 39 + E / T
    parabolicOuterRootDenominator a d z * x = parabolicOuterRootNumerator a d y z := by
  have scale_nonzero : (T : ℚ) ≠ 0 := by exact_mod_cast scale_positive.ne'
  rw [bZeroBDefectCOneCodeCore_thin_decomposition] at core_zero
  unfold bZeroBDefectCOneWaitFactor bZeroBDefectCOneRootPencil
    bZeroBDefectCOneComplementCore at core_zero
  dsimp only
  unfold parabolicOuterRootDenominator parabolicOuterRootNumerator
  field_simp [scale_nonzero]
  linear_combination core_zero

private theorem firstBTwo_physical_parameters
    (tail : List TagLetter) (contains_b : .b ∈ tail) (y : Nat) :
    let T : Nat := 3 ^ (tagEncode 3 tail).length
    let E : Nat := tagComplementCode tail
    let a : ℚ := 2187 * (72 * y - 9) + (9 - 8 * y) / T
    let d : ℚ := 39 + E / T
    243 ≤ T ∧ 39 ≤ d ∧ d ≤ 9477 / 242 ∧
      (2 ≤ y →
        2187 * (72 * y - 9) + (9 - 8 * y) / 243 ≤ a ∧
          a ≤ 2187 * (72 * y - 9)) ∧
      (y = 1 → 137781 ≤ a ∧ a ≤ 137781 + 1 / 243) := by
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E : Nat := tagComplementCode tail
  let a : ℚ := 2187 * (72 * y - 9) + (9 - 8 * y) / T
  let d : ℚ := 39 + E / T
  have encoded_length : 5 ≤ (tagEncode 3 tail).length :=
    tagEncode_length_five_le_of_mem_b tail contains_b
  have scale_bound : 243 ≤ T := by
    dsimp [T]
    calc
      243 = 3 ^ 5 := by norm_num
      _ ≤ 3 ^ (tagEncode 3 tail).length := Nat.pow_le_pow_right (by norm_num) encoded_length
  have scale_positive_nat : 0 < T := lt_of_lt_of_le (by norm_num) scale_bound
  have scale_positive : (0 : ℚ) < T := by exact_mod_cast scale_positive_nat
  have complement_bound_nat : 242 * E ≤ 39 * T := by
    have sharp := tagComplementCode_global_bound tail
    dsimp [T, E] at sharp ⊢
    have scale_one : 1 ≤ 3 ^ (tagEncode 3 tail).length := one_le_pow₀ (by norm_num)
    omega
  have complement_bound : (E : ℚ) / T ≤ 39 / 242 := by
    rw [div_le_div_iff₀ scale_positive (by norm_num)]
    have complement_bound_rat : (242 : ℚ) * E ≤ 39 * T := by
      exact_mod_cast complement_bound_nat
    simpa only [mul_comm] using complement_bound_rat
  have d_lower : (39 : ℚ) ≤ d := by
    dsimp [d]
    have quotient_nonnegative : (0 : ℚ) ≤ (E : ℚ) / T := by positivity
    linarith
  have d_upper : d ≤ (9477 / 242 : ℚ) := by
    dsimp [d]
    norm_num
    linarith
  refine ⟨scale_bound, d_lower, d_upper, ?_, ?_⟩
  · intro two_le_y
    have y_large : (2 : ℚ) ≤ y := by exact_mod_cast two_le_y
    have numerator_nonpositive : (9 : ℚ) - 8 * y ≤ 0 := by linarith
    have scale_bound_rat : (243 : ℚ) ≤ T := by exact_mod_cast scale_bound
    have scaled_numerator :
        ((9 : ℚ) - 8 * y) * T ≤ ((9 : ℚ) - 8 * y) * 243 :=
      mul_le_mul_of_nonpos_left scale_bound_rat numerator_nonpositive
    have fraction_lower : ((9 : ℚ) - 8 * y) / 243 ≤ (9 - 8 * y) / T := by
      rw [div_le_div_iff₀ (by norm_num) scale_positive]
      simpa only [mul_comm] using scaled_numerator
    constructor
    · linarith
    · have fraction_nonpositive : ((9 : ℚ) - 8 * y) / T ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg numerator_nonpositive scale_positive.le
      linarith
  · intro y_one
    subst y
    have reciprocal_bound : (1 : ℚ) / T ≤ 1 / 243 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast scale_bound)
    have reciprocal_bound_expanded :
        (1 : ℚ) / (3 ^ (tagEncode 3 tail).length : Nat) ≤ 1 / 243 := by
      simpa only [T] using reciprocal_bound
    constructor
    · norm_num
    · norm_num at reciprocal_bound_expanded ⊢
      linarith

private theorem firstBTwo_core_zero_in_complement_coordinates
    (tail : List TagLetter) (x y z : Nat)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^ (tagEncode 3 ([.c, .c, .b] ++ tail)).length)
        (ternaryCode (tagEncode 3 ([.c, .c, .b] ++ tail))) x y z = 0) :
    let T : Nat := 3 ^ (tagEncode 3 tail).length
    let E : Nat := tagComplementCode tail
    bZeroBDefectCOneCodeCore (2187 * (T : ℚ))
      (2187 * T - 1 - (39 * T + E)) x y z = 0 := by
  let body := [.c, .c, .b] ++ tail
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E : Nat := tagComplementCode tail
  let S : Nat := 3 ^ (tagEncode 3 body).length
  let C : Nat := ternaryCode (tagEncode 3 body)
  let D : Nat := tagComplementCode body
  have scale_eq : S = 2187 * T := by
    dsimp [S, T, body]
    exact ccb_scale tail
  have complement_eq : D = 39 * T + E := by
    dsimp [D, T, E, body]
    exact ccb_complement tail
  have code_lt : C < S := by
    dsimp [C, S, body]
    exact ternaryCode_lt_pow_length (tagEncode 3 ([.c, .c, .b] ++ tail))
  have complement_nat : D = S - C - 1 := rfl
  have coordinate_sum : C + D + 1 = S := by omega
  have code_eq : (C : ℚ) = (S : ℚ) - 1 - D := by
    have coordinate_sum_rat : (C : ℚ) + D + 1 = S := by exact_mod_cast coordinate_sum
    linarith
  have scale_cast :
      (S : ℚ) = (3 : ℚ) ^ (tagEncode 3 ([.c, .c, .b] ++ tail)).length := by
    dsimp [S, body]
    norm_num
  rw [← scale_cast] at core_zero
  change bZeroBDefectCOneCodeCore (S : ℚ) (C : ℚ) x y z = 0 at core_zero
  rw [code_eq, scale_eq, complement_eq] at core_zero
  dsimp only
  push_cast at core_zero
  exact core_zero

/-- A zero on a body whose first `b` follows two leading `c` letters and whose suffix
contains `b` lies between the exact rational root envelopes. -/
theorem firstBTwo_root_between_envelopes_of_tail
    (tail : List TagLetter) (contains_b : .b ∈ tail) (x y z : Nat) (two_le_y : 2 ≤ y)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^ (tagEncode 3 ([.c, .c, .b] ++ tail)).length)
        (ternaryCode (tagEncode 3 ([.c, .c, .b] ++ tail))) x y z = 0) :
    (5541372938576372618 * y - 718629336347817375) /
          (25950255067173888 * y + 30751845545334654) ≤ (x : ℚ) ∧
      (x : ℚ) < (112032354356496 * y - 14545738406053) /
          (524493688320 * y + 618673335624) := by
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E : Nat := tagComplementCode tail
  let a : ℚ := 2187 * (72 * y - 9) + (9 - 8 * y) / T
  let d : ℚ := 39 + E / T
  have parameters := firstBTwo_physical_parameters tail contains_b y
  dsimp only at parameters
  have scale_positive : 0 < T := lt_of_lt_of_le (by norm_num) parameters.1
  have complement_core_zero :=
    firstBTwo_core_zero_in_complement_coordinates tail x y z core_zero
  dsimp only at complement_core_zero
  have root_eq : parabolicOuterRootDenominator a d z * x = parabolicOuterRootNumerator a d y z := by
    simpa only [a, d] using
      firstBTwo_normalized_root_of_core_zero T E x y z scale_positive complement_core_zero
  exact firstBTwo_root_between_envelopes a d x y z two_le_y
    (parameters.2.2.2.1 two_le_y).1 (parameters.2.2.2.1 two_le_y).2
    parameters.2.1 parameters.2.2.1 root_eq

/-- A zero on a body beginning `ccb` gives the normalized inner-wait equation used by the
finite tail-cylinder certificate. -/
theorem firstBTwo_z_equation_of_tail_zero
    (tail : List TagLetter) (x y z : Nat)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^ (tagEncode 3 ([.c, .c, .b] ++ tail)).length)
        (ternaryCode (tagEncode 3 ([.c, .c, .b] ++ tail))) x y z = 0) :
    let T : Nat := 3 ^ (tagEncode 3 tail).length
    let E : Nat := tagComplementCode tail
    let a : ℚ := 2187 * (72 * y - 9) + (9 - 8 * y) / T
    let d : ℚ := 39 + E / T
    (a * (25766986436 - 119911680 * x) -
        d * (620717828832 * y + 631601581536 * x + 422435605080)) * z =
      d * (58005064872 * y + 59048086536 * x + 37838186340) -
        a * (2408152393 - 11209824 * x) := by
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E : Nat := tagComplementCode tail
  let a : ℚ := 2187 * (72 * y - 9) + (9 - 8 * y) / T
  let d : ℚ := 39 + E / T
  have scale_positive : 0 < T := by
    dsimp [T]
    positivity
  have complement_core_zero :=
    firstBTwo_core_zero_in_complement_coordinates tail x y z core_zero
  dsimp only at complement_core_zero
  have root_eq : parabolicOuterRootDenominator a d z * x = parabolicOuterRootNumerator a d y z := by
    simpa only [a, d] using
      firstBTwo_normalized_root_of_core_zero T E x y z scale_positive complement_core_zero
  dsimp only
  unfold parabolicOuterRootDenominator parabolicOuterRootNumerator at root_eq
  linear_combination -root_eq

/-- Middle wait one cannot close a second-first-`b` body whose suffix contains `b`. -/
theorem bZeroBDefectCOneCodeCore_ccb_ne_zero_of_y_one
    (tail : List TagLetter) (contains_b : .b ∈ tail) (x z : Nat) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^ (tagEncode 3 ([.c, .c, .b] ++ tail)).length)
      (ternaryCode (tagEncode 3 ([.c, .c, .b] ++ tail))) x 1 z ≠ 0 := by
  intro core_zero
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E : Nat := tagComplementCode tail
  let a : ℚ := 2187 * (72 * (1 : ℚ) - 9) + (9 - 8 * (1 : ℚ)) / T
  let d : ℚ := 39 + E / T
  have parameters := firstBTwo_physical_parameters tail contains_b 1
  dsimp only at parameters
  have scale_positive : 0 < T := lt_of_lt_of_le (by norm_num) parameters.1
  have complement_core_zero :=
    firstBTwo_core_zero_in_complement_coordinates tail x 1 z core_zero
  dsimp only at complement_core_zero
  have root_eq : parabolicOuterRootDenominator a d z * x = parabolicOuterRootNumerator a d 1 z := by
    simpa only [a, d, Nat.cast_one] using
      firstBTwo_normalized_root_of_core_zero T E x 1 z scale_positive complement_core_zero
  have a_bounds := parameters.2.2.2.2 rfl
  exact firstBTwo_no_root_at_y_one a d x z a_bounds.1 a_bounds.2
    parameters.2.1 parameters.2.2.1 root_eq

/-- Middle wait zero cannot close a second-first-`b` body. -/
theorem bZeroBDefectCOneCodeCore_ccb_ne_zero_of_y_zero
    (tail : List TagLetter) (x z : Nat) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^ (tagEncode 3 ([.c, .c, .b] ++ tail)).length)
      (ternaryCode (tagEncode 3 ([.c, .c, .b] ++ tail))) x 0 z ≠ 0 := by
  intro core_zero
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E : Nat := tagComplementCode tail
  let S : Nat := 3 ^ (tagEncode 3 ([.c, .c, .b] ++ tail)).length
  let D : Nat := tagComplementCode ([.c, .c, .b] ++ tail)
  have scale_eq : S = 2187 * T := by
    dsimp [S, T]
    exact ccb_scale tail
  have complement_eq : D = 39 * T + E := by
    dsimp [D, T, E]
    exact ccb_complement tail
  have scale_positive : 1 ≤ T := by
    dsimp [T]
    exact one_le_pow₀ (by norm_num)
  have scale_large_nat : 1 < S := by omega
  have complement_positive_nat : 0 < D := by omega
  have complement_large_nat : S - 1 ≤ 585 * D := by omega
  have scale_large : (1 : ℚ) < S := by exact_mod_cast scale_large_nat
  have complement_positive : (0 : ℚ) < D := by exact_mod_cast complement_positive_nat
  have complement_large_cast : ((S - 1 : Nat) : ℚ) ≤ 585 * D := by
    exact_mod_cast complement_large_nat
  have complement_large : (S : ℚ) - 1 ≤ 585 * D := by
    rw [Nat.cast_sub scale_large_nat.le] at complement_large_cast
    norm_num at complement_large_cast ⊢
    exact complement_large_cast
  have complement_core_zero :=
    firstBTwo_core_zero_in_complement_coordinates tail x 0 z core_zero
  dsimp only at complement_core_zero
  have core_positive := bZeroBDefectCOneCodeCore_pos_of_zero_wait_large_complement
    (S : ℚ) D scale_large complement_positive complement_large x z
  rw [scale_eq, complement_eq] at core_positive
  push_cast at core_positive
  dsimp only [T, E] at core_positive
  exact ne_of_gt core_positive complement_core_zero

/-- Every physical tag word lies on one side of the open density gap between a first `b` in
its first two positions and a first `b` after them. -/
private theorem tagComplementCode_second_position_density_gap (body : List TagLetter) :
    13 * 3 ^ (tagEncode 3 body).length ≤ 243 * tagComplementCode body ∨
      2178 * tagComplementCode body < 39 * 3 ^ (tagEncode 3 body).length := by
  rcases tagComplementCode_first_b_position_gap 1 body with high | low
  · left
    calc
      13 * 3 ^ (tagEncode 3 body).length ≤
          81 * 3 ^ 1 * tagComplementCode body := high
      _ = 243 * tagComplementCode body := by ring
  · right
    calc
      2178 * tagComplementCode body =
          242 * 3 ^ (1 + 1) * tagComplementCode body := by ring
      _ < 39 * 3 ^ (tagEncode 3 body).length := low

private theorem ccbccb_scale (rest : List TagLetter) :
    3 ^ (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)).length =
      4782969 * 3 ^ (tagEncode 3 rest).length := by
  rw [tagEncode_append, List.length_append, pow_add]
  norm_num [tagEncode, spell, tagCode]

private theorem ccbccb_complement (rest : List TagLetter) :
    tagComplementCode ([.c, .c, .b, .c, .c, .b] ++ rest) =
      85332 * 3 ^ (tagEncode 3 rest).length + tagComplementCode rest := by
  rw [tagComplementCode_append]
  have stem_complement :
      tagComplementCode [.c, .c, .b, .c, .c, .b] = 85332 := by decide
  rw [stem_complement]

/-- The lone integral endpoint of the second-first-`b` cylinder cannot close the primitive
core, independently of the remaining physical suffix. -/
theorem bZeroBDefectCOneCodeCore_ccbccb_ne_zero (rest : List TagLetter) :
    bZeroBDefectCOneCodeCore
        ((3 : ℤ) ^ (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)).length)
        (ternaryCode (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)))
        213 465 38 ≠ 0 := by
  let R : Nat := 3 ^ (tagEncode 3 rest).length
  let G : Nat := tagComplementCode rest
  let S : Nat := 3 ^ (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)).length
  let C : Nat := ternaryCode (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest))
  let D : Nat := tagComplementCode ([.c, .c, .b, .c, .c, .b] ++ rest)
  have scale_positive : 1 ≤ R := by
    dsimp [R]
    exact one_le_pow₀ (by norm_num)
  have scale_eq : S = 4782969 * R := by
    dsimp [S, R]
    exact ccbccb_scale rest
  have complement_eq : D = 85332 * R + G := by
    dsimp [D, R, G]
    exact ccbccb_complement rest
  have code_lt : C < S := by
    dsimp [C, S]
    exact ternaryCode_lt_pow_length
      (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest))
  have complement_nat : D = S - C - 1 := by
    rfl
  have coordinate_sum : C + D + 1 = S := by omega
  have code_eq : (C : ℤ) = (S : ℤ) - 1 - D := by
    have coordinate_sum_int : (C : ℤ) + D + 1 = S := by
      exact_mod_cast coordinate_sum
    omega
  intro core_zero
  have affine_zero :
      (-378928275417207 : ℤ) * R + 16135907225190852 * G +
          31917593029119 = 0 := by
    change bZeroBDefectCOneCodeCore (S : ℤ) (C : ℤ) 213 465 38 = 0 at core_zero
    rw [code_eq, bZeroBDefectCOneCodeCore_thin_decomposition] at core_zero
    unfold bZeroBDefectCOneWaitFactor bZeroBDefectCOneRootPencil
      bZeroBDefectCOneComplementCore at core_zero
    rw [scale_eq, complement_eq] at core_zero
    push_cast at core_zero
    norm_num at core_zero ⊢
    linear_combination core_zero
  have forced_lower : (39 : ℤ) * R < 2178 * G := by
    have R_positive : (0 : ℤ) < R := by exact_mod_cast scale_positive
    linarith [affine_zero]
  have forced_upper : (243 : ℤ) * G < 13 * R := by
    have R_positive : (0 : ℤ) < R := by exact_mod_cast scale_positive
    linarith [affine_zero]
  rcases tagComplementCode_second_position_density_gap rest with high | low
  · have high_int : (13 : ℤ) * R ≤ 243 * G := by
      exact_mod_cast high
    linarith
  · have low_int : (2178 : ℤ) * G < 39 * R := by
      exact_mod_cast low
    linarith

/-- The exceptional second-first-`b` endpoint is nonzero over the rational core used by the
determinant reduction. -/
theorem bZeroBDefectCOneCodeCore_ccbccb_ne_zero_rat (rest : List TagLetter) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^ (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)).length)
      (ternaryCode (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)))
      213 465 38 ≠ 0 := by
  intro rational_core_zero
  have power_cast :
      (((3 : Nat) ^ (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)).length : Nat) : ℚ) =
        (3 : ℚ) ^ (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)).length := by
    norm_num
  rw [← power_cast] at rational_core_zero
  have cast_integer_core :
      ((bZeroBDefectCOneCodeCore
        ((3 : ℤ) ^ (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)).length)
        (ternaryCode (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)))
        213 465 38 : ℤ) : ℚ) =
        bZeroBDefectCOneCodeCore
          (((3 : Nat) ^
            (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)).length : Nat) : ℚ)
          (ternaryCode (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)))
          213 465 38 := by
    norm_num [bZeroBDefectCOneCodeCore]
  have cast_zero :
      ((bZeroBDefectCOneCodeCore
        ((3 : ℤ) ^ (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)).length)
        (ternaryCode (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)))
        213 465 38 : ℤ) : ℚ) = 0 := by
    rw [cast_integer_core]
    exact rational_core_zero
  have integer_core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℤ) ^ (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)).length)
        (ternaryCode (tagEncode 3 ([.c, .c, .b, .c, .c, .b] ++ rest)))
        213 465 38 = 0 := by
    exact_mod_cast cast_zero
  exact bZeroBDefectCOneCodeCore_ccbccb_ne_zero rest integer_core_zero

/-- The exceptional waits do not close the `b | b | c` bridge on any body with prefix
`ccbccb`. -/
theorem bridge_bZero_bTwo_cOne_det_ne_zero_of_ccbccb
    (rest : List TagLetter) :
    (bridge 27
      (bAtom 27 (3 * 38) * bAtom 27 (3 * 213 + 2) *
        cAtom 27 (nearySideLowerC 3 ([.c, .c, .b, .c, .c, .b] ++ rest))
          (nearySideLowerCScale 3 ([.c, .c, .b, .c, .c, .b] ++ rest))
          (3 * 465 + 1))).det ≠ 0 := by
  rw [bridge_bZero_bTwo_cOne_det]
  exact mul_ne_zero (by norm_num) (bZeroBDefectCOneCodeCore_ccbccb_ne_zero_rat rest)

end MatrixMortality.ParabolicBlade
