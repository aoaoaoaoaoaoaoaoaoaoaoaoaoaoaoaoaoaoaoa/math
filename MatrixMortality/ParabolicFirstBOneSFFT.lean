import MatrixMortality.ParabolicEvenBody

/-!
# SFFT coordinates for the first-`b`-after-one-`c` chamber

At the unresolved outer wait `x = 211`, the phase-zero right-`c` core admits a positive
divisor equation.  This file records that algebraic reduction and proves positivity on every
physical body beginning `cb`.  It makes no claim that the resulting divisor equation has no
solutions.
-/

namespace MatrixMortality.ParabolicBlade

/-- Negative `y*z` coefficient, after removing its content `32`, at outer wait `211`. -/
def bZeroBDefectCOneSfftN {R : Type*} [CommRing R] (S D : R) : R :=
  1047649401 * S - 19397432151 * D - 116405489

/-- `y` coefficient, after removing its content `8`, at outer wait `211`. -/
def bZeroBDefectCOneSfftM {R : Type*} [CommRing R] (S D : R) : R :=
  7250633109 * D - 385915761 * S + 42879529

/-- `z` coefficient, after removing its content `12`, at outer wait `211`. -/
def bZeroBDefectCOneSfftC {R : Type*} [CommRing R] (S D : R) : R :=
  11140864109098 * D + 349216467 * (S - 1)

/-- Constant coefficient, after removing its content `3`, at outer wait `211`. -/
def bZeroBDefectCOneSfftK {R : Type*} [CommRing R] (S D : R) : R :=
  4165661481812 * D + 128638587 * (S - 1)

/-- Positive final resultant factor at outer wait `211`. -/
def bZeroBDefectCOneSfftW {R : Type*} [CommRing R] (S D : R) : R :=
  2860660950 * S - 1096376045 * D - 319295598

/-- First affine divisor coordinate at outer wait `211`. -/
def bZeroBDefectCOneSfftU {R : Type*} [CommRing R] (S D y : R) : R :=
  8 * bZeroBDefectCOneSfftN S D * y - 3 * bZeroBDefectCOneSfftC S D

/-- Second affine divisor coordinate at outer wait `211`. -/
def bZeroBDefectCOneSfftV {R : Type*} [CommRing R] (S D z : R) : R :=
  4 * bZeroBDefectCOneSfftN S D * z - bZeroBDefectCOneSfftM S D

/-- At outer wait `211`, the primitive core is a four-term bilinear form in the two
remaining waits. -/
theorem bZeroBDefectCOneCodeCore_x211_normal_form
    {R : Type*} [CommRing R] (S D y z : R) :
    bZeroBDefectCOneCodeCore S (S - 1 - D) 211 y z =
      -32 * bZeroBDefectCOneSfftN S D * y * z +
        8 * bZeroBDefectCOneSfftM S D * y +
        12 * bZeroBDefectCOneSfftC S D * z +
        3 * bZeroBDefectCOneSfftK S D := by
  unfold bZeroBDefectCOneCodeCore bZeroBDefectCOneSfftN
    bZeroBDefectCOneSfftM bZeroBDefectCOneSfftC bZeroBDefectCOneSfftK
  ring

/-- The SFFT resultant at outer wait `211` has only the complement coordinate and one
positive linear factor beyond its fixed content. -/
theorem bZeroBDefectCOneSfft_resultant
    {R : Type*} [CommRing R] (S D : R) :
    bZeroBDefectCOneSfftM S D * bZeroBDefectCOneSfftC S D +
        bZeroBDefectCOneSfftK S D * bZeroBDefectCOneSfftN S D =
      22636197954 * D * bZeroBDefectCOneSfftW S D := by
  unfold bZeroBDefectCOneSfftN bZeroBDefectCOneSfftM bZeroBDefectCOneSfftC
    bZeroBDefectCOneSfftK bZeroBDefectCOneSfftW
  ring

/-- Exact divisor identity.  A zero core makes the left side a positive factorization once
the cylinder signs are supplied. -/
theorem bZeroBDefectCOneSfft_identity
    {R : Type*} [CommRing R] (S D y z : R) :
    bZeroBDefectCOneSfftU S D y * bZeroBDefectCOneSfftV S D z -
        67908593862 * D * bZeroBDefectCOneSfftW S D =
      -bZeroBDefectCOneSfftN S D *
        bZeroBDefectCOneCodeCore S (S - 1 - D) 211 y z := by
  rw [bZeroBDefectCOneCodeCore_x211_normal_form]
  have resultant := bZeroBDefectCOneSfft_resultant S D
  unfold bZeroBDefectCOneSfftU bZeroBDefectCOneSfftV
  linear_combination 3 * resultant

/-- A zero core produces the exact body-dependent divisor equation. -/
theorem bZeroBDefectCOneSfft_eq_of_core_zero
    {R : Type*} [CommRing R] (S D y z : R)
    (core_zero : bZeroBDefectCOneCodeCore S (S - 1 - D) 211 y z = 0) :
    bZeroBDefectCOneSfftU S D y * bZeroBDefectCOneSfftV S D z =
      67908593862 * D * bZeroBDefectCOneSfftW S D := by
  have identity := bZeroBDefectCOneSfft_identity S D y z
  rw [core_zero, mul_zero] at identity
  exact sub_eq_zero.mp identity

/-- The fixed coefficient in the divisor equation is
`2 · 3^14 · 31 · 229`. -/
theorem bZeroBDefectCOneSfft_fixed_content :
    67908593862 = 2 * 3 ^ 14 * 31 * 229 := by norm_num

/-- The two divisor coordinates satisfy their reconstruction congruences. -/
theorem bZeroBDefectCOneSfft_reconstruction_divisibility
    (S D y z : ℤ) :
    8 * bZeroBDefectCOneSfftN S D ∣
        bZeroBDefectCOneSfftU S D y + 3 * bZeroBDefectCOneSfftC S D ∧
      4 * bZeroBDefectCOneSfftN S D ∣
        bZeroBDefectCOneSfftV S D z + bZeroBDefectCOneSfftM S D := by
  constructor
  · refine ⟨y, ?_⟩
    unfold bZeroBDefectCOneSfftU
    ring
  · refine ⟨z, ?_⟩
    unfold bZeroBDefectCOneSfftV
    ring

/-- Eliminating the complement coordinate from `U` leaves the inherited wait factor. -/
theorem bZeroBDefectCOneSfftU_complement_resultant
    {R : Type*} [CommRing R] (S D y : R) :
    bZeroBDefectCOneSfftU S D y +
        6 * (25863242868 * y + 5570432054549) * D =
      116405489 * bZeroBDefectCOneWaitFactor S y := by
  unfold bZeroBDefectCOneSfftU bZeroBDefectCOneSfftN
    bZeroBDefectCOneSfftC bZeroBDefectCOneWaitFactor
  ring

/-- Eliminating the complement coordinate from `V` leaves two affine factors. -/
theorem bZeroBDefectCOneSfftV_complement_resultant
    {R : Type*} [CommRing R] (S D z : R) :
    bZeroBDefectCOneSfftV S D z +
        2997 * (25889132 * z + 2419297) * D =
      (9 * S - 1) * (465621956 * z + 42879529) := by
  unfold bZeroBDefectCOneSfftV bZeroBDefectCOneSfftN bZeroBDefectCOneSfftM
  ring

/-- Eliminating the complement coordinate between `U` and `W` gives this product. -/
theorem bZeroBDefectCOneSfftU_W_resultant
    {R : Type*} [CommRing R] (S D y : R) :
    -6 * (25863242868 * y + 5570432054549) *
          bZeroBDefectCOneSfftW S D +
        1096376045 * bZeroBDefectCOneSfftU S D y =
      -(100325969278335 * S - 11199056405551) *
        (4333144 * y + 953012007) := by
  unfold bZeroBDefectCOneSfftU bZeroBDefectCOneSfftN
    bZeroBDefectCOneSfftC bZeroBDefectCOneSfftW
  ring

/-- Eliminating the complement coordinate between `V` and `W` gives this pencil. -/
theorem bZeroBDefectCOneSfftV_W_resultant
    {R : Type*} [CommRing R] (S D z : R) :
    -2997 * (25889132 * z + 2419297) * bZeroBDefectCOneSfftW S D +
        1096376045 * bZeroBDefectCOneSfftV S D z =
      -541643 *
        (401303877113340 * S * z + 37512705235635 * S -
          44796225622204 * z - 4187413381139) := by
  unfold bZeroBDefectCOneSfftV bZeroBDefectCOneSfftN bZeroBDefectCOneSfftM
    bZeroBDefectCOneSfftW
  ring

/-- If scale and complement are divisible by `3`, then the specialized SFFT coefficients
occupy their fixed residue classes modulo `3`. -/
theorem bZeroBDefectCOneSfft_mod_three
    (S D : ℤ) (scale_divisible : 3 ∣ S) (complement_divisible : 3 ∣ D) :
    (∃ n, bZeroBDefectCOneSfftN S D = 3 * n + 1) ∧
      (∃ m, bZeroBDefectCOneSfftM S D = 3 * m + 1) ∧
      3 ∣ bZeroBDefectCOneSfftC S D ∧
      3 ∣ bZeroBDefectCOneSfftK S D ∧
      3 ∣ bZeroBDefectCOneSfftW S D := by
  obtain ⟨s, rfl⟩ := scale_divisible
  obtain ⟨d, rfl⟩ := complement_divisible
  constructor
  · refine ⟨1047649401 * s - 19397432151 * d - 38801830, ?_⟩
    unfold bZeroBDefectCOneSfftN
    ring
  constructor
  · refine ⟨7250633109 * d - 385915761 * s + 14293176, ?_⟩
    unfold bZeroBDefectCOneSfftM
    ring
  constructor
  · refine ⟨11140864109098 * d + 349216467 * s - 116405489, ?_⟩
    unfold bZeroBDefectCOneSfftC
    ring
  constructor
  · refine ⟨4165661481812 * d + 128638587 * s - 42879529, ?_⟩
    unfold bZeroBDefectCOneSfftK
    ring
  · refine ⟨2860660950 * s - 1096376045 * d - 106431866, ?_⟩
    unfold bZeroBDefectCOneSfftW
    ring

/-- Modulo `3`, the first divisor coordinate is `2y` and the second is `z − 1`. -/
theorem bZeroBDefectCOneSfft_divisor_mod_three
    (S D y z : ℤ) (scale_divisible : 3 ∣ S) (complement_divisible : 3 ∣ D) :
    3 ∣ bZeroBDefectCOneSfftU S D y - 2 * y ∧
      3 ∣ bZeroBDefectCOneSfftV S D z - (z - 1) := by
  rcases bZeroBDefectCOneSfft_mod_three S D scale_divisible complement_divisible with
    ⟨⟨n, n_eq⟩, ⟨m, m_eq⟩, c_divisible, _, _⟩
  obtain ⟨c, c_eq⟩ := c_divisible
  constructor
  · refine ⟨8 * n * y - 3 * c + 2 * y, ?_⟩
    unfold bZeroBDefectCOneSfftU
    rw [n_eq, c_eq]
    ring
  · refine ⟨4 * n * z - m + z, ?_⟩
    unfold bZeroBDefectCOneSfftV
    rw [n_eq, m_eq]
    ring

/-- All five SFFT parameters are positive throughout the full rational density cylinder of a
body beginning `cb`. -/
theorem bZeroBDefectCOneSfft_pos_of_cb_coordinates
    (T E : ℚ) (scale_one : 1 ≤ T) (complement_nonnegative : 0 ≤ E)
    (density_upper : 242 * E ≤ 39 * (T - 1)) :
    0 < bZeroBDefectCOneSfftN (729 * T) (39 * T + E) ∧
      0 < bZeroBDefectCOneSfftM (729 * T) (39 * T + E) ∧
      0 < bZeroBDefectCOneSfftC (729 * T) (39 * T + E) ∧
      0 < bZeroBDefectCOneSfftK (729 * T) (39 * T + E) ∧
      0 < bZeroBDefectCOneSfftW (729 * T) (39 * T + E) := by
  let U : ℚ := 39 * (T - 1) - 242 * E
  have U_nonnegative : 0 ≤ U := by dsimp [U]; linarith
  have scale_positive : 0 < T := lt_of_lt_of_le (by norm_num) scale_one
  have scale_gap_nonnegative : 0 ≤ T - 1 := sub_nonneg.mpr scale_one
  have n_identity :
      242 * bZeroBDefectCOneSfftN (729 * T) (39 * T + E) =
        994747530591 * T + 728329725551 + 19397432151 * U := by
    dsimp [U]
    unfold bZeroBDefectCOneSfftN
    ring
  have w_identity :
      242 * bZeroBDefectCOneSfftW (729 * T) (39 * T + E) =
        494281727698635 * (T - 1) + 494247216829674 + 1096376045 * U := by
    dsimp [U]
    unfold bZeroBDefectCOneSfftW
    ring
  constructor
  · nlinarith
  constructor
  · unfold bZeroBDefectCOneSfftM
    nlinarith
  constructor
  · unfold bZeroBDefectCOneSfftC
    nlinarith
  constructor
  · unfold bZeroBDefectCOneSfftK
    nlinarith
  · nlinarith

private theorem cb_scale (tail : List TagLetter) :
    3 ^ (tagEncode 3 ([.c, .b] ++ tail)).length =
      729 * 3 ^ (tagEncode 3 tail).length := by
  rw [tagEncode_append, List.length_append, pow_add]
  norm_num [tagEncode, spell, tagCode]

private theorem cb_complement (tail : List TagLetter) :
    tagComplementCode ([.c, .b] ++ tail) =
      39 * 3 ^ (tagEncode 3 tail).length + tagComplementCode tail := by
  rw [tagComplementCode_append]
  have stem_complement : tagComplementCode [.c, .b] = 39 := by decide
  rw [stem_complement]

/-- The SFFT parameters are positive on every physical body with prefix `cb`. -/
theorem bZeroBDefectCOneSfft_pos_of_cb (tail : List TagLetter) :
    let body := [.c, .b] ++ tail
    let S := 3 ^ (tagEncode 3 body).length
    let D := tagComplementCode body
    0 < bZeroBDefectCOneSfftN (S : ℚ) D ∧
      0 < bZeroBDefectCOneSfftM (S : ℚ) D ∧
      0 < bZeroBDefectCOneSfftC (S : ℚ) D ∧
      0 < bZeroBDefectCOneSfftK (S : ℚ) D ∧
      0 < bZeroBDefectCOneSfftW (S : ℚ) D := by
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E : Nat := tagComplementCode tail
  have scale_one : 1 ≤ T := by
    dsimp [T]
    exact one_le_pow₀ (by norm_num)
  have density_upper_nat : 242 * E ≤ 39 * (T - 1) := by
    dsimp [T, E]
    exact tagComplementCode_global_bound tail
  have density_upper : (242 : ℚ) * E ≤ 39 * (T - 1) := by
    have cast_bound :
        (242 : ℚ) * E ≤ 39 * ((T - 1 : Nat) : ℚ) := by
      exact_mod_cast density_upper_nat
    have cast_sub : ((T - 1 : Nat) : ℚ) = (T : ℚ) - 1 := by
      rw [Nat.cast_sub scale_one]
      norm_num
    rw [cast_sub] at cast_bound
    exact cast_bound
  have positivity := bZeroBDefectCOneSfft_pos_of_cb_coordinates
    (T : ℚ) E (by exact_mod_cast scale_one) (by positivity) density_upper
  dsimp only
  have scale_eq :
      (3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length =
        729 * (T : ℚ) := by
    exact_mod_cast cb_scale tail
  have complement_eq :
      (tagComplementCode ([.c, .b] ++ tail) : ℚ) = 39 * T + E := by
    exact_mod_cast cb_complement tail
  rw [scale_eq, complement_eq]
  exact positivity

/-- At a zero in the positive SFFT chamber, both affine divisor coordinates are positive. -/
theorem bZeroBDefectCOneSfft_positive_divisors_of_core_zero
    (S D : ℤ) (y z : Nat)
    (complement_positive : 0 < D)
    (m_positive : 0 < bZeroBDefectCOneSfftM S D)
    (k_positive : 0 < bZeroBDefectCOneSfftK S D)
    (w_positive : 0 < bZeroBDefectCOneSfftW S D)
    (core_zero : bZeroBDefectCOneCodeCore S (S - 1 - D) 211 y z = 0) :
    0 < bZeroBDefectCOneSfftU S D y ∧
      0 < bZeroBDefectCOneSfftV S D z ∧
      bZeroBDefectCOneSfftU S D y * bZeroBDefectCOneSfftV S D z =
        67908593862 * D * bZeroBDefectCOneSfftW S D := by
  have divisor_eq := bZeroBDefectCOneSfft_eq_of_core_zero S D (y : ℤ) (z : ℤ) core_zero
  have normal_zero := core_zero
  rw [bZeroBDefectCOneCodeCore_x211_normal_form] at normal_zero
  have y_nonnegative : (0 : ℤ) ≤ y := by positivity
  have z_nonnegative : (0 : ℤ) ≤ z := by positivity
  have z_positive : (0 : ℤ) < z := by
    by_contra z_not_positive
    have z_zero : (z : ℤ) = 0 := by omega
    rw [z_zero] at normal_zero
    nlinarith
  have u_positive : 0 < bZeroBDefectCOneSfftU S D y := by
    unfold bZeroBDefectCOneSfftU
    nlinarith
  have right_positive :
      0 < (67908593862 : ℤ) * D * bZeroBDefectCOneSfftW S D := by positivity
  have v_positive : 0 < bZeroBDefectCOneSfftV S D z := by
    nlinarith [divisor_eq]
  exact ⟨u_positive, v_positive, divisor_eq⟩

end MatrixMortality.ParabolicBlade
