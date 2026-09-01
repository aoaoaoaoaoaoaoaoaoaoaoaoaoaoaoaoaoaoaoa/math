import MatrixMortality.ParabolicFirstBOnePosition

/-!
# Extinction of long trailing runs at outer wait 211

The SFFT product controls the trailing-run length even though its two divisor coordinates can
move along unbounded 3-adic rays. Under the retained inner-wait bound `z < 3^13`, the second
coordinate has order at most thirteen, so the first has order at least `h + 3`. Exact root
congruences reduce every run `h ≥ 6` to four finite middle-wait chambers; density eliminates
three, and the last has incompatible exact coordinate orders.
-/

namespace MatrixMortality.ParabolicBlade

/-- Scale coordinate of a `cb · stem · b c^h` body after the stem scale is named `A`. -/
def firstBOneX211RunScale (h : Nat) (A : ℤ) : ℤ :=
  729 * (243 * 3 ^ h * A)

/-- Complement coordinate of a `cb · stem · b c^h` body after the stem coordinates are
named `A` and `G`. -/
def firstBOneX211RunComplement (h : Nat) (A G : ℤ) : ℤ :=
  39 * (243 * 3 ^ h * A) + 3 ^ (h + 1) * (81 * G + 13)

private abbrev runS := firstBOneX211RunScale
private abbrev runD := firstBOneX211RunComplement

private def runN (h : Nat) (A G : ℤ) : ℤ :=
  bZeroBDefectCOneSfftN (runS h A) (runD h A G)

private def runU (h : Nat) (A G : ℤ) (y : Nat) : ℤ :=
  bZeroBDefectCOneSfftU (runS h A) (runD h A G) (y : ℤ)

private def runV (h : Nat) (A G : ℤ) (z : Nat) : ℤ :=
  bZeroBDefectCOneSfftV (runS h A) (runD h A G) (z : ℤ)

private theorem runD_exact (h : Nat) (A G : ℤ) :
    ExactThreeOrder (runD h A G) (h + 1) := by
  have shape : runD h A G = (3 : ℤ) ^ (h + 1) * (3159 * A + 81 * G + 13) := by
    unfold runD firstBOneX211RunComplement
    rw [pow_succ]
    ring
  rw [shape]
  constructor
  · exact dvd_mul_right ((3 : ℤ) ^ (h + 1)) (3159 * A + 81 * G + 13)
  · intro next_divisible
    rw [pow_succ] at next_divisible
    have power_ne : (3 : ℤ) ^ (h + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have cofactor_divisible : (3 : ℤ) ∣ 3159 * A + 81 * G + 13 :=
      (Int.mul_dvd_mul_iff_left power_ne).mp (by simpa [mul_assoc] using next_divisible)
    obtain ⟨q, equation⟩ := cofactor_divisible
    omega

private theorem runN_unit (h : Nat) (A G : ℤ) :
    ¬(3 : ℤ) ∣ bZeroBDefectCOneSfftN (runS h A) (runD h A G) := by
  intro divisible
  obtain ⟨q, equation⟩ := divisible
  unfold bZeroBDefectCOneSfftN runS runD firstBOneX211RunScale
    firstBOneX211RunComplement at equation
  rw [pow_succ] at equation
  omega

private theorem runW_exact (h : Nat) (A G : ℤ) (h_large : 6 ≤ h) :
    ExactThreeOrder (bZeroBDefectCOneSfftW (runS h A) (runD h A G)) 1 := by
  have h_power : 2 ≤ h + 1 := by omega
  have D_nine : (3 : ℤ) ^ 2 ∣ runD h A G :=
    (pow_dvd_pow (3 : ℤ) h_power).trans (runD_exact h A G).1
  have S_nine : (3 : ℤ) ^ 2 ∣ runS h A := by
    refine ⟨81 * (243 * 3 ^ h * A), ?_⟩
    unfold runS firstBOneX211RunScale
    norm_num
    ring
  have congruent : (3 : ℤ) ^ 2 ∣
      bZeroBDefectCOneSfftW (runS h A) (runD h A G) - 1 * (-319295598) := by
    obtain ⟨s, hs⟩ := S_nine
    obtain ⟨d, hd⟩ := D_nine
    refine ⟨2860660950 * s - 1096376045 * d, ?_⟩
    unfold bZeroBDefectCOneSfftW
    rw [hs, hd]
    norm_num
    ring
  exact (exactThreeOrder_congruent_unit_iff
    (bZeroBDefectCOneSfftW (runS h A) (runD h A G)) 1 (-319295598) 1 2
      (by omega) (by norm_num) congruent).mpr (by norm_num [ExactThreeOrder])

private theorem runV_root_congruent (h : Nat) (A G : ℤ) :
    (3 : ℤ) ^ 14 ∣
      bZeroBDefectCOneSfftV (runS h A) (runD h A G) 420724 -
        1 * (-195898374695673) := by
  refine ⟨(3 : ℤ) ^ h *
    (618725575026 * A - 1658480324535 * G - 266175854555), ?_⟩
  unfold bZeroBDefectCOneSfftV bZeroBDefectCOneSfftN bZeroBDefectCOneSfftM
    runS runD firstBOneX211RunScale firstBOneX211RunComplement
  rw [pow_succ]
  norm_num
  ring

private theorem runV_root_exact (h : Nat) (A G : ℤ) :
    ExactThreeOrder
      (bZeroBDefectCOneSfftV (runS h A) (runD h A G) 420724) 13 := by
  exact (exactThreeOrder_congruent_unit_iff
    (bZeroBDefectCOneSfftV (runS h A) (runD h A G) 420724)
      1 (-195898374695673) 13 14 (by omega) (by norm_num)
      (runV_root_congruent h A G)).mpr (by norm_num [ExactThreeOrder])

private theorem runV_congruent (h : Nat) (A G : ℤ) (z : Nat) :
    (3 : ℤ) ^ 13 ∣
      bZeroBDefectCOneSfftV (runS h A) (runD h A G) z -
        4 * bZeroBDefectCOneSfftN (runS h A) (runD h A G) *
          ((z : ℤ) - 420724) := by
  have root_divisible := (runV_root_exact h A G).1
  convert root_divisible using 1
  unfold bZeroBDefectCOneSfftV
  ring

private theorem runU_h6_congruent (A G : ℤ) (y : Nat) :
    (3 : ℤ) ^ 9 ∣
      bZeroBDefectCOneSfftU (runS 6 A) (runD 6 A G) y -
        8 * bZeroBDefectCOneSfftN (runS 6 A) (runD 6 A G) *
          ((y : ℤ) - 5742) := by
  norm_num [runS, runD, firstBOneX211RunScale, firstBOneX211RunComplement,
    bZeroBDefectCOneSfftU, bZeroBDefectCOneSfftN, bZeroBDefectCOneSfftC]
  ring_nf
  exact ⟨-8746436184677595 * A - 8320167320540670 * G - 1335335767502051, by ring⟩

private theorem runU_h7_congruent (A G : ℤ) (y : Nat) :
    (3 : ℤ) ^ 10 ∣
      bZeroBDefectCOneSfftU (runS 7 A) (runD 7 A G) y -
        8 * bZeroBDefectCOneSfftN (runS 7 A) (runD 7 A G) *
          ((y : ℤ) - 31986) := by
  refine ⟨4927534963244325 * A - 44972934395241438 * G - 7217878864153893, ?_⟩
  norm_num [runS, runD, firstBOneX211RunScale, firstBOneX211RunComplement,
    bZeroBDefectCOneSfftU, bZeroBDefectCOneSfftN, bZeroBDefectCOneSfftC]
  ring

private theorem runU_h8_congruent (A G : ℤ) (y : Nat) :
    (3 : ℤ) ^ 11 ∣
      bZeroBDefectCOneSfftU (runS 8 A) (runD 8 A G) y -
        8 * bZeroBDefectCOneSfftN (runS 8 A) (runD 8 A G) *
          ((y : ℤ) - 51669) := by
  refine ⟨15183013324185765 * A - 72462509701267014 * G - 11629785779223563, ?_⟩
  norm_num [runS, runD, firstBOneX211RunScale, firstBOneX211RunComplement,
    bZeroBDefectCOneSfftU, bZeroBDefectCOneSfftN, bZeroBDefectCOneSfftC]
  ring

private theorem runU_h8_deep_congruent (A G : ℤ) (y : Nat)
    (G_three : (3 : ℤ) ∣ G) :
    (3 : ℤ) ^ 15 ∣
      bZeroBDefectCOneSfftU (runS 8 A) (runD 8 A G) y -
        8 * bZeroBDefectCOneSfftN (runS 8 A) (runD 8 A G) *
          ((y : ℤ) - 228816) := by
  obtain ⟨g, rfl⟩ := G_three
  refine ⟨1326942204600725 * A - 11846988424277674 * g - 633789519029547, ?_⟩
  norm_num [runS, runD, firstBOneX211RunScale, firstBOneX211RunComplement,
    bZeroBDefectCOneSfftU, bZeroBDefectCOneSfftN, bZeroBDefectCOneSfftC]
  ring

private theorem runU_h9_congruent (A G : ℤ) (y : Nat) :
    (3 : ℤ) ^ 12 ∣
      bZeroBDefectCOneSfftU (runS 9 A) (runD 9 A G) y -
        8 * bZeroBDefectCOneSfftN (runS 9 A) (runD 9 A G) *
          ((y : ℤ) - 287865) := by
  refine ⟨138248753655483045 * A - 402337413373573926 * G - 64572671786602317, ?_⟩
  norm_num [runS, runD, firstBOneX211RunScale, firstBOneX211RunComplement,
    bZeroBDefectCOneSfftU, bZeroBDefectCOneSfftN, bZeroBDefectCOneSfftC]
  ring

private theorem runU_high_congruent (h : Nat) (A G : ℤ) (y : Nat)
    (h_large : 10 ≤ h) :
    (3 : ℤ) ^ 12 ∣
      bZeroBDefectCOneSfftU (runS h A) (runD h A G) y -
        8 * bZeroBDefectCOneSfftN (runS h A) (runD h A G) *
          ((y : ℤ) - 465012) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h_large
  refine ⟨(3 : ℤ) ^ k *
      (691644176711868015 * A - 1949230773383412330 * G - 312839506839313090) -
        814838423, ?_⟩
  unfold bZeroBDefectCOneSfftU bZeroBDefectCOneSfftN bZeroBDefectCOneSfftC
    runS runD firstBOneX211RunScale firstBOneX211RunComplement
  simp only [pow_add]
  norm_num
  ring

private theorem run_eightN_unit (h : Nat) (A G : ℤ) :
    ¬(3 : ℤ) ∣ 8 * bZeroBDefectCOneSfftN (runS h A) (runD h A G) := by
  intro divisible
  obtain ⟨q, equation⟩ := divisible
  apply runN_unit h A G
  refine ⟨3 * bZeroBDefectCOneSfftN (runS h A) (runD h A G) - q, ?_⟩
  omega

private theorem run_fourN_unit (h : Nat) (A G : ℤ) :
    ¬(3 : ℤ) ∣ 4 * bZeroBDefectCOneSfftN (runS h A) (runD h A G) := by
  intro divisible
  obtain ⟨q, equation⟩ := divisible
  apply runN_unit h A G
  refine ⟨q - bZeroBDefectCOneSfftN (runS h A) (runD h A G), ?_⟩
  omega

/-- The exact SFFT information used to control a long trailing run. It retains the coordinate
order sum, the unit coefficient, and the universal inner-wait root. -/
def FirstBOneX211RunEnvelope (h : Nat) (A G : ℤ) (y z : Nat) : Prop :=
  let S := firstBOneX211RunScale h A
  let D := firstBOneX211RunComplement h A G
  let N := bZeroBDefectCOneSfftN S D
  let U := bZeroBDefectCOneSfftU S D (y : ℤ)
  let V := bZeroBDefectCOneSfftV S D (z : ℤ)
  padicValInt 3 U + padicValInt 3 V = h + 16 ∧
    ¬(3 : ℤ) ∣ 8 * N ∧ ¬(3 : ℤ) ∣ 4 * N ∧
    ExactThreeOrder (bZeroBDefectCOneSfftV S D 420724) 13 ∧
    (3 : ℤ) ^ 13 ∣ V - 4 * N * ((z : ℤ) - 420724)

private theorem run_product_orders
    (h : Nat) (A G : ℤ) (y z : Nat) (h_large : 6 ≤ h)
    (core_zero :
      bZeroBDefectCOneCodeCore (runS h A) (runS h A - 1 - runD h A G)
        211 y z = 0) :
    runU h A G y ≠ 0 ∧ runV h A G z ≠ 0 ∧
      padicValInt 3 (runU h A G y) + padicValInt 3 (runV h A G z) = h + 16 := by
  let S := runS h A
  let D := runD h A G
  let U := bZeroBDefectCOneSfftU S D (y : ℤ)
  let V := bZeroBDefectCOneSfftV S D (z : ℤ)
  let W := bZeroBDefectCOneSfftW S D
  have d_exact : ExactThreeOrder D (h + 1) := by
    dsimp [D]
    exact runD_exact h A G
  have w_exact : ExactThreeOrder W 1 := by
    dsimp [W, S, D]
    exact runW_exact h A G h_large
  have product_eq : U * V = 67908593862 * D * W := by
    dsimp [U, V, S, D, W]
    exact bZeroBDefectCOneSfft_eq_of_core_zero
      (runS h A) (runD h A G) y z core_zero
  have d_value := (exactThreeOrder_iff_padicValInt D (h + 1)).mp d_exact
  have w_value := (exactThreeOrder_iff_padicValInt W 1).mp w_exact
  have right_ne : (67908593862 : ℤ) * D * W ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) d_value.1) w_value.1
  have product_ne : U * V ≠ 0 := product_eq ▸ right_ne
  have u_ne : U ≠ 0 := left_ne_zero_of_mul product_ne
  have v_ne : V ≠ 0 := right_ne_zero_of_mul product_ne
  have coefficient_order : padicValInt 3 (67908593862 : ℤ) = 14 := by
    exact (exactThreeOrder_iff_padicValInt 67908593862 14).mp
      (by norm_num [ExactThreeOrder]) |>.2
  have left_order := padicValInt.mul (p := 3) u_ne v_ne
  have coefficient_d_ne : (67908593862 : ℤ) * D ≠ 0 :=
    mul_ne_zero (by norm_num) d_value.1
  have coefficient_d_order :=
    padicValInt.mul (p := 3) (by norm_num : (67908593862 : ℤ) ≠ 0) d_value.1
  have right_order := padicValInt.mul (p := 3) coefficient_d_ne w_value.1
  have valuations_equal :
      padicValInt 3 U + padicValInt 3 V =
        padicValInt 3 (67908593862 : ℤ) + padicValInt 3 D + padicValInt 3 W := by
    calc
      padicValInt 3 U + padicValInt 3 V = padicValInt 3 (U * V) := left_order.symm
      _ = padicValInt 3 ((67908593862 : ℤ) * D * W) :=
        congrArg (padicValInt 3) product_eq
      _ = padicValInt 3 ((67908593862 : ℤ) * D) + padicValInt 3 W := right_order
      _ = (padicValInt 3 (67908593862 : ℤ) + padicValInt 3 D) +
          padicValInt 3 W := by rw [coefficient_d_order]
      _ = padicValInt 3 (67908593862 : ℤ) + padicValInt 3 D +
          padicValInt 3 W := by omega
  rw [coefficient_order, d_value.2, w_value.2] at valuations_equal
  have order_final : padicValInt 3 U + padicValInt 3 V = h + 16 := by omega
  refine ⟨?_, ?_, ?_⟩
  · simpa [runU, U, S, D] using u_ne
  · simpa [runV, V, S, D] using v_ne
  · simpa [runU, runV, U, V, S, D] using order_final

/-- A zero at the exact long-run coordinates forces the SFFT run envelope. -/
theorem firstBOneX211RunEnvelope_of_core_zero
    (h : Nat) (A G : ℤ) (y z : Nat) (h_large : 6 ≤ h)
    (core_zero :
      bZeroBDefectCOneCodeCore
        (firstBOneX211RunScale h A)
        (firstBOneX211RunScale h A - 1 - firstBOneX211RunComplement h A G)
        211 y z = 0) :
    FirstBOneX211RunEnvelope h A G y z := by
  obtain ⟨_, _, order_sum⟩ := run_product_orders h A G y z h_large core_zero
  unfold FirstBOneX211RunEnvelope
  exact ⟨order_sum, run_eightN_unit h A G, run_fourN_unit h A G,
    runV_root_exact h A G, runV_congruent h A G z⟩

private theorem h6_density_impossible
    (j y z : Nat) (y_cases : y = 25425 ∨ y = 45108)
    (density : FirstBOneX211DensityEnvelope 6 j y z) : False := by
  rcases y_cases with rfl | rfl
  · by_cases position_large : 13 ≤ j
    · have y_lower : 22529 ≤ 25425 := by omega
      obtain ⟨f_positive, f_upper⟩ :=
        firstBOneX211_large_position_strip 6 j 25425 z position_large y_lower density
      have y_cases := firstBOneX211_large_position_y_cases 25425 z y_lower (by omega)
        f_positive f_upper
      omega
    · have position_small : j ≤ 12 := by omega
      interval_cases j <;>
        norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
          firstBOneX211Q, firstBOneX211J] at density <;>
        omega
  · by_cases position_large : 13 ≤ j
    · have y_lower : 22529 ≤ 45108 := by omega
      obtain ⟨f_positive, f_upper⟩ :=
        firstBOneX211_large_position_strip 6 j 45108 z position_large y_lower density
      have y_cases := firstBOneX211_large_position_y_cases 45108 z y_lower (by omega)
        f_positive f_upper
      omega
    · have position_small : j ≤ 12 := by omega
      interval_cases j <;>
        norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
          firstBOneX211Q, firstBOneX211J] at density <;>
        omega

private theorem h7_density_impossible
    (j z : Nat) (density : FirstBOneX211DensityEnvelope 7 j 31986 z) : False := by
  by_cases position_large : 13 ≤ j
  · obtain ⟨f_positive, f_upper⟩ :=
      firstBOneX211_large_position_strip 7 j 31986 z position_large (by omega) density
    have y_cases := firstBOneX211_large_position_y_cases 31986 z (by omega) (by omega)
      f_positive f_upper
    omega
  · have position_small : j ≤ 12 := by omega
    interval_cases j <;>
      norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
        firstBOneX211Q, firstBOneX211J] at density <;>
      omega

private theorem h8_density_case
    (j z : Nat) (density : FirstBOneX211DensityEnvelope 8 j 51669 z) :
    j = 0 ∧ z = 1 := by
  by_cases position_large : 13 ≤ j
  · obtain ⟨f_positive, f_upper⟩ :=
      firstBOneX211_large_position_strip 8 j 51669 z position_large (by omega) density
    have y_cases := firstBOneX211_large_position_y_cases 51669 z (by omega) (by omega)
      f_positive f_upper
    omega
  · have position_small : j ≤ 12 := by omega
    interval_cases j <;>
      norm_num [FirstBOneX211DensityEnvelope, firstBOneX211A, firstBOneX211B,
        firstBOneX211Q, firstBOneX211J] at density ⊢ <;>
      omega

/-- The exact run and density envelopes force the last `b` to have fewer than six trailing
`c`s. The inner-wait bound is essential: it caps the second SFFT coordinate at order thirteen. -/
theorem firstBOneX211_run_lt_six_of_envelopes
    (h j y z : Nat) (A G : ℤ)
    (y_lower : 22529 ≤ y) (y_upper : y ≤ 51767) (z_upper : z < 3 ^ 13)
    (G_three : (3 : ℤ) ∣ G)
    (valuation : FirstBOneX211RunEnvelope h A G y z)
    (density : FirstBOneX211DensityEnvelope h j y z) :
    h < 6 := by
  by_contra run_not_bounded
  have h_large : 6 ≤ h := by omega
  unfold FirstBOneX211RunEnvelope at valuation
  rcases valuation with
    ⟨order_sum, eight_n_unit, four_n_unit, v_root_exact, v_congruent⟩
  change padicValInt 3 (runU h A G y) + padicValInt 3 (runV h A G z) = h + 16 at order_sum
  change ¬(3 : ℤ) ∣ 8 * runN h A G at eight_n_unit
  change ¬(3 : ℤ) ∣ 4 * runN h A G at four_n_unit
  change ExactThreeOrder
    (bZeroBDefectCOneSfftV (runS h A) (runD h A G) 420724) 13 at v_root_exact
  change (3 : ℤ) ^ 13 ∣
    runV h A G z - 4 * runN h A G * ((z : ℤ) - 420724) at v_congruent
  have v_cap_transfer :
      (3 : ℤ) ^ 13 ∣ runV h A G z ↔ (3 : ℤ) ^ 13 ∣ (z : ℤ) - 420724 :=
    three_pow_dvd_congruent_unit_iff (runV h A G z) (4 * runN h A G)
      ((z : ℤ) - 420724) 13 four_n_unit v_congruent
  have v_bound : padicValInt 3 (runV h A G z) ≤ 13 := by
    by_cases z_eq : z = 420724
    · subst z
      have root_value :=
        (exactThreeOrder_iff_padicValInt
          (bZeroBDefectCOneSfftV (runS h A) (runD h A G) 420724) 13).mp
          v_root_exact
      exact root_value.2.le
    · by_contra order_not_bounded
      have cap_divisible : (3 : ℤ) ^ 13 ∣ runV h A G z :=
        (padicValInt_dvd_iff 13 (runV h A G z)).mpr
          (Or.inr (Nat.le_of_lt (Nat.lt_of_not_ge order_not_bounded)))
      have difference_divisible := v_cap_transfer.mp cap_divisible
      norm_num only [Nat.reducePow] at difference_divisible
      obtain ⟨q, difference_eq⟩ := difference_divisible
      have z_upper_int : (z : ℤ) < 1594323 := by exact_mod_cast z_upper
      have z_nonnegative : (0 : ℤ) ≤ z := by positivity
      have z_eq_int : (z : ℤ) = 420724 := by omega
      exact z_eq (by exact_mod_cast z_eq_int)
  let uOrder := padicValInt 3 (runU h A G y)
  let vOrder := padicValInt 3 (runV h A G z)
  have order_sum_named : uOrder + vOrder = h + 16 := order_sum
  have v_bound_named : vOrder ≤ 13 := v_bound
  have u_lower_named : h + 3 ≤ uOrder := by omega
  have u_lower : h + 3 ≤ padicValInt 3 (runU h A G y) := u_lower_named
  rcases (show h = 6 ∨ h = 7 ∨ h = 8 ∨ h = 9 ∨ 10 ≤ h by omega) with
      rfl | rfl | rfl | rfl | h_high
  · have U_divisible : (3 : ℤ) ^ 9 ∣ runU 6 A G y :=
      (padicValInt_dvd_iff 9 (runU 6 A G y)).mpr (Or.inr u_lower)
    have base_divisible : (3 : ℤ) ^ 9 ∣ (y : ℤ) - 5742 :=
      (three_pow_dvd_congruent_unit_iff (runU 6 A G y) (8 * runN 6 A G)
        ((y : ℤ) - 5742) 9 eight_n_unit
        (by simpa [runU, runN] using runU_h6_congruent A G y)).mp U_divisible
    norm_num only [Nat.reducePow] at base_divisible
    obtain ⟨q, equation⟩ := base_divisible
    have y_cases : y = 25425 ∨ y = 45108 := by omega
    exact h6_density_impossible j y z y_cases density
  · have U_divisible : (3 : ℤ) ^ 10 ∣ runU 7 A G y :=
      (padicValInt_dvd_iff 10 (runU 7 A G y)).mpr (Or.inr u_lower)
    have base_divisible : (3 : ℤ) ^ 10 ∣ (y : ℤ) - 31986 :=
      (three_pow_dvd_congruent_unit_iff (runU 7 A G y) (8 * runN 7 A G)
        ((y : ℤ) - 31986) 10 eight_n_unit
        (by simpa [runU, runN] using runU_h7_congruent A G y)).mp U_divisible
    norm_num only [Nat.reducePow] at base_divisible
    obtain ⟨q, equation⟩ := base_divisible
    have y_eq : y = 31986 := by omega
    subst y
    exact h7_density_impossible j z density
  · have U_divisible : (3 : ℤ) ^ 11 ∣ runU 8 A G y :=
      (padicValInt_dvd_iff 11 (runU 8 A G y)).mpr (Or.inr u_lower)
    have base_divisible : (3 : ℤ) ^ 11 ∣ (y : ℤ) - 51669 :=
      (three_pow_dvd_congruent_unit_iff (runU 8 A G y) (8 * runN 8 A G)
        ((y : ℤ) - 51669) 11 eight_n_unit
        (by simpa [runU, runN] using runU_h8_congruent A G y)).mp U_divisible
    norm_num only [Nat.reducePow] at base_divisible
    obtain ⟨q, equation⟩ := base_divisible
    have y_eq : y = 51669 := by omega
    subst y
    obtain ⟨j_eq, z_eq⟩ := h8_density_case j z density
    subst j
    subst z
    have u_exact : ExactThreeOrder (runU 8 A G 51669) 11 :=
      (exactThreeOrder_congruent_unit_iff (runU 8 A G 51669) (8 * runN 8 A G)
        ((51669 : ℤ) - 228816) 11 15 (by omega) eight_n_unit
        (by simpa [runU, runN] using runU_h8_deep_congruent A G 51669 G_three)).mpr
        (by norm_num [ExactThreeOrder])
    have v_exact : ExactThreeOrder (runV 8 A G 1) 2 :=
      (exactThreeOrder_congruent_unit_iff (runV 8 A G 1) (4 * runN 8 A G)
        ((1 : ℤ) - 420724) 2 13 (by omega) four_n_unit v_congruent).mpr
        (by norm_num [ExactThreeOrder])
    have u_value := (exactThreeOrder_iff_padicValInt (runU 8 A G 51669) 11).mp u_exact
    have v_value := (exactThreeOrder_iff_padicValInt (runV 8 A G 1) 2).mp v_exact
    omega
  · have U_divisible : (3 : ℤ) ^ 12 ∣ runU 9 A G y :=
      (padicValInt_dvd_iff 12 (runU 9 A G y)).mpr (Or.inr u_lower)
    have base_divisible : (3 : ℤ) ^ 12 ∣ (y : ℤ) - 287865 :=
      (three_pow_dvd_congruent_unit_iff (runU 9 A G y) (8 * runN 9 A G)
        ((y : ℤ) - 287865) 12 eight_n_unit
        (by simpa [runU, runN] using runU_h9_congruent A G y)).mp U_divisible
    norm_num only [Nat.reducePow] at base_divisible
    obtain ⟨q, equation⟩ := base_divisible
    omega
  · have U_divisible : (3 : ℤ) ^ 12 ∣ runU h A G y :=
      (padicValInt_dvd_iff 12 (runU h A G y)).mpr
        (Or.inr (le_trans (by omega) u_lower))
    have base_divisible : (3 : ℤ) ^ 12 ∣ (y : ℤ) - 465012 :=
      (three_pow_dvd_congruent_unit_iff (runU h A G y) (8 * runN h A G)
        ((y : ℤ) - 465012) 12 eight_n_unit
        (by simpa [runU, runN] using runU_high_congruent h A G y h_high)).mp U_divisible
    norm_num only [Nat.reducePow] at base_divisible
    obtain ⟨q, equation⟩ := base_divisible
    omega

/-- No exact long-run coordinate zero can satisfy the physical density and bounded-wait
envelopes. -/
theorem bZeroBDefectCOneCodeCore_x211_ne_zero_of_large_run_coordinates
    (h j y z : Nat) (A G : ℤ) (h_large : 6 ≤ h)
    (y_lower : 22529 ≤ y) (y_upper : y ≤ 51767) (z_upper : z < 3 ^ 13)
    (G_three : (3 : ℤ) ∣ G)
    (density : FirstBOneX211DensityEnvelope h j y z) :
    bZeroBDefectCOneCodeCore
      (firstBOneX211RunScale h A)
      (firstBOneX211RunScale h A - 1 - firstBOneX211RunComplement h A G)
      211 y z ≠ 0 := by
  intro core_zero
  have valuation := firstBOneX211RunEnvelope_of_core_zero h A G y z h_large core_zero
  have h_small := firstBOneX211_run_lt_six_of_envelopes h j y z A G y_lower y_upper
    z_upper G_three valuation density
  omega

end MatrixMortality.ParabolicBlade
