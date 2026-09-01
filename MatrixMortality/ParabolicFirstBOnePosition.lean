import MatrixMortality.ParabolicFirstBOneValuation

/-!
# Extinction of late next-b positions at outer wait 211

The density envelope at a next-`b` position at least thirteen contracts to eleven exact middle
waits after the common displacement `k = y - 22529` is isolated. Every wait contradicts the
base divisibility already present in the valuation envelope. Thus the bounded x=211 classifier
needs no independent next-`b` position cutoff.
-/

namespace MatrixMortality.ParabolicBlade

/-- At a next-`b` position at least thirteen, the density envelope lies in one narrow
Diophantine strip independent of the trailing run. -/
theorem firstBOneX211_large_position_strip
    (h j y z : Nat) (position_large : 13 ≤ j)
    (y_lower : 22529 ≤ y)
    (density : FirstBOneX211DensityEnvelope h j y z) :
    0 < firstBOneX211A y z - 39 * firstBOneX211J y z ∧
      242 * (3 : ℤ) ^ 13 *
          (firstBOneX211A y z - 39 * firstBOneX211J y z) ≤
        firstBOneX211B y z + 39 * firstBOneX211J y z := by
  let p : ℤ := 3 ^ j
  let H : ℤ := 3 ^ (5 + h)
  have p_positive : 0 < p := by dsimp [p]; positivity
  have H_positive : 0 < H := by dsimp [H]; positivity
  have p_lower_nat : 3 ^ 13 ≤ 3 ^ j :=
    Nat.pow_le_pow_right (by norm_num) position_large
  have p_lower : (3 : ℤ) ^ 13 ≤ p := by
    dsimp [p]
    exact_mod_cast p_lower_nat
  have H_lower : (243 : ℤ) ≤ H := by
    dsimp [H]
    have exponent_lower : 5 ≤ 5 + h := by omega
    have power_lower : (3 : Nat) ^ 5 ≤ 3 ^ (5 + h) :=
      Nat.pow_le_pow_right (by norm_num) exponent_lower
    norm_num at power_lower ⊢
    exact_mod_cast power_lower
  have J_positive : 0 < firstBOneX211J y z := by
    unfold firstBOneX211J
    positivity
  have B_nonnegative : 0 ≤ firstBOneX211B y z := by
    have y_lower_int : (22529 : ℤ) ≤ y := by exact_mod_cast y_lower
    have factor_nonnegative : (0 : ℤ) ≤ 8 * y - 9 := by omega
    unfold firstBOneX211B firstBOneX211Q
    exact mul_nonneg factor_nonnegative (by positivity)
  have lower := density.1
  change (39 * (81 * p) + 13) * firstBOneX211J y z ≤
    81 * p * firstBOneX211A y z at lower
  have f_scaled :
      13 * firstBOneX211J y z ≤
        81 * p * (firstBOneX211A y z - 39 * firstBOneX211J y z) := by
    nlinarith
  have f_positive :
      0 < firstBOneX211A y z - 39 * firstBOneX211J y z := by
    by_contra f_not_positive
    have f_nonpositive :
        firstBOneX211A y z - 39 * firstBOneX211J y z ≤ 0 := by omega
    have product_nonpositive :
        81 * p * (firstBOneX211A y z - 39 * firstBOneX211J y z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) f_nonpositive
    nlinarith
  have upper := density.2
  have power_split : (3 : ℤ) ^ (j + 5 + h) = p * H := by
    dsimp [p, H]
    rw [show j + 5 + h = j + (5 + h) by omega, pow_add]
  change
    242 * p *
        ((3 : ℤ) ^ (j + 5 + h) * firstBOneX211A y z - firstBOneX211B y z) ≤
      (3 : ℤ) ^ (j + 5 + h) *
        (39 * (242 * p) + 39) * firstBOneX211J y z at upper
  rw [power_split] at upper
  have upper_cancelled :
      242 * (p * H * firstBOneX211A y z - firstBOneX211B y z) ≤
        H * (39 * (242 * p) + 39) * firstBOneX211J y z := by
    apply (Int.mul_le_mul_left p_positive).mp
    nlinarith [upper]
  have f_upper_at_p :
      242 * p * H *
          (firstBOneX211A y z - 39 * firstBOneX211J y z) ≤
        242 * firstBOneX211B y z + 39 * H * firstBOneX211J y z := by
    nlinarith [upper_cancelled]
  have scale_monotone :
      (3 : ℤ) ^ 13 * H *
          (firstBOneX211A y z - 39 * firstBOneX211J y z) ≤
        p * H * (firstBOneX211A y z - 39 * firstBOneX211J y z) := by
    have scaled := mul_le_mul_of_nonneg_right p_lower
      (mul_nonneg H_positive.le f_positive.le)
    simpa [mul_assoc] using scaled
  have B_absorbed : 242 * firstBOneX211B y z ≤ H * firstBOneX211B y z := by
    nlinarith
  refine ⟨f_positive, ?_⟩
  have H_scaled :
      H * (242 * (3 : ℤ) ^ 13 *
          (firstBOneX211A y z - 39 * firstBOneX211J y z)) ≤
        H * (firstBOneX211B y z + 39 * firstBOneX211J y z) := by
    nlinarith [f_upper_at_p, scale_monotone, B_absorbed]
  exact (Int.mul_le_mul_left H_positive).mp (by simpa [mul_assoc] using H_scaled)

set_option maxHeartbeats 2000000 in
/-- Exact integral classification of the large-position Diophantine strip. The proof first
reduces to `k = y - 22529 ≤ 817`, then checks that single common parameter. -/
theorem firstBOneX211_large_position_y_cases
    (y z : Nat) (y_lower : 22529 ≤ y) (y_upper : y ≤ 51767)
    (f_positive : 0 < firstBOneX211A y z - 39 * firstBOneX211J y z)
    (f_upper :
      242 * (3 : ℤ) ^ 13 *
          (firstBOneX211A y z - 39 * firstBOneX211J y z) ≤
        firstBOneX211B y z + 39 * firstBOneX211J y z) :
    y = 22529 ∨ y = 22530 ∨ y = 22531 ∨ y = 22532 ∨ y = 22533 ∨
      y = 22534 ∨ y = 22538 ∨ y = 22539 ∨ y = 22540 ∨ y = 22573 ∨
      y = 23346 := by
  obtain ⟨k, y_eq⟩ := Nat.exists_eq_add_of_le y_lower
  subst y
  have k_upper : k ≤ 29238 := by omega
  have z_positive : 1 ≤ z := by
    by_contra z_not_positive
    have z_zero : z = 0 := by omega
    subst z
    norm_num [firstBOneX211A, firstBOneX211Q, firstBOneX211J] at f_positive
    omega
  have k_sharp : k ≤ 817 := by
    simp only [firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J] at f_positive f_upper
    norm_num at f_upper
    push_cast at f_positive f_upper
    ring_nf at f_positive f_upper
    have k_nonnegative : (0 : ℤ) ≤ k := by positivity
    have z_positive_int : (1 : ℤ) ≤ z := by exact_mod_cast z_positive
    by_contra k_not_sharp
    have k_large : (818 : ℤ) ≤ k := by omega
    have z_small : z ≤ 3 := by
      by_contra z_not_small
      have z_four : (4 : ℤ) ≤ z := by omega
      have kz_lower : (4 : ℤ) * k ≤ k * z := by nlinarith
      nlinarith [f_upper]
    interval_cases z <;>
      norm_num at f_positive f_upper <;>
      ring_nf at f_positive f_upper <;>
      omega
  interval_cases k <;>
    norm_num [firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J] at f_positive f_upper ⊢ <;>
    ring_nf at f_positive f_upper <;>
    omega

private theorem firstBOneX211_wait_base_dvd
    (h y z : Nat) (valuation : FirstBOneX211ValuationEnvelope h y z) :
    (3 : ℤ) ^ (h + 3) ∣ (y : ℤ) - firstBOneX211RootResidue h := by
  obtain ⟨uOrder, vOrder, u_lower, order_sum, v_upper, wait_shell, inner_shell⟩ :=
    valuation
  rcases wait_shell with shallow | deep
  · exact (pow_dvd_pow (3 : ℤ) u_lower).trans shallow.2.1
  · exact (pow_dvd_pow (3 : ℤ) (by omega)).trans deep.2

/-- The valuation and density envelopes force the tail's next `b` to occur before position
thirteen; no position bound is an input. -/
theorem firstBOneX211_position_lt_thirteen_of_envelopes
    (h j y z : Nat) (h_le : h ≤ 5)
    (y_lower : 22529 ≤ y) (y_upper : y ≤ 51767)
    (valuation : FirstBOneX211ValuationEnvelope h y z)
    (density : FirstBOneX211DensityEnvelope h j y z) :
    j < 13 := by
  by_contra position_not_bounded
  have position_large : 13 ≤ j := by omega
  obtain ⟨f_positive, f_upper⟩ :=
    firstBOneX211_large_position_strip h j y z position_large y_lower density
  have y_cases :=
    firstBOneX211_large_position_y_cases y z y_lower y_upper f_positive f_upper
  have base_divisible := firstBOneX211_wait_base_dvd h y z valuation
  rcases y_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases h <;>
    norm_num [firstBOneX211RootResidue] at base_divisible

/-- The bounded valuation-density classifier needs no independent next-`b` position bound. -/
theorem firstBOneX211Candidate_of_envelopes_without_position_bound
    (h j y z : Nat) (h_le : h ≤ 5)
    (y_lower : 22529 ≤ y) (y_upper : y ≤ 51767) (z_upper : z < 3 ^ 13)
    (valuation : FirstBOneX211ValuationEnvelope h y z)
    (density : FirstBOneX211DensityEnvelope h j y z) :
    FirstBOneX211Candidate h y z ∧ j = 0 := by
  have position_bound :=
    firstBOneX211_position_lt_thirteen_of_envelopes h j y z h_le y_lower y_upper
      valuation density
  exact firstBOneX211Candidate_of_envelopes h j y z h_le position_bound.le y_lower
    y_upper z_upper valuation density

end MatrixMortality.ParabolicBlade
