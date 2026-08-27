import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

namespace Frankl

open Real Set

/-- The Bernoulli parameter of the Boolean OR of independent Bernoulli parameters. -/
def join (p q : ℝ) : ℝ := p + q - p * q

@[simp]
theorem join_zero_right (p : ℝ) : join p 0 = p := by
  simp [join]

@[simp]
theorem join_one_right (p : ℝ) : join p 1 = 1 := by
  simp [join]

@[simp]
theorem join_one_left (p : ℝ) : join 1 p = 1 := by
  simp [join]

theorem join_comm (p q : ℝ) : join p q = join q p := by
  simp only [join]
  ring

theorem one_sub_join (p q : ℝ) : 1 - join p q = (1 - p) * (1 - q) := by
  simp only [join]
  ring

theorem join_self (p : ℝ) : join p p = 2 * p - p ^ 2 := by
  simp only [join]
  ring

theorem join_mem_Icc {p q : ℝ} (hp : p ∈ Icc 0 1) (hq : q ∈ Icc 0 1) :
    join p q ∈ Icc 0 1 := by
  constructor
  · calc
      0 ≤ p * (1 - q) + q :=
        add_nonneg (mul_nonneg hp.1 (sub_nonneg.2 hq.2)) hq.1
      _ = join p q := by
        simp only [join]
        ring
  · rw [← sub_nonneg, one_sub_join]
    exact mul_nonneg (sub_nonneg.2 hp.2) (sub_nonneg.2 hq.2)

theorem join_pos_of_pos_left {p q : ℝ} (hp : 0 < p) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    0 < join p q := by
  calc
    0 < p * (1 - q) + q := by
      rcases hq₁.eq_or_lt with rfl | hq₁
      · norm_num
      · exact add_pos_of_pos_of_nonneg (mul_pos hp (sub_pos.2 hq₁)) hq₀
    _ = join p q := by
      simp only [join]
      ring

theorem join_lt_one_of_lt_left {p q : ℝ} (hp : p < 1) (hq : q < 1) :
    join p q < 1 := by
  rw [← sub_pos, one_sub_join]
  exact mul_pos (sub_pos.2 hp) (sub_pos.2 hq)

/-- The join-entropy curvature ratio on the low square. -/
theorem join_curvature_ratio_le {p q : ℝ} (hp₀ : 0 < p) (hp₁ : p ≤ 1 / 2)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1 / 2) :
    p * (1 - q) / join p q ≤ (1 - q) / (1 + q) := by
  have hq_lt_one : q < 1 := by linarith
  have hjoin : 0 < join p q := join_pos_of_pos_left hp₀ hq₀ hq_lt_one.le
  have hdenominator : 0 < 1 + q := by linarith
  rw [div_le_div_iff₀ hjoin hdenominator]
  have hcore : p * (1 + q) ≤ join p q := by
    dsimp [join]
    nlinarith [mul_nonneg hq₀ (sub_nonneg.2 hp₁)]
  calc
    p * (1 - q) * (1 + q) = (1 - q) * (p * (1 + q)) := by ring
    _ ≤ (1 - q) * join p q :=
      mul_le_mul_of_nonneg_left hcore (sub_nonneg.2 hq_lt_one.le)

/-- A linear majorant for the join-entropy curvature ratio on the low square. -/
theorem join_curvature_ratio_le_affine {p q : ℝ} (hp₀ : 0 < p) (hp₁ : p ≤ 1 / 2)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1 / 2) :
    p * (1 - q) / join p q ≤ 1 - 4 * q / 3 := by
  refine (join_curvature_ratio_le hp₀ hp₁ hq₀ hq₁).trans ?_
  have hdenominator : 0 < 1 + q := by linarith
  rw [div_le_iff₀ hdenominator]
  nlinarith [mul_nonneg hq₀ (sub_nonneg.2 hq₁)]

/-- The curvature of binary entropy on the open unit interval. -/
theorem iteratedDeriv_two_binEntropy (p : ℝ) :
    deriv^[2] binEntropy p = -1 / (p * (1 - p)) := by
  exact deriv2_binEntropy

end Frankl
