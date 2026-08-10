import Frankl.FiniteLaw

namespace Frankl

open Finset Real Set

/-- The strict Yu entropy gap as a function of its independent, marginal, and dependent terms. -/
noncomputable def yuGap (independent marginal dependent : ℝ) : ℝ :=
  (1 - dependentShare) * independent + dependentShare * dependent
    - (1 + entropySlack) * marginal

/-- The mass needed at parameter one to raise a marginal mean from `s` to `t`. -/
noncomputable def meanLiftRate (s t : ℝ) : ℝ := (t - s) / (1 - s)

theorem meanLiftRate_nonneg {s t : ℝ} (hst : s ≤ t) (hs₁ : s < 1) :
    0 ≤ meanLiftRate s t := by
  exact div_nonneg (sub_nonneg.2 hst) (sub_nonneg.2 hs₁.le)

theorem meanLiftRate_lt_one {s t : ℝ} (ht₁ : t < 1) (hs₁ : s < 1) :
    meanLiftRate s t < 1 := by
  rw [meanLiftRate, div_lt_one (sub_pos.2 hs₁)]
  linarith

theorem meanLiftRate_mean {s t : ℝ} (hs₁ : s < 1) :
    meanLiftRate s t + (1 - meanLiftRate s t) * s = t := by
  have hdenominator : 1 - s ≠ 0 := (sub_pos.2 hs₁).ne'
  dsimp [meanLiftRate]
  field_simp [hdenominator]
  ring

/-- Point support after adjoining the parameter-one atom. -/
noncomputable def meanLiftPoint {ι : Type*} (point : ι → ℝ) : Option ι → ℝ
  | none => 1
  | some i => point i

/-- Weights after adjoining mass `rate` at parameter one. -/
noncomputable def meanLiftWeight {ι : Type*} (rate : ℝ) (weight : ι → ℝ) : Option ι → ℝ
  | none => rate
  | some i => (1 - rate) * weight i

theorem meanLiftWeight_sum {ι : Type*} [Fintype ι] {weight : ι → ℝ} {rate : ℝ}
    (hmass : ∑ i, weight i = 1) :
    ∑ i, meanLiftWeight rate weight i = 1 := by
  classical
  simp [meanLiftWeight, hmass, mul_sum]
  rw [← mul_sum, hmass]
  ring

theorem meanLiftWeight_nonneg {ι : Type*} {weight : ι → ℝ} {rate : ℝ}
    (hweight : ∀ i, 0 ≤ weight i) (hrate₀ : 0 ≤ rate) (hrate₁ : rate ≤ 1) :
    ∀ i, 0 ≤ meanLiftWeight rate weight i := by
  intro i
  cases i with
  | none => exact hrate₀
  | some i => exact mul_nonneg (sub_nonneg.2 hrate₁) (hweight i)

theorem meanLiftPoint_mem {ι : Type*} {point : ι → ℝ}
    (hpoint : ∀ i, point i ∈ Icc (0 : ℝ) 1) :
    ∀ i, meanLiftPoint point i ∈ Icc (0 : ℝ) 1 := by
  intro i
  cases i with
  | none => exact ⟨by simp [meanLiftPoint], by simp [meanLiftPoint]⟩
  | some i => exact hpoint i

theorem finiteExpectation_meanLift_of_value_one_eq_zero
    {ι : Type*} [Fintype ι] {weight point : ι → ℝ} {rate : ℝ} {observable : ℝ → ℝ}
    (hone : observable 1 = 0) :
    finiteExpectation (meanLiftWeight rate weight) (meanLiftPoint point) observable =
      (1 - rate) * finiteExpectation weight point observable := by
  classical
  simp [finiteExpectation, meanLiftWeight, meanLiftPoint, hone, mul_sum]
  apply sum_congr rfl
  intro i _
  ring

theorem finiteExpectation_meanLift_id
    {ι : Type*} [Fintype ι] {weight point : ι → ℝ} {rate mean : ℝ}
    (hmean : ∑ i, weight i * point i = mean) :
    finiteExpectation (meanLiftWeight rate weight) (meanLiftPoint point) id =
      rate + (1 - rate) * mean := by
  classical
  simp [finiteExpectation, meanLiftWeight, meanLiftPoint, hmean, mul_sum]
  rw [← hmean]
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  ring

theorem finiteJoinEntropy_meanLift
    {ι : Type*} [Fintype ι] {weight point : ι → ℝ} {rate : ℝ} :
    finiteJoinEntropy (meanLiftWeight rate weight) (meanLiftPoint point) =
      (1 - rate) ^ 2 * finiteJoinEntropy weight point := by
  classical
  simp [finiteJoinEntropy, meanLiftWeight, meanLiftPoint, mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

/-- Nonnegativity of the lifted strict gap reflects to the original gap. -/
theorem yuGap_nonneg_of_meanLift {independent marginal dependent rate : ℝ}
    (hindependent : 0 ≤ independent) (hrate₀ : 0 ≤ rate) (hrate₁ : rate < 1)
    (hlift :
      0 ≤ yuGap ((1 - rate) ^ 2 * independent) ((1 - rate) * marginal)
        ((1 - rate) * dependent)) :
    0 ≤ yuGap independent marginal dependent := by
  have hshare : 0 ≤ 1 - dependentShare := by
    norm_num [dependentShare]
  dsimp [yuGap] at hlift ⊢
  nlinarith [mul_nonneg (mul_nonneg hshare hrate₀) hindependent]

end Frankl
