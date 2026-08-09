import Frankl.HalfSupport

namespace Frankl

open Finset Real Set

/-- The expectation of a scalar observable under finitely indexed real weights. -/
noncomputable def finiteExpectation {ι : Type*} [Fintype ι]
    (weight : ι → ℝ) (point : ι → ℝ) (observable : ℝ → ℝ) : ℝ :=
  ∑ i, weight i * observable (point i)

/-- Independent join entropy under a finitely indexed marginal law. -/
noncomputable def finiteJoinEntropy {ι : Type*} [Fintype ι]
    (weight : ι → ℝ) (point : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, weight i * weight j * binEntropy (join (point i) (point j))

theorem finiteJoinEntropy_eq_iteratedExpectation {ι : Type*} [Fintype ι]
    (weight point : ι → ℝ) :
    finiteJoinEntropy weight point =
      finiteExpectation weight point (fun p ↦
        finiteExpectation weight point (fun q ↦ binEntropy (join p q))) := by
  classical
  dsimp [finiteJoinEntropy, finiteExpectation]
  apply sum_congr rfl
  intro i _
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  ring

/-- Jensen and monotonicity bound the expected half-support gain by its value at the candidate
mean. -/
theorem finiteExpectation_halfSupportGain_le {ι : Type*} [Fintype ι]
    {weight point : ι → ℝ} {z mean : ℝ}
    (hweight : ∀ i, 0 ≤ weight i) (hmass : ∑ i, weight i = 1)
    (hpoint : ∀ i, point i ∈ Icc (0 : ℝ) 1)
    (hmean : ∑ i, weight i * point i = mean)
    (hmean₀ : 0 ≤ mean) (hmeanTarget : mean ≤ abundanceTarget)
    (hz₀ : 0 < z) (hzHalf : z ≤ 1 / 2) :
    finiteExpectation weight point (halfSupportGain z) ≤
      halfSupportGain z abundanceTarget := by
  have hjensen := (halfSupportGain_concave hz₀ hzHalf).le_map_sum
    (t := univ) (w := weight) (p := point)
    (fun i _ ↦ hweight i) hmass (fun i _ ↦ hpoint i)
  dsimp only [smul_eq_mul, Function.comp_apply] at hjensen
  have hmeanMem : mean ∈ Icc (0 : ℝ) 1 := ⟨hmean₀, by linarith [abundanceTarget_lt_half]⟩
  have htargetMem : abundanceTarget ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [abundanceTarget_gt_three_eighths], by linarith [abundanceTarget_lt_half]⟩
  rw [hmean] at hjensen
  exact hjensen.trans ((halfSupportGain_monotone hz₀ hzHalf) hmeanMem htargetMem hmeanTarget)

/-- Polarization of independent join entropy across an arbitrary finite signed kernel. -/
theorem finiteJoinEntropy_sub_eq_of_kernelFunction {ι : Type*} [Fintype ι]
    {oldWeight newWeight point : ι → ℝ} {gain : ℝ → ℝ}
    (hkernel : ∀ r : ℝ,
      ∑ i, (newWeight i - oldWeight i) * binEntropy (join (point i) r) = gain r) :
    finiteJoinEntropy newWeight point - finiteJoinEntropy oldWeight point =
      finiteExpectation newWeight point gain + finiteExpectation oldWeight point gain := by
  classical
  let kernel := fun i j ↦ binEntropy (join (point i) (point j))
  have hfactor :
      finiteJoinEntropy newWeight point - finiteJoinEntropy oldWeight point =
        ∑ i, ∑ j,
          ((newWeight i - oldWeight i) * newWeight j
            + oldWeight i * (newWeight j - oldWeight j)) * kernel i j := by
    dsimp [finiteJoinEntropy, kernel]
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    ring
  rw [hfactor]
  have hsplit :
      (∑ i, ∑ j,
        ((newWeight i - oldWeight i) * newWeight j
          + oldWeight i * (newWeight j - oldWeight j)) * kernel i j) =
        (∑ i, ∑ j, (newWeight i - oldWeight i) * newWeight j * kernel i j)
          + ∑ i, ∑ j, oldWeight i * (newWeight j - oldWeight j) * kernel i j := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  have hfirst :
      ∑ i, ∑ j, (newWeight i - oldWeight i) * newWeight j * kernel i j =
        finiteExpectation newWeight point gain := by
    rw [sum_comm]
    calc
      ∑ j, ∑ i, (newWeight i - oldWeight i) * newWeight j * kernel i j =
          ∑ j, newWeight j * (∑ i, (newWeight i - oldWeight i) * kernel i j) := by
        apply sum_congr rfl
        intro j _
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        ring
      _ = ∑ j, newWeight j * gain (point j) := by
        apply sum_congr rfl
        intro j _
        rw [show (∑ i, (newWeight i - oldWeight i) * kernel i j) = gain (point j) by
          simpa only [kernel] using hkernel (point j)]
      _ = finiteExpectation newWeight point gain := rfl
  have hsecond :
      ∑ i, ∑ j, oldWeight i * (newWeight j - oldWeight j) * kernel i j =
        finiteExpectation oldWeight point gain := by
    calc
      ∑ i, ∑ j, oldWeight i * (newWeight j - oldWeight j) * kernel i j =
          ∑ i, oldWeight i * (∑ j, (newWeight j - oldWeight j) * kernel i j) := by
        apply sum_congr rfl
        intro i _
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        ring
      _ = ∑ i, oldWeight i * gain (point i) := by
        apply sum_congr rfl
        intro i _
        have hswap :
            ∑ j, (newWeight j - oldWeight j) * kernel i j =
              ∑ j, (newWeight j - oldWeight j) * kernel j i := by
          apply sum_congr rfl
          intro j _
          dsimp [kernel]
          rw [join_comm (point i) (point j)]
        rw [hswap]
        rw [show (∑ j, (newWeight j - oldWeight j) * kernel j i) = gain (point i) by
          simpa only [kernel] using hkernel (point i)]
      _ = finiteExpectation oldWeight point gain := rfl
  rw [hsplit, hfirst, hsecond]

/-- Polarization for old and new finite laws carried by different index types. -/
theorem finiteJoinEntropy_sub_eq_of_crossKernel {ι κ : Type*} [Fintype ι] [Fintype κ]
    {oldWeight : ι → ℝ} {oldPoint : ι → ℝ}
    {newWeight : κ → ℝ} {newPoint : κ → ℝ} {gain : ℝ → ℝ}
    (hkernel : ∀ r : ℝ,
      (∑ k, newWeight k * binEntropy (join (newPoint k) r))
          - (∑ i, oldWeight i * binEntropy (join (oldPoint i) r)) = gain r) :
    finiteJoinEntropy newWeight newPoint - finiteJoinEntropy oldWeight oldPoint =
      finiteExpectation newWeight newPoint gain + finiteExpectation oldWeight oldPoint gain := by
  classical
  let oldWeight' : Sum ι κ → ℝ
    | Sum.inl i => oldWeight i
    | Sum.inr _ => 0
  let newWeight' : Sum ι κ → ℝ
    | Sum.inl _ => 0
    | Sum.inr k => newWeight k
  let point' : Sum ι κ → ℝ
    | Sum.inl i => oldPoint i
    | Sum.inr k => newPoint k
  have hkernel' : ∀ r : ℝ,
      ∑ z, (newWeight' z - oldWeight' z) * binEntropy (join (point' z) r) = gain r := by
    intro r
    simpa [oldWeight', newWeight', point', Fintype.sum_sum_type, sub_eq_add_neg,
      ← sum_neg_distrib, add_comm] using hkernel r
  have hpolarization := finiteJoinEntropy_sub_eq_of_kernelFunction hkernel'
  simpa [finiteJoinEntropy, finiteExpectation, oldWeight', newWeight', point',
    Fintype.sum_sum_type] using hpolarization

/-- Polarization of independent join entropy across a finite signed replacement kernel. -/
theorem finiteJoinEntropy_sub_eq_of_kernel {ι : Type*} [Fintype ι]
    {oldWeight newWeight : ι → ℝ} {point : ι → ℝ} {z replacementMass : ℝ}
    (hkernel : ∀ r : ℝ,
      ∑ i, (newWeight i - oldWeight i) * binEntropy (join (point i) r) =
        replacementMass * halfSupportGain z r) :
    finiteJoinEntropy newWeight point - finiteJoinEntropy oldWeight point =
      replacementMass
        * (finiteExpectation newWeight point (halfSupportGain z)
          + finiteExpectation oldWeight point (halfSupportGain z)) := by
  classical
  have hpolarization := finiteJoinEntropy_sub_eq_of_kernelFunction
    (gain := fun r ↦ replacementMass * halfSupportGain z r) hkernel
  rw [hpolarization]
  dsimp only [finiteExpectation]
  rw [mul_add, mul_sum, mul_sum]
  congr 1 <;> apply sum_congr rfl <;> intro i _ <;> ring

/-- A half-support kernel with positive replaced mass increases the penalized marginal-minus-join
entropy functional. -/
theorem finiteHalfSupport_penalized_improves {ι : Type*} [Fintype ι]
    {oldWeight newWeight point : ι → ℝ} {z replacementMass oldMean newMean : ℝ}
    (holdWeight : ∀ i, 0 ≤ oldWeight i) (hnewWeight : ∀ i, 0 ≤ newWeight i)
    (holdMass : ∑ i, oldWeight i = 1) (hnewMass : ∑ i, newWeight i = 1)
    (hpoint : ∀ i, point i ∈ Icc (0 : ℝ) 1)
    (holdMean : ∑ i, oldWeight i * point i = oldMean)
    (hnewMean : ∑ i, newWeight i * point i = newMean)
    (holdMean₀ : 0 ≤ oldMean) (hnewMean₀ : 0 ≤ newMean)
    (holdMeanTarget : oldMean ≤ abundanceTarget)
    (hnewMeanTarget : newMean ≤ abundanceTarget)
    (hz₀ : 0 < z) (hzHalf : z < 1 / 2) (hreplacementMass : 0 < replacementMass)
    (hkernel : ∀ r : ℝ,
      ∑ i, (newWeight i - oldWeight i) * binEntropy (join (point i) r) =
        replacementMass * halfSupportGain z r)
    (hmarginal :
      finiteExpectation newWeight point binEntropy
          - finiteExpectation oldWeight point binEntropy =
        replacementMass * halfSupportGain z 0) :
    finiteJoinEntropy newWeight point - finiteJoinEntropy oldWeight point <
      marginalPenalty
        * (finiteExpectation newWeight point binEntropy
          - finiteExpectation oldWeight point binEntropy) := by
  have hnewGain := finiteExpectation_halfSupportGain_le hnewWeight hnewMass hpoint
    hnewMean hnewMean₀ hnewMeanTarget hz₀ hzHalf.le
  have holdGain := finiteExpectation_halfSupportGain_le holdWeight holdMass hpoint
    holdMean holdMean₀ holdMeanTarget hz₀ hzHalf.le
  have hpolarization := finiteJoinEntropy_sub_eq_of_kernel hkernel
  have hscalar := twice_gain_target_lt_penalty_gain_zero hz₀ hzHalf
  rw [hpolarization, hmarginal]
  nlinarith

end Frankl
