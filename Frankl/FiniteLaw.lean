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
        replacementMass * finiteExpectation newWeight point (halfSupportGain z) := by
    rw [sum_comm]
    calc
      ∑ j, ∑ i, (newWeight i - oldWeight i) * newWeight j * kernel i j =
          ∑ j, newWeight j
            * (∑ i, (newWeight i - oldWeight i) * kernel i j) := by
        apply sum_congr rfl
        intro j _
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        ring
      _ = ∑ j, newWeight j * (replacementMass * halfSupportGain z (point j)) := by
        apply sum_congr rfl
        intro j _
        rw [show (∑ i, (newWeight i - oldWeight i) * kernel i j) =
            replacementMass * halfSupportGain z (point j) by
          simpa only [kernel] using hkernel (point j)]
      _ = replacementMass * finiteExpectation newWeight point (halfSupportGain z) := by
        dsimp [finiteExpectation]
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        ring
  have hsecond :
      ∑ i, ∑ j, oldWeight i * (newWeight j - oldWeight j) * kernel i j =
        replacementMass * finiteExpectation oldWeight point (halfSupportGain z) := by
    calc
      ∑ i, ∑ j, oldWeight i * (newWeight j - oldWeight j) * kernel i j =
          ∑ i, oldWeight i
            * (∑ j, (newWeight j - oldWeight j) * kernel i j) := by
        apply sum_congr rfl
        intro i _
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        ring
      _ = ∑ i, oldWeight i * (replacementMass * halfSupportGain z (point i)) := by
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
        rw [show (∑ j, (newWeight j - oldWeight j) * kernel j i) =
            replacementMass * halfSupportGain z (point i) by
          simpa only [kernel] using hkernel (point i)]
      _ = replacementMass * finiteExpectation oldWeight point (halfSupportGain z) := by
        dsimp [finiteExpectation]
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        ring
  rw [hsplit, hfirst, hsecond]
  ring

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
