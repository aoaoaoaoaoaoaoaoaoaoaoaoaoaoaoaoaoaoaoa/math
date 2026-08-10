import Frankl.OrbitLaw

namespace Frankl

open Finset Filter Real Set Topology

private noncomputable def entropyPower (z : ℝ) (n : ℕ) : ℝ :=
  z ^ (n + 2) / (((n : ℝ) + 1) * ((n : ℝ) + 2))

private theorem hasSum_entropyRemainder {z : ℝ} (hz : |z| < 1) :
    HasSum (entropyPower z)
      (z + (1 - z) * log (1 - z)) := by
  let series := fun n : ℕ ↦ z ^ (n + 1) / ((n : ℝ) + 1)
  have hlog : HasSum series (-log (1 - z)) := by
    simpa only [series] using hasSum_pow_div_log_of_abs_lt_one hz
  have htail : HasSum (fun n ↦ series (n + 1))
      (-log (1 - z) - series 0) := by
    simpa [series] using (hasSum_nat_add_iff' 1).2 hlog
  have hdifference := (hlog.mul_left z).sub htail
  convert hdifference using 1
  · funext n
    dsimp [entropyPower, series]
    field_simp
    ring
  · dsimp [series]
    ring

private theorem hasSum_binEntropyTail {z : ℝ} (hz₀ : 0 ≤ z) (hz₁ : z < 1) :
    HasSum (fun n : ℕ ↦ -entropyPower z n)
      (binEntropy z - negMulLog z - z) := by
  obtain rfl | hz₀ := hz₀.eq_or_lt
  · simpa [entropyPower] using (hasSum_zero : HasSum (fun _ : ℕ ↦ (0 : ℝ)) 0)
  have habs : |z| < 1 := by rw [abs_of_pos hz₀]; exact hz₁
  have hseries := (hasSum_entropyRemainder habs).neg
  convert hseries using 1
  rw [binEntropy]
  rw [log_inv, log_inv]
  dsimp [negMulLog]
  ring

private theorem doubleSum_product {ι : Type*} [Fintype ι] (left right : ι → ℝ) :
    ∑ i, ∑ j, left i * right j = (∑ i, left i) * ∑ j, right j := by
  rw [Finset.sum_mul_sum]

private theorem doubleSum_separable_zero {ι : Type*} [Fintype ι]
    {difference scaled : ι → ℝ} (hscaled : ∑ i, difference i * scaled i = 0)
    (observable : ι → ℝ) :
    ∑ i, ∑ j,
        difference i * difference j
          * (scaled j * observable i + scaled i * observable j) = 0 := by
  calc
    ∑ i, ∑ j,
        difference i * difference j
          * (scaled j * observable i + scaled i * observable j) =
        (∑ i, difference i * observable i) * (∑ j, difference j * scaled j)
          + (∑ i, difference i * scaled i) * (∑ j, difference j * observable j) := by
      rw [← doubleSum_product, ← doubleSum_product, ← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro j _
      ring
    _ = 0 := by rw [hscaled]; ring

private theorem scaledProductKernel_nonpos {ι : Type*} [Fintype ι]
    {difference point : ι → ℝ}
    (hpoint₀ : ∀ i, 0 ≤ point i) (hpoint₁ : ∀ i, point i ≤ 1)
    (hmoment : ∑ i, difference i * point i = 0)
    {scale : ℝ} (hscale₀ : 0 ≤ scale) (hscale₁ : scale < 1) :
    ∑ i, ∑ j,
        difference i * difference j
          * binEntropy ((scale * point i) * (scale * point j)) ≤ 0 := by
  classical
  let scaled := fun i ↦ scale * point i
  have hscaled₀ : ∀ i, 0 ≤ scaled i := fun i ↦ mul_nonneg hscale₀ (hpoint₀ i)
  have hscaled₁ : ∀ i, scaled i < 1 := fun i ↦ by
    exact (mul_le_of_le_one_right hscale₀ (hpoint₁ i)).trans_lt hscale₁
  have hscaledMoment : ∑ i, difference i * scaled i = 0 := by
    dsimp [scaled]
    calc
      ∑ i, difference i * (scale * point i) = scale * ∑ i, difference i * point i := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hmoment, mul_zero]
  have hpointSeries : ∀ i j,
      HasSum
        (fun n : ℕ ↦
          difference i * difference j
            * (-entropyPower (scaled i * scaled j) n))
        (difference i * difference j
          * (binEntropy (scaled i * scaled j) - negMulLog (scaled i * scaled j)
            - scaled i * scaled j)) := by
    intro i j
    have hproduct₀ : 0 ≤ scaled i * scaled j := mul_nonneg (hscaled₀ i) (hscaled₀ j)
    have hproduct₁ : scaled i * scaled j < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_left (hscaled₀ i) (hscaled₁ i) (hscaled₁ j).le
    exact (hasSum_binEntropyTail hproduct₀ hproduct₁).mul_left
      (difference i * difference j)
  have hseries :
      HasSum
        (fun n : ℕ ↦ (∑ i, ∑ j,
          difference i * difference j
            * (-entropyPower (scaled i * scaled j) n)))
        (∑ i, ∑ j, difference i * difference j
          * (binEntropy (scaled i * scaled j) - negMulLog (scaled i * scaled j)
            - scaled i * scaled j)) := by
    apply hasSum_sum
    intro i _
    apply hasSum_sum
    intro j _
    exact hpointSeries i j
  have htermIdentity : ∀ n : ℕ,
      (∑ i, ∑ j,
        difference i * difference j
          * (-entropyPower (scaled i * scaled j) n)) =
        -(∑ i, difference i * scaled i ^ (n + 2)) ^ 2
          / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    intro n
    have hfactor :
        (∑ i, difference i * scaled i ^ (n + 2)) ^ 2 =
          ∑ i, ∑ j,
            (difference i * scaled i ^ (n + 2))
              * (difference j * scaled j ^ (n + 2)) := by
      rw [pow_two, Finset.sum_mul_sum]
    rw [hfactor]
    dsimp [entropyPower]
    let denominator := ((n : ℝ) + 1) * ((n : ℝ) + 2)
    calc
      ∑ i, ∑ j,
          difference i * difference j
            * (-((scaled i * scaled j) ^ (n + 2) / denominator)) =
          ∑ i, ∑ j,
            (-(difference i * scaled i ^ (n + 2)
              * (difference j * scaled j ^ (n + 2)))) / denominator := by
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro j _
        rw [mul_pow]
        ring
      _ = ∑ i,
          (∑ j, -(difference i * scaled i ^ (n + 2)
            * (difference j * scaled j ^ (n + 2)))) / denominator := by
        apply sum_congr rfl
        intro i _
        rw [sum_div]
      _ = (∑ i, ∑ j,
          -(difference i * scaled i ^ (n + 2)
            * (difference j * scaled j ^ (n + 2)))) / denominator := by
        rw [sum_div]
      _ = (-∑ i, ∑ j,
          difference i * scaled i ^ (n + 2)
            * (difference j * scaled j ^ (n + 2))) / denominator := by
        simp only [sum_neg_distrib]
  have hterms : ∀ n : ℕ,
      (∑ i, ∑ j,
        difference i * difference j
          * (-entropyPower (scaled i * scaled j) n)) ≤ 0 := by
    intro n
    rw [htermIdentity n]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
      (mul_nonneg (by positivity) (by positivity))
  have htailNonpos :
      (∑ i, ∑ j, difference i * difference j
        * (binEntropy (scaled i * scaled j) - negMulLog (scaled i * scaled j)
          - scaled i * scaled j)) ≤ 0 := by
    exact hasSum_le hterms hseries (hasSum_zero : HasSum (fun _ : ℕ ↦ (0 : ℝ)) 0)
  have hnegMulLog :
      ∑ i, ∑ j, difference i * difference j * negMulLog (scaled i * scaled j) = 0 := by
    simp_rw [negMulLog_mul]
    exact doubleSum_separable_zero hscaledMoment (fun i ↦ negMulLog (scaled i))
  have hproduct :
      ∑ i, ∑ j, difference i * difference j * (scaled i * scaled j) = 0 := by
    calc
      ∑ i, ∑ j, difference i * difference j * (scaled i * scaled j) =
          (∑ i, difference i * scaled i) * ∑ j, difference j * scaled j := by
        rw [← doubleSum_product]
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [hscaledMoment, zero_mul]
  change ∑ i, ∑ j,
      difference i * difference j * binEntropy (scaled i * scaled j) ≤ 0
  calc
    ∑ i, ∑ j, difference i * difference j * binEntropy (scaled i * scaled j) =
        (∑ i, ∑ j, difference i * difference j
          * (binEntropy (scaled i * scaled j) - negMulLog (scaled i * scaled j)
            - scaled i * scaled j))
          + (∑ i, ∑ j,
            difference i * difference j * negMulLog (scaled i * scaled j))
          + ∑ i, ∑ j, difference i * difference j * (scaled i * scaled j) := by
      rw [← sum_add_distrib, ← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      rw [← sum_add_distrib, ← sum_add_distrib]
      apply sum_congr rfl
      intro j _
      ring
    _ = ∑ i, ∑ j, difference i * difference j
        * (binEntropy (scaled i * scaled j) - negMulLog (scaled i * scaled j)
          - scaled i * scaled j) := by
      rw [hnegMulLog, hproduct, add_zero, add_zero]
    _ ≤ 0 := htailNonpos

private theorem productKernel_nonpos {ι : Type*} [Fintype ι]
    {difference point : ι → ℝ}
    (hpoint₀ : ∀ i, 0 ≤ point i) (hpoint₁ : ∀ i, point i ≤ 1)
    (hmoment : ∑ i, difference i * point i = 0) :
    ∑ i, ∑ j,
        difference i * difference j * binEntropy (point i * point j) ≤ 0 := by
  let kernel := fun scale : ℝ ↦
    ∑ i, ∑ j,
      difference i * difference j
        * binEntropy ((scale * point i) * (scale * point j))
  have hkernelContinuous : Continuous kernel := by
    dsimp only [kernel]
    fun_prop
  have hscaleTendsto :
      Tendsto (fun n : ℕ ↦ (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) :=
    tendsto_natCast_div_add_atTop 1
  have hkernelTendsto :
      Tendsto (fun n : ℕ ↦ kernel ((n : ℝ) / ((n : ℝ) + 1))) atTop
        (𝓝 (kernel 1)) :=
    (hkernelContinuous.tendsto 1).comp hscaleTendsto
  have hnonpos : ∀ n : ℕ, kernel ((n : ℝ) / ((n : ℝ) + 1)) ≤ 0 := by
    intro n
    have hdenominator : 0 < (n : ℝ) + 1 := by positivity
    have hscale₀ : 0 ≤ (n : ℝ) / ((n : ℝ) + 1) :=
      div_nonneg (Nat.cast_nonneg n) hdenominator.le
    have hscale₁ : (n : ℝ) / ((n : ℝ) + 1) < 1 := by
      rw [div_lt_one hdenominator]
      linarith
    exact scaledProductKernel_nonpos hpoint₀ hpoint₁ hmoment hscale₀ hscale₁
  have hlimit : kernel 1 ≤ 0 :=
    le_of_tendsto hkernelTendsto (Eventually.of_forall hnonpos)
  simpa only [kernel, one_mul] using hlimit

/-- The join-entropy kernel is conditionally negative on signed finite laws whose total mass
and first moment both vanish. This is the finite Alweiss--Huang--Sellke concavity kernel. -/
theorem joinEntropyKernel_nonpos {ι : Type*} [Fintype ι]
    {difference point : ι → ℝ}
    (hpoint : ∀ i, point i ∈ Icc (0 : ℝ) 1)
    (hmass : ∑ i, difference i = 0)
    (hmoment : ∑ i, difference i * point i = 0) :
    ∑ i, ∑ j,
        difference i * difference j * binEntropy (join (point i) (point j)) ≤ 0 := by
  let complement := fun i ↦ 1 - point i
  have hcomplement₀ : ∀ i, 0 ≤ complement i := fun i ↦ sub_nonneg.2 (hpoint i).2
  have hcomplement₁ : ∀ i, complement i ≤ 1 := fun i ↦ by
    dsimp [complement]
    linarith [(hpoint i).1]
  have hcomplementMoment : ∑ i, difference i * complement i = 0 := by
    dsimp only [complement]
    calc
      ∑ i, difference i * (1 - point i) =
          (∑ i, difference i) - ∑ i, difference i * point i := by
        rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hmass, hmoment, sub_zero]
  have hproduct := productKernel_nonpos hcomplement₀ hcomplement₁ hcomplementMoment
  dsimp only [complement] at hproduct
  calc
    ∑ i, ∑ j,
        difference i * difference j * binEntropy (join (point i) (point j)) =
      ∑ i, ∑ j,
        difference i * difference j * binEntropy ((1 - point i) * (1 - point j)) := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      rw [← one_sub_join, binEntropy_one_sub]
    _ ≤ 0 := hproduct

private theorem finiteJoinEntropy_mix_sub_eq {ι : Type*} [Fintype ι]
    (lowWeight highWeight : ι → ℝ) (point : ι → ℝ) (p : ℝ) :
    finiteJoinEntropy (fun i ↦ p * lowWeight i + (1 - p) * highWeight i) point
        - (p * finiteJoinEntropy lowWeight point
          + (1 - p) * finiteJoinEntropy highWeight point) =
      -p * (1 - p)
        * ∑ i, ∑ j,
          (lowWeight i - highWeight i) * (lowWeight j - highWeight j)
            * binEntropy (join (point i) (point j)) := by
  classical
  let kernel := fun i j ↦ binEntropy (join (point i) (point j))
  have haverage :
      p * finiteJoinEntropy lowWeight point
          + (1 - p) * finiteJoinEntropy highWeight point =
        ∑ i, ∑ j,
          (p * (lowWeight i * lowWeight j * kernel i j)
            + (1 - p) * (highWeight i * highWeight j * kernel i j)) := by
    dsimp [finiteJoinEntropy]
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rw [mul_sum, mul_sum, ← sum_add_distrib]
  have hscaled :
      -p * (1 - p)
          * ∑ i, ∑ j,
            (lowWeight i - highWeight i) * (lowWeight j - highWeight j) * kernel i j =
        ∑ i, ∑ j,
          (-p * (1 - p))
            * ((lowWeight i - highWeight i) * (lowWeight j - highWeight j)
              * kernel i j) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [mul_sum]
  rw [haverage]
  rw [show finiteJoinEntropy
      (fun i ↦ p * lowWeight i + (1 - p) * highWeight i) point =
      ∑ i, ∑ j,
        (p * lowWeight i + (1 - p) * highWeight i)
          * (p * lowWeight j + (1 - p) * highWeight j) * kernel i j by
    rfl]
  rw [hscaled]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  ring

/-- Independent join entropy is concave along finite probability laws with one fixed mean. -/
theorem finiteJoinEntropy_fixedMean_concave {ι : Type*} [Fintype ι]
    {lowWeight highWeight point : ι → ℝ} {mean p : ℝ}
    (hpoint : ∀ i, point i ∈ Icc (0 : ℝ) 1)
    (hlowMass : ∑ i, lowWeight i = 1) (hhighMass : ∑ i, highWeight i = 1)
    (hlowMean : ∑ i, lowWeight i * point i = mean)
    (hhighMean : ∑ i, highWeight i * point i = mean)
    (hp : p ∈ Icc (0 : ℝ) 1) :
    p * finiteJoinEntropy lowWeight point + (1 - p) * finiteJoinEntropy highWeight point ≤
      finiteJoinEntropy (fun i ↦ p * lowWeight i + (1 - p) * highWeight i) point := by
  let difference := fun i ↦ lowWeight i - highWeight i
  have hmass : ∑ i, difference i = 0 := by
    dsimp only [difference]
    rw [sum_sub_distrib, hlowMass, hhighMass, sub_self]
  have hmean : ∑ i, difference i * point i = 0 := by
    dsimp only [difference]
    calc
      ∑ i, (lowWeight i - highWeight i) * point i =
          (∑ i, lowWeight i * point i) - ∑ i, highWeight i * point i := by
        rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hlowMean, hhighMean, sub_self]
  have hkernel := joinEntropyKernel_nonpos hpoint hmass hmean
  rw [← sub_nonneg]
  rw [finiteJoinEntropy_mix_sub_eq]
  exact mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr hp.1) (sub_nonneg.2 hp.2)) hkernel

/-- Independent entropy is concave in the weights of symmetric orbit laws on one exact-mean
slice. -/
theorem orbitIndependentEntropy_fixedMean_concave {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean p : ℝ}
    (hleft : ∀ i, left i ∈ Icc (0 : ℝ) 1)
    (hright : ∀ i, right i ∈ Icc (0 : ℝ) 1)
    (hp : p ∈ Icc (0 : ℝ) 1) (low high : FiniteOrbitLaw left right mean) :
    p * orbitIndependentEntropy low + (1 - p) * orbitIndependentEntropy high ≤
      orbitIndependentEntropy (FiniteMomentLaw.mix p low high hp) := by
  dsimp only [orbitIndependentEntropy]
  rw [orbitMarginalWeight_mix hp]
  exact finiteJoinEntropy_fixedMean_concave
    (orbitMarginalPoint_mem hleft hright)
    (orbitMarginalWeight_sum low) (orbitMarginalWeight_sum high)
    (orbitMarginal_mean low) (orbitMarginal_mean high) hp

/-- Every finite symmetric exact-mean coupling has a no-worse representative on at most two
orbits. The fixed-mean concavity premise is discharged by the entropy kernel theorem above. -/
theorem orbitYuGap_exists_support_card_le_two_of_mem {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ}
    (hleft : ∀ i, left i ∈ Icc (0 : ℝ) 1)
    (hright : ∀ i, right i ∈ Icc (0 : ℝ) 1)
    (law : FiniteOrbitLaw left right mean) :
    ∃ reduced : FiniteOrbitLaw left right mean,
      reduced.support.card ≤ 2 ∧ orbitYuGap reduced ≤ orbitYuGap law := by
  exact orbitYuGap_exists_support_card_le_two
    (fun p hp low high ↦
      orbitIndependentEntropy_fixedMean_concave hleft hright hp low high)
    law

/-- Sharpened orbit reduction: a no-worse coupling is either one exact-mean orbit or two
orbits whose means strictly straddle the prescribed marginal mean. -/
theorem orbitYuGap_exists_support_straddles_of_mem {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ}
    (hleft : ∀ i, left i ∈ Icc (0 : ℝ) 1)
    (hright : ∀ i, right i ∈ Icc (0 : ℝ) 1)
    (law : FiniteOrbitLaw left right mean) :
    ∃ reduced : FiniteOrbitLaw left right mean,
      orbitYuGap reduced ≤ orbitYuGap law ∧
        ((∃ i, i ∈ reduced.support ∧ reduced.support.card = 1
            ∧ orbitMean left right i = mean) ∨
          ∃ i j, i ≠ j ∧ i ∈ reduced.support ∧ j ∈ reduced.support
            ∧ reduced.support.card = 2
            ∧ orbitMean left right i < mean ∧ mean < orbitMean left right j) := by
  exact FiniteMomentLaw.exists_support_straddles
    (orbitYuGap_isConcave fun p hp low high ↦
      orbitIndependentEntropy_fixedMean_concave hleft hright hp low high)
    law

/-- The fully identified support shape of an extreme finite orbit law. -/
def IsIdentifiedOrbitExtreme {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ} (law : FiniteOrbitLaw left right mean) : Prop :=
  (∃ i, i ∈ law.support ∧ law.support.card = 1 ∧ orbitMean left right i = mean) ∨
    ∃ i j, i ≠ j ∧ i ∈ law.support ∧ j ∈ law.support
      ∧ law.support.card = 2
      ∧ orbitMean left right i < mean ∧ mean < orbitMean left right j
      ∧ law.weight i = lowerOrbitWeight (orbitMean left right i) mean
        (orbitMean left right j)
      ∧ law.weight j = upperOrbitWeight (orbitMean left right i) mean
        (orbitMean left right j)

/-- Fully identified orbit extreme: in the two-orbit case, the live masses are exactly the
lower and upper exact-mean weights used by the contraction estimates. -/
theorem orbitYuGap_exists_extreme_orbitWeights_of_mem {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ}
    (hleft : ∀ i, left i ∈ Icc (0 : ℝ) 1)
    (hright : ∀ i, right i ∈ Icc (0 : ℝ) 1)
    (law : FiniteOrbitLaw left right mean) :
    ∃ reduced : FiniteOrbitLaw left right mean,
      orbitYuGap reduced ≤ orbitYuGap law ∧ IsIdentifiedOrbitExtreme reduced := by
  simpa only [IsIdentifiedOrbitExtreme] using
    FiniteMomentLaw.exists_support_straddles_with_weights
      (orbitYuGap_isConcave fun p hp low high ↦
        orbitIndependentEntropy_fixedMean_concave hleft hright hp low high)
      law

end Frankl
