import Frankl.FixedMeanConcavity

namespace Frankl

open Finset Real Set

/-- Adjoining the orbit `(1,1)` is pointwise the scalar mean lift on orbit means. -/
theorem orbitMean_meanLiftPoint {ι : Type*} {left right : ι → ℝ} :
    orbitMean (meanLiftPoint left) (meanLiftPoint right) =
      meanLiftPoint (orbitMean left right) := by
  funext z
  cases z <;> simp [orbitMean, meanLiftPoint]

/-- A symmetric orbit law lifted from marginal mean `source` to `target` by adjoining the
zero-cost orbit `(1,1)`. -/
noncomputable def meanLiftOrbitLaw {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {source target : ℝ}
    (law : FiniteOrbitLaw left right source) (hsourceTarget : source ≤ target)
    (hsourceOne : source < 1) (htargetOne : target < 1) :
    FiniteOrbitLaw (meanLiftPoint left) (meanLiftPoint right) target where
  weight := meanLiftWeight (meanLiftRate source target) law.weight
  weight_nonneg := meanLiftWeight_nonneg law.weight_nonneg
    (meanLiftRate_nonneg hsourceTarget hsourceOne)
    (meanLiftRate_lt_one htargetOne hsourceOne).le
  weight_sum := meanLiftWeight_sum law.weight_sum
  moment_sum := by
    rw [orbitMean_meanLiftPoint]
    have hlift := finiteExpectation_meanLift_id
      (rate := meanLiftRate source target) law.moment_sum
    dsimp only [finiteExpectation, id_eq] at hlift
    rw [hlift]
    exact meanLiftRate_mean hsourceOne

/-- Marginal entropy scales linearly under the exact-mean orbit lift. -/
theorem orbitMarginalEntropy_meanLift {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {source target : ℝ}
    (law : FiniteOrbitLaw left right source) (hsourceTarget : source ≤ target)
    (hsourceOne : source < 1) (htargetOne : target < 1) :
    orbitMarginalEntropy
        (meanLiftOrbitLaw law hsourceTarget hsourceOne htargetOne) =
      (1 - meanLiftRate source target) * orbitMarginalEntropy law := by
  classical
  simp [orbitMarginalEntropy, finiteExpectation, orbitMarginalWeight,
    orbitMarginalPoint, meanLiftOrbitLaw, meanLiftWeight, meanLiftPoint,
    Fintype.sum_prod_type, mul_sum]
  apply sum_congr rfl
  intro i _
  ring

/-- The dependent coupling term scales linearly under the exact-mean orbit lift. -/
theorem orbitDependentEntropy_meanLift {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {source target : ℝ}
    (law : FiniteOrbitLaw left right source) (hsourceTarget : source ≤ target)
    (hsourceOne : source < 1) (htargetOne : target < 1) :
    orbitDependentEntropy
        (meanLiftOrbitLaw law hsourceTarget hsourceOne htargetOne) =
      (1 - meanLiftRate source target) * orbitDependentEntropy law := by
  classical
  have hone : dependentCost 1 1 = 0 := by
    rw [dependentCost, dependentParameter, max_self,
      max_eq_left (show (1 / 2 : ℝ) ≤ 1 by norm_num),
      min_eq_right (show (1 : ℝ) ≤ 1 + 1 by norm_num), binEntropy_one]
  simp [orbitDependentEntropy, meanLiftOrbitLaw, meanLiftWeight, meanLiftPoint,
    hone, mul_sum]
  apply sum_congr rfl
  intro i _
  ring

/-- Independent join entropy scales quadratically under the exact-mean orbit lift. -/
theorem orbitIndependentEntropy_meanLift {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {source target : ℝ}
    (law : FiniteOrbitLaw left right source) (hsourceTarget : source ≤ target)
    (hsourceOne : source < 1) (htargetOne : target < 1) :
    orbitIndependentEntropy
        (meanLiftOrbitLaw law hsourceTarget hsourceOne htargetOne) =
      (1 - meanLiftRate source target) ^ 2 * orbitIndependentEntropy law := by
  classical
  simp [orbitIndependentEntropy, finiteJoinEntropy, orbitMarginalWeight,
    orbitMarginalPoint, meanLiftOrbitLaw, meanLiftWeight, meanLiftPoint,
    Fintype.sum_prod_type, mul_sum]
  apply sum_congr rfl
  intro i _
  rw [mul_add, mul_sum, mul_sum]
  congr 1 <;> apply sum_congr rfl <;> intro j _ <;> ring

/-- Nonnegativity of the exact-mean lifted orbit gap reflects to the source law. -/
theorem orbitYuGap_nonneg_of_meanLift {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {source target : ℝ}
    (law : FiniteOrbitLaw left right source) (hsourceTarget : source ≤ target)
    (hsourceOne : source < 1) (htargetOne : target < 1)
    (hindependent : 0 ≤ orbitIndependentEntropy law)
    (hlift : 0 ≤ orbitYuGap
      (meanLiftOrbitLaw law hsourceTarget hsourceOne htargetOne)) :
    0 ≤ orbitYuGap law := by
  rw [orbitYuGap, orbitIndependentEntropy_meanLift,
    orbitMarginalEntropy_meanLift, orbitDependentEntropy_meanLift] at hlift
  exact yuGap_nonneg_of_meanLift hindependent
    (meanLiftRate_nonneg hsourceTarget hsourceOne)
    (meanLiftRate_lt_one htargetOne hsourceOne) hlift

/-- The exact-mean lift reflects gap nonnegativity for probability-valued orbit coordinates. -/
theorem orbitYuGap_nonneg_of_meanLift_of_mem {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {source target : ℝ}
    (hleft : ∀ i, left i ∈ Icc (0 : ℝ) 1)
    (hright : ∀ i, right i ∈ Icc (0 : ℝ) 1)
    (law : FiniteOrbitLaw left right source) (hsourceTarget : source ≤ target)
    (hsourceOne : source < 1) (htargetOne : target < 1)
    (hlift : 0 ≤ orbitYuGap
      (meanLiftOrbitLaw law hsourceTarget hsourceOne htargetOne)) :
    0 ≤ orbitYuGap law := by
  exact orbitYuGap_nonneg_of_meanLift law hsourceTarget hsourceOne htargetOne
    (orbitIndependentEntropy_nonneg hleft hright law) hlift

/-- Every bounded-mean finite orbit law is controlled by the fully identified extremes on the
exact target-mean slice. This composes the mean lift, fixed-mean concavity, and finite support
reduction without any compactness or global-concavity premise. -/
theorem orbitYuGap_nonneg_of_identified_target_extremes {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {source target : ℝ}
    (hleft : ∀ i, left i ∈ Icc (0 : ℝ) 1)
    (hright : ∀ i, right i ∈ Icc (0 : ℝ) 1)
    (law : FiniteOrbitLaw left right source) (hsourceTarget : source ≤ target)
    (hsourceOne : source < 1) (htargetOne : target < 1)
    (hextremes :
      ∀ reduced : FiniteOrbitLaw (meanLiftPoint left) (meanLiftPoint right) target,
        IsIdentifiedOrbitExtreme reduced → 0 ≤ orbitYuGap reduced) :
    0 ≤ orbitYuGap law := by
  let lifted := meanLiftOrbitLaw law hsourceTarget hsourceOne htargetOne
  obtain ⟨reduced, hgap, hextreme⟩ :=
    orbitYuGap_exists_extreme_orbitWeights_of_mem
      (meanLiftPoint_mem hleft) (meanLiftPoint_mem hright) lifted
  have hlift : 0 ≤ orbitYuGap lifted := (hextremes reduced hextreme).trans hgap
  exact orbitYuGap_nonneg_of_meanLift_of_mem hleft hright law hsourceTarget
    hsourceOne htargetOne hlift

end Frankl
