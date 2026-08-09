import Frankl.MomentReduction

namespace Frankl

open Finset Real Set

/-- The mean of the two coordinates in a symmetric two-point orbit. -/
noncomputable def orbitMean {ι : Type*} (left right : ι → ℝ) (i : ι) : ℝ :=
  (left i + right i) / 2

/-- A finite symmetric coupling represented by weights on unoriented two-point orbits. -/
abbrev FiniteOrbitLaw {ι : Type*} [Fintype ι]
    (left right : ι → ℝ) (mean : ℝ) :=
  FiniteMomentLaw ι (orbitMean left right) mean

/-- The marginal support point selected by one orientation of an orbit. -/
noncomputable def orbitMarginalPoint {ι : Type*} (left right : ι → ℝ) : ι × Bool → ℝ
  | (i, false) => left i
  | (i, true) => right i

/-- The marginal law induced by a symmetric orbit law. -/
noncomputable def orbitMarginalWeight {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ} (law : FiniteOrbitLaw left right mean) :
    ι × Bool → ℝ
  | (i, _) => law.weight i / 2

theorem orbitMarginalWeight_nonneg {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ} (law : FiniteOrbitLaw left right mean) :
    ∀ z, 0 ≤ orbitMarginalWeight law z := by
  intro z
  exact div_nonneg (law.weight_nonneg z.1) (by norm_num)

theorem orbitMarginalWeight_sum {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ} (law : FiniteOrbitLaw left right mean) :
    ∑ z, orbitMarginalWeight law z = 1 := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, orbitMarginalWeight]
  calc
    ∑ i, (law.weight i / 2 + law.weight i / 2) = ∑ i, law.weight i := by
      apply sum_congr rfl
      intro i _
      ring
    _ = 1 := law.weight_sum

theorem orbitMarginalPoint_mem {ι : Type*}
    {left right : ι → ℝ} (hleft : ∀ i, left i ∈ Icc (0 : ℝ) 1)
    (hright : ∀ i, right i ∈ Icc (0 : ℝ) 1) :
    ∀ z, orbitMarginalPoint left right z ∈ Icc (0 : ℝ) 1 := by
  rintro ⟨i, orientation⟩
  cases orientation <;> simp [orbitMarginalPoint, hleft i, hright i]

theorem orbitMarginal_mean {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ} (law : FiniteOrbitLaw left right mean) :
    ∑ z, orbitMarginalWeight law z * orbitMarginalPoint left right z = mean := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, orbitMarginalWeight, orbitMarginalPoint]
  calc
    ∑ i, (law.weight i / 2 * right i + law.weight i / 2 * left i) =
        ∑ i, law.weight i * orbitMean left right i := by
      apply sum_congr rfl
      intro i _
      dsimp [orbitMean]
      ring
    _ = mean := law.moment_sum

/-- Independent-union entropy of the marginal induced by an orbit law. -/
noncomputable def orbitIndependentEntropy {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ} (law : FiniteOrbitLaw left right mean) : ℝ :=
  finiteJoinEntropy (orbitMarginalWeight law) (orbitMarginalPoint left right)

/-- Entropy of the marginal induced by an orbit law. -/
noncomputable def orbitMarginalEntropy {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ} (law : FiniteOrbitLaw left right mean) : ℝ :=
  finiteExpectation (orbitMarginalWeight law) (orbitMarginalPoint left right) binEntropy

/-- Yu's dependent-union entropy averaged over the symmetric coupling orbits. -/
noncomputable def orbitDependentEntropy {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ} (law : FiniteOrbitLaw left right mean) : ℝ :=
  ∑ i, law.weight i * dependentCost (left i) (right i)

/-- The strict candidate gap on a finite symmetric orbit law. -/
noncomputable def orbitYuGap {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ} (law : FiniteOrbitLaw left right mean) : ℝ :=
  yuGap (orbitIndependentEntropy law) (orbitMarginalEntropy law) (orbitDependentEntropy law)

theorem dependentCost_comm (p q : ℝ) : dependentCost p q = dependentCost q p := by
  simp [dependentCost, dependentParameter, add_comm, max_comm]

theorem orbitMarginalWeight_mix {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean p : ℝ} {low high : FiniteOrbitLaw left right mean}
    (hp : p ∈ Icc (0 : ℝ) 1) :
    orbitMarginalWeight (FiniteMomentLaw.mix p low high hp) =
      fun z ↦ p * orbitMarginalWeight low z + (1 - p) * orbitMarginalWeight high z := by
  funext z
  rcases z with ⟨i, orientation⟩
  cases orientation <;> simp [orbitMarginalWeight, FiniteMomentLaw.mix]
  all_goals ring

theorem orbitMarginalEntropy_mix {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean p : ℝ} {low high : FiniteOrbitLaw left right mean}
    (hp : p ∈ Icc (0 : ℝ) 1) :
    orbitMarginalEntropy (FiniteMomentLaw.mix p low high hp) =
      p * orbitMarginalEntropy low + (1 - p) * orbitMarginalEntropy high := by
  classical
  dsimp [orbitMarginalEntropy, finiteExpectation]
  rw [orbitMarginalWeight_mix hp, mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro z _
  ring

theorem orbitDependentEntropy_mix {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean p : ℝ} {low high : FiniteOrbitLaw left right mean}
    (hp : p ∈ Icc (0 : ℝ) 1) :
    orbitDependentEntropy (FiniteMomentLaw.mix p low high hp) =
      p * orbitDependentEntropy low + (1 - p) * orbitDependentEntropy high := by
  classical
  dsimp [orbitDependentEntropy, FiniteMomentLaw.mix]
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  ring

/-- Fixed-mean concavity of independent entropy implies concavity of the complete Yu gap;
the marginal and dependent terms are exactly affine in orbit weights. -/
theorem orbitYuGap_isConcave {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ}
    (hindependent :
      ∀ (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (low high : FiniteOrbitLaw left right mean),
        p * orbitIndependentEntropy low + (1 - p) * orbitIndependentEntropy high ≤
          orbitIndependentEntropy (FiniteMomentLaw.mix p low high hp)) :
    FiniteMomentLaw.IsConcaveFunctional
      (fun law : FiniteOrbitLaw left right mean ↦ orbitYuGap law) := by
  intro p hp low high
  have hcoefficient : 0 ≤ 1 - dependentShare := by
    norm_num [dependentShare]
  have hscaled := mul_le_mul_of_nonneg_left (hindependent p hp low high) hcoefficient
  calc
    p * orbitYuGap low + (1 - p) * orbitYuGap high =
        (1 - dependentShare)
            * (p * orbitIndependentEntropy low + (1 - p) * orbitIndependentEntropy high)
          + dependentShare
            * (p * orbitDependentEntropy low + (1 - p) * orbitDependentEntropy high)
          - (1 + entropySlack)
            * (p * orbitMarginalEntropy low + (1 - p) * orbitMarginalEntropy high) := by
      dsimp [orbitYuGap, yuGap]
      ring
    _ ≤ (1 - dependentShare)
            * orbitIndependentEntropy (FiniteMomentLaw.mix p low high hp)
          + dependentShare * orbitDependentEntropy (FiniteMomentLaw.mix p low high hp)
          - (1 + entropySlack) * orbitMarginalEntropy (FiniteMomentLaw.mix p low high hp) := by
      rw [orbitDependentEntropy_mix hp, orbitMarginalEntropy_mix hp]
      linarith
    _ = orbitYuGap (FiniteMomentLaw.mix p low high hp) := by
      rfl

/-- Subject only to fixed-mean independent-entropy concavity, every finite symmetric coupling
has a no-worse representative supported on at most two symmetric orbits. -/
theorem orbitYuGap_exists_support_card_le_two {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ}
    (hindependent :
      ∀ (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (low high : FiniteOrbitLaw left right mean),
        p * orbitIndependentEntropy low + (1 - p) * orbitIndependentEntropy high ≤
          orbitIndependentEntropy (FiniteMomentLaw.mix p low high hp))
    (law : FiniteOrbitLaw left right mean) :
    ∃ reduced : FiniteOrbitLaw left right mean,
      reduced.support.card ≤ 2 ∧ orbitYuGap reduced ≤ orbitYuGap law := by
  exact FiniteMomentLaw.exists_support_card_le_two (orbitYuGap_isConcave hindependent) law

end Frankl
