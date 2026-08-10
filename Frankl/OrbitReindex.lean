import Frankl.OrbitHalfSupport

namespace Frankl

open Finset Real Set

/-- Marginal entropy contributed by one symmetric orbit. -/
noncomputable def orbitMarginalKernel {ι : Type*} (left right : ι → ℝ) (i : ι) : ℝ :=
  (binEntropy (left i) + binEntropy (right i)) / 2

/-- Independent join entropy contributed by an ordered pair of symmetric orbits. -/
noncomputable def orbitCrossKernel {ι : Type*} (left right : ι → ℝ) (i j : ι) : ℝ :=
  (binEntropy (join (left i) (left j))
    + binEntropy (join (left i) (right j))
    + binEntropy (join (right i) (left j))
    + binEntropy (join (right i) (right j))) / 4

theorem orbitMarginalEntropy_eq_kernel_sum {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ} (law : FiniteOrbitLaw left right mean) :
    orbitMarginalEntropy law = ∑ i, law.weight i * orbitMarginalKernel left right i := by
  classical
  simp [orbitMarginalEntropy, finiteExpectation, orbitMarginalWeight,
    orbitMarginalPoint, orbitMarginalKernel, Fintype.sum_prod_type, Fintype.sum_bool]
  apply sum_congr rfl
  intro i _
  ring

theorem orbitIndependentEntropy_eq_kernel_sum {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ} (law : FiniteOrbitLaw left right mean) :
    orbitIndependentEntropy law =
      ∑ i, ∑ j, law.weight i * law.weight j * orbitCrossKernel left right i j := by
  classical
  simp [orbitIndependentEntropy, finiteJoinEntropy, orbitMarginalWeight,
    orbitMarginalPoint, orbitCrossKernel, Fintype.sum_prod_type, Fintype.sum_bool,
    join_comm]
  apply sum_congr rfl
  intro i _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  ring

/-- Coordinates obtained by reindexing two named old orbits onto `Bool`. -/
noncomputable def reindexedPairCoordinate {ι : Type*} (coordinate : ι → ℝ)
    (lower upper : ι) : Bool → ℝ
  | false => coordinate lower
  | true => coordinate upper

/-- Weights obtained by reindexing two named old atoms onto `Bool`. -/
noncomputable def reindexedPairWeight {ι : Type*} [Fintype ι]
    {moment : ι → ℝ} {mean : ℝ} (law : FiniteMomentLaw ι moment mean)
    (lower upper : ι) : Bool → ℝ
  | false => law.weight lower
  | true => law.weight upper

theorem support_eq_singleton_of_card_eq_one {ι : Type*} [Fintype ι]
    {moment : ι → ℝ} {mean : ℝ} (law : FiniteMomentLaw ι moment mean) {i : ι}
    (hi : i ∈ law.support) (hcard : law.support.card = 1) :
    law.support = {i} := by
  classical
  obtain ⟨j, hsupport⟩ := Finset.card_eq_one.mp hcard
  have hij : i = j := by simpa [hsupport] using hi
  subst j
  exact hsupport

theorem weight_eq_one_of_support_card_eq_one {ι : Type*} [Fintype ι]
    {moment : ι → ℝ} {mean : ℝ} (law : FiniteMomentLaw ι moment mean) {i : ι}
    (hi : i ∈ law.support) (hcard : law.support.card = 1) :
    law.weight i = 1 := by
  classical
  have hsupport := support_eq_singleton_of_card_eq_one law hi hcard
  have hsum := law.sum_weight_eq_sum_support (fun _ ↦ (1 : ℝ))
  simp only [mul_one] at hsum
  rw [law.weight_sum, hsupport] at hsum
  simpa using hsum.symm

theorem moment_eq_mean_of_support_card_eq_one {ι : Type*} [Fintype ι]
    {moment : ι → ℝ} {mean : ℝ} (law : FiniteMomentLaw ι moment mean) {i : ι}
    (hi : i ∈ law.support) (hcard : law.support.card = 1) :
    moment i = mean := by
  classical
  have hsupport := support_eq_singleton_of_card_eq_one law hi hcard
  have hweight := weight_eq_one_of_support_card_eq_one law hi hcard
  have hsum := law.sum_weight_eq_sum_support moment
  rw [law.moment_sum, hsupport] at hsum
  simpa [hweight] using hsum.symm

/-- A one-support orbit law reindexed without changing its orbit. -/
noncomputable def reindexedSingleOrbitLaw {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ} (law : FiniteOrbitLaw left right mean)
    {i : ι} (hi : i ∈ law.support) (hcard : law.support.card = 1) :
    FiniteOrbitLaw (Function.const Unit (left i))
      (Function.const Unit (right i)) mean where
  weight _ := 1
  weight_nonneg _ := by norm_num
  weight_sum := by simp
  moment_sum := by
    simpa using
      moment_eq_mean_of_support_card_eq_one law hi hcard

/-- Reindexing the sole live orbit preserves the complete Yu gap. -/
theorem reindexedSingleOrbitLaw_gap_eq {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ} (law : FiniteOrbitLaw left right mean)
    {i : ι} (hi : i ∈ law.support) (hcard : law.support.card = 1) :
    orbitYuGap (reindexedSingleOrbitLaw law hi hcard) = orbitYuGap law := by
  classical
  have hsupport := support_eq_singleton_of_card_eq_one law hi hcard
  have hweight := weight_eq_one_of_support_card_eq_one law hi hcard
  have hmarginal : orbitMarginalEntropy (reindexedSingleOrbitLaw law hi hcard) =
      orbitMarginalEntropy law := by
    rw [orbitMarginalEntropy_eq_kernel_sum, orbitMarginalEntropy_eq_kernel_sum]
    have hold := law.sum_weight_eq_sum_support (orbitMarginalKernel left right)
    rw [hsupport] at hold
    simpa [reindexedSingleOrbitLaw, hweight] using hold.symm
  have hdependent : orbitDependentEntropy (reindexedSingleOrbitLaw law hi hcard) =
      orbitDependentEntropy law := by
    have hold := law.sum_weight_eq_sum_support
      (fun j ↦ dependentCost (left j) (right j))
    rw [hsupport] at hold
    simpa [orbitDependentEntropy, reindexedSingleOrbitLaw,
      hweight] using hold.symm
  have hindependent : orbitIndependentEntropy (reindexedSingleOrbitLaw law hi hcard) =
      orbitIndependentEntropy law := by
    rw [orbitIndependentEntropy_eq_kernel_sum, orbitIndependentEntropy_eq_kernel_sum]
    have hold :
        (∑ j, ∑ k, law.weight j * law.weight k * orbitCrossKernel left right j k) =
          ∑ j ∈ law.support, ∑ k ∈ law.support,
            law.weight j * law.weight k * orbitCrossKernel left right j k := by
      calc
        (∑ j, ∑ k, law.weight j * law.weight k * orbitCrossKernel left right j k) =
            ∑ j, law.weight j *
              (∑ k, law.weight k * orbitCrossKernel left right j k) := by
          apply sum_congr rfl
          intro j _
          rw [mul_sum]
          apply sum_congr rfl
          intro k _
          ring
        _ = ∑ j ∈ law.support, law.weight j *
            (∑ k, law.weight k * orbitCrossKernel left right j k) :=
          law.sum_weight_eq_sum_support _
        _ = ∑ j ∈ law.support, ∑ k ∈ law.support,
            law.weight j * law.weight k * orbitCrossKernel left right j k := by
          apply sum_congr rfl
          intro j _
          rw [law.sum_weight_eq_sum_support (orbitCrossKernel left right j)]
          rw [mul_sum]
          apply sum_congr rfl
          intro k _
          ring
    rw [hsupport] at hold
    simpa [reindexedSingleOrbitLaw, hweight] using hold.symm
  rw [orbitYuGap, hindependent, hmarginal, hdependent]
  rfl

/-- A two-support orbit law reindexed without changing either orbit. -/
noncomputable def reindexedPairOrbitLaw {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ} (law : FiniteOrbitLaw left right mean)
    {lower upper : ι} (hlowerUpper : lower ≠ upper)
    (hlower : lower ∈ law.support) (hupper : upper ∈ law.support)
    (hcard : law.support.card = 2) :
    FiniteOrbitLaw (reindexedPairCoordinate left lower upper)
      (reindexedPairCoordinate right lower upper) mean where
  weight := reindexedPairWeight law lower upper
  weight_nonneg choice := by
    cases choice
    · exact law.weight_nonneg lower
    · exact law.weight_nonneg upper
  weight_sum := by
    simpa [reindexedPairWeight, Fintype.sum_bool, add_comm] using
      law.two_support_weights_sum hlowerUpper hlower hupper hcard
  moment_sum := by
    simpa [reindexedPairWeight, reindexedPairCoordinate, orbitMean,
      Fintype.sum_bool, add_comm] using
      law.two_support_moment_sum hlowerUpper hlower hupper hcard

/-- Reindexing the two live orbits preserves all three entropy terms and hence the Yu gap. -/
theorem reindexedPairOrbitLaw_gap_eq {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ} (law : FiniteOrbitLaw left right mean)
    {lower upper : ι} (hlowerUpper : lower ≠ upper)
    (hlower : lower ∈ law.support) (hupper : upper ∈ law.support)
    (hcard : law.support.card = 2) :
    orbitYuGap
        (reindexedPairOrbitLaw law hlowerUpper hlower hupper hcard) = orbitYuGap law := by
  classical
  have hsupport := law.support_eq_pair_of_card_eq_two hlowerUpper hlower hupper hcard
  have hmarginal :
      orbitMarginalEntropy (reindexedPairOrbitLaw law hlowerUpper hlower hupper hcard) =
        orbitMarginalEntropy law := by
    rw [orbitMarginalEntropy_eq_kernel_sum, orbitMarginalEntropy_eq_kernel_sum]
    have hold := law.sum_weight_eq_sum_support (orbitMarginalKernel left right)
    rw [hsupport] at hold
    simpa [reindexedPairOrbitLaw, reindexedPairWeight, reindexedPairCoordinate,
      orbitMarginalKernel, Fintype.sum_bool, hlowerUpper, add_comm] using hold.symm
  have hdependent :
      orbitDependentEntropy (reindexedPairOrbitLaw law hlowerUpper hlower hupper hcard) =
        orbitDependentEntropy law := by
    have hold := law.sum_weight_eq_sum_support
      (fun i ↦ dependentCost (left i) (right i))
    rw [hsupport] at hold
    simpa [orbitDependentEntropy, reindexedPairOrbitLaw, reindexedPairWeight,
      reindexedPairCoordinate, Fintype.sum_bool, hlowerUpper, add_comm] using hold.symm
  have hindependent :
      orbitIndependentEntropy (reindexedPairOrbitLaw law hlowerUpper hlower hupper hcard) =
        orbitIndependentEntropy law := by
    rw [orbitIndependentEntropy_eq_kernel_sum, orbitIndependentEntropy_eq_kernel_sum]
    have hold :
        (∑ i, ∑ j, law.weight i * law.weight j * orbitCrossKernel left right i j) =
          ∑ i ∈ law.support, ∑ j ∈ law.support,
            law.weight i * law.weight j * orbitCrossKernel left right i j := by
      calc
        (∑ i, ∑ j, law.weight i * law.weight j * orbitCrossKernel left right i j) =
            ∑ i, law.weight i *
              (∑ j, law.weight j * orbitCrossKernel left right i j) := by
          apply sum_congr rfl
          intro i _
          rw [mul_sum]
          apply sum_congr rfl
          intro j _
          ring
        _ = ∑ i ∈ law.support, law.weight i *
            (∑ j, law.weight j * orbitCrossKernel left right i j) :=
          law.sum_weight_eq_sum_support _
        _ = ∑ i ∈ law.support, ∑ j ∈ law.support,
            law.weight i * law.weight j * orbitCrossKernel left right i j := by
          apply sum_congr rfl
          intro i _
          rw [law.sum_weight_eq_sum_support (orbitCrossKernel left right i)]
          rw [mul_sum]
          apply sum_congr rfl
          intro j _
          ring
    rw [hsupport] at hold
    simpa [reindexedPairOrbitLaw, reindexedPairWeight, reindexedPairCoordinate,
      orbitCrossKernel, Fintype.sum_bool, hlowerUpper, add_comm, join_comm] using hold.symm
  rw [orbitYuGap, hindependent, hmarginal, hdependent]
  rfl

/-- Lower coordinate of an orbit after canonical within-orbit sorting. -/
noncomputable def sortedOrbitLeft {ι : Type*} (left right : ι → ℝ) (i : ι) : ℝ :=
  min (left i) (right i)

/-- Upper coordinate of an orbit after canonical within-orbit sorting. -/
noncomputable def sortedOrbitRight {ι : Type*} (left right : ι → ℝ) (i : ι) : ℝ :=
  max (left i) (right i)

theorem sortedOrbitMean_eq {ι : Type*} (left right : ι → ℝ) (i : ι) :
    orbitMean (sortedOrbitLeft left right) (sortedOrbitRight left right) i =
      orbitMean left right i := by
  dsimp [orbitMean, sortedOrbitLeft, sortedOrbitRight]
  rw [min_add_max]

/-- Sorting every orbit leaves its weights and prescribed mean unchanged. -/
noncomputable def sortedOrbitLaw {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ} (law : FiniteOrbitLaw left right mean) :
    FiniteOrbitLaw (sortedOrbitLeft left right) (sortedOrbitRight left right) mean where
  weight := law.weight
  weight_nonneg := law.weight_nonneg
  weight_sum := law.weight_sum
  moment_sum := by
    simpa only [sortedOrbitMean_eq] using law.moment_sum

theorem orbitMarginalKernel_sorted {ι : Type*} (left right : ι → ℝ) (i : ι) :
    orbitMarginalKernel (sortedOrbitLeft left right) (sortedOrbitRight left right) i =
      orbitMarginalKernel left right i := by
  rcases le_total (left i) (right i) with hordered | hordered
  · simp [orbitMarginalKernel, sortedOrbitLeft, sortedOrbitRight, min_eq_left hordered,
      max_eq_right hordered]
  · simp [orbitMarginalKernel, sortedOrbitLeft, sortedOrbitRight, min_eq_right hordered,
      max_eq_left hordered, add_comm]

theorem orbitCrossKernel_sorted {ι : Type*} (left right : ι → ℝ) (i j : ι) :
    orbitCrossKernel (sortedOrbitLeft left right) (sortedOrbitRight left right) i j =
      orbitCrossKernel left right i j := by
  rcases le_total (left i) (right i) with hi | hi <;>
    rcases le_total (left j) (right j) with hj | hj
  all_goals
    simp [orbitCrossKernel, sortedOrbitLeft, sortedOrbitRight, min_eq_left,
      min_eq_right, max_eq_left, max_eq_right, hi, hj, join_comm]
  all_goals ring

theorem dependentCost_sorted {ι : Type*} (left right : ι → ℝ) (i : ι) :
    dependentCost (sortedOrbitLeft left right i) (sortedOrbitRight left right i) =
      dependentCost (left i) (right i) := by
  rcases le_total (left i) (right i) with hordered | hordered
  · simp [sortedOrbitLeft, sortedOrbitRight, min_eq_left hordered, max_eq_right hordered]
  · simp [sortedOrbitLeft, sortedOrbitRight, min_eq_right hordered, max_eq_left hordered,
      dependentCost_comm]

/-- Canonical within-orbit sorting preserves the complete Yu gap. -/
theorem sortedOrbitLaw_gap_eq {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ} (law : FiniteOrbitLaw left right mean) :
    orbitYuGap (sortedOrbitLaw law) = orbitYuGap law := by
  have hmarginal : orbitMarginalEntropy (sortedOrbitLaw law) = orbitMarginalEntropy law := by
    rw [orbitMarginalEntropy_eq_kernel_sum, orbitMarginalEntropy_eq_kernel_sum]
    apply sum_congr rfl
    intro i _
    rw [orbitMarginalKernel_sorted]
    rfl
  have hindependent :
      orbitIndependentEntropy (sortedOrbitLaw law) = orbitIndependentEntropy law := by
    rw [orbitIndependentEntropy_eq_kernel_sum, orbitIndependentEntropy_eq_kernel_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [orbitCrossKernel_sorted]
    rfl
  have hdependent : orbitDependentEntropy (sortedOrbitLaw law) = orbitDependentEntropy law := by
    dsimp [orbitDependentEntropy, sortedOrbitLaw]
    apply sum_congr rfl
    intro i _
    rw [dependentCost_sorted]
  rw [orbitYuGap, hindependent, hmarginal, hdependent]
  rfl

/-- Orbit laws with identical coordinate functions and weights have identical Yu gaps, even
when presented through propositionally equal coordinate types. -/
theorem orbitYuGap_congr {ι : Type*} [Fintype ι]
    {left₁ right₁ left₂ right₂ : ι → ℝ} {mean : ℝ}
    (law₁ : FiniteOrbitLaw left₁ right₁ mean)
    (law₂ : FiniteOrbitLaw left₂ right₂ mean)
    (hleft : left₁ = left₂) (hright : right₁ = right₂)
    (hweight : law₁.weight = law₂.weight) :
    orbitYuGap law₁ = orbitYuGap law₂ := by
  subst left₂
  subst right₂
  have hlaw : law₁ = law₂ := FiniteMomentLaw.ext hweight
  subst law₂
  rfl

/-- A unit-indexed presentation with the stated symmetric coordinates is the canonical single
low-orbit law. -/
theorem singleLowOrbitLaw_gap_eq_of_coordinates
    {left right : Unit → ℝ} {a d : ℝ}
    (law : FiniteOrbitLaw left right a)
    (hleft : left () = a - d) (hright : right () = a + d)
    (hweight : law.weight () = 1) :
    orbitYuGap (singleLowOrbitLaw a d) = orbitYuGap law := by
  apply orbitYuGap_congr (singleLowOrbitLaw a d) law
  · funext z
    cases z
    simpa using hleft.symm
  · funext z
    cases z
    simpa using hright.symm
  · funext z
    cases z
    simpa [singleLowOrbitLaw] using hweight.symm

/-- A Boolean two-orbit presentation with the stated coordinates and exact masses is the
canonical low–low law used by the contraction theorem. -/
theorem twoLowOrbitLaw_gap_eq_of_coordinates
    {left right : Bool → ℝ} {a d target b e : ℝ}
    (law : FiniteOrbitLaw left right target)
    (haTarget : a ≤ target) (htargetB : target ≤ b) (hab : a < b)
    (hleftLower : left false = a - d) (hrightLower : right false = a + d)
    (hleftUpper : left true = b - e) (hrightUpper : right true = b + e)
    (hlowerWeight : law.weight false = lowerOrbitWeight a target b)
    (hupperWeight : law.weight true = upperOrbitWeight a target b) :
    orbitYuGap (twoLowOrbitLaw a d target b e haTarget htargetB hab) = orbitYuGap law := by
  apply orbitYuGap_congr (twoLowOrbitLaw a d target b e haTarget htargetB hab) law
  · funext choice
    cases choice
    · simpa [twoLowOrbitLeft] using hleftLower.symm
    · simpa [twoLowOrbitLeft] using hleftUpper.symm
  · funext choice
    cases choice
    · simpa [twoLowOrbitRight] using hrightLower.symm
    · simpa [twoLowOrbitRight] using hrightUpper.symm
  · funext choice
    cases choice
    · simpa [twoLowOrbitLaw, twoOrbitWeight] using hlowerWeight.symm
    · simpa [twoLowOrbitLaw, twoOrbitWeight] using hupperWeight.symm

/-- A Boolean presentation with one low orbit and one `(q,1)` orbit is the canonical endpoint
law used by the contraction theorem. -/
theorem lowEndpointOrbitLaw_gap_eq_of_coordinates
    {left right : Bool → ℝ} {a d target q : ℝ}
    (law : FiniteOrbitLaw left right target)
    (haTarget : a ≤ target) (htargetEndpoint : target ≤ endpointOrbitMean q)
    (haEndpoint : a < endpointOrbitMean q)
    (hleftLower : left false = a - d) (hrightLower : right false = a + d)
    (hleftUpper : left true = q) (hrightUpper : right true = 1)
    (hlowerWeight : law.weight false = lowerOrbitWeight a target (endpointOrbitMean q))
    (hupperWeight : law.weight true = upperOrbitWeight a target (endpointOrbitMean q)) :
    orbitYuGap
        (lowEndpointOrbitLaw a d target q haTarget htargetEndpoint haEndpoint) =
      orbitYuGap law := by
  apply orbitYuGap_congr
    (lowEndpointOrbitLaw a d target q haTarget htargetEndpoint haEndpoint) law
  · funext choice
    cases choice
    · simpa [lowEndpointOrbitLeft] using hleftLower.symm
    · simpa [lowEndpointOrbitLeft] using hleftUpper.symm
  · funext choice
    cases choice
    · simpa [lowEndpointOrbitRight] using hrightLower.symm
    · simpa [lowEndpointOrbitRight] using hrightUpper.symm
  · funext choice
    cases choice
    · simpa [lowEndpointOrbitLaw, twoOrbitWeight] using hlowerWeight.symm
    · simpa [lowEndpointOrbitLaw, twoOrbitWeight] using hupperWeight.symm

end Frankl
