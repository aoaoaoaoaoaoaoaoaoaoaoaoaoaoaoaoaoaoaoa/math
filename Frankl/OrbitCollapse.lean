import Frankl.OrbitMeanLift

namespace Frankl

open Finset Real Set

/-- The lower/upper orbit masses, encoded respectively by `false` and `true`. -/
noncomputable def twoOrbitWeight (a target b : ℝ) : Bool → ℝ
  | false => lowerOrbitWeight a target b
  | true => upperOrbitWeight a target b

/-- Left representatives of two symmetric low orbits. -/
noncomputable def twoLowOrbitLeft (a d b e : ℝ) : Bool → ℝ
  | false => a - d
  | true => b - e

/-- Right representatives of two symmetric low orbits. -/
noncomputable def twoLowOrbitRight (a d b e : ℝ) : Bool → ℝ
  | false => a + d
  | true => b + e

/-- The exact-target law on a lower orbit `(a-d,a+d)` and an upper orbit `(b-e,b+e)`. -/
noncomputable def twoLowOrbitLaw (a d target b e : ℝ)
    (haTarget : a ≤ target) (htargetB : target ≤ b) (hab : a < b) :
    FiniteOrbitLaw (twoLowOrbitLeft a d b e) (twoLowOrbitRight a d b e) target where
  weight := twoOrbitWeight a target b
  weight_nonneg z := by
    cases z
    · exact lowerOrbitWeight_nonneg htargetB hab
    · exact upperOrbitWeight_nonneg haTarget hab
  weight_sum := by
    simpa [twoOrbitWeight, Fintype.sum_bool, add_comm] using
      (orbitWeights_sum (a := a) (t := target) (b := b) hab)
  moment_sum := by
    simpa [twoOrbitWeight, twoLowOrbitLeft, twoLowOrbitRight, orbitMean,
      Fintype.sum_bool, add_comm] using
      (orbitWeights_mean (a := a) (t := target) (b := b) hab)

/-- The mean of the symmetric endpoint orbit `(q,1)`. -/
noncomputable def endpointOrbitMean (q : ℝ) : ℝ := (q + 1) / 2

/-- Left representatives of a low orbit and an endpoint orbit. -/
noncomputable def lowEndpointOrbitLeft (a d q : ℝ) : Bool → ℝ
  | false => a - d
  | true => q

/-- Right representatives of a low orbit and an endpoint orbit. -/
noncomputable def lowEndpointOrbitRight (a d : ℝ) : Bool → ℝ
  | false => a + d
  | true => 1

/-- The exact-target law on a low orbit and the endpoint orbit `(q,1)`. -/
noncomputable def lowEndpointOrbitLaw (a d target q : ℝ)
    (haTarget : a ≤ target) (htargetEndpoint : target ≤ endpointOrbitMean q)
    (haEndpoint : a < endpointOrbitMean q) :
    FiniteOrbitLaw (lowEndpointOrbitLeft a d q) (lowEndpointOrbitRight a d) target where
  weight := twoOrbitWeight a target (endpointOrbitMean q)
  weight_nonneg z := by
    cases z
    · exact lowerOrbitWeight_nonneg htargetEndpoint haEndpoint
    · exact upperOrbitWeight_nonneg haTarget haEndpoint
  weight_sum := by
    simpa [twoOrbitWeight, Fintype.sum_bool, add_comm] using
      (orbitWeights_sum (a := a) (t := target) (b := endpointOrbitMean q) haEndpoint)
  moment_sum := by
    simpa [twoOrbitWeight, lowEndpointOrbitLeft, lowEndpointOrbitRight, orbitMean,
      endpointOrbitMean, Fintype.sum_bool, add_comm] using
      (orbitWeights_mean (a := a) (t := target) (b := endpointOrbitMean q) haEndpoint)

/-- The unit-mass law on one symmetric orbit of mean `a`. -/
noncomputable def singleLowOrbitLaw (a d : ℝ) :
    FiniteOrbitLaw (Function.const Unit (a - d)) (Function.const Unit (a + d)) a where
  weight _ := 1
  weight_nonneg _ := by norm_num
  weight_sum := by simp
  moment_sum := by
    simp [orbitMean]

/-- Yu's dependent cost of a symmetric orbit in the low square depends only on its mean. -/
theorem dependentCost_symmetric_low_eq_mean {a d : ℝ}
    (hupper : a + d ≤ 1 / 2) (hd : 0 ≤ d) :
    dependentCost (a - d) (a + d) = dependentCost a a := by
  have hordered : a - d ≤ a + d := by linarith
  have haHalf : a ≤ 1 / 2 := by linarith
  rw [dependentCost, dependentCost, dependentParameter, dependentParameter,
    max_eq_right hordered, max_eq_right hupper, max_self, max_eq_right haHalf]
  congr 2
  ring

theorem singleLowOrbit_marginal_difference (a d : ℝ) :
    orbitMarginalEntropy (singleLowOrbitLaw a 0)
        - orbitMarginalEntropy (singleLowOrbitLaw a d) =
      orbitDeficit binEntropy a d := by
  simp [orbitMarginalEntropy, finiteExpectation, orbitMarginalWeight,
    orbitMarginalPoint, singleLowOrbitLaw,
    orbitDeficit, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

theorem singleLowOrbit_independent_difference (a d : ℝ) :
    orbitIndependentEntropy (singleLowOrbitLaw a 0)
        - orbitIndependentEntropy (singleLowOrbitLaw a d) = selfPairDeficit a d := by
  simp [orbitIndependentEntropy, finiteJoinEntropy, orbitMarginalWeight,
    orbitMarginalPoint, singleLowOrbitLaw,
    selfPairDeficit, Fintype.sum_prod_type, Fintype.sum_bool, join_comm]
  ring

theorem singleLowOrbit_dependent_eq {a d : ℝ}
    (haUpper : a + d ≤ 1 / 2) (hd : 0 ≤ d) :
    orbitDependentEntropy (singleLowOrbitLaw a 0) =
      orbitDependentEntropy (singleLowOrbitLaw a d) := by
  have hcost := dependentCost_symmetric_low_eq_mean haUpper hd
  simpa [orbitDependentEntropy, singleLowOrbitLaw]
    using hcost.symm

/-- Contracting the lower orbit raises marginal entropy by its weighted Jensen deficit. -/
theorem twoLowOrbit_lower_marginal_difference {a d target b e : ℝ}
    (haTarget : a ≤ target) (htargetB : target ≤ b) (hab : a < b) :
    orbitMarginalEntropy (twoLowOrbitLaw a 0 target b e haTarget htargetB hab)
        - orbitMarginalEntropy (twoLowOrbitLaw a d target b e haTarget htargetB hab) =
      lowerOrbitWeight a target b * orbitDeficit binEntropy a d := by
  classical
  simp [orbitMarginalEntropy, finiteExpectation, orbitMarginalWeight,
    orbitMarginalPoint, twoLowOrbitLaw, twoOrbitWeight, twoLowOrbitLeft,
    twoLowOrbitRight, orbitDeficit, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

/-- Contracting the upper orbit after the lower one raises marginal entropy by its weighted
Jensen deficit. -/
theorem twoLowOrbit_upper_marginal_difference {a target b e : ℝ}
    (haTarget : a ≤ target) (htargetB : target ≤ b) (hab : a < b) :
    orbitMarginalEntropy (twoLowOrbitLaw a 0 target b 0 haTarget htargetB hab)
        - orbitMarginalEntropy (twoLowOrbitLaw a 0 target b e haTarget htargetB hab) =
      upperOrbitWeight a target b * orbitDeficit binEntropy b e := by
  classical
  simp [orbitMarginalEntropy, finiteExpectation, orbitMarginalWeight,
    orbitMarginalPoint, twoLowOrbitLaw, twoOrbitWeight, twoLowOrbitLeft,
    twoLowOrbitRight, orbitDeficit, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

/-- Exact independent-entropy cost of contracting the lower of two low orbits. -/
theorem twoLowOrbit_lower_independent_difference {a d target b e : ℝ}
    (haTarget : a ≤ target) (htargetB : target ≤ b) (hab : a < b) :
    orbitIndependentEntropy (twoLowOrbitLaw a 0 target b e haTarget htargetB hab)
        - orbitIndependentEntropy (twoLowOrbitLaw a d target b e haTarget htargetB hab) =
      lowerOrbitWeight a target b ^ 2 * selfPairDeficit a d
        + lowerOrbitWeight a target b * upperOrbitWeight a target b
          * (orbitDeficit (fun x ↦ binEntropy (join x (b - e))) a d
            + orbitDeficit (fun x ↦ binEntropy (join x (b + e))) a d) := by
  classical
  simp [orbitIndependentEntropy, finiteJoinEntropy, orbitMarginalWeight,
    orbitMarginalPoint, twoLowOrbitLaw, twoOrbitWeight, twoLowOrbitLeft,
    twoLowOrbitRight, selfPairDeficit, orbitDeficit, Fintype.sum_prod_type,
    Fintype.sum_bool, join_comm]
  ring

/-- Exact independent-entropy cost of contracting the upper orbit after the lower orbit. -/
theorem twoLowOrbit_upper_independent_difference {a target b e : ℝ}
    (haTarget : a ≤ target) (htargetB : target ≤ b) (hab : a < b) :
    orbitIndependentEntropy (twoLowOrbitLaw a 0 target b 0 haTarget htargetB hab)
        - orbitIndependentEntropy (twoLowOrbitLaw a 0 target b e haTarget htargetB hab) =
      upperOrbitWeight a target b ^ 2 * selfPairDeficit b e
        + 2 * lowerOrbitWeight a target b * upperOrbitWeight a target b
          * orbitDeficit (fun x ↦ binEntropy (join x a)) b e := by
  classical
  simp [orbitIndependentEntropy, finiteJoinEntropy, orbitMarginalWeight,
    orbitMarginalPoint, twoLowOrbitLaw, twoOrbitWeight, twoLowOrbitLeft,
    twoLowOrbitRight, selfPairDeficit, orbitDeficit, Fintype.sum_prod_type,
    Fintype.sum_bool, join_comm]
  ring

/-- Contracting the lower low orbit preserves Yu's dependent entropy term. -/
theorem twoLowOrbit_lower_dependent_eq {a d target b e : ℝ}
    (haTarget : a ≤ target) (htargetB : target ≤ b) (hab : a < b)
    (haUpper : a + d ≤ 1 / 2) (hd : 0 ≤ d) :
    orbitDependentEntropy (twoLowOrbitLaw a 0 target b e haTarget htargetB hab) =
      orbitDependentEntropy (twoLowOrbitLaw a d target b e haTarget htargetB hab) := by
  classical
  have hcost := dependentCost_symmetric_low_eq_mean haUpper hd
  simp [orbitDependentEntropy, twoLowOrbitLaw, twoOrbitWeight, twoLowOrbitLeft,
    twoLowOrbitRight, Fintype.sum_bool, hcost]

/-- Contracting the upper low orbit preserves Yu's dependent entropy term. -/
theorem twoLowOrbit_upper_dependent_eq {a target b e : ℝ}
    (haTarget : a ≤ target) (htargetB : target ≤ b) (hab : a < b)
    (hbUpper : b + e ≤ 1 / 2) (he : 0 ≤ e) :
    orbitDependentEntropy (twoLowOrbitLaw a 0 target b 0 haTarget htargetB hab) =
      orbitDependentEntropy (twoLowOrbitLaw a 0 target b e haTarget htargetB hab) := by
  classical
  have hcost := dependentCost_symmetric_low_eq_mean hbUpper he
  simp [orbitDependentEntropy, twoLowOrbitLaw, twoOrbitWeight, twoLowOrbitLeft,
    twoLowOrbitRight, Fintype.sum_bool, hcost]

/-- Contracting the low orbit against `(q,1)` raises marginal entropy by its weighted Jensen
deficit. -/
theorem lowEndpointOrbit_marginal_difference {a d target q : ℝ}
    (haTarget : a ≤ target) (htargetEndpoint : target ≤ endpointOrbitMean q)
    (haEndpoint : a < endpointOrbitMean q) :
    orbitMarginalEntropy
        (lowEndpointOrbitLaw a 0 target q haTarget htargetEndpoint haEndpoint)
        - orbitMarginalEntropy
          (lowEndpointOrbitLaw a d target q haTarget htargetEndpoint haEndpoint) =
      lowerOrbitWeight a target (endpointOrbitMean q) * orbitDeficit binEntropy a d := by
  classical
  simp [orbitMarginalEntropy, finiteExpectation, orbitMarginalWeight,
    orbitMarginalPoint, lowEndpointOrbitLaw, twoOrbitWeight, lowEndpointOrbitLeft,
    lowEndpointOrbitRight, orbitDeficit, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

/-- Exact independent-entropy cost of contracting a low orbit against `(q,1)`. -/
theorem lowEndpointOrbit_independent_difference {a d target q : ℝ}
    (haTarget : a ≤ target) (htargetEndpoint : target ≤ endpointOrbitMean q)
    (haEndpoint : a < endpointOrbitMean q) :
    orbitIndependentEntropy
        (lowEndpointOrbitLaw a 0 target q haTarget htargetEndpoint haEndpoint)
        - orbitIndependentEntropy
          (lowEndpointOrbitLaw a d target q haTarget htargetEndpoint haEndpoint) =
      lowerOrbitWeight a target (endpointOrbitMean q) ^ 2 * selfPairDeficit a d
        + lowerOrbitWeight a target (endpointOrbitMean q)
          * upperOrbitWeight a target (endpointOrbitMean q)
          * (orbitDeficit (fun x ↦ binEntropy (join x q)) a d
            + orbitDeficit (fun x ↦ binEntropy (join x 1)) a d) := by
  classical
  simp [orbitIndependentEntropy, finiteJoinEntropy, orbitMarginalWeight,
    orbitMarginalPoint, lowEndpointOrbitLaw, twoOrbitWeight, lowEndpointOrbitLeft,
    lowEndpointOrbitRight, selfPairDeficit, orbitDeficit, Fintype.sum_prod_type,
    Fintype.sum_bool, join_comm]
  ring

/-- Contracting the low orbit against `(q,1)` preserves Yu's dependent term. -/
theorem lowEndpointOrbit_dependent_eq {a d target q : ℝ}
    (haTarget : a ≤ target) (htargetEndpoint : target ≤ endpointOrbitMean q)
    (haEndpoint : a < endpointOrbitMean q) (haUpper : a + d ≤ 1 / 2)
    (hd : 0 ≤ d) :
    orbitDependentEntropy
        (lowEndpointOrbitLaw a 0 target q haTarget htargetEndpoint haEndpoint) =
      orbitDependentEntropy
        (lowEndpointOrbitLaw a d target q haTarget htargetEndpoint haEndpoint) := by
  classical
  have hcost := dependentCost_symmetric_low_eq_mean haUpper hd
  simp [orbitDependentEntropy, lowEndpointOrbitLaw, twoOrbitWeight,
    lowEndpointOrbitLeft, lowEndpointOrbitRight, Fintype.sum_bool, hcost]

/-- If a contraction raises independent entropy by no more than marginal entropy, it cannot
raise the strict Yu gap while the dependent term is fixed. -/
theorem yuGap_le_of_join_difference_le_marginal {oldJoin newJoin oldMarginal newMarginal
    dependent : ℝ}
    (hdifference : newJoin - oldJoin ≤ newMarginal - oldMarginal)
    (hmarginal : 0 ≤ newMarginal - oldMarginal) :
    yuGap newJoin newMarginal dependent ≤ yuGap oldJoin oldMarginal dependent := by
  norm_num [yuGap, dependentShare, entropySlack] at *
  linarith

/-- A single symmetric low orbit may collapse to its diagonal mean without increasing the
strict Yu gap. -/
theorem singleLowOrbit_collapse_le {a d : ℝ}
    (haLower : 0 ≤ a - d) (haUpper : a + d ≤ 1 / 2) (hd : 0 ≤ d) :
    orbitYuGap (singleLowOrbitLaw a 0) ≤ orbitYuGap (singleLowOrbitLaw a d) := by
  have hjoin :
      orbitIndependentEntropy (singleLowOrbitLaw a 0)
          - orbitIndependentEntropy (singleLowOrbitLaw a d) ≤
        orbitMarginalEntropy (singleLowOrbitLaw a 0)
          - orbitMarginalEntropy (singleLowOrbitLaw a d) := by
    rw [singleLowOrbit_independent_difference, singleLowOrbit_marginal_difference]
    exact selfPairDeficit_le_orbitDeficit haLower haUpper hd
  have hmarginal :
      0 ≤ orbitMarginalEntropy (singleLowOrbitLaw a 0)
        - orbitMarginalEntropy (singleLowOrbitLaw a d) := by
    rw [singleLowOrbit_marginal_difference]
    exact orbitDeficit_nonneg haLower (haUpper.trans (by norm_num)) hd
  rw [orbitYuGap, orbitYuGap, singleLowOrbit_dependent_eq haUpper hd]
  exact yuGap_le_of_join_difference_le_marginal hjoin hmarginal

/-- The scalar lower-orbit estimate acts on the actual two-orbit Yu functional. -/
theorem twoLowOrbit_lower_collapse_le {a d target b e : ℝ}
    (haLower : 0 ≤ a - d) (haUpper : a + d ≤ 1 / 2) (hd : 0 ≤ d)
    (hbLower : 0 ≤ b - e) (hbUpper : b + e ≤ 1 / 2) (he : 0 ≤ e)
    (haTarget : a ≤ target) (htargetB : target ≤ b) (hab : a < b)
    (hbThreeEighths : 3 / 8 ≤ b) :
    orbitYuGap (twoLowOrbitLaw a 0 target b e haTarget htargetB hab) ≤
      orbitYuGap (twoLowOrbitLaw a d target b e haTarget htargetB hab) := by
  let lowerWeight := lowerOrbitWeight a target b
  let upperWeight := upperOrbitWeight a target b
  have hlowerWeight : 0 ≤ lowerWeight := lowerOrbitWeight_nonneg htargetB hab
  have hupperWeight : 0 ≤ upperWeight := upperOrbitWeight_nonneg haTarget hab
  have hweightSum : lowerWeight + upperWeight = 1 := orbitWeights_sum hab
  have hscalar := lowerLowOrbitDeficit_le_marginal haLower haUpper hd
    hbLower hbUpper he hlowerWeight hupperWeight hweightSum hbThreeEighths
  have hjoin :
      orbitIndependentEntropy (twoLowOrbitLaw a 0 target b e haTarget htargetB hab)
          - orbitIndependentEntropy (twoLowOrbitLaw a d target b e haTarget htargetB hab) ≤
        orbitMarginalEntropy (twoLowOrbitLaw a 0 target b e haTarget htargetB hab)
          - orbitMarginalEntropy (twoLowOrbitLaw a d target b e haTarget htargetB hab) := by
    rw [twoLowOrbit_lower_independent_difference,
      twoLowOrbit_lower_marginal_difference]
    exact hscalar
  have hmarginal :
      0 ≤ orbitMarginalEntropy (twoLowOrbitLaw a 0 target b e haTarget htargetB hab)
        - orbitMarginalEntropy (twoLowOrbitLaw a d target b e haTarget htargetB hab) := by
    rw [twoLowOrbit_lower_marginal_difference]
    exact mul_nonneg hlowerWeight (orbitDeficit_nonneg haLower
      (haUpper.trans (by norm_num)) hd)
  rw [orbitYuGap, orbitYuGap,
    twoLowOrbit_lower_dependent_eq haTarget htargetB hab haUpper hd]
  exact yuGap_le_of_join_difference_le_marginal hjoin hmarginal

/-- The scalar upper-orbit estimate acts on the actual two-orbit Yu functional after the lower
orbit has collapsed. -/
theorem twoLowOrbit_upper_collapse_le {a target b e : ℝ}
    (haZero : 0 ≤ a) (haHalf : a ≤ 1 / 2)
    (hbLower : 0 ≤ b - e) (hbUpper : b + e ≤ 1 / 2) (he : 0 ≤ e)
    (haTarget : a ≤ target) (htargetB : target ≤ b) (hab : a < b)
    (hfactor :
      2 * upperOrbitWeight a target b * (1 - 4 * b / 3)
          + 2 * lowerOrbitWeight a target b * ((1 - a) / (1 + a)) ≤ 1) :
    orbitYuGap (twoLowOrbitLaw a 0 target b 0 haTarget htargetB hab) ≤
      orbitYuGap (twoLowOrbitLaw a 0 target b e haTarget htargetB hab) := by
  let lowerWeight := lowerOrbitWeight a target b
  let upperWeight := upperOrbitWeight a target b
  have hlowerWeight : 0 ≤ lowerWeight := lowerOrbitWeight_nonneg htargetB hab
  have hupperWeight : 0 ≤ upperWeight := upperOrbitWeight_nonneg haTarget hab
  have hscalar := upperLowOrbitDeficit_le_marginal haZero haHalf
    hbLower hbUpper he hlowerWeight hupperWeight hfactor
  have hjoin :
      orbitIndependentEntropy (twoLowOrbitLaw a 0 target b 0 haTarget htargetB hab)
          - orbitIndependentEntropy (twoLowOrbitLaw a 0 target b e haTarget htargetB hab) ≤
        orbitMarginalEntropy (twoLowOrbitLaw a 0 target b 0 haTarget htargetB hab)
          - orbitMarginalEntropy (twoLowOrbitLaw a 0 target b e haTarget htargetB hab) := by
    rw [twoLowOrbit_upper_independent_difference,
      twoLowOrbit_upper_marginal_difference]
    exact hscalar
  have hmarginal :
      0 ≤ orbitMarginalEntropy (twoLowOrbitLaw a 0 target b 0 haTarget htargetB hab)
        - orbitMarginalEntropy (twoLowOrbitLaw a 0 target b e haTarget htargetB hab) := by
    rw [twoLowOrbit_upper_marginal_difference]
    exact mul_nonneg hupperWeight (orbitDeficit_nonneg hbLower
      (hbUpper.trans (by norm_num)) he)
  rw [orbitYuGap, orbitYuGap,
    twoLowOrbit_upper_dependent_eq haTarget htargetB hab hbUpper he]
  exact yuGap_le_of_join_difference_le_marginal hjoin hmarginal

/-- At the candidate target, both low orbits of an exact-mean extreme may be collapsed to their
diagonal means without increasing the strict Yu gap. -/
theorem twoLowOrbit_target_collapse_le {a d b e : ℝ}
    (haLower : 0 ≤ a - d) (haUpper : a + d ≤ 1 / 2) (hd : 0 ≤ d)
    (hbLower : 0 ≤ b - e) (hbUpper : b + e ≤ 1 / 2) (he : 0 ≤ e)
    (haTarget : a ≤ abundanceTarget) (htargetB : abundanceTarget ≤ b) (hab : a < b) :
    orbitYuGap
        (twoLowOrbitLaw a 0 abundanceTarget b 0 haTarget htargetB hab) ≤
      orbitYuGap
        (twoLowOrbitLaw a d abundanceTarget b e haTarget htargetB hab) := by
  have haZero : 0 ≤ a := by linarith
  have haHalf : a ≤ 1 / 2 := haTarget.trans abundanceTarget_lt_half.le
  have hbHalf : b ≤ 1 / 2 := by linarith
  have hlower := twoLowOrbit_lower_collapse_le haLower haUpper hd hbLower hbUpper he
    haTarget htargetB hab (abundanceTarget_gt_three_eighths.le.trans htargetB)
  have hfactor :
      2 * upperOrbitWeight a abundanceTarget b * (1 - 4 * b / 3)
          + 2 * lowerOrbitWeight a abundanceTarget b * ((1 - a) / (1 + a)) ≤ 1 :=
    (targetUpperContractionFactor_lt_one haZero htargetB hbHalf hab).le
  have hupper := twoLowOrbit_upper_collapse_le haZero haHalf hbLower hbUpper he
    haTarget htargetB hab hfactor
  exact hupper.trans hlower

/-- An exact-mean extreme supported on a low orbit and `(q,1)` may collapse its low orbit to
the diagonal without increasing the strict Yu gap. -/
theorem lowEndpointOrbit_collapse_le {a d target q : ℝ}
    (haLower : 0 ≤ a - d) (haUpper : a + d ≤ 1 / 2) (hd : 0 ≤ d)
    (hqZero : 0 ≤ q) (hqOne : q ≤ 1)
    (haTarget : a ≤ target) (htargetEndpoint : target ≤ endpointOrbitMean q)
    (haEndpoint : a < endpointOrbitMean q) :
    orbitYuGap
        (lowEndpointOrbitLaw a 0 target q haTarget htargetEndpoint haEndpoint) ≤
      orbitYuGap
        (lowEndpointOrbitLaw a d target q haTarget htargetEndpoint haEndpoint) := by
  let lowerWeight := lowerOrbitWeight a target (endpointOrbitMean q)
  let upperWeight := upperOrbitWeight a target (endpointOrbitMean q)
  have hlowerWeight : 0 ≤ lowerWeight :=
    lowerOrbitWeight_nonneg htargetEndpoint haEndpoint
  have hupperWeight : 0 ≤ upperWeight := upperOrbitWeight_nonneg haTarget haEndpoint
  have hweightSum : lowerWeight + upperWeight = 1 := orbitWeights_sum haEndpoint
  have hscalar := lowerEndpointOrbitDeficit_le_marginal haLower haUpper hd hqZero hqOne
    hlowerWeight hupperWeight hweightSum
  have hjoin :
      orbitIndependentEntropy
          (lowEndpointOrbitLaw a 0 target q haTarget htargetEndpoint haEndpoint)
          - orbitIndependentEntropy
            (lowEndpointOrbitLaw a d target q haTarget htargetEndpoint haEndpoint) ≤
        orbitMarginalEntropy
          (lowEndpointOrbitLaw a 0 target q haTarget htargetEndpoint haEndpoint)
          - orbitMarginalEntropy
            (lowEndpointOrbitLaw a d target q haTarget htargetEndpoint haEndpoint) := by
    rw [lowEndpointOrbit_independent_difference,
      lowEndpointOrbit_marginal_difference]
    exact hscalar
  have hmarginal :
      0 ≤ orbitMarginalEntropy
          (lowEndpointOrbitLaw a 0 target q haTarget htargetEndpoint haEndpoint)
        - orbitMarginalEntropy
          (lowEndpointOrbitLaw a d target q haTarget htargetEndpoint haEndpoint) := by
    rw [lowEndpointOrbit_marginal_difference]
    exact mul_nonneg hlowerWeight (orbitDeficit_nonneg haLower
      (haUpper.trans (by norm_num)) hd)
  rw [orbitYuGap, orbitYuGap,
    lowEndpointOrbit_dependent_eq haTarget htargetEndpoint haEndpoint haUpper hd]
  exact yuGap_le_of_join_difference_le_marginal hjoin hmarginal

end Frankl
