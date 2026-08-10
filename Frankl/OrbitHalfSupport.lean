import Frankl.OrbitCollapse

namespace Frankl

open Finset Real Set

/-- The two-point mean-preserving half-support kernel. `false` is the low output and `true` is
the endpoint output; points already at or below one half are left fixed. -/
noncomputable def halfSupportKernelPoint (x : ℝ) : Bool → ℝ
  | false => if x ≤ 1 / 2 then x else 1 / 2
  | true => if x ≤ 1 / 2 then x else 1

/-- Output masses of the mean-preserving half-support kernel. -/
noncomputable def halfSupportKernelWeight (x : ℝ) : Bool → ℝ
  | false => if x ≤ 1 / 2 then 1 else 2 * (1 - x)
  | true => if x ≤ 1 / 2 then 0 else 2 * x - 1

theorem halfSupportKernelWeight_nonneg {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∀ choice, 0 ≤ halfSupportKernelWeight x choice := by
  intro choice
  cases choice <;> simp only [halfSupportKernelWeight] <;> split_ifs
  · norm_num
  · linarith [hx.2]
  · norm_num
  · linarith

theorem halfSupportKernelWeight_sum (x : ℝ) :
    ∑ choice, halfSupportKernelWeight x choice = 1 := by
  rw [Fintype.sum_bool]
  simp only [halfSupportKernelWeight]
  split_ifs <;> ring

theorem halfSupportKernel_mean (x : ℝ) :
    ∑ choice, halfSupportKernelWeight x choice * halfSupportKernelPoint x choice = x := by
  rw [Fintype.sum_bool]
  simp only [halfSupportKernelWeight, halfSupportKernelPoint]
  split_ifs <;> ring

theorem halfSupportKernelPoint_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∀ choice, halfSupportKernelPoint x choice ∈ Icc (0 : ℝ) 1 := by
  intro choice
  cases choice <;> simp only [halfSupportKernelPoint] <;> split_ifs
  · exact hx
  · constructor <;> norm_num
  · exact hx
  · constructor <;> norm_num

theorem halfSupportKernelPoint_range (x : ℝ) (choice : Bool) :
    halfSupportKernelPoint x choice ≤ 1 / 2 ∨ halfSupportKernelPoint x choice = 1 := by
  cases choice <;> simp only [halfSupportKernelPoint] <;> split_ifs with hxHalf
  · exact Or.inl hxHalf
  · exact Or.inl (by norm_num)
  · exact Or.inl hxHalf
  · exact Or.inr rfl

/-- Every live output of the kernel lies in `[0,1/2] ∪ {1}`. -/
theorem halfSupportKernel_live_range {x : ℝ} (choice : Bool)
    (hlive : 0 < halfSupportKernelWeight x choice) :
    halfSupportKernelPoint x choice ≤ 1 / 2 ∨ halfSupportKernelPoint x choice = 1 := by
  cases choice
  · simp only [halfSupportKernelPoint]
    split_ifs with hxHalf
    · exact Or.inl hxHalf
    · exact Or.inl (by norm_num)
  · simp only [halfSupportKernelPoint]
    split_ifs with hxHalf
    · have hfalse : False := by
        simp only [halfSupportKernelWeight] at hlive
        split_ifs at hlive <;> linarith
      exact hfalse.elim
    · exact Or.inr rfl

/-- Applying the half-support kernel to one coordinate cannot increase Yu's dependent cost. -/
theorem halfSupportKernel_dependentCost_le {x r : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1) :
    (∑ choice, halfSupportKernelWeight x choice
      * dependentCost (halfSupportKernelPoint x choice) r) ≤ dependentCost x r := by
  rw [Fintype.sum_bool]
  simp only [halfSupportKernelWeight, halfSupportKernelPoint]
  split_ifs with hxHalf
  · simpa only [zero_mul, one_mul, zero_add] using le_refl (dependentCost x r)
  · have hzZero : 0 ≤ 1 - x := by linarith [hx.2]
    have hzHalf : 1 - x ≤ 1 / 2 := by linarith
    have hcost := halfSupportDependentCost_le hzZero hzHalf hr.1 hr.2
    convert hcost using 1 <;> ring_nf

/-- Applying the half-support kernel independently to both coordinates cannot increase Yu's
dependent cost. -/
theorem halfSupportKernel_pair_dependentCost_le {p q : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) :
    (∑ pChoice, ∑ qChoice,
      halfSupportKernelWeight p pChoice * halfSupportKernelWeight q qChoice
        * dependentCost (halfSupportKernelPoint p pChoice)
          (halfSupportKernelPoint q qChoice)) ≤ dependentCost p q := by
  have hinner : ∀ pChoice,
      (∑ qChoice, halfSupportKernelWeight q qChoice
        * dependentCost (halfSupportKernelPoint p pChoice)
          (halfSupportKernelPoint q qChoice)) ≤
        dependentCost (halfSupportKernelPoint p pChoice) q := by
    intro pChoice
    calc
      (∑ qChoice, halfSupportKernelWeight q qChoice
          * dependentCost (halfSupportKernelPoint p pChoice)
            (halfSupportKernelPoint q qChoice)) =
          ∑ qChoice, halfSupportKernelWeight q qChoice
            * dependentCost (halfSupportKernelPoint q qChoice)
              (halfSupportKernelPoint p pChoice) := by
        apply sum_congr rfl
        intro qChoice _
        rw [dependentCost_comm]
      _ ≤ dependentCost q (halfSupportKernelPoint p pChoice) :=
        halfSupportKernel_dependentCost_le hq (halfSupportKernelPoint_mem hp pChoice)
      _ = dependentCost (halfSupportKernelPoint p pChoice) q := dependentCost_comm _ _
  calc
    (∑ pChoice, ∑ qChoice,
        halfSupportKernelWeight p pChoice * halfSupportKernelWeight q qChoice
          * dependentCost (halfSupportKernelPoint p pChoice)
            (halfSupportKernelPoint q qChoice)) =
        ∑ pChoice, halfSupportKernelWeight p pChoice
          * (∑ qChoice, halfSupportKernelWeight q qChoice
            * dependentCost (halfSupportKernelPoint p pChoice)
              (halfSupportKernelPoint q qChoice)) := by
      apply sum_congr rfl
      intro pChoice _
      rw [mul_sum]
      apply sum_congr rfl
      intro qChoice _
      ring
    _ ≤ ∑ pChoice, halfSupportKernelWeight p pChoice
        * dependentCost (halfSupportKernelPoint p pChoice) q := by
      apply sum_le_sum
      intro pChoice _
      exact mul_le_mul_of_nonneg_left (hinner pChoice)
        (halfSupportKernelWeight_nonneg hp pChoice)
    _ ≤ dependentCost p q := halfSupportKernel_dependentCost_le hp hq

theorem halfSupportKernel_pair_weight_sum (p q : ℝ) :
    ∑ pChoice, ∑ qChoice,
      halfSupportKernelWeight p pChoice * halfSupportKernelWeight q qChoice = 1 := by
  rw [Fintype.sum_bool]
  simp only [Fintype.sum_bool, halfSupportKernelWeight]
  split_ifs <;> ring

theorem halfSupportKernel_pair_mean (p q : ℝ) :
    (∑ pChoice, ∑ qChoice,
      halfSupportKernelWeight p pChoice * halfSupportKernelWeight q qChoice
        * ((halfSupportKernelPoint p pChoice + halfSupportKernelPoint q qChoice) / 2)) =
      (p + q) / 2 := by
  rw [Fintype.sum_bool]
  simp only [Fintype.sum_bool, halfSupportKernelWeight, halfSupportKernelPoint]
  split_ifs <;> ring

/-- Pushforward points of a finite marginal under the half-support kernel. -/
noncomputable def halfSupportMarginalPoint {ι : Type*} (point : ι → ℝ) :
    ι × Bool → ℝ
  | (i, choice) => halfSupportKernelPoint (point i) choice

/-- Pushforward weights of a finite marginal under the half-support kernel. -/
noncomputable def halfSupportMarginalWeight {ι : Type*}
    (weight point : ι → ℝ) : ι × Bool → ℝ
  | (i, choice) => weight i * halfSupportKernelWeight (point i) choice

theorem halfSupportMarginalWeight_nonneg {ι : Type*}
    {weight point : ι → ℝ} (hweight : ∀ i, 0 ≤ weight i)
    (hpoint : ∀ i, point i ∈ Icc (0 : ℝ) 1) :
    ∀ z, 0 ≤ halfSupportMarginalWeight weight point z := by
  rintro ⟨i, choice⟩
  exact mul_nonneg (hweight i) (halfSupportKernelWeight_nonneg (hpoint i) choice)

theorem halfSupportMarginalWeight_sum {ι : Type*} [Fintype ι]
    {weight point : ι → ℝ} (hmass : ∑ i, weight i = 1) :
    ∑ z, halfSupportMarginalWeight weight point z = 1 := by
  classical
  simp only [Fintype.sum_prod_type, halfSupportMarginalWeight]
  calc
    ∑ i, ∑ choice, weight i * halfSupportKernelWeight (point i) choice =
        ∑ i, weight i * (∑ choice, halfSupportKernelWeight (point i) choice) := by
      apply sum_congr rfl
      intro i _
      rw [mul_sum]
    _ = ∑ i, weight i := by
      apply sum_congr rfl
      intro i _
      rw [halfSupportKernelWeight_sum, mul_one]
    _ = 1 := hmass

theorem halfSupportMarginal_mean {ι : Type*} [Fintype ι]
    {weight point : ι → ℝ} :
    ∑ z, halfSupportMarginalWeight weight point z * halfSupportMarginalPoint point z =
      ∑ i, weight i * point i := by
  classical
  simp only [Fintype.sum_prod_type, halfSupportMarginalWeight, halfSupportMarginalPoint]
  calc
    ∑ i, ∑ choice,
        weight i * halfSupportKernelWeight (point i) choice
          * halfSupportKernelPoint (point i) choice =
        ∑ i, weight i *
          (∑ choice, halfSupportKernelWeight (point i) choice
            * halfSupportKernelPoint (point i) choice) := by
      apply sum_congr rfl
      intro i _
      rw [mul_sum]
      apply sum_congr rfl
      intro choice _
      ring
    _ = ∑ i, weight i * point i := by
      apply sum_congr rfl
      intro i _
      rw [halfSupportKernel_mean]

theorem halfSupportMarginalPoint_mem {ι : Type*} {point : ι → ℝ}
    (hpoint : ∀ i, point i ∈ Icc (0 : ℝ) 1) :
    ∀ z, halfSupportMarginalPoint point z ∈ Icc (0 : ℝ) 1 := by
  rintro ⟨i, choice⟩
  exact halfSupportKernelPoint_mem (hpoint i) choice

/-- Join-entropy gain produced by the half-support kernel at one source point. -/
noncomputable def halfSupportKernelGain (x r : ℝ) : ℝ :=
  (∑ choice, halfSupportKernelWeight x choice
    * binEntropy (join (halfSupportKernelPoint x choice) r))
    - binEntropy (join x r)

/-- Aggregate join-entropy gain of a finite marginal under the half-support kernel. -/
noncomputable def aggregateHalfSupportGain {ι : Type*} [Fintype ι]
    (weight point : ι → ℝ) (r : ℝ) : ℝ :=
  ∑ i, weight i * halfSupportKernelGain (point i) r

theorem halfSupportKernelGain_eq_zero_of_le {x r : ℝ} (hxHalf : x ≤ 1 / 2) :
    halfSupportKernelGain x r = 0 := by
  rw [halfSupportKernelGain, Fintype.sum_bool]
  simp only [halfSupportKernelWeight, halfSupportKernelPoint]
  split_ifs
  · ring
  · contradiction

theorem halfSupportKernelGain_eq_halfSupportGain {x r : ℝ} (hxHalf : 1 / 2 < x) :
    halfSupportKernelGain x r = halfSupportGain (1 - x) r := by
  have hhalfJoin :
      binEntropy (join (1 / 2) r) = binEntropy ((1 - r) / 2) := by
    rw [← binEntropy_one_sub]
    congr 1
    simp only [join]
    ring
  have hxJoin : binEntropy (join x r) = binEntropy ((1 - x) * (1 - r)) := by
    rw [← binEntropy_one_sub]
    congr 1
    simp only [join]
    ring
  rw [halfSupportKernelGain, Fintype.sum_bool]
  simp only [halfSupportKernelWeight, halfSupportKernelPoint]
  split_ifs with hle
  · linarith
  · rw [hhalfJoin, join_one_left, binEntropy_one, hxJoin]
    dsimp [halfSupportGain]
    ring

theorem halfSupportMarginal_kernel {ι : Type*} [Fintype ι]
    {weight point : ι → ℝ} (r : ℝ) :
    (∑ z, halfSupportMarginalWeight weight point z
      * binEntropy (join (halfSupportMarginalPoint point z) r))
        - (∑ i, weight i * binEntropy (join (point i) r)) =
      aggregateHalfSupportGain weight point r := by
  classical
  simp only [Fintype.sum_prod_type, halfSupportMarginalWeight,
    halfSupportMarginalPoint, aggregateHalfSupportGain, halfSupportKernelGain]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  rw [mul_sub, mul_sum]
  congr 1
  apply sum_congr rfl
  intro choice _
  ring

/-- Polarization of independent entropy for the complete simultaneous half-support
pushforward. -/
theorem finiteJoinEntropy_halfSupport_sub {ι : Type*} [Fintype ι]
    {weight point : ι → ℝ} :
    finiteJoinEntropy (halfSupportMarginalWeight weight point)
        (halfSupportMarginalPoint point)
        - finiteJoinEntropy weight point =
      finiteExpectation (halfSupportMarginalWeight weight point)
          (halfSupportMarginalPoint point) (aggregateHalfSupportGain weight point)
        + finiteExpectation weight point (aggregateHalfSupportGain weight point) := by
  exact finiteJoinEntropy_sub_eq_of_crossKernel (halfSupportMarginal_kernel (weight := weight)
    (point := point))

theorem finiteExpectation_halfSupport_sub {ι : Type*} [Fintype ι]
    {weight point : ι → ℝ} :
    finiteExpectation (halfSupportMarginalWeight weight point)
        (halfSupportMarginalPoint point) binEntropy
        - finiteExpectation weight point binEntropy =
      aggregateHalfSupportGain weight point 0 := by
  have hkernel := halfSupportMarginal_kernel (weight := weight) (point := point) 0
  simpa only [finiteExpectation, join_zero_right] using hkernel

/-- Any finite probability law of mean at most the candidate target averages a one-source
kernel gain below its value at the target. -/
theorem finiteExpectation_halfSupportKernelGain_le {ι : Type*} [Fintype ι]
    {weight point : ι → ℝ} {mean x : ℝ}
    (hweight : ∀ i, 0 ≤ weight i) (hmass : ∑ i, weight i = 1)
    (hpoint : ∀ i, point i ∈ Icc (0 : ℝ) 1)
    (hmean : ∑ i, weight i * point i = mean)
    (hmeanZero : 0 ≤ mean) (hmeanTarget : mean ≤ abundanceTarget)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    finiteExpectation weight point (halfSupportKernelGain x) ≤
      halfSupportKernelGain x abundanceTarget := by
  by_cases hxHalf : x ≤ 1 / 2
  · have hzero : halfSupportKernelGain x = 0 := by
      funext r
      exact halfSupportKernelGain_eq_zero_of_le hxHalf
    rw [hzero]
    simp [finiteExpectation]
  · have hxHalf' : 1 / 2 < x := lt_of_not_ge hxHalf
    have hgain : halfSupportKernelGain x = halfSupportGain (1 - x) := by
      funext r
      exact halfSupportKernelGain_eq_halfSupportGain hxHalf'
    rw [hgain]
    by_cases hxOne : x = 1
    · subst x
      simp [halfSupportGain, finiteExpectation]
    · have hzZero : 0 < 1 - x := sub_pos.2 (lt_of_le_of_ne hx.2 hxOne)
      have hzHalf : 1 - x ≤ 1 / 2 := by linarith
      exact finiteExpectation_halfSupportGain_le hweight hmass hpoint hmean
        hmeanZero hmeanTarget hzZero hzHalf

/-- A nonnegative aggregate of source-kernel gains obeys the same target-mean expectation
bound under any finite evaluating probability law. -/
theorem finiteExpectation_aggregateHalfSupportGain_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {sourceWeight sourcePoint : ι → ℝ} {weight point : κ → ℝ} {mean : ℝ}
    (hsourceWeight : ∀ i, 0 ≤ sourceWeight i)
    (hsourcePoint : ∀ i, sourcePoint i ∈ Icc (0 : ℝ) 1)
    (hweight : ∀ k, 0 ≤ weight k) (hmass : ∑ k, weight k = 1)
    (hpoint : ∀ k, point k ∈ Icc (0 : ℝ) 1)
    (hmean : ∑ k, weight k * point k = mean)
    (hmeanZero : 0 ≤ mean) (hmeanTarget : mean ≤ abundanceTarget) :
    finiteExpectation weight point (aggregateHalfSupportGain sourceWeight sourcePoint) ≤
      aggregateHalfSupportGain sourceWeight sourcePoint abundanceTarget := by
  classical
  calc
    finiteExpectation weight point (aggregateHalfSupportGain sourceWeight sourcePoint) =
        ∑ k, ∑ i, weight k *
          (sourceWeight i * halfSupportKernelGain (sourcePoint i) (point k)) := by
      dsimp only [finiteExpectation, aggregateHalfSupportGain]
      apply sum_congr rfl
      intro k _
      rw [mul_sum]
    _ = ∑ i, ∑ k, weight k *
        (sourceWeight i * halfSupportKernelGain (sourcePoint i) (point k)) := sum_comm
    _ = ∑ i, sourceWeight i *
        finiteExpectation weight point (halfSupportKernelGain (sourcePoint i)) := by
      apply sum_congr rfl
      intro i _
      dsimp only [finiteExpectation]
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      ring
    _ ≤ ∑ i, sourceWeight i
        * halfSupportKernelGain (sourcePoint i) abundanceTarget := by
      apply sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (finiteExpectation_halfSupportKernelGain_le hweight hmass hpoint hmean
          hmeanZero hmeanTarget (hsourcePoint i))
        (hsourceWeight i)
    _ = aggregateHalfSupportGain sourceWeight sourcePoint abundanceTarget := rfl

/-- The scalar half-support inequality survives an arbitrary nonnegative finite aggregate. -/
theorem twice_aggregateHalfSupportGain_target_le {ι : Type*} [Fintype ι]
    {weight point : ι → ℝ}
    (hweight : ∀ i, 0 ≤ weight i) (hpoint : ∀ i, point i ∈ Icc (0 : ℝ) 1) :
    2 * aggregateHalfSupportGain weight point abundanceTarget ≤
      marginalPenalty * aggregateHalfSupportGain weight point 0 := by
  have hpointwise : ∀ i,
      2 * halfSupportKernelGain (point i) abundanceTarget ≤
        marginalPenalty * halfSupportKernelGain (point i) 0 := by
    intro i
    by_cases hiHalf : point i ≤ 1 / 2
    · rw [halfSupportKernelGain_eq_zero_of_le hiHalf,
        halfSupportKernelGain_eq_zero_of_le hiHalf]
      simp
    · have hiHalf' : 1 / 2 < point i := lt_of_not_ge hiHalf
      rw [halfSupportKernelGain_eq_halfSupportGain hiHalf',
        halfSupportKernelGain_eq_halfSupportGain hiHalf']
      by_cases hiOne : point i = 1
      · rw [hiOne]
        simp [halfSupportGain]
      · have hzZero : 0 < 1 - point i :=
          sub_pos.2 (lt_of_le_of_ne (hpoint i).2 hiOne)
        have hzHalf : 1 - point i < 1 / 2 := by linarith
        exact (twice_gain_target_lt_penalty_gain_zero hzZero hzHalf).le
  calc
    2 * aggregateHalfSupportGain weight point abundanceTarget =
        ∑ i, weight i * (2 * halfSupportKernelGain (point i) abundanceTarget) := by
      dsimp only [aggregateHalfSupportGain]
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, weight i *
        (marginalPenalty * halfSupportKernelGain (point i) 0) := by
      apply sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hpointwise i) (hweight i)
    _ = marginalPenalty * aggregateHalfSupportGain weight point 0 := by
      dsimp only [aggregateHalfSupportGain]
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring

/-- Simultaneously applying the half-support kernel to every atom cannot increase independent
entropy faster than the normalized marginal penalty. -/
theorem finiteHalfSupportKernel_penalized_le {ι : Type*} [Fintype ι]
    {weight point : ι → ℝ} {mean : ℝ}
    (hweight : ∀ i, 0 ≤ weight i) (hmass : ∑ i, weight i = 1)
    (hpoint : ∀ i, point i ∈ Icc (0 : ℝ) 1)
    (hmean : ∑ i, weight i * point i = mean)
    (hmeanZero : 0 ≤ mean) (hmeanTarget : mean ≤ abundanceTarget) :
    finiteJoinEntropy (halfSupportMarginalWeight weight point)
        (halfSupportMarginalPoint point)
        - finiteJoinEntropy weight point ≤
      marginalPenalty
        * (finiteExpectation (halfSupportMarginalWeight weight point)
            (halfSupportMarginalPoint point) binEntropy
          - finiteExpectation weight point binEntropy) := by
  have hnewWeight := halfSupportMarginalWeight_nonneg hweight hpoint
  have hnewMass := halfSupportMarginalWeight_sum (point := point) hmass
  have hnewPoint := halfSupportMarginalPoint_mem hpoint
  have hnewMean :
      ∑ z, halfSupportMarginalWeight weight point z
          * halfSupportMarginalPoint point z = mean := by
    rw [halfSupportMarginal_mean, hmean]
  have hnewGain := finiteExpectation_aggregateHalfSupportGain_le
    hweight hpoint hnewWeight hnewMass hnewPoint hnewMean hmeanZero hmeanTarget
  have holdGain := finiteExpectation_aggregateHalfSupportGain_le
    hweight hpoint hweight hmass hpoint hmean hmeanZero hmeanTarget
  have hpolarization := finiteJoinEntropy_halfSupport_sub (weight := weight) (point := point)
  have hjoin :
      finiteJoinEntropy (halfSupportMarginalWeight weight point)
          (halfSupportMarginalPoint point)
          - finiteJoinEntropy weight point ≤
        2 * aggregateHalfSupportGain weight point abundanceTarget := by
    rw [hpolarization]
    linarith
  have hscalar := twice_aggregateHalfSupportGain_target_le hweight hpoint
  have hmarginal := finiteExpectation_halfSupport_sub (weight := weight) (point := point)
  calc
    finiteJoinEntropy (halfSupportMarginalWeight weight point)
          (halfSupportMarginalPoint point)
          - finiteJoinEntropy weight point ≤
        2 * aggregateHalfSupportGain weight point abundanceTarget := hjoin
    _ ≤ marginalPenalty * aggregateHalfSupportGain weight point 0 := hscalar
    _ = marginalPenalty
        * (finiteExpectation (halfSupportMarginalWeight weight point)
            (halfSupportMarginalPoint point) binEntropy
          - finiteExpectation weight point binEntropy) := by rw [hmarginal]

/-- Left coordinates after applying the half-support kernel independently to both coordinates
of every old orbit. -/
noncomputable def halfSupportOrbitLeft {ι : Type*} (left : ι → ℝ) :
    ι × (Bool × Bool) → ℝ
  | (i, (leftChoice, _)) => halfSupportKernelPoint (left i) leftChoice

/-- Right coordinates after applying the half-support kernel independently to both coordinates
of every old orbit. -/
noncomputable def halfSupportOrbitRight {ι : Type*} (right : ι → ℝ) :
    ι × (Bool × Bool) → ℝ
  | (i, (_, rightChoice)) => halfSupportKernelPoint (right i) rightChoice

/-- Orbit masses after the independent coordinatewise half-support transformation. -/
noncomputable def halfSupportOrbitWeight {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ} (law : FiniteOrbitLaw left right mean) :
    ι × (Bool × Bool) → ℝ
  | (i, (leftChoice, rightChoice)) =>
      law.weight i * halfSupportKernelWeight (left i) leftChoice
        * halfSupportKernelWeight (right i) rightChoice

/-- Applying the half-support kernel independently to both coordinates of a symmetric orbit
law preserves total mass and marginal mean. -/
noncomputable def halfSupportOrbitLaw {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ}
    (hleft : ∀ i, left i ∈ Icc (0 : ℝ) 1)
    (hright : ∀ i, right i ∈ Icc (0 : ℝ) 1)
    (law : FiniteOrbitLaw left right mean) :
    FiniteOrbitLaw (halfSupportOrbitLeft left) (halfSupportOrbitRight right) mean where
  weight := halfSupportOrbitWeight law
  weight_nonneg z := by
    rcases z with ⟨i, leftChoice, rightChoice⟩
    exact mul_nonneg
      (mul_nonneg (law.weight_nonneg i)
        (halfSupportKernelWeight_nonneg (hleft i) leftChoice))
      (halfSupportKernelWeight_nonneg (hright i) rightChoice)
  weight_sum := by
    classical
    simp only [Fintype.sum_prod_type, halfSupportOrbitWeight]
    calc
      ∑ i, ∑ leftChoice, ∑ rightChoice,
          law.weight i * halfSupportKernelWeight (left i) leftChoice
            * halfSupportKernelWeight (right i) rightChoice =
          ∑ i, law.weight i *
            (∑ leftChoice, ∑ rightChoice,
              halfSupportKernelWeight (left i) leftChoice
                * halfSupportKernelWeight (right i) rightChoice) := by
        apply sum_congr rfl
        intro i _
        rw [mul_sum]
        apply sum_congr rfl
        intro leftChoice _
        rw [mul_sum]
        apply sum_congr rfl
        intro rightChoice _
        ring
      _ = ∑ i, law.weight i := by
        apply sum_congr rfl
        intro i _
        rw [halfSupportKernel_pair_weight_sum, mul_one]
      _ = 1 := law.weight_sum
  moment_sum := by
    classical
    simp only [Fintype.sum_prod_type, halfSupportOrbitWeight, orbitMean,
      halfSupportOrbitLeft, halfSupportOrbitRight]
    calc
      ∑ i, ∑ leftChoice, ∑ rightChoice,
          law.weight i * halfSupportKernelWeight (left i) leftChoice
              * halfSupportKernelWeight (right i) rightChoice
            * ((halfSupportKernelPoint (left i) leftChoice
              + halfSupportKernelPoint (right i) rightChoice) / 2) =
          ∑ i, law.weight i *
            (∑ leftChoice, ∑ rightChoice,
              halfSupportKernelWeight (left i) leftChoice
                  * halfSupportKernelWeight (right i) rightChoice
                * ((halfSupportKernelPoint (left i) leftChoice
                  + halfSupportKernelPoint (right i) rightChoice) / 2)) := by
        apply sum_congr rfl
        intro i _
        rw [mul_sum]
        apply sum_congr rfl
        intro leftChoice _
        rw [mul_sum]
        apply sum_congr rfl
        intro rightChoice _
        ring
      _ = ∑ i, law.weight i * orbitMean left right i := by
        apply sum_congr rfl
        intro i _
        rw [halfSupportKernel_pair_mean]
        rfl
      _ = mean := law.moment_sum

/-- Every live left coordinate of the transformed law lies in `[0,1/2] ∪ {1}`. -/
theorem halfSupportOrbitLaw_live_left_range {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ}
    (hleft : ∀ i, left i ∈ Icc (0 : ℝ) 1)
    (hright : ∀ i, right i ∈ Icc (0 : ℝ) 1)
    (law : FiniteOrbitLaw left right mean)
    {z : ι × (Bool × Bool)} (hz : z ∈ (halfSupportOrbitLaw hleft hright law).support) :
    halfSupportOrbitLeft left z ≤ 1 / 2 ∨ halfSupportOrbitLeft left z = 1 := by
  rcases z with ⟨i, leftChoice, rightChoice⟩
  have hlive := (halfSupportOrbitLaw hleft hright law).weight_pos_of_mem_support hz
  have hleftNonneg := halfSupportKernelWeight_nonneg (hleft i) leftChoice
  have hleftPositive : 0 < halfSupportKernelWeight (left i) leftChoice := by
    by_contra hnot
    have hzero : halfSupportKernelWeight (left i) leftChoice = 0 :=
      le_antisymm (not_lt.mp hnot) hleftNonneg
    simp [halfSupportOrbitLaw, halfSupportOrbitWeight, hzero] at hlive
  exact halfSupportKernel_live_range leftChoice hleftPositive

/-- Every live right coordinate of the transformed law lies in `[0,1/2] ∪ {1}`. -/
theorem halfSupportOrbitLaw_live_right_range {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ}
    (hleft : ∀ i, left i ∈ Icc (0 : ℝ) 1)
    (hright : ∀ i, right i ∈ Icc (0 : ℝ) 1)
    (law : FiniteOrbitLaw left right mean)
    {z : ι × (Bool × Bool)} (hz : z ∈ (halfSupportOrbitLaw hleft hright law).support) :
    halfSupportOrbitRight right z ≤ 1 / 2 ∨ halfSupportOrbitRight right z = 1 := by
  rcases z with ⟨i, leftChoice, rightChoice⟩
  have hlive := (halfSupportOrbitLaw hleft hright law).weight_pos_of_mem_support hz
  have hrightNonneg := halfSupportKernelWeight_nonneg (hright i) rightChoice
  have hrightPositive : 0 < halfSupportKernelWeight (right i) rightChoice := by
    by_contra hnot
    have hzero : halfSupportKernelWeight (right i) rightChoice = 0 :=
      le_antisymm (not_lt.mp hnot) hrightNonneg
    simp [halfSupportOrbitLaw, halfSupportOrbitWeight, hzero] at hlive
  exact halfSupportKernel_live_range rightChoice hrightPositive

/-- The coordinatewise half-support transformation cannot increase the dependent entropy of a
symmetric finite coupling. -/
theorem orbitDependentEntropy_halfSupport_le {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ}
    (hleft : ∀ i, left i ∈ Icc (0 : ℝ) 1)
    (hright : ∀ i, right i ∈ Icc (0 : ℝ) 1)
    (law : FiniteOrbitLaw left right mean) :
    orbitDependentEntropy (halfSupportOrbitLaw hleft hright law) ≤
      orbitDependentEntropy law := by
  classical
  simp only [orbitDependentEntropy, halfSupportOrbitLaw, Fintype.sum_prod_type,
    halfSupportOrbitWeight, halfSupportOrbitLeft, halfSupportOrbitRight]
  apply sum_le_sum
  intro i _
  calc
    (∑ leftChoice, ∑ rightChoice,
        law.weight i * halfSupportKernelWeight (left i) leftChoice
            * halfSupportKernelWeight (right i) rightChoice
          * dependentCost (halfSupportKernelPoint (left i) leftChoice)
            (halfSupportKernelPoint (right i) rightChoice)) =
        law.weight i *
          (∑ leftChoice, ∑ rightChoice,
            halfSupportKernelWeight (left i) leftChoice
                * halfSupportKernelWeight (right i) rightChoice
              * dependentCost (halfSupportKernelPoint (left i) leftChoice)
                (halfSupportKernelPoint (right i) rightChoice)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro leftChoice _
      rw [mul_sum]
      apply sum_congr rfl
      intro rightChoice _
      ring
    _ ≤ law.weight i * dependentCost (left i) (right i) :=
      mul_le_mul_of_nonneg_left
        (halfSupportKernel_pair_dependentCost_le (hleft i) (hright i))
        (law.weight_nonneg i)

/-- The marginal of the transformed orbit law is the scalar-kernel pushforward of the old
marginal, as tested against every observable. -/
theorem orbitHalfSupport_expectation_eq {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ}
    (hleft : ∀ i, left i ∈ Icc (0 : ℝ) 1)
    (hright : ∀ i, right i ∈ Icc (0 : ℝ) 1)
    (law : FiniteOrbitLaw left right mean) (observable : ℝ → ℝ) :
    finiteExpectation (orbitMarginalWeight (halfSupportOrbitLaw hleft hright law))
        (orbitMarginalPoint (halfSupportOrbitLeft left) (halfSupportOrbitRight right))
        observable =
      finiteExpectation
        (halfSupportMarginalWeight (orbitMarginalWeight law)
          (orbitMarginalPoint left right))
        (halfSupportMarginalPoint (orbitMarginalPoint left right)) observable := by
  classical
  simp only [finiteExpectation, Fintype.sum_prod_type, Fintype.sum_bool,
    orbitMarginalWeight, orbitMarginalPoint, halfSupportOrbitLaw,
    halfSupportOrbitWeight, halfSupportOrbitLeft, halfSupportOrbitRight,
    halfSupportMarginalWeight, halfSupportMarginalPoint]
  apply sum_congr rfl
  intro i _
  have hleftSum := halfSupportKernelWeight_sum (left i)
  have hrightSum := halfSupportKernelWeight_sum (right i)
  rw [Fintype.sum_bool] at hleftSum hrightSum
  have hleftFalse : halfSupportKernelWeight (left i) false =
      1 - halfSupportKernelWeight (left i) true := by linarith
  have hrightFalse : halfSupportKernelWeight (right i) false =
      1 - halfSupportKernelWeight (right i) true := by linarith
  rw [hleftFalse, hrightFalse]
  ring

theorem orbitMarginalEntropy_halfSupport_eq {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ}
    (hleft : ∀ i, left i ∈ Icc (0 : ℝ) 1)
    (hright : ∀ i, right i ∈ Icc (0 : ℝ) 1)
    (law : FiniteOrbitLaw left right mean) :
    orbitMarginalEntropy (halfSupportOrbitLaw hleft hright law) =
      finiteExpectation
        (halfSupportMarginalWeight (orbitMarginalWeight law)
          (orbitMarginalPoint left right))
        (halfSupportMarginalPoint (orbitMarginalPoint left right)) binEntropy := by
  exact orbitHalfSupport_expectation_eq hleft hright law binEntropy

theorem orbitIndependentEntropy_halfSupport_eq {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ}
    (hleft : ∀ i, left i ∈ Icc (0 : ℝ) 1)
    (hright : ∀ i, right i ∈ Icc (0 : ℝ) 1)
    (law : FiniteOrbitLaw left right mean) :
    orbitIndependentEntropy (halfSupportOrbitLaw hleft hright law) =
      finiteJoinEntropy
        (halfSupportMarginalWeight (orbitMarginalWeight law)
          (orbitMarginalPoint left right))
        (halfSupportMarginalPoint (orbitMarginalPoint left right)) := by
  let transformed := halfSupportOrbitLaw hleft hright law
  let transformedWeight := orbitMarginalWeight transformed
  let transformedPoint := orbitMarginalPoint
    (halfSupportOrbitLeft left) (halfSupportOrbitRight right)
  let pushedWeight := halfSupportMarginalWeight (orbitMarginalWeight law)
    (orbitMarginalPoint left right)
  let pushedPoint := halfSupportMarginalPoint (orbitMarginalPoint left right)
  have hinner : ∀ r,
      finiteExpectation transformedWeight transformedPoint
          (fun q ↦ binEntropy (join r q)) =
        finiteExpectation pushedWeight pushedPoint (fun q ↦ binEntropy (join r q)) := by
    intro r
    exact orbitHalfSupport_expectation_eq hleft hright law
      (fun q ↦ binEntropy (join r q))
  rw [orbitIndependentEntropy, finiteJoinEntropy_eq_iteratedExpectation,
    finiteJoinEntropy_eq_iteratedExpectation]
  calc
    finiteExpectation transformedWeight transformedPoint (fun r ↦
        finiteExpectation transformedWeight transformedPoint
          (fun q ↦ binEntropy (join r q))) =
        finiteExpectation transformedWeight transformedPoint (fun r ↦
          finiteExpectation pushedWeight pushedPoint
            (fun q ↦ binEntropy (join r q))) := by
      change (∑ z, transformedWeight z *
        finiteExpectation transformedWeight transformedPoint
          (fun q ↦ binEntropy (join (transformedPoint z) q))) =
        ∑ z, transformedWeight z *
          finiteExpectation pushedWeight pushedPoint
            (fun q ↦ binEntropy (join (transformedPoint z) q))
      apply sum_congr rfl
      intro z _
      rw [hinner (transformedPoint z)]
    _ = finiteExpectation pushedWeight pushedPoint (fun r ↦
        finiteExpectation pushedWeight pushedPoint
          (fun q ↦ binEntropy (join r q))) :=
      orbitHalfSupport_expectation_eq hleft hright law _

/-- A normalized independent-versus-marginal contraction and a dependent-cost contraction
together decrease the complete strict Yu gap. -/
theorem yuGap_le_of_penalized_join_and_dependent
    {oldJoin newJoin oldMarginal newMarginal oldDependent newDependent : ℝ}
    (hjoin : newJoin - oldJoin ≤ marginalPenalty * (newMarginal - oldMarginal))
    (hdependent : newDependent ≤ oldDependent) :
    yuGap newJoin newMarginal newDependent ≤
      yuGap oldJoin oldMarginal oldDependent := by
  norm_num [yuGap, marginalPenalty, dependentShare, entropySlack] at *
  linarith

/-- The simultaneous coordinatewise half-support transformation does not increase the complete
strict Yu gap, preserves the exact marginal mean, and has only live coordinates in
`[0,1/2] ∪ {1}`. -/
theorem orbitYuGap_halfSupport_le {ι : Type*} [Fintype ι]
    {left right : ι → ℝ} {mean : ℝ}
    (hleft : ∀ i, left i ∈ Icc (0 : ℝ) 1)
    (hright : ∀ i, right i ∈ Icc (0 : ℝ) 1)
    (law : FiniteOrbitLaw left right mean)
    (hmeanZero : 0 ≤ mean) (hmeanTarget : mean ≤ abundanceTarget) :
    orbitYuGap (halfSupportOrbitLaw hleft hright law) ≤ orbitYuGap law := by
  have hpenalized := finiteHalfSupportKernel_penalized_le
    (orbitMarginalWeight_nonneg law) (orbitMarginalWeight_sum law)
    (orbitMarginalPoint_mem hleft hright) (orbitMarginal_mean law)
    hmeanZero hmeanTarget
  have hjoin :
      orbitIndependentEntropy (halfSupportOrbitLaw hleft hright law)
          - orbitIndependentEntropy law ≤
        marginalPenalty
          * (orbitMarginalEntropy (halfSupportOrbitLaw hleft hright law)
            - orbitMarginalEntropy law) := by
    rw [orbitIndependentEntropy_halfSupport_eq hleft hright,
      orbitMarginalEntropy_halfSupport_eq hleft hright]
    exact hpenalized
  have hdependent := orbitDependentEntropy_halfSupport_le hleft hright law
  exact yuGap_le_of_penalized_join_and_dependent hjoin hdependent

/-- Every coordinate of an orbit system lies either in the low half-interval or at the endpoint
one. -/
def HasHalfSupportCoordinates {ι : Type*} (left right : ι → ℝ) : Prop :=
  ∀ i, (left i ≤ 1 / 2 ∨ left i = 1) ∧ (right i ≤ 1 / 2 ∨ right i = 1)

theorem halfSupportOrbit_coordinates {ι : Type*}
    (left right : ι → ℝ) :
    HasHalfSupportCoordinates (halfSupportOrbitLeft left) (halfSupportOrbitRight right) := by
  rintro ⟨i, leftChoice, rightChoice⟩
  exact ⟨halfSupportKernelPoint_range (left i) leftChoice,
    halfSupportKernelPoint_range (right i) rightChoice⟩

/-- Every exact-target finite symmetric coupling has a no-worse fully identified extreme whose
coordinates lie in `[0,1/2] ∪ {1}`. -/
theorem orbitYuGap_exists_halfSupported_extreme_of_mem {ι : Type*} [Fintype ι]
    {left right : ι → ℝ}
    (hleft : ∀ i, left i ∈ Icc (0 : ℝ) 1)
    (hright : ∀ i, right i ∈ Icc (0 : ℝ) 1)
    (law : FiniteOrbitLaw left right abundanceTarget) :
    ∃ reduced : FiniteOrbitLaw (halfSupportOrbitLeft left)
        (halfSupportOrbitRight right) abundanceTarget,
      orbitYuGap reduced ≤ orbitYuGap law ∧ IsIdentifiedOrbitExtreme reduced
        ∧ HasHalfSupportCoordinates (halfSupportOrbitLeft left)
          (halfSupportOrbitRight right) := by
  let transformed := halfSupportOrbitLaw hleft hright law
  have htransformedLeft :
      ∀ z, halfSupportOrbitLeft left z ∈ Icc (0 : ℝ) 1 := by
    rintro ⟨i, leftChoice, _⟩
    exact halfSupportKernelPoint_mem (hleft i) leftChoice
  have htransformedRight :
      ∀ z, halfSupportOrbitRight right z ∈ Icc (0 : ℝ) 1 := by
    rintro ⟨i, _, rightChoice⟩
    exact halfSupportKernelPoint_mem (hright i) rightChoice
  have htransformedGap : orbitYuGap transformed ≤ orbitYuGap law :=
    orbitYuGap_halfSupport_le hleft hright law
      (by linarith [abundanceTarget_gt_three_eighths]) le_rfl
  obtain ⟨reduced, hreducedGap, hextreme⟩ :=
    orbitYuGap_exists_extreme_orbitWeights_of_mem
      htransformedLeft htransformedRight transformed
  exact ⟨reduced, hreducedGap.trans htransformedGap, hextreme,
    halfSupportOrbit_coordinates left right⟩

end Frankl
