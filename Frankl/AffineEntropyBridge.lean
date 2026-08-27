import Frankl.EndpointBoundary
import Frankl.FiniteCoupling

namespace Frankl

open Finset Real Set

/-- Boolean cubes presented as iterated prefix/last-bit products. -/
@[reducible]
def BitCube : ℕ → Type
  | 0 => Unit
  | n + 1 => BitCube n × Bool

@[instance_reducible]
private def bitCubeFintype : ∀ n, Fintype (BitCube n)
  | 0 => by
      change Fintype Unit
      exact inferInstance
  | n + 1 => by
      change Fintype (BitCube n × Bool)
      letI := bitCubeFintype n
      exact inferInstance

@[instance_reducible]
private def bitCubeDecidableEq : ∀ n, DecidableEq (BitCube n)
  | 0 => by
      change DecidableEq Unit
      exact inferInstance
  | n + 1 => by
      change DecidableEq (BitCube n × Bool)
      letI := bitCubeDecidableEq n
      exact inferInstance

instance (n : ℕ) : Fintype (BitCube n) := bitCubeFintype n

instance (n : ℕ) : DecidableEq (BitCube n) := bitCubeDecidableEq n

/-- Coordinatewise Boolean union. -/
def BitCube.union : ∀ {n}, BitCube n → BitCube n → BitCube n
  | 0, _, _ => ()
  | _ + 1, x, y => (BitCube.union x.1 y.1, x.2 || y.2)

/-- A coordinate of the iterated Boolean cube. -/
inductive BitCube.Coordinate : ℕ → Type
  | prior {n} : Coordinate n → Coordinate (n + 1)
  | last {n} : Coordinate (n + 1)

/-- Read one coordinate. -/
def BitCube.read : ∀ {n}, BitCube n → BitCube.Coordinate n → Bool
  | _ + 1, x, .prior coordinate => BitCube.read x.1 coordinate
  | _ + 1, x, .last => x.2

/-- The all-zero Boolean vector. -/
def BitCube.zero : ∀ n, BitCube n
  | 0 => ()
  | n + 1 => (BitCube.zero n, false)

theorem BitCube.exists_true_coordinate {n : ℕ} {x : BitCube n} (hx : x ≠ BitCube.zero n) :
    ∃ coordinate, BitCube.read x coordinate = true := by
  induction n with
  | zero => exact (hx rfl).elim
  | succ n ih =>
      rcases x with ⟨stemBits, bit⟩
      cases bit
      · have hprefix : stemBits ≠ BitCube.zero n := by
          intro h
          apply hx
          rw [BitCube.zero, h]
        obtain ⟨coordinate, hcoordinate⟩ := ih hprefix
        exact ⟨.prior coordinate, hcoordinate⟩
      · exact ⟨.last, rfl⟩

namespace FiniteProbabilityLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Mean of the final Boolean coordinate. -/
noncomputable def finalMean (source : FiniteProbabilityLaw (ι × Bool)) : ℝ :=
  source.second.weight true

theorem sum_conditionalParameter (source : FiniteProbabilityLaw (ι × Bool)) :
    (∑ i, source.first.weight i * source.successParameter i) = source.finalMean := by
  rw [finalMean, second_weight]
  apply sum_congr rfl
  intro i _
  exact source.first_mul_successParameter i

/-- The conditional-probability coupling at one coordinate, represented in the orbit-law
interface used by the finite Yu certificate. -/
noncomputable def conditionalOrbitLaw (source : FiniteProbabilityLaw (ι × Bool))
    (coupling : SymmetricCoupling source.first) :
    FiniteOrbitLaw
      (fun z : ι × ι ↦ source.successParameter z.1)
      (fun z : ι × ι ↦ source.successParameter z.2) source.finalMean where
  weight := coupling.joint.weight
  weight_nonneg := coupling.joint.weight_nonneg
  weight_sum := coupling.joint.weight_sum
  moment_sum := by
    change (∑ z, coupling.joint.weight z *
      ((source.successParameter z.1 + source.successParameter z.2) / 2)) = source.finalMean
    calc
      (∑ z, coupling.joint.weight z *
          ((source.successParameter z.1 + source.successParameter z.2) / 2)) =
          ((∑ z, coupling.joint.weight z * source.successParameter z.1) +
            ∑ z, coupling.joint.weight z * source.successParameter z.2) / 2 := by
        calc
          (∑ z, coupling.joint.weight z *
              ((source.successParameter z.1 + source.successParameter z.2) / 2)) =
              ∑ z, (coupling.joint.weight z * source.successParameter z.1 / 2 +
                coupling.joint.weight z * source.successParameter z.2 / 2) := by
            apply sum_congr rfl
            intro z _
            ring
          _ = ((∑ z, coupling.joint.weight z * source.successParameter z.1) +
              ∑ z, coupling.joint.weight z * source.successParameter z.2) / 2 := by
            rw [sum_add_distrib, ← sum_div, ← sum_div]
            ring
      _ = ((∑ i, source.first.weight i * source.successParameter i) +
          ∑ i, source.first.weight i * source.successParameter i) / 2 := by
        rw [coupling.sum_left, coupling.sum_right]
      _ = source.finalMean := by
        rw [source.sum_conditionalParameter]
        ring

theorem conditionalOrbit_expectation (source : FiniteProbabilityLaw (ι × Bool))
    (coupling : SymmetricCoupling source.first) (observable : ℝ → ℝ) :
    finiteExpectation
        (orbitMarginalWeight (source.conditionalOrbitLaw coupling))
        (orbitMarginalPoint
          (fun z : ι × ι ↦ source.successParameter z.1)
          (fun z : ι × ι ↦ source.successParameter z.2)) observable =
      ∑ i, source.first.weight i * observable (source.successParameter i) := by
  classical
  rw [finiteExpectation, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, orbitMarginalWeight, conditionalOrbitLaw,
    orbitMarginalPoint]
  calc
    (∑ z, (coupling.joint.weight z / 2 * observable (source.successParameter z.2) +
        coupling.joint.weight z / 2 * observable (source.successParameter z.1))) =
        ((∑ z, coupling.joint.weight z * observable (source.successParameter z.2)) +
          ∑ z, coupling.joint.weight z * observable (source.successParameter z.1)) / 2 := by
      rw [sum_add_distrib]
      simp_rw [div_mul_eq_mul_div]
      rw [← sum_div, ← sum_div]
      ring
    _ = ((∑ i, source.first.weight i * observable (source.successParameter i)) +
        ∑ i, source.first.weight i * observable (source.successParameter i)) / 2 := by
      rw [coupling.sum_right (fun i ↦ observable (source.successParameter i)),
        coupling.sum_left (fun i ↦ observable (source.successParameter i))]
    _ = ∑ i, source.first.weight i * observable (source.successParameter i) := by ring

theorem conditionalOrbitMarginalEntropy (source : FiniteProbabilityLaw (ι × Bool))
    (coupling : SymmetricCoupling source.first) :
    orbitMarginalEntropy (source.conditionalOrbitLaw coupling) =
      ∑ i, source.first.weight i * binEntropy (source.successParameter i) := by
  exact source.conditionalOrbit_expectation coupling binEntropy

theorem conditionalOrbitDependentEntropy (source : FiniteProbabilityLaw (ι × Bool))
    (coupling : SymmetricCoupling source.first) :
    orbitDependentEntropy (source.conditionalOrbitLaw coupling) =
      ∑ z, coupling.joint.weight z *
        dependentCost (source.successParameter z.1) (source.successParameter z.2) := rfl

theorem conditionalOrbitIndependentEntropy (source : FiniteProbabilityLaw (ι × Bool))
    (coupling : SymmetricCoupling source.first) :
    orbitIndependentEntropy (source.conditionalOrbitLaw coupling) =
      ∑ u, ∑ v, source.first.weight u * source.first.weight v *
        binEntropy (join (source.successParameter u) (source.successParameter v)) := by
  rw [orbitIndependentEntropy, finiteJoinEntropy_eq_iteratedExpectation]
  rw [source.conditionalOrbit_expectation coupling]
  apply sum_congr rfl
  intro u _
  rw [source.conditionalOrbit_expectation coupling]
  rw [mul_sum]
  apply sum_congr rfl
  intro v _
  ring

theorem conditionalOrbitYuGap (source : FiniteProbabilityLaw (ι × Bool))
    (coupling : SymmetricCoupling source.first) (hmean : source.finalMean ≤ abundanceTarget) :
    (1 - dependentShare) *
          (∑ u, ∑ v, source.first.weight u * source.first.weight v *
            binEntropy (join (source.successParameter u) (source.successParameter v))) +
        dependentShare *
          (∑ z, coupling.joint.weight z *
            dependentCost (source.successParameter z.1) (source.successParameter z.2)) ≥
      (1 + entropySlack) *
        ∑ i, source.first.weight i * binEntropy (source.successParameter i) := by
  have hgap := orbitYuGap_nonneg
    (law := source.conditionalOrbitLaw coupling)
    (fun z : ι × ι ↦ source.successParameter_mem z.1)
    (fun z : ι × ι ↦ source.successParameter_mem z.2) hmean
  rw [orbitYuGap, yuGap, source.conditionalOrbitIndependentEntropy coupling,
    source.conditionalOrbitMarginalEntropy coupling,
    source.conditionalOrbitDependentEntropy coupling] at hgap
  linarith

end FiniteProbabilityLaw

/-- Every coordinate mean of a Boolean-cube law is at most the certified target. -/
def CoordinateMeansLE : ∀ n, FiniteProbabilityLaw (BitCube n) → Prop
  | 0, _ => True
  | _ + 1, source =>
      CoordinateMeansLE _ source.first ∧ source.finalMean ≤ abundanceTarget

/-- Probability that one coordinate is true. -/
noncomputable def coordinateMean {n : ℕ} (source : FiniteProbabilityLaw (BitCube n))
    (coordinate : BitCube.Coordinate n) : ℝ :=
  ∑ x, source.weight x * if BitCube.read x coordinate then 1 else 0

theorem coordinateMean_last {n : ℕ}
    (source : FiniteProbabilityLaw (BitCube (n + 1))) :
    coordinateMean source .last = source.finalMean := by
  rw [coordinateMean, FiniteProbabilityLaw.finalMean, FiniteProbabilityLaw.second_weight]
  change (∑ x : BitCube n × Bool, source.weight x * if x.2 then 1 else 0) =
    ∑ i : BitCube n, source.weight (i, true)
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro stemBits _
  simp

theorem coordinateMean_prior {n : ℕ}
    (source : FiniteProbabilityLaw (BitCube (n + 1)))
    (coordinate : BitCube.Coordinate n) :
    coordinateMean source (.prior coordinate) = coordinateMean source.first coordinate := by
  rw [coordinateMean, coordinateMean]
  change (∑ x : BitCube n × Bool,
      source.weight x * if BitCube.read x.1 coordinate then 1 else 0) =
    ∑ x : BitCube n, source.first.weight x *
      if BitCube.read x coordinate then 1 else 0
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro stemBits _
  change (∑ y : Bool, source.weight (stemBits, y) *
      if BitCube.read stemBits coordinate then 1 else 0) =
    source.first.weight stemBits * if BitCube.read stemBits coordinate then 1 else 0
  rw [← sum_mul, ← FiniteProbabilityLaw.first_weight]

theorem coordinateMeansLE_iff : ∀ n (source : FiniteProbabilityLaw (BitCube n)),
    CoordinateMeansLE n source ↔
      ∀ coordinate, coordinateMean source coordinate ≤ abundanceTarget := by
  intro n
  induction n with
  | zero =>
      intro source
      constructor
      · intro _ coordinate
        exact nomatch coordinate
      · intro _
        trivial
  | succ n ih =>
      intro source
      change (CoordinateMeansLE n source.first ∧
        source.finalMean ≤ abundanceTarget) ↔ _
      rw [ih source.first]
      constructor
      · rintro ⟨hprior, hlast⟩ coordinate
        cases coordinate with
        | prior coordinate =>
            rw [coordinateMean_prior]
            exact hprior coordinate
        | last =>
            rw [coordinateMean_last]
            exact hlast
      · intro hcoordinate
        constructor
        · intro coordinate
          rw [← coordinateMean_prior source coordinate]
          exact hcoordinate (.prior coordinate)
        · rw [← coordinateMean_last source]
          exact hcoordinate .last

theorem exists_coordinateMean_gt_of_not {n : ℕ}
    (source : FiniteProbabilityLaw (BitCube n))
    (hsource : ¬CoordinateMeansLE n source) :
    ∃ coordinate, abundanceTarget < coordinateMean source coordinate := by
  rw [coordinateMeansLE_iff] at hsource
  push Not at hsource
  exact hsource

private theorem dependentParameter_mem_Icc {p q : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) :
    dependentParameter p q ∈ Icc (0 : ℝ) 1 := by
  rw [dependentParameter]
  constructor
  · exact le_min (add_nonneg hp.1 hq.1)
      (le_max_of_le_left (le_max_of_le_left hp.1))
  · exact (min_le_right _ _).trans (max_le (max_le hp.2 hq.2) (by norm_num))

/-- The recursively coupled Boolean cube using Yu's local maximum-entropy kernel. -/
noncomputable def dependentCubeCoupling : ∀ n (source : FiniteProbabilityLaw (BitCube n)),
    FiniteProbabilityLaw.SymmetricCoupling source
  | 0, source => FiniteProbabilityLaw.SymmetricCoupling.independent source
  | _ + 1, source =>
      FiniteProbabilityLaw.SymmetricCoupling.appendBool source
        (dependentCubeCoupling _ source.first)
        (fun u v ↦ dependentParameter
          (source.successParameter u) (source.successParameter v))
        (fun u v ↦ FiniteProbabilityLaw.dependentBernoulliCoupling
          (source.successParameter u) (source.successParameter v)
          (source.successParameter_mem u) (source.successParameter_mem v))
        (fun u v x y ↦ FiniteProbabilityLaw.dependentBernoulliCoupling_swap_weight
          (source.successParameter u) (source.successParameter v)
          (source.successParameter_mem u) (source.successParameter_mem v) x y)

/-- Union of two independent samples from a Boolean-cube law. -/
noncomputable def independentUnionLaw {n : ℕ} (source : FiniteProbabilityLaw (BitCube n)) :
    FiniteProbabilityLaw (BitCube n) :=
  (FiniteProbabilityLaw.SymmetricCoupling.independent source).output BitCube.union

/-- Union under the recursively dependent Yu coupling. -/
noncomputable def dependentUnionLaw {n : ℕ} (source : FiniteProbabilityLaw (BitCube n)) :
    FiniteProbabilityLaw (BitCube n) :=
  (dependentCubeCoupling n source).output BitCube.union

private theorem entropy_unit (law : FiniteProbabilityLaw Unit) : law.entropy = 0 := by
  have hweight : law.weight () = 1 := by simpa using law.weight_sum
  simp [FiniteProbabilityLaw.entropy, hweight]

namespace FiniteProbabilityLaw

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem independentOutput_entropy_gain (source : FiniteProbabilityLaw (ι × Bool))
    (merge : ι → ι → κ) :
    (∑ u, ∑ v, source.first.weight u * source.first.weight v *
        binEntropy (join (source.successParameter u) (source.successParameter v))) ≤
      ((SymmetricCoupling.independent source).output
          (fun x y ↦ (merge x.1 y.1, x.2 || y.2))).entropy -
        ((SymmetricCoupling.independent source.first).output merge).entropy := by
  let parameter : ι → ι → ℝ := fun u v ↦
    join (source.successParameter u) (source.successParameter v)
  let kernel := fun u v ↦ independentBernoulliCoupling
    (source.successParameter u) (source.successParameter v)
    (source.successParameter_mem u) (source.successParameter_mem v)
  let appended := SymmetricCoupling.appendBool source
    (SymmetricCoupling.independent source.first) parameter kernel
    (fun u v x y ↦ independentBernoulliCoupling_swap_weight
      (source.successParameter u) (source.successParameter v)
      (source.successParameter_mem u) (source.successParameter_mem v) x y)
  have hgain := appendBool_output_entropy_gain source
    (SymmetricCoupling.independent source.first) parameter
    (fun u v ↦ join_mem_Icc (source.successParameter_mem u) (source.successParameter_mem v))
    kernel
    (fun u v x y ↦ independentBernoulliCoupling_swap_weight
      (source.successParameter u) (source.successParameter v)
      (source.successParameter_mem u) (source.successParameter_mem v) x y) merge
  have hjoint : appended.joint = (SymmetricCoupling.independent source).joint := by
    exact SymmetricCoupling.appendBool_independent_joint source
  have houtput : appended.output (fun x y ↦ (merge x.1 y.1, x.2 || y.2)) =
      (SymmetricCoupling.independent source).output
        (fun x y ↦ (merge x.1 y.1, x.2 || y.2)) := by
    unfold SymmetricCoupling.output
    rw [hjoint]
  change (∑ uv, (SymmetricCoupling.independent source.first).joint.weight uv *
      binEntropy (parameter uv.1 uv.2)) ≤
    (appended.output (fun x y ↦ (merge x.1 y.1, x.2 || y.2))).entropy -
      ((SymmetricCoupling.independent source.first).output merge).entropy at hgain
  rw [houtput] at hgain
  dsimp only [parameter, kernel] at hgain
  rw [Fintype.sum_prod_type] at hgain
  simpa only [SymmetricCoupling.independent, product] using hgain

end FiniteProbabilityLaw

/-- The finite orbit certificate amplifies entropy for every Boolean-cube law whose coordinate
means lie below the abundance target. -/
theorem affineEntropyAmplification : ∀ n (source : FiniteProbabilityLaw (BitCube n)),
    CoordinateMeansLE n source →
      (1 - dependentShare) * (independentUnionLaw source).entropy +
          dependentShare * (dependentUnionLaw source).entropy ≥
        (1 + entropySlack) * source.entropy := by
  intro n
  induction n with
  | zero =>
      intro source _
      have hsource : source.entropy = 0 := entropy_unit source
      have hindependent : (independentUnionLaw source).entropy = 0 :=
        entropy_unit (independentUnionLaw source)
      have hdependent : (dependentUnionLaw source).entropy = 0 :=
        entropy_unit (dependentUnionLaw source)
      rw [hsource, hindependent, hdependent]
      norm_num
  | succ n ih =>
      intro source hmeans
      rcases hmeans with ⟨hprefixMeans, hfinalMean⟩
      let stem := dependentCubeCoupling n source.first
      let parameter : BitCube n → BitCube n → ℝ := fun u v ↦
        dependentParameter (source.successParameter u) (source.successParameter v)
      let kernel := fun u v ↦ FiniteProbabilityLaw.dependentBernoulliCoupling
        (source.successParameter u) (source.successParameter v)
        (source.successParameter_mem u) (source.successParameter_mem v)
      have hprefix := ih source.first hprefixMeans
      have hindependentGain := source.independentOutput_entropy_gain
        (BitCube.union : BitCube n → BitCube n → BitCube n)
      have hdependentGain := FiniteProbabilityLaw.appendBool_output_entropy_gain source stem
        parameter
        (fun u v ↦ dependentParameter_mem_Icc
          (source.successParameter_mem u) (source.successParameter_mem v))
        kernel
        (fun u v x y ↦ FiniteProbabilityLaw.dependentBernoulliCoupling_swap_weight
          (source.successParameter u) (source.successParameter v)
          (source.successParameter_mem u) (source.successParameter_mem v) x y)
        (BitCube.union : BitCube n → BitCube n → BitCube n)
      have hgap := source.conditionalOrbitYuGap stem hfinalMean
      have hchain := source.entropy_eq_first_add_conditional
      change
        (∑ u, ∑ v, source.first.weight u * source.first.weight v *
            binEntropy (join (source.successParameter u) (source.successParameter v))) ≤
          (independentUnionLaw source).entropy -
            (independentUnionLaw source.first).entropy at hindependentGain
      change
        (∑ z, stem.joint.weight z *
            dependentCost (source.successParameter z.1) (source.successParameter z.2)) ≤
          (dependentUnionLaw source).entropy -
            (dependentUnionLaw source.first).entropy at hdependentGain
      have hindependentScaled := mul_le_mul_of_nonneg_left hindependentGain
        (sub_nonneg.2 (show dependentShare ≤ 1 by norm_num [dependentShare]))
      have hdependentScaled := mul_le_mul_of_nonneg_left hdependentGain
        (show 0 ≤ dependentShare by norm_num [dependentShare])
      rw [hchain]
      linarith

/-- Closure under a binary operation keeps the output of any self-coupling inside the original
finite support. -/
theorem FiniteProbabilityLaw.SymmetricCoupling.output_weight_eq_zero_of_closed
    {n : ℕ} (family : Finset (BitCube n)) (hfamily : family.Nonempty)
    (hclosed : ∀ x ∈ family, ∀ y ∈ family, BitCube.union x y ∈ family)
    (coupling : FiniteProbabilityLaw.SymmetricCoupling
      (FiniteProbabilityLaw.uniformOn family hfamily))
    {z : BitCube n} (hz : z ∉ family) :
    (coupling.output BitCube.union).weight z = 0 := by
  classical
  simp only [FiniteProbabilityLaw.SymmetricCoupling.output,
    FiniteProbabilityLaw.map_weight]
  apply sum_eq_zero
  intro pair _
  by_cases hunion : BitCube.union pair.1 pair.2 = z
  · rw [if_pos hunion]
    by_cases hleft : pair.1 ∈ family
    · have hright : pair.2 ∉ family := by
        intro hright
        exact hz (hunion ▸ hclosed pair.1 hleft pair.2 hright)
      exact coupling.weight_eq_zero_of_right_source_eq_zero pair.1
        (FiniteProbabilityLaw.uniformOn_weight_of_not_mem family hfamily hright)
    · exact coupling.weight_eq_zero_of_left_source_eq_zero
        (FiniteProbabilityLaw.uniformOn_weight_of_not_mem family hfamily hleft) pair.2
  · rw [if_neg hunion]

/-- The checked finite orbit inequality rules out a union-closed family of at least two members
whose every coordinate frequency is at most the abundance target. -/
theorem unionClosed_not_coordinateMeansLE {n : ℕ} (family : Finset (BitCube n))
    (hfamily : family.Nonempty) (hcard : 2 ≤ family.card)
    (hclosed : ∀ x ∈ family, ∀ y ∈ family, BitCube.union x y ∈ family) :
    ¬CoordinateMeansLE n (FiniteProbabilityLaw.uniformOn family hfamily) := by
  intro hmeans
  let source := FiniteProbabilityLaw.uniformOn family hfamily
  have hamplification := affineEntropyAmplification n source hmeans
  have hindependentSupport : ∀ z, z ∉ family →
      (independentUnionLaw source).weight z = 0 := by
    intro z hz
    exact (FiniteProbabilityLaw.SymmetricCoupling.independent source)
      |>.output_weight_eq_zero_of_closed family hfamily hclosed hz
  have hdependentSupport : ∀ z, z ∉ family →
      (dependentUnionLaw source).weight z = 0 := by
    intro z hz
    exact (dependentCubeCoupling n source)
      |>.output_weight_eq_zero_of_closed family hfamily hclosed hz
  have hindependentCeiling := (independentUnionLaw source).entropy_le_log_card_of_support
    family hfamily hindependentSupport
  have hdependentCeiling := (dependentUnionLaw source).entropy_le_log_card_of_support
    family hfamily hdependentSupport
  have hsourceEntropy : source.entropy = log family.card :=
    FiniteProbabilityLaw.entropy_uniformOn family hfamily
  have hleftCeiling :
      (1 - dependentShare) * (independentUnionLaw source).entropy +
          dependentShare * (dependentUnionLaw source).entropy ≤ log family.card := by
    have hdependentShare : 0 ≤ dependentShare := by norm_num [dependentShare]
    have hindependentShare : 0 ≤ 1 - dependentShare := by norm_num [dependentShare]
    have hindependentScaled :=
      mul_le_mul_of_nonneg_left hindependentCeiling hindependentShare
    have hdependentScaled := mul_le_mul_of_nonneg_left hdependentCeiling hdependentShare
    nlinarith
  have hcardReal : (1 : ℝ) < family.card := by exact_mod_cast hcard
  have hlogPositive : 0 < log family.card := log_pos hcardReal
  have hstrict : log family.card < (1 + entropySlack) * log family.card := by
    have hslack : 0 < entropySlack := by norm_num [entropySlack]
    nlinarith
  rw [hsourceEntropy] at hamplification
  linarith

/-- Number of family members containing one Boolean-cube coordinate. -/
def coordinateFrequency {n : ℕ} (family : Finset (BitCube n))
    (coordinate : BitCube.Coordinate n) : ℕ :=
  (family.filter fun x ↦ BitCube.read x coordinate).card

theorem coordinateMean_uniformOn {n : ℕ} (family : Finset (BitCube n))
    (hfamily : family.Nonempty) (coordinate : BitCube.Coordinate n) :
    coordinateMean (FiniteProbabilityLaw.uniformOn family hfamily) coordinate =
      (coordinateFrequency family coordinate : ℝ) / family.card := by
  rw [coordinateMean]
  simp_rw [FiniteProbabilityLaw.uniformOn_weight]
  calc
    (∑ x, (if x ∈ family then (family.card : ℝ)⁻¹ else 0) *
        if BitCube.read x coordinate then 1 else 0) =
        ∑ x, if x ∈ family then (family.card : ℝ)⁻¹ *
          (if BitCube.read x coordinate then 1 else 0) else 0 := by
      apply sum_congr rfl
      intro x _
      by_cases hx : x ∈ family <;> simp [hx]
    _ = ∑ x ∈ family, (family.card : ℝ)⁻¹ *
        (if BitCube.read x coordinate then 1 else 0) := by
      rw [← Finset.sum_filter]
      simp
    _ = (family.card : ℝ)⁻¹ *
        ∑ x ∈ family, if BitCube.read x coordinate then 1 else 0 := by
      rw [mul_sum]
    _ = (family.card : ℝ)⁻¹ * coordinateFrequency family coordinate := by
      rw [Finset.sum_boole]
      rfl
    _ = (coordinateFrequency family coordinate : ℝ) / family.card := by
      rw [div_eq_mul_inv]
      ring

theorem unionClosed_exists_abundant_coordinate_of_two {n : ℕ}
    (family : Finset (BitCube n)) (hfamily : family.Nonempty) (hcard : 2 ≤ family.card)
    (hclosed : ∀ x ∈ family, ∀ y ∈ family, BitCube.union x y ∈ family) :
    ∃ coordinate, abundanceTarget * family.card <
      (coordinateFrequency family coordinate : ℝ) := by
  have hnot := unionClosed_not_coordinateMeansLE family hfamily hcard hclosed
  obtain ⟨coordinate, hmean⟩ :=
    exists_coordinateMean_gt_of_not (FiniteProbabilityLaw.uniformOn family hfamily) hnot
  rw [coordinateMean_uniformOn family hfamily coordinate] at hmean
  have hcardPositive : (0 : ℝ) < family.card := by exact_mod_cast hfamily.card_pos
  exact ⟨coordinate, (lt_div_iff₀ hcardPositive).1 hmean⟩

/-- Universal abundance theorem at `38234553336670271 / 100000000000000000` for finite
nontrivial union-closed Boolean families. -/
theorem unionClosed_exists_abundant_coordinate {n : ℕ} (family : Finset (BitCube n))
    (hfamily : family.Nonempty) (hnontrivial : family ≠ {BitCube.zero n})
    (hclosed : ∀ x ∈ family, ∀ y ∈ family, BitCube.union x y ∈ family) :
    ∃ coordinate, abundanceTarget * family.card <
      (coordinateFrequency family coordinate : ℝ) := by
  by_cases hcard : 2 ≤ family.card
  · exact unionClosed_exists_abundant_coordinate_of_two family hfamily hcard hclosed
  · have hcardPositive := hfamily.card_pos
    have hcardOne : family.card = 1 := by omega
    obtain ⟨member, hfamilyEq⟩ := card_eq_one.mp hcardOne
    have hmember : member ≠ BitCube.zero n := by
      intro hmember
      apply hnontrivial
      rw [hfamilyEq, hmember]
    obtain ⟨coordinate, hcoordinate⟩ := BitCube.exists_true_coordinate hmember
    refine ⟨coordinate, ?_⟩
    rw [hfamilyEq]
    have hfrequency : coordinateFrequency {member} coordinate = 1 := by
      rw [coordinateFrequency, Finset.filter_eq_self.2]
      · exact Finset.card_singleton member
      · intro x hx
        rw [Finset.mem_singleton.mp hx]
        exact hcoordinate
    rw [hfrequency]
    simp only [Finset.card_singleton, Nat.cast_one, mul_one]
    norm_num [abundanceTarget]

end Frankl
