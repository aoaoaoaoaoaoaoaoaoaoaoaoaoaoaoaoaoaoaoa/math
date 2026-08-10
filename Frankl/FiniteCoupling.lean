import Frankl.ConditionalEntropy
import Frankl.HalfSupport

namespace Frankl

open Finset Real Set

namespace FiniteProbabilityLaw

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

private theorem sum_pair_indicator (g : ι → ι → ℝ) (u v : ι) :
    (∑ x, ∑ y, if x = u ∧ y = v then g x y else 0) = g u v := by
  rw [sum_eq_single u]
  · rw [sum_eq_single v]
    · simp
    · intro y _ hyv
      simp [hyv]
    · simp
  · intro x _ hxu
    apply sum_eq_zero
    intro y _
    simp [hxu]
  · simp

/-- A symmetric self-coupling of a finite probability law. -/
structure SymmetricCoupling (source : FiniteProbabilityLaw ι) where
  /-- The joint law. -/
  joint : FiniteProbabilityLaw (ι × ι)
  first_eq : joint.first = source
  second_eq : joint.second = source
  swap_weight : ∀ i j, joint.weight (i, j) = joint.weight (j, i)

namespace SymmetricCoupling

/-- The independent self-coupling. -/
noncomputable def independent (source : FiniteProbabilityLaw ι) :
    SymmetricCoupling source where
  joint := source.product source
  first_eq := first_product source source
  second_eq := second_product source source
  swap_weight i j := by
    dsimp only [product]
    ring

theorem sum_left {source : FiniteProbabilityLaw ι} (coupling : SymmetricCoupling source)
    (observable : ι → ℝ) :
    (∑ z, coupling.joint.weight z * observable z.1) =
      ∑ i, source.weight i * observable i := by
  classical
  rw [Fintype.sum_prod_type]
  calc
    (∑ i, ∑ j, coupling.joint.weight (i, j) * observable i) =
        ∑ i, coupling.joint.first.weight i * observable i := by
      apply sum_congr rfl
      intro i _
      rw [first_weight, sum_mul]
    _ = ∑ i, source.weight i * observable i := by rw [coupling.first_eq]

theorem sum_right {source : FiniteProbabilityLaw ι} (coupling : SymmetricCoupling source)
    (observable : ι → ℝ) :
    (∑ z, coupling.joint.weight z * observable z.2) =
      ∑ i, source.weight i * observable i := by
  classical
  rw [Fintype.sum_prod_type]
  calc
    (∑ i, ∑ j, coupling.joint.weight (i, j) * observable j) =
        ∑ j, coupling.joint.second.weight j * observable j := by
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      rw [second_weight, sum_mul]
    _ = ∑ j, source.weight j * observable j := by rw [coupling.second_eq]

theorem weight_eq_zero_of_left_source_eq_zero {source : FiniteProbabilityLaw ι}
    (coupling : SymmetricCoupling source) {i : ι} (hi : source.weight i = 0) (j : ι) :
    coupling.joint.weight (i, j) = 0 := by
  have hsum : ∑ k, coupling.joint.weight (i, k) = 0 := by
    rw [← first_weight, coupling.first_eq, hi]
  exact (sum_eq_zero_iff_of_nonneg
    (fun k _ ↦ coupling.joint.weight_nonneg (i, k))).1 hsum j (mem_univ j)

theorem weight_eq_zero_of_right_source_eq_zero {source : FiniteProbabilityLaw ι}
    (coupling : SymmetricCoupling source) (i : ι) {j : ι} (hj : source.weight j = 0) :
    coupling.joint.weight (i, j) = 0 := by
  have hsum : ∑ k, coupling.joint.weight (k, j) = 0 := by
    rw [← second_weight, coupling.second_eq, hj]
  exact (sum_eq_zero_iff_of_nonneg
    (fun k _ ↦ coupling.joint.weight_nonneg (k, j))).1 hsum i (mem_univ i)

end SymmetricCoupling

/-- A coupling of two Bernoulli laws together with its Boolean-OR parameter. -/
structure BernoulliCoupling (p q parameter : ℝ)
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) where
  /-- The joint Boolean law. -/
  joint : FiniteProbabilityLaw (Bool × Bool)
  first_eq : joint.first = bernoulli p hp
  second_eq : joint.second = bernoulli q hq
  or_true : (∑ z, if (z.1 || z.2) = true then joint.weight z else 0) = parameter

/-- Independent Bernoulli coupling. -/
noncomputable def independentBernoulliCoupling (p q : ℝ)
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) :
    BernoulliCoupling p q (join p q) hp hq where
  joint := (bernoulli p hp).product (bernoulli q hq)
  first_eq := first_product _ _
  second_eq := second_product _ _
  or_true := by
    simp [Fintype.sum_prod_type, Fintype.sum_bool, product, join]
    ring

theorem independentBernoulliCoupling_swap_weight (p q : ℝ)
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) (x y : Bool) :
    (independentBernoulliCoupling p q hp hq).joint.weight (x, y) =
      (independentBernoulliCoupling q p hq hp).joint.weight (y, x) := by
  simp only [independentBernoulliCoupling, product]
  ring

private theorem dependentParameter_lower_max {p q : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) :
    max p q ≤ dependentParameter p q := by
  rw [dependentParameter]
  exact le_min (max_le (le_add_of_nonneg_right hq.1) (le_add_of_nonneg_left hp.1))
    (le_max_left _ _)

private theorem dependentParameter_le_add {p q : ℝ} :
    dependentParameter p q ≤ p + q := by
  exact min_le_left _ _

private theorem dependentParameter_le_one {p q : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) :
    dependentParameter p q ≤ 1 := by
  rw [dependentParameter]
  refine (min_le_right _ _).trans ?_
  exact max_le (max_le hp.2 hq.2) (by norm_num)

/-- Yu's maximum-entropy local Bernoulli coupling. -/
noncomputable def dependentBernoulliCoupling (p q : ℝ)
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) :
    BernoulliCoupling p q (dependentParameter p q) hp hq := by
  let d := dependentParameter p q
  have hdMax : max p q ≤ d := dependentParameter_lower_max hp hq
  have hdAdd : d ≤ p + q := dependentParameter_le_add
  have hdOne : d ≤ 1 := dependentParameter_le_one hp hq
  let joint : FiniteProbabilityLaw (Bool × Bool) :=
    { weight := fun z ↦ match z with
        | (false, false) => 1 - d
        | (false, true) => d - p
        | (true, false) => d - q
        | (true, true) => p + q - d
      weight_nonneg := fun z ↦ by
        rcases z with ⟨x, y⟩
        cases x <;> cases y <;> simp only
        · exact sub_nonneg.2 hdOne
        · exact sub_nonneg.2 ((le_max_left p q).trans hdMax)
        · exact sub_nonneg.2 ((le_max_right p q).trans hdMax)
        · exact sub_nonneg.2 hdAdd
      weight_sum := by
        simp only [Fintype.sum_prod_type, Fintype.sum_bool]
        ring }
  refine
    { joint := joint
      first_eq := ?_
      second_eq := ?_
      or_true := ?_ }
  · apply ext
    funext b
    cases b <;> simp [first_weight, joint, bernoulli, Fintype.sum_bool]
  · apply ext
    funext b
    cases b <;> simp [second_weight, joint, bernoulli, Fintype.sum_bool]
  · simp [joint, Fintype.sum_prod_type, Fintype.sum_bool]

theorem dependentBernoulliCoupling_swap_weight (p q : ℝ)
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) (x y : Bool) :
    (dependentBernoulliCoupling p q hp hq).joint.weight (x, y) =
      (dependentBernoulliCoupling q p hq hp).joint.weight (y, x) := by
  cases x <;> cases y <;>
    simp [dependentBernoulliCoupling, dependentParameter, add_comm, max_comm]

/-- Append one coupled Boolean coordinate to a coupling of prefixes. -/
noncomputable def SymmetricCoupling.appendBool
    (source : FiniteProbabilityLaw (ι × Bool))
    (stem : SymmetricCoupling source.first)
    (parameter : ι → ι → ℝ)
    (kernel : ∀ u v, BernoulliCoupling
      (source.successParameter u) (source.successParameter v)
      (parameter u v)
      (source.successParameter_mem u) (source.successParameter_mem v))
    (hswap : ∀ u v x y,
      (kernel u v).joint.weight (x, y) = (kernel v u).joint.weight (y, x)) :
    SymmetricCoupling source := by
  let raw := stem.joint.extend fun uv ↦ (kernel uv.1 uv.2).joint
  let regroup : ((ι × ι) × (Bool × Bool)) → ((ι × Bool) × (ι × Bool)) :=
    fun z ↦ ((z.1.1, z.2.1), (z.1.2, z.2.2))
  let joint := raw.map regroup
  have hjointWeight : ∀ u v x y,
      joint.weight ((u, x), (v, y)) =
        stem.joint.weight (u, v) * (kernel u v).joint.weight (x, y) := by
    intro u v x y
    classical
    cases x <;> cases y <;>
      simp only [joint, map_weight, raw, extend, regroup, Fintype.sum_prod_type,
        Fintype.sum_bool, Bool.false_or, Bool.true_or, Bool.or_false, Bool.or_true,
        Bool.false_eq_true, Bool.true_eq_false, if_false, if_true, Prod.mk.injEq,
        true_and, and_true, false_and, and_false, zero_add, add_zero]
    all_goals exact sum_pair_indicator _ u v
  refine
    { joint := joint
      first_eq := ?_
      second_eq := ?_
      swap_weight := ?_ }
  · apply ext
    funext z
    rcases z with ⟨u, x⟩
    rw [first_weight, Fintype.sum_prod_type]
    simp_rw [hjointWeight]
    calc
      (∑ v, ∑ y, stem.joint.weight (u, v) * (kernel u v).joint.weight (x, y)) =
          ∑ v, stem.joint.weight (u, v) * (kernel u v).joint.first.weight x := by
        apply sum_congr rfl
        intro v _
        rw [first_weight]
        rw [mul_sum]
      _ = ∑ v, stem.joint.weight (u, v) *
          (bernoulli (source.successParameter u) (source.successParameter_mem u)).weight x := by
        apply sum_congr rfl
        intro v _
        rw [(kernel u v).first_eq]
      _ = stem.joint.first.weight u *
          (bernoulli (source.successParameter u) (source.successParameter_mem u)).weight x := by
        rw [first_weight, sum_mul]
      _ = source.first.weight u *
          (bernoulli (source.successParameter u) (source.successParameter_mem u)).weight x := by
        rw [stem.first_eq]
      _ = source.weight (u, x) := by
        simpa only [extend] using congrArg
          (fun law : FiniteProbabilityLaw (ι × Bool) ↦ law.weight (u, x))
          source.extend_successParameter
  · apply ext
    funext z
    rcases z with ⟨v, y⟩
    rw [second_weight, Fintype.sum_prod_type]
    simp_rw [hjointWeight]
    calc
      (∑ u, ∑ x, stem.joint.weight (u, v) * (kernel u v).joint.weight (x, y)) =
          ∑ u, stem.joint.weight (u, v) * (kernel u v).joint.second.weight y := by
        apply sum_congr rfl
        intro u _
        rw [second_weight]
        rw [mul_sum]
      _ = ∑ u, stem.joint.weight (u, v) *
          (bernoulli (source.successParameter v) (source.successParameter_mem v)).weight y := by
        apply sum_congr rfl
        intro u _
        rw [(kernel u v).second_eq]
      _ = stem.joint.second.weight v *
          (bernoulli (source.successParameter v) (source.successParameter_mem v)).weight y := by
        rw [second_weight, sum_mul]
      _ = source.first.weight v *
          (bernoulli (source.successParameter v) (source.successParameter_mem v)).weight y := by
        rw [stem.second_eq]
      _ = source.weight (v, y) := by
        simpa only [extend] using congrArg
          (fun law : FiniteProbabilityLaw (ι × Bool) ↦ law.weight (v, y))
          source.extend_successParameter
  · intro z w
    rcases z with ⟨u, x⟩
    rcases w with ⟨v, y⟩
    rw [hjointWeight, hjointWeight, stem.swap_weight, hswap]

theorem SymmetricCoupling.appendBool_joint_weight
    (source : FiniteProbabilityLaw (ι × Bool))
    (stem : SymmetricCoupling source.first) (parameter : ι → ι → ℝ)
    (kernel : ∀ u v, BernoulliCoupling
      (source.successParameter u) (source.successParameter v) (parameter u v)
      (source.successParameter_mem u) (source.successParameter_mem v))
    (hswap : ∀ u v x y,
      (kernel u v).joint.weight (x, y) = (kernel v u).joint.weight (y, x))
    (u v : ι) (x y : Bool) :
    (SymmetricCoupling.appendBool source stem parameter kernel hswap).joint.weight
        ((u, x), (v, y)) =
      stem.joint.weight (u, v) * (kernel u v).joint.weight (x, y) := by
  classical
  cases x <;> cases y <;>
    simp only [SymmetricCoupling.appendBool, map_weight, extend, Fintype.sum_prod_type,
      Fintype.sum_bool, Bool.false_or, Bool.true_or, Bool.or_false, Bool.or_true,
      Bool.false_eq_true, Bool.true_eq_false, if_false, if_true, Prod.mk.injEq,
      true_and, and_true, false_and, and_false, zero_add, add_zero]
  all_goals exact sum_pair_indicator _ u v

theorem SymmetricCoupling.appendBool_independent_joint
    (source : FiniteProbabilityLaw (ι × Bool)) :
    (SymmetricCoupling.appendBool source (SymmetricCoupling.independent source.first)
      (fun u v ↦ join (source.successParameter u) (source.successParameter v))
      (fun u v ↦ independentBernoulliCoupling
        (source.successParameter u) (source.successParameter v)
        (source.successParameter_mem u) (source.successParameter_mem v))
      (fun u v x y ↦ independentBernoulliCoupling_swap_weight _ _ _ _ x y)).joint =
      (SymmetricCoupling.independent source).joint := by
  apply ext
  funext z
  rcases z with ⟨⟨u, x⟩, ⟨v, y⟩⟩
  rw [SymmetricCoupling.appendBool_joint_weight]
  simp only [SymmetricCoupling.independent, product, independentBernoulliCoupling]
  have hu := congrArg
    (fun law : FiniteProbabilityLaw (ι × Bool) ↦ law.weight (u, x))
    source.extend_successParameter
  have hv := congrArg
    (fun law : FiniteProbabilityLaw (ι × Bool) ↦ law.weight (v, y))
    source.extend_successParameter
  simp only [extend] at hu hv
  rw [← hu, ← hv]
  ring

/-- Push a coupling through a binary operation on its source space. -/
noncomputable def SymmetricCoupling.output {source : FiniteProbabilityLaw ι}
    (coupling : SymmetricCoupling source)
    (merge : ι → ι → κ) : FiniteProbabilityLaw κ :=
  coupling.joint.map fun z ↦ merge z.1 z.2

/-- The joint law of the detailed prefix pair and the OR of its appended bits. -/
noncomputable def coupledBitOr
    (source : FiniteProbabilityLaw (ι × Bool))
    (stem : SymmetricCoupling source.first) (parameter : ι → ι → ℝ)
    (kernel : ∀ u v, BernoulliCoupling
      (source.successParameter u) (source.successParameter v) (parameter u v)
      (source.successParameter_mem u) (source.successParameter_mem v)) :
    FiniteProbabilityLaw ((ι × ι) × Bool) :=
  (stem.joint.extend fun uv ↦ (kernel uv.1 uv.2).joint).map
    fun z ↦ (z.1, z.2.1 || z.2.2)

theorem coupledBitOr_weight_true
    (source : FiniteProbabilityLaw (ι × Bool))
    (stem : SymmetricCoupling source.first) (parameter : ι → ι → ℝ)
    (kernel : ∀ u v, BernoulliCoupling
      (source.successParameter u) (source.successParameter v) (parameter u v)
      (source.successParameter_mem u) (source.successParameter_mem v)) (u v : ι) :
    (coupledBitOr source stem parameter kernel).weight ((u, v), true) =
      stem.joint.weight (u, v) * parameter u v := by
  classical
  simp only [coupledBitOr, map_weight]
  rw [Fintype.sum_prod_type]
  rw [sum_eq_single (u, v)]
  · simp only [Prod.mk.injEq, true_and, extend]
    calc
      (∑ x, if (x.1 || x.2) = true then
          stem.joint.weight (u, v) * (kernel u v).joint.weight x else 0) =
          stem.joint.weight (u, v) *
            ∑ x, if (x.1 || x.2) = true then (kernel u v).joint.weight x else 0 := by
        rw [mul_sum]
        apply sum_congr rfl
        intro bits _
        by_cases hor : (bits.1 || bits.2) = true <;> simp [hor]
      _ = stem.joint.weight (u, v) * parameter u v := by
        rw [(kernel u v).or_true]
  · intro state _ hstate
    apply sum_eq_zero
    intro bits _
    rw [if_neg]
    intro h
    exact hstate (congrArg Prod.fst h)
  · simp

@[simp]
theorem coupledBitOr_first
    (source : FiniteProbabilityLaw (ι × Bool))
    (stem : SymmetricCoupling source.first) (parameter : ι → ι → ℝ)
    (kernel : ∀ u v, BernoulliCoupling
      (source.successParameter u) (source.successParameter v) (parameter u v)
      (source.successParameter_mem u) (source.successParameter_mem v)) :
    (coupledBitOr source stem parameter kernel).first = stem.joint := by
  change ((stem.joint.extend fun uv ↦ (kernel uv.1 uv.2).joint).map
      (fun z ↦ (z.1, z.2.1 || z.2.2))).first = stem.joint
  rw [first, map_comp]
  change (stem.joint.extend fun uv ↦ (kernel uv.1 uv.2).joint).map Prod.fst = stem.joint
  exact first_extend stem.joint _

theorem coupledBitOr_eq_extend
    (source : FiniteProbabilityLaw (ι × Bool))
    (stem : SymmetricCoupling source.first) (parameter : ι → ι → ℝ)
    (hparameter : ∀ u v, parameter u v ∈ Icc (0 : ℝ) 1)
    (kernel : ∀ u v, BernoulliCoupling
      (source.successParameter u) (source.successParameter v) (parameter u v)
      (source.successParameter_mem u) (source.successParameter_mem v)) :
    coupledBitOr source stem parameter kernel =
      stem.joint.extend fun uv ↦ bernoulli (parameter uv.1 uv.2)
        (hparameter uv.1 uv.2) := by
  apply ext
  funext z
  rcases z with ⟨⟨u, v⟩, b⟩
  cases b
  · have htotal :
        (coupledBitOr source stem parameter kernel).weight ((u, v), false) +
            (coupledBitOr source stem parameter kernel).weight ((u, v), true) =
          stem.joint.weight (u, v) := by
        rw [add_comm, ← Fintype.sum_bool
          (fun b ↦ (coupledBitOr source stem parameter kernel).weight ((u, v), b))]
        rw [← first_weight, coupledBitOr_first]
    rw [coupledBitOr_weight_true] at htotal
    simp only [extend, bernoulli_weight_false]
    linarith
  · rw [coupledBitOr_weight_true]
    simp only [extend, bernoulli_weight_true]

theorem entropy_coupledBitOr
    (source : FiniteProbabilityLaw (ι × Bool))
    (stem : SymmetricCoupling source.first) (parameter : ι → ι → ℝ)
    (hparameter : ∀ u v, parameter u v ∈ Icc (0 : ℝ) 1)
    (kernel : ∀ u v, BernoulliCoupling
      (source.successParameter u) (source.successParameter v) (parameter u v)
      (source.successParameter_mem u) (source.successParameter_mem v)) :
    (coupledBitOr source stem parameter kernel).entropy = stem.joint.entropy +
      ∑ uv, stem.joint.weight uv * binEntropy (parameter uv.1 uv.2) := by
  rw [coupledBitOr_eq_extend source stem parameter hparameter kernel, entropy_extend]
  simp only [entropy_bernoulli]

theorem appendBool_output_eq_coarsen
    (source : FiniteProbabilityLaw (ι × Bool))
    (stem : SymmetricCoupling source.first) (parameter : ι → ι → ℝ)
    (kernel : ∀ u v, BernoulliCoupling
      (source.successParameter u) (source.successParameter v) (parameter u v)
      (source.successParameter_mem u) (source.successParameter_mem v))
    (hswap : ∀ u v x y,
      (kernel u v).joint.weight (x, y) = (kernel v u).joint.weight (y, x))
    (merge : ι → ι → κ) :
    (SymmetricCoupling.appendBool source stem parameter kernel hswap).output
        (fun x y ↦ (merge x.1 y.1, x.2 || y.2)) =
      (coupledBitOr source stem parameter kernel).coarsenFirst
        (fun uv ↦ merge uv.1 uv.2) := by
  classical
  simp only [SymmetricCoupling.output, SymmetricCoupling.appendBool, coupledBitOr,
    coarsenFirst, map_comp]
  congr 1

theorem appendBool_output_entropy_gain
    (source : FiniteProbabilityLaw (ι × Bool))
    (stem : SymmetricCoupling source.first) (parameter : ι → ι → ℝ)
    (hparameter : ∀ u v, parameter u v ∈ Icc (0 : ℝ) 1)
    (kernel : ∀ u v, BernoulliCoupling
      (source.successParameter u) (source.successParameter v) (parameter u v)
      (source.successParameter_mem u) (source.successParameter_mem v))
    (hswap : ∀ u v x y,
      (kernel u v).joint.weight (x, y) = (kernel v u).joint.weight (y, x))
    (merge : ι → ι → κ) :
    (∑ uv, stem.joint.weight uv * binEntropy (parameter uv.1 uv.2)) ≤
      ((SymmetricCoupling.appendBool source stem parameter kernel hswap).output
          (fun x y ↦ (merge x.1 y.1, x.2 || y.2))).entropy -
        (stem.output merge).entropy := by
  let bitOrLaw := coupledBitOr source stem parameter kernel
  let coarsened := bitOrLaw.coarsenFirst fun uv ↦ merge uv.1 uv.2
  have hconditional := bitOrLaw.entropy_coarsenFirst_sub_first_ge
    (fun uv ↦ merge uv.1 uv.2)
  have hbitOrEntropy := entropy_coupledBitOr source stem parameter hparameter kernel
  have hbitOrFirst := coupledBitOr_first source stem parameter kernel
  have hcoarsenedFirst : coarsened.first = stem.output merge := by
    dsimp only [coarsened, bitOrLaw]
    rw [coarsenFirst_first, coupledBitOr_first]
    rfl
  have hfull :
      (SymmetricCoupling.appendBool source stem parameter kernel hswap).output
          (fun x y ↦ (merge x.1 y.1, x.2 || y.2)) = coarsened := by
    exact appendBool_output_eq_coarsen source stem parameter kernel hswap merge
  calc
    (∑ uv, stem.joint.weight uv * binEntropy (parameter uv.1 uv.2)) =
        bitOrLaw.entropy - bitOrLaw.first.entropy := by
      rw [hbitOrEntropy, hbitOrFirst]
      ring
    _ = ∑ uv, bitOrLaw.first.weight uv *
        binEntropy (bitOrLaw.successParameter uv) := by
      rw [bitOrLaw.entropy_eq_first_add_conditional]
      ring
    _ ≤ coarsened.entropy - coarsened.first.entropy := hconditional
    _ = ((SymmetricCoupling.appendBool source stem parameter kernel hswap).output
          (fun x y ↦ (merge x.1 y.1, x.2 || y.2))).entropy -
        (stem.output merge).entropy := by
      rw [hfull, hcoarsenedFirst]

end FiniteProbabilityLaw

end Frankl
