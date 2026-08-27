import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Fintype.Pi

namespace Frankl

open Finset Real Set

/-- A probability law on a finite indexing type, represented by real masses. -/
structure FiniteProbabilityLaw (ι : Type*) [Fintype ι] where
  /-- The mass of each outcome. -/
  weight : ι → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : ∑ i, weight i = 1

namespace FiniteProbabilityLaw

variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq τ]

omit [DecidableEq ι] in
@[ext]
theorem ext {left right : FiniteProbabilityLaw ι} (hweight : left.weight = right.weight) :
    left = right := by
  cases left
  cases right
  simp_all

theorem weight_le_one (law : FiniteProbabilityLaw ι) (i : ι) : law.weight i ≤ 1 := by
  have hrest : 0 ≤ ∑ j ∈ univ.erase i, law.weight j :=
    sum_nonneg fun j _ ↦ law.weight_nonneg j
  rw [← law.weight_sum]
  rw [← Finset.sum_erase_add Finset.univ law.weight (Finset.mem_univ i)]
  linarith

/-- Shannon entropy in nats. -/
noncomputable def entropy (law : FiniteProbabilityLaw ι) : ℝ :=
  ∑ i, negMulLog (law.weight i)

theorem entropy_nonneg (law : FiniteProbabilityLaw ι) : 0 ≤ law.entropy := by
  exact sum_nonneg fun i _ ↦ negMulLog_nonneg (law.weight_nonneg i) (law.weight_le_one i)

/-- The Bernoulli law with the stated success probability. -/
noncomputable def bernoulli (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    FiniteProbabilityLaw Bool where
  weight b := if b then p else 1 - p
  weight_nonneg b := by
    cases b <;> simp [hp.1, sub_nonneg.2 hp.2]
  weight_sum := by
    simp

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq τ] in
@[simp]
theorem bernoulli_weight_false (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    (bernoulli p hp).weight false = 1 - p := rfl

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq τ] in
@[simp]
theorem bernoulli_weight_true (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    (bernoulli p hp).weight true = p := rfl

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq τ] in
@[simp]
theorem entropy_bernoulli (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    (bernoulli p hp).entropy = binEntropy p := by
  simp [entropy, binEntropy_eq_negMulLog_add_negMulLog_one_sub]

/-- The uniform probability law on a nonempty finite set. -/
noncomputable def uniformOn (s : Finset ι) (hs : s.Nonempty) : FiniteProbabilityLaw ι := by
  classical
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  exact
    { weight := fun i ↦ if i ∈ s then (s.card : ℝ)⁻¹ else 0
      weight_nonneg := fun i ↦ by
        by_cases hi : i ∈ s <;> simp [hi]
      weight_sum := by
        rw [← sum_filter]
        simp [hcard] }

theorem uniformOn_weight (s : Finset ι) (hs : s.Nonempty) (i : ι) :
    (uniformOn s hs).weight i = if i ∈ s then (s.card : ℝ)⁻¹ else 0 := rfl

theorem uniformOn_weight_of_mem (s : Finset ι) (hs : s.Nonempty) {i : ι} (hi : i ∈ s) :
    (uniformOn s hs).weight i = (s.card : ℝ)⁻¹ := by
  simp [uniformOn_weight, hi]

theorem uniformOn_weight_of_not_mem (s : Finset ι) (hs : s.Nonempty) {i : ι} (hi : i ∉ s) :
    (uniformOn s hs).weight i = 0 := by
  simp [uniformOn_weight, hi]

theorem entropy_uniformOn (s : Finset ι) (hs : s.Nonempty) :
    (uniformOn s hs).entropy = log s.card := by
  classical
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  rw [entropy]
  simp_rw [uniformOn_weight]
  simp_rw [apply_ite, negMulLog_zero]
  rw [Finset.sum_ite]
  simp only [sum_const_zero, add_zero, filter_mem_eq_inter, Finset.univ_inter, sum_const,
    nsmul_eq_mul]
  rw [negMulLog_def]
  dsimp only
  rw [Real.log_inv]
  field_simp [hcard]

/-- The point law at one outcome. -/
def point (i : ι) : FiniteProbabilityLaw ι := by
  exact
    { weight := fun j ↦ if j = i then 1 else 0
      weight_nonneg := fun j ↦ by by_cases hji : j = i <;> simp [hji]
      weight_sum := by simp }

/-- Push a finite probability law through a function. -/
def map (law : FiniteProbabilityLaw ι) (f : ι → κ) :
    FiniteProbabilityLaw κ := by
  exact
    { weight := fun y ↦ ∑ x, if f x = y then law.weight x else 0
      weight_nonneg := fun y ↦ sum_nonneg fun x _ ↦ by
        split
        · exact law.weight_nonneg x
        · norm_num
      weight_sum := by
        calc
          (∑ y, ∑ x, (if f x = y then law.weight x else 0)) =
              ∑ x, ∑ y, (if f x = y then law.weight x else 0) := sum_comm
          _ = (∑ x, law.weight x) := by
            apply sum_congr rfl
            intro x _
            simp
          _ = 1 := law.weight_sum }

omit [DecidableEq ι] in
theorem map_weight (law : FiniteProbabilityLaw ι) (f : ι → κ) (y : κ) :
    (law.map f).weight y = ∑ x, if f x = y then law.weight x else 0 := rfl

omit [DecidableEq ι] in
theorem map_comp (law : FiniteProbabilityLaw ι) (f : ι → κ) (g : κ → τ) :
    (law.map f).map g = law.map (g ∘ f) := by
  classical
  apply ext
  funext z
  simp only [map_weight, Function.comp_apply]
  calc
    (∑ y, if g y = z then (∑ x, if f x = y then law.weight x else 0) else 0) =
        ∑ y, ∑ x, (if g y = z then (if f x = y then law.weight x else 0) else 0) := by
      apply sum_congr rfl
      intro y _
      by_cases hgy : g y = z <;> simp [hgy]
    _ = ∑ x, ∑ y, (if g y = z then (if f x = y then law.weight x else 0) else 0) :=
      sum_comm
    _ = (∑ x, if g (f x) = z then law.weight x else 0) := by
      apply sum_congr rfl
      intro x _
      rw [sum_eq_single (f x)]
      · simp
      · intro y _ hy
        simp [Ne.symm hy]
      · simp

@[simp]
theorem map_id (law : FiniteProbabilityLaw ι) : law.map id = law := by
  classical
  apply ext
  funext x
  simp [map_weight, id_eq]

/-- The independent product of two finite probability laws. -/
noncomputable def product (left : FiniteProbabilityLaw ι)
    (right : FiniteProbabilityLaw κ) : FiniteProbabilityLaw (ι × κ) where
  weight z := left.weight z.1 * right.weight z.2
  weight_nonneg z := mul_nonneg (left.weight_nonneg z.1) (right.weight_nonneg z.2)
  weight_sum := by
    rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum]
    simp only [right.weight_sum, mul_one]
    exact left.weight_sum

/-- Extend a law by a finite transition kernel, retaining the source outcome. -/
noncomputable def extend (law : FiniteProbabilityLaw ι)
    (kernel : ι → FiniteProbabilityLaw κ) : FiniteProbabilityLaw (ι × κ) where
  weight z := law.weight z.1 * (kernel z.1).weight z.2
  weight_nonneg z := mul_nonneg (law.weight_nonneg z.1) ((kernel z.1).weight_nonneg z.2)
  weight_sum := by
    rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum, FiniteProbabilityLaw.weight_sum, mul_one]
    exact law.weight_sum

omit [DecidableEq ι] [DecidableEq κ] in
theorem entropy_extend (law : FiniteProbabilityLaw ι)
    (kernel : ι → FiniteProbabilityLaw κ) :
    (law.extend kernel).entropy = law.entropy + ∑ i, law.weight i * (kernel i).entropy := by
  classical
  simp only [entropy, extend, negMulLog_mul, Fintype.sum_prod_type]
  calc
    ∑ i, ∑ k,
        ((kernel i).weight k * negMulLog (law.weight i) +
          law.weight i * negMulLog ((kernel i).weight k)) =
        ∑ i, (negMulLog (law.weight i) + law.weight i * (kernel i).entropy) := by
      apply sum_congr rfl
      intro i _
      rw [sum_add_distrib]
      simp only [← sum_mul, (kernel i).weight_sum, one_mul, ← mul_sum, entropy]
    _ = law.entropy + ∑ i, law.weight i * (kernel i).entropy := by
      rw [sum_add_distrib]
      rfl

omit [DecidableEq ι] [DecidableEq κ] in
theorem entropy_product (left : FiniteProbabilityLaw ι)
    (right : FiniteProbabilityLaw κ) :
    (left.product right).entropy = left.entropy + right.entropy := by
  rw [show left.product right = left.extend (fun _ ↦ right) by rfl, entropy_extend]
  simp only [← sum_mul, left.weight_sum, one_mul]

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq τ] in
/-- A probability law on `N` outcomes has entropy at most `log N`. -/
theorem entropy_le_log_card [Nonempty ι] (law : FiniteProbabilityLaw ι) :
    law.entropy ≤ log (Fintype.card ι) := by
  let cardinal : ℝ := Fintype.card ι
  have hcardinal : 0 < cardinal := by
    dsimp [cardinal]
    exact_mod_cast Fintype.card_pos
  have hweights : ∀ i ∈ (univ : Finset ι), 0 ≤ cardinal⁻¹ := by
    intro _ _
    positivity
  have hweightSum : ∑ _ : ι, cardinal⁻¹ = 1 := by
    simp only [sum_const, card_univ, nsmul_eq_mul, cardinal]
    exact mul_inv_cancel₀ hcardinal.ne'
  have hpoints : ∀ i ∈ (univ : Finset ι), law.weight i ∈ Ici (0 : ℝ) := by
    exact fun i _ ↦ law.weight_nonneg i
  have hjensen := concaveOn_negMulLog.le_map_sum hweights hweightSum hpoints
  dsimp only [smul_eq_mul, Function.comp_apply] at hjensen
  have hmean : ∑ i, cardinal⁻¹ * law.weight i = cardinal⁻¹ := by
    rw [← mul_sum, law.weight_sum, mul_one]
  rw [hmean] at hjensen
  have hscaled := mul_le_mul_of_nonneg_left hjensen hcardinal.le
  rw [mul_sum] at hscaled
  simp_rw [← mul_assoc, mul_inv_cancel₀ hcardinal.ne', one_mul] at hscaled
  rw [negMulLog_def] at hscaled
  dsimp only at hscaled
  rw [Real.log_inv] at hscaled
  calc
    law.entropy = ∑ i, negMulLog (law.weight i) := rfl
    _ ≤ cardinal * (-cardinal⁻¹ * -log cardinal) := hscaled
    _ = log (Fintype.card ι) := by
      dsimp [cardinal]
      field_simp

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq τ] in
/-- An `M`-point support bounds entropy by `log M`. -/
theorem entropy_le_log_card_of_support (law : FiniteProbabilityLaw ι) (s : Finset ι)
    (hs : s.Nonempty) (hzero : ∀ i, i ∉ s → law.weight i = 0) :
    law.entropy ≤ log s.card := by
  let cardinal : ℝ := s.card
  have hcardinal : 0 < cardinal := by
    dsimp [cardinal]
    exact_mod_cast hs.card_pos
  have hmass : ∑ i ∈ s, law.weight i = 1 := by
    rw [← law.weight_sum]
    exact sum_subset (subset_univ s) fun i _ hi ↦ hzero i hi
  have hweights : ∀ i ∈ s, 0 ≤ cardinal⁻¹ := by
    intro _ _
    positivity
  have hweightSum : ∑ _ ∈ s, cardinal⁻¹ = 1 := by
    simp only [sum_const, nsmul_eq_mul, cardinal]
    exact mul_inv_cancel₀ hcardinal.ne'
  have hpoints : ∀ i ∈ s, law.weight i ∈ Ici (0 : ℝ) := by
    exact fun i _ ↦ law.weight_nonneg i
  have hjensen := concaveOn_negMulLog.le_map_sum hweights hweightSum hpoints
  dsimp only [smul_eq_mul, Function.comp_apply] at hjensen
  have hmean : ∑ i ∈ s, cardinal⁻¹ * law.weight i = cardinal⁻¹ := by
    rw [← mul_sum, hmass, mul_one]
  rw [hmean] at hjensen
  have hscaled := mul_le_mul_of_nonneg_left hjensen hcardinal.le
  rw [mul_sum] at hscaled
  simp_rw [← mul_assoc, mul_inv_cancel₀ hcardinal.ne', one_mul] at hscaled
  rw [negMulLog_def] at hscaled
  dsimp only at hscaled
  rw [Real.log_inv] at hscaled
  have hentropy : law.entropy = ∑ i ∈ s, negMulLog (law.weight i) := by
    rw [entropy]
    exact (sum_subset (subset_univ s) fun i _ hi ↦ by
      rw [hzero i hi, negMulLog_zero]).symm
  calc
    law.entropy = ∑ i ∈ s, negMulLog (law.weight i) := hentropy
    _ ≤ cardinal * (-cardinal⁻¹ * -log cardinal) := hscaled
    _ = log s.card := by
      dsimp [cardinal]
      field_simp

/-- The first marginal of a finite joint law. -/
noncomputable def first (law : FiniteProbabilityLaw (ι × κ)) : FiniteProbabilityLaw ι :=
  law.map Prod.fst

/-- The second marginal of a finite joint law. -/
noncomputable def second (law : FiniteProbabilityLaw (ι × κ)) : FiniteProbabilityLaw κ :=
  law.map Prod.snd

omit [DecidableEq κ] in
theorem first_weight (law : FiniteProbabilityLaw (ι × κ)) (i : ι) :
    law.first.weight i = ∑ k, law.weight (i, k) := by
  classical
  simp only [first, map_weight]
  rw [Fintype.sum_prod_type]
  simp [eq_comm]

omit [DecidableEq ι] in
theorem second_weight (law : FiniteProbabilityLaw (ι × κ)) (k : κ) :
    law.second.weight k = ∑ i, law.weight (i, k) := by
  classical
  simp only [second, map_weight]
  rw [Fintype.sum_prod_type]
  simp

omit [DecidableEq κ] in
@[simp]
theorem first_extend (law : FiniteProbabilityLaw ι)
    (kernel : ι → FiniteProbabilityLaw κ) :
    (law.extend kernel).first = law := by
  classical
  apply ext
  funext i
  rw [first_weight]
  dsimp only [extend]
  rw [← mul_sum, (kernel i).weight_sum, mul_one]

omit [DecidableEq κ] in
@[simp]
theorem first_product (left : FiniteProbabilityLaw ι)
    (right : FiniteProbabilityLaw κ) :
    (left.product right).first = left := by
  classical
  apply ext
  funext i
  rw [first_weight]
  dsimp only [product]
  rw [← mul_sum, right.weight_sum, mul_one]

omit [DecidableEq ι] in
@[simp]
theorem second_product (left : FiniteProbabilityLaw ι)
    (right : FiniteProbabilityLaw κ) :
    (left.product right).second = right := by
  classical
  apply ext
  funext k
  rw [second_weight]
  dsimp only [product]
  rw [← sum_mul, left.weight_sum, one_mul]

/-- Conditional success probability of a Boolean second coordinate. Division by a zero
marginal mass uses Lean's zero convention and therefore returns zero. -/
noncomputable def successParameter (law : FiniteProbabilityLaw (ι × Bool)) (i : ι) : ℝ :=
  law.weight (i, true) / law.first.weight i

omit [DecidableEq κ] [DecidableEq τ] in
theorem joint_true_le_first (law : FiniteProbabilityLaw (ι × Bool)) (i : ι) :
    law.weight (i, true) ≤ law.first.weight i := by
  rw [first_weight, Fintype.sum_bool]
  linarith [law.weight_nonneg (i, false)]

omit [DecidableEq κ] [DecidableEq τ] in
theorem successParameter_mem (law : FiniteProbabilityLaw (ι × Bool)) (i : ι) :
    law.successParameter i ∈ Icc (0 : ℝ) 1 := by
  have hmarginal : 0 ≤ law.first.weight i := law.first.weight_nonneg i
  constructor
  · exact div_nonneg (law.weight_nonneg (i, true)) hmarginal
  · rcases hmarginal.eq_or_lt with hmarginalZero | hmarginalPositive
    · rw [successParameter, hmarginalZero.symm, div_zero]
      exact zero_le_one
    · exact (div_le_one hmarginalPositive).2 (law.joint_true_le_first i)

omit [DecidableEq κ] [DecidableEq τ] in
theorem weight_eq_zero_of_first_eq_zero (law : FiniteProbabilityLaw (ι × Bool))
    {i : ι} (hi : law.first.weight i = 0) (b : Bool) :
    law.weight (i, b) = 0 := by
  have hsum : ∑ c : Bool, law.weight (i, c) = 0 := by
    rw [← first_weight, hi]
  cases b <;> simp only [Fintype.sum_bool] at hsum ⊢
  all_goals linarith [law.weight_nonneg (i, false), law.weight_nonneg (i, true)]

omit [DecidableEq κ] [DecidableEq τ] in
theorem first_mul_successParameter (law : FiniteProbabilityLaw (ι × Bool)) (i : ι) :
    law.first.weight i * law.successParameter i = law.weight (i, true) := by
  by_cases hmarginal : law.first.weight i = 0
  · rw [hmarginal, zero_mul, law.weight_eq_zero_of_first_eq_zero hmarginal]
  · exact mul_div_cancel₀ _ hmarginal

omit [DecidableEq κ] [DecidableEq τ] in
/-- Every finite Boolean joint law is its first marginal followed by its conditional Bernoulli
kernel. -/
theorem extend_successParameter (law : FiniteProbabilityLaw (ι × Bool)) :
    law.first.extend (fun i ↦ bernoulli (law.successParameter i) (law.successParameter_mem i)) =
      law := by
  apply ext
  funext z
  rcases z with ⟨i, b⟩
  by_cases hmarginal : law.first.weight i = 0
  · rw [law.weight_eq_zero_of_first_eq_zero hmarginal b]
    simp [extend, hmarginal]
  · cases b
    · change law.first.weight i *
        (1 - law.weight (i, true) / law.first.weight i) = law.weight (i, false)
      rw [first_weight, Fintype.sum_bool] at hmarginal ⊢
      field_simp [hmarginal]
      ring
    · change law.first.weight i * law.successParameter i = law.weight (i, true)
      simp only [successParameter]
      exact mul_div_cancel₀ _ hmarginal

omit [DecidableEq κ] [DecidableEq τ] in
/-- Shannon's chain rule for a finite state followed by one Boolean coordinate. -/
theorem entropy_eq_first_add_conditional (law : FiniteProbabilityLaw (ι × Bool)) :
    law.entropy = law.first.entropy +
      ∑ i, law.first.weight i * binEntropy (law.successParameter i) := by
  calc
    law.entropy = (law.first.extend fun i ↦
        bernoulli (law.successParameter i) (law.successParameter_mem i)).entropy :=
      congrArg entropy law.extend_successParameter.symm
    _ = law.first.entropy + ∑ i, law.first.weight i *
        (bernoulli (law.successParameter i) (law.successParameter_mem i)).entropy :=
      entropy_extend law.first _
    _ = law.first.entropy +
        ∑ i, law.first.weight i * binEntropy (law.successParameter i) := by
      simp only [entropy_bernoulli]

end FiniteProbabilityLaw

end Frankl
