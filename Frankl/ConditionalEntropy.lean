import Frankl.FiniteEntropy
import Mathlib.Algebra.BigOperators.Field

namespace Frankl

open Finset Real Set

namespace FiniteProbabilityLaw

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Coarsen the first coordinate of a finite Boolean joint law. -/
noncomputable def coarsenFirst (law : FiniteProbabilityLaw (ι × Bool)) (f : ι → κ) :
    FiniteProbabilityLaw (κ × Bool) :=
  law.map fun z ↦ (f z.1, z.2)

@[simp]
theorem coarsenFirst_first (law : FiniteProbabilityLaw (ι × Bool)) (f : ι → κ) :
    (law.coarsenFirst f).first = law.first.map f := by
  classical
  simp only [coarsenFirst, first, map_comp]
  congr 1

omit [DecidableEq ι] in
theorem coarsenFirst_weight (law : FiniteProbabilityLaw (ι × Bool)) (f : ι → κ)
    (k : κ) (b : Bool) :
    (law.coarsenFirst f).weight (k, b) =
      ∑ i, if f i = k then law.weight (i, b) else 0 := by
  classical
  simp only [coarsenFirst, map_weight]
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _
  rw [sum_eq_single b]
  · simp
  · intro c _ hcb
    simp [hcb]
  · simp

theorem coarsenFirst_first_weight (law : FiniteProbabilityLaw (ι × Bool)) (f : ι → κ)
    (k : κ) :
    (law.coarsenFirst f).first.weight k =
      ∑ i, if f i = k then law.first.weight i else 0 := by
  rw [coarsenFirst_first, map_weight]

private theorem fiber_conditionalEntropy_le (law : FiniteProbabilityLaw (ι × Bool))
    (f : ι → κ) (k : κ) :
    (∑ i, if f i = k then
        law.first.weight i * binEntropy (law.successParameter i) else 0) ≤
      (law.coarsenFirst f).first.weight k *
        binEntropy ((law.coarsenFirst f).successParameter k) := by
  classical
  let coarseMass := (law.coarsenFirst f).first.weight k
  have hcoarseMass : 0 ≤ coarseMass := (law.coarsenFirst f).first.weight_nonneg k
  rcases hcoarseMass.eq_or_lt with hcoarseMassZero | hcoarseMassPositive
  · have hsourceZero : ∀ i, f i = k → law.first.weight i = 0 := by
      intro i hi
      have hsum : (∑ j, if f j = k then law.first.weight j else 0) = 0 := by
        rw [← law.coarsenFirst_first_weight f k]
        exact hcoarseMassZero.symm
      have htermNonneg : ∀ j ∈ (univ : Finset ι),
          0 ≤ if f j = k then law.first.weight j else 0 := by
        intro j _
        split
        · exact law.first.weight_nonneg j
        · exact le_rfl
      have htermZero := (sum_eq_zero_iff_of_nonneg htermNonneg).1 hsum i (mem_univ i)
      simpa [hi] using htermZero
    rw [show (law.coarsenFirst f).first.weight k = 0 by exact hcoarseMassZero.symm]
    simp only [zero_mul]
    apply sum_nonpos
    intro i _
    by_cases hi : f i = k
    · rw [if_pos hi, hsourceZero i hi, zero_mul]
    · rw [if_neg hi]
  · let normalized : ι → ℝ := fun i ↦
      if f i = k then law.first.weight i / coarseMass else 0
    have hnormalizedNonneg : ∀ i ∈ (univ : Finset ι), 0 ≤ normalized i := by
      intro i _
      dsimp only [normalized]
      split
      · exact div_nonneg (law.first.weight_nonneg i) hcoarseMassPositive.le
      · exact le_rfl
    have hnormalizedSum : ∑ i, normalized i = 1 := by
      dsimp only [normalized]
      calc
        (∑ i, if f i = k then law.first.weight i / coarseMass else 0) =
            (∑ i, if f i = k then law.first.weight i else 0) / coarseMass := by
          rw [Finset.sum_div]
          apply sum_congr rfl
          intro i _
          by_cases hi : f i = k <;> simp [hi]
        _ = coarseMass / coarseMass := by
          rw [← law.coarsenFirst_first_weight f k]
        _ = 1 := div_self hcoarseMassPositive.ne'
    have hparameters : ∀ i ∈ (univ : Finset ι),
        law.successParameter i ∈ Icc (0 : ℝ) 1 :=
      fun i _ ↦ law.successParameter_mem i
    have hjensen := strictConcave_binEntropy.concaveOn.le_map_sum
      hnormalizedNonneg hnormalizedSum hparameters
    dsimp only [smul_eq_mul, Function.comp_apply] at hjensen
    have hparameterMean :
        ∑ i, normalized i * law.successParameter i =
          (law.coarsenFirst f).successParameter k := by
      rw [successParameter]
      dsimp only [normalized, coarseMass]
      rw [coarsenFirst_weight]
      calc
        (∑ i, (if f i = k then law.first.weight i /
            (law.coarsenFirst f).first.weight k else 0) * law.successParameter i) =
            (∑ i, if f i = k then law.weight (i, true) else 0) /
              (law.coarsenFirst f).first.weight k := by
          rw [Finset.sum_div]
          apply sum_congr rfl
          intro i _
          by_cases hi : f i = k
          · rw [if_pos hi, if_pos hi]
            rw [div_mul_eq_mul_div, law.first_mul_successParameter]
          · simp [hi]
        _ = _ := rfl
    rw [hparameterMean] at hjensen
    have hscaled := mul_le_mul_of_nonneg_left hjensen hcoarseMassPositive.le
    dsimp only [normalized] at hscaled
    calc
      (∑ i, if f i = k then
          law.first.weight i * binEntropy (law.successParameter i) else 0) =
          coarseMass * ∑ i,
            (if f i = k then law.first.weight i / coarseMass else 0) *
              binEntropy (law.successParameter i) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        by_cases hi : f i = k
        · simp only [if_pos hi]
          field_simp [hcoarseMassPositive.ne']
        · simp [hi]
      _ ≤ coarseMass * binEntropy ((law.coarsenFirst f).successParameter k) := hscaled

/-- Revealing a finer first-coordinate state cannot increase the conditional entropy of a
Boolean second coordinate. -/
theorem conditionalEntropy_le_coarsenFirst (law : FiniteProbabilityLaw (ι × Bool))
    (f : ι → κ) :
    (∑ i, law.first.weight i * binEntropy (law.successParameter i)) ≤
      ∑ k, (law.coarsenFirst f).first.weight k *
        binEntropy ((law.coarsenFirst f).successParameter k) := by
  classical
  calc
    (∑ i, law.first.weight i * binEntropy (law.successParameter i)) =
        ∑ k, ∑ i, if f i = k then
          law.first.weight i * binEntropy (law.successParameter i) else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      rw [sum_eq_single (f i)]
      · simp
      · intro k _ hki
        simp [Ne.symm hki]
      · simp
    _ ≤ ∑ k, (law.coarsenFirst f).first.weight k *
        binEntropy ((law.coarsenFirst f).successParameter k) := by
      exact sum_le_sum fun k _ ↦ fiber_conditionalEntropy_le law f k

/-- Entropy gained by a Boolean coordinate is bounded below after deterministic coarsening of
the previously revealed state. -/
theorem entropy_coarsenFirst_sub_first_ge (law : FiniteProbabilityLaw (ι × Bool))
    (f : ι → κ) :
    (∑ i, law.first.weight i * binEntropy (law.successParameter i)) ≤
      (law.coarsenFirst f).entropy - (law.coarsenFirst f).first.entropy := by
  rw [law.coarsenFirst f |>.entropy_eq_first_add_conditional]
  linarith [law.conditionalEntropy_le_coarsenFirst f]

end FiniteProbabilityLaw

end Frankl
