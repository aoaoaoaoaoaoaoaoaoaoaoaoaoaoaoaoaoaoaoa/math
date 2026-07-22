import Mathlib

/-!
# Terminal-tile absorption for matrix mortality

This file machine-checks the generic rank-one algebra used by the `M₃(5)` reduction.  It is
independent of the word-system source and covers arbitrary products over ordinary invertible
generators and one exceptional outer product.
-/

namespace MatrixMortality

open scoped Matrix

section OuterProduct

variable {ι 𝕜 : Type*} [Fintype ι] [Field 𝕜]

abbrev Square (ι 𝕜 : Type*) := Matrix ι ι 𝕜

theorem mul_outer (M : Square ι 𝕜) (c r : ι → 𝕜) :
    M * Matrix.vecMulVec c r = Matrix.vecMulVec (M *ᵥ c) r := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.mulVec, Matrix.vecMulVec_apply, Matrix.dotProduct]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem outer_mul (c r : ι → 𝕜) (M : Square ι 𝕜) :
    Matrix.vecMulVec c r * M = Matrix.vecMulVec c (r ᵥ* M) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMul, Matrix.vecMulVec_apply, Matrix.dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem outer_mul_outer (c r d s : ι → 𝕜) :
    Matrix.vecMulVec c r * Matrix.vecMulVec d s =
      (r ⬝ᵥ d) • Matrix.vecMulVec c s := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.dotProduct,
    Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [Fintype ι] in
theorem outer_ne_zero {c r : ι → 𝕜} (hc : c ≠ 0) (hr : r ≠ 0) :
    Matrix.vecMulVec c r ≠ 0 := by
  intro h
  apply hc
  funext i
  by_contra hci
  apply hr
  funext j
  by_contra hrj
  have hij := congr_fun (congr_fun h i) j
  simp only [Matrix.vecMulVec_apply, Pi.zero_apply] at hij
  exact (mul_ne_zero hci hrj) hij

end OuterProduct

section RankOneChain

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [Field 𝕜]

/-- `rankOneChain A [P₀, ..., Pₜ]` is `P₀ A P₁ A ⋯ A Pₜ`. -/
def rankOneChain (A : Square ι 𝕜) : List (Square ι 𝕜) → Square ι 𝕜
  | [] => 1
  | [P] => P
  | P :: Q :: blocks => P * A * rankOneChain A (Q :: blocks)

/-- The scalar contributed by an invertible block between two rank-one separators. -/
def bridgeScalar (c r : ι → 𝕜) (P : Square ι 𝕜) : 𝕜 := r ⬝ᵥ P *ᵥ c

omit [DecidableEq ι] in
/-- Fixed left and right boundary matrices can both be folded into the two vectors of the
rank-one separator. -/
theorem bridgeScalar_fold_boundaries (l c : ι → 𝕜) (left middle right : Square ι 𝕜) :
    bridgeScalar (right *ᵥ c) (l ᵥ* left) middle =
      l ⬝ᵥ (left * middle * right) *ᵥ c := by
  unfold bridgeScalar
  rw [← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem unit_mulVec_ne_zero {P : Square ι 𝕜} {c : ι → 𝕜}
    (hP : IsUnit P) (hc : c ≠ 0) : P *ᵥ c ≠ 0 := by
  intro hPc
  rcases hP.exists_left_inv with ⟨Q, hQP⟩
  apply hc
  calc
    c = 1 *ᵥ c := by simp
    _ = (Q * P) *ᵥ c := by rw [hQP]
    _ = Q *ᵥ P *ᵥ c := by rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hPc]; simp

theorem unit_vecMul_ne_zero {P : Square ι 𝕜} {r : ι → 𝕜}
    (hP : IsUnit P) (hr : r ≠ 0) : r ᵥ* P ≠ 0 := by
  intro hrP
  rcases hP.exists_right_inv with ⟨Q, hPQ⟩
  apply hr
  calc
    r = r ᵥ* 1 := by simp
    _ = r ᵥ* (P * Q) := by rw [hPQ]
    _ = (r ᵥ* P) ᵥ* Q := by rw [Matrix.vecMul_vecMul]
    _ = 0 := by rw [hrP]; simp

theorem rankOneChain_formula (c r : ι → 𝕜) (P₀ Pₜ : Square ι 𝕜) :
    ∀ middle : List (Square ι 𝕜),
      rankOneChain (Matrix.vecMulVec c r) (P₀ :: middle ++ [Pₜ]) =
        (middle.map (bridgeScalar c r)).prod •
          Matrix.vecMulVec (P₀ *ᵥ c) (r ᵥ* Pₜ)
  | [] => by
      simp [rankOneChain, mul_outer, outer_mul]
  | P :: middle => by
      rw [show P₀ :: (P :: middle) ++ [Pₜ] = P₀ :: P :: (middle ++ [Pₜ]) by rfl]
      rw [rankOneChain]
      rw [show rankOneChain (Matrix.vecMulVec c r) (P :: (middle ++ [Pₜ])) =
          (middle.map (bridgeScalar c r)).prod •
            Matrix.vecMulVec (P *ᵥ c) (r ᵥ* Pₜ) by
        simpa using rankOneChain_formula c r P Pₜ middle]
      rw [mul_smul_comm]
      rw [show P₀ * Matrix.vecMulVec c r = Matrix.vecMulVec (P₀ *ᵥ c) r from
        mul_outer P₀ c r]
      rw [outer_mul_outer]
      simp [bridgeScalar, smul_smul, mul_comm]

theorem rankOneChain_eq_zero_iff (c r : ι → 𝕜) (P₀ Pₜ : Square ι 𝕜)
    (middle : List (Square ι 𝕜)) (hc : c ≠ 0) (hr : r ≠ 0)
    (hP₀ : IsUnit P₀) (hPₜ : IsUnit Pₜ) :
    rankOneChain (Matrix.vecMulVec c r) (P₀ :: middle ++ [Pₜ]) = 0 ↔
      ∃ P ∈ middle, bridgeScalar c r P = 0 := by
  rw [rankOneChain_formula, smul_eq_zero]
  have hboundary : Matrix.vecMulVec (P₀ *ᵥ c) (r ᵥ* Pₜ) ≠ 0 :=
    outer_ne_zero (unit_mulVec_ne_zero hP₀ hc) (unit_vecMul_ne_zero hPₜ hr)
  simp only [hboundary, or_false, List.prod_eq_zero_iff, List.mem_map]

theorem list_prod_isUnit {blocks : List (Square ι 𝕜)}
    (hblocks : ∀ P ∈ blocks, IsUnit P) : IsUnit blocks.prod := by
  induction blocks with
  | nil => simp
  | cons P blocks ih =>
      simp only [List.prod_cons]
      exact (hblocks P (by simp)).mul (ih fun Q hQ => hblocks Q (by simp [hQ]))

/-- Split a generator word at `none`, erasing the separators from the resulting blocks. -/
def fracture {α : Type*} : List (Option α) → List (List α)
  | [] => [[]]
  | none :: word => [] :: fracture word
  | some i :: word => (fracture word).modifyHead (i :: ·)

theorem fracture_ne_nil {α : Type*} (word : List (Option α)) : fracture word ≠ [] := by
  induction word with
  | nil => simp [fracture]
  | cons head word ih =>
      cases head with
      | none => simp [fracture]
      | some i =>
          cases h : fracture word with
          | nil => exact (ih h).elim
          | cons block blocks => simp [fracture, h]

theorem fracture_length_two_le_of_none_mem {α : Type*} {word : List (Option α)}
    (hnone : none ∈ word) : 2 ≤ (fracture word).length := by
  induction word with
  | nil => simp at hnone
  | cons head word ih =>
      cases head with
      | none =>
          simp only [fracture, List.length_cons]
          have := List.length_pos.mpr (fracture_ne_nil word)
          omega
      | some i =>
          have htail : none ∈ word := by simpa using hnone
          have hlength := ih htail
          have hfracture := fracture_ne_nil word
          rcases List.exists_cons_of_ne_nil hfracture with ⟨block, blocks, hblocks⟩
          simp [fracture, hblocks]
          simpa [hblocks] using hlength

theorem fracture_map_some_append_none {α : Type*} (word : List α) :
    fracture (word.map some ++ [none]) = [word, []] := by
  induction word with
  | nil => rfl
  | cons i word ih => simp [fracture, ih]

def blockProduct {α : Type*} (X : α → Square ι 𝕜) (block : List α) : Square ι 𝕜 :=
  (block.map X).prod

def separatedGenerator {α : Type*} (A : Square ι 𝕜) (X : α → Square ι 𝕜) :
    Option α → Square ι 𝕜
  | none => A
  | some i => X i

def generatorProduct {α : Type*} (A : Square ι 𝕜) (X : α → Square ι 𝕜)
    (word : List (Option α)) : Square ι 𝕜 :=
  (word.map (separatedGenerator A X)).prod

theorem rankOneChain_one_cons (A : Square ι 𝕜) {blocks : List (Square ι 𝕜)}
    (hblocks : blocks ≠ []) :
    rankOneChain A (1 :: blocks) = A * rankOneChain A blocks := by
  rcases List.exists_cons_of_ne_nil hblocks with ⟨P, blocks, rfl⟩
  cases blocks <;> simp [rankOneChain]

theorem rankOneChain_modifyHead (A X : Square ι 𝕜) {blocks : List (Square ι 𝕜)}
    (hblocks : blocks ≠ []) :
    rankOneChain A (blocks.modifyHead (X * ·)) = X * rankOneChain A blocks := by
  rcases List.exists_cons_of_ne_nil hblocks with ⟨P, blocks, rfl⟩
  cases blocks <;> simp [rankOneChain, mul_assoc]

theorem generatorProduct_eq_rankOneChain {α : Type*} (A : Square ι 𝕜)
    (X : α → Square ι 𝕜) (word : List (Option α)) :
    generatorProduct A X word = rankOneChain A ((fracture word).map (blockProduct X)) := by
  induction word with
  | nil => simp [generatorProduct, fracture, blockProduct, rankOneChain]
  | cons head word ih =>
      cases head with
      | none =>
          simp only [generatorProduct, separatedGenerator, List.map_cons, List.prod_cons,
            fracture, List.map_cons, blockProduct, List.map_nil, List.prod_nil]
          have hmap : (fracture word).map (blockProduct X) ≠ [] := by
            simpa using fracture_ne_nil word
          rw [show (word.map (separatedGenerator A X)).prod = generatorProduct A X word from rfl,
            ih, rankOneChain_one_cons _ hmap]
      | some i =>
          simp only [generatorProduct, separatedGenerator, List.map_cons, List.prod_cons]
          rw [show (word.map (separatedGenerator A X)).prod = generatorProduct A X word from rfl,
            ih]
          have hfracture := fracture_ne_nil word
          rcases List.exists_cons_of_ne_nil hfracture with ⟨block, blocks, hblocks⟩
          rw [show fracture (some i :: word) = (fracture word).modifyHead (i :: ·) by rfl,
            hblocks]
          simp only [List.modifyHead, List.map_cons, blockProduct, List.map_cons, List.prod_cons]
          simpa using (rankOneChain_modifyHead A (X i)
            (List.cons_ne_nil (blockProduct X block) (blocks.map (blockProduct X)))).symm

theorem blockProduct_isUnit {α : Type*} {X : α → Square ι 𝕜}
    (hX : ∀ i, IsUnit (X i)) (block : List α) : IsUnit (blockProduct X block) := by
  apply list_prod_isUnit
  intro P hP
  rcases List.mem_map.mp hP with ⟨i, _, rfl⟩
  exact hX i

theorem generatorProduct_isUnit_of_none_not_mem {α : Type*} (A : Square ι 𝕜)
    {X : α → Square ι 𝕜} (hX : ∀ i, IsUnit (X i)) {word : List (Option α)}
    (hnone : none ∉ word) : IsUnit (generatorProduct A X word) := by
  apply list_prod_isUnit
  intro P hP
  rcases List.mem_map.mp hP with ⟨letter, hletter, rfl⟩
  cases letter with
  | none => exact (hnone hletter).elim
  | some i => exact hX i

end RankOneChain

end MatrixMortality
