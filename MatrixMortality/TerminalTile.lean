import MatrixMortality.MatrixSemigroup

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

/-- Interpret `none` as the separator and `some i` as ordinary generator `X i`. -/
def separatedGenerator {α : Type*} (A : Square ι 𝕜) (X : α → Square ι 𝕜) :
    Option α → Square ι 𝕜
  | none => A
  | some i => X i

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

theorem separated_wordProduct_eq_rankOneChain {α : Type*} (A : Square ι 𝕜)
    (X : α → Square ι 𝕜) (word : List (Option α)) :
    wordProduct (separatedGenerator A X) word =
      rankOneChain A ((fracture word).map (wordProduct X)) := by
  induction word with
  | nil => simp [fracture, wordProduct, rankOneChain]
  | cons head word ih =>
      cases head with
      | none =>
          simp only [wordProduct, separatedGenerator, List.map_cons, List.prod_cons,
            fracture, List.map_cons, List.map_nil, List.prod_nil]
          have hmap : (fracture word).map (wordProduct X) ≠ [] := by
            simpa using fracture_ne_nil word
          rw [show (word.map (separatedGenerator A X)).prod =
              wordProduct (separatedGenerator A X) word from rfl,
            ih, rankOneChain_one_cons _ hmap]
      | some i =>
          simp only [wordProduct, separatedGenerator, List.map_cons, List.prod_cons]
          rw [show (word.map (separatedGenerator A X)).prod =
              wordProduct (separatedGenerator A X) word from rfl,
            ih]
          have hfracture := fracture_ne_nil word
          rcases List.exists_cons_of_ne_nil hfracture with ⟨block, blocks, hblocks⟩
          rw [show fracture (some i :: word) = (fracture word).modifyHead (i :: ·) by rfl,
            hblocks]
          simp only [List.modifyHead, List.map_cons, wordProduct, List.map_cons, List.prod_cons]
          simpa using (rankOneChain_modifyHead A (X i)
            (List.cons_ne_nil (wordProduct X block) (blocks.map (wordProduct X)))).symm

/-- A common fixed column replaces invertibility in the rank-one scalar-to-mortality compiler. -/
theorem fixedAnchor_mortal_adjoin_outer_iff {α : Type*} (X : α → Square ι 𝕜)
    (anchor column row : ι → 𝕜) (fixed : ∀ label, X label *ᵥ anchor = anchor)
    (row_anchor_nonzero : row ⬝ᵥ anchor ≠ 0) :
    IsMortal (separatedGenerator (Matrix.vecMulVec column row) X) ↔
      ∃ word : List α, bridgeScalar column row (wordProduct X word) = 0 := by
  let separator := Matrix.vecMulVec column row
  have anchor_nonzero : anchor ≠ 0 := by
    intro anchor_zero
    apply row_anchor_nonzero
    rw [anchor_zero]
    simp
  have separator_free_fixed :
      ∀ (word : List (Option α)), none ∉ word →
        wordProduct (separatedGenerator separator X) word *ᵥ anchor = anchor := by
    intro word no_separator
    induction word with
    | nil => simp
    | cons head tail induction =>
        cases head with
        | none => exact (no_separator (by simp)).elim
        | some label =>
            have tail_no_separator : none ∉ tail := by
              intro member
              exact no_separator (by simp [member])
            rw [wordProduct_cons, separatedGenerator, ← Matrix.mulVec_mulVec]
            change X label *ᵥ (wordProduct (separatedGenerator separator X) tail *ᵥ anchor) =
              anchor
            rw [induction tail_no_separator, fixed]
  constructor
  · rintro ⟨raw, _, product_zero⟩
    have chain_zero : wordProduct (separatedGenerator separator X) raw = 0 :=
      product_zero
    have separator_mem : none ∈ raw := by
      by_contra no_separator
      have product_fixed := separator_free_fixed raw no_separator
      rw [chain_zero] at product_fixed
      exact anchor_nonzero (by simpa using product_fixed.symm)
    rw [separated_wordProduct_eq_rankOneChain] at chain_zero
    have fracture_length := fracture_length_two_le_of_none_mem separator_mem
    have fracture_nonempty := fracture_ne_nil raw
    obtain ⟨first, rest, fracture_eq⟩ := List.exists_cons_of_ne_nil fracture_nonempty
    have rest_nonempty : rest ≠ [] := by
      intro rest_empty
      rw [fracture_eq, rest_empty] at fracture_length
      simp at fracture_length
    let last := rest.getLast rest_nonempty
    let middle := rest.dropLast
    have fracture_decomposition : fracture raw = first :: middle ++ [last] := by
      rw [fracture_eq]
      congr 1
      exact (List.dropLast_append_getLast rest_nonempty).symm
    have mapped_decomposition : (fracture raw).map (wordProduct X) =
        wordProduct X first :: middle.map (wordProduct X) ++ [wordProduct X last] := by
      simp [fracture_decomposition]
    rw [mapped_decomposition] at chain_zero
    change rankOneChain (Matrix.vecMulVec column row)
      (wordProduct X first :: middle.map (wordProduct X) ++ [wordProduct X last]) = 0
      at chain_zero
    rw [rankOneChain_formula] at chain_zero
    by_cases first_column_zero : wordProduct X first *ᵥ column = 0
    · refine ⟨first, ?_⟩
      simp [bridgeScalar, first_column_zero]
    · have last_row_nonzero : row ᵥ* wordProduct X last ≠ 0 := by
        simpa [wordProduct] using
          vecMul_wordProduct_ne_zero_of_fixed X anchor row fixed row_anchor_nonzero last
      have boundary_nonzero :
          Matrix.vecMulVec (wordProduct X first *ᵥ column)
            (row ᵥ* wordProduct X last) ≠ 0 :=
        outer_ne_zero first_column_zero last_row_nonzero
      have scalar_product_zero :
          ((middle.map (wordProduct X)).map (bridgeScalar column row)).prod = 0 :=
        (smul_eq_zero.mp chain_zero).resolve_right boundary_nonzero
      have zero_mem :
          0 ∈ (middle.map (wordProduct X)).map (bridgeScalar column row) :=
        List.prod_eq_zero_iff.mp scalar_product_zero
      obtain ⟨matrix, matrix_mem, bridge_zero⟩ := List.mem_map.mp zero_mem
      obtain ⟨word, _, rfl⟩ := List.mem_map.mp matrix_mem
      exact ⟨word, bridge_zero⟩
  · rintro ⟨word, bridge_zero⟩
    refine ⟨none :: word.map some ++ [none], by simp, ?_⟩
    have fracture_shape : fracture (none :: word.map some ++ [none]) = [[], word, []] := by
      simp [fracture, fracture_map_some_append_none]
    change wordProduct (separatedGenerator separator X) (none :: word.map some ++ [none]) = 0
    rw [separated_wordProduct_eq_rankOneChain, fracture_shape]
    rw [show ([[], word, []] : List (List α)).map (wordProduct X) =
      [1, wordProduct X word, 1] by simp [wordProduct]]
    rw [show rankOneChain separator [1, wordProduct X word, 1] =
      bridgeScalar column row (wordProduct X word) • Matrix.vecMulVec column row by
        simpa [separator] using rankOneChain_formula column row 1 1 [wordProduct X word]]
    simp [bridge_zero]

end RankOneChain

end MatrixMortality
