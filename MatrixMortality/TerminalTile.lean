import MatrixMortality.RankOne

/-!
# Terminal-tile absorption for matrix mortality

This file machine-checks the generic rank-one algebra used by the `M₃(5)` reduction.  It is
independent of the word-system source and covers arbitrary products over ordinary invertible
generators and one exceptional outer product.
-/

namespace MatrixMortality

open scoped Matrix

section RankOneChain

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [Field 𝕜]

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

theorem rankOneIntercalatedProduct_formula (c r : ι → 𝕜) (P₀ Pₜ : Square ι 𝕜) :
    ∀ middle : List (Square ι 𝕜),
      intercalatedProduct (Matrix.vecMulVec c r) (P₀ :: middle ++ [Pₜ]) =
        (middle.map (bridgeScalar c r)).prod •
          Matrix.vecMulVec (P₀ *ᵥ c) (r ᵥ* Pₜ)
  | [] => by
      simp [intercalatedProduct, mul_outer, outer_mul]
  | P :: middle => by
      rw [show P₀ :: (P :: middle) ++ [Pₜ] = P₀ :: P :: (middle ++ [Pₜ]) by rfl]
      rw [intercalatedProduct]
      rw [show intercalatedProduct (Matrix.vecMulVec c r) (P :: (middle ++ [Pₜ])) =
          (middle.map (bridgeScalar c r)).prod •
            Matrix.vecMulVec (P *ᵥ c) (r ᵥ* Pₜ) by
        simpa using rankOneIntercalatedProduct_formula c r P Pₜ middle]
      rw [mul_smul_comm]
      rw [show P₀ * Matrix.vecMulVec c r = Matrix.vecMulVec (P₀ *ᵥ c) r from
        mul_outer P₀ c r]
      rw [outer_mul_outer]
      simp [bridgeScalar, smul_smul, mul_comm]

/-- Adjoining one outer-product separator to an arbitrary matrix family is mortal exactly when
one scalar bridge vanishes. Singular controls, zero control products, and zero exterior blocks
need no separate hypotheses: each already supplies a scalar-zero word. -/
theorem mortal_adjoin_outer_iff {α : Type*} (generators : α → Square ι 𝕜)
    (column row : ι → 𝕜) :
    IsMortal (separatedGenerator (Matrix.vecMulVec column row) generators) ↔
      ∃ word : List α, bridgeScalar column row (wordProduct generators word) = 0 := by
  let separator := Matrix.vecMulVec column row
  constructor
  · rintro ⟨raw, _, product_zero⟩
    by_cases separator_mem : none ∈ raw
    · rw [wordProduct_separatedGenerator_eq_intercalatedProduct] at product_zero
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
      have mapped_decomposition : (fracture raw).map (wordProduct generators) =
          wordProduct generators first ::
            middle.map (wordProduct generators) ++ [wordProduct generators last] := by
        simp [fracture_decomposition]
      rw [mapped_decomposition] at product_zero
      change intercalatedProduct separator
        (wordProduct generators first ::
          middle.map (wordProduct generators) ++ [wordProduct generators last]) = 0
        at product_zero
      rw [rankOneIntercalatedProduct_formula] at product_zero
      by_cases first_column_zero : wordProduct generators first *ᵥ column = 0
      · exact ⟨first, by simp [bridgeScalar, first_column_zero]⟩
      by_cases last_row_zero : row ᵥ* wordProduct generators last = 0
      · refine ⟨last, ?_⟩
        rw [bridgeScalar, Matrix.dotProduct_mulVec, last_row_zero]
        simp
      have boundary_nonzero :
          Matrix.vecMulVec (wordProduct generators first *ᵥ column)
            (row ᵥ* wordProduct generators last) ≠ 0 :=
        outer_ne_zero first_column_zero last_row_zero
      have scalar_product_zero :
          ((middle.map (wordProduct generators)).map
            (bridgeScalar column row)).prod = 0 :=
        (smul_eq_zero.mp product_zero).resolve_right boundary_nonzero
      have zero_mem :
          0 ∈ (middle.map (wordProduct generators)).map
            (bridgeScalar column row) :=
        List.prod_eq_zero_iff.mp scalar_product_zero
      obtain ⟨matrix, matrix_mem, bridge_zero⟩ := List.mem_map.mp zero_mem
      obtain ⟨word, _, rfl⟩ := List.mem_map.mp matrix_mem
      exact ⟨word, bridge_zero⟩
    · obtain ⟨word, rfl⟩ := exists_eq_map_some_of_none_not_mem raw separator_mem
      rw [wordProduct_separatedGenerator_map_some] at product_zero
      exact ⟨word, by simp [bridgeScalar, product_zero]⟩
  · rintro ⟨word, bridge_zero⟩
    refine ⟨none :: word.map some ++ [none], by simp, ?_⟩
    have fracture_shape : fracture (none :: word.map some ++ [none]) = [[], word, []] := by
      simp [fracture, fracture_map_some_append_none]
    change wordProduct (separatedGenerator separator generators)
      (none :: word.map some ++ [none]) = 0
    rw [wordProduct_separatedGenerator_eq_intercalatedProduct, fracture_shape]
    rw [show ([[], word, []] : List (List α)).map (wordProduct generators) =
      [1, wordProduct generators word, 1] by simp [wordProduct]]
    rw [show intercalatedProduct separator [1, wordProduct generators word, 1] =
      bridgeScalar column row (wordProduct generators word) •
        Matrix.vecMulVec column row by
          simpa [separator] using
            rankOneIntercalatedProduct_formula column row 1 1 [wordProduct generators word]]
    simp [bridge_zero]

/-- One rank-one separator carrying fixed word boundaries on its two rays. -/
def boundaryOuter {α : Type*} (generators : α → Square ι 𝕜) (left right : List α)
    (column row : ι → 𝕜) : Square ι 𝕜 :=
  Matrix.vecMulVec (wordProduct generators right *ᵥ column)
    (row ᵥ* wordProduct generators left)

/-- Fixed word boundaries fold into one separator without hypotheses on the matrix family or
boundary vectors. -/
theorem mortal_boundaryOuter_iff {α : Type*} (generators : α → Square ι 𝕜)
    (left right : List α) (column row : ι → 𝕜) :
    IsMortal (separatedGenerator
      (boundaryOuter generators left right column row) generators) ↔
      ∃ word : List α,
        row ⬝ᵥ wordProduct generators (left ++ word ++ right) *ᵥ column = 0 := by
  rw [boundaryOuter, mortal_adjoin_outer_iff]
  apply exists_congr
  intro word
  rw [bridgeScalar_fold_boundaries, wordProduct_append, wordProduct_append]

end RankOneChain

end MatrixMortality
