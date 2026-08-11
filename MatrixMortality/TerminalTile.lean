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

/-- A family of units plus one nonzero rank-one separator is mortal exactly when one scalar
bridge between separators vanishes. -/
theorem unitFamily_mortal_adjoin_outer_iff {α : Type*}
    (generators : α → Square ι 𝕜) (column row : ι → 𝕜)
    [Nonempty ι]
    (generator_unit : ∀ label, IsUnit (generators label))
    (column_ne : column ≠ 0) (row_ne : row ≠ 0) :
    IsMortal (separatedGenerator (Matrix.vecMulVec column row) generators) ↔
      ∃ word : List α, bridgeScalar column row (wordProduct generators word) = 0 := by
  let separator := Matrix.vecMulVec column row
  constructor
  · rintro ⟨raw, _, product_zero⟩
    have separator_mem : none ∈ raw := by
      by_contra no_separator
      obtain ⟨word, rfl⟩ := exists_eq_map_some_of_none_not_mem raw no_separator
      rw [wordProduct_separatedGenerator_map_some] at product_zero
      exact (wordProduct_isUnit generators generator_unit word).ne_zero product_zero
    rw [wordProduct_separatedGenerator_eq_intercalatedProduct] at product_zero
    have fracture_length := fracture_length_two_le_of_none_mem separator_mem
    have fracture_nonempty := fracture_ne_nil raw
    obtain ⟨first, rest, fracture_eq⟩ :=
      List.exists_cons_of_ne_nil fracture_nonempty
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
    have first_column_nonzero :
        wordProduct generators first *ᵥ column ≠ 0 :=
      unit_mulVec_ne_zero (wordProduct_isUnit generators generator_unit first) column_ne
    have last_row_nonzero :
        row ᵥ* wordProduct generators last ≠ 0 :=
      vecMul_unit_ne_zero row_ne (wordProduct_isUnit generators generator_unit last)
    have boundary_nonzero :
        Matrix.vecMulVec (wordProduct generators first *ᵥ column)
          (row ᵥ* wordProduct generators last) ≠ 0 :=
      outer_ne_zero first_column_nonzero last_row_nonzero
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

/-- One rank-one separator carrying fixed data boundaries on its two rays. -/
def boundaryOuter {α : Type*} (generators : α → Square ι 𝕜) (left right : List α)
    (column row : ι → 𝕜) : Square ι 𝕜 :=
  Matrix.vecMulVec (wordProduct generators right *ᵥ column)
    (row ᵥ* wordProduct generators left)

/-- Fixed boundaries cost no state and no generator: one boundary-bearing separator recognizes
the scalar zero language between two arbitrary occurrences, with a converse over every physical
word. -/
theorem unitFamily_mortal_boundaryOuter_iff {α : Type*} [Nonempty ι]
    (generators : α → Square ι 𝕜) (left right : List α) (column row : ι → 𝕜)
    (generator_unit : ∀ label, IsUnit (generators label))
    (column_ne : column ≠ 0) (row_ne : row ≠ 0) :
    IsMortal (separatedGenerator
      (boundaryOuter generators left right column row) generators) ↔
      ∃ word : List α,
        row ⬝ᵥ wordProduct generators (left ++ word ++ right) *ᵥ column = 0 := by
  have right_unit := wordProduct_isUnit generators generator_unit right
  have left_unit := wordProduct_isUnit generators generator_unit left
  have bounded_column_ne : wordProduct generators right *ᵥ column ≠ 0 :=
    unit_mulVec_ne_zero right_unit column_ne
  have bounded_row_ne : row ᵥ* wordProduct generators left ≠ 0 :=
    vecMul_unit_ne_zero row_ne left_unit
  rw [boundaryOuter, unitFamily_mortal_adjoin_outer_iff generators _ _ generator_unit
    bounded_column_ne bounded_row_ne]
  apply exists_congr
  intro word
  rw [bridgeScalar_fold_boundaries]
  rw [wordProduct_append, wordProduct_append]

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
    rw [wordProduct_separatedGenerator_eq_intercalatedProduct] at chain_zero
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
    change intercalatedProduct (Matrix.vecMulVec column row)
      (wordProduct X first :: middle.map (wordProduct X) ++ [wordProduct X last]) = 0
      at chain_zero
    rw [rankOneIntercalatedProduct_formula] at chain_zero
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
    rw [wordProduct_separatedGenerator_eq_intercalatedProduct, fracture_shape]
    rw [show ([[], word, []] : List (List α)).map (wordProduct X) =
      [1, wordProduct X word, 1] by simp [wordProduct]]
    rw [show intercalatedProduct separator [1, wordProduct X word, 1] =
      bridgeScalar column row (wordProduct X word) • Matrix.vecMulVec column row by
        simpa [separator] using
          rankOneIntercalatedProduct_formula column row 1 1 [wordProduct X word]]
    simp [bridge_zero]

end RankOneChain

end MatrixMortality
