import Mathlib

/-!
# Matrix-semigroup foundations

This file owns the common semantics and transport laws used by every mortality compiler in the
project. It is independent of the encoded word system.
-/

namespace MatrixMortality

open scoped Matrix

/-- Square matrices indexed by `ι` over `R`. -/
abbrev Square (ι R : Type*) := Matrix ι ι R

/-- A nonsingular inverse reverses any stated matrix-vector action. -/
theorem nonsingInv_mulVec_eq_of_mulVec_eq
    {ι K : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {matrix : Square ι K} (matrix_unit : IsUnit matrix)
    {source target : ι → K} (action : matrix *ᵥ source = target) :
    matrix⁻¹ *ᵥ target = source := by
  calc
    matrix⁻¹ *ᵥ target = matrix⁻¹ *ᵥ (matrix *ᵥ source) :=
      congrArg (fun vector => matrix⁻¹ *ᵥ vector) action.symm
    _ = (matrix⁻¹ * matrix) *ᵥ source :=
      Matrix.mulVec_mulVec source matrix⁻¹ matrix
    _ = 1 *ᵥ source := congrArg (fun M => M *ᵥ source)
      (Matrix.nonsing_inv_mul matrix
        (matrix.isUnit_iff_isUnit_det.mp matrix_unit))
    _ = source := Matrix.one_mulVec source

/-- Interpret a word by multiplying its generators from left to right. -/
def wordProduct {α M : Type*} [Monoid M] (generators : α → M) (word : List α) : M :=
  (word.map generators).prod

@[simp]
theorem wordProduct_nil {α M : Type*} [Monoid M] (generators : α → M) :
    wordProduct generators [] = 1 := rfl

@[simp]
theorem wordProduct_cons {α M : Type*} [Monoid M] (generators : α → M)
    (head : α) (tail : List α) :
    wordProduct generators (head :: tail) = generators head * wordProduct generators tail := by
  simp [wordProduct]

theorem wordProduct_map {α M N : Type*} [Monoid M] [Monoid N] (map : M →* N)
    (generators : α → M) (word : List α) :
    wordProduct (map ∘ generators) word = map (wordProduct generators word) := by
  exact List.prod_map_hom word generators map

theorem wordProduct_append {α M : Type*} [Monoid M] (generators : α → M)
    (left right : List α) :
    wordProduct generators (left ++ right) =
      wordProduct generators left * wordProduct generators right := by
  simp [wordProduct, List.map_append, List.prod_append]

/-- Inserting a word whose product is a scalar identity only scales the surrounding matrix
product. -/
theorem wordProduct_projectiveIdentity_insertion
    {α : Type*} (generators : α → Square (Fin 2) ℚ)
    (left neutral right : List α) (scale : ℚ)
    (neutral_product :
      wordProduct generators neutral = scale • (1 : Square (Fin 2) ℚ)) :
    wordProduct generators (left ++ neutral ++ right) =
      scale • wordProduct generators (left ++ right) := by
  rw [wordProduct_append, wordProduct_append, wordProduct_append,
    neutral_product, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- A nonzero projective-identity word may be inserted or deleted in any context without
changing whether the product is zero. -/
theorem wordProduct_zero_iff_projectiveIdentity_insertion
    {α : Type*} (generators : α → Square (Fin 2) ℚ)
    (left neutral right : List α) (scale : ℚ) (scale_ne_zero : scale ≠ 0)
    (neutral_product :
      wordProduct generators neutral = scale • (1 : Square (Fin 2) ℚ)) :
    wordProduct generators (left ++ neutral ++ right) = 0 ↔
      wordProduct generators (left ++ right) = 0 := by
  rw [wordProduct_projectiveIdentity_insertion generators left neutral right scale
    neutral_product]
  simp [scale_ne_zero]

theorem wordProduct_comp {α β M : Type*} [Monoid M] (generators : β → M)
    (relabel : α → β) (word : List α) :
    wordProduct (generators ∘ relabel) word =
      wordProduct generators (word.map relabel) := by
  simp [wordProduct, List.map_map, Function.comp_def]

@[simp]
theorem wordProduct_const {α M : Type*} [Monoid M] (element : M) (word : List α) :
    wordProduct (fun _ : α => element) word = element ^ word.length := by
  induction word with
  | nil => simp
  | cons head tail induction =>
      rw [wordProduct_cons, induction, List.length_cons, pow_succ']

/-! ## Word-series zero languages -/

namespace WordSeries

/-- Pull a word series back along a letter map. -/
def relabel {α β R : Type*} (series : List β → R) (map : α → β) : List α → R :=
  fun word => series (word.map map)

/-- A word series vanishes on some nonempty word. -/
def HasNonemptyZero {α R : Type*} [Zero R] (series : List α → R) : Prop :=
  ∃ word : List α, word ≠ [] ∧ series word = 0

/-- A word series vanishes on some word, possibly the empty word. -/
def HasZero {α R : Type*} [Zero R] (series : List α → R) : Prop :=
  ∃ word : List α, series word = 0

theorem hasNonemptyZero_relabel_equiv {α β R : Type*} [Zero R]
    (series : List β → R) (equivalence : α ≃ β) :
    HasNonemptyZero (relabel series equivalence) ↔ HasNonemptyZero series := by
  constructor
  · rintro ⟨word, word_nonempty, series_zero⟩
    exact ⟨word.map equivalence, by simpa using word_nonempty, series_zero⟩
  · rintro ⟨word, word_nonempty, series_zero⟩
    refine ⟨word.map equivalence.symm, by simpa using word_nonempty, ?_⟩
    simpa [relabel, List.map_map, Function.comp_def] using series_zero

theorem hasZero_relabel_equiv {α β R : Type*} [Zero R]
    (series : List β → R) (equivalence : α ≃ β) :
    HasZero (relabel series equivalence) ↔ HasZero series := by
  constructor
  · rintro ⟨word, series_zero⟩
    exact ⟨word.map equivalence, series_zero⟩
  · rintro ⟨word, series_zero⟩
    refine ⟨word.map equivalence.symm, ?_⟩
    simpa [relabel, List.map_map, Function.comp_def] using series_zero

theorem hasNonemptyZero_iff_hasZero_of_nil_ne {α R : Type*} [Zero R]
    (series : List α → R) (nil_ne : series [] ≠ 0) :
    HasNonemptyZero series ↔ HasZero series := by
  constructor
  · rintro ⟨word, _, series_zero⟩
    exact ⟨word, series_zero⟩
  · rintro ⟨word, series_zero⟩
    refine ⟨word, ?_, series_zero⟩
    rintro rfl
    exact nil_ne series_zero

end WordSeries

/-- Interpret `none` as one distinguished generator and `some label` as an ordinary generator. -/
def separatedGenerator {α M : Type*} (separator : M) (generators : α → M) : Option α → M
  | none => separator
  | some label => generators label

@[simp]
theorem wordProduct_separatedGenerator_map_some {α M : Type*} [Monoid M]
    (separator : M) (generators : α → M) (word : List α) :
    wordProduct (separatedGenerator separator generators) (word.map some) =
      wordProduct generators word := by
  induction word with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.map_cons, wordProduct_cons, separatedGenerator, induction]

theorem exists_eq_map_some_of_none_not_mem {α : Type*}
    (word : List (Option α)) (none_not_mem : none ∉ word) :
    ∃ ordinary : List α, word = ordinary.map some := by
  induction word with
  | nil => exact ⟨[], rfl⟩
  | cons head tail induction =>
      cases head with
      | none => exact (none_not_mem (by simp)).elim
      | some label =>
          have tail_none_not_mem : none ∉ tail := by
            intro none_mem
            exact none_not_mem (by simp [none_mem])
          obtain ⟨ordinary, rfl⟩ := induction tail_none_not_mem
          exact ⟨label :: ordinary, rfl⟩

/-- Insert `separator` between a nonempty list of monoid blocks. The empty list denotes `1`. -/
def intercalatedProduct {M : Type*} [Monoid M] (separator : M) : List M → M
  | [] => 1
  | [block] => block
  | block :: next :: blocks =>
      block * separator * intercalatedProduct separator (next :: blocks)

/-- Split a word at every `none`, erasing separators and retaining all possibly empty blocks. -/
def fracture {α : Type*} : List (Option α) → List (List α)
  | [] => [[]]
  | none :: word => [] :: fracture word
  | some label :: word => (fracture word).modifyHead (label :: ·)

theorem fracture_ne_nil {α : Type*} (word : List (Option α)) : fracture word ≠ [] := by
  induction word with
  | nil => simp [fracture]
  | cons head word induction =>
      cases head with
      | none => simp [fracture]
      | some label =>
          cases fracture_eq : fracture word with
          | nil => exact (induction fracture_eq).elim
          | cons block blocks => simp [fracture, fracture_eq]

theorem fracture_length_two_le_of_none_mem {α : Type*} {word : List (Option α)}
    (none_mem : none ∈ word) : 2 ≤ (fracture word).length := by
  induction word with
  | nil => simp at none_mem
  | cons head word induction =>
      cases head with
      | none =>
          simp only [fracture, List.length_cons]
          have positive := List.length_pos_iff.mpr (fracture_ne_nil word)
          omega
      | some label =>
          have tail_none_mem : none ∈ word := by simpa using none_mem
          have length_bound := induction tail_none_mem
          have fracture_nonempty := fracture_ne_nil word
          obtain ⟨block, blocks, fracture_eq⟩ :=
            List.exists_cons_of_ne_nil fracture_nonempty
          simp [fracture, fracture_eq]
          simpa [fracture_eq] using length_bound

theorem fracture_map_some_append_none {α : Type*} (word : List α) :
    fracture (word.map some ++ [none]) = [word, []] := by
  induction word with
  | nil => rfl
  | cons label word induction => simp [fracture, induction]

theorem intercalatedProduct_one_cons {M : Type*} [Monoid M]
    (separator : M) {blocks : List M} (blocks_nonempty : blocks ≠ []) :
    intercalatedProduct separator (1 :: blocks) =
      separator * intercalatedProduct separator blocks := by
  obtain ⟨block, blocks, rfl⟩ := List.exists_cons_of_ne_nil blocks_nonempty
  cases blocks <;> simp [intercalatedProduct]

theorem intercalatedProduct_modifyHead {M : Type*} [Monoid M]
    (separator left : M) {blocks : List M} (blocks_nonempty : blocks ≠ []) :
    intercalatedProduct separator (blocks.modifyHead (left * ·)) =
      left * intercalatedProduct separator blocks := by
  obtain ⟨block, blocks, rfl⟩ := List.exists_cons_of_ne_nil blocks_nonempty
  cases blocks <;> simp [intercalatedProduct, mul_assoc]

/-- Every word over ordinary generators and one separator is the intercalation of its fractured
ordinary blocks. -/
theorem wordProduct_separatedGenerator_eq_intercalatedProduct {α M : Type*} [Monoid M]
    (separator : M) (generators : α → M) (word : List (Option α)) :
    wordProduct (separatedGenerator separator generators) word =
      intercalatedProduct separator ((fracture word).map (wordProduct generators)) := by
  induction word with
  | nil => simp [fracture, wordProduct, intercalatedProduct]
  | cons head word induction =>
      cases head with
      | none =>
          simp only [wordProduct, separatedGenerator, List.map_cons, List.prod_cons,
            fracture, List.map_cons, List.map_nil, List.prod_nil]
          have fractured_nonempty : (fracture word).map (wordProduct generators) ≠ [] := by
            simpa using fracture_ne_nil word
          rw [show (word.map (separatedGenerator separator generators)).prod =
              wordProduct (separatedGenerator separator generators) word from rfl,
            induction, intercalatedProduct_one_cons _ fractured_nonempty]
      | some label =>
          simp only [wordProduct, separatedGenerator, List.map_cons, List.prod_cons]
          rw [show (word.map (separatedGenerator separator generators)).prod =
              wordProduct (separatedGenerator separator generators) word from rfl,
            induction]
          have fractured_nonempty := fracture_ne_nil word
          obtain ⟨block, blocks, fracture_eq⟩ :=
            List.exists_cons_of_ne_nil fractured_nonempty
          rw [show fracture (some label :: word) =
              (fracture word).modifyHead (label :: ·) by rfl, fracture_eq]
          simp only [List.modifyHead, List.map_cons, wordProduct, List.prod_cons]
          simpa [wordProduct] using (intercalatedProduct_modifyHead separator (generators label)
            (List.cons_ne_nil (wordProduct generators block)
              (blocks.map (wordProduct generators)))).symm

/-- A labelled family is mortal when a nonempty generator word multiplies to zero. -/
def IsMortal {α M : Type*} [MonoidWithZero M] (generators : α → M) : Prop :=
  WordSeries.HasNonemptyZero (wordProduct generators)

/-- In a nontrivial monoid, the empty product is not zero, so an explicit nonemptiness condition
on a zero word is redundant. -/
theorem isMortal_iff_exists_wordProduct_eq_zero {α M : Type*}
    [MonoidWithZero M] [Nontrivial M] (generators : α → M) :
    IsMortal generators ↔ ∃ word, wordProduct generators word = 0 := by
  exact WordSeries.hasNonemptyZero_iff_hasZero_of_nil_ne
    (wordProduct generators) (by simp)

theorem unit_sandwich_eq_zero_iff {M : Type*} [MonoidWithZero M]
    {left middle right : M} (left_unit : IsUnit left) (right_unit : IsUnit right) :
    left * middle * right = 0 ↔ middle = 0 := by
  constructor
  · intro sandwich_zero
    have left_cancelled : middle * right = 0 := by
      apply left_unit.mul_left_cancel
      simpa [mul_assoc] using sandwich_zero
    apply right_unit.mul_right_cancel
    simpa using left_cancelled
  · rintro rfl
    simp

/-- The nonsingular inverse of a unit square matrix is again a unit. -/
theorem nonsingInv_isUnit {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (matrix : Square ι K) (matrix_unit : IsUnit matrix) :
    IsUnit matrix⁻¹ := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_nonsing_inv]
  obtain ⟨unit, unit_eq⟩ := (Matrix.isUnit_iff_isUnit_det matrix).mp matrix_unit
  rw [← unit_eq, Ring.inverse_unit]
  exact Units.isUnit unit⁻¹

/-- A unit square matrix is a left inverse of its nonsingular inverse. -/
theorem mul_nonsingInv_of_isUnit {ι K : Type*}
    [Fintype ι] [DecidableEq ι] [Field K]
    (matrix : Square ι K) (matrix_unit : IsUnit matrix) :
    matrix * matrix⁻¹ = 1 :=
  Matrix.mul_nonsing_inv matrix
    ((Matrix.isUnit_iff_isUnit_det matrix).mp matrix_unit)

/-- The nonsingular inverse of a unit square matrix is its left inverse. -/
theorem nonsingInv_mul_of_isUnit {ι K : Type*}
    [Fintype ι] [DecidableEq ι] [Field K]
    (matrix : Square ι K) (matrix_unit : IsUnit matrix) :
    matrix⁻¹ * matrix = 1 :=
  Matrix.nonsing_inv_mul matrix
    ((Matrix.isUnit_iff_isUnit_det matrix).mp matrix_unit)

/-- A word over unit generators is a unit. -/
theorem wordProduct_isUnit_of_mem {α M : Type*} [Monoid M]
    (generators : α → M) (word : List α)
    (generator_unit : ∀ label ∈ word, IsUnit (generators label)) :
    IsUnit (wordProduct generators word) := by
  induction word with
  | nil => simp
  | cons head tail induction =>
      rw [wordProduct_cons]
      exact (generator_unit head (by simp)).mul
        (induction fun label label_mem => generator_unit label (by simp [label_mem]))

/-- A word over a family of unit generators is a unit. -/
theorem wordProduct_isUnit {α M : Type*} [Monoid M]
    (generators : α → M) (generator_unit : ∀ label, IsUnit (generators label))
    (word : List α) : IsUnit (wordProduct generators word) :=
  wordProduct_isUnit_of_mem generators word fun label _ => generator_unit label

/-- A nontrivial monoid family consisting entirely of units is immortal. -/
theorem not_isMortal_of_forall_isUnit {α M : Type*} [MonoidWithZero M] [Nontrivial M]
    (generators : α → M) (generator_unit : ∀ label, IsUnit (generators label)) :
    ¬IsMortal generators := by
  rintro ⟨word, _, product_zero⟩
  exact (wordProduct_isUnit generators generator_unit word).ne_zero product_zero

/-! ## Common eigenvector certificates -/

/-- A common eigenvector propagates through every matrix word with the product eigenvalue. -/
theorem wordProduct_mulVec_common_eigenvector
    {α ι R : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]
    (generators : α → Square ι R) (column : ι → R) (eigenvalue : α → R)
    (eigenvector : ∀ label, Matrix.mulVec (generators label) column =
      eigenvalue label • column) (word : List α) :
    Matrix.mulVec (wordProduct generators word) column =
      (word.map eigenvalue).prod • column := by
  induction word with
  | nil => simp
  | cons label tail induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec, induction, Matrix.mulVec_smul,
        eigenvector, List.map_cons, List.prod_cons, smul_smul]
      rw [mul_comm]

/-- A nonzero common eigenvector with nonzero eigenvalues certifies immortality over a field. -/
theorem not_isMortal_of_common_eigenvector
    {α ι K : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (generators : α → Square ι K) (column : ι → K) (eigenvalue : α → K)
    (column_nonzero : column ≠ 0)
    (eigenvalue_nonzero : ∀ label, eigenvalue label ≠ 0)
    (eigenvector : ∀ label, Matrix.mulVec (generators label) column =
      eigenvalue label • column) :
    ¬IsMortal generators := by
  rintro ⟨word, _, product_zero⟩
  have product_eigenvalue_nonzero : (word.map eigenvalue).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro zero_mem
    obtain ⟨label, _, label_zero⟩ := List.mem_map.mp zero_mem
    exact eigenvalue_nonzero label label_zero
  have image_nonzero : (word.map eigenvalue).prod • column ≠ 0 :=
    smul_ne_zero product_eigenvalue_nonzero column_nonzero
  apply image_nonzero
  rw [← wordProduct_mulVec_common_eigenvector generators column eigenvalue eigenvector,
    product_zero, Matrix.zero_mulVec]

/-! ## Finite ray-action certificates -/

/-- State reached by a word acting from right to left on a projective-ray automaton. -/
def rayState {α σ : Type*} (transition : α → σ → σ) : List α → σ → σ
  | [], state => state
  | label :: tail, state => transition label (rayState transition tail state)

/-- Scalar accumulated by a word acting from right to left on a projective-ray automaton. -/
def rayWeight {α σ K : Type*} [CommMonoid K]
    (transition : α → σ → σ) (weight : α → σ → K) : List α → σ → K
  | [], _ => 1
  | label :: tail, state =>
      rayWeight transition weight tail state *
        weight label (rayState transition tail state)

/-- A matrix word follows the induced ray automaton and accumulates its transition weights. -/
theorem wordProduct_mulVec_ray_action
    {α σ ι R : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]
    (generators : α → Square ι R) (ray : σ → ι → R)
    (transition : α → σ → σ) (weight : α → σ → R)
    (action : ∀ label state,
      Matrix.mulVec (generators label) (ray state) =
        weight label state • ray (transition label state))
    (word : List α) (state : σ) :
    Matrix.mulVec (wordProduct generators word) (ray state) =
      rayWeight transition weight word state •
        ray (rayState transition word state) := by
  induction word with
  | nil => simp [rayState, rayWeight]
  | cons label tail induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec, induction, Matrix.mulVec_smul,
        action, rayState, rayWeight, smul_smul]

/-- A nonvanishing projective-ray automaton certifies immortality. Unlike a common-eigenvector
certificate, generators may permute or reset a family of rays. -/
theorem not_isMortal_of_ray_action
    {α σ ι K : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (generators : α → Square ι K) (ray : σ → ι → K)
    (transition : α → σ → σ) (weight : α → σ → K) (initial : σ)
    (ray_nonzero : ∀ state, ray state ≠ 0)
    (weight_nonzero : ∀ label state, weight label state ≠ 0)
    (action : ∀ label state,
      Matrix.mulVec (generators label) (ray state) =
        weight label state • ray (transition label state)) :
    ¬IsMortal generators := by
  rintro ⟨word, _, product_zero⟩
  have every_weight_nonzero :
      ∀ tail state, rayWeight transition weight tail state ≠ 0 := by
    intro tail state
    induction tail generalizing state with
    | nil => simp [rayWeight]
    | cons label tail induction =>
        rw [rayWeight]
        exact mul_ne_zero (induction state)
          (weight_nonzero label (rayState transition tail state))
  have accumulated_nonzero :
      rayWeight transition weight word initial ≠ 0 :=
    every_weight_nonzero word initial
  have image_nonzero :
      rayWeight transition weight word initial •
          ray (rayState transition word initial) ≠ 0 :=
    smul_ne_zero accumulated_nonzero
      (ray_nonzero (rayState transition word initial))
  apply image_nonzero
  rw [← wordProduct_mulVec_ray_action
    generators ray transition weight action word initial,
    product_zero, Matrix.zero_mulVec]

/-- Canonical relabelling that separates zero from the positive natural numbers. -/
def natEquivOption : Nat ≃ Option Nat where
  toFun
    | 0 => none
    | n + 1 => some n
  invFun
    | none => 0
    | some n => n + 1
  left_inv n := by cases n <;> rfl
  right_inv n := by cases n <;> rfl

@[simp]
theorem natEquivOption_zero : natEquivOption 0 = none := rfl

@[simp]
theorem natEquivOption_succ (n : Nat) : natEquivOption (n + 1) = some n := rfl

/-- Relabelling a family along an equivalence preserves mortality. -/
theorem isMortal_comp_equiv {α β M : Type*} [MonoidWithZero M]
    (generators : β → M) (equivalence : α ≃ β) :
    IsMortal (generators ∘ equivalence) ↔ IsMortal generators := by
  rw [IsMortal, show wordProduct (generators ∘ equivalence) =
      WordSeries.relabel (wordProduct generators) equivalence by
        funext word
        exact wordProduct_comp generators equivalence word]
  exact WordSeries.hasNonemptyZero_relabel_equiv _ equivalence

/-- Every zero-preserving monoid homomorphism sends mortal families to mortal families. -/
theorem isMortal_map {α M N : Type*} [MonoidWithZero M] [MonoidWithZero N]
    (map : M →*₀ N) (generators : α → M) :
    IsMortal generators → IsMortal (map ∘ generators) := by
  rintro ⟨word, word_nonempty, product_zero⟩
  refine ⟨word, word_nonempty, ?_⟩
  calc
    wordProduct (map ∘ generators) word =
        map (wordProduct generators word) := by
          simpa using wordProduct_map map.toMonoidHom generators word
    _ = 0 := by simp [product_zero]

/-- Immortality in one zero-preserving quotient certifies immortality of the original family. -/
theorem not_isMortal_of_map_not_isMortal
    {α M N : Type*} [MonoidWithZero M] [MonoidWithZero N]
    (map : M →*₀ N) (generators : α → M)
    (image_immortal : ¬IsMortal (map ∘ generators)) :
    ¬IsMortal generators :=
  fun mortality => image_immortal (isMortal_map map generators mortality)

/-- An injective zero-preserving monoid map reflects and preserves mortality. -/
theorem isMortal_map_iff {α M N : Type*} [MonoidWithZero M] [MonoidWithZero N]
    (map : M →*₀ N) (injective : Function.Injective map) (generators : α → M) :
    IsMortal (map ∘ generators) ↔ IsMortal generators := by
  constructor
  · rintro ⟨word, word_nonempty, product_zero⟩
    refine ⟨word, word_nonempty, ?_⟩
    apply injective
    calc
      map (wordProduct generators word) =
          wordProduct (map ∘ generators) word := by
            simpa using (wordProduct_map map.toMonoidHom generators word).symm
      _ = 0 := product_zero
      _ = map 0 := map.map_zero.symm
  · exact isMortal_map map generators

/-- Simultaneously reindexing both matrix axes preserves mortality. -/
theorem isMortal_reindex_iff {α ι κ R : Type*} [CommSemiring R]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (equivalence : ι ≃ κ) (generators : α → Square ι R) :
    IsMortal (Matrix.reindex equivalence equivalence ∘ generators) ↔ IsMortal generators := by
  let reindexMap : Square ι R →*₀ Square κ R :=
    (Matrix.reindexAlgEquiv R R equivalence).toAlgHom.toRingHom.toMonoidWithZeroHom
  exact isMortal_map_iff reindexMap
    (Matrix.reindexAlgEquiv R R equivalence).injective generators

/-! ## Independent nonzero generator scaling -/

theorem wordProduct_smulMatrix {α ι K : Type*} [CommSemiring K] [Fintype ι]
    [DecidableEq ι] (scales : α → K) (generators : α → Square ι K)
    (word : List α) :
    wordProduct (fun label => scales label • generators label) word =
      (word.map scales).prod • wordProduct generators word := by
  induction word with
  | nil => simp
  | cons label tail induction =>
      simp only [wordProduct_cons, List.map_cons, List.prod_cons, induction]
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- Multiplying each matrix generator by an independently chosen nonzero field scalar preserves
every nonempty zero product. -/
theorem isMortal_smulMatrix_iff {α ι K : Type*} [Field K] [Fintype ι]
    [DecidableEq ι] (scales : α → K) (scale_nonzero : ∀ label, scales label ≠ 0)
    (generators : α → Square ι K) :
    IsMortal (fun label => scales label • generators label) ↔ IsMortal generators := by
  constructor
  · rintro ⟨word, word_nonempty, scaled_zero⟩
    refine ⟨word, word_nonempty, ?_⟩
    rw [wordProduct_smulMatrix] at scaled_zero
    have factors_nonzero : 0 ∉ word.map scales := by
      intro zero_mem
      obtain ⟨label, _, scale_zero⟩ := List.mem_map.mp zero_mem
      exact scale_nonzero label scale_zero
    exact (smul_eq_zero.mp scaled_zero).resolve_left
      (List.prod_ne_zero factors_nonzero)
  · rintro ⟨word, word_nonempty, product_zero⟩
    refine ⟨word, word_nonempty, ?_⟩
    rw [wordProduct_smulMatrix, product_zero, smul_zero]

/-! ## Integral matrices inside rational matrices -/

/-- Entrywise scalar extension commutes with every matrix word product. -/
theorem wordProduct_mapMatrix {α ι R S : Type*} [Semiring R] [Semiring S]
    [Fintype ι] [DecidableEq ι] (map : R →+* S)
    (generators : α → Square ι R) (word : List α) :
    (wordProduct generators word).map map =
      wordProduct (fun label => (generators label).map map) word := by
  simpa [Function.comp_def] using
    (wordProduct_map map.mapMatrix.toMonoidHom generators word).symm

/-- Entrywise scalar extension commutes with outer products. -/
theorem vecMulVec_map {m n R S : Type*} [Semiring R] [Semiring S]
    (map : R →+* S) (column : m → R) (row : n → R) :
    (Matrix.vecMulVec column row).map map =
      Matrix.vecMulVec (map ∘ column) (map ∘ row) := by
  ext i j
  simp [Matrix.vecMulVec]

/-- Entrywise inclusion of an integer matrix into the rationals. -/
def castMatrix {m n : Type*} (matrix : Matrix m n ℤ) : Matrix m n ℚ :=
  matrix.map (Int.castRingHom ℚ)

/-- Entrywise inclusion of an integer vector into the rationals. -/
def castVector {ι : Type*} (vector : ι → ℤ) : ι → ℚ :=
  (Int.castRingHom ℚ) ∘ vector

theorem castMatrix_det {n : Type*} [Fintype n] [DecidableEq n]
    (matrix : Matrix n n ℤ) :
    (castMatrix matrix).det = (matrix.det : ℚ) :=
  ((Int.castRingHom ℚ).map_det matrix).symm

theorem castMatrix_eq_zero_iff {m n : Type*} (matrix : Matrix m n ℤ) :
    castMatrix matrix = 0 ↔ matrix = 0 := by
  constructor
  · intro cast_zero
    ext i j
    have entry := congr_fun (congr_fun cast_zero i) j
    simpa [castMatrix] using entry
  · rintro rfl
    simp [castMatrix]

theorem castMatrix_wordProduct {α ι : Type*} [Fintype ι] [DecidableEq ι]
    (generators : α → Square ι ℤ) (word : List α) :
    castMatrix (wordProduct generators word) =
      wordProduct (castMatrix ∘ generators) word := by
  exact wordProduct_mapMatrix (Int.castRingHom ℚ) generators word

theorem isMortal_cast_iff {α ι : Type*} [Fintype ι] [DecidableEq ι]
    (generators : α → Square ι ℤ) :
    IsMortal (castMatrix ∘ generators) ↔ IsMortal generators := by
  constructor
  · rintro ⟨word, word_nonempty, product_zero⟩
    refine ⟨word, word_nonempty, ?_⟩
    apply (castMatrix_eq_zero_iff _).mp
    rw [castMatrix_wordProduct]
    exact product_zero
  · rintro ⟨word, word_nonempty, product_zero⟩
    refine ⟨word, word_nonempty, ?_⟩
    rw [← castMatrix_wordProduct, product_zero]
    simp [castMatrix]

/-! ## Simultaneous change of basis -/

theorem wordProduct_conjugate {α ι R : Type*} [CommSemiring R] [Fintype ι]
    [DecidableEq ι] (generators : α → Square ι R) (change inverse : Square ι R)
    (change_inverse : change * inverse = 1) (inverse_change : inverse * change = 1)
    (word : List α) :
    wordProduct (fun label => inverse * generators label * change) word =
      inverse * wordProduct generators word * change := by
  induction word with
  | nil => simp [inverse_change]
  | cons head tail induction =>
      simp only [wordProduct_cons, induction]
      calc
        (inverse * generators head * change) *
              (inverse * wordProduct generators tail * change) =
            inverse * generators head * (change * inverse) *
              wordProduct generators tail * change := by
                simp only [Matrix.mul_assoc]
        _ = inverse * (generators head * wordProduct generators tail) * change := by
          rw [change_inverse]
          simp only [mul_one, Matrix.mul_assoc]

/-- Simultaneous conjugation by mutually inverse matrices preserves mortality. -/
theorem isMortal_conjugate_iff {α ι R : Type*} [CommSemiring R] [Fintype ι]
    [DecidableEq ι] (generators : α → Square ι R) (change inverse : Square ι R)
    (change_inverse : change * inverse = 1) (inverse_change : inverse * change = 1) :
    IsMortal (fun label => inverse * generators label * change) ↔ IsMortal generators := by
  constructor
  · rintro ⟨word, word_nonempty, product_zero⟩
    refine ⟨word, word_nonempty, ?_⟩
    have conjugate_zero :
        inverse * wordProduct generators word * change = 0 := by
      rw [← wordProduct_conjugate generators change inverse change_inverse inverse_change]
      exact product_zero
    calc
      wordProduct generators word =
          1 * wordProduct generators word * 1 := by simp
      _ = (change * inverse) * wordProduct generators word * (change * inverse) := by
        rw [change_inverse]
      _ = change * (inverse * wordProduct generators word * change) * inverse := by
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [conjugate_zero]; simp
  · rintro ⟨word, word_nonempty, product_zero⟩
    refine ⟨word, word_nonempty, ?_⟩
    rw [wordProduct_conjugate generators change inverse change_inverse inverse_change,
      product_zero]
    simp

/-! ## Common-image restriction -/

theorem wordProduct_intertwine {α Large Small R : Type*} [CommSemiring R]
    [Fintype Large] [DecidableEq Large] [Fintype Small] [DecidableEq Small]
    (ambient : α → Square Large R)
    (restricted : α → Square Small R) (embed : Matrix Large Small R)
    (intertwine : ∀ label, ambient label * embed = embed * restricted label)
    (word : List α) :
    wordProduct ambient word * embed = embed * wordProduct restricted word := by
  induction word with
  | nil => simp
  | cons head tail induction =>
      rw [wordProduct_cons, wordProduct_cons]
      calc
        ambient head * wordProduct ambient tail * embed =
            ambient head * (wordProduct ambient tail * embed) := by
              rw [Matrix.mul_assoc]
        _ = ambient head * (embed * wordProduct restricted tail) := by
          rw [induction]
        _ = (ambient head * embed) * wordProduct restricted tail := by
          rw [Matrix.mul_assoc]
        _ = (embed * restricted head) * wordProduct restricted tail := by
          rw [intertwine]
        _ = embed * (restricted head * wordProduct restricted tail) := by
          rw [Matrix.mul_assoc]

theorem wordProduct_restrict {α Large Small R : Type*} [CommSemiring R]
    [Fintype Large] [DecidableEq Large] [Fintype Small] [DecidableEq Small]
    (ambient : α → Square Large R) (restricted : α → Square Small R)
    (embed : Matrix Large Small R) (retract : Matrix Small Large R)
    (retract_embed : retract * embed = 1)
    (intertwine : ∀ label, ambient label * embed = embed * restricted label)
    (word : List α) :
    wordProduct restricted word = retract * wordProduct ambient word * embed := by
  calc
    wordProduct restricted word =
        1 * wordProduct restricted word := by simp
    _ = (retract * embed) * wordProduct restricted word := by rw [retract_embed]
    _ = retract * (embed * wordProduct restricted word) := by
      simp only [Matrix.mul_assoc]
    _ = retract * (wordProduct ambient word * embed) := by
      rw [wordProduct_intertwine ambient restricted embed intertwine word]
    _ = retract * wordProduct ambient word * embed := by
      simp only [Matrix.mul_assoc]

/-- Restriction to a common image preserves mortality when one ambient generator factors through
the restricted carrier. A restricted zero lifts by appending that generator. -/
theorem isMortal_commonImage_iff {α Large Small R : Type*} [CommSemiring R]
    [Fintype Large] [DecidableEq Large] [Fintype Small] [DecidableEq Small]
    (ambient : α → Square Large R) (restricted : α → Square Small R)
    (embed : Matrix Large Small R) (retract : Matrix Small Large R)
    (retract_embed : retract * embed = 1)
    (intertwine : ∀ label, ambient label * embed = embed * restricted label)
    (reset : α) (resetTail : Matrix Small Large R)
    (reset_factor : ambient reset = embed * resetTail) :
    IsMortal restricted ↔ IsMortal ambient := by
  constructor
  · rintro ⟨word, _, restricted_zero⟩
    refine ⟨word ++ [reset], by simp, ?_⟩
    rw [wordProduct_append]
    simp only [wordProduct_cons, wordProduct_nil, mul_one]
    rw [reset_factor, ← Matrix.mul_assoc,
      wordProduct_intertwine ambient restricted embed intertwine, restricted_zero]
    simp
  · rintro ⟨word, word_nonempty, ambient_zero⟩
    refine ⟨word, word_nonempty, ?_⟩
    rw [wordProduct_restrict ambient restricted embed retract retract_embed intertwine,
      ambient_zero]
    simp

/-! ## Zero-block dimension padding -/

/-- Adjoin an identically zero square block. This preserves multiplication but not the identity. -/
def zeroPad {ι κ R : Type*} [Zero R] (matrix : Square ι R) : Square (ι ⊕ κ) R
  | .inl row, .inl column => matrix row column
  | _, _ => 0

theorem zeroPad_mul {ι κ R : Type*} [CommSemiring R] [Fintype ι] [Fintype κ]
    (left right : Square ι R) :
    zeroPad (κ := κ) (left * right) = zeroPad left * zeroPad right := by
  ext row column
  cases row <;> cases column <;>
    simp [zeroPad, Matrix.mul_apply, Fintype.sum_sum_type]

theorem zeroPad_eq_zero_iff {ι κ R : Type*} [Zero R] (matrix : Square ι R) :
    zeroPad (κ := κ) matrix = 0 ↔ matrix = 0 := by
  constructor
  · intro padded_zero
    ext row column
    have entry := congr_fun (congr_fun padded_zero (.inl row)) (.inl column)
    simpa [zeroPad] using entry
  · rintro rfl
    ext row column
    cases row <;> cases column <;> rfl

theorem wordProduct_zeroPad_cons {α ι κ R : Type*} [CommSemiring R]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (generators : α → Square ι R) (head : α) (tail : List α) :
    wordProduct (zeroPad (κ := κ) ∘ generators) (head :: tail) =
      zeroPad (wordProduct generators (head :: tail)) := by
  induction tail generalizing head with
  | nil =>
      simp [wordProduct]
  | cons next tail induction =>
      calc
        wordProduct (zeroPad (κ := κ) ∘ generators) (head :: next :: tail) =
            zeroPad (generators head) *
              wordProduct (zeroPad (κ := κ) ∘ generators) (next :: tail) := by
          rw [wordProduct_cons]
          rfl
        _ = zeroPad (generators head) *
              zeroPad (wordProduct generators (next :: tail)) := by
            rw [induction]
        _ = zeroPad (generators head * wordProduct generators (next :: tail)) :=
          (zeroPad_mul _ _).symm
        _ = zeroPad (wordProduct generators (head :: next :: tail)) := by
          simp only [wordProduct_cons]

/-- Adjoining a zero block preserves nonempty-word mortality exactly. -/
theorem isMortal_zeroPad_iff {α ι κ R : Type*} [CommSemiring R]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (generators : α → Square ι R) :
    IsMortal (zeroPad (κ := κ) ∘ generators) ↔ IsMortal generators := by
  constructor
  · rintro ⟨word, word_nonempty, padded_zero⟩
    obtain ⟨head, tail, rfl⟩ := List.exists_cons_of_ne_nil word_nonempty
    refine ⟨head :: tail, List.cons_ne_nil _ _, ?_⟩
    apply (zeroPad_eq_zero_iff (κ := κ) _).mp
    rw [← wordProduct_zeroPad_cons]
    exact padded_zero
  · rintro ⟨word, word_nonempty, product_zero⟩
    obtain ⟨head, tail, rfl⟩ := List.exists_cons_of_ne_nil word_nonempty
    refine ⟨head :: tail, List.cons_ne_nil _ _, ?_⟩
    rw [wordProduct_zeroPad_cons, product_zero]
    exact (zeroPad_eq_zero_iff (κ := κ) (0 : Square ι R)).mpr rfl

/-! ## Common fixed columns -/

theorem wordProduct_mulVec_fixed {α ι R : Type*} [CommSemiring R] [Fintype ι]
    [DecidableEq ι] (generators : α → Square ι R) (anchor : ι → R)
    (fixed : ∀ label, generators label *ᵥ anchor = anchor) (word : List α) :
    wordProduct generators word *ᵥ anchor = anchor := by
  induction word with
  | nil => simp
  | cons head tail induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec, induction, fixed]

theorem wordProduct_ne_zero_of_fixed {α ι R : Type*} [CommSemiring R] [Fintype ι]
    [DecidableEq ι] (generators : α → Square ι R) (anchor : ι → R)
    (fixed : ∀ label, generators label *ᵥ anchor = anchor) (anchor_nonzero : anchor ≠ 0)
    (word : List α) :
    wordProduct generators word ≠ 0 := by
  intro product_zero
  have := wordProduct_mulVec_fixed generators anchor fixed word
  rw [product_zero] at this
  exact anchor_nonzero (by simpa using this.symm)

theorem vecMul_wordProduct_ne_zero_of_fixed {α ι R : Type*} [CommSemiring R]
    [Fintype ι] [DecidableEq ι] (generators : α → Square ι R) (anchor row : ι → R)
    (fixed : ∀ label, generators label *ᵥ anchor = anchor)
    (row_anchor_nonzero : row ⬝ᵥ anchor ≠ 0) (word : List α) :
    row ᵥ* wordProduct generators word ≠ 0 := by
  intro row_zero
  apply row_anchor_nonzero
  calc
    row ⬝ᵥ anchor =
        row ⬝ᵥ wordProduct generators word *ᵥ anchor := by
          rw [wordProduct_mulVec_fixed generators anchor fixed word]
    _ = (row ᵥ* wordProduct generators word) ⬝ᵥ anchor := by
      rw [Matrix.dotProduct_mulVec]
    _ = 0 := by rw [row_zero]; simp

/-! ## Anti-isomorphism by transposition -/

theorem wordProduct_transpose {α ι R : Type*} [CommSemiring R] [Fintype ι]
    [DecidableEq ι] (generators : α → Square ι R) (word : List α) :
    wordProduct (Matrix.transpose ∘ generators) word =
      (wordProduct generators word.reverse)ᵀ := by
  rw [wordProduct, wordProduct, Matrix.transpose_list_prod]
  simp [List.map_map, Function.comp_def]

theorem scalarCoefficient_transpose {α ι R : Type*} [CommSemiring R] [Fintype ι]
    [DecidableEq ι] (generators : α → Square ι R) (row column : ι → R)
    (word : List α) :
    column ⬝ᵥ wordProduct (Matrix.transpose ∘ generators) word *ᵥ row =
      row ⬝ᵥ wordProduct generators word.reverse *ᵥ column := by
  rw [wordProduct_transpose, Matrix.mulVec_transpose, dotProduct_comm,
    ← Matrix.dotProduct_mulVec]

/-- Transposition and word reversal preserve matrix mortality. -/
theorem isMortal_transpose_iff {α ι R : Type*} [CommSemiring R] [Fintype ι]
    [DecidableEq ι] (generators : α → Square ι R) :
    IsMortal (Matrix.transpose ∘ generators) ↔ IsMortal generators := by
  constructor
  · rintro ⟨word, word_nonempty, product_zero⟩
    refine ⟨word.reverse, by simpa using word_nonempty, ?_⟩
    apply Matrix.transpose_injective
    simpa [wordProduct_transpose] using product_zero
  · rintro ⟨word, word_nonempty, product_zero⟩
    refine ⟨word.reverse, by simpa using word_nonempty, ?_⟩
    rw [wordProduct_transpose, List.reverse_reverse, product_zero, Matrix.transpose_zero]

end MatrixMortality
