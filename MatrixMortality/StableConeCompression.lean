import MatrixMortality.MatrixSemigroup

/-!
# Stable-cone compression

A word whose every complete block is bracketed by one separator `Y = i ∘ q` acts through the
separator carrier. Multiplication of endomorphisms is composition: the rightmost factor acts
first. Thus the stable word

`Y * M₁ * Y * M₂ * Y * ... * Mₖ * Y`

compresses to the carrier word with letters `q ∘ Mⱼ ∘ i`, between the boundary maps `i` and `q`.
-/

namespace MatrixMortality

namespace StableConeCompression

variable {K V W : Type*} [CommSemiring K]
  [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]

/-- A list of complete blocks, each followed by the separator and preceded by one initial
separator. For `[M₁, ..., Mₖ]` this is `Y * M₁ * Y * ... * Mₖ * Y`. -/
def stableProduct (separator : Module.End K V) (blocks : List (Module.End K V)) :
    Module.End K V :=
  separator * wordProduct (fun block => block * separator) blocks

/-- Action of one complete ambient block on the separator carrier. -/
def compressedBlock (embed : W →ₗ[K] V) (retract : V →ₗ[K] W)
    (block : Module.End K V) : Module.End K W :=
  retract.comp (block.comp embed)

/-- Every separator-bracketed ambient block word factors through the separator carrier. -/
theorem stableProduct_eq_compressed
    (embed : W →ₗ[K] V) (retract : V →ₗ[K] W) (separator : Module.End K V)
    (separator_eq : separator = embed.comp retract) (blocks : List (Module.End K V)) :
    stableProduct separator blocks =
      embed.comp ((wordProduct (compressedBlock embed retract) blocks).comp retract) := by
  induction blocks with
  | nil =>
      ext point
      simp [stableProduct, separator_eq, LinearMap.comp_apply]
  | cons block blocks induction =>
      ext point
      simp only [stableProduct, wordProduct_cons, Module.End.mul_apply, LinearMap.comp_apply]
      rw [show separator
          (block (separator (wordProduct (fun next => next * separator) blocks point))) =
            separator (block (stableProduct separator blocks point)) by
          rfl,
        LinearMap.congr_fun induction]
      simp [separator_eq, compressedBlock, LinearMap.comp_apply]

/-- Canonical complete-block action on the image of the separator. -/
def rangeCompressedBlock (separator : Module.End K V) (block : Module.End K V) :
    Module.End K separator.range :=
  separator.rangeRestrict.comp (block.comp separator.range.subtype)

/-- Every stable word factors canonically through the image of its separator. -/
theorem stableProduct_eq_rangeCompressed (separator : Module.End K V)
    (blocks : List (Module.End K V)) :
    stableProduct separator blocks =
      separator.range.subtype.comp
        ((wordProduct (rangeCompressedBlock separator) blocks).comp separator.rangeRestrict) := by
  change stableProduct separator blocks =
    separator.range.subtype.comp
      ((wordProduct
        (compressedBlock separator.range.subtype separator.rangeRestrict) blocks).comp
          separator.rangeRestrict)
  exact stableProduct_eq_compressed separator.range.subtype separator.rangeRestrict separator rfl
    blocks

/-- If every compressed block is a scalar endomorphism, a stable word is the product of those
scalars times its boundary separator. In particular, the order of its complete blocks is lost. -/
theorem stableProduct_eq_smul
    (embed : W →ₗ[K] V) (retract : V →ₗ[K] W) (separator : Module.End K V)
    (separator_eq : separator = embed.comp retract) (coefficient : Module.End K V → K)
    (compressed_eq : ∀ block,
      compressedBlock embed retract block = coefficient block • LinearMap.id)
    (blocks : List (Module.End K V)) :
    stableProduct separator blocks = (blocks.map coefficient).prod • separator := by
  rw [stableProduct_eq_compressed embed retract separator separator_eq]
  have compressedWord :
      wordProduct (compressedBlock embed retract) blocks =
        (blocks.map coefficient).prod • LinearMap.id := by
    induction blocks with
    | nil => simp [Module.End.one_eq_id]
    | cons block blocks induction =>
        rw [wordProduct_cons, compressed_eq, induction]
        ext point
        simpa only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
          List.map_cons, List.prod_cons] using
          smul_smul (coefficient block) ((blocks.map coefficient).prod : K) point
  rw [compressedWord]
  ext point
  simp [separator_eq, LinearMap.comp_apply]

section RankOne

variable {F A B : Type*} [Field F]
  [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]

/-- On a one-dimensional separator carrier, every complete block has one canonical scalar
coefficient. -/
theorem exists_rankOne_coefficients (embed : B →ₗ[F] A) (retract : A →ₗ[F] B)
    (rank_one : Module.finrank F B = 1) :
    ∃ coefficient : Module.End F A → F, ∀ block,
      compressedBlock embed retract block = coefficient block • LinearMap.id := by
  let coefficient : Module.End F A → F := fun block =>
    (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one rank_one
      (compressedBlock embed retract block)).choose
  refine ⟨coefficient, fun block => ?_⟩
  exact (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one rank_one
    (compressedBlock embed retract block)).choose_spec.1

/-- Every stable word through a one-dimensional separator carrier is its separator multiplied by
the product of block-local scalars. -/
theorem exists_stableProduct_eq_smul_of_finrank_eq_one
    (embed : B →ₗ[F] A) (retract : A →ₗ[F] B) (separator : Module.End F A)
    (separator_eq : separator = embed.comp retract) (rank_one : Module.finrank F B = 1) :
    ∃ coefficient : Module.End F A → F, ∀ blocks,
      stableProduct separator blocks = (blocks.map coefficient).prod • separator := by
  obtain ⟨coefficient, compressed_eq⟩ := exists_rankOne_coefficients embed retract rank_one
  exact ⟨coefficient,
    stableProduct_eq_smul embed retract separator separator_eq coefficient compressed_eq⟩

/-- A rank-one separator makes every stable word a product of block-local scalars times that
separator, with the separator image used as the canonical carrier. -/
theorem exists_stableProduct_eq_smul_of_finrank_range_eq_one
    (separator : Module.End F A) (rank_one : Module.finrank F separator.range = 1) :
    ∃ coefficient : Module.End F A → F, ∀ blocks,
      stableProduct separator blocks = (blocks.map coefficient).prod • separator := by
  exact exists_stableProduct_eq_smul_of_finrank_eq_one separator.range.subtype
    separator.rangeRestrict separator rfl rank_one

end RankOne

end StableConeCompression

end MatrixMortality
