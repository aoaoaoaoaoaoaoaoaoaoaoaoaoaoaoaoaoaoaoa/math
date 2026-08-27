import MatrixMortality.FullMatrixAlgebra
import MatrixMortality.InternalSandwich

/-!
# Full matrix algebras force exact behavior dimension

If physical word products span the full matrix algebra, every nonzero interface input reaches
the entire state space and every nonzero interface output observes it faithfully.  The
reachable-observable quotient of any nonzero internal sandwich therefore retains the ambient
dimension.
-/

namespace MatrixMortality

open scoped Matrix

variable {K ι Q Glyph : Type*} [Field K] [Fintype ι] [DecidableEq ι]
  [AddCommGroup Q] [Module K Q]

/-- The linear actions corresponding to a family of square matrices. -/
def matrixEndGenerators (generators : Glyph → Square ι K) :
    Glyph → Module.End K (ι → K) :=
  fun label => Matrix.toLin' (generators label)

theorem wordProduct_matrixEndGenerators (generators : Glyph → Square ι K)
    (word : List Glyph) :
    wordProduct (matrixEndGenerators generators) word =
      Matrix.toLin' (wordProduct generators word) :=
  wordProduct_toLin generators word

theorem exists_matrix_mulVec_eq_of_ne_zero
    {source : ι → K} (source_nonzero : source ≠ 0) (target : ι → K) :
    ∃ matrix : Square ι K, matrix *ᵥ source = target := by
  classical
  have exists_coordinate : ∃ index, source index ≠ 0 := by
    by_contra no_coordinate
    push Not at no_coordinate
    apply source_nonzero
    funext index
    exact no_coordinate index
  obtain ⟨index, coordinate_nonzero⟩ := exists_coordinate
  refine ⟨Matrix.vecMulVec target (Pi.single index (source index)⁻¹), ?_⟩
  ext row
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  rw [Fintype.sum_eq_single index]
  · simp [coordinate_nonzero]
  · intro other other_ne
    simp [Ne.symm other_ne]

theorem wordProductSpan_mulVec_mem_reachable
    (generators : Glyph → Square ι K) (input : Q →ₗ[K] (ι → K))
    (matrix : Square ι K) (matrix_mem : matrix ∈ wordProductSpan generators)
    (q : Q) :
    matrix *ᵥ input q ∈
      InternalSandwich.reachable (matrixEndGenerators generators) input := by
  refine Submodule.span_induction
    (p := fun candidate : Square ι K => fun _ ↦
      candidate *ᵥ input q ∈
        InternalSandwich.reachable (matrixEndGenerators generators) input)
    (s := Set.range (wordProduct generators))
    ?_ ?_ ?_ ?_ (by simpa only [wordProductSpan] using matrix_mem)
  · rintro _ ⟨word, rfl⟩
    apply Submodule.subset_span
    refine ⟨word, q, ?_⟩
    rw [wordProduct_matrixEndGenerators]
    rfl
  · simp
  · intro left right _ _ left_mem right_mem
    rw [Matrix.add_mulVec]
    exact
      (InternalSandwich.reachable (matrixEndGenerators generators) input).add_mem
        left_mem right_mem
  · intro scalar candidate _ candidate_mem
    rw [Matrix.smul_mulVec]
    exact
      (InternalSandwich.reachable (matrixEndGenerators generators) input).smul_mem
        scalar candidate_mem

/-- Full generated algebra and one nonzero input direction force complete reachability. -/
theorem reachable_eq_top_of_wordProductSpan_eq_top
    (generators : Glyph → Square ι K) (input : Q →ₗ[K] (ι → K))
    (full : wordProductSpan generators = ⊤) (input_nonzero : input ≠ 0) :
    InternalSandwich.reachable (matrixEndGenerators generators) input = ⊤ := by
  have exists_input : ∃ q, input q ≠ 0 := by
    by_contra no_input
    push Not at no_input
    apply input_nonzero
    apply LinearMap.ext
    intro q
    exact no_input q
  obtain ⟨q, input_q_nonzero⟩ := exists_input
  apply top_unique
  intro target _
  obtain ⟨matrix, action⟩ :=
    exists_matrix_mulVec_eq_of_ne_zero input_q_nonzero target
  rw [← action]
  apply wordProductSpan_mulVec_mem_reachable generators input
  rw [full]
  exact Submodule.mem_top

theorem wordProductSpan_output_mulVec_eq_zero
    (generators : Glyph → Square ι K) (input : Q →ₗ[K] (ι → K))
    (output : (ι → K) →ₗ[K] Q)
    (x : InternalSandwich.unobservable
      (matrixEndGenerators generators) input output)
    (matrix : Square ι K) (matrix_mem : matrix ∈ wordProductSpan generators) :
    output (matrix *ᵥ (x : ι → K)) = 0 := by
  have invisible_word :
      ∀ word : List Glyph,
        output (wordProduct (matrixEndGenerators generators) word
          (x : ι → K)) = 0 := by
    intro word
    have invisible_all :
        ∀ future : List Glyph,
          (x : InternalSandwich.reachable
            (matrixEndGenerators generators) input) ∈
              LinearMap.ker
                ((output.comp
                  (wordProduct (matrixEndGenerators generators) future)).domRestrict
                    (InternalSandwich.reachable
                      (matrixEndGenerators generators) input)) := by
      apply (Submodule.mem_iInf (fun future : List Glyph =>
        LinearMap.ker
          ((output.comp
            (wordProduct (matrixEndGenerators generators) future)).domRestrict
              (InternalSandwich.reachable
                (matrixEndGenerators generators) input)))).mp
      simpa only [InternalSandwich.unobservable] using x.property
    have invisible := invisible_all word
    exact LinearMap.mem_ker.mp invisible
  refine Submodule.span_induction
    (p := fun candidate : Square ι K => fun _ ↦
      output (candidate *ᵥ (x : ι → K)) = 0)
    (s := Set.range (wordProduct generators))
    ?_ ?_ ?_ ?_ (by simpa only [wordProductSpan] using matrix_mem)
  · rintro _ ⟨word, rfl⟩
    rw [← Matrix.toLin'_apply, ← wordProduct_matrixEndGenerators]
    exact invisible_word word
  · simp
  · intro left right _ _ left_zero right_zero
    rw [Matrix.add_mulVec, map_add, left_zero, right_zero, add_zero]
  · intro scalar candidate _ candidate_zero
    rw [Matrix.smul_mulVec, map_smul, candidate_zero, smul_zero]

/-- Full generated algebra and one nonzero output direction force complete observability. -/
theorem unobservable_eq_bot_of_wordProductSpan_eq_top
    (generators : Glyph → Square ι K) (input : Q →ₗ[K] (ι → K))
    (output : (ι → K) →ₗ[K] Q)
    (full : wordProductSpan generators = ⊤) (output_nonzero : output ≠ 0) :
    InternalSandwich.unobservable
      (matrixEndGenerators generators) input output = ⊥ := by
  have exists_output : ∃ target, output target ≠ 0 := by
    by_contra no_output
    push Not at no_output
    apply output_nonzero
    apply LinearMap.ext
    intro target
    exact no_output target
  obtain ⟨target, target_observed⟩ := exists_output
  rw [Submodule.eq_bot_iff]
  intro x invisible
  apply Subtype.ext
  by_contra x_nonzero
  obtain ⟨matrix, action⟩ :=
    exists_matrix_mulVec_eq_of_ne_zero x_nonzero target
  have matrix_mem : matrix ∈ wordProductSpan generators := by
    rw [full]
    exact Submodule.mem_top
  have vanished :=
    wordProductSpan_output_mulVec_eq_zero generators input output
      ⟨x, invisible⟩ matrix matrix_mem
  rw [action] at vanished
  exact target_observed vanished

/-- Every nonzero exact interface over a full generated matrix algebra has the ambient
reachable-observable dimension. -/
theorem quotient_finrank_eq_card_of_wordProductSpan_eq_top
    (generators : Glyph → Square ι K) (input : Q →ₗ[K] (ι → K))
    (output : (ι → K) →ₗ[K] Q)
    (full : wordProductSpan generators = ⊤)
    (input_nonzero : input ≠ 0) (output_nonzero : output ≠ 0) :
    Module.finrank K
        ((InternalSandwich.reachable (matrixEndGenerators generators) input) ⧸
          InternalSandwich.unobservable
            (matrixEndGenerators generators) input output) =
      Fintype.card ι := by
  have reachable_top :=
    reachable_eq_top_of_wordProductSpan_eq_top generators input full input_nonzero
  have unobservable_bot :=
    unobservable_eq_bot_of_wordProductSpan_eq_top
      generators input output full output_nonzero
  have dimension_sum :=
    (InternalSandwich.unobservable
      (matrixEndGenerators generators) input output).finrank_quotient_add_finrank
  rw [unobservable_bot, finrank_bot, add_zero, reachable_top,
    finrank_top, Module.finrank_pi] at dimension_sum
  rw [unobservable_bot, reachable_top]
  exact dimension_sum

/-- Every exact realization of a nonzero sandwich over a full generated matrix algebra has at
least the ambient number of states. -/
theorem card_le_of_wordProductSpan_eq_top_of_represents
    {State : Type*} [AddCommGroup State] [Module K State]
    [FiniteDimensional K State]
    (generators : Glyph → Square ι K) (input : Q →ₗ[K] (ι → K))
    (output : (ι → K) →ₗ[K] Q)
    (full : wordProductSpan generators = ⊤)
    (input_nonzero : input ≠ 0) (output_nonzero : output ≠ 0)
    (realization : Glyph → Module.End K State)
    (realizationInput : Q →ₗ[K] State)
    (realizationOutput : State →ₗ[K] Q)
    (exact : InternalSandwich.RepresentsSandwich
      (matrixEndGenerators generators) input output
      realization realizationInput realizationOutput) :
    Fintype.card ι ≤ Module.finrank K State := by
  rw [← quotient_finrank_eq_card_of_wordProductSpan_eq_top
    generators input output full input_nonzero output_nonzero]
  exact InternalSandwich.quotient_finrank_le_of_represents
    (matrixEndGenerators generators) input output
    realization realizationInput realizationOutput exact

end MatrixMortality
