import MatrixMortality.ExactBehavior

/-!
# Internal-word sandwich minimization

A physical word whose product factors through a finite interface repairs the reachable and
observable minimization of that interface.  This file constructs the canonical invariant
subquotient and proves mortality equivalence without imposing a language on physical words.
-/

namespace MatrixMortality

namespace InternalSandwich

variable {K V Q Glyph : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup Q] [Module K Q]

/-- Vectors reached from the interface input by arbitrary physical words. -/
def reachable (generators : Glyph → Module.End K V) (input : Q →ₗ[K] V) : Submodule K V :=
  Submodule.span K {x | ∃ word : List Glyph, ∃ q : Q, x = wordProduct generators word (input q)}

theorem input_mem_reachable (generators : Glyph → Module.End K V) (input : Q →ₗ[K] V)
    (q : Q) :
    input q ∈ reachable generators input := by
  apply Submodule.subset_span
  exact ⟨[], q, by simp⟩

theorem reachable_invariant (generators : Glyph → Module.End K V) (input : Q →ₗ[K] V)
    (label : Glyph) :
    Submodule.map (generators label) (reachable generators input) ≤ reachable generators input := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨word, q, rfl⟩
  apply Submodule.subset_span
  exact ⟨label :: word, q, by simp [Module.End.mul_apply]⟩

/-- Restrict one physical generator to the canonical reachable carrier. -/
def reachableGenerator (generators : Glyph → Module.End K V) (input : Q →ₗ[K] V)
    (label : Glyph) : Module.End K (reachable generators input) :=
  (generators label).domRestrict (reachable generators input) |>.codRestrict
    (reachable generators input) fun x =>
      reachable_invariant generators input label (Submodule.mem_map_of_mem x.property)

theorem reachableGenerator_apply (generators : Glyph → Module.End K V) (input : Q →ₗ[K] V)
    (label : Glyph) (x : reachable generators input) :
    (reachableGenerator generators input label x : V) = generators label x := rfl

theorem reachableWord_apply (generators : Glyph → Module.End K V) (input : Q →ₗ[K] V)
    (word : List Glyph) (x : reachable generators input) :
    ((wordProduct (reachableGenerator generators input) word x :
        reachable generators input) : V) =
      wordProduct generators word x := by
  induction word with
  | nil => simp
  | cons label tail induction =>
      simp only [wordProduct_cons, Module.End.mul_apply]
      rw [reachableGenerator_apply, induction]

/-- Reachable vectors invisible to every future interface observation. -/
def unobservable (generators : Glyph → Module.End K V) (input : Q →ₗ[K] V)
    (output : V →ₗ[K] Q) : Submodule K (reachable generators input) :=
  ⨅ word : List Glyph,
    LinearMap.ker ((output.comp (wordProduct generators word)).domRestrict
      (reachable generators input))

theorem unobservable_output_zero (generators : Glyph → Module.End K V)
    (input : Q →ₗ[K] V) (output : V →ₗ[K] Q)
    (x : unobservable generators input output) :
    output (x : reachable generators input) = 0 := by
  have invisible_all :
      ∀ word : List Glyph,
        (x : reachable generators input) ∈
          LinearMap.ker ((output.comp (wordProduct generators word)).domRestrict
            (reachable generators input)) := by
    simpa only [unobservable, Submodule.mem_iInf] using x.property
  have invisible_empty := invisible_all ([] : List Glyph)
  simpa using invisible_empty

theorem unobservable_invariant (generators : Glyph → Module.End K V)
    (input : Q →ₗ[K] V) (output : V →ₗ[K] Q) (label : Glyph) :
    Submodule.map (reachableGenerator generators input label)
        (unobservable generators input output) ≤
      unobservable generators input output := by
  rintro _ ⟨x, hx, rfl⟩
  rw [unobservable, Submodule.mem_iInf]
  intro word
  have invisible_all :
      ∀ future : List Glyph,
        x ∈ LinearMap.ker ((output.comp (wordProduct generators future)).domRestrict
          (reachable generators input)) := by
    intro future
    exact (show unobservable generators input output ≤
        LinearMap.ker ((output.comp (wordProduct generators future)).domRestrict
          (reachable generators input)) by
      rw [unobservable]
      exact iInf_le _ future) hx
  have invisible := invisible_all (word ++ [label])
  simpa [LinearMap.mem_ker, reachableGenerator_apply, wordProduct_append,
    Module.End.mul_apply] using invisible

/-- The generator induced on the reachable-observable quotient. -/
def quotientGenerator (generators : Glyph → Module.End K V) (input : Q →ₗ[K] V)
    (output : V →ₗ[K] Q) (label : Glyph) :
    Module.End K ((reachable generators input) ⧸ unobservable generators input output) :=
  (unobservable generators input output).mapQ
    (unobservable generators input output)
    (reachableGenerator generators input label)
    (Submodule.map_le_iff_le_comap.mp
      (unobservable_invariant generators input output label))

theorem quotientGenerator_mk (generators : Glyph → Module.End K V) (input : Q →ₗ[K] V)
    (output : V →ₗ[K] Q) (label : Glyph) (x : reachable generators input) :
    quotientGenerator generators input output label
        ((unobservable generators input output).mkQ x) =
      (unobservable generators input output).mkQ
        (reachableGenerator generators input label x) :=
  Submodule.mapQ_apply _ _ _ _

theorem quotientWord_mk (generators : Glyph → Module.End K V) (input : Q →ₗ[K] V)
    (output : V →ₗ[K] Q) (word : List Glyph) (x : reachable generators input) :
    wordProduct (quotientGenerator generators input output) word
        ((unobservable generators input output).mkQ x) =
      (unobservable generators input output).mkQ
        (wordProduct (reachableGenerator generators input) word x) := by
  induction word with
  | nil => simp
  | cons label tail induction =>
      simp only [wordProduct_cons, Module.End.mul_apply, induction]
      rw [quotientGenerator_mk]

/-- The interface input with codomain restricted to the reachable carrier. -/
def reachableInput (generators : Glyph → Module.End K V) (input : Q →ₗ[K] V) :
    Q →ₗ[K] reachable generators input :=
  input.codRestrict (reachable generators input) (input_mem_reachable generators input)

theorem quotient_mortal_of_ambient_mortal (generators : Glyph → Module.End K V)
    (input : Q →ₗ[K] V) (output : V →ₗ[K] Q)
    (mortal : IsMortal generators) :
    IsMortal (quotientGenerator generators input output) := by
  obtain ⟨word, word_nonempty, product_zero⟩ := mortal
  refine ⟨word, word_nonempty, ?_⟩
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ :=
    Submodule.mkQ_surjective (unobservable generators input output) q
  rw [quotientWord_mk]
  apply (Submodule.Quotient.mk_eq_zero
    (unobservable generators input output)).mpr
  have : wordProduct (reachableGenerator generators input) word x = 0 := by
    apply Subtype.ext
    simp [reachableWord_apply, product_zero]
  rw [this]
  exact (unobservable generators input output).zero_mem

theorem ambient_mortal_of_quotient_mortal
    (generators : Glyph → Module.End K V) (input : Q →ₗ[K] V) (output : V →ₗ[K] Q)
    (repairWord : List Glyph) (repair_nonempty : repairWord ≠ [])
    (repair :
      wordProduct generators repairWord = input.comp output)
    (mortal : IsMortal (quotientGenerator generators input output)) :
    IsMortal generators := by
  obtain ⟨word, _, quotient_zero⟩ := mortal
  have middle_zero :
      output.comp ((wordProduct generators word).comp input) = 0 := by
    apply LinearMap.ext
    intro q
    let x : reachable generators input := reachableInput generators input q
    have quotient_action :
        (unobservable generators input output).mkQ
            (wordProduct (reachableGenerator generators input) word x) = 0 := by
      rw [← quotientWord_mk]
      simp [quotient_zero]
    have invisible :
        wordProduct (reachableGenerator generators input) word x ∈
          unobservable generators input output :=
      (Submodule.Quotient.mk_eq_zero
        (unobservable generators input output)).mp quotient_action
    have observed_zero :=
      unobservable_output_zero generators input output
        ⟨wordProduct (reachableGenerator generators input) word x, invisible⟩
    simpa [x, LinearMap.comp_apply, reachableWord_apply, reachableInput] using
      observed_zero
  refine ⟨repairWord ++ word ++ repairWord, by simp [repair_nonempty], ?_⟩
  rw [wordProduct_append, wordProduct_append, repair]
  apply LinearMap.ext
  intro x
  have vanished := LinearMap.congr_fun middle_zero (output x)
  simpa [Module.End.mul_apply, LinearMap.comp_apply] using congrArg input vanished

/-- A physical finite-rank word preserves mortality under canonical reachable-observable
minimization of its sandwich series. -/
theorem mortal_quotient_iff (generators : Glyph → Module.End K V)
    (input : Q →ₗ[K] V) (output : V →ₗ[K] Q)
    (repairWord : List Glyph) (repair_nonempty : repairWord ≠ [])
    (repair : wordProduct generators repairWord = input.comp output) :
    IsMortal (quotientGenerator generators input output) ↔ IsMortal generators :=
  ⟨ambient_mortal_of_quotient_mortal generators input output repairWord repair_nonempty repair,
    quotient_mortal_of_ambient_mortal generators input output⟩

/-- If minimization annihilates the entire state space, the physical repair word wrapped around
itself certifies a mortal source family. -/
theorem ambient_mortal_of_quotient_subsingleton
    (generators : Glyph → Module.End K V) (input : Q →ₗ[K] V) (output : V →ₗ[K] Q)
    (repairWord : List Glyph) (repair_nonempty : repairWord ≠ [])
    (repair : wordProduct generators repairWord = input.comp output)
    [Subsingleton
      ((reachable generators input) ⧸ unobservable generators input output)] :
    IsMortal generators := by
  apply ambient_mortal_of_quotient_mortal generators input output
    repairWord repair_nonempty repair
  exact ⟨repairWord, repair_nonempty, Subsingleton.elim _ _⟩

/-! ## Block-Hankel minimality -/

/-- Future interface observations of an ambient state. -/
def behavior (generators : Glyph → Module.End K V) (output : V →ₗ[K] Q) :
    V →ₗ[K] (List Glyph → Q) where
  toFun x word := output (wordProduct generators word x)
  map_add' x y := by
    funext word
    simp
  map_smul' scalar x := by
    funext word
    simp

/-- Future observations restricted to the reachable carrier. -/
def reachableBehavior (generators : Glyph → Module.End K V) (input : Q →ₗ[K] V)
    (output : V →ₗ[K] Q) :
    reachable generators input →ₗ[K] (List Glyph → Q) :=
  (behavior generators output).domRestrict (reachable generators input)

theorem ker_reachableBehavior (generators : Glyph → Module.End K V)
    (input : Q →ₗ[K] V) (output : V →ₗ[K] Q) :
    LinearMap.ker (reachableBehavior generators input output) =
      unobservable generators input output := by
  ext x
  constructor
  · intro annihilated
    rw [unobservable, Submodule.mem_iInf]
    intro word
    rw [LinearMap.mem_ker]
    have pointwise := congrFun (LinearMap.mem_ker.mp annihilated) word
    simpa [reachableBehavior, behavior] using pointwise
  · intro invisible
    rw [LinearMap.mem_ker]
    apply funext
    intro word
    have invisible_all :
        ∀ future : List Glyph,
          x ∈ LinearMap.ker ((output.comp (wordProduct generators future)).domRestrict
            (reachable generators input)) := by
      apply (Submodule.mem_iInf (fun future : List Glyph =>
        LinearMap.ker ((output.comp (wordProduct generators future)).domRestrict
          (reachable generators input)))).mp
      simpa only [unobservable] using invisible
    simpa [reachableBehavior, behavior, LinearMap.mem_ker] using invisible_all word

/-- One flattened block-Hankel column: the interface response after a past word and input
vector, indexed by every future word. -/
def blockHankelColumn (generators : Glyph → Module.End K V) (input : Q →ₗ[K] V)
    (output : V →ₗ[K] Q) (past : List Glyph) (q : Q) : List Glyph → Q :=
  behaviorColumn (linearBehavior generators input output) past q

theorem behavior_word (generators : Glyph → Module.End K V)
    (input : Q →ₗ[K] V) (output : V →ₗ[K] Q) (past : List Glyph) (q : Q) :
    behavior generators output (wordProduct generators past (input q)) =
      blockHankelColumn generators input output past q := by
  funext future
  simp [behavior, blockHankelColumn, behaviorColumn, linearBehavior,
    wordProduct_append, Module.End.mul_apply]

theorem reachableBehavior_word (generators : Glyph → Module.End K V)
    (input : Q →ₗ[K] V) (output : V →ₗ[K] Q) (past : List Glyph) (q : Q) :
    reachableBehavior generators input output
        ⟨wordProduct generators past (input q),
          Submodule.subset_span ⟨past, q, rfl⟩⟩ =
      blockHankelColumn generators input output past q := by
  exact behavior_word generators input output past q

/-- The range of the canonical behavior map is exactly the span of the flattened
block-Hankel columns. -/
theorem range_reachableBehavior_eq_span (generators : Glyph → Module.End K V)
    (input : Q →ₗ[K] V) (output : V →ₗ[K] Q) :
    LinearMap.range (reachableBehavior generators input output) =
      Submodule.span K {column | ∃ past : List Glyph, ∃ q : Q,
        column = blockHankelColumn generators input output past q} := by
  apply le_antisymm
  · rintro column ⟨x, rfl⟩
    change behavior generators output (x : V) ∈
      Submodule.span K {column | ∃ past : List Glyph, ∃ q : Q,
        column = blockHankelColumn generators input output past q}
    refine Submodule.span_induction
      (p := fun vector : V => fun _ ↦
        behavior generators output vector ∈
          Submodule.span K {column | ∃ past : List Glyph, ∃ q : Q,
            column = blockHankelColumn generators input output past q})
      (s := {vector | ∃ past : List Glyph, ∃ q : Q,
        vector = wordProduct generators past (input q)})
      ?_ ?_ ?_ ?_ (by simpa only [reachable] using x.property)
    · rintro vector ⟨past, q, rfl⟩
      rw [behavior_word]
      exact Submodule.subset_span ⟨past, q, rfl⟩
    · simp
    · intro x y _ _ hx hy
      simpa using Submodule.add_mem _ hx hy
    · intro scalar x _ hx
      simpa using Submodule.smul_mem _ scalar hx
  · rw [Submodule.span_le]
    rintro column ⟨past, q, rfl⟩
    refine ⟨⟨wordProduct generators past (input q),
      Submodule.subset_span ⟨past, q, rfl⟩⟩, ?_⟩
    exact reachableBehavior_word generators input output past q

/-- The canonical quotient is linearly equivalent to the column space of the flattened
matrix-valued block Hankel array. -/
noncomputable def quotientEquivHankelRange
    (generators : Glyph → Module.End K V) (input : Q →ₗ[K] V) (output : V →ₗ[K] Q) :
    ((reachable generators input) ⧸ unobservable generators input output) ≃ₗ[K]
      LinearMap.range (reachableBehavior generators input output) :=
  (Submodule.quotEquivOfEq
      (unobservable generators input output)
      (LinearMap.ker (reachableBehavior generators input output))
      (ker_reachableBehavior generators input output).symm).trans
    (reachableBehavior generators input output).quotKerEquivRange

/-- Finite-dimensional state count equals flattened block-Hankel column rank. -/
theorem quotient_finrank_eq_blockHankel
    (generators : Glyph → Module.End K V) (input : Q →ₗ[K] V) (output : V →ₗ[K] Q) :
    Module.finrank K
        ((reachable generators input) ⧸ unobservable generators input output) =
      Module.finrank K
        (LinearMap.range (reachableBehavior generators input output)) :=
  (quotientEquivHankelRange generators input output).finrank_eq

/-- An exact realization of the same matrix-valued sandwich series on another carrier. -/
def RepresentsSandwich {State : Type*} [AddCommGroup State] [Module K State]
    (generators : Glyph → Module.End K V) (input : Q →ₗ[K] V) (output : V →ₗ[K] Q)
    (realization : Glyph → Module.End K State) (realizationInput : Q →ₗ[K] State)
    (realizationOutput : State →ₗ[K] Q) : Prop :=
  RepresentsBehavior (linearBehavior generators input output)
    realization realizationInput realizationOutput

theorem blockHankelColumn_mem_realizationBehavior
    {State : Type*} [AddCommGroup State] [Module K State]
    (generators : Glyph → Module.End K V) (input : Q →ₗ[K] V) (output : V →ₗ[K] Q)
    (realization : Glyph → Module.End K State) (realizationInput : Q →ₗ[K] State)
    (realizationOutput : State →ₗ[K] Q)
    (exact :
      RepresentsSandwich generators input output realization realizationInput realizationOutput)
    (past : List Glyph) (q : Q) :
    blockHankelColumn generators input output past q ∈
      LinearMap.range (behavior realization realizationOutput) := by
  refine ⟨wordProduct realization past (realizationInput q), ?_⟩
  funext future
  have coefficient := LinearMap.congr_fun (exact (future ++ past)) q
  simpa [behavior, blockHankelColumn, behaviorColumn, linearBehavior,
    RepresentsSandwich, RepresentsBehavior, wordProduct_append,
    Module.End.mul_apply, LinearMap.comp_apply] using coefficient

/-- Every exact realization has at least the canonical quotient's state dimension. -/
theorem quotient_finrank_le_of_represents
    {State : Type*} [AddCommGroup State] [Module K State]
    [FiniteDimensional K State]
    (generators : Glyph → Module.End K V) (input : Q →ₗ[K] V) (output : V →ₗ[K] Q)
    (realization : Glyph → Module.End K State) (realizationInput : Q →ₗ[K] State)
    (realizationOutput : State →ₗ[K] Q)
    (exact :
      RepresentsSandwich generators input output realization realizationInput realizationOutput) :
    Module.finrank K
        ((reachable generators input) ⧸ unobservable generators input output) ≤
      Module.finrank K State := by
  rw [quotient_finrank_eq_blockHankel]
  have range_le :
      LinearMap.range (reachableBehavior generators input output) ≤
        LinearMap.range (behavior realization realizationOutput) := by
    rw [range_reachableBehavior_eq_span, Submodule.span_le]
    rintro column ⟨past, q, rfl⟩
    exact blockHankelColumn_mem_realizationBehavior generators input output
      realization realizationInput realizationOutput exact past q
  exact (LinearMap.finrank_le_finrank_of_injective
      (Submodule.inclusion_injective range_le)).trans
    (LinearMap.finrank_range_le (behavior realization realizationOutput))

end InternalSandwich

end MatrixMortality
