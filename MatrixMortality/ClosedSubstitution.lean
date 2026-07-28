import Mathlib.Data.Fintype.Card

/-!
# Closed-token substitution

A queue of complete semantic tokens whose processed head emits only complete tokens is a
deletion-one substitution system. This file proves its exact finite dependency-graph
criterion: one initial queue halts precisely when none of its reachable tokens lies on a
directed cycle. The terminating direction assigns every token the size of its finite
substitution tree; the converse follows a cycle lineage through every queue step.
-/

namespace MatrixMortality

/-- The child-to-parent relation of the substitution forest. -/
def SubstitutionChild {Γ : Type*} (τ : Γ → List Γ) (child parent : Γ) : Prop :=
  child ∈ τ parent

/-- Consume the queue head and append its complete-token emission. -/
def closedSubstitutionStep {Γ : Type*} (τ : Γ → List Γ) : List Γ → List Γ
  | [] => []
  | head :: tail => tail ++ τ head

/-- A closed-token queue reaches the empty queue after finitely many substitutions. -/
def ClosedSubstitutionHalts {Γ : Type*} (τ : Γ → List Γ) (word : List Γ) : Prop :=
  ∃ steps : Nat, (closedSubstitutionStep τ)^[steps] word = []

/-- Size of the finite substitution tree rooted at one token. -/
noncomputable def substitutionTreeSize {Γ : Type*} (τ : Γ → List Γ)
    (wf : WellFounded (SubstitutionChild τ)) (token : Γ) : Nat :=
  wf.fix (fun parent descendants =>
    1 + ((τ parent).attach.map fun child => descendants child.1 child.2).sum) token

theorem substitutionTreeSize_eq {Γ : Type*} (τ : Γ → List Γ)
    (wf : WellFounded (SubstitutionChild τ)) (token : Γ) :
    substitutionTreeSize τ wf token =
      1 + ((τ token).map (substitutionTreeSize τ wf)).sum := by
  rw [substitutionTreeSize, WellFounded.fix_eq]
  exact congrArg (fun size : Nat => 1 + size) (congrArg List.sum (by
    simpa only [substitutionTreeSize] using
      List.attach_map_val (τ token) (substitutionTreeSize τ wf)))

/-- Total number of nodes in the substitution forest represented by a queue. -/
noncomputable def substitutionForestSize {Γ : Type*} (τ : Γ → List Γ)
    (wf : WellFounded (SubstitutionChild τ)) (word : List Γ) : Nat :=
  (word.map (substitutionTreeSize τ wf)).sum

theorem substitutionForestSize_cons {Γ : Type*} (τ : Γ → List Γ)
    (wf : WellFounded (SubstitutionChild τ)) (head : Γ) (tail : List Γ) :
    substitutionForestSize τ wf (head :: tail) =
      substitutionForestSize τ wf (closedSubstitutionStep τ (head :: tail)) + 1 := by
  simp [substitutionForestSize, substitutionTreeSize_eq, closedSubstitutionStep,
    List.sum_append]
  omega

/-- A well-founded token dependency relation makes every closed-token queue halt. -/
theorem closedSubstitutionHalts_of_wellFounded {Γ : Type*} (τ : Γ → List Γ)
    (wf : WellFounded (SubstitutionChild τ)) (word : List Γ) :
    ClosedSubstitutionHalts τ word := by
  induction word using (measure (substitutionForestSize τ wf)).wf.induction with
  | h word induction =>
      cases word with
      | nil => exact ⟨0, rfl⟩
      | cons head tail =>
          have size_lt :
              substitutionForestSize τ wf (closedSubstitutionStep τ (head :: tail)) <
                substitutionForestSize τ wf (head :: tail) := by
            rw [substitutionForestSize_cons]
            omega
          obtain ⟨steps, empty⟩ :=
            induction (closedSubstitutionStep τ (head :: tail)) size_lt
          refine ⟨steps + 1, ?_⟩
          rw [Function.iterate_add_apply]
          simpa using empty

/-- The finite dependency graph contains no directed cycle. -/
def NoSubstitutionCycle {Γ : Type*} (τ : Γ → List Γ) : Prop :=
  ∀ token, ¬Relation.TransGen (SubstitutionChild τ) token token

theorem substitutionChild_wellFounded_of_noCycle {Γ : Type*} [Finite Γ]
    (τ : Γ → List Γ) (no_cycle : NoSubstitutionCycle τ) :
    WellFounded (SubstitutionChild τ) := by
  let closure := Relation.TransGen (SubstitutionChild τ)
  letI : IsIrrefl Γ closure := ⟨no_cycle⟩
  have closure_wf : WellFounded closure :=
    Finite.wellFounded_of_trans_of_irrefl closure
  exact Subrelation.wf (fun edge => Relation.TransGen.single edge) closure_wf

/-- A queue still carries a descendant path from the distinguished cycle token. -/
def QueueCarries {Γ : Type*} (τ : Γ → List Γ) (token : Γ)
    (word : List Γ) : Prop :=
  ∃ current ∈ word,
    Relation.ReflTransGen (SubstitutionChild τ) token current

theorem queueCarries_step_of_cycle {Γ : Type*} (τ : Γ → List Γ) (token : Γ)
    (cycle : Relation.TransGen (SubstitutionChild τ) token token)
    {word : List Γ} (carries : QueueCarries τ token word) :
    QueueCarries τ token (closedSubstitutionStep τ word) := by
  obtain ⟨current, current_mem, path⟩ := carries
  cases word with
  | nil => simp at current_mem
  | cons head tail =>
      simp only [closedSubstitutionStep, QueueCarries]
      rw [List.mem_cons] at current_mem
      rcases current_mem with current_is_head | current_tail
      · subst current
        have nonempty_path :
            Relation.TransGen (SubstitutionChild τ) token head := by
          by_cases head_is_token : head = token
          · simpa [head_is_token] using cycle
          · obtain ⟨before, before_path, edge⟩ :=
              path.cases_tail.resolve_left head_is_token
            exact Relation.TransGen.tail' before_path edge
        obtain ⟨before, before_path, edge⟩ :=
          Relation.TransGen.tail'_iff.mp nonempty_path
        exact ⟨before, List.mem_append_right tail edge, before_path⟩
      · exact ⟨current, List.mem_append_left _ current_tail, path⟩

theorem queueCarries_iterate_of_cycle {Γ : Type*} (τ : Γ → List Γ) (token : Γ)
    (cycle : Relation.TransGen (SubstitutionChild τ) token token)
    (steps : Nat) :
    QueueCarries τ token ((closedSubstitutionStep τ)^[steps] [token]) := by
  induction steps with
  | zero =>
      exact ⟨token, by simp, Relation.ReflTransGen.refl⟩
  | succ steps induction =>
      rw [Function.iterate_succ_apply']
      exact queueCarries_step_of_cycle τ token cycle induction

/-- Carrying a path to a cycle persists from any initial queue. -/
theorem queueCarries_iterate_of_cycle_from {Γ : Type*} (τ : Γ → List Γ)
    (token : Γ)
    (cycle : Relation.TransGen (SubstitutionChild τ) token token)
    {word : List Γ} (carries : QueueCarries τ token word) (steps : Nat) :
    QueueCarries τ token ((closedSubstitutionStep τ)^[steps] word) := by
  induction steps with
  | zero => exact carries
  | succ steps induction =>
      rw [Function.iterate_succ_apply']
      exact queueCarries_step_of_cycle τ token cycle induction

/-- A token on a dependency cycle yields a nonhalting singleton queue. -/
theorem singleton_not_closedSubstitutionHalts_of_cycle {Γ : Type*}
    (τ : Γ → List Γ) (token : Γ)
    (cycle : Relation.TransGen (SubstitutionChild τ) token token) :
    ¬ClosedSubstitutionHalts τ [token] := by
  rintro ⟨steps, empty⟩
  have carries := queueCarries_iterate_of_cycle τ token cycle steps
  rw [empty] at carries
  simp [QueueCarries] at carries

/-- On a finite token alphabet, every queue halts exactly when the dependency graph is
acyclic. -/
theorem all_closedSubstitutionHalts_iff_noCycle {Γ : Type*} [Finite Γ]
    (τ : Γ → List Γ) :
    (∀ word, ClosedSubstitutionHalts τ word) ↔ NoSubstitutionCycle τ := by
  constructor
  · intro all_halt token cycle
    exact singleton_not_closedSubstitutionHalts_of_cycle τ token cycle (all_halt [token])
  · intro no_cycle
    exact closedSubstitutionHalts_of_wellFounded τ
      (substitutionChild_wellFounded_of_noCycle τ no_cycle)

/-- Descendant reachability from at least one token in the supplied initial queue. -/
def TokenDescendsFromWord {Γ : Type*} (τ : Γ → List Γ)
    (word : List Γ) (token : Γ) : Prop :=
  ∃ root ∈ word,
    Relation.ReflTransGen (SubstitutionChild τ) token root

/-- The finite alphabet restricted to descendants of an initial queue. -/
abbrev DescendantToken {Γ : Type*} (τ : Γ → List Γ) (word : List Γ) :=
  { token // TokenDescendsFromWord τ word token }

/-- Regard every initial token as its own reflexive descendant. -/
def liftDescendantWord {Γ : Type*} (τ : Γ → List Γ)
    (word : List Γ) : List (DescendantToken τ word) :=
  word.attach.map fun root =>
    ⟨root.1, root.1, root.2, Relation.ReflTransGen.refl⟩

/-- Restrict a substitution to descendants of one initial queue. -/
def descendantSubstitution {Γ : Type*} (τ : Γ → List Γ) (word : List Γ)
    (parent : DescendantToken τ word) : List (DescendantToken τ word) :=
  (τ parent.1).attach.map fun child =>
    ⟨child.1, by
      obtain ⟨root, root_mem, path⟩ := parent.2
      exact ⟨root, root_mem, Relation.ReflTransGen.head child.2 path⟩⟩

theorem liftDescendantWord_map_val {Γ : Type*} (τ : Γ → List Γ)
    (word : List Γ) :
    (liftDescendantWord τ word).map Subtype.val = word := by
  unfold liftDescendantWord
  rw [List.map_map]
  simpa only [Function.comp_apply, id_eq, List.map_id] using
    List.attach_map_val word id

theorem descendantSubstitution_map_val {Γ : Type*} (τ : Γ → List Γ)
    (word : List Γ) (parent : DescendantToken τ word) :
    (descendantSubstitution τ word parent).map Subtype.val = τ parent.1 := by
  unfold descendantSubstitution
  rw [List.map_map]
  simpa only [Function.comp_apply, id_eq, List.map_id] using
    List.attach_map_val (τ parent.1) id

theorem closedSubstitutionStep_descendant_map_val {Γ : Type*}
    (τ : Γ → List Γ) (initial : List Γ)
    (word : List (DescendantToken τ initial)) :
    (closedSubstitutionStep (descendantSubstitution τ initial) word).map Subtype.val =
      closedSubstitutionStep τ (word.map Subtype.val) := by
  cases word with
  | nil => rfl
  | cons head tail =>
      simp [closedSubstitutionStep, List.map_append, descendantSubstitution_map_val]

theorem iterate_closedSubstitutionStep_descendant_map_val {Γ : Type*}
    (τ : Γ → List Γ) (initial : List Γ) (steps : Nat)
    (word : List (DescendantToken τ initial)) :
    (((closedSubstitutionStep (descendantSubstitution τ initial))^[steps] word).map
        Subtype.val) =
      (closedSubstitutionStep τ)^[steps] (word.map Subtype.val) := by
  induction steps with
  | zero => rfl
  | succ steps induction =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        closedSubstitutionStep_descendant_map_val, induction]

theorem closedSubstitutionHalts_descendant_iff {Γ : Type*}
    (τ : Γ → List Γ) (initial : List Γ) :
    ClosedSubstitutionHalts (descendantSubstitution τ initial)
        (liftDescendantWord τ initial) ↔
      ClosedSubstitutionHalts τ initial := by
  constructor
  · rintro ⟨steps, empty⟩
    refine ⟨steps, ?_⟩
    have mapped := congrArg (List.map Subtype.val) empty
    simpa [iterate_closedSubstitutionStep_descendant_map_val,
      liftDescendantWord_map_val] using mapped
  · rintro ⟨steps, empty⟩
    refine ⟨steps, ?_⟩
    apply List.map_eq_nil.mp
    rw [iterate_closedSubstitutionStep_descendant_map_val,
      liftDescendantWord_map_val, empty]

/-- No descendant of the initial queue lies on a dependency cycle. -/
def NoDescendantSubstitutionCycle {Γ : Type*} (τ : Γ → List Γ)
    (word : List Γ) : Prop :=
  ∀ token, TokenDescendsFromWord τ word token →
    ¬Relation.TransGen (SubstitutionChild τ) token token

theorem descendant_cycle_projects {Γ : Type*} (τ : Γ → List Γ)
    (initial : List Γ) (token : DescendantToken τ initial)
    (cycle :
      Relation.TransGen (SubstitutionChild (descendantSubstitution τ initial))
        token token) :
    Relation.TransGen (SubstitutionChild τ) token.1 token.1 := by
  refine cycle.lift Subtype.val ?_
  intro child parent edge
  have mapped :
      child.1 ∈ (descendantSubstitution τ initial parent).map Subtype.val :=
    List.mem_map_of_mem Subtype.val edge
  simpa [descendantSubstitution_map_val] using mapped

theorem descendantSubstitution_noCycle {Γ : Type*} (τ : Γ → List Γ)
    (initial : List Γ) (no_cycle : NoDescendantSubstitutionCycle τ initial) :
    NoSubstitutionCycle (descendantSubstitution τ initial) := by
  intro token cycle
  exact no_cycle token.1 token.2 (descendant_cycle_projects τ initial token cycle)

/-- Exact finite-graph criterion for one initial closed-token queue. -/
theorem closedSubstitutionHalts_iff_noReachableCycle {Γ : Type*} [Finite Γ]
    (τ : Γ → List Γ) (initial : List Γ) :
    ClosedSubstitutionHalts τ initial ↔
      NoDescendantSubstitutionCycle τ initial := by
  constructor
  · intro halts token reachable cycle
    obtain ⟨steps, empty⟩ := halts
    have carries : QueueCarries τ token initial := reachable
    have survives := queueCarries_iterate_of_cycle_from τ token cycle carries steps
    rw [empty] at survives
    simp [QueueCarries] at survives
  · intro no_cycle
    rw [← closedSubstitutionHalts_descendant_iff]
    exact (all_closedSubstitutionHalts_iff_noCycle
      (descendantSubstitution τ initial)).mpr
        (descendantSubstitution_noCycle τ initial no_cycle) (liftDescendantWord τ initial)

end MatrixMortality
