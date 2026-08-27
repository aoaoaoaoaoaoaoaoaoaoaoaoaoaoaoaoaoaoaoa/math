import MatrixMortality.OverlapLag

/-!
# Exact decision of the zero-framed binary two-Lag kernel

The apparent source kernel has no universal behavior.  Its accepting instances have a direct
syntactic classification, independent of the two promises required by the mortality compiler.
-/

namespace MatrixMortality.OverlapLag

/-- Reachability between two Lag configurations, suppressing the chronological trace word. -/
private def Reaches (append : Bool → Bool → List Bool) (source : Bool) (initial : List Bool)
    (target : Bool) (residual : List Bool) : Prop :=
  ∃ word, Trace append source initial word target residual

private theorem reaches_step {append : Bool → Bool → List Bool}
    {source head target : Bool} {tail residual : List Bool}
    (trace : Reaches append head (tail ++ append source head) target residual) :
    Reaches append source (head :: tail) target residual := by
  obtain ⟨word, trace⟩ := trace
  exact ⟨head :: word, .step trace⟩

/-- Every nontrivial accepting trace has one of the two possible last predecessors. -/
private theorem trace_empty_split {n : Nat} {U V W : List Bool}
    {source target : Bool} {initial word residual : List Bool}
    (trace : Trace (appendant n U V W) source initial word target residual)
    (target_eq : target = false) (residual_eq : residual = []) :
    (source = false ∧ initial = []) ∨
      (U = [] ∧ Reaches (appendant n U V W) source initial true [false]) ∨
      (V = [] ∧ Reaches (appendant n U V W) source initial false [false]) := by
  induction trace with
  | nil phase queue => exact Or.inl ⟨target_eq, residual_eq⟩
  | @step phase target head tail word residual trace induction =>
      specialize induction target_eq residual_eq
      rcases induction with terminal | terminal | terminal
      · obtain ⟨rfl, empty⟩ := terminal
        have split := List.append_eq_nil_iff.mp empty
        have tail_empty : tail = [] := split.1
        have appendant_empty : appendant n U V W phase false = [] := split.2
        subst tail
        cases phase
        · exact Or.inr (Or.inr ⟨by simpa using appendant_empty, ⟨[], .nil false [false]⟩⟩)
        · exact Or.inr (Or.inl ⟨by simpa using appendant_empty, ⟨[], .nil true [false]⟩⟩)
      · exact Or.inr (Or.inl ⟨terminal.1, reaches_step terminal.2⟩)
      · exact Or.inr (Or.inr ⟨terminal.1, reaches_step terminal.2⟩)

/-- The complete backward cone of `10` consists of the words `1ᵏ0`. -/
private theorem trace_ten_shape {n : Nat} {U V W : List Bool} (n_pos : 0 < n)
    {source target : Bool} {initial word residual : List Bool}
    (trace : Trace (appendant n U V W) source initial word target residual)
    (target_eq : target = true) (residual_eq : residual = [false]) :
    source = true ∧
      encode source initial = List.replicate (word.length + 1) true ++ [false] := by
  induction trace with
  | nil phase queue => subst phase; subst queue; simp [encode]
  | @step phase target head tail word residual trace induction =>
      specialize induction target_eq residual_eq
      obtain ⟨rfl, shape⟩ := induction
      have core :
          tail ++ appendant n U V W phase true =
            List.replicate word.length true ++ [false] := by
        simpa [encode, List.replicate_succ] using shape
      cases phase
      · have impossible :
            tail ++ W ++ List.replicate n false = List.replicate word.length true := by
          rw [appendant_false_true] at core
          have framed :
              (tail ++ W ++ List.replicate n false) ++ [false] =
                List.replicate word.length true ++ [false] := by
            simpa [appendant, List.replicate_succ', List.append_assoc] using core
          exact List.append_cancel_right framed
        have false_mem : false ∈ tail ++ W ++ List.replicate n false := by
          simp [n_pos.ne']
        rw [impossible] at false_mem
        simp at false_mem
      · constructor
        · rfl
        · rw [appendant_true_true] at core
          simpa [encode, List.replicate_succ] using
            congrArg (List.cons true) core

/-- A `1` occurring in the rule appendant survives every Lag step. -/
private theorem true_mem_encode_of_trace {n : Nat} {U V W : List Bool}
    {source target : Bool} {initial word residual : List Bool} (true_mem : true ∈ U)
    (trace : Trace (appendant n U V W) source initial word target residual)
    (source_mem : true ∈ encode source initial) :
    true ∈ encode target residual := by
  induction trace with
  | nil phase queue => exact source_mem
  | @step phase target head tail word residual trace induction =>
      apply induction
      cases phase <;> cases head
      · simp [encode, appendant] at source_mem ⊢
        exact Or.inl source_mem
      · simp [encode]
      · simp [encode, appendant]
        exact Or.inr true_mem
      · simp [encode]

private theorem exists_replicate_false_iff {word : List Bool} :
    (∃ m, word = List.replicate m false) ↔ true ∉ word := by
  constructor
  · rintro ⟨m, rfl⟩
    simp
  · intro true_absent
    refine ⟨word.length, ?_⟩
    induction word with
    | nil => rfl
    | cons head tail induction =>
        cases head
        · simp only [List.length_cons, List.replicate_succ, List.cons.injEq, true_and]
          exact induction (by simpa using true_absent)
        · simp at true_absent

private theorem delete_zeroes {n m : Nat} {U W : List Bool} :
    Trace (appendant n U [] W) false (List.replicate m false)
      (List.replicate m false) false [] := by
  induction m with
  | zero => exact .nil false []
  | succ m induction =>
      rw [List.replicate_succ]
      exact .step (by simpa using induction)

/-- Exact, unconditional classification of the zero-framed binary two-Lag kernel. -/
theorem accepts_iff {n : Nat} {U V W : List Bool} (n_pos : 0 < n) :
    Accepts n U V W ↔
      (n = 1 ∧ U = []) ∨
      (V = [] ∧ true ∉ U) := by
  constructor
  · rintro ⟨word, trace⟩
    rcases trace_empty_split trace rfl rfl with terminal | terminal | terminal
    · have initial_nonempty : List.replicate n false ≠ [] := by simp [n_pos.ne']
      exact False.elim (initial_nonempty terminal.2)
    · left
      refine ⟨?_, terminal.1⟩
      obtain ⟨history, history_trace⟩ := terminal.2
      have shape := trace_ten_shape n_pos history_trace rfl rfl
      have true_count := congrArg (List.count true) shape.2
      have total_length := congrArg List.length shape.2
      simp [encode] at true_count total_length
      have false_count : List.count true (List.replicate n false) = 0 := by
        rw [List.count_replicate]
        rfl
      omega
    · right
      refine ⟨terminal.1, ?_⟩
      intro true_mem
      obtain ⟨history, history_trace⟩ := terminal.2
      have survives := true_mem_encode_of_trace true_mem history_trace (by simp [encode])
      simp [encode] at survives
  · rintro (terminal | zeroes)
    · obtain ⟨rfl, rfl⟩ := terminal
      exact ⟨[false], .step (.nil false [])⟩
    · obtain ⟨rfl, zeroes⟩ := zeroes
      obtain ⟨m, rfl⟩ := exists_replicate_false_iff.mpr zeroes
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero n_pos.ne'
      refine ⟨false :: List.replicate (k + m) false, .step ?_⟩
      change Trace (appendant (k + 1) (List.replicate m false) [] W) false
        (List.replicate k false ++ List.replicate m false)
        (List.replicate (k + m) false) false []
      rw [← List.replicate_add]
      exact delete_zeroes

/-- Acceptance is decidable by the classification, without simulating the Lag orbit. -/
def acceptsDecidable {n : Nat} {U V W : List Bool} (n_pos : 0 < n) :
    Decidable (Accepts n U V W) :=
  decidable_of_iff
    ((n = 1 ∧ U = []) ∨ (V = [] ∧ true ∉ U))
    (accepts_iff n_pos).symm

/-- The mortality triple is syntactically classified whenever the compiler promises hold. -/
theorem mortality_iff_syntax {n : Nat} {U V W : List Bool} (n_pos : 0 < n)
    (singleton_isolation : SingletonIsolation n U V W)
    (avoids_long_frame : AvoidsLongFrame n U V W) :
    IsMortal (OverlapQueue.mortalityFamily transition (cancel n U V W)) ↔
      (n = 1 ∧ U = []) ∨
      (V = [] ∧ true ∉ U) := by
  rw [mortality_iff_accepts n U V W n_pos singleton_isolation avoids_long_frame,
    accepts_iff n_pos]

end MatrixMortality.OverlapLag
