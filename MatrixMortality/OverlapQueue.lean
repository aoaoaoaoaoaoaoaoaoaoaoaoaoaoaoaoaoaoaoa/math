import MatrixMortality.TwoStatePushout

/-!
# Positive overlap queues

A two-frame queue cocycle turns head consumption into positive word cancellation.  Reversal
then feeds the resulting equality directly to the two-state four-dimensional compiler.  The
same frame law exposes the necessary source mechanism: any accepted input longer than one
forces a state-preserving role to delete on both correspondence sides.
-/

namespace MatrixMortality.OverlapQueue

/-- The framed state carries one marker followed by the initial queue. -/
def frame (initial : List Bool) : PairPhase → List Bool
  | .rule => false :: initial
  | .erase => []

/-- Output accumulated while a word drives the controller from the left. -/
def emitted (δ : ControllerTransition PairPhase Bool)
    (output : PairPhase → Bool → List Bool) (phase : PairPhase)
    (word : List Bool) : List Bool :=
  spell (fun role => output role.1 role.2) (controllerRolesFrom δ phase word)

@[simp] theorem emitted_nil (δ : ControllerTransition PairPhase Bool)
    (output : PairPhase → Bool → List Bool) (phase : PairPhase) :
    emitted δ output phase [] = [] := by
  rfl

@[simp] theorem emitted_cons (δ : ControllerTransition PairPhase Bool)
    (output : PairPhase → Bool → List Bool) (phase : PairPhase)
    (head : Bool) (word : List Bool) :
    emitted δ output phase (head :: word) =
      output phase head ++ emitted δ output (δ phase head) word := by
  rfl

/-- A queue trace indexed by its exact chronological head word. -/
inductive Trace (δ : ControllerTransition PairPhase Bool)
    (produce : PairPhase → Bool → List Bool) :
    PairPhase → List Bool → List Bool → PairPhase → List Bool → Prop
  | nil (phase : PairPhase) (queue : List Bool) :
      Trace δ produce phase queue [] phase queue
  | step {phase target : PairPhase} {head : Bool} {tail word residual : List Bool} :
      Trace δ produce (δ phase head) (tail ++ produce phase head) word target residual →
      Trace δ produce phase (head :: tail) (head :: word) target residual

/-- The queue accepts by exhausting its word in the unframed state. -/
def Accepts (δ : ControllerTransition PairPhase Bool)
    (produce : PairPhase → Bool → List Bool) (initial : List Bool) : Prop :=
  ∃ word, Trace δ produce .rule initial word .erase []

/-- Local positive-word coboundary relating queue production to cancellation output. -/
def Cocycle (initial : List Bool) (δ : ControllerTransition PairPhase Bool)
    (produce cancel : PairPhase → Bool → List Bool) : Prop :=
  ∀ phase head,
    frame initial phase ++ produce phase head =
      cancel phase head ++ frame initial (δ phase head)

/-- Every empty queue reachable from the instance is accepting. -/
def EmptyIsAccepting (δ : ControllerTransition PairPhase Bool)
    (produce : PairPhase → Bool → List Bool) (initial : List Bool) : Prop :=
  ∀ word phase, Trace δ produce .rule initial word phase [] → phase = .erase

/-- The initial configuration cannot return to its strictly longer framed queue. -/
def AvoidsFramedReturn (δ : ControllerTransition PairPhase Bool)
    (produce : PairPhase → Bool → List Bool) (initial : List Bool) : Prop :=
  ∀ word, ¬Trace δ produce .rule initial word .rule (frame initial .rule)

theorem Trace.final_phase {δ : ControllerTransition PairPhase Bool}
    {produce : PairPhase → Bool → List Bool}
    {source target : PairPhase} {initial word residual : List Bool}
    (trace : Trace δ produce source initial word target residual) :
    controllerResidualFrom δ source word = target := by
  induction trace with
  | nil => rfl
  | step _ induction => exact induction

/-- A genuine trace satisfies the exact queue-history identity. -/
theorem Trace.history {δ : ControllerTransition PairPhase Bool}
    {produce : PairPhase → Bool → List Bool}
    {source target : PairPhase} {initial word residual : List Bool}
    (trace : Trace δ produce source initial word target residual) :
    initial ++ emitted δ produce source word = word ++ residual := by
  induction trace with
  | nil => simp
  | @step phase target head tail word residual trace induction =>
      simpa only [emitted_cons, List.cons_append, List.append_assoc] using
        congrArg (head :: ·) induction

/-- The local frame law telescopes along every controller word. -/
theorem Cocycle.telescope {initial : List Bool}
    {δ : ControllerTransition PairPhase Bool}
    {produce cancel : PairPhase → Bool → List Bool}
    (cocycle : Cocycle initial δ produce cancel) (phase : PairPhase)
    (word : List Bool) :
    frame initial phase ++ emitted δ produce phase word =
      emitted δ cancel phase word ++
        frame initial (controllerResidualFrom δ phase word) := by
  induction word generalizing phase with
  | nil => simp [controllerResidualFrom]
  | cons head word induction =>
      rw [emitted_cons, emitted_cons, ← List.append_assoc, cocycle phase head,
        List.append_assoc, induction]
      simp [controllerResidualFrom, List.append_assoc]

/-- Positive equality either exposes an earlier empty queue or certifies the entire head word. -/
theorem causality (δ : ControllerTransition PairPhase Bool)
    (produce : PairPhase → Bool → List Bool)
    (source : PairPhase) (initial word residual : List Bool)
    (equality : initial ++ emitted δ produce source word = word ++ residual) :
    (∃ consumed target, Trace δ produce source initial consumed target []) ∨
      Trace δ produce source initial word
        (controllerResidualFrom δ source word) residual := by
  induction word generalizing source initial residual with
  | nil =>
      right
      have initial_eq : initial = residual := by simpa using equality
      subst residual
      exact .nil source initial
  | cons head word induction =>
      cases initial with
      | nil =>
          left
          exact ⟨[], source, .nil source []⟩
      | cons actual tail =>
          have equality' :
              actual :: ((tail ++ produce source head) ++
                emitted δ produce (δ source head) word) =
                head :: (word ++ residual) := by
            simpa only [emitted_cons, List.cons_append, List.append_assoc] using equality
          have head_eq : actual = head := (List.cons.inj equality').1
          subst actual
          have tail_eq :
              (tail ++ produce source head) ++
                  emitted δ produce (δ source head) word =
                word ++ residual :=
            (List.cons.inj equality').2
          rcases induction (δ source head) (tail ++ produce source head) residual tail_eq with
            early | complete
          · left
            obtain ⟨consumed, target, trace⟩ := early
            exact ⟨head :: consumed, target, .step trace⟩
          · right
            exact .step complete

private theorem spell_singletons (roles : List (PairPhase × Bool)) :
    spell (fun role : PairPhase × Bool => [role.2]) roles = roles.map Prod.snd := by
  induction roles with
  | nil => rfl
  | cons role roles induction =>
      simp only [spell, List.map_cons]
      exact congrArg (role.2 :: ·) induction

private theorem roles_symbols (δ : ControllerTransition PairPhase Bool)
    (phase : PairPhase) (word : List Bool) :
    (controllerRolesFrom δ phase word).map Prod.snd = word := by
  induction word generalizing phase with
  | nil => rfl
  | cons head word induction => simp [controllerRolesFrom, induction]

private theorem spell_reverse {Role : Type*} (output : Role → List Bool)
    (roles : List Role) :
    spell (fun role => (output role).reverse) roles.reverse =
      (spell output roles).reverse := by
  induction roles with
  | nil => rfl
  | cons role roles induction =>
      rw [List.reverse_cons, spell_append, induction]
      simp [spell, List.reverse_append]

/-- Reversal converts the suffix-controlled terminal match into the forward cancellation law. -/
theorem coefficient_zero_iff (δ : ControllerTransition PairPhase Bool)
    (cancel : PairPhase → Bool → List Bool) (word : List Bool) :
    twoStateCoefficient ℚ (fun bit : Bool => [bit])
        (fun phase bit => (cancel phase bit).reverse) δ .rule
        (sideTerminalColumn ℚ [false]) word.reverse = 0 ↔
      false :: word = emitted δ cancel .rule word := by
  rw [twoStateCoefficient_eq_zero_iff_terminal_match]
  rw [controllerSuffixRoles, controllerSuffixDecode_reverse]
  simp only [spell_singletons, List.map_reverse, roles_symbols, spell_reverse]
  constructor <;> intro equality
  · change false :: word =
      spell (fun role => cancel role.1 role.2) (controllerRolesFrom δ .rule word)
    simpa [List.reverse_append] using congrArg List.reverse equality
  · simpa [emitted, List.reverse_append] using congrArg List.reverse equality

/-- The fixed three-matrix family emitted by a positive overlap-queue source. -/
def mortalityFamily (δ : ControllerTransition PairPhase Bool)
    (cancel : PairPhase → Bool → List Bool) :
    Option Bool → Matrix (Fin 4) (Fin 4) ℤ :=
  twoStateMortalityFamily ℤ (fun bit : Bool => [bit])
    (fun phase bit => (cancel phase bit).reverse) δ .rule
    (sideTerminalColumn ℤ [false])

/-- Positive two-frame queue acceptance is exactly mortality of three integer `4 × 4` matrices. -/
theorem mortality_iff_accepts (initial : List Bool)
    (δ : ControllerTransition PairPhase Bool)
    (produce cancel : PairPhase → Bool → List Bool)
    (initial_nonempty : initial ≠ []) (cocycle : Cocycle initial δ produce cancel)
    (empty_accepts : EmptyIsAccepting δ produce initial)
    (avoids_return : AvoidsFramedReturn δ produce initial) :
    IsMortal (mortalityFamily δ cancel) ↔ Accepts δ produce initial := by
  have cast_column :
      castVector (sideTerminalColumn ℤ [false]) = sideTerminalColumn ℚ [false] := by
    funext index
    simpa [castVector] using
      congrFun (sideTerminalColumn_map (Int.castRingHom ℚ) [false]) index
  rw [mortalityFamily,
    twoStateMortalityFamily_int_mortal_iff_nonempty_zero
      (fun bit : Bool => [bit]) (fun phase bit => (cancel phase bit).reverse) δ .rule
      (sideTerminalColumn ℤ [false]) (by simp)]
  constructor
  · rintro ⟨physical, _, coefficient_zero⟩
    let word := physical.reverse
    have physical_eq : physical = word.reverse := by simp [word]
    rw [cast_column, physical_eq, coefficient_zero_iff] at coefficient_zero
    have telescope := cocycle.telescope .rule word
    cases destination : controllerResidualFrom δ .rule word with
    | rule =>
        have history :
            initial ++ emitted δ produce .rule word =
              word ++ frame initial .rule := by
          rw [coefficient_zero.symm, destination] at telescope
          simpa [frame, List.append_assoc] using telescope
        rcases causality δ produce .rule initial word (frame initial .rule) history with
          early | complete
        · obtain ⟨consumed, target, trace⟩ := early
          have target_eq := empty_accepts consumed target trace
          subst target
          exact ⟨consumed, trace⟩
        · exact False.elim (avoids_return word (by simpa [destination] using complete))
    | erase =>
        have history :
            initial ++ emitted δ produce .rule word = word := by
          rw [coefficient_zero.symm, destination] at telescope
          simpa [frame] using telescope
        rcases causality δ produce .rule initial word [] (by simpa using history) with
          early | complete
        · obtain ⟨consumed, target, trace⟩ := early
          have target_eq := empty_accepts consumed target trace
          subst target
          exact ⟨consumed, trace⟩
        · exact ⟨word, by simpa [destination] using complete⟩
  · rintro ⟨word, trace⟩
    have word_nonempty : word ≠ [] := by
      intro word_empty
      subst word
      have := trace.history
      simp at this
      exact initial_nonempty this
    have state := trace.final_phase
    have history := trace.history
    have telescope := cocycle.telescope .rule word
    have history' : initial ++ emitted δ produce .rule word = word := by
      simpa using history
    have cancellation : false :: word = emitted δ cancel .rule word := by
      calc
        false :: word = frame initial .rule ++ emitted δ produce .rule word := by
          simp [frame, history']
        _ = emitted δ cancel .rule word ++
            frame initial (controllerResidualFrom δ .rule word) := telescope
        _ = emitted δ cancel .rule word := by simp [state, frame]
    refine ⟨word.reverse, by simpa using word_nonempty, ?_⟩
    rw [cast_column, coefficient_zero_iff]
    exact cancellation

/-- Queue length, with one unit charged to the unframed state. -/
def potential : PairPhase → List Bool → Nat
  | .rule, queue => queue.length
  | .erase, queue => queue.length + 1

private theorem potential_step_le (initial : List Bool)
    (δ : ControllerTransition PairPhase Bool)
    (produce cancel : PairPhase → Bool → List Bool)
    (initial_nonempty : initial ≠ []) (cocycle : Cocycle initial δ produce cancel)
    (no_pure_delete :
      ∀ phase head, δ phase head = phase → produce phase head ≠ [])
    (phase : PairPhase) (head : Bool) (tail : List Bool) :
    potential phase (head :: tail) ≤
      potential (δ phase head) (tail ++ produce phase head) := by
  cases phase with
  | rule =>
      cases destination : δ .rule head with
      | rule =>
          have production_positive : 0 < (produce .rule head).length :=
            List.length_pos_of_ne_nil (no_pure_delete .rule head destination)
          simp [potential, List.length_append]
          omega
      | erase =>
          simp [potential, List.length_append]
  | erase =>
      cases destination : δ .erase head with
      | erase =>
          have production_positive : 0 < (produce .erase head).length :=
            List.length_pos_of_ne_nil (no_pure_delete .erase head destination)
          simp [potential, List.length_append]
          omega
      | rule =>
          have frame_length := congrArg List.length (cocycle .erase head)
          have initial_positive : 0 < initial.length := List.length_pos_of_ne_nil initial_nonempty
          simp [frame, destination, List.length_append] at frame_length
          simp [potential, List.length_append]
          omega

/-- Without state-preserving deletion, the charged queue length cannot decrease along a trace. -/
theorem Trace.potential_le {initial : List Bool}
    {δ : ControllerTransition PairPhase Bool}
    {produce cancel : PairPhase → Bool → List Bool}
    (initial_nonempty : initial ≠ []) (cocycle : Cocycle initial δ produce cancel)
    (no_pure_delete :
      ∀ phase head, δ phase head = phase → produce phase head ≠ [])
    {source target : PairPhase} {queue word residual : List Bool}
    (trace : Trace δ produce source queue word target residual) :
    potential source queue ≤ potential target residual := by
  induction trace with
  | nil => exact le_rfl
  | @step phase _ head tail _ _ _ induction =>
      exact (potential_step_le initial δ produce cancel initial_nonempty cocycle
        no_pure_delete phase head tail).trans induction

/-- An accepted input longer than one forces a state-preserving deletion role. -/
theorem pure_deletion_of_accepts_large (initial : List Bool)
    (δ : ControllerTransition PairPhase Bool)
    (produce cancel : PairPhase → Bool → List Bool)
    (initial_nonempty : initial ≠ []) (large : 1 < initial.length)
    (cocycle : Cocycle initial δ produce cancel)
    (accepts : Accepts δ produce initial) :
    ∃ phase head,
      δ phase head = phase ∧ produce phase head = [] ∧ cancel phase head = [] := by
  by_contra no_deletion
  have no_pure_delete :
      ∀ phase head, δ phase head = phase → produce phase head ≠ [] := by
    intro phase head fixed production_empty
    exact no_deletion ⟨phase, head, fixed, production_empty, by
      have lengths :
          (frame initial phase).length =
            (cancel phase head).length + (frame initial phase).length := by
        simpa [fixed, production_empty, List.length_append] using
          congrArg List.length (cocycle phase head)
      exact List.length_eq_zero_iff.mp (by omega)⟩
  obtain ⟨word, trace⟩ := accepts
  have bound := trace.potential_le initial_nonempty cocycle no_pure_delete
  simp [potential] at bound
  omega

end MatrixMortality.OverlapQueue
