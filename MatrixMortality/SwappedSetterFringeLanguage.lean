import MatrixMortality.NearyEncoding

/-!
# Swapped-setter fringe languages

The depth-one setter comparison leaves one upper word, one lower word, and a bounded suffix.
This file owns their body-independent regular languages and the ternary code read by the swapped
setter.  Arithmetic classification belongs in `SwappedSetterFringe`.
-/

namespace MatrixMortality.SwappedSetterFringe

/-- Ternary code after exchanging the two binary digits. -/
def swappedCode (word : List Bool) : Nat :=
  ternaryCode (word.map Bool.not)

/-- Body-independent lower block at a phase of the Neary spelling. -/
def fringeBlock : Bool → List Bool
  | false => [false]
  | true => [true, true, false]

/-- A lower fringe may stop at any point inside a sequence of complete lower blocks. -/
def SourceFringe (word : List Bool) : Prop :=
  ∃ phases, word <+: spell fringeBlock phases

/-- Final bounded window of a body-independent lower spelling ending in an erasure. -/
def BlockTargetFringe (width : Nat) (word : List Bool) : Prop :=
  ∃ phases,
    phases.getLast? = some false ∧
      word = (spell fringeBlock phases).rtake width

/-- Necessary normal form of a physical target fringe ending in an erasure.  A preceding rule
block contributes either no `true`, a complete final pair, or the right member of a pair cut by
the width boundary.  The prefix before a complete pair may come from an encoded appendant. -/
def TargetFringe (width : Nat) (word : List Bool) : Prop :=
  word.length ≤ width ∧
    ((∃ zeros,
        2 ≤ zeros ∧
          word = List.replicate zeros false) ∨
      (∃ front zeros,
        2 ≤ zeros ∧
          word = front ++ [true, true] ++ List.replicate zeros false) ∨
      (word.length = width ∧
        word = true :: List.replicate (width - 1) false))

/-- The two possible shapes of the maximal unmatched upper fringe. -/
def UpperFringe (β : Nat) (word : List Bool) : Prop :=
  word = tagCode β .b ∨
    ∃ ones,
      2 ≤ ones ∧
        ones ≤ β + 2 ∧
          word = List.replicate ones true ++ List.replicate (β + 2 - ones) false

private theorem take_fringeBlock_complete_or_last_true (phases : List Bool) (n : Nat) :
    (∃ cutPhases,
        List.take n (spell fringeBlock phases) = spell fringeBlock cutPhases) ∨
      (List.take n (spell fringeBlock phases)).getLast? = some true := by
  induction phases generalizing n with
  | nil => exact Or.inl ⟨[], by simp [spell]⟩
  | cons phase phases induction =>
      cases phase with
      | false =>
          cases n with
          | zero => exact Or.inl ⟨[], rfl⟩
          | succ n =>
              rcases induction n with complete | lastTrue
              · left
                obtain ⟨cutPhases, cut_eq⟩ := complete
                refine ⟨false :: cutPhases, ?_⟩
                change false :: List.take n (spell fringeBlock phases) =
                  false :: spell fringeBlock cutPhases
                rw [cut_eq]
              · right
                change (false :: List.take n (spell fringeBlock phases)).getLast? = some true
                rw [List.getLast?_cons_of_ne_nil]
                · exact lastTrue
                · intro taken_empty
                  rw [taken_empty] at lastTrue
                  simp at lastTrue
      | true =>
          cases n with
          | zero => exact Or.inl ⟨[], rfl⟩
          | succ n =>
              cases n with
              | zero => exact Or.inr rfl
              | succ n =>
                  cases n with
                  | zero => exact Or.inr rfl
                  | succ n =>
                      rcases induction n with complete | lastTrue
                      · left
                        obtain ⟨cutPhases, cut_eq⟩ := complete
                        refine ⟨true :: cutPhases, ?_⟩
                        change [true, true, false] ++
                            List.take n (spell fringeBlock phases) =
                          [true, true, false] ++ spell fringeBlock cutPhases
                        rw [cut_eq]
                      · right
                        change
                          ([true, true, false] ++
                            List.take n (spell fringeBlock phases)).getLast? = some true
                        rw [List.getLast?_append_of_ne_nil]
                        · exact lastTrue
                        · intro taken_empty
                          rw [taken_empty] at lastTrue
                          simp at lastTrue

/-- A source fringe ending in zero cannot stop inside the `11` part of a rule block. -/
theorem sourceFringe_complete_of_getLast?_false {word : List Bool}
    (source : SourceFringe word) (last : word.getLast? = some false) :
    ∃ phases, word = spell fringeBlock phases := by
  obtain ⟨phases, isPrefix⟩ := source
  have word_eq : word = List.take word.length (spell fringeBlock phases) :=
    List.prefix_iff_eq_take.mp isPrefix
  rcases take_fringeBlock_complete_or_last_true phases word.length with complete | lastTrue
  · obtain ⟨cutPhases, complete_eq⟩ := complete
    exact ⟨cutPhases, word_eq.trans complete_eq⟩
  · rw [← word_eq, last] at lastTrue
    simp at lastTrue

private theorem fringeSpelling_zero_or_lastTrue (phases : List Bool) :
    spell fringeBlock phases = List.replicate phases.length false ∨
      ∃ front tailLength,
        1 ≤ tailLength ∧
          spell fringeBlock phases =
            spell fringeBlock front ++ [true, true] ++
              List.replicate tailLength false := by
  induction phases using List.reverseRecOn with
  | nil => exact Or.inl rfl
  | append_singleton phases phase induction =>
      rw [spell_append]
      cases phase with
      | false =>
          rcases induction with allFalse | lastTrue
          · left
            rw [allFalse]
            simp [spell, fringeBlock, List.replicate_succ']
          · right
            obtain ⟨front, tailLength, tail_pos, form⟩ := lastTrue
            refine ⟨front, tailLength + 1, by omega, ?_⟩
            rw [form]
            simp [spell, fringeBlock, List.replicate_succ']
      | true =>
          right
          refine ⟨phases, 1, by omega, ?_⟩
          simp [spell, fringeBlock]

/-- A zero-ending source fringe is either all erasures or has a final rule followed by a
positive zero tail. The prefix before that rule remains a complete block spelling. -/
theorem sourceFringe_lastTrue_normal {word : List Bool}
    (source : SourceFringe word) (last : word.getLast? = some false) :
    (∃ zeros,
        1 ≤ zeros ∧ word = List.replicate zeros false) ∨
      (∃ front phases zeros,
        1 ≤ zeros ∧
          front = spell fringeBlock phases ∧
            word = front ++ [true, true] ++ List.replicate zeros false) := by
  obtain ⟨phases, word_eq⟩ := sourceFringe_complete_of_getLast?_false source last
  rcases fringeSpelling_zero_or_lastTrue phases with allFalse | lastTrue
  · left
    refine ⟨phases.length, ?_, word_eq.trans allFalse⟩
    have phases_ne : phases ≠ [] := by
      intro phases_empty
      subst phases
      simp [spell] at word_eq
      subst word
      simp at last
    have phases_pos := List.length_pos_of_ne_nil phases_ne
    omega
  · right
    obtain ⟨frontPhases, tailLength, tail_pos, form⟩ := lastTrue
    exact ⟨spell fringeBlock frontPhases, frontPhases, tailLength, tail_pos, rfl,
      word_eq.trans form⟩

end MatrixMortality.SwappedSetterFringe
