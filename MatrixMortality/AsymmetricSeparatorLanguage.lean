import MatrixMortality.AsymmetricSeparatorTail

/-!
# The first one in a lower word

Every lower tile is either `0` or begins `110`. Consequently the first one in any concatenation
begins `110`, even when the control word is not a legal source computation.
-/

namespace MatrixMortality.AsymmetricSeparatorRealization

private theorem spell_first_one {α : Type*} (tiles : α → List Bool)
    (shape : ∀ letter, tiles letter = [false] ∨
      ∃ tail, tiles letter = [true, true, false] ++ tail)
    (word : List α) (zeros : Nat)
    (starts : List.replicate zeros false ++ [true] <+: spell tiles word) :
    List.replicate zeros false ++ [true, true, false] <+: spell tiles word := by
  induction word generalizing zeros with
  | nil =>
      have impossible : zeros + 1 ≤ 0 := by simpa [spell] using starts.length_le
      omega
  | cons letter rest induction =>
      rcases shape letter with zero | ⟨tail, rule⟩
      · cases zeros with
        | zero =>
            have mismatch : [true] <+: false :: spell tiles rest := by
              simpa only [spell, List.flatMap_cons, zero, List.replicate_zero,
                List.nil_append, List.cons_append] using starts
            exact Bool.noConfusion (List.cons_prefix_cons.mp mismatch).1
        | succ zeros =>
            have remaining : List.replicate zeros false ++ [true] <+: spell tiles rest := by
              simpa [spell, zero, List.replicate_succ] using starts
            simpa [spell, zero, List.replicate_succ] using induction zeros remaining
      · cases zeros with
        | zero => simp [spell, rule]
        | succ zeros =>
            have mismatch :
                false :: (List.replicate zeros false ++ [true]) <+:
                  true :: true :: false :: (tail ++ spell tiles rest) := by
              simpa only [spell, List.flatMap_cons, rule, List.replicate_succ,
                List.cons_append, List.nil_append, List.append_assoc] using starts
            exact Bool.noConfusion (List.cons_prefix_cons.mp mismatch).1

/-- The lower `c` tile shares the `110` prefix precisely because the body begins `10`. -/
theorem lowerTile_zero_or_110 (β : Nat) (body : List TagLetter)
    (encoded_prefix : [true, false] <+: tagEncode β body) (tile : NearyTile) :
    nearyLower β body tile = [false] ∨
      ∃ tail, nearyLower β body tile = [true, true, false] ++ tail := by
  cases tile with
  | erase letter => exact Or.inl rfl
  | rule letter =>
      cases letter with
      | b => exact Or.inr ⟨[], rfl⟩
      | c =>
          obtain ⟨tail, encoded_eq⟩ := encoded_prefix
          refine Or.inr ⟨tail ++ [true, false], ?_⟩
          simp [nearyLower, ← encoded_eq]

/-- Arbitrary lower words complete their first one to the same three-bit prefix. -/
theorem lowerWord_first_one (β : Nat) (body : List TagLetter)
    (encoded_prefix : [true, false] <+: tagEncode β body)
    (word : List NearyTile) (zeros : Nat)
    (starts : List.replicate zeros false ++ [true] <+: spell (nearyLower β body) word) :
    List.replicate zeros false ++ [true, true, false] <+: spell (nearyLower β body) word :=
  spell_first_one (nearyLower β body) (lowerTile_zero_or_110 β body encoded_prefix)
    word zeros starts

/-- A lower word cannot begin with zeros followed by `10`. -/
theorem lowerWord_no_10 (β : Nat) (body : List TagLetter)
    (encoded_prefix : [true, false] <+: tagEncode β body) (word : List NearyTile) (zeros : Nat) :
    ¬List.replicate zeros false ++ [true, false] <+: spell (nearyLower β body) word := by
  intro bad
  have one_prefix : List.replicate zeros false ++ [true] <+:
      List.replicate zeros false ++ [true, false] := by simp
  have complete := lowerWord_first_one β body encoded_prefix word zeros (one_prefix.trans bad)
  have compared := List.prefix_of_prefix_length_le bad complete (by simp)
  have impossible : [true, false] <+: [true, true, false] :=
    (List.prefix_append_right_inj _).mp compared
  exact (by decide : ¬[true, false] <+: [true, true, false]) impossible

/-- A lower word cannot begin with zeros followed by `111`. -/
theorem lowerWord_no_111 (β : Nat) (body : List TagLetter)
    (encoded_prefix : [true, false] <+: tagEncode β body) (word : List NearyTile) (zeros : Nat) :
    ¬List.replicate zeros false ++ [true, true, true] <+: spell (nearyLower β body) word := by
  intro bad
  have one_prefix : List.replicate zeros false ++ [true] <+:
      List.replicate zeros false ++ [true, true, true] := by simp
  have complete := lowerWord_first_one β body encoded_prefix word zeros (one_prefix.trans bad)
  have compared := List.prefix_of_prefix_length_le bad complete (by simp)
  have impossible : [true, true, true] <+: [true, true, false] :=
    (List.prefix_append_right_inj _).mp compared
  exact (by decide : ¬[true, true, true] <+: [true, true, false]) impossible

end MatrixMortality.AsymmetricSeparatorRealization
