import Mathlib.Data.List.Basic

/-!
# Free-monoid morphisms

The Kleisli extension `spell side` is the unique monoid morphism from source words that sends
each source letter `letter` to `side letter`. This file owns its source-independent laws.
-/

namespace MatrixMortality

/-- Extend a letter-to-word map to source words by concatenation. -/
def spell {α β : Type*} (side : α → List β) (word : List α) : List β :=
  (word.map side).join

theorem spell_append {α β : Type*} (side : α → List β) (left right : List α) :
    spell side (left ++ right) = spell side left ++ spell side right := by
  simp [spell, List.map_append]

theorem spell_map {α β γ : Type*} (map : β → γ) (side : α → List β) (word : List α) :
    spell (fun letter => (side letter).map map) word = (spell side word).map map := by
  induction word with
  | nil => simp [spell]
  | cons letter word induction => simp [spell, Function.comp_def, induction]

theorem spell_comp_spell {α β γ : Type*}
    (outer : β → List γ) (inner : α → List β) (word : List α) :
    spell outer (spell inner word) =
      spell (fun letter => spell outer (inner letter)) word := by
  induction word with
  | nil => rfl
  | cons letter word induction =>
      change spell outer (inner letter ++ spell inner word) =
        spell outer (inner letter) ++
          spell (fun current => spell outer (inner current)) word
      rw [spell_append, induction]

theorem spell_comp_map {α β γ : Type*} (side : β → List γ) (map : α → β)
    (word : List α) :
    spell (side ∘ map) word = spell side (word.map map) := by
  simp [spell, Function.comp_def]

end MatrixMortality
