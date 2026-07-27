import MatrixMortality.WordMorphism
import Mathlib.Logic.Equiv.Defs

/-!
# The primitive-to-terminal PCP bridge

This file formalizes the generic logical bridge from a primitive-terminal PCP property to the
terminal matching problem consumed by the matrix reduction.  `MarkedTerminal.lean` later
constructs that property directly with a fresh delimiter; `NearyEncoding.lean` proves the
underlying four-tile terminal equation from tag semantics.
-/

namespace MatrixMortality

/-- A nonempty solution word for a Post correspondence instance. -/
def IsPCPSolution {α β : Type*} (u v : α → List β) (word : List α) : Prop :=
  word ≠ [] ∧ spell u word = spell v word

/-- A PCP solution that is not the concatenation of two nonempty solution words. -/
def IsPrimitivePCPSolution {α β : Type*} (u v : α → List β) (word : List α) : Prop :=
  IsPCPSolution u v word ∧
    ¬ ∃ x y : List α, x ≠ [] ∧ y ≠ [] ∧ word = x ++ y ∧
      IsPCPSolution u v x ∧ IsPCPSolution u v y

/-- A generalized-PCP solution with independently fixed left and right boundaries. -/
def IsGPCPSolution {α β : Type*} (u v : α → List β)
    (leftU rightU leftV rightV : List β) (word : List α) : Prop :=
  leftU ++ spell u word ++ rightU = leftV ++ spell v word ++ rightV

/-- The nonempty-witness convention for generalized PCP. -/
def IsGPCPPlusSolution {α β : Type*} (u v : α → List β)
    (leftU rightU leftV rightV : List β) (word : List α) : Prop :=
  word ≠ [] ∧ IsGPCPSolution u v leftU rightU leftV rightV word

theorem gpcpSolvable_relabel_equiv {α β γ : Type*}
    (u v : β → List γ) (leftU rightU leftV rightV : List γ)
    (equivalence : Equiv α β) :
    (∃ word : List α,
      IsGPCPSolution (u ∘ equivalence) (v ∘ equivalence)
        leftU rightU leftV rightV word) ↔
      ∃ word : List β, IsGPCPSolution u v leftU rightU leftV rightV word := by
  constructor
  · rintro ⟨word, solution⟩
    refine ⟨word.map equivalence, ?_⟩
    simpa [IsGPCPSolution, spell_comp_map] using solution
  · rintro ⟨word, solution⟩
    refine ⟨word.map equivalence.symm, ?_⟩
    rw [IsGPCPSolution, spell_comp_map, spell_comp_map]
    simpa [IsGPCPSolution, List.map_map, Function.comp_def] using solution

theorem gpcpPlusSolvable_relabel_equiv {α β γ : Type*}
    (u v : β → List γ) (leftU rightU leftV rightV : List γ)
    (equivalence : Equiv α β) :
    (∃ word : List α,
      IsGPCPPlusSolution (u ∘ equivalence) (v ∘ equivalence)
        leftU rightU leftV rightV word) ↔
      ∃ word : List β, IsGPCPPlusSolution u v leftU rightU leftV rightV word := by
  constructor
  · rintro ⟨word, word_nonempty, solution⟩
    exact ⟨word.map equivalence, by simpa using word_nonempty,
      by simpa [IsGPCPSolution, spell_comp_map] using solution⟩
  · rintro ⟨word, word_nonempty, solution⟩
    refine ⟨word.map equivalence.symm, by simpa using word_nonempty, ?_⟩
    rw [IsGPCPSolution, spell_comp_map, spell_comp_map]
    simpa [IsGPCPSolution, List.map_map, Function.comp_def] using solution

/-- Every solvable PCP instance has a primitive solution. -/
theorem exists_primitive_of_solution {α β : Type*} (u v : α → List β)
    {word : List α} (hword : IsPCPSolution u v word) :
    ∃ primitive, IsPrimitivePCPSolution u v primitive := by
  have descend : ∀ n, ∀ candidate : List α, candidate.length = n →
      IsPCPSolution u v candidate → ∃ primitive, IsPrimitivePCPSolution u v primitive := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro candidate hlength hcandidate
        by_cases hprimitive : IsPrimitivePCPSolution u v candidate
        · exact ⟨candidate, hprimitive⟩
        · have hsplit : ∃ x y : List α, x ≠ [] ∧ y ≠ [] ∧ candidate = x ++ y ∧
              IsPCPSolution u v x ∧ IsPCPSolution u v y := by
            by_contra hnone
            exact hprimitive ⟨hcandidate, hnone⟩
          rcases hsplit with ⟨x, y, _, hy, hxy, hxsolution, _⟩
          have hxlength : x.length < n := by
            rw [← hlength, hxy, List.length_append]
            exact Nat.lt_add_of_pos_right (List.length_pos.mpr hy)
          exact ih x.length hxlength x rfl hxsolution
  exact descend word.length word rfl hword

/-- Add one distinguished terminal tile to a family of ordinary tiles. -/
def fullSide {α β : Type*} (side : α → List β) (terminal : List β) :
    Option α → List β
  | none => terminal
  | some i => side i

theorem spell_map_some_append_none {α β : Type*} (side : α → List β)
    (terminal : List β) (word : List α) :
    spell (fullSide side terminal) (word.map some ++ [none]) = spell side word ++ terminal := by
  simp [spell, List.map_append, List.map_map, Function.comp_def, fullSide]

/-- If every primitive solution uses the distinguished tile exactly once and at the end, ordinary
PCP solvability is equivalent to the terminal matching problem used by the matrix reduction. -/
theorem pcp_solvable_iff_terminal_match_of_primitive_terminal
    {α β : Type*} (u v : α → List β) (uₜ vₜ : List β)
    (hterminal : ∀ word : List (Option α),
      IsPrimitivePCPSolution (fullSide u uₜ) (fullSide v vₜ) word →
        ∃ interior : List α, word = interior.map some ++ [none]) :
    (∃ word, IsPCPSolution (fullSide u uₜ) (fullSide v vₜ) word) ↔
      ∃ interior, spell u interior ++ uₜ = spell v interior ++ vₜ := by
  constructor
  · rintro ⟨word, hword⟩
    obtain ⟨primitive, hprimitive⟩ := exists_primitive_of_solution
      (fullSide u uₜ) (fullSide v vₜ) hword
    obtain ⟨interior, rfl⟩ := hterminal primitive hprimitive
    refine ⟨interior, ?_⟩
    simpa [spell_map_some_append_none] using hprimitive.1.2
  · rintro ⟨interior, hmatch⟩
    refine ⟨interior.map some ++ [none], ?_⟩
    constructor
    · simp
    · simpa [spell_map_some_append_none] using hmatch

/-- A terminal match is exactly a GPCP instance with empty left boundaries and the terminal
tile as the two right boundaries.  Thus a five-tile primitive-terminal PCP source has only four
active GPCP generators. -/
theorem terminal_match_iff_right_bounded_gpcp {α : Type*}
    {β : Type*} (u v : α → List β) (uₜ vₜ : List β) :
    (∃ word, spell u word ++ uₜ = spell v word ++ vₜ) ↔
      ∃ word, IsGPCPSolution u v [] uₜ [] vₜ word := by
  simp [IsGPCPSolution]

/-- The primitive-terminal hypothesis converts ordinary PCP solvability directly into a
right-bounded GPCP instance on the ordinary-tile alphabet. -/
theorem pcp_solvable_iff_right_bounded_gpcp_of_primitive_terminal
    {α β : Type*} (u v : α → List β) (uₜ vₜ : List β)
    (hterminal : ∀ word : List (Option α),
      IsPrimitivePCPSolution (fullSide u uₜ) (fullSide v vₜ) word →
        ∃ interior : List α, word = interior.map some ++ [none]) :
    (∃ word, IsPCPSolution (fullSide u uₜ) (fullSide v vₜ) word) ↔
      ∃ interior, IsGPCPSolution u v [] uₜ [] vₜ interior :=
  (pcp_solvable_iff_terminal_match_of_primitive_terminal u v uₜ vₜ hterminal).trans
    (terminal_match_iff_right_bounded_gpcp u v uₜ vₜ)

/-- If the terminal words differ, the induced GPCP witness is automatically nonempty. -/
theorem pcp_solvable_iff_right_bounded_gpcpPlus_of_primitive_terminal
    {α β : Type*} (u v : α → List β) (uₜ vₜ : List β) (hterminalWords : uₜ ≠ vₜ)
    (hterminal : ∀ word : List (Option α),
      IsPrimitivePCPSolution (fullSide u uₜ) (fullSide v vₜ) word →
        ∃ interior : List α, word = interior.map some ++ [none]) :
    (∃ word, IsPCPSolution (fullSide u uₜ) (fullSide v vₜ) word) ↔
      ∃ interior, IsGPCPPlusSolution u v [] uₜ [] vₜ interior := by
  rw [pcp_solvable_iff_right_bounded_gpcp_of_primitive_terminal u v uₜ vₜ hterminal]
  constructor
  · rintro ⟨interior, hmatch⟩
    refine ⟨interior, ?_, hmatch⟩
    intro hinterior
    subst interior
    exact hterminalWords (by simpa [IsGPCPSolution] using hmatch)
  · rintro ⟨interior, _, hmatch⟩
    exact ⟨interior, hmatch⟩

end MatrixMortality
