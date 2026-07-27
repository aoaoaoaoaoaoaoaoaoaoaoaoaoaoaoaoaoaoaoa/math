import MatrixMortality.MarkedTerminal
import MatrixMortality.TerminalReduction

/-!
# Terminal correspondence compilers

This file composes source-level terminal synchronization with the three-dimensional rank-one
mortality reduction.
-/

namespace MatrixMortality

/-- A primitive-terminal property makes mortality of the absorbed integer family equivalent to
solvability of the corresponding PCP instance. -/
theorem absorbedFamily_int_mortal_iff_pcp_solvable_of_primitive_terminal
    {α : Type*} (u v : α → List Bool) (uₜ vₜ : List Bool)
    (hterminal : ∀ word : List (Option α),
      IsPrimitivePCPSolution (fullSide u uₜ) (fullSide v vₜ) word →
        ∃ interior : List α, word = interior.map some ++ [none]) :
    IsMortal (absorbedFamily ℤ u v uₜ vₜ) ↔
      ∃ word, IsPCPSolution (fullSide u uₜ) (fullSide v vₜ) word :=
  (absorbedFamily_int_mortal_iff_terminal_match u v uₜ vₜ).trans
    (pcp_solvable_iff_terminal_match_of_primitive_terminal u v uₜ vₜ hterminal).symm

/-- The exact integer family obtained after binary marker recoding. -/
def synchronizedFamilyInt {ι : Type*} (u v : ι → List Bool) (terminal : List Bool) :
    Option ι → Matrix (Fin 3) (Fin 3) Int :=
  absorbedFamily ℤ (binaryMarkedOrdinary u) (binaryMarkedOrdinary v)
    (binaryMarkedTerminal terminal) (binaryMarkedTerminal [])

/-- Fresh-marker synchronization and fixed-length binary recoding preserve the terminal word
equation through the exact five-matrix compiler. -/
theorem synchronizedFamilyInt_mortal_iff_terminal_match {ι : Type*}
    (u v : ι → List Bool) (terminal : List Bool) :
    IsMortal (synchronizedFamilyInt u v terminal) ↔
      ∃ word, spell u word ++ terminal = spell v word := by
  rw [synchronizedFamilyInt, absorbedFamily_int_mortal_iff_terminal_match]
  apply exists_congr
  intro word
  rw [spell_binaryMarkedOrdinary, spell_binaryMarkedOrdinary]
  constructor
  · intro hmatch
    have hencoded : encodeMarkedBits (suture (spell u word ++ terminal)) =
        encodeMarkedBits (suture (spell v word)) := by
      simpa [binaryMarkedTerminal, suture, encodeMarkedBits_append, List.map_append,
        List.append_assoc] using hmatch
    exact (suture_prefix_iff _ _).mp <| by
      simp [encodeMarkedBits_injective hencoded]
  · intro hmatch
    have hencoded := congrArg encodeMarkedBits (congrArg suture hmatch)
    simpa [binaryMarkedTerminal, suture, encodeMarkedBits_append, List.map_append,
      List.append_assoc] using hencoded

end MatrixMortality
