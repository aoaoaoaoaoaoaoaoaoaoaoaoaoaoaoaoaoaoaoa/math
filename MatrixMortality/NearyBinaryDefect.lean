import MatrixMortality.BinaryDefect
import MatrixMortality.NearyEncoding

/-!
# Binary morphism obstruction for Neary macro roles

The generic two-word defect theorem forbids assigning distinct internal and final binary
codewords to one exact Neary macro realization.
-/

namespace MatrixMortality

/-- Upper word of either Neary macro role after pairing a role with the following `D_b`. -/
def nearyMacroUpper (β : Nat) : TagLetter → List Bool
  | .b => tagCode β .b ++ tagCode β .b
  | .c => tagCode β .c ++ tagCode β .b

theorem nearyMacroUpper_not_commute (β : Nat) (β_pos : 0 < β) :
    nearyMacroUpper β .b ++ nearyMacroUpper β .c ≠
      nearyMacroUpper β .c ++ nearyMacroUpper β .b := by
  cases β with
  | zero => omega
  | succ β =>
      simp [nearyMacroUpper, tagCode, List.replicate_succ]

/-- Distinct exact internal and final binary codes for one macro are incompatible with exact
realizations of both noncommuting Neary macro upper words. -/
theorem neary_exact_internal_final_code_impossible
    (β : Nat) (β_pos : 0 < β)
    (upper : Bool → List Bool)
    (internal final codeB codeC : List Bool)
    (codes_ne : internal ≠ final)
    (same_macro : spell upper internal = spell upper final)
    (realize_b : spell upper codeB = nearyMacroUpper β .b)
    (realize_c : spell upper codeC = nearyMacroUpper β .c) :
    False := by
  have not_injective :
      ¬Function.Injective (binarySpell (upper false) (upper true)) := by
    apply Function.not_injective_iff.mpr
    refine ⟨internal, final, ?_, codes_ne⟩
    simpa only [← spell_eq_binarySpell] using same_macro
  have letters_commute :=
    binarySpell_not_injective_commute (upper false) (upper true) not_injective
  have images_commute :=
    binarySpell_commute_of_letter_commute letters_commute codeB codeC
  rw [← spell_eq_binarySpell upper codeB, ← spell_eq_binarySpell upper codeC,
    realize_b, realize_c] at images_commute
  exact nearyMacroUpper_not_commute β β_pos images_commute

end MatrixMortality
