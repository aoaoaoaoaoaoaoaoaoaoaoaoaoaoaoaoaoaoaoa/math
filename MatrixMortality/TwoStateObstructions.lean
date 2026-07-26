import MatrixMortality.PairedMortality
import MatrixMortality.TwoStatePushout

/-!
# Exact obstructions at the three-generator four-state frontier

This file owns exact compiler obstructions left by the failed `M₄(3)` attack. Each theorem
states only the algebraic architecture it excludes.
-/

namespace MatrixMortality

open scoped Matrix

/-- Replace the paired toggle by one proposed fused generator. -/
def fusedPairedGenerator (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter)
    (fused : Matrix (Fin 4) (Fin 4) R) : Option TagLetter → Matrix (Fin 4) (Fin 4) R
  | none => fused
  | some letter => pairedDataMatrix R β body letter

/-- Exact left-context toggle behavior at even one data letter forces the proposed fusion to
retain the common nonzero anchor. -/
theorem exactLeftToggleFusion_fixes_anchor (R : Type*) [CommRing R]
    (β : Nat) (body : List TagLetter) (fused : Matrix (Fin 4) (Fin 4) R)
    (letter : TagLetter)
    (exact :
      fused * pairedDataMatrix R β body letter =
        pairedToggleMatrix R * pairedDataMatrix R β body letter) :
    fused *ᵥ pairedAnchor R = pairedAnchor R := by
  have applied := congrArg (fun matrix => matrix *ᵥ pairedAnchor R) exact
  change (fused * pairedDataMatrix R β body letter) *ᵥ pairedAnchor R =
    (pairedToggleMatrix R * pairedDataMatrix R β body letter) *ᵥ pairedAnchor R at applied
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at applied
  have data_fixed :
      pairedDataMatrix R β body letter *ᵥ pairedAnchor R = pairedAnchor R := by
    simpa [pairedGenerator] using
      pairedGenerator_mulVec_anchor R β body (.data letter)
  have toggle_fixed :
      pairedToggleMatrix R *ᵥ pairedAnchor R = pairedAnchor R := by
    simpa [pairedGenerator] using
      pairedGenerator_mulVec_anchor R β body .toggle
  simpa [data_fixed, toggle_fixed] using applied

/-- Exact left-context fusion is immortal. The traditional invertible two-plane argument is
unnecessary: the contextual identity already preserves the common first column. -/
theorem exactLeftToggleFusion_immortal (R : Type*) [CommRing R] [Nontrivial R]
    (β : Nat) (body : List TagLetter) (fused : Matrix (Fin 4) (Fin 4) R)
    (letter : TagLetter)
    (exact :
      fused * pairedDataMatrix R β body letter =
        pairedToggleMatrix R * pairedDataMatrix R β body letter) :
    ¬IsMortal (fusedPairedGenerator R β body fused) := by
  have fused_fixed := exactLeftToggleFusion_fixes_anchor R β body fused letter exact
  have fixed :
      ∀ label,
        fusedPairedGenerator R β body fused label *ᵥ pairedAnchor R = pairedAnchor R := by
    intro label
    cases label with
    | none => exact fused_fixed
    | some data =>
        simpa [fusedPairedGenerator, pairedGenerator] using
          pairedGenerator_mulVec_anchor R β body (.data data)
  have anchor_nonzero : pairedAnchor R ≠ 0 := by
    intro anchor_zero
    have entry := congr_fun anchor_zero 0
    simp [pairedAnchor] at entry
  rintro ⟨word, _, product_zero⟩
  exact wordProduct_ne_zero_of_fixed
    (fusedPairedGenerator R β body fused) (pairedAnchor R) fixed anchor_nonzero word
    product_zero

end MatrixMortality
