import MatrixMortality.PairedMortality
import MatrixMortality.Undecidability.Problems

/-!
# Canonical four-matrix paired-role instances

The algebraic compiler uses the semantic label type `Option PairedControl`.  This file transports
its four labels to `Fin 4`, the transparent carrier of the encoded `M₄(4)` decision problem.
-/

namespace MatrixMortality

open scoped Matrix

namespace Undecidability

/-- Canonical enumeration of the two data controls, toggle, and separator. -/
def pairedMortalityLabelOfFin : Fin 4 → Option PairedControl
  | ⟨0, _⟩ => some (.data .b)
  | ⟨1, _⟩ => some (.data .c)
  | ⟨2, _⟩ => some .toggle
  | ⟨3, _⟩ => none

/-- Inverse of `pairedMortalityLabelOfFin`. -/
def finOfPairedMortalityLabel : Option PairedControl → Fin 4
  | some (.data .b) => 0
  | some (.data .c) => 1
  | some .toggle => 2
  | none => 3

theorem pairedMortalityLabelOfFin_finOfPairedMortalityLabel
    (label : Option PairedControl) :
    pairedMortalityLabelOfFin (finOfPairedMortalityLabel label) = label := by
  cases label with
  | none => rfl
  | some control => cases control with
    | toggle => rfl
    | data letter => cases letter <;> rfl

theorem finOfPairedMortalityLabel_pairedMortalityLabelOfFin (label : Fin 4) :
    finOfPairedMortalityLabel (pairedMortalityLabelOfFin label) = label := by
  fin_cases label <;> rfl

/-- The fixed computable equivalence at the four-matrix boundary. -/
def pairedMortalityLabelEquivFin : Option PairedControl ≃ Fin 4 where
  toFun := finOfPairedMortalityLabel
  invFun := pairedMortalityLabelOfFin
  left_inv := pairedMortalityLabelOfFin_finOfPairedMortalityLabel
  right_inv := finOfPairedMortalityLabel_pairedMortalityLabelOfFin

private theorem isMortal_comp_equiv {a b M : Type*} [MonoidWithZero M]
    (generators : b → M) (equivalence : a ≃ b) :
    IsMortal (generators ∘ equivalence) ↔ IsMortal generators := by
  constructor
  · rintro ⟨word, word_nonempty, product_zero⟩
    refine ⟨word.map equivalence, ?_, ?_⟩
    · simpa using word_nonempty
    · simpa [List.map_map, Function.comp_def] using product_zero
  · rintro ⟨word, word_nonempty, product_zero⟩
    refine ⟨word.map equivalence.symm, ?_, ?_⟩
    · simpa using word_nonempty
    · simpa [List.map_map, Function.comp_def] using product_zero

/-- The four exact `4 × 4` integer matrices emitted by one restricted tag source. -/
def nearyMortality44 (β : Nat) (body : List TagLetter) : Mortality44 :=
  fun label row column =>
    pairedMortalityFamily ℤ β body (pairedMortalityLabelOfFin label) row column

theorem nearyMortality44_mortal_iff_tagHaltsFrom (β : Nat) (body : List TagLetter)
    (β_large : 2 < β) (body_long : β - 1 ≤ body.length)
    (body_divisible : β - 1 ∣ body.length) :
    (nearyMortality44 β body).Mortal ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  rw [← pairedMortalityFamily_int_mortal_iff_tagHaltsFrom β body β_large body_long
    body_divisible]
  exact isMortal_comp_equiv (pairedMortalityFamily ℤ β body)
    pairedMortalityLabelEquivFin.symm

/-- The three nonseparator generators in the encoded family share the first column `e₁`. -/
theorem nearyMortality44_control_fixes_anchor (β : Nat) (body : List TagLetter)
    (label : Fin 3) :
    ((nearyMortality44 β body).matrix (Fin.castSucc label)) *ᵥ pairedAnchor ℤ =
      pairedAnchor ℤ := by
  fin_cases label
  · simpa [Mortality44.matrix, nearyMortality44, pairedMortalityLabelOfFin,
      pairedMortalityFamily, separatedGenerator] using
      pairedGenerator_mulVec_anchor ℤ β body (.data .b)
  · simpa [Mortality44.matrix, nearyMortality44, pairedMortalityLabelOfFin,
      pairedMortalityFamily, separatedGenerator] using
      pairedGenerator_mulVec_anchor ℤ β body (.data .c)
  · simpa [Mortality44.matrix, nearyMortality44, pairedMortalityLabelOfFin,
      pairedMortalityFamily, separatedGenerator] using
      pairedGenerator_mulVec_anchor ℤ β body .toggle

/-- The third control generator is the permutation matrix swapping coordinates one and three. -/
theorem nearyMortality44_toggle_eq_permMatrix (β : Nat) (body : List TagLetter) :
    (nearyMortality44 β body).matrix 2 =
      (Equiv.swap (1 : Fin 4) 3).permMatrix ℤ := by
  exact pairedToggleMatrix_eq_permMatrix ℤ

theorem nearyMortality44_separator_ne_zero (β : Nat) (body : List TagLetter) :
    (nearyMortality44 β body).matrix 3 ≠ 0 := by
  exact pairedSeparator_int_ne_zero β

theorem nearyMortality44_separator_rank_eq_one (β : Nat) (body : List TagLetter) :
    (castMatrix4 ((nearyMortality44 β body).matrix 3)).toLin'.rank = 1 := by
  exact castMatrix4_pairedSeparator_rank_eq_one β

end Undecidability

namespace NearyArithmeticEnvelope

/-- The exact four-matrix instance emitted by an arithmetic-envelope source. -/
def mortality44 (source : NearyArithmeticEnvelope) : Undecidability.Mortality44 :=
  Undecidability.nearyMortality44 source.β source.body

theorem mortality44_iff_halts (source : NearyArithmeticEnvelope) :
    source.mortality44.Mortal ↔
      TagHaltsFrom source.β (tagOutput source.body) source.initial := by
  exact Undecidability.nearyMortality44_mortal_iff_tagHaltsFrom source.β source.body
    source.beta_large source.body_long source.body_divisible

end NearyArithmeticEnvelope

end MatrixMortality
