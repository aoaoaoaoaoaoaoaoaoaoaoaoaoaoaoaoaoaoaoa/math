import MatrixMortality.PairedMortality
import MatrixMortality.Undecidability.NearyProblems

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

/-- The four exact `4 × 4` integer matrices emitted by one restricted tag source. -/
def nearyMortality44 (β : Nat) (body : List TagLetter) : Mortality44 :=
  fun label row column =>
    pairedMortalityFamily ℤ β body (pairedMortalityLabelOfFin label) row column

private theorem pairedDataMatrix_int_entry_primrec (β : Nat) (letter : TagLetter)
    (row column : Fin 4) :
    Primrec fun body : List TagLetter => pairedDataMatrix ℤ β body letter row column := by
  have ruleWord := nearyLower_primrec β (.rule letter)
  have eraseWord := nearyLower_primrec β (.erase letter)
  have ruleCode := ternaryCode_int_primrec.comp ruleWord
  have eraseCode := ternaryCode_int_primrec.comp eraseWord
  have ruleScale := ternaryScale_int_primrec.comp ruleWord
  have eraseScale := ternaryScale_int_primrec.comp eraseWord
  fin_cases row <;> fin_cases column <;>
    simp [pairedDataMatrix_eq_explicit]
  all_goals first | exact Primrec.const _ | exact ruleCode | exact eraseCode |
    exact ruleScale | exact eraseScale

/-- The four-matrix paired compiler is primitive recursive in its variable body. -/
theorem nearyMortality44_primrec (β : Nat) :
    Primrec (nearyMortality44 β) := by
  apply MortalityProblem.primrec
  intro label row column
  fin_cases label
  · exact pairedDataMatrix_int_entry_primrec β .b row column
  · exact pairedDataMatrix_int_entry_primrec β .c row column
  · exact Primrec.const _
  · exact Primrec.const _

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
  · change pairedGenerator ℤ β body (.data .b) *ᵥ pairedAnchor ℤ = pairedAnchor ℤ
    exact pairedGenerator_mulVec_anchor ℤ β body (.data .b)
  · change pairedGenerator ℤ β body (.data .c) *ᵥ pairedAnchor ℤ = pairedAnchor ℤ
    exact pairedGenerator_mulVec_anchor ℤ β body (.data .c)
  · change pairedGenerator ℤ β body .toggle *ᵥ pairedAnchor ℤ = pairedAnchor ℤ
    exact pairedGenerator_mulVec_anchor ℤ β body .toggle

/-- The third control generator swaps one-based coordinates two and four,
equivalently `Fin 4` indices `1` and `3`. -/
theorem nearyMortality44_toggle_eq_permMatrix (β : Nat) (body : List TagLetter) :
    (nearyMortality44 β body).matrix 2 =
      (Equiv.swap (1 : Fin 4) 3).permMatrix ℤ := by
  exact pairedToggleMatrix_eq_permMatrix ℤ

theorem nearyMortality44_separator_ne_zero (β : Nat) (body : List TagLetter) :
    (nearyMortality44 β body).matrix 3 ≠ 0 := by
  exact pairedSeparator_int_ne_zero β

theorem nearyMortality44_separator_rank_eq_one (β : Nat) (body : List TagLetter) :
    (castMatrix ((nearyMortality44 β body).matrix 3)).toLin'.rank = 1 := by
  exact castMatrix_pairedSeparator_rank_eq_one β

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
