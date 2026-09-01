import MatrixMortality.DecimalSetterMatrix
import MatrixMortality.RationalMatrixClearing
import MatrixMortality.Undecidability.Problems

/-!
# Integer family of the decimal five-state setter

Entrywise denominator clearing turns the rational setter into three integer `5 × 5` matrices
without changing mortality.  This module establishes the exact family and the forward compiler;
primitive-recursive emission and the arbitrary-word converse remain separate obligations.
-/

namespace MatrixMortality.DecimalSetterInteger

open MatrixMortality.DecimalSetterMatrix
open MatrixMortality.RationalMatrixClearing

/-- Explicit enumeration of the delimiter and two data letters. -/
def physicalLabel : Fin 3 → Option TagLetter :=
  ![none, some .b, some .c]

/-- The explicit three-label enumeration is bijective. -/
def physicalLabelEquiv : Fin 3 ≃ Option TagLetter :=
  { toFun := physicalLabel
    invFun := fun
      | none => 0
      | some .b => 1
      | some .c => 2
    left_inv := by
      intro label
      fin_cases label <;> rfl
    right_inv := by
      intro label
      rcases label with _ | letter
      · rfl
      · cases letter <;> rfl }

/-- Three rational setter generators with the decision-problem label type. -/
def rationalFamily (β : Nat) (body : List TagLetter) :
    Fin 3 → Square (Fin 5) ℚ :=
  generator β body ∘ physicalLabelEquiv

/-- Three integer setter generators obtained by independent denominator clearing. -/
def integerFamily (β : Nat) (body : List TagLetter) :
    Fin 3 → Square (Fin 5) ℤ :=
  clearRationalFamily (rationalFamily β body)

/-- Transparent `M₅(3)` instance emitted by the decimal setter. -/
def mortalityProblem (β : Nat) (body : List TagLetter) :
    Undecidability.MortalityProblem 5 3 :=
  integerFamily β body

/-- Clearing and the explicit label equivalence preserve mortality exactly. -/
theorem integerFamily_mortal_iff (β : Nat) (body : List TagLetter) :
    IsMortal (integerFamily β body) ↔ IsMortal (generator β body) := by
  rw [integerFamily, clearRationalFamily_mortal_iff, rationalFamily,
    isMortal_comp_equiv]

/-- The transparent mortality problem denotes the cleared integer family. -/
theorem mortalityProblem_mortal_iff (β : Nat) (body : List TagLetter) :
    (mortalityProblem β body).Mortal ↔ IsMortal (generator β body) := by
  exact integerFamily_mortal_iff β body

/-- Halting of a restricted Neary source implies mortality of its integer `M₅(3)` instance. -/
theorem mortalityProblem_mortal_of_tagHaltsFrom (β : Nat) (body : List TagLetter)
    (β_large : 2 < β) (body_long : β - 1 ≤ body.length)
    (body_divisible : β - 1 ∣ body.length)
    (halts : TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b])) :
    (mortalityProblem β body).Mortal := by
  rw [mortalityProblem_mortal_iff]
  exact mortal_of_tagHaltsFrom β body β_large body_long body_divisible halts

end MatrixMortality.DecimalSetterInteger
