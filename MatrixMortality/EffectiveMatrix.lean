import MatrixMortality.EffectiveRational
import MatrixMortality.RationalClearing

/-!
# Integer matrices from effective fractions

Each matrix receives one common nonzero denominator. The resulting integer family has
primitive-recursive entries and exactly the mortality predicate of its rational evaluation.
-/

namespace MatrixMortality.EffectiveMatrix

variable {α κ : Type*} [Primcodable α] {d : Nat}
  (fractions : κ → Square (Fin d) (EffectiveFraction α))

/-- Row-major common-denominator clearing for one matrix. -/
def clearing (label : κ) :
    ClearedFin (fun index : Fin (d * d) =>
      fractions label ((@finProdFinEquiv d d).symm index).1
        ((@finProdFinEquiv d d).symm index).2) :=
  clearFin _

/-- The integer family obtained by clearing each generator independently. -/
def integral (input : α) : κ → Square (Fin d) Int :=
  fun label row column =>
    ((clearing fractions label).entry (@finProdFinEquiv d d (row, column))).value input

/-- Rational semantics of the operation-only effective family. -/
def value (input : α) : κ → Square (Fin d) ℚ :=
  fun label row column => (fractions label row column).value input

theorem integral_entry_primrec (label : κ) (row column : Fin d) :
    Primrec fun input => integral fractions input label row column :=
  ((clearing fractions label).entry (@finProdFinEquiv d d (row, column))).value_primrec

/-- Each integer matrix is a nonzero rational multiple of its intended matrix. -/
theorem cast_integral (input : α) (label : κ) :
    castMatrix (integral fractions input label) =
      ((clearing fractions label).denominator.value input : ℚ) • value fractions input label := by
  ext row column
  change (((clearing fractions label).entry
    (@finProdFinEquiv d d (row, column))).value input : ℚ) = _
  rw [(clearing fractions label).cast_entry (@finProdFinEquiv d d (row, column)) input]
  simp [value]

/-- Clearing reflects mortality as well as preserving it, with no common scale across labels. -/
theorem integral_mortal_iff (input : α) :
    IsMortal (integral fractions input) ↔ IsMortal (value fractions input) := by
  have cast_family : castMatrix ∘ integral fractions input =
      fun label => ((clearing fractions label).denominator.value input : ℚ) •
        value fractions input label := by
    funext label
    exact cast_integral fractions input label
  have denominators_ne (label : κ) :
      ((clearing fractions label).denominator.value input : ℚ) ≠ 0 := by
    exact_mod_cast (clearing fractions label).denominator_ne_zero input
  calc
    IsMortal (integral fractions input) ↔ IsMortal (castMatrix ∘ integral fractions input) :=
      (isMortal_cast_iff _).symm
    _ ↔ IsMortal (value fractions input) := by
      rw [cast_family, isMortal_smulMatrix_iff _ denominators_ne]

end MatrixMortality.EffectiveMatrix
