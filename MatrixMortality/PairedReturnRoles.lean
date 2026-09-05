import MatrixMortality.ChangedSeparatorRealization

/-!
# Paired roles shared by the return realizations

The data matrices, absorbed boundary, and four-role return alphabet are independent of the
physical chart. Their coordinate certificates are shared by the eight- and nine-state proofs.
-/

namespace MatrixMortality.ChangedSeparatorRealization

open scoped Matrix

/-- The chart's closed `b` role is the paired Neary generator. -/
theorem chainDataB_eq_pairedDataMatrix (β : Nat) (body : List TagLetter) :
    chainDataB (widthScale β) = pairedDataMatrix ℚ β body .b := by
  have upper_b :
      (ternaryCode (nearyUpper β (.rule .b)) : ℚ) =
        (15 * (3 : ℚ) ^ β + 1) / 2 := by
    simpa [nearyUpper, nearySideUpperB] using nearySideUpperB_eq β
  have upper_b_scale :
      ((3 : ℚ) ^ (nearyUpper β (.rule .b)).length) = 9 * (3 : ℚ) ^ β := by
    simpa [nearyUpper, nearySideUpperBScale] using nearySideUpperBScale_eq β
  have lower_b_scale :
      ((3 : ℚ) ^ (nearyLower β body (.rule .b)).length) = 27 := by
    norm_num [nearyLower]
  have erase_scale :
      ((3 : ℚ) ^ (nearyLower β body (.erase .b)).length) = 3 := by
    norm_num [nearyLower]
  rw [pairedDataMatrix_eq_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chainDataB, widthScale, upper_b, upper_b_scale, lower_b_scale,
      erase_scale]

/-- The chart's closed `c` role is the paired Neary generator. -/
theorem chainDataC_eq_pairedDataMatrix (β : Nat) (body : List TagLetter) :
    chainDataC (ChangedSeparatorTail.lowerCCode β body)
        (ChangedSeparatorTail.lowerCScale β body) =
      pairedDataMatrix ℚ β body .c := by
  rw [pairedDataMatrix_eq_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chainDataC, ChangedSeparatorTail.lowerCCode,
      ChangedSeparatorTail.lowerCScale, nearySideLowerC,
      nearySideLowerCScale, nearyUpper, nearyLower, tagCode, ternaryDigit]

/-- The realized tail column is the paired boundary after absorbing one trailing toggle. -/
theorem chainTailColumn_eq_pairedTrailingToggleColumn (β : Nat) :
    chainTailColumn (widthScale β) = pairedTrailingToggleColumn ℚ β := by
  rw [pairedTrailingToggleColumn, pairedColumn]
  change
    chainTailColumn (widthScale β) =
      pairedToggleMatrix ℚ *ᵥ phaseVector ℚ .rule (nearySideColumn β)
  rw [nearySideColumn_eq_native]
  funext i
  fin_cases i <;>
    simp [chainTailColumn, widthScale, pairedToggleMatrix_eq_explicit,
      nearySideNativeColumn, nearySideMarkerValue_eq, nearySideMarkerScale_eq,
      phaseVector, controllerVector, pairControllerEquiv,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Finite paired role represented by one return time. -/
def returnLabel : Nat → Option PairedControl
  | 0 => some .toggle
  | 1 => some (.data .b)
  | 2 => some (.data .c)
  | Nat.succ (Nat.succ (Nat.succ _)) => none

/-- Canonical return time realizing each finite paired role. -/
def returnIndex : Option PairedControl → Nat
  | none => 3
  | some .toggle => 0
  | some (.data .b) => 1
  | some (.data .c) => 2

theorem returnLabel_returnIndex (label : Option PairedControl) :
    returnLabel (returnIndex label) = label := by
  cases label with
  | none => rfl
  | some control =>
      cases control with
      | toggle => rfl
      | data letter => cases letter <;> rfl

end MatrixMortality.ChangedSeparatorRealization
