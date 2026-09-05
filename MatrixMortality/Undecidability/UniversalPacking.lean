import MatrixMortality.Undecidability.PackingProblems
import MatrixMortality.Undecidability.UniversalMortality35

/-!
# Packed universal mortality endpoints
-/

namespace MatrixMortality.Undecidability.UniversalNeary

/-- Certified composition of universal halting with `M₃(5) ≤ M₆(3)`. -/
noncomputable def mortality63Reduction :
    PrimrecReduction CodeHalts (MortalityProblem.Mortal (d := 6) (k := 3)) where
  emit index := mortality63Pack (mortality35Reduction.emit index)
  emit_primrec := mortality63Pack_primrec.comp mortality35Reduction.emit_primrec
  target_iff_source index := by
    rw [mortality63Pack_mortal_iff, mortality35Reduction.target_iff_source]

/-- Halting at input zero many-one reduces to mortality of three `6 × 6` integer matrices. -/
theorem codeHalts_reduces_mortality63 :
    CodeHalts ≤₀ MortalityProblem.Mortal (d := 6) (k := 3) :=
  mortality63Reduction.toManyOne

/-- Mortality of three `6 × 6` integer matrices is not computable. -/
theorem mortality63_not_computable :
    ¬ComputablePred (MortalityProblem.Mortal (d := 6) (k := 3)) :=
  mortality63Reduction.target_not_computable codeHalts_not_computable

/-- Certified composition of universal halting with `M₃(5) ≤ M₁₂(2)`. -/
noncomputable def mortality122Reduction :
    PrimrecReduction CodeHalts (MortalityProblem.Mortal (d := 12) (k := 2)) where
  emit index := mortality122Pack (mortality35Reduction.emit index)
  emit_primrec := mortality122Pack_primrec.comp mortality35Reduction.emit_primrec
  target_iff_source index := by
    rw [mortality122Pack_mortal_iff, mortality35Reduction.target_iff_source]

/-- Halting at input zero many-one reduces to mortality of two `12 × 12` integer matrices. -/
theorem codeHalts_reduces_mortality122 :
    CodeHalts ≤₀ MortalityProblem.Mortal (d := 12) (k := 2) :=
  mortality122Reduction.toManyOne

/-- Mortality of two `12 × 12` integer matrices is not computable. -/
theorem mortality122_not_computable :
    ¬ComputablePred (MortalityProblem.Mortal (d := 12) (k := 2)) :=
  mortality122Reduction.target_not_computable codeHalts_not_computable

end MatrixMortality.Undecidability.UniversalNeary
