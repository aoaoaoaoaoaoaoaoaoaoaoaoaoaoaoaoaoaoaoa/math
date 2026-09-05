import MatrixMortality.Undecidability.PairedProblems
import MatrixMortality.Undecidability.UniversalNearySource

/-!
# The universal M₄(4) endpoint
-/

namespace MatrixMortality.Undecidability.UniversalNeary

/-- Certified compilation from universal halting to four-matrix four-state mortality. -/
noncomputable def mortality44Reduction :
    PrimrecReduction CodeHalts (MortalityProblem.Mortal (d := 4) (k := 4)) where
  emit index := nearyMortality44 source.width (source.body index)
  emit_primrec := (nearyMortality44_primrec source.width).comp source.body_primrec
  target_iff_source index := by
    rw [nearyMortality44_mortal_iff_tagHaltsFrom source.width (source.body index)
      source.width_large (source.body_long index) (source.body_divisible index),
      tagHaltsFrom_iff_codeHalts]

/-- Halting at input zero many-one reduces to mortality of four `4 × 4` integer matrices. -/
theorem codeHalts_reduces_mortality44 :
    CodeHalts ≤₀ MortalityProblem.Mortal (d := 4) (k := 4) :=
  mortality44Reduction.toManyOne

/-- Mortality of four `4 × 4` integer matrices is not computable. -/
theorem mortality44_not_computable :
    ¬ComputablePred (MortalityProblem.Mortal (d := 4) (k := 4)) :=
  mortality44Reduction.target_not_computable codeHalts_not_computable

end MatrixMortality.Undecidability.UniversalNeary
