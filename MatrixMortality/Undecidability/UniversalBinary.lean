import MatrixMortality.Undecidability.BinaryProblems
import MatrixMortality.Undecidability.PrefixProblems
import MatrixMortality.Undecidability.UniversalNearySource

/-!
# Universal binary compilation endpoints
-/

namespace MatrixMortality.Undecidability.UniversalNeary

/-- Certified compilation from universal halting to two-matrix six-state scalar zero. -/
noncomputable def scalarZero62Reduction :
    PrimrecReduction CodeHalts (ScalarZeroProblem.HasZero (d := 6) (k := 2)) where
  emit index := nearyScalarZero62 source.width (source.body index)
  emit_primrec := (nearyScalarZero62_primrec source.width).comp source.body_primrec
  target_iff_source index := by
    rw [nearyScalarZero62_hasZero_iff_tagHaltsFrom source.width (source.body index)
      source.width_large (source.body_long index) (source.body_divisible index),
      tagHaltsFrom_iff_codeHalts]

/-- Halting at input zero many-one reduces to scalar zero for two `6 × 6` integer matrices. -/
theorem codeHalts_reduces_scalarZero62 :
    CodeHalts ≤₀ ScalarZeroProblem.HasZero (d := 6) (k := 2) :=
  scalarZero62Reduction.toManyOne

/-- Scalar zero for two `6 × 6` integer matrices is not computable. -/
theorem scalarZero62_not_computable :
    ¬ComputablePred (ScalarZeroProblem.HasZero (d := 6) (k := 2)) :=
  scalarZero62Reduction.target_not_computable codeHalts_not_computable

/-- Certified compilation from universal halting to two-matrix ten-state mortality. -/
noncomputable def mortality102Reduction :
    PrimrecReduction CodeHalts (MortalityProblem.Mortal (d := 10) (k := 2)) where
  emit index := nearyMortality102 source.width (source.body index)
  emit_primrec := (nearyMortality102_primrec source.width).comp source.body_primrec
  target_iff_source index := by
    rw [nearyMortality102_mortal_iff_tagHaltsFrom source.width (source.body index)
      source.width_large (source.body_long index) (source.body_divisible index),
      tagHaltsFrom_iff_codeHalts]

/-- Halting at input zero many-one reduces to mortality of two `10 × 10` integer matrices. -/
theorem codeHalts_reduces_mortality102 :
    CodeHalts ≤₀ MortalityProblem.Mortal (d := 10) (k := 2) :=
  mortality102Reduction.toManyOne

/-- Mortality of two `10 × 10` integer matrices is not computable. -/
theorem mortality102_not_computable :
    ¬ComputablePred (MortalityProblem.Mortal (d := 10) (k := 2)) :=
  mortality102Reduction.target_not_computable codeHalts_not_computable

end MatrixMortality.Undecidability.UniversalNeary
