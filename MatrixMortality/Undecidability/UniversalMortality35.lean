import MatrixMortality.Undecidability.NearyProblems
import MatrixMortality.Undecidability.UniversalNearySource

/-!
# Universal GPCP and M₃(5) endpoints
-/

namespace MatrixMortality.Undecidability.UniversalNeary

/-- Certified compilation from universal halting to four-letter binary GPCP. -/
noncomputable def gpcp4Reduction :
    PrimrecReduction CodeHalts BinaryGPCP4.Solvable where
  emit index := nearyGPCP4 source.width (source.body index)
  emit_primrec := (nearyGPCP4_primrec source.width).comp source.body_primrec
  target_iff_source index := by
    rw [nearyGPCP4_solvable_iff_tagHaltsFrom source.width (source.body index)
      source.width_large (source.body_long index) (source.body_divisible index),
      tagHaltsFrom_iff_codeHalts]

/-- The concrete four-letter GPCP instance emitted for one source program. -/
noncomputable def gpcpInstance : Nat.Partrec.Code → BinaryGPCP4 :=
  gpcp4Reduction.emit

/-- The GPCP instance family is primitive recursive. -/
theorem gpcpInstance_primrec : Primrec gpcpInstance :=
  gpcp4Reduction.emit_primrec

theorem gpcpInstance_solvable_iff_codeHalts (index : Nat.Partrec.Code) :
    (gpcpInstance index).Solvable ↔ CodeHalts index :=
  gpcp4Reduction.target_iff_source index

/-- Halting at input zero many-one reduces to four-letter binary GPCP. -/
theorem codeHalts_reduces_gpcp4 :
    CodeHalts ≤₀ BinaryGPCP4.Solvable :=
  gpcp4Reduction.toManyOne

/-- Four-letter binary GPCP solvability is not computable. -/
theorem gpcp4_not_computable : ¬ComputablePred BinaryGPCP4.Solvable :=
  gpcp4Reduction.target_not_computable codeHalts_not_computable

/-- Certified compilation from universal halting to five-matrix three-state mortality. -/
noncomputable def mortality35Reduction :
    PrimrecReduction CodeHalts (MortalityProblem.Mortal (d := 3) (k := 5)) where
  emit index := nearyMortality35 source.width (source.body index)
  emit_primrec := (nearyMortality35_primrec source.width).comp source.body_primrec
  target_iff_source index := by
    rw [nearyMortality35_mortal_iff_tagHaltsFrom source.width (source.body index)
      source.width_large (source.body_long index) (source.body_divisible index),
      tagHaltsFrom_iff_codeHalts]

/-- The concrete five-matrix mortality instance emitted for one source program. -/
noncomputable def mortalityInstance : Nat.Partrec.Code → Mortality35 :=
  mortality35Reduction.emit

/-- The mortality instance family is primitive recursive. -/
theorem mortalityInstance_primrec : Primrec mortalityInstance :=
  mortality35Reduction.emit_primrec

theorem mortalityInstance_mortal_iff_codeHalts (index : Nat.Partrec.Code) :
    (mortalityInstance index).Mortal ↔ CodeHalts index :=
  mortality35Reduction.target_iff_source index

/-- Halting at input zero many-one reduces to mortality of five `3 × 3` integer matrices. -/
theorem codeHalts_reduces_mortality35 :
    CodeHalts ≤₀ MortalityProblem.Mortal (d := 3) (k := 5) :=
  mortality35Reduction.toManyOne

/-- Mortality of five `3 × 3` integer matrices is not computable. -/
theorem mortality35_not_computable :
    ¬ComputablePred (MortalityProblem.Mortal (d := 3) (k := 5)) :=
  mortality35Reduction.target_not_computable codeHalts_not_computable

end MatrixMortality.Undecidability.UniversalNeary
