import MatrixMortality.Undecidability.BinaryProblems
import MatrixMortality.Undecidability.ChangedSeparatorProblems
import MatrixMortality.Undecidability.NearyProblems
import MatrixMortality.Undecidability.NearySource
import MatrixMortality.Undecidability.PairedProblems
import MatrixMortality.Undecidability.PackingProblems
import MatrixMortality.Undecidability.PrefixProblems
import MatrixMortality.Undecidability.UniversalTwoTag

/-!
# A fixed universal Neary source

The fixed universal two-tag system is compiled through Cook's cyclic-tag construction and
Neary's restricted binary-tag construction. Protected execution gives the forward implication.
The cyclic firing reflection theorem and Neary's arbitrary-execution converse give the reverse
implication.
-/

namespace MatrixMortality
namespace Undecidability
namespace UniversalNeary

open scoped Classical

/-- Cook–Neary compilation of the verified universal two-tag source. -/
noncomputable def source : RestrictedTagSource Nat.Partrec.Code CodeHalts :=
  NearyCompiler.compile UniversalTwoTag.source

/-- The emitted restricted binary-tag instance halts exactly for accepted source codes. -/
theorem tagHaltsFrom_iff_codeHalts (index : Nat.Partrec.Code) :
    TagHaltsFrom source.width (tagOutput (source.body index))
        ((source.body index).drop (source.width - 1) ++ [.b]) ↔
      CodeHalts index :=
  source.halts_iff index

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

/-- Certified compilation from universal halting to two-matrix nine-dimensional mortality. -/
noncomputable def mortality92Reduction :
    PrimrecReduction CodeHalts (MortalityProblem.Mortal (d := 9) (k := 2)) where
  emit index := nearyMortality92 source.width (source.body index)
  emit_primrec := (nearyMortality92_primrec source.width).comp source.body_primrec
  target_iff_source index := by
    rw [nearyMortality92_mortal_iff_tagHaltsFrom source.width (source.body index)
      source.width_large (source.body_long index) (source.body_divisible index)
      (source.b_mem index),
      tagHaltsFrom_iff_codeHalts]

/-- The concrete two-matrix nine-dimensional mortality instance emitted for one source program. -/
noncomputable def mortality92Instance : Nat.Partrec.Code → Mortality92 :=
  mortality92Reduction.emit

/-- The nine-dimensional mortality instance family is primitive recursive. -/
theorem mortality92Instance_primrec : Primrec mortality92Instance :=
  mortality92Reduction.emit_primrec

theorem mortality92Instance_mortal_iff_codeHalts (index : Nat.Partrec.Code) :
    (mortality92Instance index).Mortal ↔ CodeHalts index :=
  mortality92Reduction.target_iff_source index

/-- Halting at input zero many-one reduces to mortality of two `9 × 9` integer matrices. -/
theorem codeHalts_reduces_mortality92 :
    CodeHalts ≤₀ MortalityProblem.Mortal (d := 9) (k := 2) :=
  mortality92Reduction.toManyOne

/-- Mortality of two `9 × 9` integer matrices is not computable. -/
theorem mortality92_not_computable :
    ¬ComputablePred (MortalityProblem.Mortal (d := 9) (k := 2)) :=
  mortality92Reduction.target_not_computable codeHalts_not_computable

/-- Certified compilation from universal halting to two-matrix mortality in dimension
`9 + extra`. -/
noncomputable def mortality9PlusReduction (extra : Nat) :
    PrimrecReduction CodeHalts (MortalityProblem.Mortal (d := 9 + extra) (k := 2)) where
  emit index := nearyMortality9Plus extra source.width (source.body index)
  emit_primrec :=
    (nearyMortality9Plus_primrec extra source.width).comp source.body_primrec
  target_iff_source index := by
    rw [nearyMortality9Plus_mortal_iff_tagHaltsFrom extra source.width
      (source.body index) source.width_large (source.body_long index)
      (source.body_divisible index) (source.b_mem index),
      tagHaltsFrom_iff_codeHalts]

/-- Halting at input zero many-one reduces to two-matrix mortality in every dimension at least
nine. -/
theorem codeHalts_reduces_mortality9Plus (extra : Nat) :
    CodeHalts ≤₀ MortalityProblem.Mortal (d := 9 + extra) (k := 2) :=
  (mortality9PlusReduction extra).toManyOne

/-- Mortality of two integer matrices is not computable in every dimension at least nine. -/
theorem mortality9Plus_not_computable (extra : Nat) :
    ¬ComputablePred (MortalityProblem.Mortal (d := 9 + extra) (k := 2)) :=
  (mortality9PlusReduction extra).target_not_computable codeHalts_not_computable

end UniversalNeary
end Undecidability
end MatrixMortality
