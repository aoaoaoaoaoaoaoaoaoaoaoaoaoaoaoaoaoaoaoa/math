import MatrixMortality.Undecidability.NearyProblems
import MatrixMortality.Undecidability.NearySource
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

/-- The concrete four-letter GPCP instance emitted for one source program. -/
noncomputable def gpcpInstance (index : Nat.Partrec.Code) : BinaryGPCP4 :=
  nearyGPCP4 source.width (source.body index)

/-- The GPCP instance family is primitive recursive. -/
theorem gpcpInstance_primrec : Primrec gpcpInstance :=
  (nearyGPCP4_primrec source.width).comp source.body_primrec

theorem gpcpInstance_solvable_iff_codeHalts (index : Nat.Partrec.Code) :
    (gpcpInstance index).Solvable ↔ CodeHalts index := by
  rw [gpcpInstance,
    nearyGPCP4_solvable_iff_tagHaltsFrom source.width (source.body index)
      source.width_large (source.body_long index) (source.body_divisible index),
    tagHaltsFrom_iff_codeHalts]

/-- Halting at input zero many-one reduces to four-letter binary GPCP. -/
theorem codeHalts_reduces_gpcp4 :
    CodeHalts ≤₀ BinaryGPCP4.Solvable :=
  ⟨gpcpInstance, gpcpInstance_primrec.to_comp,
    fun index => (gpcpInstance_solvable_iff_codeHalts index).symm⟩

/-- Four-letter binary GPCP solvability is not computable. -/
theorem gpcp4_not_computable : ¬ComputablePred BinaryGPCP4.Solvable :=
  gpcp4_not_computable_of_reduction codeHalts_reduces_gpcp4

/-- The concrete five-matrix mortality instance emitted for one source program. -/
noncomputable def mortalityInstance (index : Nat.Partrec.Code) : Mortality35 :=
  nearyMortality35 source.width (source.body index)

/-- The mortality instance family is primitive recursive. -/
theorem mortalityInstance_primrec : Primrec mortalityInstance :=
  (nearyMortality35_primrec source.width).comp source.body_primrec

theorem mortalityInstance_mortal_iff_codeHalts (index : Nat.Partrec.Code) :
    (mortalityInstance index).Mortal ↔ CodeHalts index := by
  rw [mortalityInstance,
    nearyMortality35_mortal_iff_tagHaltsFrom source.width (source.body index)
      source.width_large (source.body_long index) (source.body_divisible index),
    tagHaltsFrom_iff_codeHalts]

/-- Halting at input zero many-one reduces to mortality of five `3 × 3` integer matrices. -/
theorem codeHalts_reduces_mortality35 :
    CodeHalts ≤₀ MortalityProblem.Mortal (d := 3) (k := 5) :=
  ⟨mortalityInstance, mortalityInstance_primrec.to_comp,
    fun index => (mortalityInstance_mortal_iff_codeHalts index).symm⟩

/-- Mortality of five `3 × 3` integer matrices is not computable. -/
theorem mortality35_not_computable :
    ¬ComputablePred (MortalityProblem.Mortal (d := 3) (k := 5)) :=
  mortality35_not_computable_of_reduction codeHalts_reduces_mortality35

end UniversalNeary
end Undecidability
end MatrixMortality
