import Mathlib.Computability.Halting
import Mathlib.Computability.Reduce
import MatrixMortality.Computability
import MatrixMortality.MatrixSemigroup
import MatrixMortality.WordMorphism

/-!
# Encoded decision problems

This file fixes the computability-theoretic boundary of the development. The source is mathlib's
universal partially recursive evaluator at input zero. The targets are concrete binary
four-generator GPCP instances, finite integer-matrix mortality families, and finite integer
scalar-zero systems. Simulation compilers belong in later files; no external undecidability
premise is introduced here.
-/

namespace MatrixMortality
namespace Undecidability

open scoped Matrix

/-- The noncomputable source predicate supplied by mathlib's halting theorem. -/
def CodeHalts (code : Nat.Partrec.Code) : Prop := (code.eval 0).Dom

theorem codeHalts_not_computable : ¬ComputablePred CodeHalts :=
  ComputablePred.halting_problem 0

/-- A binary GPCP instance with four source letters and independent fixed boundaries. -/
structure BinaryGPCP4 where
  /-- Upper source morphism. -/
  upper : Fin 4 → List Bool
  /-- Lower source morphism. -/
  lower : Fin 4 → List Bool
  /-- Fixed upper-left boundary. -/
  upperLeft : List Bool
  /-- Fixed upper-right boundary. -/
  upperRight : List Bool
  /-- Fixed lower-left boundary. -/
  lowerLeft : List Bool
  /-- Fixed lower-right boundary. -/
  lowerRight : List Bool

private abbrev BinaryGPCP4Code :=
  (Fin 4 → List Bool) ×
    (Fin 4 → List Bool) ×
      List Bool × List Bool × List Bool × List Bool

private def binaryGPCP4Equiv : BinaryGPCP4 ≃ BinaryGPCP4Code where
  toFun problem :=
    (problem.upper, problem.lower, problem.upperLeft, problem.upperRight,
      problem.lowerLeft, problem.lowerRight)
  invFun code :=
    { upper := code.1
      lower := code.2.1
      upperLeft := code.2.2.1
      upperRight := code.2.2.2.1
      lowerLeft := code.2.2.2.2.1
      lowerRight := code.2.2.2.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable BinaryGPCP4 :=
  Primcodable.ofEquiv BinaryGPCP4Code binaryGPCP4Equiv

/-- Solvability under the standard GPCP convention, which permits an empty witness. -/
def BinaryGPCP4.Solvable (problem : BinaryGPCP4) : Prop :=
  ∃ word : List (Fin 4),
    problem.upperLeft ++ spell problem.upper word ++ problem.upperRight =
      problem.lowerLeft ++ spell problem.lower word ++ problem.lowerRight

namespace BinaryGPCP4

/-- Assemble a primitive-recursive family of encoded four-letter GPCP instances. -/
theorem primrec_mk {α : Type*} [Primcodable α]
    (upper lower : α → Fin 4 → List Bool)
    (upperLeft upperRight lowerLeft lowerRight : α → List Bool)
    (upperRec : Primrec upper) (lowerRec : Primrec lower)
    (upperLeftRec : Primrec upperLeft) (upperRightRec : Primrec upperRight)
    (lowerLeftRec : Primrec lowerLeft) (lowerRightRec : Primrec lowerRight) :
    Primrec fun input =>
      ({ upper := upper input
         lower := lower input
         upperLeft := upperLeft input
         upperRight := upperRight input
         lowerLeft := lowerLeft input
         lowerRight := lowerRight input } : BinaryGPCP4) := by
  apply (Primrec.of_equiv_iff binaryGPCP4Equiv).mp
  exact
    Primrec.pair upperRec <|
      Primrec.pair lowerRec <|
        Primrec.pair upperLeftRec <|
          Primrec.pair upperRightRec <|
            Primrec.pair lowerLeftRec lowerRightRec

end BinaryGPCP4

/-- A finite integer linear representation with distinguished row and column. -/
structure ScalarZeroProblem (d k : Nat) where
  /-- The labelled square matrices. -/
  matrix : Fin k → Fin d → Fin d → ℤ
  /-- The left boundary row. -/
  row : Fin d → ℤ
  /-- The right boundary column. -/
  column : Fin d → ℤ

private abbrev ScalarZeroProblemCode (d k : Nat) :=
  (Fin k → Fin d → Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)

private def scalarZeroProblemEquiv (d k : Nat) :
    ScalarZeroProblem d k ≃ ScalarZeroProblemCode d k where
  toFun problem := (problem.matrix, problem.row, problem.column)
  invFun code := ⟨code.1, code.2.1, code.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (d k : Nat) : Primcodable (ScalarZeroProblem d k) :=
  Primcodable.ofEquiv (ScalarZeroProblemCode d k) (scalarZeroProblemEquiv d k)

namespace ScalarZeroProblem

/-- Assemble a primitive-recursive family of encoded scalar-zero instances from its entries. -/
theorem primrec_mk {α : Type*} [Primcodable α] {d k : Nat}
    (matrix : α → Fin k → Fin d → Fin d → ℤ)
    (row column : α → Fin d → ℤ)
    (matrixRec : ∀ label row column,
      Primrec fun input => matrix input label row column)
    (rowRec : ∀ coordinate, Primrec fun input => row input coordinate)
    (columnRec : ∀ coordinate, Primrec fun input => column input coordinate) :
    Primrec fun input =>
      ({ matrix := matrix input
         row := row input
         column := column input } : ScalarZeroProblem d k) := by
  apply (Primrec.of_equiv_iff (scalarZeroProblemEquiv d k)).mp
  exact
    Primrec.pair
      (MatrixMortality.Primrec.fin_function fun label =>
        MatrixMortality.Primrec.fin_function fun row =>
          MatrixMortality.Primrec.fin_function fun column =>
            matrixRec label row column)
      (Primrec.pair
        (MatrixMortality.Primrec.fin_function rowRec)
        (MatrixMortality.Primrec.fin_function columnRec))

/-- The scalar coefficient assigned to a generator word. -/
def coefficient {d k : Nat} (problem : ScalarZeroProblem d k) (word : List (Fin k)) : ℤ :=
  problem.row ⬝ᵥ wordProduct problem.matrix word *ᵥ problem.column

/-- Nonempty-word scalar zero reachability. -/
def HasZero {d k : Nat} (problem : ScalarZeroProblem d k) : Prop :=
  WordSeries.HasNonemptyZero problem.coefficient

/-- Scalar zero reachability under the free-monoid convention. -/
def HasZeroStar {d k : Nat} (problem : ScalarZeroProblem d k) : Prop :=
  WordSeries.HasZero problem.coefficient

theorem hasZero_iff_hasZeroStar_of_empty_ne {d k : Nat} (problem : ScalarZeroProblem d k)
    (empty_ne : problem.coefficient [] ≠ 0) :
    problem.HasZero ↔ problem.HasZeroStar :=
  WordSeries.hasNonemptyZero_iff_hasZero_of_nil_ne problem.coefficient empty_ne

end ScalarZeroProblem

/-- Two labelled `6 × 6` integer matrices with scalar boundaries. -/
abbrev ScalarZero62 := ScalarZeroProblem 6 2

/-- `k` labelled integer matrices of dimension `d`, represented transparently for
`Primcodable`. -/
abbrev MortalityProblem (d k : Nat) := Fin k → Fin d → Fin d → ℤ

namespace MortalityProblem

/-- Assemble a primitive-recursive finite matrix family from its entries. -/
theorem primrec {α : Type*} [Primcodable α] {d k : Nat}
    (problem : α → MortalityProblem d k)
    (entries : ∀ label row column,
      Primrec fun input => problem input label row column) :
    Primrec problem :=
  MatrixMortality.Primrec.fin_function fun label =>
    MatrixMortality.Primrec.fin_function fun row =>
      MatrixMortality.Primrec.fin_function fun column =>
        entries label row column

/-- Interpret the transparent encoding as a family with matrix multiplication. -/
def matrix {d k : Nat} (problem : MortalityProblem d k) (label : Fin k) :
    Matrix (Fin d) (Fin d) ℤ :=
  problem label

/-- Mortality requires a nonempty generator word. -/
def Mortal {d k : Nat} (problem : MortalityProblem d k) : Prop :=
  IsMortal problem.matrix

end MortalityProblem

/-- Five labelled `3 × 3` integer matrices. -/
abbrev Mortality35 := MortalityProblem 3 5

/-- Four labelled `4 × 4` integer matrices. -/
abbrev Mortality44 := MortalityProblem 4 4

/-- Two labelled `10 × 10` integer matrices. -/
abbrev Mortality102 := MortalityProblem 10 2

/-- A primitive-recursive emitter together with its exact predicate equivalence. -/
structure PrimrecReduction {Source Target : Type*} [Primcodable Source] [Primcodable Target]
    (source : Source → Prop) (target : Target → Prop) where
  /-- The emitted target instance. -/
  emit : Source → Target
  /-- The emitter is primitive recursive. -/
  emit_primrec : Primrec emit
  /-- Emission preserves and reflects the decision predicate. -/
  target_iff_source : ∀ input, target (emit input) ↔ source input

namespace PrimrecReduction

variable {Source Target : Type*} [Primcodable Source] [Primcodable Target]
  {source : Source → Prop} {target : Target → Prop}

/-- Forget the certificate structure to obtain mathlib's many-one reduction. -/
theorem toManyOne (reduction : PrimrecReduction source target) : source ≤₀ target :=
  ⟨reduction.emit, reduction.emit_primrec.to_comp,
    fun input => (reduction.target_iff_source input).symm⟩

/-- Undecidability crosses a certified primitive-recursive reduction. -/
theorem target_not_computable (reduction : PrimrecReduction source target)
    (source_not_computable : ¬ComputablePred source) :
    ¬ComputablePred target := by
  intro target_computable
  exact source_not_computable
    (ComputablePred.computable_of_manyOneReducible reduction.toManyOne target_computable)

end PrimrecReduction

theorem not_computable_of_codeHalts_reduction {Target : Type*} [Primcodable Target]
    {target : Target → Prop} (reduction : CodeHalts ≤₀ target) :
    ¬ComputablePred target := by
  intro target_computable
  exact codeHalts_not_computable
    (ComputablePred.computable_of_manyOneReducible reduction target_computable)

theorem gpcp4_not_computable_of_reduction
    (reduction : CodeHalts ≤₀ BinaryGPCP4.Solvable) :
    ¬ComputablePred BinaryGPCP4.Solvable :=
  not_computable_of_codeHalts_reduction reduction

theorem mortality_not_computable_of_reduction {d k : Nat}
    (reduction : CodeHalts ≤₀ MortalityProblem.Mortal (d := d) (k := k)) :
    ¬ComputablePred (MortalityProblem.Mortal (d := d) (k := k)) :=
  not_computable_of_codeHalts_reduction reduction

theorem scalarZero_not_computable_of_reduction {d k : Nat}
    (reduction : CodeHalts ≤₀ ScalarZeroProblem.HasZero (d := d) (k := k)) :
    ¬ComputablePred (ScalarZeroProblem.HasZero (d := d) (k := k)) :=
  not_computable_of_codeHalts_reduction reduction

theorem mortality35_not_computable_of_reduction
    (reduction : CodeHalts ≤₀ MortalityProblem.Mortal (d := 3) (k := 5)) :
    ¬ComputablePred (MortalityProblem.Mortal (d := 3) (k := 5)) :=
  mortality_not_computable_of_reduction reduction

theorem mortality44_not_computable_of_reduction
    (reduction : CodeHalts ≤₀ MortalityProblem.Mortal (d := 4) (k := 4)) :
    ¬ComputablePred (MortalityProblem.Mortal (d := 4) (k := 4)) :=
  mortality_not_computable_of_reduction reduction

end Undecidability
end MatrixMortality
