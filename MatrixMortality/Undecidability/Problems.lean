import Mathlib.Computability.Halting
import Mathlib.Computability.Reduce
import MatrixMortality.NearyEncoding

/-!
# Encoded decision problems

This file fixes the computability-theoretic boundary of the development.  The source is
mathlib's universal partially recursive evaluator at input zero.  The targets are concrete binary
four-generator GPCP instances, five labelled `3 × 3` integer matrices, and four labelled `4 × 4`
integer matrices. Simulation compilers belong in later files; no external undecidability premise
is introduced here.
-/

namespace MatrixMortality
namespace Undecidability

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

/-- Five labelled `3 × 3` integer matrices, represented transparently for `Primcodable`. -/
abbrev Mortality35 := Fin 5 → Fin 3 → Fin 3 → ℤ

/-- Four labelled `4 × 4` integer matrices, represented transparently for `Primcodable`. -/
abbrev Mortality44 := Fin 4 → Fin 4 → Fin 4 → ℤ

/-- Interpret the transparent encoding as a family with matrix multiplication. -/
def Mortality35.matrix (problem : Mortality35) (label : Fin 5) :
    Matrix (Fin 3) (Fin 3) ℤ :=
  problem label

/-- Mortality requires a nonempty generator word. -/
def Mortality35.Mortal (problem : Mortality35) : Prop :=
  IsMortal problem.matrix

/-- Interpret the transparent `M₄(4)` encoding as a matrix family. -/
def Mortality44.matrix (problem : Mortality44) (label : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℤ :=
  problem label

/-- Mortality for four labelled `4 × 4` matrices requires a nonempty generator word. -/
def Mortality44.Mortal (problem : Mortality44) : Prop :=
  IsMortal problem.matrix

theorem gpcp4_not_computable_of_reduction
    (reduction : CodeHalts ≤₀ BinaryGPCP4.Solvable) :
    ¬ComputablePred BinaryGPCP4.Solvable := by
  intro decidableTarget
  exact codeHalts_not_computable
    (ComputablePred.computable_of_manyOneReducible reduction decidableTarget)

theorem mortality35_not_computable_of_reduction
    (reduction : CodeHalts ≤₀ Mortality35.Mortal) :
    ¬ComputablePred Mortality35.Mortal := by
  intro decidableTarget
  exact codeHalts_not_computable
    (ComputablePred.computable_of_manyOneReducible reduction decidableTarget)

theorem mortality44_not_computable_of_reduction
    (reduction : CodeHalts ≤₀ Mortality44.Mortal) :
    ¬ComputablePred Mortality44.Mortal := by
  intro decidableTarget
  exact codeHalts_not_computable
    (ComputablePred.computable_of_manyOneReducible reduction decidableTarget)

end Undecidability
end MatrixMortality
