import MatrixMortality.Undecidability.UniversalMortality44

/-!
# The publication contract for M4(4)
-/

namespace Verification

open MatrixMortality.Undecidability

noncomputable example :
    PrimrecReduction CodeHalts (MortalityProblem.Mortal (d := 4) (k := 4)) :=
  UniversalNeary.mortality44Reduction

example : CodeHalts ≤₀ MortalityProblem.Mortal (d := 4) (k := 4) :=
  UniversalNeary.codeHalts_reduces_mortality44

example : ¬ComputablePred (MortalityProblem.Mortal (d := 4) (k := 4)) :=
  UniversalNeary.mortality44_not_computable

end Verification
