import MatrixMortality.Undecidability.UniversalMortality35

/-!
# The publication contract for M3(5)
-/

namespace Verification

open MatrixMortality.Undecidability

noncomputable example :
    PrimrecReduction CodeHalts (MortalityProblem.Mortal (d := 3) (k := 5)) :=
  UniversalNeary.mortality35Reduction

example : CodeHalts ≤₀ MortalityProblem.Mortal (d := 3) (k := 5) :=
  UniversalNeary.codeHalts_reduces_mortality35

example : ¬ComputablePred (MortalityProblem.Mortal (d := 3) (k := 5)) :=
  UniversalNeary.mortality35_not_computable

end Verification
