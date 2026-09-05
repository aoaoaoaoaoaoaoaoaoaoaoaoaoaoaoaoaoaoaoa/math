import MatrixMortality.Undecidability.UniversalMortality92

/-!
# The publication contract for M₉(2)

These probes pin the endpoint's type, independently of its implementation.
-/

namespace Verification

open MatrixMortality.Undecidability

noncomputable example :
    PrimrecReduction CodeHalts (MortalityProblem.Mortal (d := 9) (k := 2)) :=
  UniversalNeary.mortality92Reduction

example : CodeHalts ≤₀ MortalityProblem.Mortal (d := 9) (k := 2) :=
  UniversalNeary.codeHalts_reduces_mortality92

example : ¬ComputablePred (MortalityProblem.Mortal (d := 9) (k := 2)) :=
  UniversalNeary.mortality92_not_computable

end Verification
