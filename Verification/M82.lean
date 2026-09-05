import MatrixMortality.Undecidability.UniversalMortality82

/-!
# The publication contract for M₈(2)

These probes independently pin the unrestricted integer endpoint and primitive-recursive map.
-/

namespace Verification

open MatrixMortality.Undecidability

noncomputable example :
    PrimrecReduction CodeHalts (MortalityProblem.Mortal (d := 8) (k := 2)) :=
  UniversalNeary.mortality82Reduction

example : CodeHalts ≤₀ MortalityProblem.Mortal (d := 8) (k := 2) :=
  UniversalNeary.codeHalts_reduces_mortality82

example : ¬ComputablePred (MortalityProblem.Mortal (d := 8) (k := 2)) :=
  UniversalNeary.mortality82_not_computable

example (extra : Nat) :
    ¬ComputablePred (MortalityProblem.Mortal (d := 8 + extra) (k := 2)) :=
  UniversalNeary.mortality8Plus_not_computable extra

end Verification
