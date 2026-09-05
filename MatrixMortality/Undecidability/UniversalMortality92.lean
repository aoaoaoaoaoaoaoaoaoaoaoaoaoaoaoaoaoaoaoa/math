import MatrixMortality.Undecidability.ChangedSeparatorProblems
import MatrixMortality.Undecidability.UniversalNearySource

/-!
# The universal M₉(2) endpoint
-/

namespace MatrixMortality.Undecidability.UniversalNeary

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

end MatrixMortality.Undecidability.UniversalNeary
