import MatrixMortality.Undecidability.AsymmetricSeparatorProblems
import MatrixMortality.Undecidability.MortalityPadding
import MatrixMortality.Undecidability.UniversalNearySource
import MatrixMortality.AsymmetricSeparatorSource

/-!
# The universal M₈(2) endpoint

The fixed universal source satisfies the asymmetric separator's `bcb` prefix condition.
Composition gives a primitive-recursive reduction to two integer matrices of dimension eight.
-/

namespace MatrixMortality.Undecidability.UniversalNeary

/-- The actual universal compiler emits the prefix used by the wrong-phase exclusion. -/
theorem source_body_take_three (index : Nat.Partrec.Code) :
    (source.body index).take 3 = [.b, .c, .b] :=
  NearyCompiler.body_take_three UniversalTwoTag.source.cyclicSystem
    (UniversalTwoTag.source.cyclicInput index) UniversalTwoTag.source.haltPhase
    UniversalTwoTag.source.period_pos

/-- Certified primitive-recursive reduction from universal halting to standard M₈(2). -/
noncomputable def mortality82Reduction :
    PrimrecReduction CodeHalts (MortalityProblem.Mortal (d := 8) (k := 2)) where
  emit index := nearyMortality82 source.width (source.body index)
  emit_primrec := (nearyMortality82_primrec source.width).comp source.body_primrec
  target_iff_source index :=
    (nearyMortality82_mortal_iff_tagHaltsFrom source.width (source.body index)
      source.width_large (source.body_long index) (source.body_divisible index)
      (source_body_take_three index)).trans (tagHaltsFrom_iff_codeHalts index)

/-- The two concrete integer matrices emitted for one program code. -/
noncomputable def mortality82Instance : Nat.Partrec.Code → MortalityProblem 8 2 :=
  mortality82Reduction.emit

theorem mortality82Instance_primrec : Primrec mortality82Instance :=
  mortality82Reduction.emit_primrec

theorem mortality82Instance_mortal_iff_codeHalts (index : Nat.Partrec.Code) :
    (mortality82Instance index).Mortal ↔ CodeHalts index :=
  mortality82Reduction.target_iff_source index

/-- Halting at input zero many-one reduces to mortality of two `8 × 8` integer matrices. -/
theorem codeHalts_reduces_mortality82 :
    CodeHalts ≤₀ MortalityProblem.Mortal (d := 8) (k := 2) :=
  mortality82Reduction.toManyOne

/-- Mortality of two `8 × 8` integer matrices is undecidable. -/
theorem mortality82_not_computable :
    ¬ComputablePred (MortalityProblem.Mortal (d := 8) (k := 2)) :=
  mortality82Reduction.target_not_computable codeHalts_not_computable

/-- Dimension padding transports the same certified reduction to every larger dimension. -/
noncomputable def mortality8PlusReduction (extra : Nat) :
    PrimrecReduction CodeHalts (MortalityProblem.Mortal (d := 8 + extra) (k := 2)) where
  emit index := MortalityProblem.pad extra (mortality82Instance index)
  emit_primrec := (MortalityProblem.pad_primrec 8 2 extra).comp mortality82Instance_primrec
  target_iff_source index :=
    (MortalityProblem.pad_mortal_iff extra (mortality82Instance index)).trans
      (mortality82Instance_mortal_iff_codeHalts index)

theorem codeHalts_reduces_mortality8Plus (extra : Nat) :
    CodeHalts ≤₀ MortalityProblem.Mortal (d := 8 + extra) (k := 2) :=
  (mortality8PlusReduction extra).toManyOne

/-- Mortality of two integer matrices is undecidable in every dimension at least eight. -/
theorem mortality8Plus_not_computable (extra : Nat) :
    ¬ComputablePred (MortalityProblem.Mortal (d := 8 + extra) (k := 2)) :=
  (mortality8PlusReduction extra).target_not_computable codeHalts_not_computable

end MatrixMortality.Undecidability.UniversalNeary
