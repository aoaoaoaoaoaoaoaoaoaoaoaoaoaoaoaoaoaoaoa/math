import Mathlib.Computability.TMToPartrec

/-!
# A finite-state universal source machine

Mathlib proves both that `Nat.Partrec.Code.eval` is universal and that every partially recursive
function is evaluated by a verified four-stack `TM2` program.  This file composes those results
without choosing a program noncomputably: the universal interpreter remains under an existential
until a reduction proof fixes it once and for all.
-/

open Mathlib (Vector)
open Turing

namespace MatrixMortality.Undecidability

private def universalEval (v : Vector ℕ 2) : Part ℕ :=
  Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code v.head) v.tail.head

private theorem universalEval_partrec : Nat.Partrec' universalEval := by
  simpa [universalEval] using Nat.Partrec'.part_iff₂.mpr
    (Nat.Partrec.Code.eval_part.comp₂
      ((Computable.ofNat Nat.Partrec.Code).comp Computable.fst).to₂
      Computable.snd.to₂)

/-- A single `ToPartrec.Code` interprets every encoded `Nat.Partrec.Code`. -/
theorem exists_universalToPartrecCode :
    ∃ interpreter : ToPartrec.Code, ∀ source input,
      interpreter.eval [Encodable.encode source, input] =
        ((fun output => [output]) <$> Nat.Partrec.Code.eval source input) := by
  obtain ⟨interpreter, hinterpreter⟩ := ToPartrec.Code.exists_code universalEval_partrec
  refine ⟨interpreter, fun source input => ?_⟩
  have h := hinterpreter
    (⟨[Encodable.encode source, input], by simp⟩ : Vector ℕ 2)
  change interpreter.eval [Encodable.encode source, input] =
    ((fun output => [output]) <$>
      Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code (Encodable.encode source)) input)
    at h
  simpa using h

/-- Halting of mathlib's verified `TM2` interpreter from a concrete configuration. -/
def UniversalTM2Halts (cfg : PartrecToTM2.Cfg') : Prop :=
  (Turing.eval (TM2.step PartrecToTM2.tr) cfg).Dom

/-- One fixed, effectively finite `TM2` program recognizes universal code halting. -/
theorem exists_universalTM2 :
    ∃ interpreter : ToPartrec.Code, ∀ source input,
      UniversalTM2Halts
          (PartrecToTM2.init interpreter [Encodable.encode source, input]) ↔
        (Nat.Partrec.Code.eval source input).Dom := by
  obtain ⟨interpreter, hinterpreter⟩ := exists_universalToPartrecCode
  refine ⟨interpreter, fun source input => ?_⟩
  simp only [UniversalTM2Halts, PartrecToTM2.tr_eval, hinterpreter]
  simp

/-- The labels accessible to the fixed interpreter lie in an explicit finite support. -/
theorem universalTM2_finiteSupport (interpreter : ToPartrec.Code) :
    @TM2.Supports PartrecToTM2.K' (fun _ => PartrecToTM2.Γ') PartrecToTM2.Λ'
      (Option PartrecToTM2.Γ')
      ⟨PartrecToTM2.trNormal interpreter PartrecToTM2.Cont'.halt⟩
      PartrecToTM2.tr
      (PartrecToTM2.codeSupp interpreter PartrecToTM2.Cont'.halt) :=
  PartrecToTM2.tr_supports interpreter PartrecToTM2.Cont'.halt

end MatrixMortality.Undecidability
