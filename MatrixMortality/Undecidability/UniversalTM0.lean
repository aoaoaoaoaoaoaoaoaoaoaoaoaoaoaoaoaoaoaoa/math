import MatrixMortality.Undecidability.FiniteTM0
import MatrixMortality.Undecidability.SeededTM2
import MatrixMortality.Undecidability.UniversalMachine

/-!
# A fixed universal binary TM0 machine

Mathlib's verified universal interpreter is translated through its `TM2 → TM1`, finite-alphabet
`TM1 → TM1`, and `TM1 → TM0` compilers.  The final support restriction replaces mathlib's
finitely supported label type by an actual finite type.
-/

open Mathlib (Vector)
open Turing
open scoped Classical

namespace MatrixMortality
namespace Undecidability
namespace UniversalTM0

instance : Fintype PartrecToTM2.K' where
  elems := {.main, .rev, .aux, .stack}
  complete index := by cases index <;> simp

/-- The alphabet emitted by the four-stack-to-one-tape compiler. -/
abbrev StackAlphabet :=
  @TM2to1.Γ' PartrecToTM2.K' (fun _ => PartrecToTM2.Γ')

/-- Labels of the rooted four-stack interpreter after one-tape translation. -/
abbrev StackLabel :=
  @TM2to1.Λ' PartrecToTM2.K' (fun _ => PartrecToTM2.Γ')
    (SeededTM2.Label PartrecToTM2.Λ') (Option PartrecToTM2.Γ')

/-- Labels of the fixed-alphabet binary translation. -/
abbrev BinaryLabel :=
  @TM1to1.Λ' StackAlphabet StackLabel (Option PartrecToTM2.Γ')

/-- The single-tape alphabet emitted by mathlib's `TM2 → TM1` compiler. -/
instance : Fintype StackAlphabet := inferInstance

/-- Fixed-width binary alphabet coding chosen once for the universal interpreter. -/
noncomputable def binaryWidth : Nat :=
  (TM1to1.exists_enc_dec (Γ := StackAlphabet)).choose

/-- Fixed-width binary encoder for the stack alphabet. -/
noncomputable def binaryEncode : StackAlphabet → Vector Bool binaryWidth :=
  (TM1to1.exists_enc_dec (Γ := StackAlphabet)).choose_spec.choose

/-- Decoder inverse to `binaryEncode` on encoded stack symbols. -/
noncomputable def binaryDecode : Vector Bool binaryWidth → StackAlphabet :=
  (TM1to1.exists_enc_dec (Γ := StackAlphabet)).choose_spec.choose_spec.choose

theorem binaryEncode_blank :
    binaryEncode default = Vector.replicate binaryWidth false :=
  (TM1to1.exists_enc_dec (Γ := StackAlphabet)).choose_spec.choose_spec.choose_spec.1

theorem binaryDecode_encode (symbol : StackAlphabet) :
    binaryDecode (binaryEncode symbol) = symbol :=
  (TM1to1.exists_enc_dec (Γ := StackAlphabet)).choose_spec.choose_spec.choose_spec.2 symbol

/-- The `TM1` tape emitted from the universal interpreter's four-stack input. -/
def stackInput (input : List ℕ) : List StackAlphabet :=
  TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList input)

/-- Fixed-width binary spelling of `stackInput`. -/
noncomputable def binaryInput (input : List ℕ) : List Bool :=
  (stackInput input).bind fun symbol => (binaryEncode symbol).toList

/-- The root label that specializes the fixed interpreter while leaving its input variable. -/
def rootLabel (interpreter : ToPartrec.Code) : PartrecToTM2.Λ' :=
  PartrecToTM2.trNormal interpreter PartrecToTM2.Cont'.halt

/-- Mathlib's four-stack interpreter with a canonical initial label. -/
def seededMachine (interpreter : ToPartrec.Code) :
    SeededTM2.Label PartrecToTM2.Λ' →
      TM2.Stmt (fun _ : PartrecToTM2.K' => PartrecToTM2.Γ')
        (SeededTM2.Label PartrecToTM2.Λ') (Option PartrecToTM2.Γ') :=
  SeededTM2.machine PartrecToTM2.tr (rootLabel interpreter)

/-- The finite labels visited by the rooted four-stack interpreter. -/
noncomputable def seededSupport (interpreter : ToPartrec.Code) :
    Finset (SeededTM2.Label PartrecToTM2.Λ') :=
  insert .root
    ((PartrecToTM2.codeSupp interpreter PartrecToTM2.Cont'.halt).image
      SeededTM2.Label.source)

/-- Mathlib's rooted four-stack interpreter after translation to a one-tape machine. -/
def stackMachine (interpreter : ToPartrec.Code) :
    StackLabel → TM1.Stmt StackAlphabet StackLabel (Option PartrecToTM2.Γ') :=
  TM2to1.tr (seededMachine interpreter)

/-- Fixed binary-alphabet translation of `stackMachine`. -/
noncomputable def binaryMachine (interpreter : ToPartrec.Code) :
    BinaryLabel → TM1.Stmt Bool BinaryLabel (Option PartrecToTM2.Γ') :=
  TM1to1.tr binaryEncode binaryDecode (stackMachine interpreter)

/-- Finite support of the one-tape stack interpreter. -/
noncomputable def stackSupport (interpreter : ToPartrec.Code) : Finset StackLabel :=
  TM2to1.trSupp (seededMachine interpreter) (seededSupport interpreter)

/-- Finite support after binary alphabet translation. -/
noncomputable def binarySupport (interpreter : ToPartrec.Code) : Finset BinaryLabel :=
  TM1to1.trSupp (stackMachine interpreter) (stackSupport interpreter)

/-- Label type emitted by mathlib's `TM1 → TM0` compiler. -/
abbrev PostLabel (interpreter : ToPartrec.Code) :=
  TM1to0.Λ' (binaryMachine interpreter)

/-- Binary `TM0` interpreter before restricting its finitely supported label type. -/
noncomputable def postMachine (interpreter : ToPartrec.Code) :
    TM0.Machine Bool (PostLabel interpreter) :=
  TM1to0.tr (binaryMachine interpreter)

/-- Finite support of the binary `TM0` interpreter. -/
noncomputable def postSupport (interpreter : ToPartrec.Code) :
    Finset (PostLabel interpreter) :=
  TM1to0.trStmts (binaryMachine interpreter) (binarySupport interpreter)

theorem seeded_init_eq (interpreter : ToPartrec.Code) (input : List ℕ) :
    SeededTM2.config (rootLabel interpreter)
        (TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList input) :
          TM2.Cfg (fun _ : PartrecToTM2.K' => PartrecToTM2.Γ')
            (SeededTM2.Label PartrecToTM2.Λ') (Option PartrecToTM2.Γ')) =
      PartrecToTM2.init interpreter input := by
  simp only [TM2.init, PartrecToTM2.init, SeededTM2.config, rootLabel, default]
  congr 1
  funext index
  cases index <;> simp

theorem binary_trCfg_init (input : List ℕ) :
    TM1to1.trCfg binaryEncode binaryEncode_blank
        (TM1.init (stackInput input) :
          TM1.Cfg StackAlphabet StackLabel (Option PartrecToTM2.Γ')) =
      (TM1.init (binaryInput input) :
        TM1.Cfg Bool
          (@TM1to1.Λ' StackAlphabet StackLabel (Option PartrecToTM2.Γ'))
          (Option PartrecToTM2.Γ')) := by
  simp only [TM1to1.trCfg, TM1.init]
  congr 1

/-- The rooted four-stack interpreter remains inside its explicit finite support. -/
theorem seeded_supported (interpreter : ToPartrec.Code) :
    TM2.Supports (seededMachine interpreter) (seededSupport interpreter) := by
  letI : Inhabited PartrecToTM2.Λ' := ⟨rootLabel interpreter⟩
  exact SeededTM2.supports PartrecToTM2.tr (rootLabel interpreter)
    (PartrecToTM2.codeSupp interpreter PartrecToTM2.Cont'.halt)
    (universalTM2_finiteSupport interpreter)
    (universalTM2_finiteSupport interpreter).1

theorem stack_supported (interpreter : ToPartrec.Code) :
    TM1.Supports (stackMachine interpreter) (stackSupport interpreter) := by
  apply TM2to1.tr_supports
  exact seeded_supported interpreter

theorem binary_supported (interpreter : ToPartrec.Code) :
    TM1.Supports (binaryMachine interpreter) (binarySupport interpreter) := by
  exact TM1to1.tr_supports binaryEncode binaryDecode (stackMachine interpreter)
    (stack_supported interpreter)

theorem post_supported (interpreter : ToPartrec.Code) :
    TM0.Supports (postMachine interpreter) ↑(postSupport interpreter) := by
  exact TM1to0.tr_supports (binaryMachine interpreter) (binary_supported interpreter)

/-- The finite binary `TM0` restriction halts exactly when the fixed four-stack interpreter
halts on the same input. -/
theorem eval_dom_iff_tm2 (interpreter : ToPartrec.Code) (input : List ℕ) :
    (Turing.eval
        (TM0.step
          (FiniteTM0.machine (postMachine interpreter) (postSupport interpreter)))
        (TM0.init (binaryInput input) :
          TM0.Cfg Bool (FiniteTM0.State (postSupport interpreter)))).Dom ↔
      UniversalTM2Halts (PartrecToTM2.init interpreter input) := by
  rw [FiniteTM0.eval_dom_iff (postMachine interpreter) (postSupport interpreter)
    (post_supported interpreter) (binaryInput input)]
  change
    (Turing.eval (TM0.step (TM1to0.tr (binaryMachine interpreter)))
      (TM0.init (binaryInput input))).Dom ↔
        UniversalTM2Halts (PartrecToTM2.init interpreter input)
  rw [Turing.tr_eval_dom
    (a₁ := TM1.init (binaryInput input))
    (a₂ := TM0.init (binaryInput input))
    (TM1to0.tr_respects (binaryMachine interpreter)) rfl]
  change
    (Turing.eval
      (TM1.step (TM1to1.tr binaryEncode binaryDecode (stackMachine interpreter)))
      (TM1.init (binaryInput input))).Dom ↔
        UniversalTM2Halts (PartrecToTM2.init interpreter input)
  rw [Turing.tr_eval_dom
    (TM1to1.tr_respects binaryDecode (stackMachine interpreter) binaryDecode_encode)
    (binary_trCfg_init input)]
  have translated :=
    TM2to1.tr_eval_dom (seededMachine interpreter) PartrecToTM2.K'.main
      (PartrecToTM2.trList input)
  change
    (Turing.eval
      (TM1.step (TM2to1.tr (seededMachine interpreter)))
      (TM1.init
        (TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList input)))).Dom ↔
      (Turing.eval
        (TM2.step (seededMachine interpreter))
        (TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList input))).Dom
    at translated
  change
    (Turing.eval
      (TM1.step (TM2to1.tr (seededMachine interpreter)))
      (TM1.init
        (TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList input)))).Dom ↔
        UniversalTM2Halts (PartrecToTM2.init interpreter input)
  rw [translated]
  change
    (Turing.eval
      (TM2.step (seededMachine interpreter))
      (TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList input))).Dom ↔
        (Turing.eval (TM2.step PartrecToTM2.tr)
          (PartrecToTM2.init interpreter input)).Dom
  rw [Turing.tr_eval_dom
    (SeededTM2.respects PartrecToTM2.tr (rootLabel interpreter))
    (seeded_init_eq interpreter input)]
  rfl

end UniversalTM0
end Undecidability
end MatrixMortality
