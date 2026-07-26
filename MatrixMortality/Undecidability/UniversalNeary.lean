import MatrixMortality.Undecidability.CyclicTagAvoidance
import MatrixMortality.Undecidability.NearyConverse
import MatrixMortality.Undecidability.NearyExecution
import MatrixMortality.Undecidability.NearyProblems
import MatrixMortality.Undecidability.UniversalTwoTag

/-!
# A fixed universal Neary source

The fixed universal two-tag system is compiled through Cook's cyclic-tag construction and
Neary's restricted binary-tag construction. Protected execution gives the forward implication.
The cyclic firing reflection theorem and Neary's arbitrary-execution converse give the reverse
implication.
-/

namespace MatrixMortality
namespace Undecidability
namespace UniversalNeary

open scoped Classical

/-- Number of phases in Cook's cyclic compiler. -/
noncomputable def period : Nat :=
  UniversalTwoTag.alphabet + UniversalTwoTag.alphabet

theorem period_pos : 0 < period := by
  unfold period
  have := UniversalTwoTag.alphabet_one_lt
  omega

/-- Cook's cyclic compiler applied to the fixed universal two-tag system. -/
noncomputable def cyclicSystem : CyclicTag period :=
  CyclicTag.ofTwoTag UniversalTwoTag.system

/-- Relabelled Cocke–Minsky queue encoding one source program. -/
noncomputable def twoTagInput (source : Nat.Partrec.Code) :
    List (Fin UniversalTwoTag.alphabet) :=
  UniversalTwoTag.initialWord source

/-- The fixed two-tag queue is primitive recursive in its source code. -/
theorem twoTagInput_primrec : Primrec twoTagInput :=
  UniversalTwoTag.initialWord_primrec

theorem twoTagInput_nonempty (source : Nat.Partrec.Code) :
    twoTagInput source ≠ [] := by
  exact UniversalTwoTag.initialWord_nonempty source

/-- One-hot binary encoding of the source queue. -/
noncomputable def cyclicInput (source : Nat.Partrec.Code) : List Bool :=
  CyclicTag.encodeWord (twoTagInput source)

/-- The one-hot cyclic-tag input is primitive recursive in its source code. -/
theorem cyclicInput_primrec : Primrec cyclicInput :=
  CyclicTag.encodeWord_primrec.comp twoTagInput_primrec

theorem cyclicInput_nonempty (source : Nat.Partrec.Code) :
    cyclicInput source ≠ [] := by
  exact
    CyclicTag.encodeWord_ne_nil (by have := UniversalTwoTag.alphabet_one_lt; omega)
      (twoTagInput_nonempty source)

/-- Program phase exposing the last, halting two-tag label. -/
noncomputable def haltPhase : Fin period :=
  CyclicTag.shift
    (CyclicTag.initialPhase (by have := UniversalTwoTag.alphabet_one_lt; omega))
    UniversalTwoTag.haltLabel

theorem haltPhase_nonzero : haltPhase.val ≠ 0 := by
  rw [haltPhase, CyclicTag.shift_initial_val
    (by have := UniversalTwoTag.alphabet_one_lt; omega) (by
      have := UniversalTwoTag.haltLabel.isLt
      omega)]
  exact UniversalTwoTag.haltLabel_nonzero

/-- Deletion width of the fixed restricted-tag compiler. -/
noncomputable def beta : Nat :=
  NearyCompiler.deletionWidth period

/-- Restricted binary-tag appendant emitted for one source program. -/
noncomputable def body (source : Nat.Partrec.Code) : List TagLetter :=
  NearyCompiler.body cyclicSystem (cyclicInput source) haltPhase period_pos

/-- The complete fixed-machine Neary source compiler is primitive recursive. -/
theorem body_primrec : Primrec body :=
  (NearyCompiler.body_primrec cyclicSystem haltPhase period_pos).comp
    cyclicInput_primrec

theorem beta_large : 2 < beta :=
  NearyCompiler.deletionWidth_large period_pos

theorem body_long (source : Nat.Partrec.Code) :
    beta - 1 ≤ (body source).length := by
  simpa [beta, body] using
    NearyArithmeticEnvelope.body_long
      (NearyCompiler.arithmeticEnvelope cyclicSystem (cyclicInput source)
        haltPhase period_pos)

theorem body_divisible (source : Nat.Partrec.Code) :
    beta - 1 ∣ (body source).length := by
  simpa [beta, body] using
    NearyArithmeticEnvelope.body_divisible
      (NearyCompiler.arithmeticEnvelope cyclicSystem (cyclicInput source)
        haltPhase period_pos)

private theorem appendant_nonempty_at_zero (instruction : Fin period)
    (instruction_zero : instruction.val = 0) :
    cyclicSystem.appendant instruction ≠ [] := by
  have alphabet_pos : 0 < UniversalTwoTag.alphabet := by
    have := UniversalTwoTag.alphabet_one_lt
    omega
  have instruction_eq :
      instruction = CyclicTag.initialPhase alphabet_pos := by
    apply Fin.ext
    simpa [CyclicTag.initialPhase] using instruction_zero
  subst instruction
  have phase_eq :
      CyclicTag.shift (CyclicTag.initialPhase alphabet_pos) UniversalTwoTag.zeroLabel =
        CyclicTag.initialPhase alphabet_pos := by
    apply Fin.ext
    simp [CyclicTag.shift, CyclicTag.initialPhase, UniversalTwoTag.zeroLabel]
  rw [← phase_eq]
  change
    (CyclicTag.ofTwoTag UniversalTwoTag.system).appendant
        (CyclicTag.shift (CyclicTag.initialPhase alphabet_pos) UniversalTwoTag.zeroLabel) ≠ []
  rw [CyclicTag.ofTwoTag_appendant_first UniversalTwoTag.system alphabet_pos
    UniversalTwoTag.zeroLabel]
  exact
    CyclicTag.encodeWord_ne_nil alphabet_pos UniversalTwoTag.system_production_zero_nonempty

/-- Source-code halting forces halting of the emitted restricted binary-tag instance. -/
theorem codeHalts_implies_tagHaltsFrom (source : Nat.Partrec.Code)
    (halts : CodeHalts source) :
    TagHaltsFrom beta (tagOutput (body source))
      ((body source).drop (beta - 1) ++ [.b]) := by
  have twoTagReach := UniversalTwoTag.halts_implies_halt_avoiding source halts
  have cyclicReach :=
    CyclicTag.avoiding_reaches_last_firing UniversalTwoTag.system
      (by have := UniversalTwoTag.alphabet_one_lt; omega)
      UniversalTwoTag.haltLabel UniversalTwoTag.haltLabel_last
      (twoTagInput source) twoTagReach
  have compiled :=
    NearyCompiler.read_exact_firing_halts cyclicSystem (cyclicInput source) haltPhase
      period_pos (cyclicInput_nonempty source) haltPhase_nonzero
      appendant_nonempty_at_zero cyclicReach
  rw [NearyCompiler.compiledOutput_eq_tagOutput] at compiled
  exact compiled

/-- Every halting execution of the emitted restricted binary-tag instance reflects source-code
halting. -/
theorem tagHaltsFrom_implies_codeHalts (source : Nat.Partrec.Code)
    (halts :
      TagHaltsFrom beta (tagOutput (body source))
        ((body source).drop (beta - 1) ++ [.b])) :
    CodeHalts source := by
  have compiledHalts :
      TagHaltsFrom beta
        (NearyCompiler.compiledOutput cyclicSystem (cyclicInput source) haltPhase period_pos)
        ((body source).drop (beta - 1) ++ [.b]) := by
    rw [NearyCompiler.compiledOutput_eq_tagOutput]
    exact halts
  obtain ⟨firing, reach, fires⟩ :=
    NearyCompiler.compiled_halts_implies_firing cyclicSystem (cyclicInput source)
      haltPhase period_pos (cyclicInput_nonempty source) appendant_nonempty_at_zero compiledHalts
  rcases
      CyclicTag.avoiding_firing_reflects UniversalTwoTag.system
        (by have := UniversalTwoTag.alphabet_one_lt; omega)
        UniversalTwoTag.haltLabel UniversalTwoTag.haltLabel_last
        (twoTagInput source) firing reach fires with
    twoTagHalts | reachesHalt
  · exact UniversalTwoTag.tagHaltsFrom_implies_halts source twoTagHalts
  · exact UniversalTwoTag.reachesHead_halt_implies_halts source reachesHalt

/-- The emitted restricted binary-tag instance halts exactly for source codes halting at input
zero. -/
theorem tagHaltsFrom_iff_codeHalts (source : Nat.Partrec.Code) :
    TagHaltsFrom beta (tagOutput (body source))
        ((body source).drop (beta - 1) ++ [.b]) ↔
      CodeHalts source :=
  ⟨tagHaltsFrom_implies_codeHalts source, codeHalts_implies_tagHaltsFrom source⟩

/-- The concrete four-letter GPCP instance emitted for one source program. -/
noncomputable def gpcpInstance (source : Nat.Partrec.Code) : BinaryGPCP4 :=
  nearyGPCP4 beta (body source)

/-- The GPCP instance family is primitive recursive. -/
theorem gpcpInstance_primrec : Primrec gpcpInstance :=
  (nearyGPCP4_primrec beta).comp body_primrec

theorem gpcpInstance_solvable_iff_codeHalts (source : Nat.Partrec.Code) :
    (gpcpInstance source).Solvable ↔ CodeHalts source := by
  rw [gpcpInstance,
    nearyGPCP4_solvable_iff_tagHaltsFrom beta (body source)
      beta_large (body_long source) (body_divisible source),
    tagHaltsFrom_iff_codeHalts]

/-- Halting at input zero many-one reduces to four-letter binary GPCP. -/
theorem codeHalts_reduces_gpcp4 :
    CodeHalts ≤₀ BinaryGPCP4.Solvable :=
  ⟨gpcpInstance, gpcpInstance_primrec.to_comp,
    fun source => (gpcpInstance_solvable_iff_codeHalts source).symm⟩

/-- Four-letter binary GPCP solvability is not computable. -/
theorem gpcp4_not_computable : ¬ComputablePred BinaryGPCP4.Solvable :=
  gpcp4_not_computable_of_reduction codeHalts_reduces_gpcp4

/-- The concrete five-matrix mortality instance emitted for one source program. -/
noncomputable def mortalityInstance (source : Nat.Partrec.Code) : Mortality35 :=
  nearyMortality35 beta (body source)

/-- The mortality instance family is primitive recursive. -/
theorem mortalityInstance_primrec : Primrec mortalityInstance :=
  (nearyMortality35_primrec beta).comp body_primrec

theorem mortalityInstance_mortal_iff_codeHalts (source : Nat.Partrec.Code) :
    (mortalityInstance source).Mortal ↔ CodeHalts source := by
  rw [mortalityInstance,
    nearyMortality35_mortal_iff_tagHaltsFrom beta (body source)
      beta_large (body_long source) (body_divisible source),
    tagHaltsFrom_iff_codeHalts]

/-- Halting at input zero many-one reduces to mortality of five `3 × 3` integer matrices. -/
theorem codeHalts_reduces_mortality35 :
    CodeHalts ≤₀ MortalityProblem.Mortal (d := 3) (k := 5) :=
  ⟨mortalityInstance, mortalityInstance_primrec.to_comp,
    fun source => (mortalityInstance_mortal_iff_codeHalts source).symm⟩

/-- Mortality of five `3 × 3` integer matrices is not computable. -/
theorem mortality35_not_computable :
    ¬ComputablePred (MortalityProblem.Mortal (d := 3) (k := 5)) :=
  mortality35_not_computable_of_reduction codeHalts_reduces_mortality35

end UniversalNeary
end Undecidability
end MatrixMortality
