import MatrixMortality.Undecidability.CyclicTagAvoidance
import MatrixMortality.Undecidability.Problems

/-!
# Verified two-tag sources

A `TwoTagSource` is the exact interface needed by Cook's cyclic compiler: a fixed finite
two-tag system, computable nonempty inputs, a last-labelled halt symbol, a live production, and
the three arbitrary-execution reflection laws.  The cyclic system, one-hot inputs, distinguished
phase, exact firing simulation, and firing reflection are consequences rather than a second
source description.
-/

namespace MatrixMortality.Undecidability

/-- A fixed two-tag system recognizing a predicate on computable inputs. -/
structure TwoTagSource (ι : Type*) [Primcodable ι] (accepts : ι → Prop) where
  /-- Cardinality of the fixed tag alphabet. -/
  alphabet : Nat
  /-- The alphabet contains distinct live and halt labels. -/
  alphabet_one_lt : 1 < alphabet
  /-- Fixed two-tag transition system. -/
  system : TwoTag alphabet
  /-- Distinguished terminal label. -/
  haltLabel : Fin alphabet
  /-- Label whose production seeds Cook's cyclic simulation. -/
  liveLabel : Fin alphabet
  /-- The live label occupies the initial alphabet position. -/
  liveLabel_zero : liveLabel.val = 0
  /-- The halt label occupies the last alphabet position. -/
  haltLabel_last : haltLabel.val + 1 = alphabet
  /-- The live label emits a nonempty word. -/
  liveProduction_nonempty : system.production liveLabel ≠ []
  /-- Computable queue encoding of one source input. -/
  input : ι → List (Fin alphabet)
  /-- The source queue compiler is primitive recursive. -/
  input_primrec : Primrec input
  /-- Every emitted source queue is nonempty. -/
  input_nonempty : ∀ index, input index ≠ []
  /-- Acceptance has a halt-avoiding path to the exact singleton terminal queue. -/
  accepts_implies_avoidingHalt :
    ∀ index, accepts index →
      system.HeadAvoidingReaches haltLabel (input index) [haltLabel]
  /-- Every arbitrary terminating tag execution reflects source acceptance. -/
  accepts_of_tagTermination :
    ∀ index, TagHaltsFrom 2 system.production (input index) → accepts index
  /-- Every arbitrary path to a halt-headed queue reflects source acceptance. -/
  accepts_of_haltHead :
    ∀ index, system.CanReachHead (input index) haltLabel → accepts index

namespace TwoTagSource

theorem alphabet_pos {ι : Type*} [Primcodable ι] {accepts : ι → Prop}
    (source : TwoTagSource ι accepts) :
    0 < source.alphabet :=
  Nat.zero_lt_of_lt source.alphabet_one_lt

theorem haltLabel_nonzero {ι : Type*} [Primcodable ι] {accepts : ι → Prop}
    (source : TwoTagSource ι accepts) :
    source.haltLabel.val ≠ 0 := by
  have last := source.haltLabel_last
  have nontrivial := source.alphabet_one_lt
  omega

/-- Exact singleton-halt reachability is equivalent to source acceptance. -/
theorem reachesHalt_iff {ι : Type*} [Primcodable ι] {accepts : ι → Prop}
    (source : TwoTagSource ι accepts) (index : ι) :
    source.system.QueueReaches (source.input index) [source.haltLabel] ↔ accepts index := by
  constructor
  · intro reach
    exact source.accepts_of_haltHead index ⟨[], by simpa using reach⟩
  · intro accepted
    exact (source.accepts_implies_avoidingHalt index accepted).toReaches

/-- Number of phases in Cook's one-hot cyclic compiler. -/
def period {ι : Type*} [Primcodable ι] {accepts : ι → Prop}
    (source : TwoTagSource ι accepts) : Nat :=
  source.alphabet + source.alphabet

theorem period_pos {ι : Type*} [Primcodable ι] {accepts : ι → Prop}
    (source : TwoTagSource ι accepts) :
    0 < source.period := by
  simp [period, source.alphabet_pos]

/-- Cook's cyclic compiler applied to the fixed two-tag system. -/
def cyclicSystem {ι : Type*} [Primcodable ι] {accepts : ι → Prop}
    (source : TwoTagSource ι accepts) : CyclicTag source.period :=
  CyclicTag.ofTwoTag source.system

/-- One-hot cyclic encoding of a source queue. -/
def cyclicInput {ι : Type*} [Primcodable ι] {accepts : ι → Prop}
    (source : TwoTagSource ι accepts) (index : ι) : List Bool :=
  CyclicTag.encodeWord (source.input index)

theorem cyclicInput_primrec {ι : Type*} [Primcodable ι] {accepts : ι → Prop}
    (source : TwoTagSource ι accepts) :
    Primrec source.cyclicInput :=
  CyclicTag.encodeWord_primrec.comp source.input_primrec

theorem cyclicInput_nonempty {ι : Type*} [Primcodable ι] {accepts : ι → Prop}
    (source : TwoTagSource ι accepts) (index : ι) :
    source.cyclicInput index ≠ [] :=
  CyclicTag.encodeWord_ne_nil source.alphabet_pos (source.input_nonempty index)

/-- Cyclic phase exposing the distinguished two-tag halt label. -/
def haltPhase {ι : Type*} [Primcodable ι] {accepts : ι → Prop}
    (source : TwoTagSource ι accepts) : Fin source.period :=
  CyclicTag.shift (CyclicTag.initialPhase source.alphabet_pos) source.haltLabel

theorem haltPhase_nonzero {ι : Type*} [Primcodable ι] {accepts : ι → Prop}
    (source : TwoTagSource ι accepts) :
    source.haltPhase.val ≠ 0 := by
  rw [haltPhase, CyclicTag.shift_initial_val source.alphabet_pos (by
    have := source.haltLabel.isLt
    omega)]
  exact source.haltLabel_nonzero

/-- The zero cyclic phase has a nonempty appendant. -/
theorem appendant_nonempty_at_zero {ι : Type*} [Primcodable ι]
    {accepts : ι → Prop} (source : TwoTagSource ι accepts)
    (instruction : Fin source.period) (instruction_zero : instruction.val = 0) :
    source.cyclicSystem.appendant instruction ≠ [] := by
  have instruction_eq :
      instruction = CyclicTag.initialPhase source.alphabet_pos := by
    apply Fin.ext
    simpa [CyclicTag.initialPhase] using instruction_zero
  subst instruction
  have phase_eq :
      CyclicTag.shift (CyclicTag.initialPhase source.alphabet_pos) source.liveLabel =
        CyclicTag.initialPhase source.alphabet_pos := by
    apply Fin.ext
    simp [CyclicTag.shift, CyclicTag.initialPhase, source.liveLabel_zero]
  rw [← phase_eq]
  change
    (CyclicTag.ofTwoTag source.system).appendant
        (CyclicTag.shift (CyclicTag.initialPhase source.alphabet_pos) source.liveLabel) ≠ []
  rw [CyclicTag.ofTwoTag_appendant_first source.system source.alphabet_pos source.liveLabel]
  exact CyclicTag.encodeWord_ne_nil source.alphabet_pos source.liveProduction_nonempty

/-- Acceptance reaches Cook's exact distinguished true pulse without firing it earlier. -/
theorem accepts_implies_exactFiring {ι : Type*} [Primcodable ι]
    {accepts : ι → Prop} (source : TwoTagSource ι accepts)
    (index : ι) (accepted : accepts index) :
    source.cyclicSystem.FiringAvoidingReaches source.haltPhase
      { data := source.cyclicInput index, phase := ⟨0, source.period_pos⟩ }
      { data := [true], phase := source.haltPhase } := by
  exact
    CyclicTag.avoiding_reaches_last_firing source.system source.alphabet_pos
      source.haltLabel source.haltLabel_last (source.input index)
      (source.accepts_implies_avoidingHalt index accepted)

/-- Any distinguished firing on a protected cyclic path reflects source acceptance. -/
theorem accepts_of_avoidingFiring {ι : Type*} [Primcodable ι]
    {accepts : ι → Prop} (source : TwoTagSource ι accepts)
    (index : ι) (firing : CyclicTag.Config source.period)
    (reach :
      source.cyclicSystem.FiringAvoidingReaches source.haltPhase
        { data := source.cyclicInput index, phase := ⟨0, source.period_pos⟩ } firing)
    (fires : CyclicTag.FiresAt source.haltPhase firing) :
    accepts index := by
  rcases
      CyclicTag.avoiding_firing_reflects source.system source.alphabet_pos
        source.haltLabel source.haltLabel_last (source.input index) firing reach fires with
    terminates | reachesHead
  · exact source.accepts_of_tagTermination index terminates
  · exact source.accepts_of_haltHead index reachesHead

end TwoTagSource
end MatrixMortality.Undecidability
