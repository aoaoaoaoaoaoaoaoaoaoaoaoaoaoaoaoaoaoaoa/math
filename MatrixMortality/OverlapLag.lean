import MatrixMortality.OverlapQueue

/-!
# The zero-framed binary two-Lag kernel

The principal deletion scanner is literally a binary context-two Lag system: prefix the queue
by its controller bit, inspect the first two bits, delete the first, and append one production.
This file proves the step-for-step equivalence, translates both reachability promises, and
composes the kernel directly with the checked three-matrix mortality compiler.
-/

namespace MatrixMortality.OverlapLag

open OverlapQueue

/-- Encode the erase/rule phase as the leading bit of a Lag configuration. -/
def phaseBit : PairPhase → Bool
  | .erase => false
  | .rule => true

/-- Decode the leading bit of a Lag configuration. -/
def bitPhase : Bool → PairPhase
  | false => .erase
  | true => .rule

@[simp] theorem phaseBit_bitPhase (bit : Bool) : phaseBit (bitPhase bit) = bit := by
  cases bit <;> rfl

@[simp] theorem bitPhase_phaseBit (phase : PairPhase) : bitPhase (phaseBit phase) = phase := by
  cases phase <;> rfl

/-- The deletion scanner moves to the state named by the consumed queue bit. -/
def transition : PairPhase → Bool → PairPhase
  | .rule, head => bitPhase head
  | .erase, head => bitPhase head

@[simp] theorem transition_eq (phase : PairPhase) (head : Bool) :
    transition phase head = bitPhase head := by
  cases phase <;> rfl

/-- The four appendants of the zero-framed Lag scanner.

The argument order is n, U, V, W.  In phase rule the roles 0 and 1 append U and the empty word;
in phase erase they append V and W followed by n+1 zeroes.
-/
def produce (n : Nat) (U V W : List Bool) : PairPhase → Bool → List Bool
  | .rule, false => U
  | .rule, true => []
  | .erase, false => V
  | .erase, true => W ++ List.replicate (n + 1) false

/-- Cancellation words which witness the positive two-frame cocycle. -/
def cancel (n : Nat) (U V W : List Bool) : PairPhase → Bool → List Bool
  | .rule, false => List.replicate (n + 1) false ++ U
  | .rule, true => []
  | .erase, false => V
  | .erase, true => W

/-- A binary Lag trace, retaining the chronological word of inspected queue bits.

The encoded configuration is phase :: queue.  A step

  phase :: head :: tail  ↦  head :: (tail ++ append phase head)

inspects the leading context of length two and deletes its first bit.
-/
inductive Trace (append : Bool → Bool → List Bool) :
    Bool → List Bool → List Bool → Bool → List Bool → Prop
  | nil (phase : Bool) (queue : List Bool) :
      Trace append phase queue [] phase queue
  | step {phase target head : Bool} {tail word residual : List Bool} :
      Trace append head (tail ++ append phase head) word target residual →
      Trace append phase (head :: tail) (head :: word) target residual

/-- Prefix a queue by the controller bit inspected by the context-two Lag rule. -/
def encode (phase : Bool) (queue : List Bool) : List Bool :=
  phase :: queue

/-- One Lag step has the advertised operation on encoded configurations. -/
theorem encode_step (append : Bool → Bool → List Bool) (phase head : Bool)
    (tail : List Bool) :
    encode head (tail ++ append phase head) =
      head :: (tail ++ append phase head) := by
  rfl

/-- View the scanner appendant table as the four context-two Lag productions. -/
def appendant (n : Nat) (U V W : List Bool) (phase head : Bool) : List Bool :=
  produce n U V W (bitPhase phase) head

@[simp] theorem appendant_false_false (n : Nat) (U V W : List Bool) :
    appendant n U V W false false = V := by
  rfl

@[simp] theorem appendant_false_true (n : Nat) (U V W : List Bool) :
    appendant n U V W false true = W ++ List.replicate (n + 1) false := by
  rfl

@[simp] theorem appendant_true_false (n : Nat) (U V W : List Bool) :
    appendant n U V W true false = U := by
  rfl

@[simp] theorem appendant_true_true (n : Nat) (U V W : List Bool) :
    appendant n U V W true true = [] := by
  rfl

/-- Every overlap-queue trace is the same chronological binary Lag trace. -/
theorem ofQueueTrace {n : Nat} {U V W : List Bool}
    {source target : PairPhase} {initial word residual : List Bool}
    (trace : OverlapQueue.Trace transition (produce n U V W)
      source initial word target residual) :
    Trace (appendant n U V W) (phaseBit source) initial word
      (phaseBit target) residual := by
  induction trace with
  | nil phase queue => exact .nil (phaseBit phase) queue
  | @step phase target head tail word residual _trace induction =>
      apply Trace.step
      simpa [appendant] using induction

/-- Every binary Lag trace decodes to the corresponding overlap-queue trace. -/
theorem toQueueTrace {n : Nat} {U V W : List Bool}
    {source target : Bool} {initial word residual : List Bool}
    (trace : Trace (appendant n U V W) source initial word target residual) :
    OverlapQueue.Trace transition (produce n U V W)
      (bitPhase source) initial word (bitPhase target) residual := by
  induction trace with
  | nil phase queue => exact .nil (bitPhase phase) queue
  | @step phase target head tail word residual _trace induction =>
      apply OverlapQueue.Trace.step
      simpa [appendant] using induction

/-- Reachability of the accepting singleton 0 in the binary Lag system. -/
def Accepts (n : Nat) (U V W : List Bool) : Prop :=
  ∃ word,
    Trace (appendant n U V W) true (List.replicate n false) word false []

/-- Every reachable singleton is the accepting singleton 0. -/
def SingletonIsolation (n : Nat) (U V W : List Bool) : Prop :=
  ∀ word target,
    Trace (appendant n U V W) true (List.replicate n false) word target [] →
      target = false

/-- The forbidden framed return is 1 followed by n+1 zeroes, not the initial Lag word. -/
def AvoidsLongFrame (n : Nat) (U V W : List Bool) : Prop :=
  ∀ word,
    ¬Trace (appendant n U V W) true (List.replicate n false) word true
      (List.replicate (n + 1) false)

theorem accepts_iff_queueAccepts (n : Nat) (U V W : List Bool) :
    Accepts n U V W ↔
      OverlapQueue.Accepts transition (produce n U V W)
        (List.replicate n false) := by
  constructor
  · rintro ⟨word, trace⟩
    exact ⟨word, by simpa using toQueueTrace trace⟩
  · rintro ⟨word, trace⟩
    exact ⟨word, by simpa using ofQueueTrace trace⟩

theorem singletonIsolation_iff_emptyIsAccepting (n : Nat) (U V W : List Bool) :
    SingletonIsolation n U V W ↔
      OverlapQueue.EmptyIsAccepting transition (produce n U V W)
        (List.replicate n false) := by
  constructor
  · intro isolation word phase trace
    have decoded := ofQueueTrace trace
    have bit_eq := isolation word (phaseBit phase) decoded
    cases phase <;> simp_all [phaseBit]
  · intro empty_accepts word target trace
    have decoded := toQueueTrace trace
    have phase_eq := empty_accepts word (bitPhase target) decoded
    cases target <;> simp_all [bitPhase]

theorem avoidsLongFrame_iff_avoidsFramedReturn (n : Nat) (U V W : List Bool) :
    AvoidsLongFrame n U V W ↔
      OverlapQueue.AvoidsFramedReturn transition (produce n U V W)
        (List.replicate n false) := by
  have frame_eq :
      OverlapQueue.frame (List.replicate n false) .rule =
        List.replicate (n + 1) false := by
    simp [OverlapQueue.frame, List.replicate_succ]
  constructor
  · intro avoids word trace
    apply avoids word
    rw [← frame_eq]
    simpa using ofQueueTrace trace
  · intro avoids word trace
    apply avoids word
    rw [frame_eq]
    simpa using toQueueTrace trace

/-- The scanner productions and cancellation words obey the exact local frame law. -/
theorem cocycle (n : Nat) (U V W : List Bool) :
    OverlapQueue.Cocycle (List.replicate n false) transition
      (produce n U V W) (cancel n U V W) := by
  intro phase head
  cases phase <;> cases head <;>
    simp [OverlapQueue.frame, transition, bitPhase, produce, cancel, List.replicate_succ,
      List.append_assoc]

/-- The literal binary two-Lag kernel compiles to three integer 4 by 4 matrices.

Under singleton isolation and avoidance of the longer frame, matrix mortality is exactly
reachability of the singleton 0 from 1 followed by n zeroes.
-/
theorem mortality_iff_accepts (n : Nat) (U V W : List Bool) (n_pos : 0 < n)
    (singleton_isolation : SingletonIsolation n U V W)
    (avoids_long_frame : AvoidsLongFrame n U V W) :
    IsMortal (OverlapQueue.mortalityFamily transition (cancel n U V W)) ↔
      Accepts n U V W := by
  rw [accepts_iff_queueAccepts]
  apply OverlapQueue.mortality_iff_accepts
  · intro empty
    have lengths := congrArg List.length empty
    simp at lengths
    omega
  · exact cocycle n U V W
  · exact (singletonIsolation_iff_emptyIsAccepting n U V W).mp singleton_isolation
  · exact (avoidsLongFrame_iff_avoidsFramedReturn n U V W).mp avoids_long_frame

/-- A fixed morphism cannot identify a terminal letter with its own compulsory framed image.

This rules out the direct homomorphic Neary coding: if initial = prefix ++ [terminal], then
mapping terminal to 0 :: spell map initial contradicts word length.
-/
theorem terminal_image_ne_frame {α : Type*} (map : α → List Bool)
    (stem : List α) (terminal : α) :
    map terminal ≠ false :: spell map (stem ++ [terminal]) := by
  intro equality
  have lengths := congrArg List.length equality
  simp [spell_append, spell] at lengths
  omega

end MatrixMortality.OverlapLag
