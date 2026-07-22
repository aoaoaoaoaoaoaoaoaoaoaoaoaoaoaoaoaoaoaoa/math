import MatrixMortality.NearyEncoding
import MatrixMortality.Undecidability.CyclicTag
import MatrixMortality.Undecidability.TagExecution
import MatrixMortality.Undecidability.Tracks

/-!
# Neary's Table 2 compiler

This file constructs the restricted binary-tag appendant by prescribing its fixed-stride tracks.
The padding is deliberately generous: it is computable, satisfies every Table 2 lower bound, and
is congruent to one modulo `β - 1` as required by the terminal GPCP reduction.
-/

open scoped BigOperators

namespace MatrixMortality.Undecidability.NearyCompiler

open Mathlib (Vector)

/-- The prime code for the empty cyclic-tag symbol. -/
def epsilonPrime : List TagLetter :=
  List.replicate 4 .b ++ .c :: List.replicate 6 .b

/-- The length-eleven prime code for a cyclic-tag bit. -/
def bitPrime : Bool → List TagLetter
  | false => List.replicate 6 .b ++ .c :: List.replicate 4 .b
  | true => List.replicate 8 .b ++ .c :: List.replicate 2 .b

@[simp]
theorem epsilonPrime_length : epsilonPrime.length = 11 := by
  simp [epsilonPrime]

@[simp]
theorem bitPrime_length (bit : Bool) : (bitPrime bit).length = 11 := by
  cases bit <;> simp [bitPrime]

/-- Prime-code a binary word. -/
def encodePrimes (bits : List Bool) : List TagLetter :=
  (bits.map bitPrime).join

@[simp]
theorem encodePrimes_length (bits : List Bool) : (encodePrimes bits).length = 11 * bits.length := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      rw [show encodePrimes (bit :: bits) = bitPrime bit ++ encodePrimes bits by rfl]
      simp [ih, Nat.mul_succ, Nat.add_comm]

/-- Repeat and concatenate one word. -/
def repeatWord {α : Type*} (count : Nat) (word : List α) : List α :=
  (List.replicate count word).join

@[simp]
theorem repeatWord_length {α : Type*} (count : Nat) (word : List α) :
    (repeatWord count word).length = count * word.length := by
  induction count with
  | zero => simp [repeatWord]
  | succ count ih =>
      rw [show repeatWord (count + 1) word = word ++ repeatWord count word by
        unfold repeatWord
        rw [List.replicate_succ]
        rfl]
      simp [ih, Nat.succ_mul, Nat.add_comm]

theorem repeatWord_succ_right {α : Type*} (count : Nat) (word : List α) :
    repeatWord (count + 1) word = repeatWord count word ++ word := by
  simp [repeatWord, List.replicate_succ']

theorem repeatWord_succ_left {α : Type*} (count : Nat) (word : List α) :
    repeatWord (count + 1) word = word ++ repeatWord count word := by
  unfold repeatWord
  rw [List.replicate_succ]
  rfl

/-- Pad a prefix on the right to an exact target length. -/
def padRight {α : Type*} (width : Nat) (filler : α) (stem : List α) : List α :=
  stem ++ List.replicate (width - stem.length) filler

theorem padRight_length {α : Type*} {width : Nat} (filler : α) (stem : List α)
    (stem_fits : stem.length ≤ width) :
    (padRight width filler stem).length = width := by
  simp [padRight]
  omega

/-- Place padding between a fixed prefix and suffix. -/
def padBetween {α : Type*} (width : Nat) (filler : α) (stem ending : List α) : List α :=
  stem ++ List.replicate (width - stem.length - ending.length) filler ++ ending

theorem padBetween_length {α : Type*} {width : Nat} (filler : α)
    (stem ending : List α) (fixed_fits : stem.length + ending.length ≤ width) :
    (padBetween width filler stem ending).length = width := by
  simp [padBetween]
  omega

/-- Table 2 deletion width. -/
def deletionWidth (period : Nat) : Nat := 10 * period

/-- Total appendant length, used as a simple computable upper bound on every appendant. -/
def appendantMass {period : Nat} (system : CyclicTag period) : Nat :=
  ∑ phase : Fin period, (system.appendant phase).length

theorem appendant_length_le_mass {period : Nat} (system : CyclicTag period)
    (phase : Fin period) :
    (system.appendant phase).length ≤ appendantMass system := by
  simpa [appendantMass] using
    (Finset.single_le_sum (fun index _ => Nat.zero_le (system.appendant index).length)
      (Finset.mem_univ phase))

/-- A uniform lower bound stronger than every nonnegative-exponent obligation in Table 2. -/
def safetyBound {period : Nat} (system : CyclicTag period) (input : List Bool) : Nat :=
  11 * (input.length + period + deletionWidth period + appendantMass system + 1) +
    deletionWidth period + 2

/-- Number of padding rounds. -/
def paddingRounds {period : Nat} (system : CyclicTag period) (input : List Bool) : Nat :=
  safetyBound system input

/-- Track length, chosen congruent to one modulo `β - 1`. -/
def trackWidth {period : Nat} (system : CyclicTag period) (input : List Bool) : Nat :=
  paddingRounds system input * (deletionWidth period - 1) + 1

theorem deletionWidth_pos {period : Nat} (period_pos : 0 < period) :
    0 < deletionWidth period := by
  simp [deletionWidth, period_pos]

theorem deletionWidth_large {period : Nat} (period_pos : 0 < period) :
    2 < deletionWidth period := by
  simp [deletionWidth]
  omega

theorem safetyBound_pos {period : Nat} (system : CyclicTag period) (input : List Bool) :
    0 < safetyBound system input := by
  simp [safetyBound]

theorem safetyBound_le_trackWidth {period : Nat} (system : CyclicTag period)
    (input : List Bool) (period_pos : 0 < period) :
    safetyBound system input ≤ trackWidth system input := by
  unfold trackWidth paddingRounds
  have multiplier : 1 ≤ deletionWidth period - 1 := by
    have := deletionWidth_large period_pos
    omega
  calc
    safetyBound system input ≤ safetyBound system input * (deletionWidth period - 1) :=
      Nat.le_mul_of_pos_right _ multiplier
    _ ≤ safetyBound system input * (deletionWidth period - 1) + 1 := Nat.le_add_right _ _

theorem deletionWidth_le_trackWidth {period : Nat} (system : CyclicTag period)
    (input : List Bool) (period_pos : 0 < period) :
    deletionWidth period ≤ trackWidth system input := by
  have bounded := safetyBound_le_trackWidth system input period_pos
  unfold safetyBound at bounded
  omega

theorem trackWidth_pos {period : Nat} (system : CyclicTag period) (input : List Bool) :
    0 < trackWidth system input := by
  simp [trackWidth]

theorem input_fixed_fits {period : Nat} (system : CyclicTag period) (input : List Bool)
    (period_pos : 0 < period) :
    (deletionWidth period - 2 + (encodePrimes input).length) +
        (repeatWord period epsilonPrime).length ≤
      trackWidth system input := by
  rw [encodePrimes_length, repeatWord_length, epsilonPrime_length]
  refine le_trans ?_ (safetyBound_le_trackWidth system input period_pos)
  simp [safetyBound, deletionWidth]
  omega

theorem epsilon_fixed_fits {period : Nat} (system : CyclicTag period) (input : List Bool)
    (period_pos : 0 < period) :
    (repeatWord period epsilonPrime).length ≤ trackWidth system input := by
  rw [repeatWord_length, epsilonPrime_length]
  refine le_trans ?_ (safetyBound_le_trackWidth system input period_pos)
  simp [safetyBound]
  omega

theorem clipped_epsilon_fixed_fits {period : Nat} (system : CyclicTag period)
    (input : List Bool) (period_pos : 0 < period) :
    (epsilonPrime.tail ++ repeatWord (period - 1) epsilonPrime).length ≤
      trackWidth system input := by
  refine le_trans ?_ (epsilon_fixed_fits system input period_pos)
  simp [repeatWord]
  omega

theorem appendant_fixed_fits {period : Nat} (system : CyclicTag period)
    (input : List Bool) (period_pos : 0 < period) (phase : Fin period) :
    (encodePrimes (system.appendant phase)).length ≤ trackWidth system input := by
  rw [encodePrimes_length]
  refine le_trans ?_ (safetyBound_le_trackWidth system input period_pos)
  have bounded := appendant_length_le_mass system phase
  simp [safetyBound]
  omega

/-- The block containing a Table 2 phase; `β = 10p` gives exactly `p` blocks. -/
def phaseBlock {period : Nat} (phase : Fin (deletionWidth period)) : Fin period :=
  ⟨phase / 10, by
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < 10)]
    exact lt_of_lt_of_le phase.isLt
      (Nat.le_of_eq (by simp [deletionWidth, Nat.mul_comm] : deletionWidth period = period * 10))⟩

/-- Program position attached to the `⟨1⟩` track in one ten-phase block. -/
def instructionAt {period : Nat} (phase : Fin (deletionWidth period)) : Fin period :=
  Fin.rev (phaseBlock phase)

/-- Table 2's input track. -/
def inputTrack {period : Nat} (system : CyclicTag period) (input : List Bool)
    (period_pos : 0 < period) : Vector TagLetter (trackWidth system input) :=
  ⟨padBetween (trackWidth system input) .c
      (List.replicate (deletionWidth period - 2) TagLetter.b ++ encodePrimes input)
      (repeatWord period epsilonPrime),
    padBetween_length TagLetter.c _ _ (by
      simpa using input_fixed_fits system input period_pos)⟩

theorem repeatWord_epsilonPrime_getLast? {period : Nat} (period_pos : 0 < period) :
    (repeatWord period epsilonPrime).getLast? = some .b := by
  obtain ⟨count, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt period_pos)
  change (repeatWord (count + 1) epsilonPrime).getLast? = some .b
  rw [repeatWord_succ_right, List.getLast?_append_of_ne_nil]
  · simp [epsilonPrime]
  · simp [epsilonPrime]

theorem inputTrack_getLast? {period : Nat} (system : CyclicTag period) (input : List Bool)
    (period_pos : 0 < period) :
    (inputTrack system input period_pos).val.getLast? = some .b := by
  unfold inputTrack padBetween
  rw [List.getLast?_append_of_ne_nil]
  · exact repeatWord_epsilonPrime_getLast? period_pos
  · intro empty
    have lengths := congrArg List.length empty
    simp at lengths
    omega

/-- Final column in every nonempty Table 2 track. -/
def lastColumn {period : Nat} (system : CyclicTag period) (input : List Bool) :
    Fin (trackWidth system input) :=
  ⟨trackWidth system input - 1, Nat.pred_lt (trackWidth_pos system input).ne'⟩

theorem inputTrack_last {period : Nat} (system : CyclicTag period) (input : List Bool)
    (period_pos : 0 < period) :
    (inputTrack system input period_pos).get (lastColumn system input) = .b := by
  let track := inputTrack system input period_pos
  have track_ne : track.val ≠ [] := by
    intro empty
    have lengths := congrArg List.length empty
    rw [track.property] at lengths
    simp at lengths
    exact (trackWidth_pos system input).ne' lengths
  have last_eq : track.val.getLast track_ne = .b := by
    have encoded := inputTrack_getLast? system input period_pos
    rw [List.getLast?_eq_getLast_of_ne_nil track_ne] at encoded
    exact Option.some.inj encoded
  let index : Fin track.val.length :=
    ⟨trackWidth system input - 1, by
      rw [track.property]
      exact Nat.pred_lt (trackWidth_pos system input).ne'⟩
  change track.val.get index = .b
  have index_eq : index =
      ⟨track.val.length - 1, Nat.pred_lt (List.length_pos.mpr track_ne).ne'⟩ := by
    apply Fin.ext
    simp [index, track.property]
  rw [index_eq, List.get_length_sub_one]
  exact last_eq

/-- The common `⟨ε⟩` and `⟨0⟩` track, with the wraparound track clipped on the left. -/
def epsilonTrack {period : Nat} (system : CyclicTag period) (input : List Bool)
    (period_pos : 0 < period) (wraps : Bool) : Vector TagLetter (trackWidth system input) :=
  if wraps then
    ⟨padRight (trackWidth system input) .c
        (epsilonPrime.tail ++ repeatWord (period - 1) epsilonPrime),
      padRight_length TagLetter.c _ (clipped_epsilon_fixed_fits system input period_pos)⟩
  else
    ⟨padRight (trackWidth system input) .c (repeatWord period epsilonPrime),
      padRight_length TagLetter.c _ (epsilon_fixed_fits system input period_pos)⟩

/-- The ordinary `⟨1⟩` track for one cyclic appendant. -/
def appendantTrack {period : Nat} (system : CyclicTag period) (input : List Bool)
    (period_pos : 0 < period) (phase : Fin period) (wraps : Bool) :
    Vector TagLetter (trackWidth system input) :=
  if wraps then
    ⟨padRight (trackWidth system input) .c (encodePrimes (system.appendant phase)).tail,
      padRight_length TagLetter.c _
        (le_trans (by simp)
          (appendant_fixed_fits system input period_pos phase))⟩
  else
    ⟨padRight (trackWidth system input) .c (encodePrimes (system.appendant phase)),
      padRight_length TagLetter.c _ (appendant_fixed_fits system input period_pos phase)⟩

/-- The exceptional `⟨1⟩` track that initiates the tag-system halting cascade. -/
def haltingTrack {period : Nat} (system : CyclicTag period) (input : List Bool) :
    Vector TagLetter (trackWidth system input) :=
  ⟨.b :: List.replicate (trackWidth system input - 1) .c, by
    have positive : 0 < trackWidth system input := by
      simp [trackWidth]
    simp
    omega⟩

/-- The exact length-`s` track assigned to one of the `β = 10p` phases in Table 2. -/
def tableTrack {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period)
    (phase : Fin (deletionWidth period)) : Vector TagLetter (trackWidth system input) :=
  if phase.val = deletionWidth period - 1 then
    inputTrack system input period_pos
  else
    match phase.val % 10 with
    | 1 => ⟨List.replicate (trackWidth system input) .c, by simp⟩
    | 3 =>
        let instruction := instructionAt phase
        if instruction = haltPhase then
          haltingTrack system input
        else
          appendantTrack system input period_pos instruction (instruction.val = 0)
    | 5 | 7 =>
        let instruction := instructionAt phase
        epsilonTrack system input period_pos (instruction.val = 0)
    | _ => ⟨List.replicate (trackWidth system input) .b, by simp⟩

/-- Final phase in the woven Table 2 word. -/
def lastPhase {period : Nat} (period_pos : 0 < period) : Fin (deletionWidth period) :=
  ⟨deletionWidth period - 1, Nat.pred_lt (deletionWidth_pos period_pos).ne'⟩

@[simp]
theorem tableTrack_lastPhase {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) :
    tableTrack system input haltPhase period_pos (lastPhase period_pos) =
      inputTrack system input period_pos := by
  simp [tableTrack, lastPhase]

/-- Whole `c`-appendant, including its final `b`, obtained by weaving the prescribed tracks. -/
def wholeAppendant {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) : List TagLetter :=
  weave (deletionWidth period) (trackWidth system input) (deletionWidth_pos period_pos)
    fun phase column => (tableTrack system input haltPhase period_pos phase).get column

/-- Restricted binary-tag output function emitted by the compiler. -/
def compiledOutput {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) : TagLetter → List TagLetter
  | .b => [.b]
  | .c => wholeAppendant system input haltPhase period_pos

theorem gridTrack_tableTrack {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period)
    (phase : Fin (deletionWidth period)) :
    gridTrack
        (fun row column => (tableTrack system input haltPhase period_pos row).get column)
        phase =
      (tableTrack system input haltPhase period_pos phase).val := by
  unfold gridTrack
  rw [← Mathlib.Vector.toList_ofFn]
  exact congrArg Mathlib.Vector.toList <| Mathlib.Vector.ext fun column => by simp

@[simp]
theorem wholeAppendant_length {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) :
    (wholeAppendant system input haltPhase period_pos).length =
      deletionWidth period * trackWidth system input := by
  simp [wholeAppendant]

theorem trackFront_length {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period)
    (phase : Fin (deletionWidth period)) (tail : List TagLetter)
    (phase_fits : phase.val ≤ tail.length) :
    ((wholeAppendant system input haltPhase period_pos).drop phase.val ++
        tail.take phase.val).length =
      trackWidth system input * deletionWidth period := by
  rw [List.length_append, List.length_drop, wholeAppendant_length, List.length_take,
    Nat.min_eq_left phase_fits]
  have phase_le : phase.val ≤ deletionWidth period * trackWidth system input := by
    exact (Nat.le_of_lt phase.isLt).trans
      (Nat.le_mul_of_pos_right _ (trackWidth_pos system input))
  rw [Nat.sub_add_cancel phase_le]
  exact Nat.mul_comm _ _

/-- Reading the compiler word at a selected shift emits exactly the prescribed Table 2 track. -/
theorem read_wholeAppendant_track {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period)
    (phase : Fin (deletionWidth period)) (tail : List TagLetter)
    (phase_fits : phase.val ≤ tail.length) :
    TagReaches (deletionWidth period)
        (compiledOutput system input haltPhase period_pos)
        ((wholeAppendant system input haltPhase period_pos).drop phase.val ++ tail)
        (tail.drop phase.val ++
          spell (compiledOutput system input haltPhase period_pos)
            (tableTrack system input haltPhase period_pos phase).val) := by
  let front :=
    (wholeAppendant system input haltPhase period_pos).drop phase.val ++ tail.take phase.val
  have front_length : front.length = trackWidth system input * deletionWidth period := by
    exact trackFront_length system input haltPhase period_pos phase tail phase_fits
  have enough : trackWidth system input * deletionWidth period ≤ front.length := by
    rw [front_length]
  have execution := tagReaches_chunks (deletionWidth period) (deletionWidth_pos period_pos)
    (compiledOutput system input haltPhase period_pos) (trackWidth system input) front
    (tail.drop phase.val) enough
  have samples := sampleHeads_weave (deletionWidth_pos period_pos)
    (trackWidth_pos system input)
    (fun row column => (tableTrack system input haltPhase period_pos row).get column)
    phase tail phase_fits
  change sampleHeads (deletionWidth period) (deletionWidth_pos period_pos)
      (trackWidth system input) front enough =
    gridTrack
      (fun row column => (tableTrack system input haltPhase period_pos row).get column) phase
    at samples
  rw [samples, gridTrack_tableTrack] at execution
  rw [← front_length, List.take_length] at execution
  simpa [front, List.append_assoc] using execution

theorem trackIndex_last {period : Nat} (system : CyclicTag period) (input : List Bool)
    (period_pos : 0 < period) :
    (trackIndex (lastPhase period_pos) (lastColumn system input)).val =
      deletionWidth period * trackWidth system input - 1 := by
  simp only [trackIndex, lastPhase, lastColumn, Fin.val_mk]
  have beta_split : deletionWidth period = deletionWidth period - 1 + 1 := by
    have := deletionWidth_pos period_pos
    omega
  have width_split : trackWidth system input = trackWidth system input - 1 + 1 := by
    have := trackWidth_pos system input
    omega
  have total_split :
      deletionWidth period * trackWidth system input =
        (deletionWidth period - 1) +
            deletionWidth period * (trackWidth system input - 1) + 1 := by
    calc
      deletionWidth period * trackWidth system input =
          deletionWidth period * (trackWidth system input - 1 + 1) :=
        congrArg (deletionWidth period * ·) width_split
      _ = deletionWidth period * (trackWidth system input - 1) +
          deletionWidth period := by ring
      _ = deletionWidth period * (trackWidth system input - 1) +
          (deletionWidth period - 1) + 1 := by omega
      _ = (deletionWidth period - 1) +
          deletionWidth period * (trackWidth system input - 1) + 1 := by ac_rfl
  omega

theorem wholeAppendant_get_lastTrack {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period) :
    (wholeAppendant system input haltPhase period_pos).get
        (Fin.cast (wholeAppendant_length system input haltPhase period_pos).symm
          (trackIndex (lastPhase period_pos) (lastColumn system input))) = .b := by
  simpa [wholeAppendant, inputTrack_last] using
    weave_get_track (deletionWidth_pos period_pos)
      (fun phase column => (tableTrack system input haltPhase period_pos phase).get column)
      (lastPhase period_pos) (lastColumn system input)

theorem wholeAppendant_getLast {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) :
    (wholeAppendant system input haltPhase period_pos).getLast (by
      intro empty
      have lengths := congrArg List.length empty
      rw [wholeAppendant_length] at lengths
      have beta_pos := deletionWidth_pos period_pos
      have width_pos := trackWidth_pos system input
      simp at lengths
      omega) = .b := by
  let word := wholeAppendant system input haltPhase period_pos
  have word_ne : word ≠ [] := by
    intro empty
    have lengths := congrArg List.length empty
    rw [wholeAppendant_length] at lengths
    have beta_pos := deletionWidth_pos period_pos
    have width_pos := trackWidth_pos system input
    simp at lengths
    omega
  let index : Fin word.length :=
    Fin.cast (wholeAppendant_length system input haltPhase period_pos).symm
      (trackIndex (lastPhase period_pos) (lastColumn system input))
  have index_eq : index =
      ⟨word.length - 1, Nat.pred_lt (List.length_pos.mpr word_ne).ne'⟩ := by
    apply Fin.ext
    simp [index, word, trackIndex_last, wholeAppendant_length]
  have at_index := wholeAppendant_get_lastTrack system input haltPhase period_pos
  change word.get index = .b at at_index
  rw [index_eq, List.get_length_sub_one] at at_index
  exact at_index

/-- The variable body consumed by the fixed-boundary source theorem. -/
def body {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) : List TagLetter :=
  (wholeAppendant system input haltPhase period_pos).dropLast

theorem wholeAppendant_eq_body_append {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period) :
    wholeAppendant system input haltPhase period_pos =
      body system input haltPhase period_pos ++ [.b] := by
  let word := wholeAppendant system input haltPhase period_pos
  have word_ne : word ≠ [] := by
    intro empty
    have lengths := congrArg List.length empty
    rw [wholeAppendant_length] at lengths
    have beta_pos := deletionWidth_pos period_pos
    have width_pos := trackWidth_pos system input
    simp at lengths
    omega
  have decomposition := List.dropLast_append_getLast word_ne
  rw [wholeAppendant_getLast system input haltPhase period_pos] at decomposition
  exact decomposition.symm

theorem compiledOutput_eq_tagOutput {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period) :
    compiledOutput system input haltPhase period_pos =
      tagOutput (body system input haltPhase period_pos) := by
  funext letter
  cases letter with
  | b => rfl
  | c =>
      exact wholeAppendant_eq_body_append system input haltPhase period_pos

/-- Track traversal stated with the downstream restricted tag output function. -/
theorem read_wholeAppendant_track_tagOutput {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period)
    (phase : Fin (deletionWidth period)) (tail : List TagLetter)
    (phase_fits : phase.val ≤ tail.length) :
    TagReaches (deletionWidth period)
        (tagOutput (body system input haltPhase period_pos))
        ((wholeAppendant system input haltPhase period_pos).drop phase.val ++ tail)
        (tail.drop phase.val ++
          spell (tagOutput (body system input haltPhase period_pos))
            (tableTrack system input haltPhase period_pos phase).val) := by
  rw [← compiledOutput_eq_tagOutput system input haltPhase period_pos]
  exact read_wholeAppendant_track system input haltPhase period_pos phase tail phase_fits

/-- Expand a Table 2 prime word into its binary-tag object. -/
def expandPrime {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (prime : List TagLetter) :
    List TagLetter :=
  spell (compiledOutput system input haltPhase period_pos) prime

/-- Shift-neutral object used to encode no cyclic-tag symbol. -/
def epsilonObject {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) : List TagLetter :=
  expandPrime system input haltPhase period_pos epsilonPrime

/-- Object encoding one cyclic-tag data bit. -/
def bitObject {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (bit : Bool) : List TagLetter :=
  expandPrime system input haltPhase period_pos (bitPrime bit)

theorem expandPrime_append {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (left right : List TagLetter) :
    expandPrime system input haltPhase period_pos (left ++ right) =
      expandPrime system input haltPhase period_pos left ++
        expandPrime system input haltPhase period_pos right := by
  exact spell_append _ _ _

theorem spell_repeatWord {α δ : Type*} (side : α → List δ) (count : Nat) (word : List α) :
    spell side (repeatWord count word) = repeatWord count (spell side word) := by
  induction count with
  | zero => simp [repeatWord, spell]
  | succ count ih =>
      rw [show repeatWord (count + 1) word = word ++ repeatWord count word by
        unfold repeatWord
        rw [List.replicate_succ]
        rfl]
      rw [spell_append, ih]
      unfold repeatWord
      rw [List.replicate_succ]
      rfl

theorem expandPrime_repeatWord {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period)
    (count : Nat) (word : List TagLetter) :
    expandPrime system input haltPhase period_pos (repeatWord count word) =
      repeatWord count (expandPrime system input haltPhase period_pos word) := by
  exact spell_repeatWord _ _ _

@[simp]
theorem expandPrime_replicate_b {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (count : Nat) :
    expandPrime system input haltPhase period_pos (List.replicate count .b) =
      List.replicate count .b := by
  induction count with
  | zero => rfl
  | succ count ih => simp [expandPrime, spell, compiledOutput, ih]

@[simp]
theorem expandPrime_replicate_c {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) (count : Nat) :
    expandPrime system input haltPhase period_pos (List.replicate count .c) =
      repeatWord count (wholeAppendant system input haltPhase period_pos) := by
  simp [expandPrime, repeatWord, spell, compiledOutput]

@[simp]
theorem epsilonObject_eq {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) :
    epsilonObject system input haltPhase period_pos =
      List.replicate 4 .b ++ wholeAppendant system input haltPhase period_pos ++
        List.replicate 6 .b := by
  simp [epsilonObject, expandPrime, epsilonPrime, spell_append, spell, compiledOutput,
    List.append_assoc]

theorem bitObject_eq_false {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) :
    bitObject system input haltPhase period_pos false =
      List.replicate 6 .b ++ wholeAppendant system input haltPhase period_pos ++
        List.replicate 4 .b := by
  simp [bitObject, expandPrime, bitPrime, spell_append, spell, compiledOutput,
    List.append_assoc]

theorem bitObject_eq_true {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) :
    bitObject system input haltPhase period_pos true =
      List.replicate 8 .b ++ wholeAppendant system input haltPhase period_pos ++
        List.replicate 2 .b := by
  simp [bitObject, expandPrime, bitPrime, spell_append, spell, compiledOutput,
    List.append_assoc]

theorem expandPrime_encodePrimes {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period)
    (bits : List Bool) :
    expandPrime system input haltPhase period_pos (encodePrimes bits) =
      (bits.map (bitObject system input haltPhase period_pos)).join := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      change expandPrime system input haltPhase period_pos
          (bitPrime bit ++ encodePrimes bits) = _
      rw [expandPrime, spell_append]
      change bitObject system input haltPhase period_pos bit ++
          expandPrime system input haltPhase period_pos (encodePrimes bits) = _
      rw [ih]
      rfl

theorem body_length {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) :
    (body system input haltPhase period_pos).length =
      (paddingRounds system input * deletionWidth period + 1) *
        (deletionWidth period - 1) := by
  rw [body, List.length_dropLast, wholeAppendant_length]
  unfold trackWidth
  have beta_split : deletionWidth period = deletionWidth period - 1 + 1 := by
    have := deletionWidth_pos period_pos
    omega
  have product_eq :
      deletionWidth period *
          (paddingRounds system input * (deletionWidth period - 1) + 1) =
        (paddingRounds system input * deletionWidth period + 1) *
            (deletionWidth period - 1) + 1 := by
    calc
      deletionWidth period *
          (paddingRounds system input * (deletionWidth period - 1) + 1) =
        paddingRounds system input * deletionWidth period * (deletionWidth period - 1) +
          deletionWidth period := by ring
      _ = paddingRounds system input * deletionWidth period * (deletionWidth period - 1) +
          (deletionWidth period - 1) + 1 := by omega
      _ = (paddingRounds system input * deletionWidth period + 1) *
          (deletionWidth period - 1) + 1 := by ring
  rw [product_eq]
  omega

/-- Every padded Table 2 output inhabits the arithmetic envelope consumed downstream. -/
def arithmeticEnvelope {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) : NearyArithmeticEnvelope where
  β := deletionWidth period
  body := body system input haltPhase period_pos
  paddingRounds := paddingRounds system input
  beta_large := deletionWidth_large period_pos
  body_length := body_length system input haltPhase period_pos

theorem initial_eq_drop_whole {period : Nat} (system : CyclicTag period) (input : List Bool)
    (haltPhase : Fin period) (period_pos : 0 < period) :
    (body system input haltPhase period_pos).drop (deletionWidth period - 1) ++ [.b] =
      (wholeAppendant system input haltPhase period_pos).drop (deletionWidth period - 1) := by
  rw [wholeAppendant_eq_body_append]
  rw [List.drop_append_of_le_length]
  exact NearyArithmeticEnvelope.body_long
    (arithmeticEnvelope system input haltPhase period_pos)

end MatrixMortality.Undecidability.NearyCompiler
