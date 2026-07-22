import MatrixMortality.TagQueue
import MatrixMortality.Undecidability.Tracks

/-!
# Exact finite tag executions

This file turns a list of fixed-width strokes into a concrete tag execution.  It also builds the
canonical stroke history that consumes a prescribed number of complete blocks from a word.  The
construction is the low-level bridge between Neary's fixed-stride tracks and tag-system dynamics.
-/

open Mathlib (Vector)

namespace MatrixMortality.Undecidability

/-- Reflexive-transitive reachability under one fixed-width tag step. -/
def TagReaches {α : Type*} (β : Nat) (output : α → List α) : List α → List α → Prop :=
  Relation.ReflTransGen (TagStep β output)

/-- A stroke history consumes its letters before touching the protected tail. -/
theorem tagReaches_history {α : Type*} {β : Nat} (output : α → List α)
    (history : List (Stroke α β)) (tail : List α) :
    TagReaches β output (consumed history ++ tail) (tail ++ produced output history) := by
  induction history generalizing tail with
  | nil =>
      simpa [TagReaches] using
        (Relation.ReflTransGen.refl : Relation.ReflTransGen (TagStep β output) tail tail)
  | cons stroke history ih =>
      apply Relation.ReflTransGen.head
      · refine ⟨stroke, consumed history ++ tail, ?_, rfl⟩
        simp [List.append_assoc]
      · simpa only [produced_cons, List.append_assoc] using
          ih (tail ++ output stroke.head)

/-- The first `width` symbols of a sufficiently long word, with their exact length retained. -/
def frontVector {α : Type*} (width : Nat) (word : List α) (fits : width ≤ word.length) :
    Vector α width :=
  ⟨word.take width, by simp [List.length_take, Nat.min_eq_left fits]⟩

/-- Regard a nonempty fixed-length vector as one tag stroke. -/
def vectorStroke {α : Type*} {width : Nat} (width_pos : 0 < width)
    (block : Vector α width) : Stroke α width where
  head := block.val.head (by
    intro empty
    have lengths := congrArg List.length empty
    rw [block.property] at lengths
    simp at lengths
    omega)
  wake := block.val.tail
  width := by
    rw [List.length_tail, block.property]
    omega

@[simp]
theorem vectorStroke_letters {α : Type*} {width : Nat} (width_pos : 0 < width)
    (block : Vector α width) :
    (vectorStroke width_pos block).letters = block.val := by
  exact List.head_cons_tail _ (by
    intro empty
    have lengths := congrArg List.length empty
    rw [block.property] at lengths
    simp at lengths
    omega)

/-- Canonical strokes consuming `count` complete blocks from the front of `word`. -/
def chunkHistory {α : Type*} (width : Nat) (width_pos : 0 < width) :
    (count : Nat) → (word : List α) → count * width ≤ word.length → List (Stroke α width)
  | 0, _, _ => []
  | count + 1, word, enough =>
      let frontFits : width ≤ word.length := by
        have : width ≤ (count + 1) * width := by
          rw [Nat.succ_mul]
          omega
        exact this.trans enough
      vectorStroke width_pos (frontVector width word frontFits) ::
        chunkHistory width width_pos count (word.drop width) (by
          rw [Nat.succ_mul] at enough
          rw [List.length_drop]
          omega)

@[simp]
theorem chunkHistory_length {α : Type*} (width : Nat) (width_pos : 0 < width)
    (count : Nat) (word : List α) (enough : count * width ≤ word.length) :
    (chunkHistory width width_pos count word enough).length = count := by
  induction count generalizing word with
  | zero => simp only [chunkHistory, List.length_nil]
  | succ count ih =>
      simp only [chunkHistory, List.length_cons]
      rw [ih]

/-- Canonical block strokes consume exactly the corresponding prefix. -/
theorem consumed_chunkHistory {α : Type*} (width : Nat) (width_pos : 0 < width)
    (count : Nat) (word : List α) (enough : count * width ≤ word.length) :
    consumed (chunkHistory width width_pos count word enough) = word.take (count * width) := by
  induction count generalizing word with
  | zero => simp only [chunkHistory, consumed_nil, Nat.zero_mul, List.take_zero]
  | succ count ih =>
      simp only [chunkHistory, consumed_cons, vectorStroke_letters, frontVector]
      rw [ih]
      rw [show (count + 1) * width = width + count * width by ring]
      rw [← List.take_append_drop width (word.take (width + count * width))]
      simp only [List.take_take, List.drop_take]
      congr 1
      · rw [Nat.min_eq_left]
        omega
      · congr 1
        omega

/-- Heads at successive multiples of `width` in a protected prefix. -/
def sampleHeads {α : Type*} (width : Nat) (width_pos : 0 < width) (count : Nat)
    (word : List α) (enough : count * width ≤ word.length) : List α :=
  List.ofFn fun index : Fin count =>
    word.get ⟨index.val * width,
      ((Nat.mul_lt_mul_right width_pos).mpr index.isLt).trans_le enough⟩

@[simp]
theorem sampleHeads_length {α : Type*} (width : Nat) (width_pos : 0 < width)
    (count : Nat) (word : List α) (enough : count * width ≤ word.length) :
    (sampleHeads width width_pos count word enough).length = count := by
  simp [sampleHeads]

theorem vectorStroke_frontVector_head {α : Type*} (width : Nat) (width_pos : 0 < width)
    (word : List α) (fits : width ≤ word.length) :
    (vectorStroke width_pos (frontVector width word fits)).head =
      word.get ⟨0, width_pos.trans_le fits⟩ := by
  obtain ⟨width, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt width_pos)
  cases word with
  | nil => simp at fits
  | cons head tail => simp [vectorStroke, frontVector]

/-- Execute one deterministic step from any queue containing a complete deletion block. -/
theorem tagReaches_one {α : Type*} (width : Nat) (width_pos : 0 < width)
    (output : α → List α) (word : List α) (enough : width ≤ word.length) :
    TagReaches width output word
      (word.drop width ++ output (word.get ⟨0, width_pos.trans_le enough⟩)) := by
  apply Relation.ReflTransGen.single
  refine ⟨vectorStroke width_pos (frontVector width word enough), word.drop width, ?_, ?_⟩
  · rw [vectorStroke_letters]
    exact (List.take_append_drop width word).symm
  · rw [vectorStroke_frontVector_head]

/-- The heads of the canonical strokes are precisely the fixed-stride samples. -/
theorem chunkHistory_heads {α : Type*} (width : Nat) (width_pos : 0 < width)
    (count : Nat) (word : List α) (enough : count * width ≤ word.length) :
    (chunkHistory width width_pos count word enough).map Stroke.head =
      sampleHeads width width_pos count word enough := by
  induction count generalizing word with
  | zero => simp [chunkHistory, sampleHeads]
  | succ count ih =>
      simp only [chunkHistory, List.map_cons, sampleHeads, List.ofFn_succ]
      rw [List.cons.injEq]
      constructor
      · simpa using vectorStroke_frontVector_head width width_pos word _
      · rw [ih]
        apply congrArg List.ofFn
        funext index
        rw [List.get_eq_getElem, List.get_eq_getElem]
        simp [Nat.succ_mul, Nat.add_comm]

/-- A complete protected prefix is consumed according to its fixed-stride heads. -/
theorem tagReaches_chunks {α : Type*} (width : Nat) (width_pos : 0 < width)
    (output : α → List α) (count : Nat) (word tail : List α)
    (enough : count * width ≤ word.length) :
    TagReaches width output (word.take (count * width) ++ tail)
      (tail ++ spell output (sampleHeads width width_pos count word enough)) := by
  have execution := tagReaches_history output
    (chunkHistory width width_pos count word enough) tail
  rw [consumed_chunkHistory] at execution
  have emitted : produced output (chunkHistory width width_pos count word enough) =
      spell output (sampleHeads width width_pos count word enough) := by
    unfold produced spell
    rw [show (chunkHistory width width_pos count word enough).map
          (fun stroke => output stroke.head) =
        ((chunkHistory width width_pos count word enough).map Stroke.head).map output by
          simp [List.map_map]]
    rw [chunkHistory_heads]
  rw [emitted] at execution
  exact execution

/-- Sampling a woven word after a phase offset recovers the corresponding prescribed track. -/
theorem sampleHeads_weave {α : Type*} {period columns : Nat} (period_pos : 0 < period)
    (columns_pos : 0 < columns) (grid : Fin period → Fin columns → α) (phase : Fin period)
    (tail : List α) (phase_fits : phase.val ≤ tail.length) :
    sampleHeads period period_pos columns
        ((weave period columns period_pos grid).drop phase.val ++ tail.take phase.val) (by
          rw [List.length_append, List.length_drop, weave_length, List.length_take,
            Nat.min_eq_left phase_fits]
          have phase_le : phase.val ≤ period * columns := by
            exact (Nat.le_of_lt phase.isLt).trans
              (Nat.le_mul_of_pos_right period columns_pos)
          rw [Nat.sub_add_cancel phase_le]
          simp [Nat.mul_comm]) =
      gridTrack grid phase := by
  unfold sampleHeads gridTrack
  apply congrArg List.ofFn
  funext column
  have sample_in_drop : column.val * period <
      ((weave period columns period_pos grid).drop phase.val).length := by
    rw [List.length_drop, weave_length]
    have next_column : (column.val + 1) * period ≤ columns * period :=
      Nat.mul_le_mul_right period (Nat.succ_le_of_lt column.isLt)
    have phase_before_next : column.val * period + phase.val < (column.val + 1) * period := by
      rw [Nat.succ_mul]
      omega
    rw [Nat.mul_comm period columns]
    omega
  rw [List.get_eq_getElem, List.getElem_append_left _ _ sample_in_drop]
  have source_index : phase.val + column.val * period <
      (weave period columns period_pos grid).length := by
    rw [weave_length, Nat.mul_comm period columns]
    have next_column : (column.val + 1) * period ≤ columns * period :=
      Nat.mul_le_mul_right period (Nat.succ_le_of_lt column.isLt)
    rw [Nat.succ_mul] at next_column
    omega
  rw [← List.getElem_drop' (weave period columns period_pos grid) source_index]
  have prescribed := weave_get_track period_pos grid phase column
  rw [List.get_eq_getElem] at prescribed
  simpa [trackIndex, Nat.add_comm, Nat.mul_comm] using prescribed

/-- A contiguous range of columns on one woven track. -/
def gridTrackSlice {α : Type*} {period columns : Nat}
    (grid : Fin period → Fin columns → α) (phase : Fin period)
    (start count : Nat) (fits : start + count ≤ columns) : List α :=
  List.ofFn fun index : Fin count =>
    grid phase ⟨start + index, lt_of_lt_of_le (Nat.add_lt_add_left index.isLt start) fits⟩

@[simp]
theorem gridTrackSlice_length {α : Type*} {period columns : Nat}
    (grid : Fin period → Fin columns → α) (phase : Fin period)
    (start count : Nat) (fits : start + count ≤ columns) :
    (gridTrackSlice grid phase start count fits).length = count := by
  simp [gridTrackSlice]

theorem gridTrackSlice_zero {α : Type*} {period columns : Nat}
    (grid : Fin period → Fin columns → α) (phase : Fin period) (count : Nat)
    (fits : count ≤ columns) :
    gridTrackSlice grid phase 0 count (by simpa using fits) =
      (gridTrack grid phase).take count := by
  apply List.ext_getElem
  · simp [gridTrackSlice, gridTrack, Nat.min_eq_left fits]
  · intro index slice_bound track_bound
    rw [List.getElem_take']
    simp [gridTrackSlice, gridTrack]

theorem gridTrackSlice_suffix {α : Type*} {period columns : Nat}
    (grid : Fin period → Fin columns → α) (phase : Fin period) (start : Nat)
    (start_le : start ≤ columns) :
    gridTrackSlice grid phase start (columns - start)
        (Nat.le_of_eq (Nat.add_sub_of_le start_le)) =
      (gridTrack grid phase).drop start := by
  apply List.ext_getElem
  · simp [gridTrackSlice, gridTrack]
  · intro index slice_bound track_bound
    rw [List.getElem_drop]
    simp [gridTrackSlice, gridTrack]

/-- Sampling complete blocks after a column-aligned drop recovers that track slice. -/
theorem sampleHeads_weave_slice {α : Type*} {period columns : Nat} (period_pos : 0 < period)
    (grid : Fin period → Fin columns → α) (phase : Fin period) (start count : Nat)
    (fits : start + count ≤ columns) (tail : List α)
    (enough : count * period ≤
      ((weave period columns period_pos grid).drop (phase.val + period * start) ++ tail).length) :
    sampleHeads period period_pos count
        ((weave period columns period_pos grid).drop (phase.val + period * start) ++ tail)
        enough =
      gridTrackSlice grid phase start count fits := by
  unfold sampleHeads gridTrackSlice
  apply congrArg List.ofFn
  funext index
  let column : Fin columns :=
    ⟨start + index, lt_of_lt_of_le (Nat.add_lt_add_left index.isLt start) fits⟩
  have source_index_lt :
      phase.val + period * (start + index.val) < period * columns := by
    have column_lt : start + index.val < columns := column.isLt
    have before_next :
        phase.val + period * (start + index.val) < period * (start + index.val + 1) := by
      rw [Nat.mul_succ]
      omega
    exact before_next.trans_le <|
      Nat.mul_le_mul_left period (Nat.succ_le_of_lt column_lt)
  have sample_in_drop : index.val * period <
      ((weave period columns period_pos grid).drop (phase.val + period * start)).length := by
    rw [List.length_drop, weave_length]
    rw [Nat.lt_sub_iff_add_lt]
    convert source_index_lt using 1
    all_goals ring
  rw [List.get_eq_getElem, List.getElem_append_left _ _ sample_in_drop]
  have source_index : phase.val + period * start + index.val * period <
      (weave period columns period_pos grid).length := by
    rw [weave_length]
    convert source_index_lt using 1
    all_goals ring
  rw [← List.getElem_drop' (weave period columns period_pos grid) source_index]
  have prescribed := weave_get_track period_pos grid phase column
  rw [List.get_eq_getElem] at prescribed
  simpa [trackIndex, column, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
    Nat.mul_add, Nat.mul_comm] using prescribed

/-- Rotate a track's repeated head padding through one deterministic terminal-letter step. -/
theorem tagReaches_rotate_terminal {α : Type*} (width : Nat) (width_pos : 0 < width)
    (output : α → List α) (letter : α) (track : List α)
    (track_long : width ≤ track.length)
    (prefix_eq : track.take (width - 1) = List.replicate (width - 1) letter)
    (terminal :
      track.getLast (List.ne_nil_of_length_pos (width_pos.trans_le track_long)) = letter)
    (letter_output : output letter = [letter]) :
    TagReaches width output
      ([letter] ++ spell output track.dropLast)
      (spell output (track.drop (width - 1))) := by
  let front := track.dropLast
  let middle := front.drop (width - 1)
  have front_length : front.length = track.length - 1 := List.length_dropLast track
  have prefix_fits : width - 1 ≤ front.length := by
    rw [front_length]
    omega
  have front_prefix : front.take (width - 1) = List.replicate (width - 1) letter := by
    change track.dropLast.take (width - 1) = _
    rw [List.dropLast_eq_take, List.take_take, Nat.min_eq_left]
    · exact prefix_eq
    · omega
  have front_decomposition :
      front = List.replicate (width - 1) letter ++ middle := by
    rw [← front_prefix]
    exact (List.take_append_drop (width - 1) front).symm
  have track_decomposition : front ++ [letter] = track := by
    simpa [front, terminal] using
      List.dropLast_append_getLast
        (List.ne_nil_of_length_pos (width_pos.trans_le track_long))
  have source_shape :
      [letter] ++ spell output front =
        List.replicate width letter ++ spell output middle := by
    rw [front_decomposition, spell_append]
    have spell_replicate :
        spell output (List.replicate (width - 1) letter) =
          List.replicate (width - 1) letter := by
      induction width - 1 with
      | zero => rfl
      | succ count ih => simp [List.replicate_succ, spell, letter_output, ih]
    rw [spell_replicate]
    have replicate_width :
        List.replicate width letter = letter :: List.replicate (width - 1) letter := by
      conv_lhs =>
        rw [show width = (width - 1) + 1 by omega]
        rw [List.replicate_succ]
    rw [replicate_width]
    simp [List.append_assoc]
  have source_long : width ≤ ([letter] ++ spell output front).length := by
    rw [source_shape]
    simp
  have step := tagReaches_one width width_pos output
    ([letter] ++ spell output front) source_long
  have source_head :
      ([letter] ++ spell output front).get ⟨0, width_pos.trans_le source_long⟩ = letter := by
    simp
  rw [source_head, letter_output, source_shape] at step
  have target_shape :
      spell output (track.drop (width - 1)) = spell output middle ++ [letter] := by
    rw [← track_decomposition]
    rw [List.drop_append_of_le_length prefix_fits]
    rw [spell_append]
    simp [middle, spell, letter_output]
  rw [target_shape, source_shape]
  simpa using step

end MatrixMortality.Undecidability
