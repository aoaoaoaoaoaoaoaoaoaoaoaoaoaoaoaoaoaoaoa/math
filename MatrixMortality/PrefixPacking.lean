import MatrixMortality.WeightedTransducer

/-!
# Synchronizing prefix packing

A complete prefix decoder turns a family indexed by its leaves into one block generator per
alphabet letter. A synchronizing word aligns every block row before an encoded zero word, while
the root block of any packed zero word recovers a source zero. Thus a code with `s` internal
states and `a` letters transports `s * (a - 1) + 1` source generators in dimension `d` to `a`
generators in dimension `s * d`.
-/

namespace MatrixMortality.PrefixPacking

open scoped Matrix

/-- Run a deterministic prefix decoder, recording each completed leaf label. -/
def decode {State Letter Source : Type*}
    (next : State → Letter → State) (emission : State → Letter → Option Source) :
    State → List Letter → State × List Source
  | state, [] => (state, [])
  | state, letter :: word =>
      let tail := decode next emission (next state letter) word
      match emission state letter with
      | none => tail
      | some label => (tail.1, label :: tail.2)

/-- A total deterministic complete prefix code with an explicit synchronizer. The cardinality
law is the leaf count of a full `a`-ary prefix tree with `s` internal states. -/
structure CompleteCode (State Letter Source : Type*)
    [Fintype State] [Fintype Letter] [Fintype Source] where
  /-- Empty-prefix state. -/
  root : State
  /-- Total prefix-state transition. -/
  next : State → Letter → State
  /-- A leaf label is emitted exactly when a codeword completes. -/
  emission : State → Letter → Option Source
  /-- Codeword of each source label. -/
  code : Source → List Letter
  /-- Codewords contain at least one letter. -/
  code_nonempty : ∀ label, code label ≠ []
  /-- Decoding one codeword from the root emits exactly its label and returns to the root. -/
  decode_code : ∀ label, decode next emission root (code label) = (root, [label])
  /-- Word aligning every decoder state with the root. -/
  sync : List Letter
  /-- The synchronizer aligns every initial state. Its emissions are immaterial. -/
  sync_state : ∀ state, (decode next emission state sync).1 = root
  /-- Full-tree leaf count. -/
  source_card : Fintype.card Source = Fintype.card State * (Fintype.card Letter - 1) + 1

variable {State Letter Source Index R : Type*}
  [Fintype State] [DecidableEq State]
  [Fintype Letter] [Fintype Source]
  [Fintype Index] [DecidableEq Index]
  [CommSemiring R]

namespace CompleteCode

omit [DecidableEq State] in
/-- Decode two consecutive words by continuing from the intermediate state. -/
theorem decode_append (code : CompleteCode State Letter Source)
    (state : State) (left right : List Letter) :
    decode code.next code.emission state (left ++ right) =
      let first := decode code.next code.emission state left
      let second := decode code.next code.emission first.1 right
      (second.1, first.2 ++ second.2) := by
  induction left generalizing state with
  | nil => simp [decode]
  | cons letter left induction =>
      simp only [List.cons_append, decode]
      split <;> simp [induction]

/-- Concatenate the codewords of a source word. -/
def encode (code : CompleteCode State Letter Source) (word : List Source) : List Letter :=
  word.flatMap code.code

omit [DecidableEq State] in
/-- Encoding and then decoding a source word is exact. -/
theorem decode_encode (code : CompleteCode State Letter Source) (word : List Source) :
    decode code.next code.emission code.root (code.encode word) = (code.root, word) := by
  induction word with
  | nil => rfl
  | cons label word induction =>
      change
        decode code.next code.emission code.root (List.flatMap code.code word) =
          (code.root, word) at induction
      rw [encode, List.flatMap_cons, decode_append, code.decode_code]
      dsimp only
      rw [induction]
      rfl

omit [DecidableEq State] in
/-- A nonempty source word has a nonempty encoding. -/
theorem encode_ne_nil (code : CompleteCode State Letter Source) {word : List Source}
    (word_nonempty : word ≠ []) : code.encode word ≠ [] := by
  obtain ⟨label, word, rfl⟩ := List.exists_cons_of_ne_nil word_nonempty
  simp only [encode, List.flatMap_cons]
  exact List.append_ne_nil_of_left_ne_nil (code.code_nonempty label) _

/-- Matrix output attached to one prefix transition. -/
def output (code : CompleteCode State Letter Source)
    (source : Source → Square Index R) (state : State) (letter : Letter) : Square Index R :=
  match code.emission state letter with
  | none => 1
  | some label => source label

/-- Block-matrix transducer attached to a complete prefix code. -/
def machine (code : CompleteCode State Letter Source)
    (source : Source → Square Index R) : WeightedTransducer State Letter Index R where
  next := code.next
  output := code.output source

omit [DecidableEq State] in
/-- A transducer run emits the product of the source labels decoded along that run. -/
theorem machine_run (code : CompleteCode State Letter Source)
    (source : Source → Square Index R) (state : State) (word : List Letter) :
    (code.machine source).run state word =
      let decoded := decode code.next code.emission state word
      (decoded.1, wordProduct source decoded.2) := by
  induction word generalizing state with
  | nil => simp [decode, WeightedTransducer.run]
  | cons letter word induction =>
      rw [WeightedTransducer.run, induction]
      simp only [machine, output, decode]
      split <;> simp [wordProduct_cons]

omit [DecidableEq State] in
/-- A source zero remains zero after synchronizing any packed block row. -/
theorem sync_encode_output_zero (code : CompleteCode State Letter Source)
    (source : Source → Square Index R) (sourceWord : List Source)
    (source_zero : wordProduct source sourceWord = 0) (state : State) :
    ((code.machine source).run state (code.sync ++ code.encode sourceWord)).2 = 0 := by
  rw [machine_run, decode_append]
  dsimp only
  rw [code.sync_state, code.decode_encode]
  simp [wordProduct_append, source_zero]

/-- Prefix packing preserves and reflects mortality. The packed dimension is the product of the
internal-state count and the source dimension; `source_card` records the generator trade
`s * (a - 1) + 1 ↦ a`. -/
theorem machine_isMortal_iff_source [Nontrivial R] [Nonempty Index]
    (code : CompleteCode State Letter Source) (source : Source → Square Index R) :
    IsMortal (code.machine source).generator ↔ IsMortal source := by
  constructor
  · rintro ⟨letters, _, packed_zero⟩
    let decoded := decode code.next code.emission code.root letters
    have output_zero : ((code.machine source).run code.root letters).2 = 0 := by
      ext row column
      have entry_zero := congr_fun (congr_fun packed_zero (code.root, row))
        (((code.machine source).run code.root letters).1, column)
      rw [(code.machine source).wordProduct_apply letters code.root
        ((code.machine source).run code.root letters).1 row column, if_pos rfl] at entry_zero
      simpa using entry_zero
    have source_zero : wordProduct source decoded.2 = 0 := by
      rw [machine_run] at output_zero
      exact output_zero
    have decoded_nonempty : decoded.2 ≠ [] := by
      intro decoded_empty
      rw [decoded_empty, wordProduct_nil] at source_zero
      exact one_ne_zero source_zero
    exact ⟨decoded.2, decoded_nonempty, source_zero⟩
  · rintro ⟨sourceWord, sourceWord_nonempty, source_zero⟩
    let letters := code.sync ++ code.encode sourceWord
    refine ⟨letters, ?_, ?_⟩
    · exact List.append_ne_nil_of_right_ne_nil code.sync
        (code.encode_ne_nil sourceWord_nonempty)
    · ext ⟨start, row⟩ ⟨finish, column⟩
      rw [(code.machine source).wordProduct_apply letters start finish row column]
      split
      · rw [code.sync_encode_output_zero source sourceWord source_zero start]
        rfl
      · rfl

omit [DecidableEq State] [DecidableEq Index] in
theorem packed_state_card (_code : CompleteCode State Letter Source) :
    Fintype.card (State × Index) = Fintype.card State * Fintype.card Index := by
  simp

end CompleteCode

end MatrixMortality.PrefixPacking
