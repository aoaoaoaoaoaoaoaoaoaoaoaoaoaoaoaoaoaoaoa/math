import MatrixMortality.HistoryFracture

/-!
# Periodic null histories in three states

The width-three body `bcbb` has terminal role language `P₀Q*`. This file proves that grammar,
cuts it out on the entire paired-control free monoid with a singular three-state positional
decoder, and clears the resulting rank-one separator to four explicit integral matrices.
-/

namespace MatrixMortality

namespace PeriodicHistory

open scoped Matrix

/-- The width-three Neary body `bcbb`. -/
def bcbbBody : List TagLetter := [.b, .c, .b, .b]

/-- A width-three stroke assembled from its head and two wake letters. -/
def stroke₃ (head wake₁ wake₂ : TagLetter) : Stroke TagLetter 3 :=
  ⟨head, [wake₁, wake₂], by simp⟩

/-- The stroke `bbb`. -/
def strokeBBB : Stroke TagLetter 3 := stroke₃ .b .b .b

/-- The stroke `cbb`. -/
def strokeCBB : Stroke TagLetter 3 := stroke₃ .c .b .b

/-- The stroke `cbc`. -/
def strokeCBC : Stroke TagLetter 3 := stroke₃ .c .b .c

/-- A null history preserves the boundary queue `[b]` under `bcbb` production. -/
def bcbbNull (history : List (Stroke TagLetter 3)) : Prop :=
  consumed history ++ [.b] = [.b] ++ produced (tagOutput bcbbBody) history

private def wakes (history : List (Stroke TagLetter 3)) : List TagLetter :=
  (history.map Stroke.wake).join

private theorem countC_consumed (history : List (Stroke TagLetter 3)) :
    (consumed history).count .c =
      (history.map Stroke.head).count .c + (wakes history).count .c := by
  induction history with
  | nil => simp [consumed, wakes]
  | cons stroke history induction =>
      rcases stroke with ⟨head, wake, width⟩
      cases head <;>
        simp [consumed_cons, wakes, Stroke.letters, induction, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm]

private theorem countC_produced (history : List (Stroke TagLetter 3)) :
    (produced (tagOutput bcbbBody) history).count .c =
      (history.map Stroke.head).count .c := by
  induction history with
  | nil => rfl
  | cons stroke history induction =>
      rcases stroke with ⟨head, wake, width⟩
      rw [produced_cons, List.count_append]
      cases head
      · simpa [bcbbBody, tagOutput, nearyBody] using induction
      · have induction' :
            (produced (tagOutput [TagLetter.b, TagLetter.c, TagLetter.b, TagLetter.b])
                history).count .c = (history.map Stroke.head).count .c := by
          simpa [bcbbBody] using induction
        simp [bcbbBody, tagOutput, nearyBody, induction', Nat.add_comm]

private theorem consumed_length (history : List (Stroke TagLetter 3)) :
    (consumed history).length = 3 * history.length := by
  induction history with
  | nil => rfl
  | cons stroke history induction =>
      rw [consumed_cons, List.length_append, Stroke.length_letters, induction,
        List.length_cons]
      omega

private theorem produced_length (history : List (Stroke TagLetter 3)) :
    (produced (tagOutput bcbbBody) history).length =
      history.length + 4 * (history.map Stroke.head).count .c := by
  induction history with
  | nil => rfl
  | cons stroke history induction =>
      rw [produced_cons, List.length_append, induction, List.length_cons, List.map_cons]
      cases stroke.head <;> simp [bcbbBody, tagOutput, nearyBody] <;> omega

private theorem bcbbNull_wakes (history : List (Stroke TagLetter 3))
    (null : bcbbNull history) : (wakes history).count .c = 0 := by
  have counts := congrArg (List.count TagLetter.c) null
  simp only [bcbbNull, List.count_append, List.count_cons, List.count_nil,
    countC_consumed, countC_produced] at counts
  omega

private theorem stroke_eq_B_or_C {history : List (Stroke TagLetter 3)}
    (null : bcbbNull history) {stroke : Stroke TagLetter 3} (member : stroke ∈ history) :
    stroke = strokeBBB ∨ stroke = strokeCBB := by
  have wake_count := bcbbNull_wakes history null
  have wake_no_c : TagLetter.c ∉ stroke.wake := by
    intro wake_c
    have c_in_wakes : TagLetter.c ∈ wakes history := by
      simp only [wakes, List.mem_join, List.mem_map]
      exact ⟨stroke.wake, ⟨stroke, member, rfl⟩, wake_c⟩
    exact (List.count_eq_zero.mp wake_count) c_in_wakes
  rcases stroke with ⟨head, wake, width⟩
  have wake_length : wake.length = 2 := by omega
  obtain ⟨wake₁, wake₂, rfl⟩ := List.length_eq_two.mp wake_length
  have wake₁_b : wake₁ = .b := by
    cases wake₁
    · rfl
    · exact False.elim (wake_no_c (by simp))
  have wake₂_b : wake₂ = .b := by
    cases wake₂
    · rfl
    · exact False.elim (wake_no_c (by simp))
  subst wake₁
  subst wake₂
  cases head <;> simp [strokeBBB, strokeCBB, stroke₃]

private theorem bcbbNull_length (history : List (Stroke TagLetter 3))
    (null : bcbbNull history) :
    history.length = 2 * (history.map Stroke.head).count .c := by
  have lengths := congrArg List.length null
  simp only [bcbbNull, List.length_append, List.length_cons, List.length_nil,
    consumed_length, produced_length] at lengths
  omega

private theorem exists_C_of_ne_nil {history : List (Stroke TagLetter 3)}
    (null : bcbbNull history) (nonempty : history ≠ []) : strokeCBB ∈ history := by
  have count_pos : 0 < (history.map Stroke.head).count .c := by
    have length_pos := List.length_pos.mpr nonempty
    have := bcbbNull_length history null
    omega
  have c_mem : TagLetter.c ∈ history.map Stroke.head :=
    List.count_pos_iff_mem.mp count_pos
  obtain ⟨source, source_mem, source_head⟩ := List.mem_map.mp c_mem
  have source_C := stroke_eq_B_or_C null source_mem
  rcases source_C with source_B | source_C
  · subst source
    simp [strokeBBB, stroke₃] at source_head
  · simpa [source_C] using source_mem

private theorem split_first_C {history : List (Stroke TagLetter 3)}
    (all : ∀ stroke ∈ history, stroke = strokeBBB ∨ stroke = strokeCBB)
    (exists_C : strokeCBB ∈ history) :
    ∃ prefixLength tail,
      history = List.replicate prefixLength strokeBBB ++ strokeCBB :: tail := by
  induction history with
  | nil => simp at exists_C
  | cons stroke history induction =>
      rcases all stroke (by simp) with stroke_B | stroke_C
      · subst stroke
        have tail_C : strokeCBB ∈ history := by
          simpa [strokeBBB, strokeCBB, stroke₃] using exists_C
        obtain ⟨prefixLength, tail, split⟩ :=
          induction (fun candidate member => all candidate (by simp [member])) tail_C
        refine ⟨prefixLength + 1, tail, ?_⟩
        simp [split, List.replicate_succ]
      · subst stroke
        exact ⟨0, history, by simp⟩

private def leadingB (word : List TagLetter) : Nat :=
  (word.takeWhile fun letter => letter == .b).length

@[simp] private theorem leadingB_replicate_c (length : Nat) (tail : List TagLetter) :
    leadingB (List.replicate length .b ++ .c :: tail) = length := by
  induction length with
  | zero => simp [leadingB]
  | succ length induction => simp [leadingB, List.replicate_succ, induction]

@[simp] private theorem consumed_replicate_B (length : Nat) :
    consumed (List.replicate length strokeBBB) = List.replicate (3 * length) .b := by
  induction length with
  | zero => rfl
  | succ length induction =>
      rw [List.replicate_succ, consumed_cons, induction]
      rw [show 3 * (length + 1) = 3 + 3 * length by omega, List.replicate_add]
      rfl

@[simp] private theorem produced_replicate_B (length : Nat) :
    produced (tagOutput bcbbBody) (List.replicate length strokeBBB) =
      List.replicate length .b := by
  induction length with
  | zero => rfl
  | succ length induction =>
      rw [List.replicate_succ, produced_cons, induction]
      rw [List.replicate_succ]
      rfl

private theorem consumed_append (left right : List (Stroke TagLetter 3)) :
    consumed (left ++ right) = consumed left ++ consumed right := by
  simp [consumed, List.map_append]

private theorem produced_append (left right : List (Stroke TagLetter 3)) :
    produced (tagOutput bcbbBody) (left ++ right) =
      produced (tagOutput bcbbBody) left ++ produced (tagOutput bcbbBody) right := by
  simp [produced, List.map_append]

private theorem leadingB_null_left (prefixLength : Nat) (tail : List TagLetter) :
    leadingB
      (List.replicate (3 * prefixLength) .b ++ [.c, .b, .b] ++ tail) =
      3 * prefixLength := by
  simp [List.append_assoc]

@[simp] private theorem leadingB_null_right (prefixLength : Nat) (tail : List TagLetter) :
    leadingB
      (.b :: (List.replicate prefixLength .b ++
        .b :: .c :: .b :: .b :: .b :: tail)) =
      prefixLength + 2 := by
  induction prefixLength with
  | zero => simp [leadingB]
  | succ prefixLength induction =>
      simp [List.replicate_succ, leadingB, induction, Nat.add_assoc]

private theorem bcbbNull_peel (history : List (Stroke TagLetter 3))
    (null : bcbbNull history) :
    history = [] ∨ ∃ tail,
      history = strokeBBB :: strokeCBB :: tail ∧ bcbbNull tail := by
  by_cases empty : history = []
  · exact Or.inl empty
  · right
    have all : ∀ stroke ∈ history, stroke = strokeBBB ∨ stroke = strokeCBB :=
      fun _ member => stroke_eq_B_or_C null member
    obtain ⟨prefixLength, tail, split⟩ :=
      split_first_C all (exists_C_of_ne_nil null empty)
    have normalized :
        List.replicate (3 * prefixLength) .b ++ [.c, .b, .b] ++
              consumed tail ++ [.b] =
          [.b] ++ List.replicate prefixLength .b ++ [.b, .c, .b, .b, .b] ++
            produced (tagOutput bcbbBody) tail := by
      rw [split] at null
      change consumed (List.replicate prefixLength strokeBBB ++ strokeCBB :: tail) ++
          [.b] = [.b] ++ produced (tagOutput bcbbBody)
            (List.replicate prefixLength strokeBBB ++ strokeCBB :: tail) at null
      rw [consumed_append, produced_append, consumed_replicate_B, produced_replicate_B,
        consumed_cons, produced_cons] at null
      simpa [strokeCBB, stroke₃, Stroke.letters, bcbbBody, tagOutput, nearyBody,
        List.append_assoc] using null
    have lead_equality : 3 * prefixLength = prefixLength + 2 := by
      simpa [List.append_assoc, leadingB_null_left] using congrArg leadingB normalized
    have prefix_one : prefixLength = 1 := by omega
    subst prefixLength
    refine ⟨tail, ?_, ?_⟩
    · simpa [strokeBBB, List.replicate_succ] using split
    · simpa [bcbbNull] using normalized

/-- The `k`-fold null-history ray `(bbb,cbb)^k`. -/
def bcbbNullRay : Nat → List (Stroke TagLetter 3)
  | 0 => []
  | k + 1 => strokeBBB :: strokeCBB :: bcbbNullRay k

@[simp] theorem bcbbNull_pair_iff (tail : List (Stroke TagLetter 3)) :
    bcbbNull (strokeBBB :: strokeCBB :: tail) ↔ bcbbNull tail := by
  simp [bcbbNull, strokeBBB, strokeCBB, stroke₃, Stroke.letters, bcbbBody,
    tagOutput, nearyBody, List.append_assoc]

@[simp] theorem bcbbNull_ray (k : Nat) : bcbbNull (bcbbNullRay k) := by
  induction k with
  | zero => rfl
  | succ k induction => simpa [bcbbNullRay] using induction

private theorem bcbbNull_classify (history : List (Stroke TagLetter 3))
    (null : bcbbNull history) : ∃ k, history = bcbbNullRay k := by
  obtain empty | ⟨tail, split, tailNull⟩ := bcbbNull_peel history null
  · exact ⟨0, by simp [empty, bcbbNullRay]⟩
  · obtain ⟨k, tail_eq⟩ := bcbbNull_classify tail tailNull
    exact ⟨k + 1, by simp [split, tail_eq, bcbbNullRay]⟩
termination_by history.length
decreasing_by
  rw [split]
  simp only [List.length_cons]
  omega

theorem bcbbNull_iff (history : List (Stroke TagLetter 3)) :
    bcbbNull history ↔ ∃ k, history = bcbbNullRay k := by
  constructor
  · exact bcbbNull_classify history
  · rintro ⟨k, rfl⟩
    exact bcbbNull_ray k

theorem terminal_match_tileHistory_iff (β : Nat) (body : List TagLetter)
    (β_pos : 0 < β) (first : Stroke TagLetter β)
    (history : List (Stroke TagLetter β)) :
    spell (nearyUpper β) (tileHistory (first :: history)) ++ nearyMarker β =
        spell (nearyLower β body) (tileHistory (first :: history)) ↔
      consumed (first :: history) ++ [.b] =
        .c :: nearyBody body first.head ++ [.b] ++
          produced (tagOutput body) history := by
  constructor
  · intro terminal
    have bits := congrArg (fun word => word ++ [true]) terminal
    change (spell (nearyUpper β) (tileHistory (first :: history)) ++ nearyMarker β) ++
        [true] = spell (nearyLower β body) (tileHistory (first :: history)) ++ [true] at bits
    rw [spell_nearyUpper_tileHistory, spell_nearyLower_tileHistory_append_true] at bits
    have encoded :
        tagEncode β (consumed (first :: history) ++ [.b]) =
          tagEncode β
            (.c :: nearyBody body first.head ++ [.b] ++
              produced (tagOutput body) history) := by
      simpa [tagEncode_append, marker_append_true, List.append_assoc] using bits
    exact tagEncode_injective β β_pos encoded
  · intro semantic
    apply List.append_cancel_right (bs := [true])
    rw [spell_nearyUpper_tileHistory, spell_nearyLower_tileHistory_append_true]
    calc
      (tagEncode β (consumed (first :: history)) ++ nearyMarker β) ++ [true] =
          tagEncode β (consumed (first :: history)) ++ (nearyMarker β ++ [true]) := by
            simp [List.append_assoc]
      _ = tagEncode β (consumed (first :: history)) ++ tagEncode β [.b] := by
        rw [marker_append_true]
      _ = tagEncode β (consumed (first :: history) ++ [.b]) :=
        (tagEncode_append β _ _).symm
      _ = tagEncode β
          (.c :: nearyBody body first.head ++ [.b] ++
            produced (tagOutput body) history) := congrArg _ semantic

private def bcbbTail (history : List (Stroke TagLetter 3)) : Prop :=
  consumed history ++ [.b] = [.b, .b, .b] ++
    produced (tagOutput bcbbBody) history

private theorem bcbbTail_iff (history : List (Stroke TagLetter 3)) :
    bcbbTail history ↔ ∃ tail, history = strokeBBB :: tail ∧ bcbbNull tail := by
  cases history with
  | nil => simp [bcbbTail]
  | cons first tail =>
      rcases first with ⟨head, wake, width⟩
      have wake_length : wake.length = 2 := by omega
      obtain ⟨wake₁, wake₂, rfl⟩ := List.length_eq_two.mp wake_length
      cases head <;> cases wake₁ <;> cases wake₂ <;>
        simp [bcbbTail, bcbbNull, consumed_cons, produced_cons, strokeBBB, stroke₃,
          Stroke.letters, bcbbBody, tagOutput, nearyBody, List.append_assoc]

/-- The complete terminal history `cbc,bbb,(bbb,cbb)^k`. -/
def bcbbTerminalHistory (k : Nat) : List (Stroke TagLetter 3) :=
  strokeCBC :: strokeBBB :: bcbbNullRay k

theorem bcbb_terminal_match_iff (word : List NearyTile) :
    spell (nearyUpper 3) word ++ nearyMarker 3 = spell (nearyLower 3 bcbbBody) word ↔
      ∃ k, word = tileHistory (bcbbTerminalHistory k) := by
  constructor
  · intro terminal
    obtain ⟨history, rfl⟩ :=
      tileHistory_of_terminal_match 3 bcbbBody (by decide) word terminal
    have nonempty : history ≠ [] := by
      intro empty
      subst history
      simp [spell, nearyMarker] at terminal
    obtain ⟨first, tail, rfl⟩ := List.exists_cons_of_ne_nil nonempty
    have semantic :=
      (terminal_match_tileHistory_iff 3 bcbbBody (by decide) first tail).mp terminal
    rcases first with ⟨head, wake, width⟩
    have wake_length : wake.length = 2 := by omega
    obtain ⟨wake₁, wake₂, rfl⟩ := List.length_eq_two.mp wake_length
    cases head <;> cases wake₁ <;> cases wake₂ <;>
      simp [consumed_cons, produced_cons, bcbbBody, tagOutput, nearyBody,
        Stroke.letters, List.append_assoc] at semantic
    obtain ⟨nullTail, tail_eq, null⟩ := (bcbbTail_iff tail).mp semantic
    obtain ⟨k, null_eq⟩ := (bcbbNull_iff nullTail).mp null
    refine ⟨k, ?_⟩
    simp [bcbbTerminalHistory, strokeCBC, stroke₃, tail_eq, null_eq]
  · rintro ⟨k, rfl⟩
    apply (terminal_match_tileHistory_iff 3 bcbbBody (by decide)
      strokeCBC (strokeBBB :: bcbbNullRay k)).mpr
    simpa [strokeCBC, strokeBBB, stroke₃, Stroke.letters, consumed_cons, produced_cons,
      bcbbBody, tagOutput, nearyBody, bcbbNull, List.append_assoc] using bcbbNull_ray k

/-! ## Periodic affine decoder -/

/-- Most-significant-digit-first base-five code of a role word. -/
def forwardHistoryCode (word : List NearyTile) : Nat := historyCode word.reverse

@[simp] theorem forwardHistoryCode_nil : forwardHistoryCode [] = 0 := rfl

@[simp] theorem forwardHistoryCode_cons (tile : NearyTile) (word : List NearyTile) :
    forwardHistoryCode (tile :: word) =
      forwardHistoryCode word + 5 ^ word.length * historyDigit tile := by
  simp [forwardHistoryCode, historyCode, List.map_append, Nat.ofDigits_append,
    Nat.ofDigits]

theorem forwardHistoryCode_append (left right : List NearyTile) :
    forwardHistoryCode (left ++ right) =
      5 ^ right.length * forwardHistoryCode left + forwardHistoryCode right := by
  simp [forwardHistoryCode, historyCode, List.map_append, Nat.ofDigits_append,
    Nat.mul_comm, Nat.add_comm]

theorem forwardHistoryCode_injective : Function.Injective forwardHistoryCode := by
  intro left right equality
  apply List.reverse_injective
  exact historyCode_injective equality

/-- Singular data controls retaining the positional scale discarded by `historyDataMatrix`. -/
def periodicDataMatrix (R : Type*) [CommRing R] : TagLetter → Matrix (Fin 3) (Fin 3) R
  | .b =>
      !![(1 : R), -1, 2;
         0, 0, -5;
         0, 0, 5]
  | .c =>
      !![(1 : R), -1, 3;
         0, 0, -5;
         0, 0, 5]

/-- The two singular data controls and the phase toggle. -/
def periodicGenerator (R : Type*) [CommRing R] :
    PairedControl → Matrix (Fin 3) (Fin 3) R
  | .data letter => periodicDataMatrix R letter
  | .toggle => historyToggleMatrix R

/-- Initial affine offset, phase sign, and positional scale. -/
def periodicColumn (R : Type*) [CommRing R] (κ : R) : Fin 3 → R := ![κ, 1, 1]

/-- Phase-blind row comparing the affine code with its positional scale. -/
def periodicRow (R : Type*) [CommRing R] (α : R) : Fin 3 → R := ![1, 0, -α]

/-- Decoded affine code, signed scale, and unsigned scale. -/
def periodicState (R : Type*) [CommRing R] (κ : R)
    (decoded : PairPhase × List NearyTile) : Fin 3 → R :=
  ![κ + forwardHistoryCode decoded.2,
    historyPhaseSign R decoded.1 * (5 : R) ^ decoded.2.length,
    (5 : R) ^ decoded.2.length]

theorem periodicProduct_mulVec_column (R : Type*) [CommRing R] (κ : R)
    (word : List PairedControl) :
    wordProduct (periodicGenerator R) word *ᵥ periodicColumn R κ =
      periodicState R κ (suffixDecode word) := by
  induction word with
  | nil =>
      ext coordinate
      fin_cases coordinate <;>
        simp [wordProduct, periodicColumn, periodicState, suffixDecode, historyPhaseSign]
  | cons control word induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec, induction]
      cases decoded_eq : suffixDecode word with
      | mk phase decoded =>
          cases control with
          | toggle =>
              cases phase <;>
                ext coordinate <;>
                fin_cases coordinate <;>
                simp [periodicGenerator, historyToggleMatrix, periodicState, suffixDecode,
                  decoded_eq, PairPhase.flip, historyPhaseSign, Matrix.mulVec,
                  Matrix.dotProduct, Fin.sum_univ_succ]
          | data letter =>
              cases phase <;> cases letter <;>
                ext coordinate <;>
                fin_cases coordinate <;>
                simp [periodicGenerator, periodicDataMatrix, periodicState, suffixDecode,
                  decoded_eq, PairPhase.tile, historyPhaseSign, historyDigit, Matrix.mulVec,
                  Matrix.dotProduct, Fin.sum_univ_succ, pow_succ'] <;>
                ring

/-- Scalar cut out by one affine row section of the positional decoder. -/
def periodicCoefficient (κ α : ℚ) (word : List PairedControl) : ℚ :=
  linearCoefficient (periodicGenerator ℚ) (periodicRow ℚ α) (periodicColumn ℚ κ) word

theorem periodicCoefficient_eq (κ α : ℚ) (word : List PairedControl) :
    periodicCoefficient κ α word =
      κ + forwardHistoryCode (decodePairedWord word) -
        α * 5 ^ (decodePairedWord word).length := by
  rw [periodicCoefficient, linearCoefficient, periodicProduct_mulVec_column]
  cases decoded_eq : suffixDecode word with
  | mk phase decoded =>
      cases phase <;>
        simp [periodicRow, periodicState, decodePairedWord, decoded_eq, Matrix.dotProduct,
          Fin.sum_univ_succ, sub_eq_add_neg]

/-- The fixed role prefix `P₀`. -/
def bcbbRolePrefix : List NearyTile := tileHistory [strokeCBC, strokeBBB]

/-- The repeated role block `Q`. -/
def bcbbRolePeriod : List NearyTile := tileHistory [strokeBBB, strokeCBB]

/-- The periodic role ray `P₀Q^k`. -/
def bcbbRoleRay : Nat → List NearyTile
  | 0 => bcbbRolePrefix
  | k + 1 => bcbbRoleRay k ++ bcbbRolePeriod

@[simp] theorem bcbbRolePrefix_length : bcbbRolePrefix.length = 6 := by decide

@[simp] theorem bcbbRolePeriod_length : bcbbRolePeriod.length = 6 := by decide

@[simp] theorem bcbbRolePrefix_code : forwardHistoryCode bcbbRolePrefix = 8668 := by decide

@[simp] theorem bcbbRolePeriod_code : forwardHistoryCode bcbbRolePeriod = 5443 := by decide

private theorem bcbbNullRay_succ_append (k : Nat) :
    bcbbNullRay (k + 1) = bcbbNullRay k ++ [strokeBBB, strokeCBB] := by
  induction k with
  | zero => rfl
  | succ k induction =>
      have commute :
          [strokeBBB, strokeCBB] ++ bcbbNullRay k =
            bcbbNullRay k ++ [strokeBBB, strokeCBB] := by
        simpa [bcbbNullRay] using induction
      simpa [bcbbNullRay] using commute

private theorem tileHistory_append (left right : List (Stroke TagLetter 3)) :
    tileHistory (left ++ right) = tileHistory left ++ tileHistory right := by
  simp [tileHistory, List.map_append]

theorem bcbbRoleRay_eq_terminal (k : Nat) :
    bcbbRoleRay k = tileHistory (bcbbTerminalHistory k) := by
  induction k with
  | zero => rfl
  | succ k induction =>
      rw [bcbbRoleRay, induction]
      have terminal_succ :
          bcbbTerminalHistory (k + 1) =
            bcbbTerminalHistory k ++ [strokeBBB, strokeCBB] := by
        simp [bcbbTerminalHistory, bcbbNullRay_succ_append, List.append_assoc]
      rw [terminal_succ, tileHistory_append]
      rfl

@[simp] theorem bcbbRoleRay_length (k : Nat) : (bcbbRoleRay k).length = 6 * (k + 1) := by
  induction k with
  | zero => decide
  | succ k induction => simp [bcbbRoleRay, induction]; omega

/-- Fixed point of appending the base-five period code `5443`. -/
def bcbbKappa : ℚ := 5443 / 15624

/-- Affine slope through the fixed prefix and periodic tail. -/
def bcbbAlpha : ℚ := 5417371 / 9765000

/-- The affine positional scalar on a decoded role word. -/
def bcbbAffine (word : List NearyTile) : ℚ :=
  bcbbKappa + forwardHistoryCode word - bcbbAlpha * 5 ^ word.length

@[simp] theorem bcbbAffine_ray (k : Nat) : bcbbAffine (bcbbRoleRay k) = 0 := by
  induction k with
  | zero => norm_num [bcbbAffine, bcbbKappa, bcbbAlpha, bcbbRoleRay]
  | succ k induction =>
      rw [bcbbRoleRay, bcbbAffine, forwardHistoryCode_append, List.length_append,
        bcbbRolePeriod_length, bcbbRolePeriod_code, pow_add]
      rw [bcbbAffine] at induction
      norm_num [bcbbKappa, bcbbAlpha] at induction ⊢
      linarith

private theorem bcbbAffine_nat_eq (word : List NearyTile) (zero : bcbbAffine word = 0) :
    15625 * (15624 * forwardHistoryCode word + 5443) =
      5 ^ word.length * (15624 * 8668 + 5443) := by
  apply_mod_cast show
    (15625 : ℚ) * (15624 * forwardHistoryCode word + 5443) =
      5 ^ word.length * (15624 * 8668 + 5443) from ?_
  norm_num [bcbbAffine, bcbbKappa, bcbbAlpha] at zero ⊢
  linarith

private theorem bcbbAffine_length_dvd_six (word : List NearyTile)
    (zero : bcbbAffine word = 0) : 6 ∣ word.length := by
  have natural := bcbbAffine_nat_eq word zero
  have modulus_mul (value : Nat) : 15624 * value ≡ 0 [MOD 15624] :=
    (dvd_mul_right 15624 value).modEq_zero_nat
  have left_mod :
      15625 * (15624 * forwardHistoryCode word + 5443) ≡ 5443 [MOD 15624] := by
    have scale : 15625 ≡ 1 [MOD 15624] := by norm_num [Nat.ModEq]
    simpa using scale.mul ((modulus_mul (forwardHistoryCode word)).add Nat.ModEq.rfl)
  have right_mod :
      5 ^ word.length * (15624 * 8668 + 5443) ≡
        5 ^ word.length * 5443 [MOD 15624] := by
    exact Nat.ModEq.rfl.mul ((modulus_mul 8668).add Nat.ModEq.rfl)
  have product_mod : 5443 ≡ 5 ^ word.length * 5443 [MOD 15624] :=
    left_mod.symm.trans ((by rw [natural] :
      15625 * (15624 * forwardHistoryCode word + 5443) ≡
        5 ^ word.length * (15624 * 8668 + 5443) [MOD 15624]).trans right_mod)
  have power_mod : 5 ^ word.length ≡ 1 [MOD 15624] := by
    have cancelled : 1 ≡ 5 ^ word.length [MOD 15624] :=
      Nat.ModEq.cancel_right_of_coprime (m := 15624) (a := 1)
        (b := 5 ^ word.length) (c := 5443) (by norm_num)
        (by simpa using product_mod)
    exact cancelled.symm
  have exponent_decomposition :
      word.length = 6 * (word.length / 6) + word.length % 6 := by
    have := Nat.div_add_mod word.length 6
    omega
  have cycle : 5 ^ 6 ≡ 1 [MOD 15624] := by norm_num [Nat.ModEq]
  have remainder_mod : 5 ^ (word.length % 6) ≡ 1 [MOD 15624] := by
    have power_decomposition :
        5 ^ word.length =
          (5 ^ 6) ^ (word.length / 6) * 5 ^ (word.length % 6) := by
      conv_lhs => rw [exponent_decomposition]
      rw [pow_add, pow_mul]
    have full_to_remainder :
        5 ^ word.length ≡ 5 ^ (word.length % 6) [MOD 15624] := by
      rw [power_decomposition]
      simpa using (cycle.pow (word.length / 6)).mul
        (Nat.ModEq.refl (5 ^ (word.length % 6)))
    exact full_to_remainder.symm.trans power_mod
  have remainder_lt : word.length % 6 < 6 := Nat.mod_lt _ (by decide)
  have remainder_zero : word.length % 6 = 0 := by
    interval_cases _remainder : word.length % 6
    · rfl
    all_goals norm_num [Nat.ModEq] at remainder_mod
  exact Nat.dvd_of_mod_eq_zero remainder_zero

theorem bcbbAffine_zero_iff (word : List NearyTile) :
    bcbbAffine word = 0 ↔ ∃ k, word = bcbbRoleRay k := by
  constructor
  · intro zero
    have length_dvd := bcbbAffine_length_dvd_six word zero
    have length_ne : word.length ≠ 0 := by
      intro length_zero
      have word_nil := List.length_eq_zero.mp length_zero
      subst word
      norm_num [bcbbAffine, bcbbKappa, bcbbAlpha] at zero
    obtain ⟨multiple, length_eq⟩ := length_dvd
    have multiple_ne : multiple ≠ 0 := by
      intro multiple_zero
      subst multiple
      apply length_ne
      omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero multiple_ne
    have ray_zero := bcbbAffine_ray k
    have ray_length : (bcbbRoleRay k).length = word.length := by
      rw [bcbbRoleRay_length, length_eq]
    have code_cast :
        (forwardHistoryCode word : ℚ) = forwardHistoryCode (bcbbRoleRay k) := by
      rw [bcbbAffine] at zero ray_zero
      rw [ray_length] at ray_zero
      linarith
    have code_eq : forwardHistoryCode word = forwardHistoryCode (bcbbRoleRay k) := by
      exact_mod_cast code_cast
    exact ⟨k, forwardHistoryCode_injective code_eq⟩
  · rintro ⟨k, rfl⟩
    exact bcbbAffine_ray k

theorem bcbbAffine_zero_iff_terminal_match (word : List NearyTile) :
    bcbbAffine word = 0 ↔
      spell (nearyUpper 3) word ++ nearyMarker 3 = spell (nearyLower 3 bcbbBody) word := by
  rw [bcbbAffine_zero_iff, bcbb_terminal_match_iff]
  constructor <;> rintro ⟨k, rfl⟩
  · exact ⟨k, bcbbRoleRay_eq_terminal k⟩
  · exact ⟨k, (bcbbRoleRay_eq_terminal k).symm⟩

theorem bcbb_periodicCoefficient_zero_iff_paired_zero (word : List PairedControl) :
    periodicCoefficient bcbbKappa bcbbAlpha word = 0 ↔
      pairedCoefficient ℚ 3 bcbbBody word = 0 := by
  rw [periodicCoefficient_eq]
  change bcbbAffine (decodePairedWord word) = 0 ↔ _
  rw [bcbbAffine_zero_iff_terminal_match, pairedCoefficient_eq_sideCoefficient,
    sideCoefficient_eq_zero_iff_terminal_match_rat]

/-! ## Cleared four-generator mortality family -/

/-- Denominator-cleared initial column `152568360000 · γ`. -/
def bcbbClearedColumn : Fin 3 → ℚ :=
  ![53150895000, 152568360000, 152568360000]

/-- The explicit integral rank-one separator. -/
def bcbbIntegralSeparator : Matrix (Fin 3) (Fin 3) ℤ :=
  !![53150895000, 0, -29486750353;
     152568360000, 0, -84641004504;
     152568360000, 0, -84641004504]

/-- Four integral generators: the separator and three positional controls. -/
def bcbbIntegralFamily : Option PairedControl → Matrix (Fin 3) (Fin 3) ℤ
  | none => bcbbIntegralSeparator
  | some control => periodicGenerator ℤ control

theorem periodicGenerator_map {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (control : PairedControl) :
    (periodicGenerator R control).map hom = periodicGenerator S control := by
  cases control with
  | data letter =>
      cases letter <;>
        ext i j <;>
        fin_cases i <;> fin_cases j <;>
        simp [periodicGenerator, periodicDataMatrix, Matrix.vecHead, Matrix.vecTail]
      all_goals
        first
        | exact map_ofNat hom 5
        | exact map_ofNat hom 3
        | exact map_ofNat hom 2
  | toggle => exact historyGenerator_map hom .toggle

theorem bcbbClearedColumn_eq :
    bcbbClearedColumn =
      (152568360000 : ℚ) • periodicColumn ℚ bcbbKappa := by
  ext coordinate
  fin_cases coordinate <;>
    norm_num [bcbbClearedColumn, periodicColumn, bcbbKappa]

theorem bcbbIntegralSeparator_cast :
    castMatrix bcbbIntegralSeparator =
      Matrix.vecMulVec bcbbClearedColumn (periodicRow ℚ bcbbAlpha) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [castMatrix, bcbbIntegralSeparator, bcbbClearedColumn, periodicRow, bcbbAlpha,
      Matrix.vecMulVec, Matrix.vecHead, Matrix.vecTail]

theorem bcbbIntegralFamily_cast (label : Option PairedControl) :
    castMatrix (bcbbIntegralFamily label) =
      separatedGenerator
        (Matrix.vecMulVec bcbbClearedColumn (periodicRow ℚ bcbbAlpha))
        (periodicGenerator ℚ) label := by
  cases label with
  | none => exact bcbbIntegralSeparator_cast
  | some control => exact periodicGenerator_map (Int.castRingHom ℚ) control

private theorem bcbbCleared_bridge (word : List PairedControl) :
    bridgeScalar bcbbClearedColumn (periodicRow ℚ bcbbAlpha)
        (wordProduct (periodicGenerator ℚ) word) =
      152568360000 * periodicCoefficient bcbbKappa bcbbAlpha word := by
  rw [bcbbClearedColumn_eq]
  simp [bridgeScalar, periodicCoefficient, linearCoefficient, Matrix.mulVec_smul,
    Matrix.dotProduct_smul]

theorem bcbbRationalFamily_mortal_iff_zero :
    IsMortal
        (separatedGenerator
          (Matrix.vecMulVec bcbbClearedColumn (periodicRow ℚ bcbbAlpha))
          (periodicGenerator ℚ)) ↔
      ∃ word : List PairedControl, periodicCoefficient bcbbKappa bcbbAlpha word = 0 := by
  rw [mortal_adjoin_outer_iff]
  apply exists_congr
  intro word
  rw [bcbbCleared_bridge]
  norm_num

theorem bcbbIntegralFamily_mortal_iff_paired_zero :
    IsMortal bcbbIntegralFamily ↔
      ∃ word : List PairedControl, pairedCoefficient ℚ 3 bcbbBody word = 0 := by
  have family_cast :
      castMatrix ∘ bcbbIntegralFamily =
        separatedGenerator
          (Matrix.vecMulVec bcbbClearedColumn (periodicRow ℚ bcbbAlpha))
          (periodicGenerator ℚ) := by
    funext label
    exact bcbbIntegralFamily_cast label
  have zero_exists :
      (∃ word : List PairedControl, periodicCoefficient bcbbKappa bcbbAlpha word = 0) ↔
        ∃ word : List PairedControl, pairedCoefficient ℚ 3 bcbbBody word = 0 :=
    exists_congr bcbb_periodicCoefficient_zero_iff_paired_zero
  rw [← zero_exists, ← bcbbRationalFamily_mortal_iff_zero, ← family_cast]
  exact (isMortal_cast_iff bcbbIntegralFamily).symm

theorem bcbbIntegralFamily_mortal : IsMortal bcbbIntegralFamily := by
  rw [bcbbIntegralFamily_mortal_iff_paired_zero]
  obtain ⟨control, decoded⟩ := decodePairedWord_surjective bcbbRolePrefix
  refine ⟨control, ?_⟩
  rw [pairedCoefficient_eq_sideCoefficient, decoded,
    sideCoefficient_eq_zero_iff_terminal_match_rat]
  exact (bcbb_terminal_match_iff bcbbRolePrefix).mpr
    ⟨0, by simpa [bcbbRoleRay] using bcbbRoleRay_eq_terminal 0⟩

theorem bcbb_integral_generator_count : Fintype.card (Option PairedControl) = 4 := by decide

end PeriodicHistory

end MatrixMortality
