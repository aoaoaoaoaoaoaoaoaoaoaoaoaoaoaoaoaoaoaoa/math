import MatrixMortality.TagQueue

/-!
# The four ordinary Neary tiles

This file gives the restricted binary-tag alphabet, its self-synchronizing binary word code,
and the four ordinary PCP labels.  The pulse automaton recognizes the only property of the
code needed for soundness: every positive run of zeroes has exactly the deletion width `β`.
-/

namespace MatrixMortality

inductive TagLetter where
  | b
  | c
  deriving DecidableEq, Fintype, Repr

inductive NearyTile where
  | rule : TagLetter → NearyTile
  | erase : TagLetter → NearyTile
  deriving DecidableEq, Fintype, Repr

/-- The fixed-boundary GPCP source alphabet has four letters. -/
theorem neary_source_generator_count : Fintype.card NearyTile = 4 := by decide

def tagCode (β : Nat) : TagLetter → List Bool
  | .b => [true] ++ List.replicate β false ++ [true]
  | .c => [true]

def tagEncode (β : Nat) (word : List TagLetter) : List Bool := spell (tagCode β) word

def nearyMarker (β : Nat) : List Bool := true :: List.replicate β false

def nearyBody (body : List TagLetter) : TagLetter → List TagLetter
  | .b => []
  | .c => body

def tagOutput (body : List TagLetter) (letter : TagLetter) : List TagLetter :=
  nearyBody body letter ++ [.b]

def nearyUpper (β : Nat) (tile : NearyTile) : List Bool :=
  match tile with
  | .rule letter | .erase letter => tagCode β letter

def NearyTile.letter : NearyTile → TagLetter
  | .rule letter | .erase letter => letter

def nearyLower (β : Nat) (body : List TagLetter) : NearyTile → List Bool
  | .rule .b => [true, true, false]
  | .rule .c => [true] ++ tagEncode β body ++ [true, false]
  | .erase _ => [false]

theorem nearyUpper_ne_nil (β : Nat) (tile : NearyTile) : nearyUpper β tile ≠ [] := by
  cases tile with
  | rule letter => cases letter <;> simp [nearyUpper, tagCode]
  | erase letter => cases letter <;> simp [nearyUpper, tagCode]

theorem nearyLower_ne_nil (β : Nat) (body : List TagLetter) (tile : NearyTile) :
    nearyLower β body tile ≠ [] := by
  cases tile with
  | rule letter => cases letter <;> simp [nearyLower]
  | erase letter => cases letter <;> simp [nearyLower]

/-- Both morphisms of the four-generator GPCP source are nonerasing. -/
theorem neary_morphisms_nonerasing (β : Nat) (body : List TagLetter) :
    (∀ tile, nearyUpper β tile ≠ []) ∧ (∀ tile, nearyLower β body tile ≠ []) :=
  ⟨nearyUpper_ne_nil β, nearyLower_ne_nil β body⟩

theorem tagEncode_append (β : Nat) (x y : List TagLetter) :
    tagEncode β (x ++ y) = tagEncode β x ++ tagEncode β y := by
  exact spell_append (tagCode β) x y

@[simp] theorem tagEncode_nil (β : Nat) : tagEncode β [] = [] := rfl

@[simp] theorem tagEncode_cons (β : Nat) (letter : TagLetter) (word : List TagLetter) :
    tagEncode β (letter :: word) = tagCode β letter ++ tagEncode β word := rfl

theorem tagCode_ne_nil (β : Nat) (letter : TagLetter) : tagCode β letter ≠ [] := by
  cases letter <;> simp [tagCode]

theorem tagEncode_eq_nil_iff (β : Nat) (word : List TagLetter) :
    tagEncode β word = [] ↔ word = [] := by
  cases word with
  | nil => simp
  | cons letter word => simp [tagEncode_cons, tagCode_ne_nil]

theorem tagEncode_ne_false_cons (β : Nat) (word : List TagLetter) (tail : List Bool) :
    tagEncode β word ≠ false :: tail := by
  cases word with
  | nil => simp
  | cons letter word => cases letter <;> simp [tagEncode_cons, tagCode]

theorem tagEncode_injective (β : Nat) (hβ : 0 < β) : Function.Injective (tagEncode β) := by
  intro x
  induction x with
  | nil =>
      intro y hxy
      exact ((tagEncode_eq_nil_iff β y).mp hxy.symm).symm
  | cons x xs ih =>
      intro y hxy
      cases y with
      | nil =>
          exact False.elim <| ((tagEncode_eq_nil_iff β (x :: xs)).not.mpr (by simp)) hxy
      | cons y ys =>
          cases β with
          | zero => omega
          | succ β =>
              cases x <;> cases y
              · simp only [tagEncode_cons, tagCode, List.append_cancel_left_eq] at hxy
                exact congrArg (TagLetter.b :: ·) (ih hxy)
              · simp only [tagEncode_cons, tagCode, List.replicate_succ, List.cons.injEq,
                  true_and] at hxy
                have htail : false :: List.replicate β false ++ [true] ++
                    tagEncode (β + 1) xs = tagEncode (β + 1) ys := by
                  exact (List.cons.inj hxy).2
                exact False.elim <| tagEncode_ne_false_cons (β + 1) ys _ htail.symm
              · simp only [tagEncode_cons, tagCode, List.replicate_succ, List.cons.injEq,
                  true_and] at hxy
                have htail : tagEncode (β + 1) xs = false :: List.replicate β false ++
                    [true] ++ tagEncode (β + 1) ys := by
                  exact (List.cons.inj hxy).2
                exact False.elim <| tagEncode_ne_false_cons (β + 1) xs _ htail
              · simp only [tagEncode_cons, tagCode, List.cons.injEq, true_and] at hxy
                exact congrArg (TagLetter.c :: ·) (ih <| List.append_cancel_left hxy)

/-! ## Pulse automaton -/

inductive Pulse where
  | virgin
  | gap : Nat → Pulse
  deriving DecidableEq, Repr

def pulseBit (β : Nat) : Pulse → Bool → Option Pulse
  | .virgin, true => some (.gap 0)
  | .virgin, false => none
  | .gap n, true => if n = 0 ∨ n = β then some (.gap 0) else none
  | .gap n, false => if n < β then some (.gap (n + 1)) else none

def pulseScan (β : Nat) : Pulse → List Bool → Option Pulse
  | state, [] => some state
  | state, bit :: bits => (pulseBit β state bit).bind fun next => pulseScan β next bits

@[simp] theorem pulseScan_nil (β : Nat) (state : Pulse) :
    pulseScan β state [] = some state := rfl

theorem pulseScan_append (β : Nat) (state : Pulse) (x y : List Bool) :
    pulseScan β state (x ++ y) =
      (pulseScan β state x).bind fun next => pulseScan β next y := by
  induction x generalizing state with
  | nil => rfl
  | cons bit x ih =>
      simp only [List.cons_append, pulseScan]
      cases hstep : pulseBit β state bit <;> simp [hstep, ih]

theorem pulseScan_false_replicate (β k n : Nat) (hbound : k + n ≤ β) :
    pulseScan β (.gap k) (List.replicate n false) = some (.gap (k + n)) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
      have hk : k < β := by omega
      have htail : k + 1 + n ≤ β := by omega
      simp only [List.replicate_succ, pulseScan, pulseBit, hk, ↓reduceIte, Option.bind_eq_bind]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1) htail

theorem pulseScan_tagCode_from_high (β : Nat) (hβ : 0 < β) (letter : TagLetter) :
    pulseScan β (.gap 0) (tagCode β letter) = some (.gap 0) := by
  cases letter with
  | c => simp [tagCode, pulseScan, pulseBit]
  | b =>
      change pulseScan β (.gap 0) (([true] ++ List.replicate β false) ++ [true]) = _
      rw [pulseScan_append, pulseScan_append]
      simp only [pulseScan, pulseBit, Option.some_bind]
      simp only [true_or, if_true, Option.some_bind]
      rw [pulseScan_false_replicate β 0 β (by simp)]
      simp [pulseScan, pulseBit, hβ.ne']

theorem pulseScan_tagCode_from_virgin (β : Nat) (hβ : 0 < β) (letter : TagLetter) :
    pulseScan β .virgin (tagCode β letter) = some (.gap 0) := by
  cases letter with
  | c => simp [tagCode, pulseScan, pulseBit]
  | b =>
      change pulseScan β .virgin (([true] ++ List.replicate β false) ++ [true]) = _
      rw [pulseScan_append, pulseScan_append]
      simp only [pulseScan, pulseBit, Option.some_bind]
      rw [pulseScan_false_replicate β 0 β (by simp)]
      simp [pulseScan, pulseBit, hβ.ne']

theorem pulseScan_tagEncode_from_high (β : Nat) (hβ : 0 < β)
    (word : List TagLetter) :
    pulseScan β (.gap 0) (tagEncode β word) = some (.gap 0) := by
  induction word with
  | nil => rfl
  | cons letter word ih =>
      rw [tagEncode_cons, pulseScan_append, pulseScan_tagCode_from_high β hβ letter]
      exact ih

theorem pulseScan_marker_from_high (β : Nat) :
    pulseScan β (.gap 0) (nearyMarker β) = some (.gap β) := by
  rw [nearyMarker, pulseScan]
  simp only [pulseBit, Option.some_bind]
  simpa using pulseScan_false_replicate β 0 β (by simp)

theorem pulseScan_marker_from_virgin (β : Nat) :
    pulseScan β .virgin (nearyMarker β) = some (.gap β) := by
  rw [nearyMarker, pulseScan]
  simp only [pulseBit, Option.some_bind]
  simpa using pulseScan_false_replicate β 0 β (by simp)

theorem pulseScan_tagEncode_from_virgin (β : Nat) (hβ : 0 < β)
    (letter : TagLetter) (word : List TagLetter) :
    pulseScan β .virgin (tagEncode β (letter :: word)) = some (.gap 0) := by
  rw [tagEncode_cons, pulseScan_append, pulseScan_tagCode_from_virgin β hβ letter]
  exact pulseScan_tagEncode_from_high β hβ word

theorem pulseScan_encoded_final (β : Nat) (hβ : 0 < β) (word : List TagLetter) :
    pulseScan β .virgin (tagEncode β word ++ nearyMarker β) = some (.gap β) := by
  cases word with
  | nil => exact pulseScan_marker_from_virgin β
  | cons letter word =>
      rw [pulseScan_append, pulseScan_tagEncode_from_virgin β hβ letter word]
      exact pulseScan_marker_from_high β

theorem spell_nearyUpper (β : Nat) (word : List NearyTile) :
    spell (nearyUpper β) word = tagEncode β (word.map NearyTile.letter) := by
  induction word with
  | nil => rfl
  | cons tile word ih =>
      change nearyUpper β tile ++ spell (nearyUpper β) word =
        tagEncode β (tile.letter :: word.map NearyTile.letter)
      rw [tagEncode_cons]
      rw [ih]
      cases tile <;> rfl

theorem pulseScan_nearyLower_rule_from_virgin (β : Nat) (body : List TagLetter)
    (hβ : 0 < β) (letter : TagLetter) :
    pulseScan β .virgin (nearyLower β body (.rule letter)) = some (.gap 1) := by
  cases letter with
  | b => simp [nearyLower, pulseScan, pulseBit, hβ]
  | c =>
      change pulseScan β .virgin ([true] ++ (tagEncode β body ++ [true, false])) = _
      rw [pulseScan_append]
      simp only [pulseScan, pulseBit, Option.some_bind]
      rw [pulseScan_append]
      rw [pulseScan_tagEncode_from_high β hβ]
      simp [pulseScan, pulseBit, hβ]

theorem pulseScan_nearyLower_rule_from_gap (β n : Nat) (body : List TagLetter)
    (hβ : 0 < β) (letter : TagLetter) :
    pulseScan β (.gap n) (nearyLower β body (.rule letter)) =
      if n = 0 ∨ n = β then some (.gap 1) else none := by
  by_cases hready : n = 0 ∨ n = β
  · simp only [hready, ↓reduceIte]
    cases letter with
    | b => simp [nearyLower, pulseScan, pulseBit, hready, hβ]
    | c =>
        change pulseScan β (.gap n) ([true] ++ (tagEncode β body ++ [true, false])) = _
        rw [pulseScan_append]
        simp only [pulseScan, pulseBit, hready, ↓reduceIte, Option.some_bind]
        rw [pulseScan_append]
        rw [pulseScan_tagEncode_from_high β hβ]
        simp [pulseScan, pulseBit, hβ]
  · simp only [hready, ↓reduceIte]
    cases letter <;> simp [nearyLower, pulseScan, pulseBit, hready]

theorem pulseScan_nearyLower_erase (β n : Nat) (body : List TagLetter)
    (letter : TagLetter) :
    pulseScan β (.gap n) (nearyLower β body (.erase letter)) =
      if n < β then some (.gap (n + 1)) else none := by
  simp [nearyLower, pulseScan, pulseBit]

def strokeTiles {β : Nat} (stroke : Stroke TagLetter β) : List NearyTile :=
  .rule stroke.head :: stroke.wake.map .erase

def tileHistory {β : Nat} (history : List (Stroke TagLetter β)) : List NearyTile :=
  (history.map strokeTiles).join

@[simp] theorem tileHistory_nil {β : Nat} :
    tileHistory ([] : List (Stroke TagLetter β)) = [] := rfl

@[simp] theorem tileHistory_cons {β : Nat} (stroke : Stroke TagLetter β)
    (history : List (Stroke TagLetter β)) :
    tileHistory (stroke :: history) = strokeTiles stroke ++ tileHistory history := rfl

private theorem tileHistory_of_scan_continuation (β : Nat) (body : List TagLetter)
    (hβ : 0 < β) (head : TagLetter) (wake : List TagLetter) (n : Nat)
    (hwidth : wake.length + 1 = n) (hn : n ≤ β) (rest : List NearyTile)
    (hscan : pulseScan β (.gap n) (spell (nearyLower β body) rest) = some (.gap β)) :
    ∃ history : List (Stroke TagLetter β),
      .rule head :: wake.map .erase ++ rest = tileHistory history := by
  induction rest generalizing head wake n with
  | nil =>
      simp only [spell, pulseScan] at hscan
      have hnβ : n = β := by simpa using Option.some.inj hscan
      let stroke : Stroke TagLetter β := ⟨head, wake, hwidth.trans hnβ⟩
      exact ⟨[stroke], by simp [tileHistory, strokeTiles, stroke]⟩
  | cons tile rest ih =>
      rw [show spell (nearyLower β body) (tile :: rest) =
          nearyLower β body tile ++ spell (nearyLower β body) rest by rfl,
        pulseScan_append] at hscan
      cases tile with
      | erase letter =>
          rw [pulseScan_nearyLower_erase] at hscan
          by_cases hstep : n < β
          · simp only [hstep, ↓reduceIte, Option.some_bind] at hscan
            have hwidth' : (wake ++ [letter]).length + 1 = n + 1 := by
              simp [hwidth]
            obtain ⟨history, hhistory⟩ :=
              ih head (wake ++ [letter]) (n + 1) hwidth' (by omega) hscan
            refine ⟨history, ?_⟩
            simpa [List.map_append, List.append_assoc] using hhistory
          · simp [hstep] at hscan
      | rule letter =>
          rw [pulseScan_nearyLower_rule_from_gap β n body hβ] at hscan
          have hn0 : n ≠ 0 := by omega
          have hnβ : n = β := by
            by_contra hne
            simp [hn0, hne] at hscan
          simp only [hnβ, or_true, ↓reduceIte, Option.some_bind] at hscan
          obtain ⟨history, hhistory⟩ :=
            ih letter [] 1 (by simp) (by omega) hscan
          let stroke : Stroke TagLetter β := ⟨head, wake, hwidth.trans hnβ⟩
          refine ⟨stroke :: history, ?_⟩
          simp only [tileHistory_cons, strokeTiles, stroke]
          simpa [List.append_assoc] using congrArg (fun tail =>
            (.rule head :: wake.map .erase) ++ tail) hhistory

/-- Acceptance by the pulse automaton forces an arbitrary label word into exact `β`-wide
strokes. -/
theorem tileHistory_of_pulseScan (β : Nat) (body : List TagLetter) (hβ : 0 < β)
    (word : List NearyTile)
    (hscan : pulseScan β .virgin (spell (nearyLower β body) word) = some (.gap β)) :
    ∃ history : List (Stroke TagLetter β), word = tileHistory history := by
  cases word with
  | nil => simp [spell, pulseScan] at hscan
  | cons tile rest =>
      rw [show spell (nearyLower β body) (tile :: rest) =
          nearyLower β body tile ++ spell (nearyLower β body) rest by rfl,
        pulseScan_append] at hscan
      cases tile with
      | erase letter => simp [nearyLower, pulseScan, pulseBit] at hscan
      | rule head =>
          rw [pulseScan_nearyLower_rule_from_virgin β body hβ] at hscan
          simp only [Option.some_bind] at hscan
          exact tileHistory_of_scan_continuation β body hβ head [] 1
            (by simp) (by omega) rest hscan

/-- Any terminal match over the four ordinary tiles has the exact fixed-width block form. -/
theorem tileHistory_of_terminal_match (β : Nat) (body : List TagLetter) (hβ : 0 < β)
    (word : List NearyTile)
    (hmatch : spell (nearyUpper β) word ++ nearyMarker β =
      spell (nearyLower β body) word) :
    ∃ history : List (Stroke TagLetter β), word = tileHistory history := by
  apply tileHistory_of_pulseScan β body hβ word
  rw [← hmatch, spell_nearyUpper]
  exact pulseScan_encoded_final β hβ _

theorem map_letter_strokeTiles {β : Nat} (stroke : Stroke TagLetter β) :
    (strokeTiles stroke).map NearyTile.letter = stroke.letters := by
  simp [strokeTiles, Stroke.letters, NearyTile.letter, Function.comp_def]

theorem map_letter_tileHistory {β : Nat} (history : List (Stroke TagLetter β)) :
    (tileHistory history).map NearyTile.letter = consumed history := by
  induction history with
  | nil => rfl
  | cons stroke history ih =>
      simp [tileHistory_cons, consumed_cons, List.map_append, map_letter_strokeTiles, ih]

theorem spell_nearyLower_erase_wake (β : Nat) (body wake : List TagLetter) :
    spell (nearyLower β body) (wake.map .erase) = List.replicate wake.length false := by
  induction wake with
  | nil => rfl
  | cons _ wake ih =>
      change [false] ++ spell (nearyLower β body) (wake.map .erase) =
        List.replicate (wake.length + 1) false
      rw [ih]
      simp [List.replicate_succ]

theorem spell_nearyLower_strokeTiles (β : Nat) (body : List TagLetter)
    (stroke : Stroke TagLetter β) :
    spell (nearyLower β body) (strokeTiles stroke) =
      tagEncode β (.c :: nearyBody body stroke.head) ++ nearyMarker β := by
  have hzeros : [false] ++ List.replicate stroke.wake.length false =
      List.replicate β false := by
    calc
      [false] ++ List.replicate stroke.wake.length false =
          List.replicate (stroke.wake.length + 1) false := by simp [List.replicate_succ]
      _ = List.replicate β false := by rw [stroke.width]
  change nearyLower β body (.rule stroke.head) ++
      spell (nearyLower β body) (stroke.wake.map .erase) = _
  rw [spell_nearyLower_erase_wake]
  cases stroke.head with
  | b =>
      change [true, true] ++ ([false] ++ List.replicate stroke.wake.length false) =
        [true, true] ++ List.replicate β false
      rw [hzeros]
  | c =>
      simp only [nearyLower, nearyBody, tagEncode_cons, tagCode]
      have htail : [true, false] ++ List.replicate stroke.wake.length false =
          nearyMarker β := by
        change true :: ([false] ++ List.replicate stroke.wake.length false) =
          true :: List.replicate β false
        rw [hzeros]
      simpa [List.append_assoc] using congrArg
        (fun tail => [true] ++ tagEncode β body ++ tail) htail

theorem marker_append_encoded_c (β : Nat) (word : List TagLetter) :
    nearyMarker β ++ tagEncode β (.c :: word) = tagEncode β (.b :: word) := by
  simp [nearyMarker, tagEncode_cons, tagCode, List.append_assoc]

theorem marker_append_true (β : Nat) :
    nearyMarker β ++ [true] = tagEncode β [.b] := by
  rw [tagEncode_cons, tagEncode_nil]
  simp [nearyMarker, tagCode, List.append_assoc]

/-- Appending one final `1` completes the last dangling marker.  The decoded lower string is
the initialization payload followed by one complete tag output for every later stroke. -/
theorem spell_nearyLower_tileHistory_append_true (β : Nat) (body : List TagLetter)
    (first : Stroke TagLetter β) (history : List (Stroke TagLetter β)) :
    spell (nearyLower β body) (tileHistory (first :: history)) ++ [true] =
      tagEncode β
        (.c :: nearyBody body first.head ++ [.b] ++ produced (tagOutput body) history) := by
  induction history generalizing first with
  | nil =>
      rw [tileHistory_cons, tileHistory_nil, List.append_nil,
        spell_nearyLower_strokeTiles]
      simp [produced, tagEncode_append, marker_append_true, List.append_assoc]
  | cons next history ih =>
      rw [tileHistory_cons, spell_append, spell_nearyLower_strokeTiles]
      calc
        (tagEncode β (.c :: nearyBody body first.head) ++ nearyMarker β ++
            spell (nearyLower β body) (tileHistory (next :: history))) ++ [true] =
            tagEncode β (.c :: nearyBody body first.head) ++ nearyMarker β ++
              (spell (nearyLower β body) (tileHistory (next :: history)) ++ [true]) := by
                simp [List.append_assoc]
        _ = tagEncode β (.c :: nearyBody body first.head) ++ nearyMarker β ++
            tagEncode β (.c :: nearyBody body next.head ++ [.b] ++
              produced (tagOutput body) history) := by rw [ih next]
        _ = tagEncode β
            (.c :: nearyBody body first.head ++ [.b] ++
              produced (tagOutput body) (next :: history)) := by
                rw [List.append_assoc]
                simp only [List.cons_append]
                rw [marker_append_encoded_c, ← tagEncode_append]
                simp [produced_cons, tagOutput, tagEncode_append, List.append_assoc]

theorem spell_nearyUpper_tileHistory (β : Nat) (history : List (Stroke TagLetter β)) :
    spell (nearyUpper β) (tileHistory history) = tagEncode β (consumed history) := by
  rw [spell_nearyUpper, map_letter_tileHistory]

/-- The global word equation cannot be reached by a malformed ordinary path.  It yields a
lawful tag execution and stops as soon as the queue becomes shorter than `β`. -/
theorem tagHaltsFrom_of_terminal_match (β : Nat) (body : List TagLetter)
    (hβ : 1 < β) (hbody : β - 1 ≤ body.length) (word : List NearyTile)
    (hmatch : spell (nearyUpper β) word ++ nearyMarker β =
      spell (nearyLower β body) word) :
    TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  obtain ⟨history, rfl⟩ := tileHistory_of_terminal_match β body (by omega) word hmatch
  have hhistory : history ≠ [] := by
    intro hempty
    subst history
    simp [spell, nearyMarker] at hmatch
  obtain ⟨first, history, rfl⟩ := List.exists_cons_of_ne_nil hhistory
  have hbits := congrArg (fun bits => bits ++ [true]) hmatch
  change (spell (nearyUpper β) (tileHistory (first :: history)) ++ nearyMarker β) ++
      [true] = spell (nearyLower β body) (tileHistory (first :: history)) ++ [true] at hbits
  rw [spell_nearyUpper_tileHistory,
    spell_nearyLower_tileHistory_append_true] at hbits
  have hencoded : tagEncode β (consumed (first :: history) ++ [.b]) =
      tagEncode β
        (.c :: nearyBody body first.head ++ [.b] ++ produced (tagOutput body) history) := by
    simpa [tagEncode_append, marker_append_true, List.append_assoc] using hbits
  have hsemantic := tagEncode_injective β (by omega) hencoded
  have hhead : first.head = .c := by
    have := congrArg List.head? hsemantic
    simpa [consumed_cons, Stroke.letters] using this
  rw [consumed_cons, Stroke.letters, hhead, nearyBody] at hsemantic
  have htail : first.wake ++ consumed history ++ [.b] =
      body ++ [.b] ++ produced (tagOutput body) history :=
    (List.cons.inj hsemantic).2
  have hwakeLength : first.wake.length = β - 1 := by
    have := first.width
    omega
  have hwakePrefixCommon : first.wake <+:
      body ++ [.b] ++ produced (tagOutput body) history := by
    rw [← htail]
    simp [List.append_assoc]
  have hbodyPrefixCommon : body <+:
      body ++ [.b] ++ produced (tagOutput body) history := by
    simp [List.append_assoc]
  have hwakePrefix : first.wake <+: body :=
    common_prefix_of_length_le hwakePrefixCommon hbodyPrefixCommon <| by
      simpa [hwakeLength] using hbody
  obtain ⟨suffix, hbodyEq⟩ := hwakePrefix
  have hdrop : body.drop (β - 1) = suffix := by
    rw [← hwakeLength, ← hbodyEq]
    simp
  have hqueue : consumed history ++ [.b] =
      (suffix ++ [.b]) ++ produced (tagOutput body) history := by
    have hnormalized : first.wake ++ (consumed history ++ [.b]) =
        first.wake ++ ((suffix ++ [.b]) ++ produced (tagOutput body) history) := by
      simpa [← hbodyEq, List.append_assoc] using htail
    exact List.append_cancel_left hnormalized
  rw [hdrop]
  exact tagHaltsFrom_of_history (tagOutput body) history (suffix ++ [.b]) [.b]
    (by simp; omega) hqueue

def EndsInB (word : List TagLetter) : Prop := ∃ front, word = front ++ [.b]

def NearyInvariant (β : Nat) (word : List TagLetter) : Prop :=
  EndsInB word ∧ word.length ≡ 1 [MOD β - 1]

theorem tagOutput_endsInB (body : List TagLetter) (letter : TagLetter) :
    EndsInB (tagOutput body letter) := ⟨nearyBody body letter, rfl⟩

theorem tagOutput_length_modEq (β : Nat) (body : List TagLetter)
    (hbodyDiv : β - 1 ∣ body.length) (letter : TagLetter) :
    (tagOutput body letter).length ≡ 1 [MOD β - 1] := by
  cases letter with
  | b =>
      simpa [tagOutput, nearyBody] using (Nat.ModEq.refl (n := β - 1) 1)
  | c =>
      simpa [tagOutput, nearyBody] using
        hbodyDiv.modEq_zero_nat.add (Nat.ModEq.refl (n := β - 1) 1)

theorem nearyInitial_invariant (β : Nat) (body : List TagLetter)
    (hbodyDiv : β - 1 ∣ body.length) :
    NearyInvariant β (body.drop (β - 1) ++ [.b]) := by
  constructor
  · exact ⟨body.drop (β - 1), rfl⟩
  · have hdropDiv : β - 1 ∣ (body.drop (β - 1)).length := by
      rw [List.length_drop]
      exact Nat.dvd_sub' hbodyDiv dvd_rfl
    simpa using hdropDiv.modEq_zero_nat.add (Nat.ModEq.refl (n := β - 1) 1)

theorem nearyInvariant_step (β : Nat) (body : List TagLetter) (hβ : 1 < β)
    (hbodyDiv : β - 1 ∣ body.length) {before after : List TagLetter}
    (hinvariant : NearyInvariant β before)
    (hstep : TagStep β (tagOutput body) before after) : NearyInvariant β after := by
  obtain ⟨stroke, rest, hbefore, hafter⟩ := hstep
  constructor
  · obtain ⟨payload, hpayload⟩ := tagOutput_endsInB body stroke.head
    refine ⟨rest ++ payload, ?_⟩
    rw [hafter, hpayload, List.append_assoc]
  · have hβmod : β ≡ 1 [MOD β - 1] := by
      have hdecompose : β = (β - 1) + 1 := by omega
      rw [hdecompose]
      exact Nat.add_modEq_left
    have hbeforeMod : β + rest.length ≡ 1 [MOD β - 1] := by
      simpa [hbefore, Stroke.length_letters, List.length_append] using hinvariant.2
    have hrestMod : rest.length + 1 ≡ 1 [MOD β - 1] := by
      have := (hβmod.add (Nat.ModEq.refl (n := β - 1) rest.length)).symm.trans hbeforeMod
      simpa [Nat.add_comm] using this
    have houtputMod := tagOutput_length_modEq β body hbodyDiv stroke.head
    have hnextMod :=
      ((Nat.ModEq.refl (n := β - 1) rest.length).add houtputMod).trans hrestMod
    simpa [hafter, List.length_append] using hnextMod

theorem nearyInvariant_short_eq_b (β : Nat) (hβ : 2 < β) {queue : List TagLetter}
    (hinvariant : NearyInvariant β queue) (hshort : queue.length < β) : queue = [.b] := by
  obtain ⟨front, rfl⟩ := hinvariant.1
  have hbound : (front ++ [TagLetter.b]).length < 1 + (β - 1) := by
    simpa [show 1 + (β - 1) = β by omega] using hshort
  have hle : (front ++ [TagLetter.b]).length ≤ 1 :=
    Nat.ModEq.le_of_lt_add hinvariant.2 hbound
  have hfront : front = [] := List.length_eq_zero.mp <| by simpa using hle
  simp [hfront]

/-- Conversely, every terminating restricted tag computation emits a terminal match over the
four ordinary tiles. -/
theorem terminal_match_of_tagHaltsFrom (β : Nat) (body : List TagLetter)
    (hβ : 2 < β) (hbody : β - 1 ≤ body.length) (hbodyDiv : β - 1 ∣ body.length)
    (hhalts : TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b])) :
    ∃ word : List NearyTile,
      spell (nearyUpper β) word ++ nearyMarker β = spell (nearyLower β body) word := by
  let initial := body.drop (β - 1) ++ [.b]
  obtain ⟨history, hhistory⟩ := terminal_history_of_tagHaltsFrom
    (tagOutput body) (NearyInvariant β) [.b] initial
    (nearyInvariant_step β body (by omega) hbodyDiv)
    (nearyInvariant_short_eq_b β hβ)
    (nearyInitial_invariant β body hbodyDiv) hhalts
  have hwake : (body.take (β - 1)).length + 1 = β := by
    rw [List.length_take, Nat.min_eq_left hbody]
    omega
  let first : Stroke TagLetter β := ⟨.c, body.take (β - 1), hwake⟩
  refine ⟨tileHistory (first :: history), ?_⟩
  apply List.append_cancel_right (bs := [true])
  rw [spell_nearyUpper_tileHistory, spell_nearyLower_tileHistory_append_true]
  have hsemantic : consumed (first :: history) ++ [.b] =
      .c :: body ++ [.b] ++ produced (tagOutput body) history := by
    simp only [consumed_cons, first, Stroke.letters]
    apply congrArg (TagLetter.c :: ·)
    calc
      body.take (β - 1) ++ consumed history ++ [.b] =
          body.take (β - 1) ++ (consumed history ++ [.b]) := by simp [List.append_assoc]
      _ = body.take (β - 1) ++ (initial ++ produced (tagOutput body) history) := by
        rw [hhistory]
      _ = body ++ [.b] ++ produced (tagOutput body) history := by
        simp only [initial]
        rw [List.append_assoc (body.drop (β - 1)) [.b],
          ← List.append_assoc (body.take (β - 1)) (body.drop (β - 1)),
          List.take_append_drop]
        simp [List.append_assoc]
  calc
    (tagEncode β (consumed (first :: history)) ++ nearyMarker β) ++ [true] =
        tagEncode β (consumed (first :: history)) ++ (nearyMarker β ++ [true]) := by
          simp [List.append_assoc]
    _ = tagEncode β (consumed (first :: history)) ++ tagEncode β [.b] := by
      rw [marker_append_true]
    _ = tagEncode β (consumed (first :: history) ++ [.b]) :=
      (tagEncode_append β _ _).symm
    _ = tagEncode β
        (.c :: body ++ [.b] ++ produced (tagOutput body) history) := congrArg _ hsemantic
    _ = tagEncode β
        (.c :: nearyBody body first.head ++ [.b] ++ produced (tagOutput body) history) := by
          rfl

theorem terminal_match_iff_tagHaltsFrom (β : Nat) (body : List TagLetter)
    (hβ : 2 < β) (hbody : β - 1 ≤ body.length) (hbodyDiv : β - 1 ∣ body.length) :
    (∃ word : List NearyTile,
      spell (nearyUpper β) word ++ nearyMarker β = spell (nearyLower β body) word) ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  constructor
  · rintro ⟨word, hmatch⟩
    exact tagHaltsFrom_of_terminal_match β body (by omega) hbody word hmatch
  · exact terminal_match_of_tagHaltsFrom β body hβ hbody hbodyDiv

theorem nearyTile_final_mismatch (β : Nat) (body : List TagLetter) :
    ∀ tile, ∃ upper lower,
      nearyUpper β tile = upper ++ [true] ∧
        nearyLower β body tile = lower ++ [false] := by
  intro tile
  cases tile with
  | rule letter =>
      cases letter with
      | b =>
          exact ⟨[true] ++ List.replicate β false, [true, true],
            by simp [nearyUpper, tagCode, List.append_assoc], rfl⟩
      | c =>
          exact ⟨[], [true] ++ tagEncode β body ++ [true], rfl,
            by simp [nearyLower, List.append_assoc]⟩
  | erase letter =>
      cases letter with
      | b =>
          exact ⟨[true] ++ List.replicate β false, [],
            by simp [nearyUpper, tagCode, List.append_assoc], rfl⟩
      | c => exact ⟨[], [], rfl, rfl⟩

def nearyPCPUpper (β : Nat) : Option NearyTile → List Bool :=
  binaryMarkedSide (nearyUpper β) (nearyMarker β)

def nearyPCPLower (β : Nat) (body : List TagLetter) : Option NearyTile → List Bool :=
  binaryMarkedSide (nearyLower β body) []

theorem nearyPCP_solvable_iff_tagHaltsFrom (β : Nat) (body : List TagLetter)
    (hβ : 2 < β) (hbody : β - 1 ≤ body.length) (hbodyDiv : β - 1 ∣ body.length) :
    (∃ word, IsPCPSolution (nearyPCPUpper β) (nearyPCPLower β body) word) ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  rw [nearyPCPUpper, nearyPCPLower,
    binaryMarked_solvable_iff_terminal_match_of_final_mismatch
      (nearyUpper β) (nearyLower β body) (nearyMarker β) true false
      (by decide) (nearyTile_final_mismatch β body)]
  exact terminal_match_iff_tagHaltsFrom β body hβ hbody hbodyDiv

theorem nearyPCP_primitive_terminal (β : Nat) (body : List TagLetter) :
    ∀ word,
      IsPrimitivePCPSolution (nearyPCPUpper β) (nearyPCPLower β body) word →
        ∃ interior : List NearyTile, word = interior.map some ++ [none] := by
  exact binaryMarked_primitive_terminal_of_final_mismatch
    (nearyUpper β) (nearyLower β body) (nearyMarker β) true false
    (by decide) (nearyTile_final_mismatch β body)

def nearyMortalityFamilyInt (β : Nat) (body : List TagLetter) :
    Option NearyTile → Matrix (Fin 3) (Fin 3) Int :=
  absorbedFamilyInt (nearyUpper β) (nearyLower β body) (nearyMarker β) []

/-- The complete exact source-to-mortality equivalence.  Its label type has five elements. -/
theorem nearyMortalityFamilyInt_mortal_iff_tagHaltsFrom (β : Nat)
    (body : List TagLetter) (hβ : 2 < β) (hbody : β - 1 ≤ body.length)
    (hbodyDiv : β - 1 ∣ body.length) :
    IsMortal (nearyMortalityFamilyInt β body) ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  rw [nearyMortalityFamilyInt, absorbedFamilyInt_mortal_iff_terminal_match]
  simpa using terminal_match_iff_tagHaltsFrom β body hβ hbody hbodyDiv

theorem nearyGPCP_solvable_iff_tagHaltsFrom (β : Nat) (body : List TagLetter)
    (hβ : 2 < β) (hbody : β - 1 ≤ body.length) (hbodyDiv : β - 1 ∣ body.length) :
    (∃ word, IsGPCPSolution (nearyUpper β) (nearyLower β body)
      [] (nearyMarker β) [] [] word) ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  rw [← terminal_match_iff_right_bounded_gpcp]
  simpa using terminal_match_iff_tagHaltsFrom β body hβ hbody hbodyDiv

/-- The nonempty right boundary excludes the empty word from the Neary GPCP instance. -/
theorem nearyGPCP_solution_ne_nil (β : Nat) (body : List TagLetter) (word : List NearyTile)
    (hsolution : IsGPCPSolution (nearyUpper β) (nearyLower β body)
      [] (nearyMarker β) [] [] word) : word ≠ [] := by
  intro hword
  subst word
  simp [IsGPCPSolution, nearyMarker, spell] at hsolution

/-- Publication-facing nonempty-witness form of the four-generator GPCP equivalence. -/
theorem nearyGPCPPlus_solvable_iff_tagHaltsFrom (β : Nat) (body : List TagLetter)
    (hβ : 2 < β) (hbody : β - 1 ≤ body.length) (hbodyDiv : β - 1 ∣ body.length) :
    (∃ word, IsGPCPPlusSolution (nearyUpper β) (nearyLower β body)
      [] (nearyMarker β) [] [] word) ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  constructor
  · rintro ⟨word, _, hsolution⟩
    exact (nearyGPCP_solvable_iff_tagHaltsFrom β body hβ hbody hbodyDiv).mp
      ⟨word, hsolution⟩
  · intro hhalts
    obtain ⟨word, hsolution⟩ :=
      (nearyGPCP_solvable_iff_tagHaltsFrom β body hβ hbody hbodyDiv).mpr hhalts
    exact ⟨word, nearyGPCP_solution_ne_nil β body word hsolution, hsolution⟩

theorem nearyMortality_ordinary_det_ne_zero (β : Nat) (body : List TagLetter)
    (tile : NearyTile) : (nearyMortalityFamilyInt β body (some tile)).det ≠ 0 := by
  simpa [nearyMortalityFamilyInt, absorbedFamilyInt, separatedGenerator] using
    pcpMatrix_det_ne_zero_int (nearyUpper β tile) (nearyLower β body tile)

theorem nearyMortality_ordinary_upperTriangular (β : Nat) (body : List TagLetter)
    (tile : NearyTile) :
    (nearyMortalityFamilyInt β body (some tile)).BlockTriangular id := by
  simpa [nearyMortalityFamilyInt, absorbedFamilyInt, separatedGenerator] using
    pcpMatrix_upperTriangular ℤ (nearyUpper β tile) (nearyLower β body tile)

theorem nearyMortality_terminal_ne_zero (β : Nat) (body : List TagLetter) :
    nearyMortalityFamilyInt β body none ≠ 0 := by
  simpa [nearyMortalityFamilyInt, absorbedFamilyInt, separatedGenerator] using
    terminalGeneratorInt_ne_zero (nearyMarker β) []

theorem nearyMortality_terminal_rank_eq_one (β : Nat) (body : List TagLetter) :
    (castMatrix (nearyMortalityFamilyInt β body none)).toLin'.rank = 1 := by
  simpa [nearyMortalityFamilyInt, absorbedFamilyInt, separatedGenerator] using
    castMatrix_terminalGeneratorInt_rank_eq_one (nearyMarker β) []

theorem neary_generator_count : Fintype.card (Option NearyTile) = 5 := by decide

/-- The arithmetic envelope consumed by the four-tile theorem.  Neary's padded compiler outputs
inhabit this strictly larger class: its whole appendant is `body ++ [b]`, and choosing
`s = x(β-1)+1` gives the displayed body length. -/
structure NearyArithmeticEnvelope where
  β : Nat
  body : List TagLetter
  paddingRounds : Nat
  beta_large : 2 < β
  body_length : body.length = (paddingRounds * β + 1) * (β - 1)

namespace NearyArithmeticEnvelope

def initial (source : NearyArithmeticEnvelope) : List TagLetter :=
  source.body.drop (source.β - 1) ++ [.b]

theorem body_divisible (source : NearyArithmeticEnvelope) :
    source.β - 1 ∣ source.body.length := by
  refine ⟨source.paddingRounds * source.β + 1, ?_⟩
  simp [source.body_length, Nat.mul_comm]

theorem body_long (source : NearyArithmeticEnvelope) :
    source.β - 1 ≤ source.body.length := by
  rw [source.body_length]
  exact Nat.le_mul_of_pos_left _ (by omega)

theorem pcp_solvable_iff_halts (source : NearyArithmeticEnvelope) :
    (∃ word, IsPCPSolution (nearyPCPUpper source.β)
      (nearyPCPLower source.β source.body) word) ↔
      TagHaltsFrom source.β (tagOutput source.body) source.initial := by
  exact nearyPCP_solvable_iff_tagHaltsFrom source.β source.body source.beta_large
    source.body_long source.body_divisible

theorem pcp_primitive_terminal (source : NearyArithmeticEnvelope) :
    ∀ word,
      IsPrimitivePCPSolution (nearyPCPUpper source.β)
          (nearyPCPLower source.β source.body) word →
        ∃ interior : List NearyTile, word = interior.map some ++ [none] :=
  nearyPCP_primitive_terminal source.β source.body

theorem gpcp_solvable_iff_halts (source : NearyArithmeticEnvelope) :
    (∃ word, IsGPCPSolution (nearyUpper source.β) (nearyLower source.β source.body)
      [] (nearyMarker source.β) [] [] word) ↔
      TagHaltsFrom source.β (tagOutput source.body) source.initial := by
  exact nearyGPCP_solvable_iff_tagHaltsFrom source.β source.body source.beta_large
    source.body_long source.body_divisible

theorem gpcpPlus_solvable_iff_halts (source : NearyArithmeticEnvelope) :
    (∃ word, IsGPCPPlusSolution (nearyUpper source.β) (nearyLower source.β source.body)
      [] (nearyMarker source.β) [] [] word) ↔
      TagHaltsFrom source.β (tagOutput source.body) source.initial := by
  exact nearyGPCPPlus_solvable_iff_tagHaltsFrom source.β source.body source.beta_large
    source.body_long source.body_divisible

theorem mortality_iff_halts (source : NearyArithmeticEnvelope) :
    IsMortal (nearyMortalityFamilyInt source.β source.body) ↔
      TagHaltsFrom source.β (tagOutput source.body) source.initial := by
  exact nearyMortalityFamilyInt_mortal_iff_tagHaltsFrom source.β source.body
    source.beta_large source.body_long source.body_divisible

end NearyArithmeticEnvelope

end MatrixMortality
