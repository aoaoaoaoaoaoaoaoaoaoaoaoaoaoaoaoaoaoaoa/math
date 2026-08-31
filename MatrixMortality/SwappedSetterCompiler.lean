import MatrixMortality.SwappedSetterResidual

/-!
# Compiler congruence for swapped-setter residuals

The two nonterminal depth-one residuals of the swapped decimal setter decode to histories whose
two sides differ by one symbol modulo `β - 1`. Neary's padded body length makes that discrepancy
impossible. This file states the cut at the binary-word boundary used by the residual classifier.
-/

namespace MatrixMortality

private theorem consumed_length_modEq (β : Nat) (β_pos : 0 < β)
    (history : List (Stroke TagLetter β)) :
    (consumed history).length ≡ history.length [MOD β - 1] := by
  induction history with
  | nil => exact Nat.ModEq.refl 0
  | cons stroke history induction =>
      have beta_mod : β ≡ 1 [MOD β - 1] := by
        have beta_eq : β = (β - 1) + 1 := by omega
        rw [beta_eq]
        exact Nat.add_modEq_left
      simpa [consumed_cons, List.length_append, Nat.add_comm] using beta_mod.add induction

private theorem produced_length_modEq (β : Nat) (body : List TagLetter)
    (body_divisible : β - 1 ∣ body.length) (history : List (Stroke TagLetter β)) :
    (produced (tagOutput body) history).length ≡ history.length [MOD β - 1] := by
  induction history with
  | nil => exact Nat.ModEq.refl 0
  | cons stroke history induction =>
      have output_mod := tagOutput_length_modEq β body body_divisible stroke.head
      simpa [produced_cons, List.length_append, Nat.add_comm] using output_mod.add induction

private theorem nearyBody_length_modEq_zero (β : Nat) (body : List TagLetter)
    (body_divisible : β - 1 ∣ body.length) (letter : TagLetter) :
    (nearyBody body letter).length ≡ 0 [MOD β - 1] := by
  cases letter with
  | b => exact Nat.ModEq.refl 0
  | c => exact body_divisible.modEq_zero_nat

private theorem adjacent_residues_false {β offset : Nat} (β_large : 2 < β)
    (residue : offset + 1 ≡ offset + 2 [MOD β - 1]) : False := by
  have one_two : 1 ≡ 2 [MOD β - 1] :=
    Nat.ModEq.add_left_cancel' offset residue
  have divides_one : β - 1 ∣ 1 := by
    simpa using one_two.dvd'
  have beta_minus_one_eq : β - 1 = 1 := Nat.eq_one_of_dvd_one divides_one
  omega

private theorem swappedCode_replicate_false (length : Nat) :
    ternaryCode ((List.replicate length false).map not) = 3 ^ length - 1 := by
  induction length with
  | zero => simp
  | succ length induction =>
      rw [List.replicate_succ, List.map_cons, ternaryCode_cons, List.length_map,
        List.length_replicate, induction, pow_succ]
      simp only [Bool.not_false, ternaryDigit]
      have power_pos : 0 < 3 ^ length := pow_pos (by omega) length
      omega

/-- Swapped ternary value of the first nonterminal fringe `111·0^(β-1)`. -/
theorem swappedCode_deltaOneUpper (β : Nat) :
    ternaryCode ((SwappedSetterResidual.deltaOneUpper β).map not) =
      14 * 3 ^ (β - 1) - 1 := by
  rw [SwappedSetterResidual.deltaOneUpper, List.map_append, ternaryCode_append,
    List.length_map, List.length_replicate, swappedCode_replicate_false]
  norm_num [ternaryCode, ternaryDigit, Nat.ofDigits]
  have power_pos : 0 < 3 ^ (β - 1) := pow_pos (by omega) (β - 1)
  omega

/-- Swapped ternary value of Neary's `b` code. -/
theorem swappedCode_tagCode_b (β : Nat) :
    ternaryCode ((tagCode β .b).map not) = 6 * 3 ^ β - 2 := by
  simp only [tagCode, List.map_append, List.map_cons, List.map_nil, Bool.not_true]
  rw [ternaryCode_append, ternaryCode_append, List.length_singleton,
    List.length_map, List.length_replicate, swappedCode_replicate_false]
  norm_num [ternaryCode, ternaryDigit, pow_succ]
  have power_pos : 0 < 3 ^ β := pow_pos (by omega) β
  omega

/-- Both terminal fringe pairs have discrepancy `5·3^β-1`. -/
theorem swappedCode_terminalFringes (β : Nat) :
    ternaryCode
          (([true, true] ++ List.replicate β false).map not) =
        5 * 3 ^ β - 1 ∧
      ternaryCode ((tagCode β .b).map not) -
          ternaryCode ((List.replicate β false).map not) =
        5 * 3 ^ β - 1 := by
  constructor
  · rw [List.map_append, ternaryCode_append, List.length_map,
      List.length_replicate, swappedCode_replicate_false]
    norm_num [ternaryCode, ternaryDigit, Nat.ofDigits]
    have power_pos : 0 < 3 ^ β := pow_pos (by omega) β
    omega
  · rw [swappedCode_tagCode_b, swappedCode_replicate_false]
    have power_pos : 0 < 3 ^ β := pow_pos (by omega) β
    omega

/-- The second nonterminal fringe has discrepancy `17·3^(β-1)-1`. -/
theorem swappedCode_deltaThree {β : Nat} (β_pos : 0 < β) :
    ternaryCode ((tagCode β .b).map not) -
        ternaryCode ((List.replicate (β - 1) false).map not) =
      17 * 3 ^ (β - 1) - 1 := by
  rw [swappedCode_tagCode_b, swappedCode_replicate_false]
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt β_pos)
  simp only [Nat.succ_sub_one]
  rw [pow_succ]
  have power_pos : 0 < 3 ^ offset := pow_pos (by omega) offset
  omega

/-- Decode the first stable residual after its forced `D_c,R_c` prefix. -/
theorem swappedDeltaOne_history_of_residual (β : Nat) (body : List TagLetter)
    (β_pos : 0 < β) (rest : List NearyTile)
    (residual :
      spell (nearyUpper β) rest ++ nearyMarker β =
        tagCode β .b ++ tagEncode β body ++ [true, false] ++
          spell (nearyLower β body) rest) :
    ∃ (first : Stroke TagLetter β) (history : List (Stroke TagLetter β)),
      .rule .c :: rest = tileHistory (first :: history) ∧
      first.head = .c ∧
      first.wake ++ consumed history ++ [TagLetter.b] =
        TagLetter.b :: body ++ [TagLetter.b] ++
          produced (tagOutput body) history := by
  let prefixed := .rule .c :: rest
  have rotated :
      nearyMarker β ++ spell (nearyLower β body) prefixed =
        spell (nearyUpper β) rest ++ nearyMarker β := by
    simpa [prefixed, spell, nearyLower, tagCode, nearyMarker, List.append_assoc] using
      residual.symm
  have accepted_prefixed :
      pulseScan β .virgin (spell (nearyLower β body) prefixed) = some (.gap β) := by
    have accepted_rotated :
        pulseScan β .virgin
          (nearyMarker β ++ spell (nearyLower β body) prefixed) = some (.gap β) := by
      rw [rotated, spell_nearyUpper]
      exact pulseScan_encoded_final β β_pos _
    rw [pulseScan_append, pulseScan_marker_from_virgin] at accepted_rotated
    simp only [Option.bind_some] at accepted_rotated
    change pulseScan β .virgin
        (nearyLower β body (.rule .c) ++ spell (nearyLower β body) rest) =
      some (.gap β)
    rw [pulseScan_append, pulseScan_nearyLower_rule_from_virgin β body β_pos]
    simp only [Option.bind_some]
    change pulseScan β (.gap β)
        (nearyLower β body (.rule .c) ++ spell (nearyLower β body) rest) =
      some (.gap β) at accepted_rotated
    rw [pulseScan_append,
      pulseScan_nearyLower_rule_from_gap β β body β_pos] at accepted_rotated
    simpa using accepted_rotated
  obtain ⟨decoded, prefixed_eq⟩ :=
    tileHistory_of_pulseScan β body β_pos prefixed accepted_prefixed
  have decoded_nonempty : decoded ≠ [] := by
    intro decoded_empty
    subst decoded
    simp [prefixed, tileHistory] at prefixed_eq
  obtain ⟨first, history, decoded_eq⟩ := List.exists_cons_of_ne_nil decoded_nonempty
  subst decoded
  have first_head : first.head = .c := by
    have heads := congrArg List.head? prefixed_eq
    simpa [prefixed, tileHistory_cons, strokeTiles] using heads.symm
  have rest_letters :
      rest.map NearyTile.letter = first.wake ++ consumed history := by
    have letters :
        .c :: rest.map NearyTile.letter =
          first.head :: first.wake ++ consumed history := by
      have mapped := congrArg (List.map NearyTile.letter) prefixed_eq
      rw [map_letter_tileHistory] at mapped
      simpa [prefixed, consumed_cons, consumed, Stroke.letters, NearyTile.letter] using mapped
    rw [first_head] at letters
    exact (List.cons.inj letters).2
  have encoded_eq := congrArg (fun bits => bits ++ [true]) residual
  have decoded_eq :
      rest.map NearyTile.letter ++ [TagLetter.b] =
        TagLetter.b :: body ++ [TagLetter.b] ++ produced (tagOutput body) history := by
    apply tagEncode_injective β β_pos
    calc
      tagEncode β (rest.map NearyTile.letter ++ [TagLetter.b]) =
          (spell (nearyUpper β) rest ++ nearyMarker β) ++ [true] := by
            rw [tagEncode_append, ← spell_nearyUpper, ← marker_append_true]
            simp [List.append_assoc]
      _ =
          (tagCode β .b ++ tagEncode β body ++ [true, false] ++
            spell (nearyLower β body) rest) ++ [true] := encoded_eq
      _ = nearyMarker β ++
          (spell (nearyLower β body) prefixed ++ [true]) := by
            simp [prefixed, spell, nearyLower, tagCode, nearyMarker,
              List.append_assoc]
      _ = nearyMarker β ++
          tagEncode β
            (.c :: nearyBody body first.head ++ [.b] ++
              produced (tagOutput body) history) := by
            rw [prefixed_eq,
              spell_nearyLower_tileHistory_append_true β body first history]
      _ = tagEncode β
          (TagLetter.b :: body ++ [TagLetter.b] ++
            produced (tagOutput body) history) := by
            rw [first_head]
            simpa [nearyBody] using marker_append_encoded_c β
              (body ++ [TagLetter.b] ++ produced (tagOutput body) history)
  have semantic_eq :
      first.wake ++ consumed history ++ [TagLetter.b] =
        TagLetter.b :: body ++ [TagLetter.b] ++ produced (tagOutput body) history := by
    simpa [rest_letters, List.append_assoc] using decoded_eq
  exact ⟨first, history, by simpa [prefixed] using prefixed_eq, first_head, semantic_eq⟩

/-- The decoded first stable residual has incompatible length residue modulo `β - 1`. -/
theorem swappedDeltaOne_history_false (β : Nat) (body : List TagLetter)
    (β_large : 2 < β) (body_divisible : β - 1 ∣ body.length)
    (first : Stroke TagLetter β) (history : List (Stroke TagLetter β))
    (semantic_eq :
      first.wake ++ consumed history ++ [TagLetter.b] =
        TagLetter.b :: body ++ [TagLetter.b] ++
          produced (tagOutput body) history) : False := by
  have wake_length : first.wake.length = β - 1 := by
    have width := first.width
    omega
  have consumed_mod := consumed_length_modEq β (by omega) history
  have produced_mod := produced_length_modEq β body body_divisible history
  have wake_mod : first.wake.length ≡ 0 [MOD β - 1] := by
    rw [wake_length]
    simp
  have body_mod : body.length ≡ 0 [MOD β - 1] := body_divisible.modEq_zero_nat
  have one_mod : 1 ≡ 1 [MOD β - 1] := Nat.ModEq.refl 1
  have left_mod :
      (first.wake ++ consumed history ++ [TagLetter.b]).length ≡
        history.length + 1 [MOD β - 1] := by
    simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      wake_mod.add (consumed_mod.add one_mod)
  have right_mod :
      (TagLetter.b :: body ++ [TagLetter.b] ++
        produced (tagOutput body) history).length ≡
        history.length + 2 [MOD β - 1] := by
    simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      one_mod.add (body_mod.add (one_mod.add produced_mod))
  have equation_mod :
      (first.wake ++ consumed history ++ [TagLetter.b]).length ≡
        (TagLetter.b :: body ++ [TagLetter.b] ++
          produced (tagOutput body) history).length
          [MOD β - 1] := by
    rw [semantic_eq]
  exact adjacent_residues_false β_large <|
    left_mod.symm.trans (equation_mod.trans right_mod)

/-- Neary's padded body congruence excludes the first stable nonterminal residual. -/
theorem swappedDeltaOne_residual_false (β : Nat) (body : List TagLetter)
    (β_large : 2 < β) (body_divisible : β - 1 ∣ body.length)
    (rest : List NearyTile)
    (residual :
      spell (nearyUpper β) rest ++ nearyMarker β =
        tagCode β .b ++ tagEncode β body ++ [true, false] ++
          spell (nearyLower β body) rest) : False := by
  obtain ⟨first, history, _, _, semantic_eq⟩ :=
    swappedDeltaOne_history_of_residual β body (by omega) rest residual
  exact swappedDeltaOne_history_false β body β_large body_divisible first history semantic_eq

/-- Decode the second stable residual after its initial `D_b` and erasure wake. -/
theorem swappedDeltaThree_history_of_residual (β : Nat) (body wake : List TagLetter)
    (β_pos : 0 < β) (rest : List NearyTile)
    (residual :
      tagEncode β wake ++ spell (nearyUpper β) rest ++ nearyMarker β =
        spell (nearyLower β body) rest) :
    ∃ (first : Stroke TagLetter β) (history : List (Stroke TagLetter β)),
      rest = tileHistory (first :: history) ∧
      wake ++ consumed (first :: history) ++ [TagLetter.b] =
        TagLetter.c :: nearyBody body first.head ++ [TagLetter.b] ++
          produced (tagOutput body) history := by
  have accepted_rest :
      pulseScan β .virgin (spell (nearyLower β body) rest) = some (.gap β) := by
    rw [← residual, spell_nearyUpper, ← tagEncode_append]
    exact pulseScan_encoded_final β β_pos _
  obtain ⟨decoded, rest_eq⟩ :=
    tileHistory_of_pulseScan β body β_pos rest accepted_rest
  have decoded_nonempty : decoded ≠ [] := by
    intro decoded_empty
    subst decoded
    simp at rest_eq
    subst rest
    simp [spell, nearyMarker] at residual
  obtain ⟨first, history, decoded_eq⟩ := List.exists_cons_of_ne_nil decoded_nonempty
  subst decoded
  have encoded_eq := congrArg (fun bits => bits ++ [true]) residual
  have semantic_eq :
      wake ++ consumed (first :: history) ++ [TagLetter.b] =
        TagLetter.c :: nearyBody body first.head ++ [TagLetter.b] ++
          produced (tagOutput body) history := by
    apply tagEncode_injective β β_pos
    calc
      tagEncode β (wake ++ consumed (first :: history) ++ [TagLetter.b]) =
          (tagEncode β wake ++ spell (nearyUpper β) rest ++ nearyMarker β) ++
            [true] := by
              rw [tagEncode_append, tagEncode_append, ← marker_append_true,
                spell_nearyUpper, rest_eq, map_letter_tileHistory]
              simp [List.append_assoc]
      _ = spell (nearyLower β body) rest ++ [true] := encoded_eq
      _ = tagEncode β
          (TagLetter.c :: nearyBody body first.head ++ [TagLetter.b] ++
            produced (tagOutput body) history) := by
            rw [rest_eq,
              spell_nearyLower_tileHistory_append_true β body first history]
  exact ⟨first, history, rest_eq, semantic_eq⟩

/-- The decoded second stable residual has incompatible length residue modulo `β - 1`. -/
theorem swappedDeltaThree_history_false (β : Nat) (body wake : List TagLetter)
    (β_large : 2 < β) (body_divisible : β - 1 ∣ body.length)
    (wake_length : wake.length = β - 2)
    (first : Stroke TagLetter β) (history : List (Stroke TagLetter β))
    (semantic_eq :
      wake ++ consumed (first :: history) ++ [TagLetter.b] =
        TagLetter.c :: nearyBody body first.head ++ [TagLetter.b] ++
          produced (tagOutput body) history) : False := by
  have consumed_mod := consumed_length_modEq β (by omega) (first :: history)
  have produced_mod := produced_length_modEq β body body_divisible history
  have payload_mod :=
    nearyBody_length_modEq_zero β body body_divisible first.head
  have one_mod : 1 ≡ 1 [MOD β - 1] := Nat.ModEq.refl 1
  have wake_mod : wake.length ≡ β - 2 [MOD β - 1] := by
    rw [wake_length]
  have left_raw :
      (wake ++ consumed (first :: history) ++ [TagLetter.b]).length ≡
        (β - 2) + (history.length + 1) + 1 [MOD β - 1] := by
    simpa [List.length_append, Nat.add_assoc] using
      wake_mod.add (consumed_mod.add one_mod)
  have beta_mod : β ≡ 1 [MOD β - 1] := by
    have beta_eq : β = (β - 1) + 1 := by omega
    rw [beta_eq]
    exact Nat.add_modEq_left
  have normalized_left :
      (β - 2) + (history.length + 1) + 1 ≡
        history.length + 1 [MOD β - 1] := by
    have shifted := beta_mod.add (Nat.ModEq.refl history.length)
    convert shifted using 1 <;> omega
  have left_mod :
      (wake ++ consumed (first :: history) ++ [TagLetter.b]).length ≡
        history.length + 1 [MOD β - 1] :=
    left_raw.trans normalized_left
  have right_mod :
      (TagLetter.c :: nearyBody body first.head ++ [TagLetter.b] ++
          produced (tagOutput body) history).length ≡
        history.length + 2 [MOD β - 1] := by
    simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      one_mod.add (payload_mod.add (one_mod.add produced_mod))
  have equation_mod :
      (wake ++ consumed (first :: history) ++ [TagLetter.b]).length ≡
        (TagLetter.c :: nearyBody body first.head ++ [TagLetter.b] ++
          produced (tagOutput body) history).length [MOD β - 1] := by
    rw [semantic_eq]
  exact adjacent_residues_false β_large <|
    left_mod.symm.trans (equation_mod.trans right_mod)

/-- Neary's padded body congruence excludes the second stable nonterminal residual. -/
theorem swappedDeltaThree_residual_false (β : Nat) (body wake : List TagLetter)
    (β_large : 2 < β) (body_divisible : β - 1 ∣ body.length)
    (wake_length : wake.length = β - 2) (rest : List NearyTile)
    (residual :
      tagEncode β wake ++ spell (nearyUpper β) rest ++ nearyMarker β =
        spell (nearyLower β body) rest) : False := by
  obtain ⟨first, history, _, semantic_eq⟩ :=
    swappedDeltaThree_history_of_residual β body wake (by omega) rest residual
  exact swappedDeltaThree_history_false β body wake β_large body_divisible wake_length
    first history semantic_eq

/-- No body of Neary-congruent length realizes the complete first fringe pair. -/
theorem swappedDeltaOne_fringe_false {β : Nat} (β_large : 2 < β)
    (body : List TagLetter) (body_divisible : β - 1 ∣ body.length)
    (word : List NearyTile) (suffix : List Bool)
    (upper_eq :
      spell (nearyUpper β) word ++ nearyMarker β =
        SwappedSetterResidual.deltaOneUpper β ++ suffix)
    (lower_eq : spell (nearyLower β body) word = suffix) : False := by
  obtain ⟨rest, _, residual⟩ :=
    SwappedSetterResidual.deltaOne_residual_decomposition (by omega) body word suffix
      upper_eq lower_eq
  exact swappedDeltaOne_residual_false β body β_large body_divisible rest residual

/-- No body of Neary-congruent length realizes the complete second fringe pair. -/
theorem swappedDeltaThree_fringe_false {β : Nat} (β_large : 2 < β)
    (body : List TagLetter) (body_divisible : β - 1 ∣ body.length)
    (word : List NearyTile) (suffix : List Bool)
    (upper_eq :
      spell (nearyUpper β) word ++ nearyMarker β = tagCode β .b ++ suffix)
    (lower_eq :
      spell (nearyLower β body) word = List.replicate (β - 1) false ++ suffix) : False := by
  obtain ⟨wake, rest, wake_length, _, residual⟩ :=
    SwappedSetterResidual.deltaThree_residual_decomposition (by omega) body word suffix
      upper_eq lower_eq
  exact swappedDeltaThree_residual_false β body wake β_large body_divisible wake_length rest
    residual

end MatrixMortality
