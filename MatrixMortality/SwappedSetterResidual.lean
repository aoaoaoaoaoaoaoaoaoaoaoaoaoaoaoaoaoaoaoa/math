import MatrixMortality.NearyEncoding

/-!
# Swapped-setter residual decomposition

The two stable nonterminal depth-one residuals of the swapped ternary setter determine exact
binary prefix pairs. This file removes those prefixes and exposes the residual Neary equations
consumed by the compiler congruence argument.
-/

namespace MatrixMortality.SwappedSetterResidual

/-- Unmatched upper fringe for `Δ = 14ρ/3 - 1`. -/
def deltaOneUpper (β : Nat) : List Bool :=
  [true, true, true] ++ List.replicate (β - 1) false

/-- Intermediate fringe after removing the forced leading `D_c`. -/
def deltaOneMiddle (β : Nat) : List Bool :=
  [true, true] ++ List.replicate β false

private theorem deltaOne_scan {β : Nat} (beta_pos : 0 < β) :
    pulseScan β .virgin (deltaOneUpper β) = some (.gap (β - 1)) := by
  unfold deltaOneUpper
  simp only [List.cons_append, List.nil_append, pulseScan, pulseBit, Option.bind_some,
    true_or, if_true]
  simpa using pulseScan_false_replicate β 0 (β - 1) (by omega)

private theorem deltaOne_false (β : Nat) (tail : List Bool) :
    deltaOneUpper (β + 1) ++ false :: tail =
      true :: (deltaOneMiddle (β + 1) ++ tail) := by
  simp [deltaOneUpper, deltaOneMiddle, List.replicate_succ', List.append_assoc]

private theorem deltaOne_ruleC (β : Nat) (bodyBits tail : List Bool) :
    deltaOneMiddle β ++ (true :: bodyBits ++ [true, false] ++ tail) =
      true ::
        (tagCode β .b ++ bodyBits ++ [true, false] ++ tail) := by
  simp [deltaOneMiddle, tagCode, List.append_assoc]

/-- The `14ρ/3 - 1` prefix pair forces `D_c,R_c`; removing them leaves the compiler residual
with lower prefix `H(b :: body)10`. -/
theorem deltaOne_residual_decomposition
    {β : Nat} (beta_large : 2 ≤ β) (body : List TagLetter)
    (word : List NearyTile) (suffix : List Bool)
    (upper_eq :
      spell (nearyUpper β) word ++ nearyMarker β = deltaOneUpper β ++ suffix)
    (lower_eq : spell (nearyLower β body) word = suffix) :
    ∃ rest,
      word = .erase .c :: .rule .c :: rest ∧
        spell (nearyUpper β) rest ++ nearyMarker β =
          tagCode β .b ++ tagEncode β body ++ [true, false] ++
            spell (nearyLower β body) rest := by
  have upper_scan :
      pulseScan β .virgin (spell (nearyUpper β) word ++ nearyMarker β) =
        some (.gap β) := by
    rw [spell_nearyUpper]
    exact pulseScan_encoded_final β (by omega) _
  have suffix_scan :
      pulseScan β (.gap (β - 1)) suffix = some (.gap β) := by
    have scanned := congrArg (pulseScan β .virgin) upper_eq
    rw [upper_scan, pulseScan_append, deltaOne_scan (by omega)] at scanned
    exact scanned.symm
  rw [← lower_eq] at suffix_scan
  rw [← lower_eq] at upper_eq
  cases word with
  | nil =>
      change some (Pulse.gap (β - 1)) = some (Pulse.gap β) at suffix_scan
      have gap_eq := Option.some.inj suffix_scan
      have index_eq := Pulse.gap.inj gap_eq
      omega
  | cons first tail =>
      rw [show spell (nearyLower β body) (first :: tail) =
        nearyLower β body first ++ spell (nearyLower β body) tail by rfl,
        pulseScan_append] at suffix_scan
      cases first with
      | rule letter =>
          rw [pulseScan_nearyLower_rule_from_gap β (β - 1) body (by omega)] at suffix_scan
          simp [show β - 1 ≠ 0 by omega, show β - 1 ≠ β by omega] at suffix_scan
      | erase letter =>
          rw [pulseScan_nearyLower_erase] at suffix_scan
          simp only [show β - 1 < β by omega, if_true, Option.bind_some,
            show β - 1 + 1 = β by omega] at suffix_scan
          cases letter with
          | b =>
              have beta_split : β = (β - 1) + 1 := by omega
              rw [show spell (nearyUpper β) (.erase .b :: tail) =
                    nearyUpper β (.erase .b) ++ spell (nearyUpper β) tail by rfl,
                  show spell (nearyLower β body) (.erase .b :: tail) =
                    nearyLower β body (.erase .b) ++
                      spell (nearyLower β body) tail by rfl] at upper_eq
              simp only [nearyUpper, nearyLower, tagCode] at upper_eq
              rw [beta_split, List.replicate_succ] at upper_eq
              simp [deltaOneUpper] at upper_eq
          | c =>
              obtain ⟨pred, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : β ≠ 0)
              have middle_eq :
                  spell (nearyUpper (pred + 1)) tail ++ nearyMarker (pred + 1) =
                    deltaOneMiddle (pred + 1) ++ spell (nearyLower (pred + 1) body) tail := by
                have expanded := upper_eq
                change
                  true :: (spell (nearyUpper (pred + 1)) tail ++ nearyMarker (pred + 1)) =
                    deltaOneUpper (pred + 1) ++
                      (false :: spell (nearyLower (pred + 1) body) tail) at expanded
                rw [deltaOne_false pred] at expanded
                exact (List.cons.inj expanded).2
              cases tail with
              | nil =>
                  have length_eq := congrArg List.length middle_eq
                  simp [spell, nearyMarker, deltaOneMiddle] at length_eq
              | cons second rest =>
                  rw [show spell (nearyLower (pred + 1) body) (second :: rest) =
                    nearyLower (pred + 1) body second ++
                      spell (nearyLower (pred + 1) body) rest by rfl,
                    pulseScan_append] at suffix_scan
                  cases second with
                  | erase secondLetter =>
                      rw [pulseScan_nearyLower_erase] at suffix_scan
                      simp at suffix_scan
                  | rule secondLetter =>
                      cases secondLetter with
                      | b =>
                          have pred_pos : 0 < pred := by omega
                          rw [show spell (nearyUpper (pred + 1)) (.rule .b :: rest) =
                                nearyUpper (pred + 1) (.rule .b) ++
                                  spell (nearyUpper (pred + 1)) rest by rfl,
                              show spell (nearyLower (pred + 1) body)
                                  (.rule .b :: rest) =
                                nearyLower (pred + 1) body (.rule .b) ++
                                  spell (nearyLower (pred + 1) body) rest by rfl] at middle_eq
                          simp only [nearyUpper, nearyLower, tagCode] at middle_eq
                          rw [List.replicate_succ] at middle_eq
                          simp [deltaOneMiddle] at middle_eq
                      | c =>
                          refine ⟨rest, rfl, ?_⟩
                          change
                            true ::
                                (spell (nearyUpper (pred + 1)) rest ++
                                  nearyMarker (pred + 1)) =
                              deltaOneMiddle (pred + 1) ++
                                (true :: tagEncode (pred + 1) body ++ [true, false] ++
                                  spell (nearyLower (pred + 1) body) rest) at middle_eq
                          rw [deltaOne_ruleC] at middle_eq
                          exact (List.cons.inj middle_eq).2

private theorem lower_replicate_false_decomposition
    (β : Nat) (body : List TagLetter) (n : Nat)
    (word : List NearyTile) (suffix : List Bool)
    (lower_eq :
      spell (nearyLower β body) word = List.replicate n false ++ suffix) :
    ∃ (letters : List TagLetter) (rest : List NearyTile),
      letters.length = n ∧
        word = letters.map NearyTile.erase ++ rest ∧
        spell (nearyLower β body) rest = suffix := by
  induction n generalizing word with
  | zero =>
      refine ⟨[], word, rfl, rfl, ?_⟩
      simpa using lower_eq
  | succ n ih =>
      cases word with
      | nil => simp [spell, List.replicate_succ] at lower_eq
      | cons first tail =>
          rw [show spell (nearyLower β body) (first :: tail) =
            nearyLower β body first ++ spell (nearyLower β body) tail by rfl] at lower_eq
          cases first with
          | rule letter =>
              cases letter <;> simp [nearyLower, List.replicate_succ] at lower_eq
          | erase letter =>
              simp only [nearyLower, List.singleton_append, List.replicate_succ] at lower_eq
              have tail_eq := (List.cons.inj lower_eq).2
              obtain ⟨letters, rest, length_eq, word_eq, rest_eq⟩ := ih tail tail_eq
              refine ⟨letter :: letters, rest, by simp [length_eq], ?_, rest_eq⟩
              simp [word_eq]

private theorem spell_upper_erase_map (β : Nat) (letters : List TagLetter) :
    spell (nearyUpper β) (letters.map .erase) = tagEncode β letters := by
  rw [spell_nearyUpper]
  simp [List.map_map, Function.comp_def, NearyTile.letter]

/-- The `17ρ/3 - 1` prefix pair begins with `β - 1` erasures carried by `b :: wake`.
Removing them leaves a Neary equation with the `β - 2`-letter wake on the upper boundary. -/
theorem deltaThree_residual_decomposition
    {β : Nat} (beta_large : 3 ≤ β) (body : List TagLetter)
    (word : List NearyTile) (suffix : List Bool)
    (upper_eq :
      spell (nearyUpper β) word ++ nearyMarker β = tagCode β .b ++ suffix)
    (lower_eq :
      spell (nearyLower β body) word = List.replicate (β - 1) false ++ suffix) :
    ∃ wake rest,
      wake.length = β - 2 ∧
        word = .erase .b :: wake.map .erase ++ rest ∧
        tagEncode β wake ++ spell (nearyUpper β) rest ++ nearyMarker β =
          spell (nearyLower β body) rest := by
  obtain ⟨letters, rest, letters_length, word_eq, rest_eq⟩ :=
    lower_replicate_false_decomposition β body (β - 1) word suffix lower_eq
  have letters_nonempty : letters ≠ [] := by
    intro letters_empty
    subst letters
    simp at letters_length
    omega
  obtain ⟨first, wake, rfl⟩ := List.exists_cons_of_ne_nil letters_nonempty
  have wake_length : wake.length = β - 2 := by
    simp only [List.length_cons] at letters_length
    omega
  have stripped_upper :
      tagEncode β (first :: wake) ++
          (spell (nearyUpper β) rest ++ nearyMarker β) =
        tagCode β .b ++ suffix := by
    calc
      tagEncode β (first :: wake) ++
          (spell (nearyUpper β) rest ++ nearyMarker β) =
          spell (nearyUpper β) ((first :: wake).map .erase ++ rest) ++
            nearyMarker β := by
              rw [spell_append, spell_upper_erase_map]
              simp [List.append_assoc]
      _ = tagCode β .b ++ suffix := by simpa [word_eq] using upper_eq
  have first_eq : first = .b := by
    cases first with
    | b => rfl
    | c =>
        have wake_nonempty : wake ≠ [] := by
          intro wake_empty
          subst wake
          simp at wake_length
          omega
        obtain ⟨second, tail, rfl⟩ := List.exists_cons_of_ne_nil wake_nonempty
        have beta_split : β = (β - 1) + 1 := by omega
        rw [tagEncode_cons, tagEncode_cons] at stripped_upper
        simp only [tagCode] at stripped_upper
        have tails_eq := (List.cons.inj stripped_upper).2
        have heads_eq := congrArg List.head? tails_eq
        rw [beta_split, List.replicate_succ] at heads_eq
        cases second <;> simp at heads_eq
  subst first
  refine ⟨wake, rest, wake_length, ?_, ?_⟩
  · simp [word_eq]
  · rw [tagEncode_cons, List.append_assoc] at stripped_upper
    have core := List.append_cancel_left stripped_upper
    simpa [rest_eq, List.append_assoc] using core

end MatrixMortality.SwappedSetterResidual
