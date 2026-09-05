import MatrixMortality.NearyEncoding

/-!
# A charge obstruction to shifted Neary matches

Charge each bit by one, except that a zero-to-one transition has charge `-β`.
An encoded tag letter has charge one. With an incoming zero, a lower rule has
charge one modulo `β - 1` whenever the body length is divisible by `β - 1`.
Thus equal upper and lower words retain a boundary charge that the decimal
setter's `β + 2`-digit peeled heads cannot satisfy.
-/

namespace MatrixMortality

/-- Bit length minus `β + 1` times the number of zero-to-one transitions,
including the transition from the specified preceding bit. -/
def pulseCharge (β : Nat) : Bool → List Bool → ℤ
  | _, [] => 0
  | previous, bit :: rest =>
      (if previous = false ∧ bit = true then -(β : ℤ) else 1) +
        pulseCharge β bit rest

private theorem pulseCharge_replicate (β n : Nat) (bit : Bool) (rest : List Bool) :
    pulseCharge β bit (List.replicate n bit ++ rest) =
      n + pulseCharge β bit rest := by
  induction n with
  | zero => simp
  | succ n induction =>
      cases bit <;> simp [List.replicate_succ, pulseCharge, induction] <;> omega

private theorem pulseCharge_zeroRun {β n : Nat} (n_pos : 0 < n) (rest : List Bool) :
    pulseCharge β true (List.replicate n false ++ rest) =
      n + pulseCharge β false rest := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp [List.replicate_succ, pulseCharge, pulseCharge_replicate]
  omega

theorem pulseCharge_tagEncode {β : Nat} (β_pos : 0 < β)
    (letters : List TagLetter) (rest : List Bool) :
    pulseCharge β true (tagEncode β letters ++ rest) =
      letters.length + pulseCharge β true rest := by
  induction letters with
  | nil => simp
  | cons letter letters induction =>
      cases letter with
      | c => simp [tagEncode_cons, tagCode, pulseCharge, induction]; omega
      | b =>
          simp only [tagEncode_cons, tagCode, List.cons_append, List.nil_append]
          simp only [List.append_assoc]
          simp only [pulseCharge, Bool.true_eq_false, false_and, ↓reduceIte]
          rw [pulseCharge_zeroRun β_pos]
          simp [pulseCharge, induction]
          omega

/-- The lower spelling has the same charge as its role length modulo `β - 1`.
The arbitrary continuation records that every nonempty lower block ends in zero. -/
theorem pulseCharge_lower_modEq {β : Nat} (β_pos : 0 < β)
    {body : List TagLetter} (body_divisible : β - 1 ∣ body.length)
    (word : List NearyTile) (rest : List Bool) :
    pulseCharge β false (spell (nearyLower β body) word ++ rest) ≡
      word.length + pulseCharge β false rest [ZMOD (β : ℤ) - 1] := by
  have body_div : (β : ℤ) - 1 ∣ (body.length : ℤ) := by
    have cast_div : ((β - 1 : Nat) : ℤ) ∣ (body.length : ℤ) := by
      exact_mod_cast body_divisible
    simpa [Nat.cast_sub (by omega : 1 ≤ β)] using cast_div
  have step_mod (tile : NearyTile) (tail : List Bool) :
      pulseCharge β false (nearyLower β body tile ++ tail) ≡
        1 + pulseCharge β false tail [ZMOD (β : ℤ) - 1] := by
    cases tile with
    | erase letter => simp [nearyLower, pulseCharge]
    | rule letter =>
        cases letter with
        | b =>
            simp only [nearyLower, List.cons_append, List.nil_append, pulseCharge,
              and_self, ↓reduceIte, Bool.true_eq_false, false_and,
              Bool.false_eq_true]
            rw [Int.modEq_iff_dvd]
            have difference :
                1 + pulseCharge β false tail -
                  (-(β : ℤ) + (1 + (1 + pulseCharge β false tail))) = (β : ℤ) - 1 := by
              ring
            rw [difference]
        | c =>
            simp only [nearyLower, List.cons_append, List.nil_append, List.append_assoc,
              pulseCharge, and_self, ↓reduceIte]
            rw [pulseCharge_tagEncode β_pos]
            simp only [pulseCharge, Bool.true_eq_false, false_and, ↓reduceIte]
            rw [Int.modEq_iff_dvd]
            have difference :
                1 + pulseCharge β false tail -
                  (-(β : ℤ) + (body.length + (1 + (1 + pulseCharge β false tail)))) =
                    ((β : ℤ) - 1) - body.length := by ring
            rw [difference]
            exact dvd_sub (dvd_refl _) body_div
  induction word with
  | nil => simp [spell]
  | cons tile word induction =>
      have first := step_mod tile (spell (nearyLower β body) word ++ rest)
      have joined := first.trans ((Int.ModEq.refl 1).add induction)
      simpa [spell, List.append_assoc, add_assoc, add_comm] using joined

/-- A shifted match with a single zero run in its head retains the head's
length modulo `β - 1`; the ordinary marker has length `β + 1`. -/
theorem shifted_neary_match_onePulse_length {β : Nat} (β_pos : 0 < β)
    {body : List TagLetter} (body_divisible : β - 1 ∣ body.length)
    (word : List NearyTile) {ones zeros : Nat} (zeros_pos : 0 < zeros)
    (matching : spell (nearyUpper β) word ++ nearyMarker β =
      (List.replicate ones true ++ List.replicate zeros false) ++
        spell (nearyLower β body) word) :
    (ones : ℤ) + zeros ≡ (β : ℤ) + 1 [ZMOD (β : ℤ) - 1] := by
  have equality := congrArg (pulseCharge β true) matching
  rw [spell_nearyUpper, pulseCharge_tagEncode β_pos, List.length_map] at equality
  have marker_charge : pulseCharge β true (nearyMarker β) = (β : ℤ) + 1 := by
    change 1 + pulseCharge β true (List.replicate β false) = _
    have zero_run := pulseCharge_zeroRun (β := β) β_pos []
    simpa [pulseCharge, add_comm] using zero_run
  rw [marker_charge, List.append_assoc, pulseCharge_replicate,
    pulseCharge_zeroRun zeros_pos] at equality
  have lower_mod := pulseCharge_lower_modEq β_pos body_divisible word []
  simp only [List.append_nil, pulseCharge, add_zero] at lower_mod
  have joined := (Int.ModEq.refl ((ones : ℤ) + zeros)).add lower_mod
  have full :
      (ones : ℤ) + zeros + pulseCharge β false (spell (nearyLower β body) word) =
        (β : ℤ) + 1 + (word.length : ℤ) := by linarith [equality]
  have rearranged :
      (ones : ℤ) + zeros + (word.length : ℤ) ≡
        (β : ℤ) + 1 + (word.length : ℤ) [ZMOD (β : ℤ) - 1] := by
    rw [full] at joined
    exact joined.symm
  exact Int.ModEq.add_right_cancel' _ rearranged

/-- The decimal setter's one-pulse head of length `β + 2` lies in the wrong
charge class for every compiler-emitted body. -/
theorem shifted_neary_match_onePulse_impossible {β : Nat} (β_large : 2 < β)
    {body : List TagLetter} (body_divisible : β - 1 ∣ body.length)
    (word : List NearyTile) {ones zeros : Nat}
    (zeros_pos : 0 < zeros) (head_length : ones + zeros = β + 2) :
    spell (nearyUpper β) word ++ nearyMarker β ≠
      (List.replicate ones true ++ List.replicate zeros false) ++
        spell (nearyLower β body) word := by
  intro matching
  have charge_mod := shifted_neary_match_onePulse_length
    (by omega) body_divisible word zeros_pos matching
  have length_cast : (ones : ℤ) + zeros = (β : ℤ) + 2 := by exact_mod_cast head_length
  rw [length_cast, Int.modEq_iff_dvd] at charge_mod
  have unit_div : (β : ℤ) - 1 ∣ (1 : ℤ) := by
    have negative_one : (β : ℤ) + 1 - ((β : ℤ) + 2) = -1 := by ring
    rw [negative_one] at charge_mod
    exact dvd_neg.mp charge_mod
  have bound := Int.le_of_dvd (by norm_num : (0 : ℤ) < 1) unit_div
  omega

end MatrixMortality
