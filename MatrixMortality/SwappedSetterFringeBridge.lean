import MatrixMortality.SwappedSetterFringeLanguage

/-!
# Physical swapped-setter fringe projections

The compiler body begins and ends in `b`. These endpoint facts replace the body-dependent
prefix and suffix of every `c`-rule by the body-independent block language used by the
depth-one fringe classifier.
-/

namespace MatrixMortality.SwappedSetterFringe

/-- Reversal of `fringeBlock`, used to read target suffixes from right to left. -/
def reverseFringeBlock : Bool → List Bool
  | true => [false, true, true]
  | false => [false]

/-- Source-prefix projection of one Neary tile. A `c`-rule is truncated after the encoded
body's initial `b`; the remaining zeroes are represented as erasure blocks. -/
def sourceFringePhase (β : Nat) : NearyTile → List Bool
  | .rule .c => true :: List.replicate (β - 1) false
  | .rule .b => [true]
  | .erase _ => [false]

/-- Extend the source-prefix projection to tile words. -/
def sourceFringePhases (β : Nat) (word : List NearyTile) : List Bool :=
  (word.map (sourceFringePhase β)).flatten

private theorem sourceFringePhase_length_pos (β : Nat) (tile : NearyTile) :
    0 < (sourceFringePhase β tile).length := by
  cases tile with
  | rule letter => cases letter <;> simp [sourceFringePhase]
  | erase letter => simp [sourceFringePhase]

private theorem sourceFringePhases_length_ge (β : Nat) (word : List NearyTile) :
    word.length ≤ (sourceFringePhases β word).length := by
  induction word with
  | nil => rfl
  | cons tile word induction =>
      rw [show sourceFringePhases β (tile :: word) =
          sourceFringePhase β tile ++ sourceFringePhases β word by rfl]
      rw [List.length_cons, List.length_append]
      have phase_pos := sourceFringePhase_length_pos β tile
      omega

private theorem spell_fringeBlock_replicate_false (n : Nat) :
    spell fringeBlock (List.replicate n false) = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n induction =>
      rw [List.replicate_succ]
      change fringeBlock false ++ spell fringeBlock (List.replicate n false) = _
      rw [induction]
      rfl

private theorem take_eq_of_take_eq {n k : Nat} {x y : List Bool}
    (taken : List.take n x = List.take n y) (bound : k ≤ n) :
    List.take k x = List.take k y := by
  have retaken := congrArg (List.take k) taken
  simpa [List.take_take, Nat.min_eq_left bound] using retaken

private theorem take_append_congr {n : Nat} (stem x y : List Bool)
    (taken : List.take n x = List.take n y) :
    List.take n (stem ++ x) = List.take n (stem ++ y) := by
  rw [List.take_append, List.take_append]
  exact congrArg (List.take n stem ++ ·) <|
    take_eq_of_take_eq taken (Nat.sub_le n stem.length)

private theorem source_rule_c_fringe (β : Nat) (beta_pos : 0 < β)
    (tail : List TagLetter) :
    List.take (β + 2) (nearyLower β (.b :: tail) (.rule .c)) =
      spell fringeBlock (sourceFringePhase β (.rule .c)) := by
  unfold sourceFringePhase
  change List.take (β + 2)
      ([true] ++ tagEncode β (.b :: tail) ++ [true, false]) =
    fringeBlock true ++ spell fringeBlock (List.replicate (β - 1) false)
  rw [spell_fringeBlock_replicate_false]
  simp only [tagEncode_cons, tagCode, fringeBlock]
  have beta_split : β = (β - 1) + 1 := by omega
  rw [beta_split, List.replicate_succ]
  simp

theorem sourceFringe_take (β : Nat) (beta_pos : 0 < β)
    (tail : List TagLetter) (word : List NearyTile) :
    List.take (β + 2) (spell (nearyLower β (.b :: tail)) word) =
      List.take (β + 2) (spell fringeBlock (sourceFringePhases β word)) := by
  induction word with
  | nil => rfl
  | cons tile word induction =>
      rw [show spell (nearyLower β (.b :: tail)) (tile :: word) =
          nearyLower β (.b :: tail) tile ++
            spell (nearyLower β (.b :: tail)) word by rfl]
      rw [show sourceFringePhases β (tile :: word) =
          sourceFringePhase β tile ++ sourceFringePhases β word by rfl]
      rw [spell_append]
      cases tile with
      | rule letter =>
          cases letter with
          | b =>
              change List.take (β + 2)
                  ([true, true, false] ++ spell (nearyLower β (.b :: tail)) word) =
                List.take (β + 2)
                  ([true, true, false] ++ spell fringeBlock (sourceFringePhases β word))
              exact take_append_congr [true, true, false] _ _ induction
          | c =>
              have actual_long :
                  β + 2 ≤ (nearyLower β (.b :: tail) (.rule .c)).length := by
                simp [nearyLower, tagEncode_cons, tagCode]
              have shadow_length :
                  (spell fringeBlock (sourceFringePhase β (.rule .c))).length =
                    β + 2 := by
                rw [sourceFringePhase, spell]
                simp [fringeBlock]
                omega
              rw [List.take_append_of_le_length actual_long,
                List.take_append_of_le_length (shadow_length.ge)]
              rw [source_rule_c_fringe β beta_pos tail]
              simp [← shadow_length]
      | erase letter =>
          change List.take (β + 2)
              ([false] ++ spell (nearyLower β (.b :: tail)) word) =
            List.take (β + 2)
              ([false] ++ spell fringeBlock (sourceFringePhases β word))
          exact take_append_congr [false] _ _ induction

/-- Every bounded actual lower prefix lies in the body-independent source-fringe language. -/
theorem sourceFringe_of_lower_prefix (β : Nat) (beta_pos : 0 < β)
    (tail : List TagLetter) (word : List NearyTile) (lowerPrefix : List Bool)
    (isPrefix : lowerPrefix <+:
      spell (nearyLower β (.b :: tail)) word)
    (prefix_bound : lowerPrefix.length ≤ β + 2) :
    SourceFringe lowerPrefix := by
  refine ⟨sourceFringePhases β word, ?_⟩
  rw [List.prefix_iff_eq_take]
  have projected := sourceFringe_take β beta_pos tail word
  have boundedProjection := take_eq_of_take_eq projected.symm prefix_bound
  rw [boundedProjection]
  exact List.prefix_iff_eq_take.mp isPrefix

private theorem spell_reverse {Role : Type*} (output : Role → List Bool)
    (roles : List Role) :
    spell (fun role => (output role).reverse) roles.reverse =
      (spell output roles).reverse := by
  induction roles with
  | nil => rfl
  | cons role roles induction =>
      rw [List.reverse_cons, spell_append, induction]
      simp [spell, List.reverse_append]

private theorem spell_reverseFringeBlock_replicate_false (n : Nat) :
    spell reverseFringeBlock (List.replicate n false) = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n induction =>
      rw [List.replicate_succ]
      change reverseFringeBlock false ++
          spell reverseFringeBlock (List.replicate n false) = _
      rw [induction]
      rfl

private theorem target_rule_c_fringe (β : Nat) (beta_pos : 0 < β)
    (front : List TagLetter) :
    List.take (β + 2) (nearyLower β (front ++ [.b]) (.rule .c)).reverse =
      spell reverseFringeBlock (sourceFringePhase β (.rule .c)) := by
  unfold sourceFringePhase
  change List.take (β + 2)
      ([true] ++ tagEncode β (front ++ [.b]) ++ [true, false]).reverse =
    reverseFringeBlock true ++
      spell reverseFringeBlock (List.replicate (β - 1) false)
  rw [tagEncode_append, List.reverse_append, spell_reverseFringeBlock_replicate_false]
  simp only [tagEncode_cons, tagEncode_nil, List.append_nil, tagCode, reverseFringeBlock,
    List.reverse_cons, List.reverse_nil]
  have beta_split : β = (β - 1) + 1 := by omega
  rw [beta_split, List.replicate_succ]
  simp

private def reverseNearyLower (β : Nat) (body : List TagLetter) (tile : NearyTile) :
    List Bool :=
  (nearyLower β body tile).reverse

private theorem targetFringe_take_reversed (β : Nat) (beta_pos : 0 < β)
    (front : List TagLetter) (word : List NearyTile) :
    List.take (β + 2)
        (spell (reverseNearyLower β (front ++ [.b])) word) =
      List.take (β + 2)
        (spell reverseFringeBlock (sourceFringePhases β word)) := by
  induction word with
  | nil => rfl
  | cons tile word induction =>
      rw [show spell (reverseNearyLower β (front ++ [.b])) (tile :: word) =
        reverseNearyLower β (front ++ [.b]) tile ++
          spell (reverseNearyLower β (front ++ [.b])) word by rfl]
      rw [show sourceFringePhases β (tile :: word) =
          sourceFringePhase β tile ++ sourceFringePhases β word by rfl]
      rw [spell_append]
      cases tile with
      | rule letter =>
          cases letter with
          | b =>
              rw [show reverseNearyLower β (front ++ [.b]) (.rule .b) =
                [false, true, true] by rfl]
              rw [show sourceFringePhase β (.rule .b) = [true] by rfl]
              change List.take (β + 2) ([false, true, true] ++ _) =
                List.take (β + 2) ([false, true, true] ++ _)
              exact take_append_congr [false, true, true] _ _ induction
          | c =>
              have actual_long :
                  β + 2 ≤
                    (reverseNearyLower β (front ++ [.b]) (.rule .c)).length := by
                simp [reverseNearyLower, nearyLower, tagEncode_append, tagCode]
                omega
              have shadow_length :
                  (spell reverseFringeBlock (sourceFringePhase β (.rule .c))).length =
                    β + 2 := by
                rw [sourceFringePhase, spell]
                simp [reverseFringeBlock]
                omega
              rw [List.take_append_of_le_length actual_long,
                List.take_append_of_le_length (shadow_length.ge)]
              rw [show List.take (β + 2)
                  (reverseNearyLower β (front ++ [.b]) (.rule .c)) =
                spell reverseFringeBlock (sourceFringePhase β (.rule .c)) by
                  simpa [reverseNearyLower] using target_rule_c_fringe β beta_pos front]
              simp [← shadow_length]
      | erase letter =>
          rw [show reverseNearyLower β (front ++ [.b]) (.erase letter) = [false] by rfl]
          rw [show sourceFringePhase β (.erase letter) = [false] by rfl]
          change List.take (β + 2) ([false] ++ _) = List.take (β + 2) ([false] ++ _)
          exact take_append_congr [false] _ _ induction

theorem targetFringe_reverse_take (β : Nat) (beta_pos : 0 < β)
    (front : List TagLetter) (word : List NearyTile) :
    List.take (β + 2) (spell (nearyLower β (front ++ [.b])) word).reverse =
      List.take (β + 2)
        (spell reverseFringeBlock (sourceFringePhases β word.reverse)) := by
  have reversed := spell_reverse (nearyLower β (front ++ [.b])) word
  have projected := targetFringe_take_reversed β beta_pos front word.reverse
  rw [← reversed]
  change List.take (β + 2)
      (spell (fun role => (nearyLower β (front ++ [.b]) role).reverse) word.reverse) = _
    at projected
  exact projected

/-- Phase word whose block spelling has the same bounded suffix as an actual target word. -/
def targetFringePhases (β : Nat) (word : List NearyTile) : List Bool :=
  (sourceFringePhases β word.reverse).reverse

private theorem reverseFringeBlock_eq (phase : Bool) :
    (fringeBlock phase).reverse = reverseFringeBlock phase := by
  cases phase <;> rfl

theorem targetFringe_rtake (β : Nat) (beta_pos : 0 < β)
    (front : List TagLetter) (word : List NearyTile) :
    (spell (nearyLower β (front ++ [.b])) word).rtake (β + 2) =
      (spell fringeBlock (targetFringePhases β word)).rtake (β + 2) := by
  have projected := targetFringe_reverse_take β beta_pos front word
  have shadow_reversed :
      (spell fringeBlock (targetFringePhases β word)).reverse =
        spell reverseFringeBlock (sourceFringePhases β word.reverse) := by
    rw [← spell_reverse]
    simp only [targetFringePhases, List.reverse_reverse]
    apply congrArg (fun side => spell side (sourceFringePhases β word.reverse))
    funext phase
    exact reverseFringeBlock_eq phase
  rw [List.rtake_eq_reverse_take_reverse, List.rtake_eq_reverse_take_reverse,
    shadow_reversed, projected]

private theorem targetFringePhases_getLast?_erase (β : Nat)
    (past : List NearyTile) (letter : TagLetter) :
    (targetFringePhases β (past ++ [.erase letter])).getLast? = some false := by
  simp [targetFringePhases, sourceFringePhases, sourceFringePhase]

private theorem targetFringePhases_length_ge_two (β : Nat)
    (past : List NearyTile) (letter : TagLetter) (past_ne : past ≠ []) :
    2 ≤ (targetFringePhases β (past ++ [.erase letter])).length := by
  have projected :=
    sourceFringePhases_length_ge β (past ++ [NearyTile.erase letter]).reverse
  rw [targetFringePhases, List.length_reverse]
  rw [List.length_reverse, List.length_append, List.length_singleton] at projected
  have past_pos := List.length_pos_of_ne_nil past_ne
  omega

/-- An actual target word ending in an erasure lies in the exact block-suffix language when the
Neary body ends in `b`. -/
theorem targetFringe_of_final_erase (β : Nat) (beta_pos : 0 < β)
    (front : List TagLetter) (past : List NearyTile) (letter : TagLetter) :
    BlockTargetFringe (β + 2)
      ((spell (nearyLower β (front ++ [.b])) (past ++ [.erase letter])).rtake (β + 2)) := by
  refine ⟨targetFringePhases β (past ++ [.erase letter]),
    targetFringePhases_getLast?_erase β past letter, ?_⟩
  exact targetFringe_rtake β beta_pos front (past ++ [.erase letter])

/-- A target with a tile before its final erasure has an exact block-suffix witness containing
at least two fringe phases. -/
theorem targetFringe_of_nontrivial_final_erase (β : Nat) (beta_pos : 0 < β)
    (front : List TagLetter) (past : List NearyTile) (letter : TagLetter)
    (past_ne : past ≠ []) :
    ∃ phases,
      2 ≤ phases.length ∧
        phases.getLast? = some false ∧
          (spell (nearyLower β (front ++ [.b]))
              (past ++ [.erase letter])).rtake (β + 2) =
            (spell fringeBlock phases).rtake (β + 2) := by
  refine ⟨targetFringePhases β (past ++ [.erase letter]),
    targetFringePhases_length_ge_two β past letter past_ne,
    targetFringePhases_getLast?_erase β past letter, ?_⟩
  exact targetFringe_rtake β beta_pos front (past ++ [.erase letter])

end MatrixMortality.SwappedSetterFringe
