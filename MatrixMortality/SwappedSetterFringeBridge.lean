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

/-- The source projection stated directly from the physical body's checked head endpoint. -/
theorem sourceFringe_of_lower_prefix_of_head_b (β : Nat) (beta_pos : 0 < β)
    (body : List TagLetter) (body_head : body.head? = some .b)
    (word : List NearyTile) (lowerPrefix : List Bool)
    (isPrefix : lowerPrefix <+: spell (nearyLower β body) word)
    (prefix_bound : lowerPrefix.length ≤ β + 2) :
    SourceFringe lowerPrefix := by
  cases body with
  | nil => simp at body_head
  | cons head tail =>
      have head_eq : head = .b := by simpa using body_head
      subst head
      exact sourceFringe_of_lower_prefix β beta_pos tail word lowerPrefix isPrefix prefix_bound

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

/-- The target projection stated directly from the physical body's checked final endpoint. -/
theorem targetFringe_of_final_erase_of_getLast?_b (β : Nat) (beta_pos : 0 < β)
    (body : List TagLetter) (body_last : body.getLast? = some .b)
    (past : List NearyTile) (letter : TagLetter) :
    BlockTargetFringe (β + 2)
      ((spell (nearyLower β body) (past ++ [.erase letter])).rtake (β + 2)) := by
  induction body using List.reverseRecOn with
  | nil => simp at body_last
  | append_singleton front last induction =>
      have last_eq : last = .b := by simpa using body_last
      subst last
      exact targetFringe_of_final_erase β beta_pos front past letter

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

/-- The nontrivial target projection stated from the physical body's checked final endpoint. -/
theorem targetFringe_of_nontrivial_final_erase_of_getLast?_b
    (β : Nat) (beta_pos : 0 < β)
    (body : List TagLetter) (body_last : body.getLast? = some .b)
    (past : List NearyTile) (letter : TagLetter) (past_ne : past ≠ []) :
    ∃ phases,
      2 ≤ phases.length ∧
        phases.getLast? = some false ∧
          (spell (nearyLower β body) (past ++ [.erase letter])).rtake (β + 2) =
            (spell fringeBlock phases).rtake (β + 2) := by
  induction body using List.reverseRecOn with
  | nil => simp at body_last
  | append_singleton front last induction =>
      have last_eq : last = .b := by simpa using body_last
      subst last
      exact targetFringe_of_nontrivial_final_erase β beta_pos front past letter past_ne

private theorem phaseSpelling_last_false {phases : List Bool}
    (phases_ne : phases ≠ []) :
    (spell fringeBlock phases).getLast? = some false := by
  induction phases using List.reverseRecOn with
  | nil => contradiction
  | append_singleton phases phase induction =>
      rw [spell_append]
      cases phase <;> simp [spell, fringeBlock]

private theorem spelling_normal_of_two_phases {phases : List Bool}
    (phase_length : 2 ≤ phases.length)
    (phase_last : phases.getLast? = some false) :
    (∃ zeros,
        2 ≤ zeros ∧
          spell fringeBlock phases = List.replicate zeros false) ∨
      (∃ front zeros,
        2 ≤ zeros ∧
          spell fringeBlock phases =
            front ++ [true, true] ++ List.replicate zeros false) := by
  induction phases using List.reverseRecOn with
  | nil => simp at phase_length
  | append_singleton initial phase induction =>
      have phase_eq : phase = false := by simpa using phase_last
      subst phase
      have initial_ne : initial ≠ [] := by
        intro initial_empty
        subst initial
        simp at phase_length
      have initial_last := phaseSpelling_last_false initial_ne
      have source : SourceFringe (spell fringeBlock initial) := by
        exact ⟨initial, List.prefix_refl _⟩
      rcases sourceFringe_lastTrue_normal source initial_last with allZeros | lastTrue
      · left
        obtain ⟨zeros, zeros_pos, initial_eq⟩ := allZeros
        refine ⟨zeros + 1, by omega, ?_⟩
        rw [spell_append, initial_eq]
        simp [spell, fringeBlock, List.replicate_succ']
      · right
        obtain ⟨front, frontPhases, zeros, zeros_pos, front_eq, initial_eq⟩ := lastTrue
        refine ⟨front, zeros + 1, by omega, ?_⟩
        rw [spell_append, initial_eq]
        simp [spell, fringeBlock, List.replicate_succ']

private theorem rtake_all_false_target {width zeros : Nat}
    (width_ge : 3 ≤ width) (zeros_ge : 2 ≤ zeros) :
    TargetFringe width ((List.replicate zeros false).rtake width) := by
  have min_ge : 2 ≤ min width zeros := by omega
  refine ⟨?_, Or.inl ⟨min width zeros, min_ge, ?_⟩⟩
  · simp [List.rtake_eq_reverse_take_reverse]
  · simp [List.rtake_eq_reverse_take_reverse]

private theorem rtake_pair_target (width : Nat) (front : List Bool) (zeros : Nat)
    (width_ge : 3 ≤ width) (zeros_ge : 2 ≤ zeros) :
    TargetFringe width
      ((front ++ [true, true] ++ List.replicate zeros false).rtake width) := by
  by_cases window_inside_zeros : width ≤ zeros
  · have taken :
        (front ++ [true, true] ++ List.replicate zeros false).rtake width =
          List.replicate width false := by
      rw [List.rtake_eq_reverse_take_reverse]
      simp only [List.reverse_append, List.reverse_replicate, List.reverse_cons,
        List.reverse_nil]
      rw [List.take_append_of_le_length (by simpa using window_inside_zeros)]
      simpa using window_inside_zeros
    rw [taken]
    exact ⟨by simp, Or.inl ⟨width, by omega, rfl⟩⟩
  · have zeros_lt : zeros < width := by omega
    by_cases pair_inside : zeros + 2 ≤ width
    · let retainedFront := front.rtake (width - (zeros + 2))
      have zeros_le : zeros ≤ width := zeros_lt.le
      have remaining_ge : 2 ≤ width - zeros := by omega
      have pair_take :
          List.take (width - zeros) ([true, true] ++ front.reverse) =
            [true, true] ++ List.take (width - (zeros + 2)) front.reverse := by
        rw [List.take_append]
        have first_take : List.take (width - zeros) [true, true] = [true, true] :=
          List.take_of_length_le (by simpa using remaining_ge)
        rw [first_take]
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
        congr 1
      have taken :
          (front ++ [true, true] ++ List.replicate zeros false).rtake width =
            retainedFront ++ [true, true] ++ List.replicate zeros false := by
        rw [List.rtake_eq_reverse_take_reverse]
        simp only [List.reverse_append, List.reverse_replicate, List.reverse_cons,
          List.reverse_nil]
        rw [List.take_append]
        simp only [List.length_replicate, List.take_replicate,
          Nat.min_eq_right zeros_le, List.reverse_append, List.reverse_replicate]
        have pair_take' :
            List.take (width - zeros) ([] ++ [true] ++ [true] ++ front.reverse) =
              [true, true] ++ List.take (width - (zeros + 2)) front.reverse := by
          simpa using pair_take
        rw [pair_take']
        simp [retainedFront, List.rtake_eq_reverse_take_reverse]
      rw [taken]
      refine ⟨?_, Or.inr <| Or.inl ⟨retainedFront, zeros, zeros_ge, rfl⟩⟩
      have retained_le : retainedFront.length ≤ width - (zeros + 2) := by
        unfold retainedFront
        rw [List.rtake_eq_reverse_take_reverse, List.length_reverse]
        exact List.length_take_le (width - (zeros + 2)) front.reverse
      simp only [List.length_append, List.length_cons, List.length_nil,
        List.length_replicate]
      omega
    · have width_eq : width = zeros + 1 := by omega
      have taken :
          (front ++ [true, true] ++ List.replicate zeros false).rtake width =
            true :: List.replicate zeros false := by
        rw [List.rtake_eq_reverse_take_reverse]
        simp only [List.reverse_append, List.reverse_replicate, List.reverse_cons,
          List.reverse_nil]
        rw [width_eq, List.take_append]
        simp
      rw [taken]
      refine ⟨by simp; omega, Or.inr <| Or.inr ⟨by simp; omega, ?_⟩⟩
      rw [show width - 1 = zeros by omega]

/-- A two-phase exact target witness satisfies the broad physical target normal form. -/
theorem targetFringe_of_blockWitness (width : Nat) (word : List Bool)
    (width_ge : 3 ≤ width) (phases : List Bool)
    (phase_length : 2 ≤ phases.length)
    (phase_last : phases.getLast? = some false)
    (word_eq : word = (spell fringeBlock phases).rtake width) :
    TargetFringe width word := by
  subst word
  rcases spelling_normal_of_two_phases phase_length phase_last with allZeros | lastTrue
  · obtain ⟨zeros, zeros_ge, spelling_eq⟩ := allZeros
    rw [spelling_eq]
    exact rtake_all_false_target width_ge zeros_ge
  · obtain ⟨front, zeros, zeros_ge, spelling_eq⟩ := lastTrue
    rw [spelling_eq]
    exact rtake_pair_target width front zeros width_ge zeros_ge

/-- The strengthened exact target language embeds in the broad physical target language. -/
theorem targetFringe_of_nontrivialBlockTarget (width : Nat) (word : List Bool)
    (width_ge : 3 ≤ width)
    (target : ∃ phases,
      2 ≤ phases.length ∧
        phases.getLast? = some false ∧
          word = (spell fringeBlock phases).rtake width) :
    TargetFringe width word := by
  obtain ⟨phases, phase_length, phase_last, word_eq⟩ := target
  exact targetFringe_of_blockWitness width word width_ge phases phase_length phase_last word_eq

end MatrixMortality.SwappedSetterFringe
