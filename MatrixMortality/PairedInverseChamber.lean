import Mathlib.Data.List.Chain
import MatrixMortality.CancellativeProjectiveNoGo

/-!
# Paired inverse chambers

Positive paired residuals occupy reduced free-group words with at most one sign turn. Two formal
inverse states have both turns, and the endpoint letters of every Neary role protect those turns
under all later positive contexts.
-/

namespace MatrixMortality

namespace PairedInverseChamber

open CancellativeRoleFraction

/-- A signed binary word with one fixed sign. -/
def signedWord (sign : Bool) (word : List Bool) : List (Bool × Bool) :=
  word.map fun bit => (bit, sign)

/-- Adjacent signed letters do not cancel freely. -/
def CancellationSafe (left right : Bool × Bool) : Prop :=
  ¬(left.1 = right.1 ∧ left.2 = !right.2)

/-- A raw signed word has no adjacent inverse pair. -/
def FreelyReduced (word : List (Bool × Bool)) : Prop :=
  word.Chain' CancellationSafe

/-- A reduced word has no negative-to-positive sign turn. -/
def PositiveNegative (word : List (Bool × Bool)) : Prop :=
  word.Chain' fun left right => ¬(left.2 = false ∧ right.2 = true)

/-- A reduced word has no positive-to-negative sign turn. -/
def NegativePositive (word : List (Bool × Bool)) : Prop :=
  word.Chain' fun left right => ¬(left.2 = true ∧ right.2 = false)

private theorem chainAll {α : Type*} (word : List α) :
    word.Chain' fun _ _ => True := by
  induction word with
  | nil => trivial
  | cons first word induction =>
      cases word with
      | nil => exact List.chain'_singleton first
      | cons second rest => exact List.Chain'.cons trivial induction

private theorem signedWord_freelyReduced (sign : Bool) (word : List Bool) :
    FreelyReduced (signedWord sign word) := by
  rw [FreelyReduced, signedWord, List.chain'_map]
  exact (chainAll word).imp fun left right _ => by simp [CancellationSafe]

private theorem reduce_eq_self_of_freelyReduced {word : List (Bool × Bool)}
    (reduced : FreelyReduced word) : FreeGroup.reduce word = word := by
  induction word with
  | nil => rfl
  | cons first word induction =>
      cases word with
      | nil => rfl
      | cons second rest =>
          have boundary := reduced.rel_head
          have tail_reduced := reduced.tail
          rw [FreeGroup.reduce.cons, induction tail_reduced]
          change
            (if first.1 = second.1 ∧ first.2 = !second.2 then rest
              else first :: second :: rest) = first :: second :: rest
          by_cases cancellation :
              first.1 = second.1 ∧ first.2 = !second.2
          · exact False.elim (boundary cancellation)
          · simp [cancellation]

private theorem reduce_positive_negative_shape (positive negative : List Bool) :
    ∃ positive' negative',
      FreeGroup.reduce (signedWord true positive ++ signedWord false negative) =
        signedWord true positive' ++ signedWord false negative' := by
  induction positive with
  | nil =>
      exact ⟨[], negative, reduce_eq_self_of_freelyReduced (signedWord_freelyReduced false _)⟩
  | cons bit positive induction =>
      obtain ⟨positive', negative', reduced_eq⟩ := induction
      change ∃ positive' negative',
        FreeGroup.reduce
            ((bit, true) ::
              (signedWord true positive ++ signedWord false negative)) =
          signedWord true positive' ++ signedWord false negative'
      rw [FreeGroup.reduce.cons, reduced_eq]
      cases positive' with
      | cons first rest =>
          refine ⟨bit :: first :: rest, negative', ?_⟩
          simp [signedWord]
      | nil =>
          cases negative' with
          | nil =>
              exact ⟨[bit], [], by simp [signedWord]⟩
          | cons first rest =>
              by_cases same : bit = first
              · exact ⟨[], rest, by simp [signedWord, same]⟩
              · exact ⟨[bit], first :: rest, by simp [signedWord, same]⟩

private theorem reduce_negative_positive_shape (negative positive : List Bool) :
    ∃ negative' positive',
      FreeGroup.reduce (signedWord false negative ++ signedWord true positive) =
        signedWord false negative' ++ signedWord true positive' := by
  induction negative with
  | nil =>
      exact ⟨[], positive, reduce_eq_self_of_freelyReduced (signedWord_freelyReduced true _)⟩
  | cons bit negative induction =>
      obtain ⟨negative', positive', reduced_eq⟩ := induction
      change ∃ negative' positive',
        FreeGroup.reduce
            ((bit, false) ::
              (signedWord false negative ++ signedWord true positive)) =
          signedWord false negative' ++ signedWord true positive'
      rw [FreeGroup.reduce.cons, reduced_eq]
      cases negative' with
      | cons first rest =>
          refine ⟨bit :: first :: rest, positive', ?_⟩
          simp [signedWord]
      | nil =>
          cases positive' with
          | nil =>
              exact ⟨[bit], [], by simp [signedWord]⟩
          | cons first rest =>
              by_cases same : bit = first
              · exact ⟨[], rest, by simp [signedWord, same]⟩
              · exact ⟨[bit], first :: rest, by simp [signedWord, same]⟩

private theorem positive_negative_signedWords
    (positive negative : List Bool) :
    PositiveNegative (signedWord true positive ++ signedWord false negative) := by
  apply List.Chain'.append
  · rw [signedWord, List.chain'_map]
    exact (chainAll positive).imp fun _ _ _ => by simp
  · rw [signedWord, List.chain'_map]
    exact (chainAll negative).imp fun _ _ _ => by simp
  · intro left left_mem right right_mem
    simp [signedWord] at left_mem right_mem
    rcases left_mem with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      rcases right_mem with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp

private theorem negative_positive_signedWords
    (negative positive : List Bool) :
    NegativePositive (signedWord false negative ++ signedWord true positive) := by
  apply List.Chain'.append
  · rw [signedWord, List.chain'_map]
    exact (chainAll negative).imp fun _ _ _ => by simp
  · rw [signedWord, List.chain'_map]
    exact (chainAll positive).imp fun _ _ _ => by simp
  · intro left left_mem right right_mem
    simp [signedWord] at left_mem right_mem
    rcases left_mem with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      rcases right_mem with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp

/-- Every positive-times-negative free-group fraction has no negative-to-positive turn in its
reduced word. -/
theorem positiveFraction_positiveNegative (upper lower : List Bool) :
    PositiveNegative
      (FreeGroup.toWord (positiveWord upper * (positiveWord lower)⁻¹)) := by
  obtain ⟨positive, negative, reduced_eq⟩ :=
    reduce_positive_negative_shape upper lower.reverse
  have raw_eq :
      FreeGroup.toWord (positiveWord upper * (positiveWord lower)⁻¹) =
        FreeGroup.reduce (signedWord true upper ++ signedWord false lower.reverse) := by
    simp [positiveWord, signedWord, FreeGroup.invRev, Function.comp_def]
  rw [raw_eq, reduced_eq]
  exact positive_negative_signedWords positive negative

/-- Every negative-times-positive free-group fraction has no positive-to-negative turn in its
reduced word. -/
theorem negativeFraction_negativePositive (upper lower : List Bool) :
    NegativePositive
      (FreeGroup.toWord ((positiveWord upper)⁻¹ * positiveWord lower)) := by
  obtain ⟨negative, positive, reduced_eq⟩ :=
    reduce_negative_positive_shape upper.reverse lower
  have raw_eq :
      FreeGroup.toWord ((positiveWord upper)⁻¹ * positiveWord lower) =
        FreeGroup.reduce (signedWord false upper.reverse ++ signedWord true lower) := by
    simp [positiveWord, signedWord, FreeGroup.invRev, Function.comp_def]
  rw [raw_eq, reduced_eq]
  exact negative_positive_signedWords negative positive

private theorem spell_getLast?_of_letter_getLast?
    {α β : Type*} (side : α → List β) (last : β)
    (letter_last : ∀ letter, (side letter).getLast? = some last) :
    ∀ {word : List α}, word ≠ [] → (spell side word).getLast? = some last := by
  intro word word_ne
  induction word with
  | nil => contradiction
  | cons letter word induction =>
      cases word with
      | nil => simpa [spell] using letter_last letter
      | cons next rest =>
          change (side letter ++ spell side (next :: rest)).getLast? = some last
          have tail_ne : spell side (next :: rest) ≠ [] := by
            intro tail_empty
            have tail_last := induction (by simp)
            rw [tail_empty] at tail_last
            simp at tail_last
          rw [List.getLast?_append_of_ne_nil _ tail_ne]
          exact induction (by simp)

private theorem getLast?_append_singleton {α : Type*} (beginning : List α) (last : α) :
    (beginning ++ [last]).getLast? = some last := by
  rw [List.getLast?_append_cons]
  rfl

theorem nearyUpper_getLast? (β : Nat) (tile : NearyTile) :
    (nearyUpper β tile).getLast? = some true := by
  cases tile with
  | rule letter =>
      cases letter with
      | b => simpa [nearyUpper, tagCode] using
          getLast?_append_singleton (true :: List.replicate β false) true
      | c => simp [nearyUpper, tagCode]
  | erase letter =>
      cases letter with
      | b => simpa [nearyUpper, tagCode] using
          getLast?_append_singleton (true :: List.replicate β false) true
      | c => simp [nearyUpper, tagCode]

theorem nearyLower_getLast? (β : Nat) (body : List TagLetter) (tile : NearyTile) :
    (nearyLower β body tile).getLast? = some false := by
  cases tile with
  | rule letter =>
      cases letter with
      | b => simp [nearyLower]
      | c => simpa [nearyLower, List.append_assoc] using
          getLast?_append_singleton (true :: tagEncode β body ++ [true]) false
  | erase letter => cases letter <;> simp [nearyLower]

/-- Every nonempty Neary upper spelling ends in the encoded `z` bit. -/
theorem upperSpell_getLast? (β : Nat) {roles : List NearyTile} (roles_ne : roles ≠ []) :
    (spell (nearyUpper β) roles).getLast? = some true :=
  spell_getLast?_of_letter_getLast? (nearyUpper β) true (nearyUpper_getLast? β) roles_ne

/-- Every nonempty Neary lower spelling ends in the encoded `x` bit. -/
theorem lowerSpell_getLast? (β : Nat) (body : List TagLetter)
    {roles : List NearyTile} (roles_ne : roles ≠ []) :
    (spell (nearyLower β body) roles).getLast? = some false :=
  spell_getLast?_of_letter_getLast? (nearyLower β body) false
    (nearyLower_getLast? β body) roles_ne

/-- Every actual paired suffix residual lies in the positive-negative chamber. -/
theorem suffixResidual_positiveNegative (β : Nat) (body : List TagLetter)
    (suffix : List PairedControl) :
    PositiveNegative (FreeGroup.toWord (suffixResidual β body suffix)) := by
  simpa [suffixResidual, positiveWord_append, mul_assoc] using
    positiveFraction_positiveNegative
      (spell (nearyUpper β) (decodePairedWord suffix) ++ nearyMarker β)
      (spell (nearyLower β body) (decodePairedWord suffix))

/-- Every phase-aware paired prefix residual lies in the negative-positive chamber. -/
theorem prefixResidual_negativePositive (β : Nat) (body : List TagLetter)
    (context : List PairedControl) (phase : PairPhase) :
    NegativePositive (FreeGroup.toWord (prefixResidual β body context phase)) := by
  simpa [prefixResidual] using
    negativeFraction_negativePositive
      (spell (nearyUpper β) (PairedResidual.decodeFrom phase context).2)
      (spell (nearyLower β body) (PairedResidual.decodeFrom phase context).2)

/-! ## Protected two-turn states -/

/-- Reduced signed word for `x⁻ᵝ z xᵝ z⁻¹`. -/
def leftInverseWord (β : Nat) : List (Bool × Bool) :=
  signedWord false (List.replicate β false) ++
    [(true, true)] ++ signedWord true (List.replicate β false) ++ [(true, false)]

/-- Reduced signed word for `x z⁻² x⁻¹ z²`. -/
def rightInverseWord : List (Bool × Bool) :=
  [(false, true), (true, false), (true, false), (false, false),
    (true, true), (true, true)]

/-- The left formal inverse state `x⁻ᵝ z xᵝ z⁻¹`. -/
def leftInverseState (β : Nat) : BitGroup :=
  FreeGroup.mk (leftInverseWord β)

/-- The right formal inverse state `x z⁻² x⁻¹ z²`. -/
def rightInverseState : BitGroup :=
  FreeGroup.mk rightInverseWord

private theorem leftInverseWord_freelyReduced {β : Nat} (β_pos : 0 < β) :
    FreelyReduced (leftInverseWord β) := by
  have β_ne : β ≠ 0 := Nat.ne_of_gt β_pos
  have negative_z :
      FreelyReduced
        (signedWord false (List.replicate β false) ++ [(true, true)]) := by
    rw [FreelyReduced]
    apply (signedWord_freelyReduced false _).append
    · exact List.chain'_singleton _
    · simp [signedWord, CancellationSafe, List.getLast?_replicate, β_ne]
  have negative_z_positive :
      FreelyReduced
        ((signedWord false (List.replicate β false) ++ [(true, true)]) ++
          signedWord true (List.replicate β false)) := by
    rw [FreelyReduced] at negative_z ⊢
    apply negative_z.append (signedWord_freelyReduced true _)
    simp [signedWord, CancellationSafe, List.head?_replicate, β_ne]
  rw [FreelyReduced] at negative_z_positive
  rw [leftInverseWord, FreelyReduced]
  apply negative_z_positive.append
  · exact List.chain'_singleton _
  · intro left left_mem right right_mem
    have positive_ne : signedWord true (List.replicate β false) ≠ [] := by
      simp [signedWord, β_ne]
    rw [List.getLast?_append_of_ne_nil _ positive_ne] at left_mem
    simp [signedWord, List.getLast?_replicate, β_ne] at left_mem
    simp at right_mem
    subst left
    subst right
    simp [CancellationSafe]

private theorem rightInverseWord_freelyReduced : FreelyReduced rightInverseWord := by
  simp [rightInverseWord, FreelyReduced, CancellationSafe]

theorem leftInverseState_toWord {β : Nat} (β_pos : 0 < β) :
    FreeGroup.toWord (leftInverseState β) = leftInverseWord β := by
  simp [leftInverseState, reduce_eq_self_of_freelyReduced
    (leftInverseWord_freelyReduced β_pos)]

theorem rightInverseState_toWord :
    FreeGroup.toWord rightInverseState = rightInverseWord := by
  simp [rightInverseState, reduce_eq_self_of_freelyReduced rightInverseWord_freelyReduced]

private theorem mk_replicate_signed (bit sign : Bool) (n : Nat) :
    FreeGroup.mk (List.replicate n (bit, sign)) =
      (if sign then FreeGroup.of bit else (FreeGroup.of bit)⁻¹) ^ n := by
  induction n with
  | zero => rfl
  | succ n induction =>
      rw [List.replicate_succ, ← List.singleton_append, ← FreeGroup.mul_mk, induction]
      cases sign <;> simp [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev, pow_succ']

/-- Group formula for the left two-turn state. -/
theorem leftInverseState_eq (β : Nat) :
    leftInverseState β = (x ^ β)⁻¹ * z * x ^ β * z⁻¹ := by
  rw [leftInverseState, leftInverseWord]
  simp only [signedWord, List.map_replicate]
  rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
  rw [mk_replicate_signed, mk_replicate_signed]
  simp [x, z, FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev, inv_pow]
  rw [show FreeGroup.mk [(false, false)] =
    (FreeGroup.mk [(false, true)])⁻¹ by rfl, inv_pow]

/-- Group formula for the right two-turn state. -/
theorem rightInverseState_eq :
    rightInverseState = x * (z ^ 2)⁻¹ * x⁻¹ * z ^ 2 := by
  rw [rightInverseState, rightInverseWord]
  change FreeGroup.mk
      ([(false, true)] ++ [(true, false)] ++ [(true, false)] ++
        [(false, false)] ++ [(true, true)] ++ [(true, true)]) = _
  simp [x, z, FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev,
    FreeGroup.mul_mk, pow_two]

/-- The left state is exactly the formal inverse product of the two left discrepancies. -/
theorem leftInverseState_eq_formalCombination (β : Nat) :
    leftInverseState β = (leftSeed β).1⁻¹ * (leftConjugate β).1 := by
  rw [leftInverseState_eq, leftSeed_eq, leftConjugate_eq]
  simp only [Prod.fst]
  group

/-- The right state is exactly the discrepancy induced by the formal inverse product of the two
right discrepancies. -/
theorem rightInverseState_eq_formalCombination (β : Nat) :
    rightInverseState = (((rightSeed β)⁻¹ * rightConjugate β).2)⁻¹ := by
  rw [rightInverseState_eq, rightSeed_eq, rightConjugate_eq]
  change x * (z ^ 2)⁻¹ * x⁻¹ * z ^ 2 =
    (((z ^ 2)⁻¹ * (x * z ^ 2 * x⁻¹)))⁻¹
  group

theorem leftInverseState_not_positiveNegative {β : Nat} (β_pos : 0 < β) :
    ¬PositiveNegative (FreeGroup.toWord (leftInverseState β)) := by
  rw [leftInverseState_toWord β_pos]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt β_pos)
  intro chamber
  have transition :
      [(false, false), (true, true)] <:+: leftInverseWord (n + 1) := by
    simpa [leftInverseWord, signedWord, List.replicate_succ', List.append_assoc] using
      (List.infix_append (List.replicate n (false, false))
        [(false, false), (true, true)]
        (List.replicate (n + 1) (false, true) ++ [(true, false)]))
  have impossible := chamber.infix transition
  simp [PositiveNegative] at impossible

theorem leftInverseState_not_negativePositive {β : Nat} (β_pos : 0 < β) :
    ¬NegativePositive (FreeGroup.toWord (leftInverseState β)) := by
  rw [leftInverseState_toWord β_pos]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt β_pos)
  intro chamber
  have transition :
      [(false, true), (true, false)] <:+: leftInverseWord (n + 1) := by
    simpa [leftInverseWord, signedWord, List.replicate_succ', List.append_assoc] using
      (List.infix_append
        (List.replicate (n + 1) (false, false) ++
          [(true, true)] ++ List.replicate n (false, true))
        [(false, true), (true, false)] [])
  have impossible := chamber.infix transition
  simp [NegativePositive] at impossible

theorem rightInverseState_not_positiveNegative :
    ¬PositiveNegative (FreeGroup.toWord rightInverseState) := by
  rw [rightInverseState_toWord]
  simp [rightInverseWord, PositiveNegative]

theorem rightInverseState_not_negativePositive :
    ¬NegativePositive (FreeGroup.toWord rightInverseState) := by
  rw [rightInverseState_toWord]
  simp [rightInverseWord, NegativePositive]

/-! ## Positive forward cones -/

/-- Apply one positive upper/lower context to a discrepancy state. -/
def continuedState (upper : List Bool) (seed : BitGroup) (lower : List Bool) : BitGroup :=
  positiveWord upper * seed * (positiveWord lower)⁻¹

private theorem continuedWord_freelyReduced
    {upper lower : List Bool} {seed : List (Bool × Bool)}
    {firstSign lastSign : Bool}
    (seed_reduced : FreelyReduced seed)
    (seed_head : seed.head? = some (false, firstSign))
    (seed_last : seed.getLast? = some (true, lastSign))
    (upper_end : upper = [] ∨ upper.getLast? = some true)
    (lower_end : lower = [] ∨ lower.getLast? = some false) :
    FreelyReduced
      (signedWord true upper ++ seed ++ signedWord false lower.reverse) := by
  have upper_seed : FreelyReduced (signedWord true upper ++ seed) := by
    rw [FreelyReduced] at seed_reduced ⊢
    apply (signedWord_freelyReduced true upper).append seed_reduced
    intro left left_mem right right_mem
    rcases upper_end with upper_empty | upper_last
    · subst upper
      simp [signedWord] at left_mem
    · rw [signedWord, List.getLast?_map, upper_last] at left_mem
      rw [seed_head] at right_mem
      simp at left_mem right_mem
      subst left
      subst right
      simp [CancellationSafe]
  rw [FreelyReduced] at upper_seed ⊢
  apply upper_seed.append (signedWord_freelyReduced false lower.reverse)
  intro left left_mem right right_mem
  have seed_ne : seed ≠ [] := by
    intro seed_empty
    rw [seed_empty] at seed_head
    simp at seed_head
  rw [List.getLast?_append_of_ne_nil _ seed_ne, seed_last] at left_mem
  rcases lower_end with lower_empty | lower_last
  · subst lower
    simp [signedWord] at right_mem
  · rw [signedWord, List.head?_map, List.head?_reverse, lower_last] at right_mem
    simp at left_mem right_mem
    subst left
    subst right
    simp [CancellationSafe]

private theorem continuedState_toWord_of_freelyReduced
    (upper lower : List Bool) (seed : List (Bool × Bool))
    (reduced : FreelyReduced
      (signedWord true upper ++ seed ++ signedWord false lower.reverse)) :
    FreeGroup.toWord (continuedState upper (FreeGroup.mk seed) lower) =
      signedWord true upper ++ seed ++ signedWord false lower.reverse := by
  have raw_eq :
      FreeGroup.toWord (continuedState upper (FreeGroup.mk seed) lower) =
        FreeGroup.reduce
          (signedWord true upper ++ seed ++ signedWord false lower.reverse) := by
    simp [continuedState, positiveWord, signedWord, FreeGroup.invRev,
      Function.comp_def, List.append_assoc]
  rw [raw_eq, reduce_eq_self_of_freelyReduced reduced]

private theorem leftInverseWord_head? {β : Nat} (β_pos : 0 < β) :
    (leftInverseWord β).head? = some (false, false) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt β_pos)
  simp [leftInverseWord, signedWord, List.replicate_succ]

private theorem leftInverseWord_getLast? (β : Nat) :
    (leftInverseWord β).getLast? = some (true, false) := by
  simpa [leftInverseWord, List.append_assoc] using
    getLast?_append_singleton
      (signedWord false (List.replicate β false) ++ [(true, true)] ++
        signedWord true (List.replicate β false)) (true, false)

private theorem rightInverseWord_head? :
    rightInverseWord.head? = some (false, true) := by
  rfl

private theorem rightInverseWord_getLast? :
    rightInverseWord.getLast? = some (true, true) := by
  rfl

private theorem upperSpell_end_or_empty (β : Nat) (roles : List NearyTile) :
    spell (nearyUpper β) roles = [] ∨
      (spell (nearyUpper β) roles).getLast? = some true := by
  cases roles with
  | nil => exact Or.inl rfl
  | cons role roles => exact Or.inr (upperSpell_getLast? β (by simp))

private theorem lowerSpell_end_or_empty (β : Nat) (body : List TagLetter)
    (roles : List NearyTile) :
    spell (nearyLower β body) roles = [] ∨
      (spell (nearyLower β body) roles).getLast? = some false := by
  cases roles with
  | nil => exact Or.inl rfl
  | cons role roles => exact Or.inr (lowerSpell_getLast? β body (by simp))

theorem leftContinuation_toWord {β : Nat} (β_pos : 0 < β)
    (upper lower : List Bool)
    (upper_end : upper = [] ∨ upper.getLast? = some true)
    (lower_end : lower = [] ∨ lower.getLast? = some false) :
    FreeGroup.toWord (continuedState upper (leftInverseState β) lower) =
      signedWord true upper ++ leftInverseWord β ++ signedWord false lower.reverse := by
  apply continuedState_toWord_of_freelyReduced
  exact continuedWord_freelyReduced (leftInverseWord_freelyReduced β_pos)
    (leftInverseWord_head? β_pos) (leftInverseWord_getLast? β) upper_end lower_end

theorem rightContinuation_toWord (upper lower : List Bool)
    (upper_end : upper = [] ∨ upper.getLast? = some true)
    (lower_end : lower = [] ∨ lower.getLast? = some false) :
    FreeGroup.toWord (continuedState upper rightInverseState lower) =
      signedWord true upper ++ rightInverseWord ++ signedWord false lower.reverse := by
  apply continuedState_toWord_of_freelyReduced
  exact continuedWord_freelyReduced rightInverseWord_freelyReduced
    rightInverseWord_head? rightInverseWord_getLast? upper_end lower_end

/-- Every protected left seed continuation retains both sign turns. -/
theorem leftContinuation_outsideChambers {β : Nat} (β_pos : 0 < β)
    (upper lower : List Bool)
    (upper_end : upper = [] ∨ upper.getLast? = some true)
    (lower_end : lower = [] ∨ lower.getLast? = some false) :
    ¬PositiveNegative
        (FreeGroup.toWord (continuedState upper (leftInverseState β) lower)) ∧
      ¬NegativePositive
        (FreeGroup.toWord (continuedState upper (leftInverseState β) lower)) := by
  have seed_positiveNegative : ¬PositiveNegative (leftInverseWord β) := by
    simpa [leftInverseState_toWord β_pos] using
      leftInverseState_not_positiveNegative β_pos
  have seed_negativePositive : ¬NegativePositive (leftInverseWord β) := by
    simpa [leftInverseState_toWord β_pos] using
      leftInverseState_not_negativePositive β_pos
  rw [leftContinuation_toWord β_pos upper lower upper_end lower_end]
  have seed_infix :
      leftInverseWord β <:+:
        signedWord true upper ++ leftInverseWord β ++ signedWord false lower.reverse :=
    List.infix_append _ _ _
  exact ⟨fun chamber => seed_positiveNegative (chamber.infix seed_infix),
    fun chamber => seed_negativePositive (chamber.infix seed_infix)⟩

/-- Every protected right seed continuation retains both sign turns. -/
theorem rightContinuation_outsideChambers (upper lower : List Bool)
    (upper_end : upper = [] ∨ upper.getLast? = some true)
    (lower_end : lower = [] ∨ lower.getLast? = some false) :
    ¬PositiveNegative
        (FreeGroup.toWord (continuedState upper rightInverseState lower)) ∧
      ¬NegativePositive
        (FreeGroup.toWord (continuedState upper rightInverseState lower)) := by
  have seed_positiveNegative : ¬PositiveNegative rightInverseWord := by
    simpa [rightInverseState_toWord] using rightInverseState_not_positiveNegative
  have seed_negativePositive : ¬NegativePositive rightInverseWord := by
    simpa [rightInverseState_toWord] using rightInverseState_not_negativePositive
  rw [rightContinuation_toWord upper lower upper_end lower_end]
  have seed_infix :
      rightInverseWord <:+:
        signedWord true upper ++ rightInverseWord ++ signedWord false lower.reverse :=
    List.infix_append _ _ _
  exact ⟨fun chamber => seed_positiveNegative (chamber.infix seed_infix),
    fun chamber => seed_negativePositive (chamber.infix seed_infix)⟩

/-- Apply a decoded Neary role sequence to a discrepancy state. -/
def roleContinuation (β : Nat) (body : List TagLetter) (roles : List NearyTile)
    (seed : BitGroup) : BitGroup :=
  continuedState (spell (nearyUpper β) roles) seed
    (spell (nearyLower β body) roles)

/-- The complete positive role cone of the left inverse state misses both residual chambers. -/
theorem leftRoleContinuation_outsideChambers {β : Nat} (β_pos : 0 < β)
    (body : List TagLetter) (roles : List NearyTile) :
    ¬PositiveNegative
        (FreeGroup.toWord (roleContinuation β body roles (leftInverseState β))) ∧
      ¬NegativePositive
        (FreeGroup.toWord (roleContinuation β body roles (leftInverseState β))) := by
  exact leftContinuation_outsideChambers β_pos _ _
    (upperSpell_end_or_empty β roles) (lowerSpell_end_or_empty β body roles)

/-- The complete positive role cone of the right inverse state misses both residual chambers. -/
theorem rightRoleContinuation_outsideChambers (β : Nat) (body : List TagLetter)
    (roles : List NearyTile) :
    ¬PositiveNegative
        (FreeGroup.toWord (roleContinuation β body roles rightInverseState)) ∧
      ¬NegativePositive
        (FreeGroup.toWord (roleContinuation β body roles rightInverseState)) := by
  exact rightContinuation_outsideChambers _ _
    (upperSpell_end_or_empty β roles) (lowerSpell_end_or_empty β body roles)

/-- No positive continuation of the left inverse state is an actual suffix residual. -/
theorem leftRoleContinuation_ne_suffixResidual {β : Nat} (β_pos : 0 < β)
    (body : List TagLetter) (roles : List NearyTile) (suffix : List PairedControl) :
    roleContinuation β body roles (leftInverseState β) ≠ suffixResidual β body suffix := by
  intro equality
  apply (leftRoleContinuation_outsideChambers β_pos body roles).1
  rw [equality]
  exact suffixResidual_positiveNegative β body suffix

/-- No positive continuation of the left inverse state is a phase-aware prefix residual. -/
theorem leftRoleContinuation_ne_prefixResidual {β : Nat} (β_pos : 0 < β)
    (body : List TagLetter) (roles : List NearyTile) (context : List PairedControl)
    (phase : PairPhase) :
    roleContinuation β body roles (leftInverseState β) ≠
      prefixResidual β body context phase := by
  intro equality
  apply (leftRoleContinuation_outsideChambers β_pos body roles).2
  rw [equality]
  exact prefixResidual_negativePositive β body context phase

/-- No positive continuation of the right inverse state is an actual suffix residual. -/
theorem rightRoleContinuation_ne_suffixResidual (β : Nat) (body : List TagLetter)
    (roles : List NearyTile) (suffix : List PairedControl) :
    roleContinuation β body roles rightInverseState ≠ suffixResidual β body suffix := by
  intro equality
  apply (rightRoleContinuation_outsideChambers β body roles).1
  rw [equality]
  exact suffixResidual_positiveNegative β body suffix

/-- No positive continuation of the right inverse state is a phase-aware prefix residual. -/
theorem rightRoleContinuation_ne_prefixResidual (β : Nat) (body : List TagLetter)
    (roles : List NearyTile) (context : List PairedControl) (phase : PairPhase) :
    roleContinuation β body roles rightInverseState ≠ prefixResidual β body context phase := by
  intro equality
  apply (rightRoleContinuation_outsideChambers β body roles).2
  rw [equality]
  exact prefixResidual_negativePositive β body context phase

end PairedInverseChamber

end MatrixMortality
