import MatrixMortality.NearyEncoding

/-!
# Binary morphism defect

The two-word defect theorem says that a noninjective morphism from the binary free monoid has
commuting letter images. This file proves that implication using elementary prefix cancellation
and a Euclidean descent on the sum of the two image lengths.
-/

namespace MatrixMortality

/-- The binary morphism taking `false` to `left` and `true` to `right`. -/
def binarySpell {α : Type*} (left right : List α) (word : List Bool) : List α :=
  spell (fun bit => if bit then right else left) word

@[simp] theorem binarySpell_nil {α : Type*} (left right : List α) :
    binarySpell left right [] = [] := by
  rfl

@[simp] theorem binarySpell_false_cons {α : Type*}
    (left right : List α) (word : List Bool) :
    binarySpell left right (false :: word) =
      left ++ binarySpell left right word := by
  rfl

@[simp] theorem binarySpell_true_cons {α : Type*}
    (left right : List α) (word : List Bool) :
    binarySpell left right (true :: word) =
      right ++ binarySpell left right word := by
  rfl

theorem binarySpell_append {α : Type*} (left right : List α)
    (first second : List Bool) :
    binarySpell left right (first ++ second) =
      binarySpell left right first ++ binarySpell left right second := by
  exact spell_append _ _ _

theorem spell_comp_spell {α β γ : Type*}
    (outer : β → List γ) (inner : α → List β) (word : List α) :
    spell outer (spell inner word) =
      spell (fun letter => spell outer (inner letter)) word := by
  induction word with
  | nil => rfl
  | cons letter word induction =>
      change spell outer (inner letter ++ spell inner word) =
        spell outer (inner letter) ++
          spell (fun current => spell outer (inner current)) word
      rw [spell_append, induction]

theorem binarySpell_eq_nil_iff {α : Type*} {left right : List α}
    (left_ne : left ≠ []) (right_ne : right ≠ []) (word : List Bool) :
    binarySpell left right word = [] ↔ word = [] := by
  induction word with
  | nil => simp
  | cons bit word _ =>
      cases bit <;> simp [left_ne, right_ne]

/-- Distinct equal-coded binary words expose an equality beginning with different letter
images after their common source prefix is cancelled. -/
theorem binarySpell_head_mismatch {α : Type*} {left right : List α}
    (left_ne : left ≠ []) (right_ne : right ≠ [])
    {first second : List Bool}
    (coded_eq : binarySpell left right first = binarySpell left right second)
    (source_ne : first ≠ second) :
    (∃ firstTail secondTail,
      left ++ binarySpell left right firstTail =
        right ++ binarySpell left right secondTail) ∨
    ∃ firstTail secondTail,
      right ++ binarySpell left right firstTail =
        left ++ binarySpell left right secondTail := by
  induction first generalizing second with
  | nil =>
      cases second with
      | nil => exact False.elim (source_ne rfl)
      | cons bit second =>
          have coded_nonempty :
              binarySpell left right (bit :: second) ≠ [] :=
            (binarySpell_eq_nil_iff left_ne right_ne _).not.mpr (by simp)
          exact False.elim (coded_nonempty coded_eq.symm)
  | cons firstHead firstTail induction =>
      cases second with
      | nil =>
          have coded_nonempty :
              binarySpell left right (firstHead :: firstTail) ≠ [] :=
            (binarySpell_eq_nil_iff left_ne right_ne _).not.mpr (by simp)
          exact False.elim (coded_nonempty coded_eq)
      | cons secondHead secondTail =>
          cases firstHead <;> cases secondHead
          · apply induction
            · exact List.append_cancel_left coded_eq
            · intro tails_eq
              exact source_ne (congrArg (false :: ·) tails_eq)
          · exact Or.inl ⟨firstTail, secondTail, coded_eq⟩
          · exact Or.inr ⟨firstTail, secondTail, coded_eq⟩
          · apply induction
            · exact List.append_cancel_left coded_eq
            · intro tails_eq
              exact source_ne (congrArg (true :: ·) tails_eq)

/-- Source recoding used when `right = left ++ residue`. -/
def factorRightCode : Bool → List Bool
  | false => [false]
  | true => [false, true]

/-- Source recoding used when `left = right ++ residue`. -/
def factorLeftCode : Bool → List Bool
  | false => [false, true]
  | true => [false]

theorem binarySpell_factor_right {α : Type*} (left residue : List α)
    (word : List Bool) :
    binarySpell left (left ++ residue) word =
      binarySpell left residue (spell factorRightCode word) := by
  unfold binarySpell
  rw [spell_comp_spell]
  congr 1
  funext bit
  cases bit <;> simp [factorRightCode, spell]

theorem binarySpell_factor_left {α : Type*} (right residue : List α)
    (word : List Bool) :
    binarySpell (right ++ residue) right word =
      binarySpell right residue (spell factorLeftCode word) := by
  unfold binarySpell
  rw [spell_comp_spell]
  congr 1
  funext bit
  cases bit <;> simp [factorLeftCode, spell]

theorem spell_factorRightCode_ne_true_cons
    (word tail : List Bool) :
    spell factorRightCode word ≠ true :: tail := by
  cases word with
  | nil => simp [spell]
  | cons head word => cases head <;> simp [spell, factorRightCode]

theorem spell_factorLeftCode_ne_true_cons
    (word tail : List Bool) :
    spell factorLeftCode word ≠ true :: tail := by
  cases word with
  | nil => simp [spell]
  | cons head word => cases head <;> simp [spell, factorLeftCode]

/-- A collision beginning with `left` and `left ++ residue` descends to a collision for
`left` and `residue`. -/
theorem factorRight_not_injective_of_forward {α : Type*}
    (left residue : List α) {first second : List Bool}
    (collision :
      left ++ binarySpell left (left ++ residue) first =
        (left ++ residue) ++ binarySpell left (left ++ residue) second) :
    ¬Function.Injective (binarySpell left residue) := by
  have cancelled :
      binarySpell left (left ++ residue) first =
        residue ++ binarySpell left (left ++ residue) second := by
    apply List.append_cancel_left
    simpa only [List.append_assoc] using collision
  rw [binarySpell_factor_right, binarySpell_factor_right] at cancelled
  apply Function.not_injective_iff.mpr
  refine ⟨spell factorRightCode first, true :: spell factorRightCode second, ?_, ?_⟩
  · simpa using cancelled
  · exact spell_factorRightCode_ne_true_cons first _

theorem factorRight_not_injective_of_reverse {α : Type*}
    (left residue : List α) {first second : List Bool}
    (collision :
      (left ++ residue) ++ binarySpell left (left ++ residue) first =
        left ++ binarySpell left (left ++ residue) second) :
    ¬Function.Injective (binarySpell left residue) := by
  have cancelled :
      residue ++ binarySpell left (left ++ residue) first =
        binarySpell left (left ++ residue) second := by
    apply List.append_cancel_left
    simpa only [List.append_assoc] using collision
  rw [binarySpell_factor_right, binarySpell_factor_right] at cancelled
  apply Function.not_injective_iff.mpr
  refine ⟨true :: spell factorRightCode first, spell factorRightCode second, ?_, ?_⟩
  · simpa using cancelled
  · exact (spell_factorRightCode_ne_true_cons second _).symm

/-- A collision beginning with `right ++ residue` and `right` descends to a collision for
`right` and `residue`. -/
theorem factorLeft_not_injective_of_forward {α : Type*}
    (right residue : List α) {first second : List Bool}
    (collision :
      (right ++ residue) ++ binarySpell (right ++ residue) right first =
        right ++ binarySpell (right ++ residue) right second) :
    ¬Function.Injective (binarySpell right residue) := by
  have cancelled :
      residue ++ binarySpell (right ++ residue) right first =
        binarySpell (right ++ residue) right second := by
    apply List.append_cancel_left
    simpa only [List.append_assoc] using collision
  rw [binarySpell_factor_left, binarySpell_factor_left] at cancelled
  apply Function.not_injective_iff.mpr
  refine ⟨true :: spell factorLeftCode first, spell factorLeftCode second, ?_, ?_⟩
  · simpa using cancelled
  · exact (spell_factorLeftCode_ne_true_cons second _).symm

theorem factorLeft_not_injective_of_reverse {α : Type*}
    (right residue : List α) {first second : List Bool}
    (collision :
      right ++ binarySpell (right ++ residue) right first =
        (right ++ residue) ++ binarySpell (right ++ residue) right second) :
    ¬Function.Injective (binarySpell right residue) := by
  have cancelled :
      binarySpell (right ++ residue) right first =
        residue ++ binarySpell (right ++ residue) right second := by
    apply List.append_cancel_left
    simpa only [List.append_assoc] using collision
  rw [binarySpell_factor_left, binarySpell_factor_left] at cancelled
  apply Function.not_injective_iff.mpr
  refine ⟨spell factorLeftCode first, true :: spell factorLeftCode second, ?_, ?_⟩
  · simpa using cancelled
  · exact spell_factorLeftCode_ne_true_cons first _

/-- Two-word defect theorem: noninjectivity of a binary free-monoid morphism forces its two
letter images to commute. -/
theorem binarySpell_not_injective_commute {α : Type*}
    (left right : List α)
    (not_injective : ¬Function.Injective (binarySpell left right)) :
    left ++ right = right ++ left := by
  by_cases left_empty : left = []
  · subst left
    simp
  by_cases right_empty : right = []
  · subst right
    simp
  by_cases equal : left = right
  · subst right
    rfl
  obtain ⟨first, second, coded_eq, source_ne⟩ :=
    Function.not_injective_iff.mp not_injective
  rcases binarySpell_head_mismatch left_empty right_empty coded_eq source_ne with
    ⟨firstTail, secondTail, mismatch⟩ | ⟨firstTail, secondTail, mismatch⟩
  · rcases List.append_eq_append_iff.mp mismatch with
      ⟨residue, right_eq, _⟩ | ⟨residue, left_eq, _⟩
    · subst right
      have commute_residue :=
        binarySpell_not_injective_commute left residue
          (factorRight_not_injective_of_forward left residue mismatch)
      simpa only [List.append_assoc] using
        congrArg (left ++ ·) commute_residue
    · subst left
      have commute_residue :=
        binarySpell_not_injective_commute right residue
          (factorLeft_not_injective_of_forward right residue mismatch)
      simpa only [List.append_assoc] using
        congrArg (right ++ ·) commute_residue.symm
  · rcases List.append_eq_append_iff.mp mismatch with
      ⟨residue, left_eq, _⟩ | ⟨residue, right_eq, _⟩
    · subst left
      have commute_residue :=
        binarySpell_not_injective_commute right residue
          (factorLeft_not_injective_of_reverse right residue mismatch)
      simpa only [List.append_assoc] using
        congrArg (right ++ ·) commute_residue.symm
    · subst right
      have commute_residue :=
        binarySpell_not_injective_commute left residue
          (factorRight_not_injective_of_reverse left residue mismatch)
      simpa only [List.append_assoc] using
        congrArg (left ++ ·) commute_residue
termination_by left.length + right.length
decreasing_by
  all_goals simp_all only [List.length_append, List.nil_append, List.append_nil]
  all_goals
    have left_positive := List.length_pos.mpr left_empty
    have right_positive := List.length_pos.mpr right_empty
    omega

/-- A generic binary morphism is the corresponding `binarySpell`. -/
theorem spell_eq_binarySpell {α : Type*} (side : Bool → List α)
    (word : List Bool) :
    spell side word = binarySpell (side false) (side true) word := by
  unfold binarySpell
  congr 1
  funext bit
  cases bit <;> rfl

theorem binarySpell_letter_commutes {α : Type*} {left right : List α}
    (letters_commute : left ++ right = right ++ left)
    (letter : Bool) (word : List Bool) :
    (if letter then right else left) ++ binarySpell left right word =
      binarySpell left right word ++ (if letter then right else left) := by
  induction word with
  | nil => simp
  | cons head tail induction =>
      have head_commutes :
          (if letter then right else left) ++
              (if head then right else left) =
            (if head then right else left) ++
              (if letter then right else left) := by
        cases letter
        · cases head
          · rfl
          · simpa using letters_commute
        · cases head
          · simpa using letters_commute.symm
          · rfl
      change (if letter then right else left) ++
          ((if head then right else left) ++ binarySpell left right tail) =
        ((if head then right else left) ++ binarySpell left right tail) ++
          (if letter then right else left)
      rw [← List.append_assoc, head_commutes, List.append_assoc, induction,
        ← List.append_assoc]

/-- Commuting binary letter images make every two morphic images commute. -/
theorem binarySpell_commute_of_letter_commute {α : Type*} {left right : List α}
    (letters_commute : left ++ right = right ++ left)
    (first second : List Bool) :
    binarySpell left right first ++ binarySpell left right second =
      binarySpell left right second ++ binarySpell left right first := by
  induction first with
  | nil => simp
  | cons head tail induction =>
      change ((if head then right else left) ++ binarySpell left right tail) ++
          binarySpell left right second =
        binarySpell left right second ++
          ((if head then right else left) ++ binarySpell left right tail)
      rw [List.append_assoc, induction, ← List.append_assoc,
        binarySpell_letter_commutes letters_commute head second, List.append_assoc]

/-- Upper word of either Neary macro role after pairing a role with the following `D_b`. -/
def nearyMacroUpper (β : Nat) : TagLetter → List Bool
  | .b => tagCode β .b ++ tagCode β .b
  | .c => tagCode β .c ++ tagCode β .b

theorem nearyMacroUpper_not_commute (β : Nat) (β_pos : 0 < β) :
    nearyMacroUpper β .b ++ nearyMacroUpper β .c ≠
      nearyMacroUpper β .c ++ nearyMacroUpper β .b := by
  cases β with
  | zero => omega
  | succ β =>
      simp [nearyMacroUpper, tagCode, List.replicate_succ]

/-- Distinct exact internal and final binary codes for one macro are incompatible with exact
realizations of both noncommuting Neary macro upper words. -/
theorem neary_exact_internal_final_code_impossible
    (β : Nat) (β_pos : 0 < β)
    (upper : Bool → List Bool)
    (internal final codeB codeC : List Bool)
    (codes_ne : internal ≠ final)
    (same_macro : spell upper internal = spell upper final)
    (realize_b : spell upper codeB = nearyMacroUpper β .b)
    (realize_c : spell upper codeC = nearyMacroUpper β .c) :
    False := by
  have not_injective :
      ¬Function.Injective (binarySpell (upper false) (upper true)) := by
    apply Function.not_injective_iff.mpr
    refine ⟨internal, final, ?_, codes_ne⟩
    simpa only [← spell_eq_binarySpell] using same_macro
  have letters_commute :=
    binarySpell_not_injective_commute (upper false) (upper true) not_injective
  have images_commute :=
    binarySpell_commute_of_letter_commute letters_commute codeB codeC
  rw [← spell_eq_binarySpell upper codeB, ← spell_eq_binarySpell upper codeC,
    realize_b, realize_c] at images_commute
  exact nearyMacroUpper_not_commute β β_pos images_commute

end MatrixMortality
