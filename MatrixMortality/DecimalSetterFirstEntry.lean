import MatrixMortality.DecimalSetterRuleEntry

/-!
# Complete decimal distinguished first-entry extinction

Every physical role block is either all-erasure or has a unique rightmost rule followed by an
erasure tail.  The first branch is empty by the complete all-erasure theorem; the second by the
complete rule-bearing theorem.  This is the exhaustive first-entry grammar from the
distinguished decimal raw head to a multi-role pole.
-/

namespace MatrixMortality.DecimalSetterFirstEntry

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterAncestry
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterChamber
open MatrixMortality.DecimalSetterDepth
open MatrixMortality.DecimalSetterRuleEntry

private theorem map_erase_letter (letters : List TagLetter) :
    (letters.map NearyTile.erase).map NearyTile.letter = letters := by
  induction letters with
  | nil => rfl
  | cons letter letters induction =>
      change letter :: (letters.map NearyTile.erase).map NearyTile.letter =
        letter :: letters
      exact congrArg (letter :: ·) induction

/-- A physical role word is all-erasure or factors at its unique rightmost rule. -/
theorem allErase_or_exists_rightmostRule (roles : List NearyTile) :
    roles = (roles.map NearyTile.letter).map NearyTile.erase ∨
      ∃ (front : List NearyTile) (ruleLetter : TagLetter) (tail : List TagLetter),
        roles = front ++ .rule ruleLetter :: tail.map NearyTile.erase := by
  induction roles with
  | nil => exact Or.inl rfl
  | cons tile roles induction =>
      rcases induction with tail_all_erase | ⟨front, ruleLetter, tail, rightmost_rule⟩
      · cases tile with
        | erase letter =>
            left
            simpa only [NearyTile.letter, List.map_cons] using
              congrArg (NearyTile.erase letter :: ·) tail_all_erase
        | rule letter =>
            right
            refine ⟨[], letter, roles.map NearyTile.letter, ?_⟩
            simpa only [List.nil_append] using
              congrArg (NearyTile.rule letter :: ·) tail_all_erase
      · right
        exact ⟨tile :: front, ruleLetter, tail, by rw [rightmost_rule]; rfl⟩

/-- No non-singleton physical first block carries the distinguished decimal-unit two-`c` raw
head into another multi-role pole. -/
theorem rawHead_firstEntry_multi_shell_impossible
    {β : Nat} (body headTail : List TagLetter) (roles : List NearyTile) {μ E G : ℤ}
    (β_large : 2 ≤ β)
    (multi_role : 2 ≤ roles.length)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: headTail)) : ℚ) 0 0)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (shell :
      HasDecimalShell
        (((code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) *
          (E * code (punctuatedUpper β (roles.map NearyTile.letter)) +
            G * code (spell (nearyLower β body) roles)) -
          10 * μ * G * code (spell (nearyLower β body) roles) : ℤ) : ℚ)
        ((((tagEncode β (roles.map NearyTile.letter)).length - 1 : Nat) : ℤ))
        ((((tagEncode β (roles.map NearyTile.letter)).length - 1 : Nat) : ℤ))) :
    False := by
  rcases allErase_or_exists_rightmostRule roles with all_erase |
      ⟨front, ruleLetter, tail, rightmost_rule⟩
  · let letters := roles.map NearyTile.letter
    have roles_eq : roles = letterEraseBlock letters := by
      simpa only [letterEraseBlock] using all_erase
    have letters_length : letters.length = roles.length := by
      simp only [letters, List.length_map]
    have rewritten_shell := shell
    rw [roles_eq] at rewritten_shell
    have role_letters :
        (letterEraseBlock letters).map NearyTile.letter = letters := by
      simpa only [letterEraseBlock] using map_erase_letter letters
    rw [role_letters] at rewritten_shell
    apply letterErase_rawHead_multi_shell_impossible body headTail letters
      β_large (by omega) head_unit mu_eq gap_eq lift_eq
    simpa only [letterEraseLowerCode] using rewritten_shell
  · have block_length : roles.length = front.length + tail.length + 1 := by
      rw [rightmost_rule, List.length_append, List.length_cons, List.length_map]
      omega
    have multi_role' : 2 ≤ front.length + tail.length + 1 := by omega
    apply rightmostRule_rawHead_shell_impossible body headTail front ruleLetter tail
      β_large multi_role' head_unit mu_eq gap_eq lift_eq
    rw [rightmost_rule] at shell
    have role_letters :
        (front ++ .rule ruleLetter :: tail.map NearyTile.erase).map NearyTile.letter =
          front.map NearyTile.letter ++ ruleLetter :: tail := by
      rw [List.map_append, List.map_cons, map_erase_letter]
      rfl
    rw [role_letters] at shell
    have target_eq :
        (tagEncode β (front.map NearyTile.letter ++ ruleLetter :: tail)).length - 1 =
          front.length + tail.length + 1 +
            (front.map NearyTile.letter ++ ruleLetter :: tail).count .b * (β + 1) - 1 := by
      rw [tagEncode_length_eq_roleLength_add_markerCount]
      simp only [List.length_append, List.length_map, List.length_cons]
      omega
    rw [target_eq] at shell
    exact shell

end MatrixMortality.DecimalSetterFirstEntry
