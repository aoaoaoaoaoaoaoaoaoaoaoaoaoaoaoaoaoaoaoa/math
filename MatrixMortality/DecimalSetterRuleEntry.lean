import MatrixMortality.DecimalSetterAllCRule

/-!
# Complete decimal rule-entry extinction

Every rightmost-rule word is either b-bearing or all-`c`.  The former branch is excluded by
the normalized three-arm coefficient theorem; the latter by the complete all-`c` frontier
extinction.  This module packages that exhaustive alphabet split at the physical raw-entry
shell.
-/

namespace MatrixMortality.DecimalSetterRuleEntry

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterAncestry
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterChamber
open MatrixMortality.DecimalSetterAllCRule
open MatrixMortality.DecimalSetterDepth
open MatrixMortality.DecimalSetterRuleCoefficient

/-- Every rightmost-rule block misses the physical multi-role pole shell from the distinguished
decimal-unit two-`c` raw head. -/
theorem rightmostRule_rawHead_shell_impossible
    {β : Nat} (body headTail : List TagLetter) (front : List NearyTile)
    (ruleLetter : TagLetter) (tail : List TagLetter) {μ E G : ℤ}
    (β_large : 2 ≤ β)
    (multi_role : 2 ≤ front.length + tail.length + 1)
    (head_unit :
      HasDecimalShell (code (peeledHeadWord β (.c :: .c :: headTail)) : ℚ) 0 0)
    (mu_eq : 9 * μ = 52 * 10 ^ β - 7)
    (gap_eq : E = 18 * 10 ^ β - 63)
    (lift_eq : G = 502 * 10 ^ β - 7)
    (shell :
      HasDecimalShell
        (((code (peeledHeadWord β (.c :: .c :: headTail)) : ℤ) *
          (E * code (punctuatedUpper β
              (front.map NearyTile.letter ++ ruleLetter :: tail)) +
            G * code
              (spell (nearyLower β body)
                (front ++ .rule ruleLetter :: tail.map NearyTile.erase))) -
          10 * μ * G * code
            (spell (nearyLower β body)
              (front ++ .rule ruleLetter :: tail.map NearyTile.erase)) : ℤ) : ℚ)
        (((front.length + tail.length + 1 +
          (front.map NearyTile.letter ++ ruleLetter :: tail).count .b *
            (β + 1) - 1 : Nat) : ℤ))
        (((front.length + tail.length + 1 +
          (front.map NearyTile.letter ++ ruleLetter :: tail).count .b *
            (β + 1) - 1 : Nat) : ℤ))) :
    False := by
  let letters := front.map NearyTile.letter ++ ruleLetter :: tail
  by_cases marker_mem : .b ∈ letters
  · exact bBearingRightmostRule_rawHead_shell_impossible
      body headTail front ruleLetter tail β_large
      (by simpa only [letters] using marker_mem) head_unit mu_eq gap_eq lift_eq shell
  · have every_letter_c : ∀ letter ∈ letters, letter = .c := by
      intro letter letter_mem
      cases letter with
      | b => exact False.elim (marker_mem letter_mem)
      | c => rfl
    have front_all_c :
        front.map NearyTile.letter = List.replicate front.length .c := by
      have raw : front.map NearyTile.letter =
          List.replicate (front.map NearyTile.letter).length .c := by
        apply List.eq_replicate_length.mpr
        intro letter letter_mem
        apply every_letter_c letter
        dsimp only [letters]
        exact List.mem_append_left _ letter_mem
      simpa using raw
    have rule_c : ruleLetter = .c := by
      apply every_letter_c ruleLetter
      dsimp only [letters]
      simp
    let tailWidth := tail.length
    have tail_all_c : tail = List.replicate tailWidth .c := by
      have raw : tail = List.replicate tail.length .c := by
        apply List.eq_replicate_length.mpr
        intro letter letter_mem
        apply every_letter_c letter
        dsimp only [letters]
        exact List.mem_append_right _ (by simp [letter_mem])
      simpa only [tailWidth] using raw
    have marker_count :
        (front.map NearyTile.letter ++ ruleLetter :: tail).count .b = 0 := by
      apply List.count_eq_zero.mpr
      simpa only [letters] using marker_mem
    have target_eq :
        front.length + tail.length + 1 +
            (front.map NearyTile.letter ++ ruleLetter :: tail).count .b * (β + 1) - 1 =
          front.length + tail.length := by
      rw [marker_count]
      omega
    have multi_role' : 2 ≤ front.length + tailWidth + 1 := by
      simpa only [tailWidth] using multi_role
    subst ruleLetter
    rw [target_eq, tail_all_c] at shell
    simp only [List.length_replicate, List.map_replicate] at shell
    apply allCRightmostRule_rawHead_shell_impossible
      (tailWidth := tailWidth) body headTail front β_large multi_role'
      front_all_c head_unit mu_eq gap_eq lift_eq
    exact shell

end MatrixMortality.DecimalSetterRuleEntry
