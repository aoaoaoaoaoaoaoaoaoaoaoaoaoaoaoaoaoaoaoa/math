import MatrixMortality.SeparatedTwoCCantor

/-!
# The first residue-two drainage cut

For the coupled width-three diagonal family `qₙ = bb c bⁿ c bⁿ`, this file refines the last
open congruence class. Writing `n = 3A - 1`, the case `A ≡ 1 (mod 3)` begins with six exact
`c`-headed events. The resulting queue has no `c` at a deletion head unless
`A ≡ 4 (mod 9)`. Consequently the classes `n ≡ 2, 20 (mod 27)` halt, and only
`n ≡ 11 (mod 27)` survives this first cut. Its exact four-`c` reproduction macro then proves
`n ≡ 11 (mod 81)` halts. `SeparatedTwoCDiagonal` closes the remaining centered block dynamics.
-/

namespace MatrixMortality.SeparatedTwoCResidue

open PeriodicHistory SeparatedTwoCOrbit Undecidability

/-- The exact two-copy expansion emitted by one canonical four-active-`c` block. -/
def fourCExpansion (A middle front : Nat) : List TagLetter :=
  bRun front ++ ([.c] ++
    (bRun (3 * A - 1) ++ ([.c] ++
    (bRun (4 * A + 1) ++ ([.c] ++
    (bRun (3 * A - 1) ++ ([.c] ++
    (bRun (3 * A + middle + 2) ++ ([.c] ++
    (bRun (3 * A - 1) ++ ([.c] ++
    (bRun (4 * A + 1) ++ ([.c] ++
    (bRun (3 * A - 1) ++ ([.c] ++
      bRun (3 * A))))))))))))))))

private def residueTwoFinal (A middle : Nat) : List TagLetter :=
  fourCExpansion A middle (4 * A)

@[simp] private theorem consumed_replicate_strokeBBB (count : Nat) :
    consumed (List.replicate count strokeBBB) = bRun (3 * count) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, consumed_cons, induction]
      simp [strokeBBB, stroke₃, Stroke.letters]
      exact congrArg bRun (by omega)

@[simp] private theorem produced_replicate_strokeBBB (body : List TagLetter) (count : Nat) :
    produced (tagOutput body) (List.replicate count strokeBBB) = bRun count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, produced_cons, induction]
      simp [strokeBBB, stroke₃, tagOutput, nearyBody]

private theorem cbbRun_reaches (body : List TagLetter) (count : Nat)
    (tail : List TagLetter) :
    TagReaches 3 (tagOutput body)
      ([.c] ++ bRun (3 * count + 2) ++ tail)
      (tail ++ tagOutput body .c ++ bRun count) := by
  have reach := tagReaches_history (tagOutput body)
    ([strokeCBB] ++ List.replicate count strokeBBB) tail
  simpa [strokeCBB, stroke₃, Stroke.letters, bRun, List.append_assoc] using reach

private def residueTwoStageOne (A : Nat) : List TagLetter :=
  [.c] ++ bRun (3 * A + 2) ++ [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (4 * A - 1)

private def residueTwoStageTwo (A : Nat) : List TagLetter :=
  [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (4 * A + 1) ++
    [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (4 * A)

private def residueTwoStageThree (A : Nat) : List TagLetter :=
  [.c] ++ bRun (4 * A + 1) ++ [.c] ++ bRun (3 * A - 1) ++
    [.c] ++ bRun (4 * A + 2) ++ [.c] ++ bRun (3 * A - 1) ++
      [.c] ++ bRun (4 * A - 1)

private def residueTwoStageFour (A middle : Nat) : List TagLetter :=
  [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (4 * A + 2) ++
    [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (4 * A + 1) ++
      [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (3 * A + middle)

private def residueTwoStageFive (A middle : Nat) : List TagLetter :=
  [.c] ++ bRun (4 * A + 2) ++ [.c] ++ bRun (3 * A - 1) ++
    [.c] ++ bRun (4 * A + 1) ++ [.c] ++ bRun (3 * A - 1) ++
      [.c] ++ bRun (3 * A + middle + 2) ++ [.c] ++ bRun (3 * A - 1) ++
        [.c] ++ bRun (4 * A - 1)

/-- The four-active-`c` block exposed by the first residue-two cut. -/
def fourCBlock (A : Nat) : List TagLetter :=
  [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (4 * A + 1) ++
    [.c] ++ bRun (3 * A - 1) ++ [.c]

/-- A canonical four-active-`c` block followed by its unary tail. -/
def fourCQueue (A tail : Nat) : List TagLetter :=
  fourCBlock A ++ bRun tail

private def fourCPrelude (A middle : Nat) : List TagLetter :=
  bRun (4 * A) ++ [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (4 * A + 1) ++
    [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (3 * A + middle + 2)

private def fourCStageOne (A tail : Nat) : List TagLetter :=
  [.c] ++ bRun (4 * A + 1) ++ [.c] ++ bRun (3 * A - 1) ++
    [.c] ++ bRun (tail + 2) ++ [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (4 * A - 1)

private def fourCStageTwo (A middle tail : Nat) : List TagLetter :=
  [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (tail + 2) ++
    [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (4 * A + 1) ++
      [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (3 * A + middle)

private def fourCStageThree (A middle tail : Nat) : List TagLetter :=
  [.c] ++ bRun (tail + 2) ++ [.c] ++ bRun (3 * A - 1) ++
    [.c] ++ bRun (4 * A + 1) ++ [.c] ++ bRun (3 * A - 1) ++
      [.c] ++ bRun (3 * A + middle + 2) ++ [.c] ++ bRun (3 * A - 1) ++
        [.c] ++ bRun (4 * A - 1)

private theorem initialPair_reaches_stageOne (A : Nat) (A_pos : 0 < A) :
    TagReaches 3 (tagOutput (separatedBody (3 * A - 1)))
      (pairQueue A (3 * A)) (residueTwoStageOne A) := by
  have reach := cbbRun_reaches (separatedBody (3 * A - 1)) (A - 1)
    ([.c] ++ bRun (3 * A))
  have firstGap : 3 * (A - 1) + 2 = 3 * A - 1 := by omega
  have bridgeGap : 3 * A + 1 + 1 = 3 * A + 2 := by omega
  have finalGap : 3 * A - 1 + 1 + (A - 1) = 4 * A - 1 := by omega
  simpa [pairQueue, residueTwoStageOne, separatedBody, tagOutput, nearyBody, bRun,
    List.append_assoc, firstGap, bridgeGap, finalGap] using reach

private theorem stageOne_reaches_stageTwo (A : Nat) (A_pos : 0 < A) :
    TagReaches 3 (tagOutput (separatedBody (3 * A - 1)))
      (residueTwoStageOne A) (residueTwoStageTwo A) := by
  have reach := cbbRun_reaches (separatedBody (3 * A - 1)) A
    ([.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (4 * A - 1))
  have bridgeGap : 4 * A - 1 + 1 + 1 = 4 * A + 1 := by omega
  have finalGap : 3 * A - 1 + 1 + A = 4 * A := by omega
  simpa [residueTwoStageOne, residueTwoStageTwo, separatedBody, tagOutput, nearyBody,
    bRun, List.append_assoc, bridgeGap, finalGap] using reach

private theorem stageTwo_reaches_stageThree (A : Nat) (A_pos : 0 < A) :
    TagReaches 3 (tagOutput (separatedBody (3 * A - 1)))
      (residueTwoStageTwo A) (residueTwoStageThree A) := by
  have reach := cbbRun_reaches (separatedBody (3 * A - 1)) (A - 1)
    ([.c] ++ bRun (4 * A + 1) ++ [.c] ++ bRun (3 * A - 1) ++
      [.c] ++ bRun (4 * A))
  have firstGap : 3 * (A - 1) + 2 = 3 * A - 1 := by omega
  have bridgeGap : 4 * A + 1 + 1 = 4 * A + 2 := by omega
  have finalGap : 3 * A - 1 + 1 + (A - 1) = 4 * A - 1 := by omega
  simpa [residueTwoStageTwo, residueTwoStageThree, separatedBody, tagOutput, nearyBody,
    bRun, List.append_assoc, firstGap, bridgeGap, finalGap] using reach

private theorem stageThree_reaches_stageFour (A middle : Nat)
    (A_pos : 0 < A) (middle_eq : 3 * middle = 4 * A - 1) :
    TagReaches 3 (tagOutput (separatedBody (3 * A - 1)))
      (residueTwoStageThree A) (residueTwoStageFour A middle) := by
  have reach := cbbRun_reaches (separatedBody (3 * A - 1)) middle
    ([.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (4 * A + 2) ++
      [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (4 * A - 1))
  have firstGap : 3 * middle + 2 = 4 * A + 1 := by omega
  have bridgeGap : 4 * A - 1 + 1 + 1 = 4 * A + 1 := by omega
  have finalGap : 3 * A - 1 + 1 + middle = 3 * A + middle := by omega
  simpa [residueTwoStageThree, residueTwoStageFour, separatedBody, tagOutput, nearyBody,
    bRun, List.append_assoc, firstGap, bridgeGap, finalGap] using reach

private theorem stageFour_reaches_stageFive (A middle : Nat) (A_pos : 0 < A) :
    TagReaches 3 (tagOutput (separatedBody (3 * A - 1)))
      (residueTwoStageFour A middle) (residueTwoStageFive A middle) := by
  have reach := cbbRun_reaches (separatedBody (3 * A - 1)) (A - 1)
    ([.c] ++ bRun (4 * A + 2) ++ [.c] ++ bRun (3 * A - 1) ++
      [.c] ++ bRun (4 * A + 1) ++ [.c] ++ bRun (3 * A - 1) ++
        [.c] ++ bRun (3 * A + middle))
  have firstGap : 3 * (A - 1) + 2 = 3 * A - 1 := by omega
  have bridgeGap : 3 * A + middle + 1 + 1 = 3 * A + middle + 2 := by omega
  have finalGap : 3 * A - 1 + 1 + (A - 1) = 4 * A - 1 := by omega
  simpa [residueTwoStageFour, residueTwoStageFive, separatedBody, tagOutput, nearyBody,
    bRun, List.append_assoc, firstGap, bridgeGap, finalGap] using reach

private theorem stageFive_step_final (A middle : Nat) (A_pos : 0 < A) :
    TagStep 3 (tagOutput (separatedBody (3 * A - 1)))
      (residueTwoStageFive A middle) (residueTwoFinal A middle) := by
  refine ⟨strokeCBB,
    bRun (4 * A) ++ [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (4 * A + 1) ++
      [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (3 * A + middle + 2) ++
        [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (4 * A - 1), ?_, ?_⟩
  · simp [residueTwoStageFive, strokeCBB, stroke₃, Stroke.letters, bRun,
      List.append_assoc]
  · have bridgeGap : 4 * A - 1 + 1 + 1 = 4 * A + 1 := by omega
    have finalGap : 3 * A - 1 + 1 = 3 * A := by omega
    simp [residueTwoFinal, fourCExpansion, separatedBody, strokeCBB, stroke₃, tagOutput, nearyBody,
      bRun, List.append_assoc, bridgeGap, finalGap]

private theorem fourCQueue_reaches_stageOne (A tail : Nat) (A_pos : 0 < A) :
    TagReaches 3 (tagOutput (separatedBody (3 * A - 1)))
      (fourCQueue A tail) (fourCStageOne A tail) := by
  have reach := cbbRun_reaches (separatedBody (3 * A - 1)) (A - 1)
    ([.c] ++ bRun (4 * A + 1) ++ [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun tail)
  have firstGap : 3 * (A - 1) + 2 = 3 * A - 1 := by omega
  have bridgeGap : tail + 1 + 1 = tail + 2 := by omega
  have finalGap : 3 * A - 1 + 1 + (A - 1) = 4 * A - 1 := by omega
  simpa [fourCQueue, fourCBlock, fourCStageOne, separatedBody, tagOutput, nearyBody,
    bRun, List.append_assoc, firstGap, bridgeGap, finalGap] using reach

private theorem fourCStageOne_reaches_stageTwo (A middle tail : Nat) (A_pos : 0 < A)
    (middle_eq : 3 * middle = 4 * A - 1) :
    TagReaches 3 (tagOutput (separatedBody (3 * A - 1)))
      (fourCStageOne A tail) (fourCStageTwo A middle tail) := by
  have reach := cbbRun_reaches (separatedBody (3 * A - 1)) middle
    ([.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (tail + 2) ++
      [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (4 * A - 1))
  have firstGap : 3 * middle + 2 = 4 * A + 1 := by omega
  have bridgeGap : 4 * A - 1 + 1 + 1 = 4 * A + 1 := by omega
  have finalGap : 3 * A - 1 + 1 + middle = 3 * A + middle := by omega
  simpa [fourCStageOne, fourCStageTwo, separatedBody, tagOutput, nearyBody,
    bRun, List.append_assoc, firstGap, bridgeGap, finalGap] using reach

private theorem fourCStageTwo_reaches_stageThree (A middle tail : Nat) (A_pos : 0 < A) :
    TagReaches 3 (tagOutput (separatedBody (3 * A - 1)))
      (fourCStageTwo A middle tail) (fourCStageThree A middle tail) := by
  have reach := cbbRun_reaches (separatedBody (3 * A - 1)) (A - 1)
    ([.c] ++ bRun (tail + 2) ++ [.c] ++ bRun (3 * A - 1) ++
      [.c] ++ bRun (4 * A + 1) ++ [.c] ++ bRun (3 * A - 1) ++
        [.c] ++ bRun (3 * A + middle))
  have firstGap : 3 * (A - 1) + 2 = 3 * A - 1 := by omega
  have bridgeGap : 3 * A + middle + 1 + 1 = 3 * A + middle + 2 := by omega
  have finalGap : 3 * A - 1 + 1 + (A - 1) = 4 * A - 1 := by omega
  simpa [fourCStageTwo, fourCStageThree, separatedBody, tagOutput, nearyBody,
    bRun, List.append_assoc, firstGap, bridgeGap, finalGap] using reach

private theorem fourCStageThree_step_final (A middle tail : Nat) (A_pos : 0 < A) :
    TagStep 3 (tagOutput (separatedBody (3 * A - 1)))
      (fourCStageThree A middle tail) (fourCExpansion A middle tail) := by
  refine ⟨strokeCBB,
    bRun tail ++ [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (4 * A + 1) ++
      [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (3 * A + middle + 2) ++
        [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (4 * A - 1), ?_, ?_⟩
  · simp [fourCStageThree, strokeCBB, stroke₃, Stroke.letters, bRun,
      List.append_assoc]
  · have bridgeGap : 4 * A - 1 + 1 + 1 = 4 * A + 1 := by omega
    have finalGap : 3 * A - 1 + 1 = 3 * A := by omega
    simp [fourCExpansion, separatedBody, strokeCBB, stroke₃, tagOutput, nearyBody,
      bRun, List.append_assoc, bridgeGap, finalGap]

/-- One canonical four-`c` block reproduces as two copies separated by the fixed middle run. -/
theorem fourCQueue_reaches_final (A middle tail : Nat) (A_pos : 0 < A)
    (middle_eq : 3 * middle = 4 * A - 1) :
    TagReaches 3 (tagOutput (separatedBody (3 * A - 1)))
      (fourCQueue A tail) (fourCExpansion A middle tail) := by
  have stageOne := fourCQueue_reaches_stageOne A tail A_pos
  have stageTwo := fourCStageOne_reaches_stageTwo A middle tail A_pos middle_eq
  have stageThree := fourCStageTwo_reaches_stageThree A middle tail A_pos
  have finalStep := Relation.ReflTransGen.single
    (fourCStageThree_step_final A middle tail A_pos)
  exact ((stageOne.trans stageTwo).trans stageThree).trans finalStep

private def fourCContextStageOne (A front : Nat) (tail : List TagLetter) : List TagLetter :=
  [.c] ++ bRun (4 * A + 1) ++ [.c] ++ bRun (3 * A - 1) ++
    [.c] ++ bRun (front + 2) ++ tail ++ bRun 2 ++ [.c] ++
      bRun (3 * A - 1) ++ [.c] ++ bRun (4 * A - 1)

private def fourCContextStageTwo (A middle front : Nat)
    (tail : List TagLetter) : List TagLetter :=
  [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (front + 2) ++ tail ++ bRun 2 ++
    [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (4 * A + 1) ++
      [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (3 * A + middle)

private def fourCContextStageThree (A middle front : Nat)
    (tail : List TagLetter) : List TagLetter :=
  [.c] ++ bRun (front + 2) ++ tail ++ bRun 2 ++ [.c] ++ bRun (3 * A - 1) ++
    [.c] ++ bRun (4 * A + 1) ++ [.c] ++ bRun (3 * A - 1) ++
      [.c] ++ bRun (3 * A + middle + 2) ++ [.c] ++ bRun (3 * A - 1) ++
        [.c] ++ bRun (4 * A - 1)

private theorem fourCContext_reaches_stageOne (A front : Nat) (tail : List TagLetter)
    (A_pos : 0 < A) :
    TagReaches 3 (tagOutput (separatedBody (3 * A - 1)))
      (fourCBlock A ++ bRun (front + 2) ++ tail)
      (fourCContextStageOne A front tail) := by
  have reach := cbbRun_reaches (separatedBody (3 * A - 1)) (A - 1)
    ([.c] ++ bRun (4 * A + 1) ++ [.c] ++ bRun (3 * A - 1) ++ [.c] ++
      bRun (front + 2) ++ tail)
  have firstGap : 3 * (A - 1) + 2 = 3 * A - 1 := by omega
  have finalGap : 3 * A - 1 + 1 + (A - 1) = 4 * A - 1 := by omega
  simpa [fourCBlock, fourCContextStageOne, separatedBody, tagOutput, nearyBody,
    bRun, List.append_assoc, firstGap, finalGap] using reach

private theorem fourCContext_stageOne_reaches_stageTwo
    (A middle front : Nat) (tail : List TagLetter) (A_pos : 0 < A)
    (middle_eq : 3 * middle = 4 * A - 1) :
    TagReaches 3 (tagOutput (separatedBody (3 * A - 1)))
      (fourCContextStageOne A front tail)
      (fourCContextStageTwo A middle front tail) := by
  have reach := cbbRun_reaches (separatedBody (3 * A - 1)) middle
    ([.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (front + 2) ++ tail ++ bRun 2 ++
      [.c] ++ bRun (3 * A - 1) ++ [.c] ++ bRun (4 * A - 1))
  have firstGap : 3 * middle + 2 = 4 * A + 1 := by omega
  have bridgeGap : 4 * A - 1 + 1 + 1 = 4 * A + 1 := by omega
  have finalGap : 3 * A - 1 + 1 + middle = 3 * A + middle := by omega
  simpa [fourCContextStageOne, fourCContextStageTwo, separatedBody, tagOutput,
    nearyBody, bRun, List.append_assoc, firstGap, bridgeGap, finalGap] using reach

private theorem fourCContext_stageTwo_reaches_stageThree
    (A middle front : Nat) (tail : List TagLetter) (A_pos : 0 < A) :
    TagReaches 3 (tagOutput (separatedBody (3 * A - 1)))
      (fourCContextStageTwo A middle front tail)
      (fourCContextStageThree A middle front tail) := by
  have reach := cbbRun_reaches (separatedBody (3 * A - 1)) (A - 1)
    ([.c] ++ bRun (front + 2) ++ tail ++ bRun 2 ++ [.c] ++ bRun (3 * A - 1) ++
      [.c] ++ bRun (4 * A + 1) ++ [.c] ++ bRun (3 * A - 1) ++
        [.c] ++ bRun (3 * A + middle))
  have firstGap : 3 * (A - 1) + 2 = 3 * A - 1 := by omega
  have bridgeGap : 3 * A + middle + 1 + 1 = 3 * A + middle + 2 := by omega
  have finalGap : 3 * A - 1 + 1 + (A - 1) = 4 * A - 1 := by omega
  simpa [fourCContextStageTwo, fourCContextStageThree, separatedBody, tagOutput,
    nearyBody, bRun, List.append_assoc, firstGap, bridgeGap, finalGap] using reach

private theorem fourCContext_stageThree_step_final
    (A middle front : Nat) (tail : List TagLetter) (A_pos : 0 < A) :
    TagStep 3 (tagOutput (separatedBody (3 * A - 1)))
      (fourCContextStageThree A middle front tail)
      (bRun front ++ tail ++ bRun 2 ++ fourCBlock A ++
        bRun (3 * A + middle + 2) ++ fourCBlock A ++ bRun (3 * A)) := by
  refine ⟨strokeCBB,
    bRun front ++ tail ++ bRun 2 ++ [.c] ++ bRun (3 * A - 1) ++ [.c] ++
      bRun (4 * A + 1) ++ [.c] ++ bRun (3 * A - 1) ++ [.c] ++
        bRun (3 * A + middle + 2) ++ [.c] ++ bRun (3 * A - 1) ++
          [.c] ++ bRun (4 * A - 1), ?_, ?_⟩
  · simp [fourCContextStageThree, strokeCBB, stroke₃, Stroke.letters, bRun,
      List.append_assoc]
  · have bridgeGap : 4 * A - 1 + 1 + 1 = 4 * A + 1 := by omega
    have finalGap : 3 * A - 1 + 1 = 3 * A := by omega
    simp [fourCBlock, separatedBody, strokeCBB, stroke₃, tagOutput, nearyBody,
      bRun, List.append_assoc, bridgeGap, finalGap]

/-- A canonical block followed by at least two unary letters reproduces across an arbitrary
suffix; the two consumed unary letters reappear immediately before the emitted copies. -/
theorem fourCBlock_bRun_reaches_final (A middle front : Nat) (tail : List TagLetter)
    (A_pos : 0 < A) (middle_eq : 3 * middle = 4 * A - 1) :
    TagReaches 3 (tagOutput (separatedBody (3 * A - 1)))
      (fourCBlock A ++ bRun (front + 2) ++ tail)
      (bRun front ++ tail ++ bRun 2 ++ fourCBlock A ++
        bRun (3 * A + middle + 2) ++ fourCBlock A ++ bRun (3 * A)) := by
  have stageOne := fourCContext_reaches_stageOne A front tail A_pos
  have stageTwo := fourCContext_stageOne_reaches_stageTwo
    A middle front tail A_pos middle_eq
  have stageThree := fourCContext_stageTwo_reaches_stageThree A middle front tail A_pos
  have finalStep := Relation.ReflTransGen.single
    (fourCContext_stageThree_step_final A middle front tail A_pos)
  exact ((stageOne.trans stageTwo).trans stageThree).trans finalStep

private def ConstantAtOffset (offset : Nat) (word : List TagLetter) : Prop :=
  ∀ (index : Nat) (index_lt : index < word.length), 3 ∣ offset + index →
    word[index] = .b

private theorem constantAtOffset_replicate (offset count : Nat) :
    ConstantAtOffset offset (bRun count) := by
  intro index index_lt _
  exact List.getElem_replicate index_lt

private theorem ConstantAtOffset.append {offset : Nat} {left right : List TagLetter}
    (left_clean : ConstantAtOffset offset left)
    (right_clean : ConstantAtOffset (offset + left.length) right) :
    ConstantAtOffset offset (left ++ right) := by
  intro index index_lt index_aligned
  by_cases in_left : index < left.length
  · rw [List.getElem_append_left in_left]
    exact left_clean index in_left index_aligned
  · have left_le : left.length ≤ index := Nat.le_of_not_gt in_left
    have right_lt : index - left.length < right.length := by
      simp only [List.length_append] at index_lt
      omega
    rw [List.getElem_append_right left_le]
    apply right_clean (index - left.length) right_lt
    convert index_aligned using 1; omega

private theorem constantAtOffset_cons_c {offset : Nat} {tail : List TagLetter}
    (inert : ¬3 ∣ offset) (tail_clean : ConstantAtOffset (offset + 1) tail) :
    ConstantAtOffset offset (.c :: tail) := by
  intro index index_lt index_aligned
  cases index with
  | zero => exact False.elim (inert index_aligned)
  | succ index =>
      simp only [List.getElem_cons_succ]
      apply tail_clean index (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using index_lt)
      convert index_aligned using 1; omega

private theorem constantAtOffset_bRun_c {offset run : Nat} {tail : List TagLetter}
    (inert : ¬3 ∣ offset + run)
    (tail_clean : ConstantAtOffset (offset + run + 1) tail) :
    ConstantAtOffset offset (bRun run ++ .c :: tail) := by
  apply ConstantAtOffset.append (constantAtOffset_replicate offset run)
  simpa [bRun, Nat.add_assoc] using constantAtOffset_cons_c inert tail_clean

private theorem sampleHeads_eq_replicate_of_constant (count : Nat) (word : List TagLetter)
    (enough : count * 3 ≤ word.length) (clean : ConstantAtMultiples 3 TagLetter.b word) :
    sampleHeads 3 (by omega) count word enough = bRun count := by
  apply List.ext_getElem
  · simp [bRun]
  · intro index sample_lt replicate_lt
    have index_lt : index < count := by simpa [bRun] using replicate_lt
    have source_lt : index * 3 < word.length := by
      exact ((Nat.mul_lt_mul_right (by omega : 0 < 3)).mpr index_lt).trans_le enough
    simp only [sampleHeads, List.getElem_ofFn, bRun, List.getElem_replicate]
    exact clean (index * 3) source_lt ⟨index, by omega⟩

@[simp] private theorem spell_tagOutput_bRun (body : List TagLetter) (count : Nat) :
    spell (tagOutput body) (bRun count) = bRun count := by
  unfold bRun
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      change [.b] ++ spell (tagOutput body) (List.replicate count .b) =
        .b :: List.replicate count .b
      rw [induction]
      rfl

private theorem cleanPrefix_reaches (body front tail : List TagLetter) (count : Nat)
    (front_length : front.length = count * 3)
    (front_clean : ConstantAtMultiples 3 TagLetter.b front) :
    TagReaches 3 (tagOutput body) (front ++ tail) (tail ++ bRun count) := by
  have enough : count * 3 ≤ front.length := front_length.ge
  have reach := tagReaches_chunks 3 (by omega) (tagOutput body) count front tail enough
  have sampled := sampleHeads_eq_replicate_of_constant count front enough front_clean
  rw [sampled] at reach
  have take_eq : front.take (count * 3) = front := by
    rw [← front_length]
    exact List.take_length
  rw [take_eq, spell_tagOutput_bRun] at reach
  exact reach

private theorem residueTwoFinal_prelude (A middle : Nat) :
    residueTwoFinal A middle =
      fourCPrelude A middle ++ fourCBlock A ++ bRun (3 * A) := by
  simp [residueTwoFinal, fourCExpansion, fourCPrelude, fourCBlock, List.append_assoc]

private theorem fourCPrelude_eleven_length (k : Nat) :
    (fourCPrelude (27 * k + 4) (36 * k + 5)).length = (165 * k + 26) * 3 := by
  simp [fourCPrelude, bRun]
  omega

private theorem fourCPrelude_eleven_clean (k : Nat) :
    ConstantAtMultiples 3 TagLetter.b (fourCPrelude (27 * k + 4) (36 * k + 5)) := by
  have shifted :
      ConstantAtOffset 0 (fourCPrelude (27 * k + 4) (36 * k + 5)) := by
    unfold fourCPrelude
    simp only [List.append_assoc, List.singleton_append]
    apply constantAtOffset_bRun_c
    · rw [Nat.dvd_iff_mod_eq_zero]
      omega
    · apply constantAtOffset_bRun_c
      · rw [Nat.dvd_iff_mod_eq_zero]
        omega
      · apply constantAtOffset_bRun_c
        · rw [Nat.dvd_iff_mod_eq_zero]
          omega
        · apply constantAtOffset_bRun_c
          · rw [Nat.dvd_iff_mod_eq_zero]
            omega
          · exact constantAtOffset_replicate _ _
  simpa [ConstantAtOffset, ConstantAtMultiples] using shifted

private theorem residueTwoFinal_eleven_reaches_fourCQueue (k : Nat) :
    TagReaches 3 (tagOutput (separatedBody (81 * k + 11)))
      (residueTwoFinal (27 * k + 4) (36 * k + 5))
      (fourCQueue (27 * k + 4) (246 * k + 38)) := by
  let A := 27 * k + 4
  let middle := 36 * k + 5
  let front := fourCPrelude A middle
  let tail := fourCBlock A ++ bRun (3 * A)
  let count := 165 * k + 26
  have front_length : front.length = count * 3 := by
    simpa [front, count, A, middle] using fourCPrelude_eleven_length k
  have front_clean : ConstantAtMultiples 3 TagLetter.b front := by
    simpa [front, A, middle] using fourCPrelude_eleven_clean k
  have reach := cleanPrefix_reaches (separatedBody (81 * k + 11)) front tail count
    front_length front_clean
  have source_eq : front ++ tail = residueTwoFinal A middle := by
    simpa [front, tail, List.append_assoc] using (residueTwoFinal_prelude A middle).symm
  have tail_eq : 3 * A + count = 246 * k + 38 := by
    dsimp [A, count]
    omega
  have target_eq : tail ++ bRun count = fourCQueue A (246 * k + 38) := by
    simp [tail, fourCQueue, bRun, List.append_assoc, tail_eq]
  rw [source_eq, target_eq] at reach
  simpa [A, middle] using reach

private theorem fourCPrelude_diagonal_length (a : Nat) :
    (fourCPrelude (9 * a + 4) (12 * a + 5)).length = (55 * a + 26) * 3 := by
  simp [fourCPrelude, bRun]
  omega

private theorem fourCPrelude_diagonal_clean (a : Nat) :
    ConstantAtMultiples 3 TagLetter.b (fourCPrelude (9 * a + 4) (12 * a + 5)) := by
  have shifted : ConstantAtOffset 0 (fourCPrelude (9 * a + 4) (12 * a + 5)) := by
    unfold fourCPrelude
    simp only [List.append_assoc, List.singleton_append]
    apply constantAtOffset_bRun_c
    · rw [Nat.dvd_iff_mod_eq_zero]
      omega
    · apply constantAtOffset_bRun_c
      · rw [Nat.dvd_iff_mod_eq_zero]
        omega
      · apply constantAtOffset_bRun_c
        · rw [Nat.dvd_iff_mod_eq_zero]
          omega
        · apply constantAtOffset_bRun_c
          · rw [Nat.dvd_iff_mod_eq_zero]
            omega
          · exact constantAtOffset_replicate _ _
  simpa [ConstantAtOffset, ConstantAtMultiples] using shifted

private theorem residueTwoFinal_diagonal_reaches_fourCQueue (a : Nat) :
    TagReaches 3 (tagOutput (separatedBody (27 * a + 11)))
      (residueTwoFinal (9 * a + 4) (12 * a + 5))
      (fourCQueue (9 * a + 4) (82 * a + 38)) := by
  let A := 9 * a + 4
  let middle := 12 * a + 5
  let front := fourCPrelude A middle
  let tail := fourCBlock A ++ bRun (3 * A)
  let count := 55 * a + 26
  have front_length : front.length = count * 3 := by
    simpa [front, count, A, middle] using fourCPrelude_diagonal_length a
  have front_clean : ConstantAtMultiples 3 TagLetter.b front := by
    simpa [front, A, middle] using fourCPrelude_diagonal_clean a
  have reach := cleanPrefix_reaches (separatedBody (27 * a + 11)) front tail count
    front_length front_clean
  have source_eq : front ++ tail = residueTwoFinal A middle := by
    simpa [front, tail, List.append_assoc] using (residueTwoFinal_prelude A middle).symm
  have tail_eq : 3 * A + count = 82 * a + 38 := by
    dsimp [A, count]
    omega
  have target_eq : tail ++ bRun count = fourCQueue A (82 * a + 38) := by
    simp [tail, fourCQueue, bRun, List.append_assoc, tail_eq]
  rw [source_eq, target_eq] at reach
  simpa [A, middle] using reach

private theorem fourCExpansion_eleven_clean (k : Nat) :
    ConstantAtMultiples 3 TagLetter.b
      (fourCExpansion (27 * k + 4) (36 * k + 5) (246 * k + 38)) := by
  have shifted : ConstantAtOffset 0
      (fourCExpansion (27 * k + 4) (36 * k + 5) (246 * k + 38)) := by
    unfold fourCExpansion
    simp only [List.singleton_append]
    apply constantAtOffset_bRun_c
    · rw [Nat.dvd_iff_mod_eq_zero]
      omega
    · apply constantAtOffset_bRun_c
      · rw [Nat.dvd_iff_mod_eq_zero]
        omega
      · apply constantAtOffset_bRun_c
        · rw [Nat.dvd_iff_mod_eq_zero]
          omega
        · apply constantAtOffset_bRun_c
          · rw [Nat.dvd_iff_mod_eq_zero]
            omega
          · apply constantAtOffset_bRun_c
            · rw [Nat.dvd_iff_mod_eq_zero]
              omega
            · apply constantAtOffset_bRun_c
              · rw [Nat.dvd_iff_mod_eq_zero]
                omega
              · apply constantAtOffset_bRun_c
                · rw [Nat.dvd_iff_mod_eq_zero]
                  omega
                · apply constantAtOffset_bRun_c
                  · rw [Nat.dvd_iff_mod_eq_zero]
                    omega
                  · exact constantAtOffset_replicate _ _
  simpa [ConstantAtOffset, ConstantAtMultiples] using shifted

private theorem residueTwoFinal_one_clean (k : Nat) :
    ConstantAtMultiples 3 TagLetter.b
      (residueTwoFinal (9 * k + 1) (12 * k + 1)) := by
  have shifted : ConstantAtOffset 0 (residueTwoFinal (9 * k + 1) (12 * k + 1)) := by
    unfold residueTwoFinal fourCExpansion
    simp only [List.singleton_append]
    apply constantAtOffset_bRun_c
    · rw [Nat.dvd_iff_mod_eq_zero]
      omega
    · apply constantAtOffset_bRun_c
      · rw [Nat.dvd_iff_mod_eq_zero]
        omega
      · apply constantAtOffset_bRun_c
        · rw [Nat.dvd_iff_mod_eq_zero]
          omega
        · apply constantAtOffset_bRun_c
          · rw [Nat.dvd_iff_mod_eq_zero]
            omega
          · apply constantAtOffset_bRun_c
            · rw [Nat.dvd_iff_mod_eq_zero]
              omega
            · apply constantAtOffset_bRun_c
              · rw [Nat.dvd_iff_mod_eq_zero]
                omega
              · apply constantAtOffset_bRun_c
                · rw [Nat.dvd_iff_mod_eq_zero]
                  omega
                · apply constantAtOffset_bRun_c
                  · rw [Nat.dvd_iff_mod_eq_zero]
                    omega
                  · exact constantAtOffset_replicate _ _
  simpa [ConstantAtOffset, ConstantAtMultiples] using shifted

private theorem residueTwoFinal_seven_clean (k : Nat) :
    ConstantAtMultiples 3 TagLetter.b
      (residueTwoFinal (9 * k + 7) (12 * k + 9)) := by
  have shifted : ConstantAtOffset 0 (residueTwoFinal (9 * k + 7) (12 * k + 9)) := by
    unfold residueTwoFinal fourCExpansion
    simp only [List.singleton_append]
    apply constantAtOffset_bRun_c
    · rw [Nat.dvd_iff_mod_eq_zero]
      omega
    · apply constantAtOffset_bRun_c
      · rw [Nat.dvd_iff_mod_eq_zero]
        omega
      · apply constantAtOffset_bRun_c
        · rw [Nat.dvd_iff_mod_eq_zero]
          omega
        · apply constantAtOffset_bRun_c
          · rw [Nat.dvd_iff_mod_eq_zero]
            omega
          · apply constantAtOffset_bRun_c
            · rw [Nat.dvd_iff_mod_eq_zero]
              omega
            · apply constantAtOffset_bRun_c
              · rw [Nat.dvd_iff_mod_eq_zero]
                omega
              · apply constantAtOffset_bRun_c
                · rw [Nat.dvd_iff_mod_eq_zero]
                  omega
                · apply constantAtOffset_bRun_c
                  · rw [Nat.dvd_iff_mod_eq_zero]
                    omega
                  · exact constantAtOffset_replicate _ _
  simpa [ConstantAtOffset, ConstantAtMultiples] using shifted

private theorem initialPair_reaches_final (A middle : Nat) (A_pos : 0 < A)
    (middle_eq : 3 * middle = 4 * A - 1) :
    TagReaches 3 (tagOutput (separatedBody (3 * A - 1)))
      (pairQueue A (3 * A)) (residueTwoFinal A middle) := by
  have stageOne := initialPair_reaches_stageOne A A_pos
  have stageTwo := stageOne_reaches_stageTwo A A_pos
  have stageThree := stageTwo_reaches_stageThree A A_pos
  have stageFour := stageThree_reaches_stageFour A middle A_pos middle_eq
  have stageFive := stageFour_reaches_stageFive A middle A_pos
  have finalStep := Relation.ReflTransGen.single (stageFive_step_final A middle A_pos)
  exact (((stageOne.trans stageTwo).trans stageThree).trans stageFour).trans
    (stageFive.trans finalStep)

/-- Every source in the last residue-two diagonal class reaches one canonical four-`c` block
with its exact unary tail. -/
theorem elevenModuloTwentySeven_reaches_fourCQueue (a : Nat) :
    TagReaches 3 (tagOutput (separatedBody (27 * a + 11)))
      (coupledInitial (27 * a + 11))
      (fourCQueue (9 * a + 4) (82 * a + 38)) := by
  let A := 9 * a + 4
  let middle := 12 * a + 5
  have A_pos : 0 < A := by simp [A]
  have middle_eq : 3 * middle = 4 * A - 1 := by
    dsimp [A, middle]
    omega
  have exponent_eq : 3 * A - 1 = 27 * a + 11 := by
    dsimp [A]
    omega
  have entry := initialPair_reaches_final A middle A_pos middle_eq
  have entry' :
      TagReaches 3 (tagOutput (separatedBody (27 * a + 11)))
        (pairQueue A (3 * A)) (residueTwoFinal A middle) := by
    rw [exponent_eq] at entry
    exact entry
  have exposure := residueTwoFinal_diagonal_reaches_fourCQueue a
  have queue_eq : pairQueue A (3 * A) = coupledInitial (27 * a + 11) := by
    rw [coupledInitial_eq]
    unfold pairQueue
    rw [exponent_eq]
    congr 2
    dsimp [A]
    omega
  rw [queue_eq] at entry'
  simpa [A, middle] using entry'.trans exposure

/-- Every coupled diagonal source with separation `n ≡ 2 (mod 27)` halts after the first
six active `c` events leave a queue whose deletion heads are all `b`. -/
theorem twoModuloTwentySeven_tagHaltsFrom (k : Nat) :
    TagHaltsFrom 3 (tagOutput (separatedBody (27 * k + 2)))
      (coupledInitial (27 * k + 2)) := by
  let A := 9 * k + 1
  let middle := 12 * k + 1
  have A_pos : 0 < A := by simp [A]
  have middle_eq : 3 * middle = 4 * A - 1 := by
    dsimp [A, middle]
    omega
  have reach := initialPair_reaches_final A middle A_pos middle_eq
  have final_halts := tagHaltsFrom_of_constantAtMultiples 3 (by omega)
    (tagOutput (separatedBody (3 * A - 1))) TagLetter.b rfl
    (residueTwoFinal A middle) (by
      simpa [A, middle] using residueTwoFinal_one_clean k)
  have root := tagHaltsFrom_of_reaches reach final_halts
  have exponent_eq : 3 * A - 1 = 27 * k + 2 := by
    dsimp [A]
    omega
  have queue_eq : pairQueue A (3 * A) = coupledInitial (27 * k + 2) := by
    rw [coupledInitial_eq]
    unfold pairQueue
    rw [exponent_eq]
    congr 2
    dsimp [A]
    omega
  rw [exponent_eq, queue_eq] at root
  exact root

/-- Every coupled diagonal source with separation `n ≡ 20 (mod 27)` also halts after the
same six-event macro; its final `c` letters all lie in the other inert block phase. -/
theorem twentyModuloTwentySeven_tagHaltsFrom (k : Nat) :
    TagHaltsFrom 3 (tagOutput (separatedBody (27 * k + 20)))
      (coupledInitial (27 * k + 20)) := by
  let A := 9 * k + 7
  let middle := 12 * k + 9
  have A_pos : 0 < A := by simp [A]
  have middle_eq : 3 * middle = 4 * A - 1 := by
    dsimp [A, middle]
    omega
  have reach := initialPair_reaches_final A middle A_pos middle_eq
  have final_halts := tagHaltsFrom_of_constantAtMultiples 3 (by omega)
    (tagOutput (separatedBody (3 * A - 1))) TagLetter.b rfl
    (residueTwoFinal A middle) (by
      simpa [A, middle] using residueTwoFinal_seven_clean k)
  have root := tagHaltsFrom_of_reaches reach final_halts
  have exponent_eq : 3 * A - 1 = 27 * k + 20 := by
    dsimp [A]
    omega
  have queue_eq : pairQueue A (3 * A) = coupledInitial (27 * k + 20) := by
    rw [coupledInitial_eq]
    unfold pairQueue
    rw [exponent_eq]
    congr 2
    dsimp [A]
    omega
  rw [exponent_eq, queue_eq] at root
  exact root

/-- In the surviving class `n ≡ 11 (mod 27)`, the first subresidue `n ≡ 11 (mod 81)`
also halts. The six-event cut exposes one canonical four-`c` block; its exact reproduction
leaves both copies away from every deletion head. -/
theorem elevenModuloEightyOne_tagHaltsFrom (k : Nat) :
    TagHaltsFrom 3 (tagOutput (separatedBody (81 * k + 11)))
      (coupledInitial (81 * k + 11)) := by
  let A := 27 * k + 4
  let middle := 36 * k + 5
  let tail := 246 * k + 38
  have A_pos : 0 < A := by simp [A]
  have middle_eq : 3 * middle = 4 * A - 1 := by
    dsimp [A, middle]
    omega
  have exponent_eq : 3 * A - 1 = 81 * k + 11 := by
    dsimp [A]
    omega
  have entry := initialPair_reaches_final A middle A_pos middle_eq
  have entry' :
      TagReaches 3 (tagOutput (separatedBody (81 * k + 11)))
        (pairQueue A (3 * A)) (residueTwoFinal A middle) := by
    rw [exponent_eq] at entry
    exact entry
  have exposure := residueTwoFinal_eleven_reaches_fourCQueue k
  have reproduction := fourCQueue_reaches_final A middle tail A_pos middle_eq
  have reproduction' :
      TagReaches 3 (tagOutput (separatedBody (81 * k + 11)))
        (fourCQueue A tail) (fourCExpansion A middle tail) := by
    rw [exponent_eq] at reproduction
    exact reproduction
  have final_halts := tagHaltsFrom_of_constantAtMultiples 3 (by omega)
    (tagOutput (separatedBody (81 * k + 11))) TagLetter.b rfl
    (fourCExpansion A middle tail) (by
      simpa [A, middle, tail] using fourCExpansion_eleven_clean k)
  have reach := (entry'.trans exposure).trans reproduction'
  have root := tagHaltsFrom_of_reaches reach final_halts
  have queue_eq : pairQueue A (3 * A) = coupledInitial (81 * k + 11) := by
    rw [coupledInitial_eq]
    unfold pairQueue
    rw [exponent_eq]
    congr 2
    dsimp [A]
    omega
  rw [queue_eq] at root
  exact root

end MatrixMortality.SeparatedTwoCResidue
