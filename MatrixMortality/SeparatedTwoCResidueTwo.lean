import MatrixMortality.SeparatedTwoCCantor

/-!
# The first residue-two drainage cut

For the coupled width-three diagonal family `qₙ = bb c bⁿ c bⁿ`, this file refines the last
open congruence class. Writing `n = 3A - 1`, the case `A ≡ 1 (mod 3)` begins with six exact
`c`-headed events. The resulting queue has no `c` at a deletion head unless
`A ≡ 4 (mod 9)`. Consequently the classes `n ≡ 2, 20 (mod 27)` halt, and only
`n ≡ 11 (mod 27)` survives this first cut.
-/

namespace MatrixMortality.SeparatedTwoCResidue

open PeriodicHistory SeparatedTwoCOrbit Undecidability

private def residueTwoFinal (A middle : Nat) : List TagLetter :=
  bRun (4 * A) ++ ([.c] ++
    (bRun (3 * A - 1) ++ ([.c] ++
    (bRun (4 * A + 1) ++ ([.c] ++
    (bRun (3 * A - 1) ++ ([.c] ++
    (bRun (3 * A + middle + 2) ++ ([.c] ++
    (bRun (3 * A - 1) ++ ([.c] ++
    (bRun (4 * A + 1) ++ ([.c] ++
    (bRun (3 * A - 1) ++ ([.c] ++
      bRun (3 * A))))))))))))))))

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
    simp [residueTwoFinal, separatedBody, strokeCBB, stroke₃, tagOutput, nearyBody,
      bRun, List.append_assoc, bridgeGap, finalGap]

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

private theorem residueTwoFinal_one_clean (k : Nat) :
    ConstantAtMultiples 3 TagLetter.b
      (residueTwoFinal (9 * k + 1) (12 * k + 1)) := by
  have shifted : ConstantAtOffset 0 (residueTwoFinal (9 * k + 1) (12 * k + 1)) := by
    unfold residueTwoFinal
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
    unfold residueTwoFinal
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

end MatrixMortality.SeparatedTwoCResidue
