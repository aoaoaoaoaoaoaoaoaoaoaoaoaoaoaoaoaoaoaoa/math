import MatrixMortality.SeparatedTwoCDiagonal

/-!
# Unequal separated two-c cycles

Every nontrivial even width-three body `b^p c b^r c b^s` has a canonical one-active-`c` queue.
Away from the middle phase `r ≡ 2 (mod 3)`, that queue returns after exactly
`(p+r+s)/2+1` steps.

Away from the same middle phase, the coupled source enters this cycle on the sheared diagonal

`b^(3t+2) c b^(n+t) c b^n`.

Thus every member of this two-parameter family with `n+t ≢ 2 (mod 3)` is nonhalting; positive
shear gives unequal runs.

Inside the excluded middle phase, a four-active-`c` history drains every source with
`n+t ≡ 8 (mod 9)` and shear not congruent to two modulo three.

On the surviving shear phase, a ten-active-`c` history drains the subwedge with middle run
`26 mod 27` and shear `2` or `5 mod 9`.

A matched six-active-`c` history also drains two joint phases in middle residues two and five
modulo nine.

Two histories containing inert `bbc`/`bcb` crossings drain one joint subphase in each of the
four phase-mismatched residue pairs over the same two middle residues.
-/

namespace MatrixMortality.SeparatedTwoCShear

open BranchingHistory PeriodicHistory SeparatedTwoCOrbit

/-- A width-three body with two distinguished `c` letters and three unary runs. -/
def twoCBody (left middle right : Nat) : List TagLetter :=
  bRun left ++ [.c] ++ bRun middle ++ [.c] ++ bRun right

@[simp] theorem twoCBody_length (left middle right : Nat) :
    (twoCBody left middle right).length = left + middle + right + 2 := by
  simp [twoCBody, bRun]
  omega

/-- The canonical one-active-`c` queue of an even two-`c` body. -/
def canonicalCycleQueue (halfRunSum right : Nat) : List TagLetter :=
  [.c] ++ bRun (right + halfRunSum + 1)

private def cycleFront (left middle right halfRunSum : Nat) : List TagLetter :=
  bRun (left + right + halfRunSum - 1) ++ [.c] ++ bRun middle

private def cycleExpansion (left middle right halfRunSum : Nat) : List TagLetter :=
  cycleFront left middle right halfRunSum ++ [.c] ++ bRun (right + 1)

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
    convert index_aligned using 1
    omega

private theorem constantAtOffset_cons_c {offset : Nat} {tail : List TagLetter}
    (inert : ¬3 ∣ offset) (tail_clean : ConstantAtOffset (offset + 1) tail) :
    ConstantAtOffset offset (.c :: tail) := by
  intro index index_lt index_aligned
  cases index with
  | zero => exact False.elim (inert index_aligned)
  | succ index =>
      simp only [List.getElem_cons_succ]
      apply tail_clean index (by
        simpa only [List.length_cons, Nat.succ_lt_succ_iff] using index_lt)
      convert index_aligned using 1
      omega

private theorem constantAtOffset_bRun_c {offset run : Nat} {tail : List TagLetter}
    (inert : ¬3 ∣ offset + run)
    (tail_clean : ConstantAtOffset (offset + run + 1) tail) :
    ConstantAtOffset offset (bRun run ++ .c :: tail) := by
  apply ConstantAtOffset.append (constantAtOffset_replicate offset run)
  simpa [bRun, Nat.add_assoc] using constantAtOffset_cons_c inert tail_clean

private theorem sampleHeads_eq_bRun (count : Nat) (word : List TagLetter)
    (enough : count * 3 ≤ word.length)
    (clean : Undecidability.ConstantAtMultiples 3 TagLetter.b word) :
    Undecidability.sampleHeads 3 (by omega) count word enough = bRun count := by
  apply List.ext_getElem
  · simp [bRun]
  · intro index sample_lt replicate_lt
    have index_lt : index < count := by simpa [bRun] using replicate_lt
    have source_lt : index * 3 < word.length :=
      ((Nat.mul_lt_mul_right (by omega : 0 < 3)).mpr index_lt).trans_le enough
    simp only [Undecidability.sampleHeads, List.getElem_ofFn, bRun,
      List.getElem_replicate]
    exact clean (index * 3) source_lt ⟨index, by omega⟩

private theorem spell_tagOutput_bRun (body : List TagLetter) (count : Nat) :
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

private theorem cleanPrefix_reachesIn (body front tail : List TagLetter) (count : Nat)
    (front_length : front.length = count * 3)
    (front_clean : Undecidability.ConstantAtMultiples 3 TagLetter.b front) :
    TagReachesIn 3 (tagOutput body) count (front ++ tail) (tail ++ bRun count) := by
  have enough : count * 3 ≤ front.length := front_length.ge
  have reach := Undecidability.tagReachesIn_chunks 3 (by omega) (tagOutput body)
    count front tail enough
  have sampled := sampleHeads_eq_bRun count front enough front_clean
  rw [sampled] at reach
  have take_eq : front.take (count * 3) = front := by
    rw [← front_length]
    exact List.take_length
  rw [take_eq, spell_tagOutput_bRun] at reach
  simpa using reach

private theorem cycleFront_length (left middle right halfRunSum : Nat)
    (halfRunSum_pos : 0 < halfRunSum)
    (run_sum : left + middle + right = 2 * halfRunSum) :
    (cycleFront left middle right halfRunSum).length = halfRunSum * 3 := by
  simp [cycleFront, bRun]
  omega

private theorem cycleFront_clean (left middle right halfRunSum : Nat)
    (halfRunSum_pos : 0 < halfRunSum)
    (run_sum : left + middle + right = 2 * halfRunSum)
    (middle_phase : middle % 3 ≠ 2) :
    Undecidability.ConstantAtMultiples 3 TagLetter.b
      (cycleFront left middle right halfRunSum) := by
  let offset := left + right + halfRunSum - 1
  have offset_balance : offset + middle + 1 = 3 * halfRunSum := by
    dsimp only [offset]
    omega
  have offset_inert : ¬3 ∣ offset := by
    intro offset_divides
    have offset_mod : offset % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp offset_divides
    have offset_division := Nat.mod_add_div offset 3
    have middle_division := Nat.mod_add_div middle 3
    have middle_mod_lt : middle % 3 < 3 := Nat.mod_lt middle (by omega)
    omega
  have clean : ConstantAtOffset 0 (bRun offset ++ .c :: bRun middle) := by
    apply constantAtOffset_bRun_c (by simpa using offset_inert)
    simpa [Nat.add_assoc] using constantAtOffset_replicate (offset + 1) middle
  simpa [cycleFront, offset, List.append_assoc, ConstantAtOffset,
    Undecidability.ConstantAtMultiples] using clean

private theorem canonicalCycle_step (left middle right halfRunSum : Nat)
    (halfRunSum_pos : 0 < halfRunSum) :
    TagStep 3 (tagOutput (twoCBody left middle right))
      (canonicalCycleQueue halfRunSum right)
      (cycleExpansion left middle right halfRunSum) := by
  have source_exponent : right + halfRunSum + 1 = 2 + (right + halfRunSum - 1) := by
    omega
  have prefix_exponent : right + halfRunSum - 1 + left =
      left + right + halfRunSum - 1 := by
    omega
  have source_split : 2 + (right + halfRunSum - 1) =
      right + halfRunSum - 1 + 1 + 1 := by
    omega
  refine ⟨stroke₃ .c .b .b, bRun (right + halfRunSum - 1), ?_, ?_⟩
  · rw [canonicalCycleQueue, source_exponent]
    simp [stroke₃, Stroke.letters, bRun, source_split]
  · simp [cycleExpansion, cycleFront, twoCBody, stroke₃, tagOutput, nearyBody,
      bRun, List.append_assoc, prefix_exponent]

/-- The canonical queue returns after one active `c` step and `(p+r+s)/2` inert steps. -/
theorem canonicalCycle_reachesIn (left middle right halfRunSum : Nat)
    (halfRunSum_pos : 0 < halfRunSum)
    (run_sum : left + middle + right = 2 * halfRunSum)
    (middle_phase : middle % 3 ≠ 2) :
    TagReachesIn 3 (tagOutput (twoCBody left middle right)) (halfRunSum + 1)
      (canonicalCycleQueue halfRunSum right) (canonicalCycleQueue halfRunSum right) := by
  have drainage := cleanPrefix_reachesIn (twoCBody left middle right)
    (cycleFront left middle right halfRunSum) ([.c] ++ bRun (right + 1)) halfRunSum
    (cycleFront_length left middle right halfRunSum halfRunSum_pos run_sum)
    (cycleFront_clean left middle right halfRunSum halfRunSum_pos run_sum middle_phase)
  have drainage' :
      TagReachesIn 3 (tagOutput (twoCBody left middle right)) halfRunSum
        (cycleExpansion left middle right halfRunSum)
        (canonicalCycleQueue halfRunSum right) := by
    have exponent_eq : right + 1 + halfRunSum = right + halfRunSum + 1 := by omega
    simpa [cycleExpansion, canonicalCycleQueue, bRun, List.append_assoc, exponent_eq] using drainage
  exact Relation.ReachesIn.head
    (canonicalCycle_step left middle right halfRunSum halfRunSum_pos) drainage'

/-- The canonical queue of every positive even two-`c` body off middle phase two is nonhalting. -/
theorem canonicalCycle_not_tagHaltsFrom (left middle right halfRunSum : Nat)
    (halfRunSum_pos : 0 < halfRunSum)
    (run_sum : left + middle + right = 2 * halfRunSum)
    (middle_phase : middle % 3 ≠ 2) :
    ¬TagHaltsFrom 3 (tagOutput (twoCBody left middle right))
      (canonicalCycleQueue halfRunSum right) := by
  let queue := canonicalCycleQueue halfRunSum right
  have cycle :
      TagReachesIn 3 (tagOutput (twoCBody left middle right)) (halfRunSum + 1)
        queue queue :=
    canonicalCycle_reachesIn left middle right halfRunSum halfRunSum_pos run_sum middle_phase
  apply Undecidability.not_tagHaltsFrom_of_transGen_progress (fun candidate => candidate = queue)
  · intro candidate candidate_eq
    subst candidate
    exact ⟨queue, rfl, cycle.toTransGen (by omega)⟩
  · rfl

/-- The sheared diagonal `b^(3t+2) c b^(n+t) c b^n`. -/
def shearedBody (shear separation : Nat) : List TagLetter :=
  twoCBody (3 * shear + 2) (separation + shear) separation

/-- Every sheared-diagonal body satisfies the scheduled width-three length envelope. -/
theorem shearedBody_admissible (shear separation : Nat) :
    2 ≤ (shearedBody shear separation).length ∧
      2 ∣ (shearedBody shear separation).length := by
  rw [shearedBody, twoCBody_length]
  constructor
  · omega
  · refine ⟨separation + 2 * shear + 2, ?_⟩
    omega

@[simp] theorem shearedBody_zero (separation : Nat) :
    shearedBody 0 separation = separatedBody separation := by
  simp [shearedBody, twoCBody, separatedBody, bRun, List.append_assoc]

/-- The source queue coupled to a sheared-diagonal body. -/
def shearedInitial (shear separation : Nat) : List TagLetter :=
  (shearedBody shear separation).drop 2 ++ [.b]

/-- The diagonal-shaped queue exposed after deleting the shear prefix. -/
def shearedEntryQueue (shear separation : Nat) : List TagLetter :=
  [.c] ++ bRun (separation + shear) ++ [.c] ++ bRun (separation + shear + 1)

@[simp] theorem shearedInitial_eq (shear separation : Nat) :
    shearedInitial shear separation =
      bRun (3 * shear) ++ [.c] ++ bRun (separation + shear) ++ [.c] ++
        bRun (separation + 1) := by
  unfold shearedInitial shearedBody twoCBody
  simp only [List.append_assoc]
  rw [List.drop_append_of_le_length (by simp [bRun])]
  rw [bRun, List.drop_replicate]
  have exponent_eq : 3 * shear + 2 - 2 = 3 * shear := by omega
  simp [bRun, List.append_assoc, exponent_eq]

private theorem shearedInitial_reaches_entry (shear separation : Nat) :
    TagReachesIn 3 (tagOutput (shearedBody shear separation)) shear
      (shearedInitial shear separation) (shearedEntryQueue shear separation) := by
  have drainage := cleanPrefix_reachesIn (shearedBody shear separation) (bRun (3 * shear))
    ([.c] ++ bRun (separation + shear) ++ [.c] ++ bRun (separation + 1)) shear
    (by simp [bRun, Nat.mul_comm])
    (Undecidability.ConstantAtMultiples.replicate 3 (3 * shear) TagLetter.b)
  have exponent_eq : separation + 1 + shear = separation + shear + 1 := by omega
  simpa [shearedInitial_eq, shearedEntryQueue, bRun, List.append_assoc, exponent_eq] using drainage

private def shearedEntryFront (shear separation : Nat) : List TagLetter :=
  let middle := separation + shear
  bRun (middle - 2) ++ [.c] ++ bRun (middle + 3 * shear + 3) ++ [.c] ++ bRun middle

private def shearedEntryExpansion (shear separation : Nat) : List TagLetter :=
  shearedEntryFront shear separation ++ [.c] ++ bRun (separation + 1)

private theorem shearedEntry_step (shear separation : Nat)
    (middle_large : 2 ≤ separation + shear) :
    TagStep 3 (tagOutput (shearedBody shear separation))
      (shearedEntryQueue shear separation) (shearedEntryExpansion shear separation) := by
  let middle := separation + shear
  have source_exponent : middle = 2 + (middle - 2) := by
    dsimp only [middle]
    omega
  have bridge_exponent : middle + 1 + (3 * shear + 2) = middle + 3 * shear + 3 := by
    omega
  have source_split : 2 + (middle - 2) = middle - 2 + 1 + 1 := by
    omega
  refine ⟨stroke₃ .c .b .b, bRun (middle - 2) ++ [.c] ++ bRun (middle + 1), ?_, ?_⟩
  · rw [shearedEntryQueue, show separation + shear = middle by rfl, source_exponent]
    simp [stroke₃, Stroke.letters, bRun, List.append_assoc, source_split]
  · simp [shearedEntryExpansion, shearedEntryFront, shearedBody, twoCBody, middle,
      stroke₃, tagOutput, nearyBody, bRun, List.append_assoc, bridge_exponent]

private theorem shearedEntryFront_length (shear separation : Nat)
    (middle_large : 2 ≤ separation + shear) :
    (shearedEntryFront shear separation).length =
      (separation + 2 * shear + 1) * 3 := by
  simp [shearedEntryFront, bRun]
  omega

private theorem shearedEntryFront_clean (shear separation : Nat)
    (middle_large : 2 ≤ separation + shear)
    (middle_phase : (separation + shear) % 3 ≠ 2) :
    Undecidability.ConstantAtMultiples 3 TagLetter.b
      (shearedEntryFront shear separation) := by
  let middle := separation + shear
  have first_inert : ¬3 ∣ middle - 2 := by
    intro divides
    have offset_mod : (middle - 2) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp divides
    have offset_division := Nat.mod_add_div (middle - 2) 3
    have middle_division := Nat.mod_add_div middle 3
    have middle_mod_lt : middle % 3 < 3 := Nat.mod_lt middle (by omega)
    omega
  have second_inert : ¬3 ∣ (middle - 2) + 1 + (middle + 3 * shear + 3) := by
    intro divides
    have offset_mod : ((middle - 2) + 1 + (middle + 3 * shear + 3)) % 3 = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp divides
    have offset_division :=
      Nat.mod_add_div ((middle - 2) + 1 + (middle + 3 * shear + 3)) 3
    have middle_division := Nat.mod_add_div middle 3
    have middle_mod_lt : middle % 3 < 3 := Nat.mod_lt middle (by omega)
    omega
  have clean : ConstantAtOffset 0
      (bRun (middle - 2) ++ .c ::
        (bRun (middle + 3 * shear + 3) ++ .c :: bRun middle)) := by
    apply constantAtOffset_bRun_c (by simpa using first_inert)
    apply constantAtOffset_bRun_c (by simpa [bRun] using second_inert)
    simpa [Nat.add_assoc] using constantAtOffset_replicate
      ((middle - 2) + 1 + (middle + 3 * shear + 3) + 1) middle
  simpa [shearedEntryFront, middle, List.append_assoc, ConstantAtOffset,
    Undecidability.ConstantAtMultiples] using clean

private theorem shearedEntry_reaches_cycle_large (shear separation : Nat)
    (middle_large : 2 ≤ separation + shear)
    (middle_phase : (separation + shear) % 3 ≠ 2) :
    TagReaches 3 (tagOutput (shearedBody shear separation))
      (shearedEntryQueue shear separation)
      (canonicalCycleQueue (separation + 2 * shear + 1) separation) := by
  let count := separation + 2 * shear + 1
  have drainage := cleanPrefix_reachesIn (shearedBody shear separation)
    (shearedEntryFront shear separation) ([.c] ++ bRun (separation + 1)) count
    (by simpa [count] using shearedEntryFront_length shear separation middle_large)
    (shearedEntryFront_clean shear separation middle_large middle_phase)
  have drainage' :
      TagReachesIn 3 (tagOutput (shearedBody shear separation)) count
        (shearedEntryExpansion shear separation)
        (canonicalCycleQueue count separation) := by
    have exponent_eq : separation + 1 + count = separation + count + 1 := by omega
    simpa [shearedEntryExpansion, canonicalCycleQueue, count, bRun, List.append_assoc,
      exponent_eq] using drainage
  exact (Relation.ReflTransGen.single (shearedEntry_step shear separation middle_large)).trans
    drainage'.toReaches

private def shearedOneEntryFront (shear : Nat) : List TagLetter :=
  bRun (3 * shear + 4) ++ [.c] ++ bRun 1

private def shearedOneEntryExpansion (shear separation : Nat) : List TagLetter :=
  shearedOneEntryFront shear ++ [.c] ++ bRun (separation + 1)

private theorem shearedOneEntry_step (shear separation : Nat)
    (middle_one : separation + shear = 1) :
    TagStep 3 (tagOutput (shearedBody shear separation))
      (shearedEntryQueue shear separation) (shearedOneEntryExpansion shear separation) := by
  refine ⟨stroke₃ .c .b .c, bRun (separation + shear + 1), ?_, ?_⟩
  · simp [shearedEntryQueue, middle_one, stroke₃, Stroke.letters, bRun]
  · simp [shearedOneEntryExpansion, shearedOneEntryFront, shearedBody, twoCBody,
      middle_one, stroke₃, tagOutput, nearyBody, bRun, List.append_assoc]

private theorem shearedOneEntryFront_clean (shear : Nat) :
    Undecidability.ConstantAtMultiples 3 TagLetter.b (shearedOneEntryFront shear) := by
  have inert : ¬3 ∣ 3 * shear + 4 := by omega
  have clean : ConstantAtOffset 0 (bRun (3 * shear + 4) ++ .c :: bRun 1) := by
    apply constantAtOffset_bRun_c (by simpa using inert)
    simpa [Nat.add_assoc] using constantAtOffset_replicate (3 * shear + 5) 1
  simpa [shearedOneEntryFront, ConstantAtOffset,
    Undecidability.ConstantAtMultiples] using clean

private theorem shearedEntry_reaches_cycle_one (shear separation : Nat)
    (middle_one : separation + shear = 1) :
    TagReaches 3 (tagOutput (shearedBody shear separation))
      (shearedEntryQueue shear separation)
      (canonicalCycleQueue (separation + 2 * shear + 1) separation) := by
  let count := shear + 2
  have drainage := cleanPrefix_reachesIn (shearedBody shear separation)
    (shearedOneEntryFront shear) ([.c] ++ bRun (separation + 1)) count
    (by simp [shearedOneEntryFront, count, bRun]; omega)
    (shearedOneEntryFront_clean shear)
  have count_eq : count = separation + 2 * shear + 1 := by
    dsimp only [count]
    omega
  have drainage' :
      TagReachesIn 3 (tagOutput (shearedBody shear separation)) count
        (shearedOneEntryExpansion shear separation)
        (canonicalCycleQueue count separation) := by
    have exponent_eq : separation + 1 + count = separation + count + 1 := by omega
    simpa [shearedOneEntryExpansion, canonicalCycleQueue, bRun, List.append_assoc,
      exponent_eq] using drainage
  rw [← count_eq]
  exact (Relation.ReflTransGen.single
      (shearedOneEntry_step shear separation middle_one)).trans drainage'.toReaches

/-- Every positive sheared-diagonal source off middle phase two reaches its canonical cycle. -/
theorem shearedInitial_reaches_cycle (shear separation : Nat)
    (middle_pos : 0 < separation + shear)
    (middle_phase : (separation + shear) % 3 ≠ 2) :
    TagReaches 3 (tagOutput (shearedBody shear separation))
      (shearedInitial shear separation)
      (canonicalCycleQueue (separation + 2 * shear + 1) separation) := by
  have entry := (shearedInitial_reaches_entry shear separation).toReaches
  by_cases middle_one : separation + shear = 1
  · exact entry.trans (shearedEntry_reaches_cycle_one shear separation middle_one)
  · have middle_large : 2 ≤ separation + shear := by omega
    exact entry.trans
      (shearedEntry_reaches_cycle_large shear separation middle_large middle_phase)

/-- Every sheared-diagonal coupled source off middle phase two is nonhalting. -/
theorem sheared_not_tagHaltsFrom (shear separation : Nat)
    (middle_phase : (separation + shear) % 3 ≠ 2) :
    ¬TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
      (shearedInitial shear separation) := by
  by_cases middle_zero : separation + shear = 0
  · have shear_zero : shear = 0 := by omega
    have separation_zero : separation = 0 := by omega
    subst shear
    subst separation
    simpa [shearedBody, shearedInitial, twoCBody, SeparatedTwoCOrbit.separatedBody,
      SeparatedTwoCOrbit.coupledInitial, bRun] using
      SeparatedTwoCDiagonal.zeroSeparation_not_tagHaltsFrom
  · have middle_pos : 0 < separation + shear := Nat.pos_of_ne_zero middle_zero
    have reaches := shearedInitial_reaches_cycle shear separation middle_pos middle_phase
    have cycle_nonhalting := canonicalCycle_not_tagHaltsFrom
      (3 * shear + 2) (separation + shear) separation (separation + 2 * shear + 1)
      (by omega) (by omega) middle_phase
    intro initial_halts
    exact cycle_nonhalting
      (Undecidability.tagHaltsFrom_after_reaches reaches initial_halts)

private theorem shear_consumed_append (left right : List (Stroke TagLetter 3)) :
    consumed (left ++ right) = consumed left ++ consumed right := by
  simp [consumed]

private theorem shear_produced_append (output : TagLetter → List TagLetter)
    (left right : List (Stroke TagLetter 3)) :
    produced output (left ++ right) = produced output left ++ produced output right := by
  simp [produced]

private theorem shearedOutput_c (shear separation : Nat) :
    tagOutput (shearedBody shear separation) .c =
      bRun (3 * shear + 2) ++ [.c] ++ bRun (separation + shear) ++ [.c] ++
        bRun (separation + 1) := by
  simp [shearedBody, twoCBody, tagOutput, nearyBody, bRun, List.append_assoc]

private theorem shearedOutput_bridge (shear separation front following : Nat)
    (tail : List TagLetter) :
    bRun front ++
        (tagOutput (shearedBody shear separation) .c ++ (bRun following ++ tail)) =
      bRun (front + (3 * shear + 2)) ++ [.c] ++ bRun (separation + shear) ++ [.c] ++
        bRun (separation + 1 + following) ++ tail := by
  simp [shearedOutput_c, bRun, List.append_assoc]

private theorem shearedOutput_initialBridge
    (shear separation left front following : Nat) (tail : List TagLetter) :
    bRun left ++
        (bRun front ++
          (tagOutput (shearedBody shear separation) .c ++ (bRun following ++ tail))) =
      bRun (left + front + (3 * shear + 2)) ++ [.c] ++
        bRun (separation + shear) ++ [.c] ++ bRun (separation + 1 + following) ++ tail := by
  simp [shearedOutput_c, bRun, List.append_assoc]
  omega

private def shearedEightHistory (shear k : Nat) : List (Stroke TagLetter 3) :=
  [strokeCBB] ++ List.replicate (3 * k + 2) strokeBBB ++ [strokeCBB] ++
    List.replicate (3 * k + 3 + shear) strokeBBB ++ [strokeCBB] ++
      List.replicate (3 * k + 2) strokeBBB ++ [strokeCBB]

private def shearedEightFinal (shear separation k : Nat) : List TagLetter :=
  bRun (12 * k + 11 + 2 * shear) ++ [.c] ++ bRun (9 * k + 8) ++ [.c] ++
    bRun (12 * k + 14 + 3 * shear) ++ [.c] ++ bRun (9 * k + 8) ++ [.c] ++
      bRun (12 * k + 13 + 2 * shear) ++ [.c] ++ bRun (9 * k + 8) ++ [.c] ++
        bRun (separation + 1)

private theorem shearedEightHistory_equation (shear separation k : Nat)
    (middle_eq : separation + shear = 9 * k + 8) :
    consumed (shearedEightHistory shear k) ++ shearedEightFinal shear separation k =
      shearedEntryQueue shear separation ++
        produced (tagOutput (shearedBody shear separation))
          (shearedEightHistory shear k) := by
  simp only [shearedEightHistory, List.singleton_append, List.append_assoc]
  simp [shearedEightFinal, shearedEntryQueue, shearedBody, twoCBody, strokeCBB, stroke₃,
    Stroke.letters, tagOutput, nearyBody, bRun, List.append_assoc]
  have shortRun : 3 * (3 * k + 2) + 1 + 1 = 9 * k + 8 := by omega
  have longRun : 3 * (3 * k + 3 + shear) + 1 + 1 = 9 * k + 11 + 3 * shear := by
    omega
  have sourceBridge : 9 * k + 8 + 1 + (3 * shear + 2) =
      9 * k + 11 + 3 * shear := by omega
  have shortBridge : 12 * k + 11 + 2 * shear + 1 + 1 =
      separation + 1 + (3 * k + 2 + (3 * shear + 2)) := by omega
  have middleBridge : 12 * k + 14 + 3 * shear =
      separation + 1 + (3 * k + 3 + shear + (3 * shear + 2)) := by omega
  have finalBridge : 12 * k + 13 + 2 * shear =
      separation + 1 + (3 * k + 2 + (3 * shear + 2)) := by omega
  rw [middle_eq, shortRun, longRun, sourceBridge, shortBridge, middleBridge, finalBridge]

private theorem shearedEightFinal_clean (shear separation k : Nat)
    (shear_phase : shear % 3 ≠ 2) :
    Undecidability.ConstantAtMultiples 3 TagLetter.b
      (shearedEightFinal shear separation k) := by
  have clean : ConstantAtOffset 0
      (bRun (12 * k + 11 + 2 * shear) ++ .c ::
        (bRun (9 * k + 8) ++ .c ::
          (bRun (12 * k + 14 + 3 * shear) ++ .c ::
            (bRun (9 * k + 8) ++ .c ::
              (bRun (12 * k + 13 + 2 * shear) ++ .c ::
                (bRun (9 * k + 8) ++ .c :: bRun (separation + 1))))))) := by
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
              · exact constantAtOffset_replicate _ _
  simpa [shearedEightFinal, List.append_assoc, ConstantAtOffset,
    Undecidability.ConstantAtMultiples] using clean

private theorem tagHaltsFrom_of_history_equation (output : TagLetter → List TagLetter)
    (history : List (Stroke TagLetter 3)) (source target : List TagLetter)
    (target_halts : TagHaltsFrom 3 output target)
    (equation : consumed history ++ target = source ++ produced output history) :
    TagHaltsFrom 3 output source := by
  obtain ⟨suffix, short, short_length, suffix_eq⟩ :=
    history_of_tagHaltsFrom output target_halts
  apply tagHaltsFrom_of_history output (history ++ suffix) source short short_length
  rw [shear_consumed_append, shear_produced_append]
  simp only [List.append_assoc]
  calc
    consumed history ++ (consumed suffix ++ short) =
        consumed history ++ (target ++ produced output suffix) := by rw [suffix_eq]
    _ = (consumed history ++ target) ++ produced output suffix := by
      simp [List.append_assoc]
    _ = (source ++ produced output history) ++ produced output suffix := by rw [equation]
    _ = source ++ (produced output history ++ produced output suffix) := by
      simp [List.append_assoc]

/-- Every sheared source with middle run `8 mod 9` and shear off phase two halts. -/
theorem shearedEight_tagHaltsFrom (shear separation k : Nat)
    (middle_eq : separation + shear = 9 * k + 8)
    (shear_phase : shear % 3 ≠ 2) :
    TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
      (shearedInitial shear separation) := by
  have final_halts := Undecidability.tagHaltsFrom_of_constantAtMultiples 3 (by omega)
    (tagOutput (shearedBody shear separation)) TagLetter.b rfl
    (shearedEightFinal shear separation k)
    (shearedEightFinal_clean shear separation k shear_phase)
  have entry_halts : TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
      (shearedEntryQueue shear separation) :=
    tagHaltsFrom_of_history_equation (tagOutput (shearedBody shear separation))
      (shearedEightHistory shear k) (shearedEntryQueue shear separation)
      (shearedEightFinal shear separation k) final_halts
      (shearedEightHistory_equation shear separation k middle_eq)
  exact Undecidability.tagHaltsFrom_of_reaches
    (shearedInitial_reaches_entry shear separation).toReaches entry_halts

private def shearedTwentySixTailHistory (phase k v : Nat) : List (Stroke TagLetter 3) :=
  List.replicate (12 * k + 13 + 6 * v + 2 * phase) strokeBBB ++ [strokeCBB] ++
    List.replicate (9 * k + 8) strokeBBB ++ [strokeCBB] ++
      List.replicate (12 * k + 14 + 9 * v + 3 * phase) strokeBBB ++ [strokeCBB] ++
        List.replicate (9 * k + 8) strokeBBB ++ [strokeCBB] ++
          List.replicate (12 * k + 13 + 6 * v + 2 * phase) strokeBBB ++ [strokeCBB] ++
            List.replicate (9 * k + 8) strokeBBB ++ [strokeCBB]

private def shearedTwentySixFinal (phase separation k v : Nat) : List TagLetter :=
  bRun (39 * k + 44 + 24 * v + 8 * phase) ++ [.c] ++ bRun (27 * k + 26) ++ [.c] ++
    bRun (36 * k + 41 + 18 * v + 6 * phase) ++ [.c] ++ bRun (27 * k + 26) ++ [.c] ++
      bRun (39 * k + 47 + 27 * v + 9 * phase) ++ [.c] ++ bRun (27 * k + 26) ++ [.c] ++
        bRun (36 * k + 41 + 18 * v + 6 * phase) ++ [.c] ++ bRun (27 * k + 26) ++ [.c] ++
          bRun (39 * k + 46 + 24 * v + 8 * phase) ++ [.c] ++ bRun (27 * k + 26) ++ [.c] ++
            bRun (36 * k + 41 + 18 * v + 6 * phase) ++ [.c] ++ bRun (27 * k + 26) ++ [.c] ++
              bRun (separation + 1)

private def shearedTwentySixProduced (phase shear separation k v : Nat) : List TagLetter :=
  bRun (12 * k + 13 + 6 * v + 2 * phase) ++
    tagOutput (shearedBody shear separation) .c ++ bRun (9 * k + 8) ++
      tagOutput (shearedBody shear separation) .c ++
        bRun (12 * k + 14 + 9 * v + 3 * phase) ++
          tagOutput (shearedBody shear separation) .c ++ bRun (9 * k + 8) ++
            tagOutput (shearedBody shear separation) .c ++
              bRun (12 * k + 13 + 6 * v + 2 * phase) ++
                tagOutput (shearedBody shear separation) .c ++ bRun (9 * k + 8) ++
                  tagOutput (shearedBody shear separation) .c

private theorem shearedTwentySixTailHistory_produced (phase shear separation k v : Nat) :
    produced (tagOutput (shearedBody shear separation))
        (shearedTwentySixTailHistory phase k v) =
      shearedTwentySixProduced phase shear separation k v := by
  simp [shearedTwentySixTailHistory, shearedTwentySixProduced, strokeCBB, stroke₃, bRun,
    List.append_assoc]

private theorem shearedEightFinal_reaches_twentySixFinal (phase shear separation k v : Nat)
    (phase_lt : phase < 2)
    (shear_eq : shear = 9 * v + 3 * phase + 2)
    (middle_eq : separation + shear = 27 * k + 26) :
    TagReaches 3 (tagOutput (shearedBody shear separation))
      (shearedEightFinal shear separation (3 * k + 2))
      (shearedTwentySixFinal phase separation k v) := by
  have reach := Undecidability.tagReaches_history (tagOutput (shearedBody shear separation))
    (shearedTwentySixTailHistory phase k v) (bRun (separation - 1))
  have source_eq :
      consumed (shearedTwentySixTailHistory phase k v) ++ bRun (separation - 1) =
        shearedEightFinal shear separation (3 * k + 2) := by
    have firstRun : 3 * (12 * k + 13 + 6 * v + 2 * phase) =
        12 * (3 * k + 2) + 11 + 2 * shear := by omega
    have shortRun : 3 * (9 * k + 8) + 2 = 9 * (3 * k + 2) + 8 := by omega
    have longRun : 3 * (12 * k + 14 + 9 * v + 3 * phase) + 2 =
        12 * (3 * k + 2) + 14 + 3 * shear := by omega
    have tailRun : separation - 1 + 2 = separation + 1 := by omega
    simp [shearedTwentySixTailHistory, shearedEightFinal, strokeCBB, stroke₃,
      Stroke.letters, bRun, List.append_assoc, firstRun, shortRun, longRun, tailRun]
    omega
  have target_eq :
      bRun (separation - 1) ++
          produced (tagOutput (shearedBody shear separation))
            (shearedTwentySixTailHistory phase k v) =
        shearedTwentySixFinal phase separation k v := by
    have initialRun : separation - 1 + (12 * k + 13 + 6 * v + 2 * phase) +
        (3 * shear + 2) = 39 * k + 44 + 24 * v + 8 * phase := by omega
    have shortBridge : separation + 1 + (9 * k + 8) + (3 * shear + 2) =
        36 * k + 41 + 18 * v + 6 * phase := by omega
    have longBridge :
        separation + 1 + ((12 * k + 14 + 9 * v + 3 * phase) + (3 * shear + 2)) =
          39 * k + 47 + 27 * v + 9 * phase := by omega
    have lastBridge : separation + 1 +
        ((12 * k + 13 + 6 * v + 2 * phase) + (3 * shear + 2)) =
          39 * k + 46 + 24 * v + 8 * phase := by omega
    rw [shearedTwentySixTailHistory_produced]
    unfold shearedTwentySixProduced shearedTwentySixFinal
    simp only [List.append_assoc]
    rw [shearedOutput_initialBridge]
    repeat rw [shearedOutput_bridge]
    simp [shearedOutput_c, bRun, List.append_assoc, initialRun, shortBridge, longBridge,
      lastBridge, middle_eq]
  rw [source_eq, target_eq] at reach
  exact reach

private theorem shearedTwentySixFinal_clean (phase separation k v : Nat)
    (phase_lt : phase < 2) :
    Undecidability.ConstantAtMultiples 3 TagLetter.b
      (shearedTwentySixFinal phase separation k v) := by
  have clean : ConstantAtOffset 0 (shearedTwentySixFinal phase separation k v) := by
    unfold shearedTwentySixFinal
    simp only [List.singleton_append, List.append_assoc]
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
  simpa [ConstantAtOffset, Undecidability.ConstantAtMultiples] using clean

/-- The shear-two residue-eight survivor halts when its middle run is `26 mod 27` and its
shear is `2` or `5 mod 9`. -/
theorem shearedTwentySix_tagHaltsFrom (phase shear separation k v : Nat)
    (phase_lt : phase < 2)
    (shear_eq : shear = 9 * v + 3 * phase + 2)
    (middle_eq : separation + shear = 27 * k + 26) :
    TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
      (shearedInitial shear separation) := by
  have final_halts := Undecidability.tagHaltsFrom_of_constantAtMultiples 3 (by omega)
    (tagOutput (shearedBody shear separation)) TagLetter.b rfl
    (shearedTwentySixFinal phase separation k v)
    (shearedTwentySixFinal_clean phase separation k v phase_lt)
  have residue_halts : TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
      (shearedEightFinal shear separation (3 * k + 2)) :=
    Undecidability.tagHaltsFrom_of_reaches
      (shearedEightFinal_reaches_twentySixFinal phase shear separation k v phase_lt shear_eq
        middle_eq)
      final_halts
  have entry_halts : TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
      (shearedEntryQueue shear separation) :=
    tagHaltsFrom_of_history_equation (tagOutput (shearedBody shear separation))
      (shearedEightHistory shear (3 * k + 2)) (shearedEntryQueue shear separation)
      (shearedEightFinal shear separation (3 * k + 2)) residue_halts
      (shearedEightHistory_equation shear separation (3 * k + 2) (by omega))
  exact Undecidability.tagHaltsFrom_of_reaches
    (shearedInitial_reaches_entry shear separation).toReaches entry_halts

private def shearedMatchedHistory (phase k u : Nat) : List (Stroke TagLetter 3) :=
  [strokeCBB] ++ List.replicate (3 * k + phase) strokeBBB ++ [strokeCBB] ++
    List.replicate (3 * k + 3 * u + 2 * phase + 1) strokeBBB ++ [strokeCBB] ++
      List.replicate (3 * k + phase) strokeBBB ++ [strokeCBB] ++
        List.replicate (4 * k + 2 * u + 2 * phase + 1) strokeBBB ++ [strokeCBB] ++
          List.replicate (3 * k + phase) strokeBBB ++ [strokeCBB]

private def shearedMatchedFinal (phase separation k u : Nat) : List TagLetter :=
  bRun (12 * k + 9 * u + 7 * phase + 4) ++ [.c] ++
    bRun (9 * k + 3 * phase + 2) ++ [.c] ++
      bRun (12 * k + 6 * u + 6 * phase + 5) ++ [.c] ++
        bRun (9 * k + 3 * phase + 2) ++ [.c] ++
          bRun (13 * k + 8 * u + 7 * phase + 6) ++ [.c] ++
            bRun (9 * k + 3 * phase + 2) ++ [.c] ++
              bRun (12 * k + 6 * u + 6 * phase + 5) ++ [.c] ++
                bRun (9 * k + 3 * phase + 2) ++ [.c] ++ bRun (separation + 1)

private theorem shearedMatchedHistory_equation (phase shear separation k u : Nat)
    (shear_eq : shear = 3 * u + phase)
    (middle_eq : separation + shear = 9 * k + 3 * phase + 2) :
    consumed (shearedMatchedHistory phase k u) ++
        shearedMatchedFinal phase separation k u =
      shearedEntryQueue shear separation ++
        produced (tagOutput (shearedBody shear separation))
          (shearedMatchedHistory phase k u) := by
  simp [shearedMatchedHistory, shearedMatchedFinal, shearedEntryQueue, shearedBody, twoCBody,
    strokeCBB, stroke₃, Stroke.letters, tagOutput, nearyBody, bRun, List.append_assoc]
  have middleRun : 3 * (3 * k + phase) + 2 = 9 * k + 3 * phase + 2 := by omega
  have firstBridge : 3 * (3 * k + 3 * u + 2 * phase + 1) + 2 =
      9 * k + 3 * phase + 2 + 1 + (3 * shear + 2) := by omega
  have matchedBridge : 3 * (4 * k + 2 * u + 2 * phase + 1) + 2 =
      separation + 1 + (3 * k + phase + (3 * shear + 2)) := by omega
  have firstFinalBridge : 12 * k + 9 * u + 7 * phase + 4 + 2 =
      separation + 1 +
        (3 * k + 3 * u + 2 * phase + 1 + (3 * shear + 2)) := by omega
  have repeatedFinalBridge : 12 * k + 6 * u + 6 * phase + 5 =
      separation + 1 + (3 * k + phase + (3 * shear + 2)) := by omega
  have highFinalBridge : 13 * k + 8 * u + 7 * phase + 6 =
      separation + 1 +
        (4 * k + 2 * u + 2 * phase + 1 + (3 * shear + 2)) := by omega
  rw [middle_eq, middleRun, firstBridge, matchedBridge, firstFinalBridge,
    repeatedFinalBridge, highFinalBridge]

private theorem shearedMatchedFinal_clean (phase separation k u : Nat)
    (phase_lt : phase < 2)
    (joint_phase : (k + 2 * u + 2 * phase + 2) % 3 ≠ 0) :
    Undecidability.ConstantAtMultiples 3 TagLetter.b
      (shearedMatchedFinal phase separation k u) := by
  have clean : ConstantAtOffset 0 (shearedMatchedFinal phase separation k u) := by
    unfold shearedMatchedFinal
    simp only [List.singleton_append, List.append_assoc]
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
  simpa [ConstantAtOffset, Undecidability.ConstantAtMultiples] using clean

/-- The matched six-active-`c` history drains two joint phases of middle residues two and
five modulo nine. -/
theorem shearedMatched_tagHaltsFrom (phase shear separation k u : Nat)
    (phase_lt : phase < 2)
    (shear_eq : shear = 3 * u + phase)
    (middle_eq : separation + shear = 9 * k + 3 * phase + 2)
    (joint_phase : (k + 2 * u + 2 * phase + 2) % 3 ≠ 0) :
    TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
      (shearedInitial shear separation) := by
  have final_halts := Undecidability.tagHaltsFrom_of_constantAtMultiples 3 (by omega)
    (tagOutput (shearedBody shear separation)) TagLetter.b rfl
    (shearedMatchedFinal phase separation k u)
    (shearedMatchedFinal_clean phase separation k u phase_lt joint_phase)
  have entry_halts : TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
      (shearedEntryQueue shear separation) :=
    tagHaltsFrom_of_history_equation (tagOutput (shearedBody shear separation))
      (shearedMatchedHistory phase k u) (shearedEntryQueue shear separation)
      (shearedMatchedFinal phase separation k u) final_halts
      (shearedMatchedHistory_equation phase shear separation k u shear_eq middle_eq)
  exact Undecidability.tagHaltsFrom_of_reaches
    (shearedInitial_reaches_entry shear separation).toReaches entry_halts

private def shearedCrossStroke (phase : Nat) : Stroke TagLetter 3 :=
  if phase = 0 then strokeBBC else strokeBCB

private def shearedOppositeCrossStroke (phase : Nat) : Stroke TagLetter 3 :=
  if phase = 0 then strokeBCB else strokeBBC

private def shearedComplementaryHistory (phase k u : Nat) : List (Stroke TagLetter 3) :=
  [strokeCBB] ++ List.replicate (3 * k + phase) strokeBBB ++ [strokeCBB] ++
    List.replicate (3 * k + 3 * u + 2) strokeBBB ++ [strokeCBB] ++
      List.replicate (3 * k + phase) strokeBBB ++ [strokeCBB] ++
        List.replicate (4 * k + 2 * u + phase + 1) strokeBBB ++
          [shearedCrossStroke phase] ++ List.replicate (3 * k + phase) strokeBBB ++
            [shearedCrossStroke phase] ++ List.replicate (4 * k + 3 * u + 3) strokeBBB ++
              [strokeCBB] ++ List.replicate (3 * k + phase) strokeBBB ++ [strokeCBB]

private def shearedComplementaryFinal
    (phase separation k u : Nat) : List TagLetter :=
  bRun (12 * k + 6 * u + 2 * phase + 5) ++ [.c] ++
    bRun (9 * k + 3 * phase + 2) ++ [.c] ++
      bRun (20 * k + 11 * u + 3 * phase + 13) ++ [.c] ++
        bRun (9 * k + 3 * phase + 2) ++ [.c] ++
          bRun (12 * k + 6 * u + 2 * phase + 7) ++ [.c] ++
            bRun (9 * k + 3 * phase + 2) ++ [.c] ++ bRun (separation + 1)

private theorem shearedComplementaryHistory_equation
    (phase shear separation k u : Nat)
    (phase_lt : phase < 2)
    (shear_eq : shear + phase = 3 * u + 1)
    (middle_eq : separation + shear = 9 * k + 3 * phase + 2) :
    consumed (shearedComplementaryHistory phase k u) ++
        shearedComplementaryFinal phase separation k u =
      shearedEntryQueue shear separation ++
        produced (tagOutput (shearedBody shear separation))
          (shearedComplementaryHistory phase k u) := by
  have phase_cases : phase = 0 ∨ phase = 1 := by omega
  rcases phase_cases with rfl | rfl
  · simp [shearedComplementaryHistory, shearedComplementaryFinal, shearedCrossStroke,
      shearedEntryQueue, shearedBody, twoCBody, strokeBBC, strokeCBB, stroke₃,
      Stroke.letters, tagOutput, nearyBody, bRun, List.append_assoc] at shear_eq middle_eq ⊢
    have middleRun : 3 * (3 * k) + 1 + 1 = 9 * k + 2 := by omega
    have sourceBridge : 3 * (3 * k + 3 * u + 2) + 1 + 1 =
        9 * k + 2 + 1 + (3 * shear + 2) := by omega
    have firstCrossBridge : 3 * (4 * k + 2 * u + 1) + 1 + 1 + 1 + 1 =
        separation + 1 + (3 * k + (3 * shear + 2)) := by omega
    have secondCrossBridge : 3 * (4 * k + 3 * u + 3) =
        separation + 1 + (3 * k + 3 * u + 2 + (3 * shear + 2)) := by omega
    have finalBridge : 12 * k + 6 * u + 5 + 1 + 1 =
        separation + 1 + (3 * k + (3 * shear + 2)) := by omega
    have highFinalBridge : 20 * k + 11 * u + 13 =
        separation + 1 +
          (4 * k + 2 * u + 1 +
            (3 * k + (4 * k + 3 * u + 3 + (3 * shear + 2) + 1) + 1)) := by
      omega
    rw [middle_eq, middleRun, sourceBridge, firstCrossBridge, secondCrossBridge, finalBridge,
      highFinalBridge]
  · simp [shearedComplementaryHistory, shearedComplementaryFinal, shearedCrossStroke,
      shearedEntryQueue, shearedBody, twoCBody, strokeBCB, strokeCBB, stroke₃,
      Stroke.letters, tagOutput, nearyBody, bRun, List.append_assoc] at shear_eq middle_eq ⊢
    have middleRun : 3 * (3 * k + 1) + 1 + 1 = 9 * k + 5 := by omega
    have middlePhase : 9 * k + 3 + 2 = 9 * k + 5 := by omega
    have sourceBridge : 3 * (3 * k + 3 * u + 2) + 1 + 1 =
        9 * k + 5 + 1 + (3 * shear + 2) := by omega
    have firstCrossBridge : 3 * (4 * k + 2 * u + 2) + 1 + 1 + 1 =
        separation + 1 + (3 * k + 1 + (3 * shear + 2)) := by omega
    have secondCrossBridge : 3 * (4 * k + 3 * u + 3) + 1 =
        separation + 1 + (3 * k + 3 * u + 2 + (3 * shear + 2)) := by omega
    have finalBridge : 12 * k + 6 * u + 7 + 1 + 1 =
        separation + 1 + (3 * k + 1 + (3 * shear + 2)) := by omega
    have highFinalBridge : 20 * k + 11 * u + 16 =
        separation + 1 +
          (4 * k + 2 * u + 1 + 1 +
            (3 * k + 1 + (4 * k + 3 * u + 3 + (3 * shear + 2) + 1) + 1)) := by
      omega
    rw [middle_eq, middleRun, middlePhase, sourceBridge, firstCrossBridge, secondCrossBridge,
      finalBridge, highFinalBridge]

private theorem shearedComplementaryFinal_clean (phase separation k u : Nat)
    (phase_lt : phase < 2)
    (joint_phase : (k + u) % 3 = 2) :
    Undecidability.ConstantAtMultiples 3 TagLetter.b
      (shearedComplementaryFinal phase separation k u) := by
  have clean : ConstantAtOffset 0 (shearedComplementaryFinal phase separation k u) := by
    unfold shearedComplementaryFinal
    simp only [List.singleton_append, List.append_assoc]
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
              · exact constantAtOffset_replicate _ _
  simpa [ConstantAtOffset, Undecidability.ConstantAtMultiples] using clean

/-- The six-active-`c` history drains the complementary middle/shear phase when the joint
quotient is two modulo three. -/
theorem shearedComplementary_tagHaltsFrom (phase shear separation k u : Nat)
    (phase_lt : phase < 2)
    (shear_eq : shear + phase = 3 * u + 1)
    (middle_eq : separation + shear = 9 * k + 3 * phase + 2)
    (joint_phase : (k + u) % 3 = 2) :
    TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
      (shearedInitial shear separation) := by
  have final_halts := Undecidability.tagHaltsFrom_of_constantAtMultiples 3 (by omega)
    (tagOutput (shearedBody shear separation)) TagLetter.b rfl
    (shearedComplementaryFinal phase separation k u)
    (shearedComplementaryFinal_clean phase separation k u phase_lt joint_phase)
  have entry_halts : TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
      (shearedEntryQueue shear separation) :=
    tagHaltsFrom_of_history_equation (tagOutput (shearedBody shear separation))
      (shearedComplementaryHistory phase k u) (shearedEntryQueue shear separation)
      (shearedComplementaryFinal phase separation k u) final_halts
      (shearedComplementaryHistory_equation phase shear separation k u phase_lt shear_eq
        middle_eq)
  exact Undecidability.tagHaltsFrom_of_reaches
    (shearedInitial_reaches_entry shear separation).toReaches entry_halts

private def shearedShearResidueTwoHistory
    (phase k u : Nat) : List (Stroke TagLetter 3) :=
  [strokeCBB] ++ List.replicate (3 * k + phase) strokeBBB ++ [strokeCBB] ++
    List.replicate (3 * k + 3 * u + phase + 3) strokeBBB ++ [strokeCBB] ++
      List.replicate (3 * k + phase) strokeBBB ++ [strokeCBB] ++
        List.replicate (4 * k + 2 * u + phase + 2) strokeBBB ++
          [shearedOppositeCrossStroke phase] ++
            List.replicate (3 * k + phase) strokeBBB ++
              [shearedOppositeCrossStroke phase] ++
                List.replicate (4 * k + 3 * u + 2 * phase + 3) strokeBBB ++
                  [shearedCrossStroke phase] ++ List.replicate (3 * k + phase) strokeBBB ++
                    [shearedCrossStroke phase] ++
                      List.replicate (4 * k + 2 * u + phase + 3) strokeBBB ++
                        [strokeCBB] ++ List.replicate (3 * k + phase) strokeBBB ++ [strokeCBB]

private def shearedShearResidueTwoFinal
    (phase separation k u : Nat) : List TagLetter :=
  bRun (27 * k + 13 * u + 9 * phase + 19) ++ [.c] ++
    bRun (9 * k + 3 * phase + 2) ++ [.c] ++
      bRun (12 * k + 6 * u + 4 * phase + 9) ++ [.c] ++
        bRun (9 * k + 3 * phase + 2) ++ [.c] ++ bRun (separation + 1)

private theorem shearedShearResidueTwoHistory_equation
    (phase shear separation k u : Nat)
    (phase_lt : phase < 2)
    (shear_eq : shear = 3 * u + 2)
    (middle_eq : separation + shear = 9 * k + 3 * phase + 2) :
    consumed (shearedShearResidueTwoHistory phase k u) ++
        shearedShearResidueTwoFinal phase separation k u =
      shearedEntryQueue shear separation ++
        produced (tagOutput (shearedBody shear separation))
          (shearedShearResidueTwoHistory phase k u) := by
  have phase_cases : phase = 0 ∨ phase = 1 := by omega
  rcases phase_cases with rfl | rfl
  · simp [shearedShearResidueTwoHistory, shearedShearResidueTwoFinal,
      shearedCrossStroke, shearedOppositeCrossStroke, shearedEntryQueue, shearedBody,
      twoCBody, strokeBBC, strokeBCB, strokeCBB, stroke₃, Stroke.letters, tagOutput,
      nearyBody, bRun, List.append_assoc] at shear_eq middle_eq ⊢
    have middleRun : 3 * (3 * k) + 1 + 1 = 9 * k + 2 := by omega
    have sourceBridge : 3 * (3 * k + 3 * u + 3) + 1 + 1 =
        9 * k + 2 + 1 + (3 * shear + 2) := by omega
    have firstCrossBridge : 3 * (4 * k + 2 * u + 2) + 1 + 1 + 1 =
        separation + 1 + (3 * k + (3 * shear + 2)) := by omega
    have secondCrossBridge : 3 * (4 * k + 3 * u + 3) + 1 + 1 + 1 =
        separation + 1 + (3 * k + 3 * u + 3 + (3 * shear + 2)) := by omega
    have thirdCrossBridge : 3 * (4 * k + 2 * u + 3) =
        separation + 1 + (3 * k + (3 * shear + 2)) := by omega
    have highFinalBridge : 27 * k + 13 * u + 19 + 1 + 1 =
        separation + 1 +
          (4 * k + 2 * u + 2 +
            (3 * k +
              (4 * k + 3 * u + 3 +
                (3 * k + (4 * k + 2 * u + 3 + (3 * shear + 2) + 1) + 1) + 1) + 1)) := by
      omega
    have finalBridge : 12 * k + 6 * u + 9 =
        separation + 1 + (3 * k + (3 * shear + 2)) := by omega
    rw [middle_eq, middleRun, sourceBridge, firstCrossBridge, secondCrossBridge, thirdCrossBridge,
      highFinalBridge, finalBridge]
  · simp [shearedShearResidueTwoHistory, shearedShearResidueTwoFinal,
      shearedCrossStroke, shearedOppositeCrossStroke, shearedEntryQueue, shearedBody,
      twoCBody, strokeBBC, strokeBCB, strokeCBB, stroke₃, Stroke.letters, tagOutput,
      nearyBody, bRun, List.append_assoc] at shear_eq middle_eq ⊢
    have middleRun : 3 * (3 * k + 1) + 1 + 1 = 9 * k + 5 := by omega
    have middlePhase : 9 * k + 3 + 2 = 9 * k + 5 := by omega
    have sourceBridge : 3 * (3 * k + 3 * u + 4) + 1 + 1 =
        9 * k + 5 + 1 + (3 * shear + 2) := by omega
    have firstCrossBridge : 3 * (4 * k + 2 * u + 3) + 1 + 1 + 1 + 1 =
        separation + 1 + (3 * k + 1 + (3 * shear + 2)) := by omega
    have secondCrossBridge : 3 * (4 * k + 3 * u + 5) + 1 =
        separation + 1 + (3 * k + 3 * u + 1 + 3 + (3 * shear + 2)) := by omega
    have thirdCrossBridge : 3 * (4 * k + 2 * u + 4) + 1 =
        separation + 1 + (3 * k + 1 + (3 * shear + 2)) := by omega
    have highFinalBridge : 27 * k + 13 * u + 28 + 1 + 1 =
        separation + 1 +
          (4 * k + 2 * u + 1 + 2 +
            (3 * k + 1 +
              (4 * k + 3 * u + 2 + 3 +
                (3 * k + 1 +
                  (4 * k + 2 * u + 1 + 3 + (3 * shear + 2) + 1) + 1) + 1) + 1)) := by
      omega
    have finalBridge : 12 * k + 6 * u + 13 =
        separation + 1 + (3 * k + 1 + (3 * shear + 2)) := by omega
    rw [middle_eq, middleRun, middlePhase, sourceBridge, firstCrossBridge, secondCrossBridge,
      thirdCrossBridge, highFinalBridge, finalBridge]

private theorem shearedShearResidueTwoFinal_clean (phase separation k u : Nat)
    (phase_lt : phase < 2)
    (quotient_phase : u % 3 = phase) :
    Undecidability.ConstantAtMultiples 3 TagLetter.b
      (shearedShearResidueTwoFinal phase separation k u) := by
  have clean : ConstantAtOffset 0 (shearedShearResidueTwoFinal phase separation k u) := by
    unfold shearedShearResidueTwoFinal
    simp only [List.singleton_append, List.append_assoc]
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
  simpa [ConstantAtOffset, Undecidability.ConstantAtMultiples] using clean

/-- The six-active-`c` history drains the shear-residue-two mismatch when its shear quotient
matches the middle quotient phase. -/
theorem shearedShearResidueTwo_tagHaltsFrom (phase shear separation k u : Nat)
    (phase_lt : phase < 2)
    (shear_eq : shear = 3 * u + 2)
    (middle_eq : separation + shear = 9 * k + 3 * phase + 2)
    (quotient_phase : u % 3 = phase) :
    TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
      (shearedInitial shear separation) := by
  have final_halts := Undecidability.tagHaltsFrom_of_constantAtMultiples 3 (by omega)
    (tagOutput (shearedBody shear separation)) TagLetter.b rfl
    (shearedShearResidueTwoFinal phase separation k u)
    (shearedShearResidueTwoFinal_clean phase separation k u phase_lt quotient_phase)
  have entry_halts : TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
      (shearedEntryQueue shear separation) :=
    tagHaltsFrom_of_history_equation (tagOutput (shearedBody shear separation))
      (shearedShearResidueTwoHistory phase k u) (shearedEntryQueue shear separation)
      (shearedShearResidueTwoFinal phase separation k u) final_halts
      (shearedShearResidueTwoHistory_equation phase shear separation k u phase_lt shear_eq
        middle_eq)
  exact Undecidability.tagHaltsFrom_of_reaches
    (shearedInitial_reaches_entry shear separation).toReaches entry_halts

end MatrixMortality.SeparatedTwoCShear
