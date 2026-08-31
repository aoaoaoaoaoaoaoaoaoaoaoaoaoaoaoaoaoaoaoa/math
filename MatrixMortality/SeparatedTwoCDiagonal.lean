import MatrixMortality.SeparatedTwoCResidueTwo

/-!
# Complete diagonal separated-two-c drainage

The remaining diagonal queues normalize to one or two copies of the canonical four-`c` block.
After centering the final unary tail, their macro dynamics is division by three with a possible
translation by one fixed span. The live states occupy a finite open interval, and the transition
map has at most one predecessor there. Its initial negative one-block state has no predecessor,
so the macro orbit must terminate.
-/

namespace MatrixMortality.SeparatedTwoCDiagonal

open PeriodicHistory SeparatedTwoCOrbit SeparatedTwoCResidue Undecidability

/-- Whether the normalized queue has one canonical block or two. -/
inductive FourCMode
  | one
  | pair
  deriving DecidableEq

instance : Fintype FourCMode where
  elems := {.one, .pair}
  complete := by
    intro mode
    cases mode with
    | one => simp
    | pair => simp

/-- A normalized block population together with its centered unary-tail coordinate. -/
abbrev FourCCenteredState := FourCMode × Int

/-- The centered inverse-ternary macro. Its missing residue in either mode is the halting case. -/
inductive FourCCenteredStep (span : Int) :
    FourCCenteredState → FourCCenteredState → Prop
  | oneIdle (next : Int) :
      FourCCenteredStep span (.one, next) (.one, 3 * next)
  | oneCross (next : Int) :
      FourCCenteredStep span (.pair, next) (.one, 3 * next + span)
  | pairIdle (next : Int) :
      FourCCenteredStep span (.pair, next) (.pair, 3 * next)
  | pairCross (next : Int) :
      FourCCenteredStep span (.one, next) (.pair, 3 * next - span)

private def insideSpan (span : Int) (state : FourCCenteredState) : Prop :=
  -span < 2 * state.2 ∧ 2 * state.2 < span

private instance insideSpan_decidable (span : Int) : DecidablePred (insideSpan span) := by
  intro state
  unfold insideSpan
  infer_instance

private noncomputable def centeredCage (span : Int) : Finset FourCCenteredState :=
  (Finset.univ.product (Finset.Icc (-span) span)).filter (insideSpan span)

private theorem mem_centeredCage {span : Int} {state : FourCCenteredState} :
    state ∈ centeredCage span ↔ insideSpan span state := by
  constructor
  · intro state_mem
    exact (Finset.mem_filter.mp state_mem).2
  · intro state_inside
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩,
      state_inside⟩
    · simp [insideSpan] at state_inside
      omega
    · simp [insideSpan] at state_inside
      omega

private theorem centeredStep_inside {span : Int} (span_pos : 0 < span)
    {next current : FourCCenteredState} (current_inside : insideSpan span current)
    (step : FourCCenteredStep span next current) : insideSpan span next := by
  cases step with
  | oneIdle next =>
      simp only [insideSpan] at current_inside ⊢
      omega
  | oneCross next =>
      simp only [insideSpan] at current_inside ⊢
      omega
  | pairIdle next =>
      simp only [insideSpan] at current_inside ⊢
      omega
  | pairCross next =>
      simp only [insideSpan] at current_inside ⊢
      omega

private theorem centeredStep_predecessor_unique {span : Int}
    {next left right : FourCCenteredState}
    (left_inside : insideSpan span left) (right_inside : insideSpan span right)
    (left_step : FourCCenteredStep span next left)
    (right_step : FourCCenteredStep span next right) : left = right := by
  cases left_step <;> cases right_step <;>
    simp only [insideSpan, Prod.mk.injEq] at left_inside right_inside ⊢ <;> omega

private theorem acc_of_finite_injective_root {α : Type*} [DecidableEq α]
    (relation : α → α → Prop) (cage : Finset α) (root : α)
    (root_mem : root ∈ cage)
    (closed : ∀ {current next}, current ∈ cage → relation next current → next ∈ cage)
    (predecessor_unique : ∀ {next left right}, left ∈ cage → right ∈ cage →
      relation next left → relation next right → left = right)
    (root_free : ∀ current, current ∈ cage → ¬relation root current) :
    Acc relation root := by
  refine ⟨root, ?_⟩
  intro next step
  have next_mem : next ∈ cage := closed root_mem step
  apply acc_of_finite_injective_root relation (cage.erase root) next
  · exact Finset.mem_erase.mpr ⟨by
      intro next_eq
      subst next
      exact root_free root root_mem step, next_mem⟩
  · intro current target current_mem edge
    have current_mem' : current ∈ cage := Finset.mem_of_mem_erase current_mem
    have target_mem : target ∈ cage := closed current_mem' edge
    have target_ne : target ≠ root := by
      intro target_eq
      subst target
      exact root_free current current_mem' edge
    exact Finset.mem_erase.mpr ⟨target_ne, target_mem⟩
  · intro target left right left_mem right_mem left_edge right_edge
    exact predecessor_unique (Finset.mem_of_mem_erase left_mem)
      (Finset.mem_of_mem_erase right_mem) left_edge right_edge
  · intro current current_mem edge
    have current_mem' : current ∈ cage := Finset.mem_of_mem_erase current_mem
    have current_eq := predecessor_unique current_mem' root_mem edge step
    exact (Finset.mem_erase.mp current_mem).1 current_eq
termination_by cage.card
decreasing_by exact Finset.card_erase_lt_of_mem root_mem

/-- The fixed translation span in the centered four-`c` macro. -/
def fourCSpan (a : Nat) : Int := 129 * (a : Int) + 62

/-- The centered defect of the first canonical block queue. -/
def fourCInitialDefect (a : Nat) : Int := -(23 * (a : Int) + 11)

/-- The centered two-mode macro is accessible from every diagonal initial defect. -/
theorem fourCCentered_initial_accessible (a : Nat) :
    Acc (FourCCenteredStep (fourCSpan a)) (.one, fourCInitialDefect a) := by
  have span_pos : 0 < fourCSpan a := by
    simp [fourCSpan]
    omega
  apply acc_of_finite_injective_root (FourCCenteredStep (fourCSpan a))
    (centeredCage (fourCSpan a)) (.one, fourCInitialDefect a)
  · rw [mem_centeredCage]
    simp [insideSpan, fourCSpan, fourCInitialDefect]
    omega
  · intro current next current_mem step
    rw [mem_centeredCage] at current_mem ⊢
    exact centeredStep_inside span_pos current_mem step
  · intro next left right left_mem right_mem left_step right_step
    rw [mem_centeredCage] at left_mem right_mem
    exact centeredStep_predecessor_unique left_mem right_mem left_step right_step
  · intro current current_mem step
    rw [mem_centeredCage] at current_mem
    cases step with
    | oneIdle next =>
        simp only [insideSpan, fourCSpan, fourCInitialDefect] at current_mem ⊢
        omega
    | pairCross next =>
        simp only [insideSpan, fourCSpan, fourCInitialDefect] at current_mem ⊢
        omega

private def blockParameter (a : Nat) : Nat := 9 * a + 4

private def blockMiddle (a : Nat) : Nat := 12 * a + 5

private def blockBridge (a : Nat) : Nat := 39 * a + 19

private def blockRemainder (a : Nat) : Nat := 27 * a + 12

private def blockSpan (a : Nat) : Nat := 129 * a + 62

private def blockCenter (a : Nat) : Nat := 105 * a + 49

/-- The normalized queue containing one canonical four-`c` block. -/
def oneBlockQueue (a tail : Nat) : List TagLetter :=
  fourCQueue (blockParameter a) tail

/-- The normalized queue containing two canonical blocks with the fixed bridge between them. -/
def twoBlockQueue (a tail : Nat) : List TagLetter :=
  fourCBlock (blockParameter a) ++ bRun (blockBridge a) ++
    fourCBlock (blockParameter a) ++ bRun tail

private def oneBlockExpansion (a tail : Nat) : List TagLetter :=
  bRun tail ++ fourCBlock (blockParameter a) ++ bRun (blockBridge a) ++
    fourCBlock (blockParameter a) ++ bRun (blockRemainder a)

private def twoBlockExpansion (a tail : Nat) : List TagLetter :=
  bRun (blockBridge a - 2) ++ fourCBlock (blockParameter a) ++ bRun tail ++ bRun 2 ++
    fourCBlock (blockParameter a) ++ bRun (blockBridge a) ++
      fourCBlock (blockParameter a) ++ bRun (blockRemainder a)

private theorem oneBlockQueue_reaches_expansion (a tail : Nat) :
    TagReaches 3 (tagOutput (separatedBody (27 * a + 11)))
      (oneBlockQueue a tail) (oneBlockExpansion a tail) := by
  have reach := fourCQueue_reaches_final (blockParameter a) (blockMiddle a) tail
    (by simp [blockParameter]) (by simp [blockParameter, blockMiddle]; omega)
  have exponent_eq : 3 * blockParameter a - 1 = 27 * a + 11 := by
    simp [blockParameter]
    omega
  rw [exponent_eq] at reach
  have remainder_eq : 3 * blockParameter a = blockRemainder a := by
    simp [blockParameter, blockRemainder]
    omega
  have bridge_eq : blockRemainder a + blockMiddle a + 2 = blockBridge a := by
    simp [blockRemainder, blockMiddle, blockBridge]
    omega
  have bridge_core_eq : blockRemainder a + blockMiddle a = blockBridge a - 2 := by
    simp [blockRemainder, blockMiddle, blockBridge]
    omega
  have bridge_roundtrip : blockBridge a - 2 + 2 = blockBridge a := by
    simp [blockBridge]
  simpa [oneBlockQueue, oneBlockExpansion, fourCExpansion, fourCBlock,
    remainder_eq, bridge_eq, bridge_core_eq, bridge_roundtrip, List.append_assoc] using reach

private theorem twoBlockQueue_reaches_expansion (a tail : Nat) :
    TagReaches 3 (tagOutput (separatedBody (27 * a + 11)))
      (twoBlockQueue a tail) (twoBlockExpansion a tail) := by
  have reach := fourCBlock_bRun_reaches_final (blockParameter a) (blockMiddle a)
    (blockBridge a - 2) (fourCBlock (blockParameter a) ++ bRun tail)
    (by simp [blockParameter]) (by simp [blockParameter, blockMiddle]; omega)
  have bridge_eq : blockBridge a - 2 + 2 = blockBridge a := by
    simp [blockBridge]
  have exponent_eq : 3 * blockParameter a - 1 = 27 * a + 11 := by
    simp [blockParameter]
    omega
  rw [exponent_eq] at reach
  have remainder_eq : 3 * blockParameter a = blockRemainder a := by
    simp [blockParameter, blockRemainder]
    omega
  have fixed_bridge_eq : blockRemainder a + blockMiddle a + 2 = blockBridge a := by
    simp [blockRemainder, blockMiddle, blockBridge]
    omega
  have bridge_core_eq : blockRemainder a + blockMiddle a = blockBridge a - 2 := by
    simp [blockRemainder, blockMiddle, blockBridge]
    omega
  simpa [twoBlockQueue, twoBlockExpansion, bridge_eq, fixed_bridge_eq, bridge_core_eq,
    remainder_eq, List.append_assoc] using reach

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
  rw [take_eq] at reach
  simpa using reach

private theorem fourCBlock_length (a : Nat) :
    (fourCBlock (blockParameter a)).length = 90 * a + 43 := by
  simp [fourCBlock, blockParameter, bRun]
  omega

private theorem fourCBlock_clean (a offset : Nat) (inert : ¬3 ∣ offset) :
    ConstantAtOffset offset (fourCBlock (blockParameter a)) := by
  unfold fourCBlock blockParameter
  simp only [List.append_assoc, List.singleton_append]
  apply constantAtOffset_cons_c inert
  apply constantAtOffset_bRun_c
  · rw [Nat.dvd_iff_mod_eq_zero] at inert ⊢
    omega
  · apply constantAtOffset_bRun_c
    · rw [Nat.dvd_iff_mod_eq_zero] at inert ⊢
      omega
    · apply constantAtOffset_bRun_c
      · rw [Nat.dvd_iff_mod_eq_zero] at inert ⊢
        omega
      · simpa [bRun] using constantAtOffset_replicate
          (offset + 1 + (3 * (9 * a + 4) - 1) + 1 + (4 * (9 * a + 4) + 1) + 1 +
            (3 * (9 * a + 4) - 1) + 1) 0

private def oneIdlePrefix (a tail : Nat) : List TagLetter :=
  bRun tail ++ fourCBlock (blockParameter a) ++ bRun (blockBridge a)

private def twoIdlePrefix (a tail : Nat) : List TagLetter :=
  bRun (blockBridge a - 2) ++ fourCBlock (blockParameter a) ++ bRun tail ++ bRun 2

private def twoCrossPrefix (a tail : Nat) : List TagLetter :=
  twoIdlePrefix a tail ++ fourCBlock (blockParameter a) ++ bRun (blockBridge a)

private theorem oneIdlePrefix_length (a tail : Nat) :
    (oneIdlePrefix a tail).length = tail + blockSpan a := by
  simp [oneIdlePrefix, fourCBlock_length, blockBridge, blockSpan, bRun]
  omega

private theorem twoIdlePrefix_length (a tail : Nat) :
    (twoIdlePrefix a tail).length = tail + blockSpan a := by
  simp [twoIdlePrefix, fourCBlock_length, blockBridge, blockSpan, bRun]
  omega

private theorem twoCrossPrefix_length (a tail : Nat) :
    (twoCrossPrefix a tail).length = tail + 2 * blockSpan a := by
  simp [twoCrossPrefix, twoIdlePrefix_length, fourCBlock_length, blockBridge, blockSpan, bRun]
  omega

private theorem oneIdlePrefix_clean (a tail : Nat) (tail_mod : tail % 3 = 1) :
    ConstantAtMultiples 3 TagLetter.b (oneIdlePrefix a tail) := by
  have shifted : ConstantAtOffset 0 (oneIdlePrefix a tail) := by
    unfold oneIdlePrefix
    simp only [List.append_assoc]
    apply ConstantAtOffset.append (constantAtOffset_replicate 0 tail)
    apply ConstantAtOffset.append
    · apply fourCBlock_clean
      simp [bRun, Nat.dvd_iff_mod_eq_zero]
      omega
    · exact constantAtOffset_replicate _ _
  simpa [ConstantAtOffset, ConstantAtMultiples] using shifted

private theorem twoIdlePrefix_clean (a tail : Nat) :
    ConstantAtMultiples 3 TagLetter.b (twoIdlePrefix a tail) := by
  have shifted : ConstantAtOffset 0 (twoIdlePrefix a tail) := by
    unfold twoIdlePrefix
    simp only [List.append_assoc]
    apply ConstantAtOffset.append (constantAtOffset_replicate 0 (blockBridge a - 2))
    apply ConstantAtOffset.append
    · apply fourCBlock_clean
      simp [bRun, blockBridge, Nat.dvd_iff_mod_eq_zero]
      omega
    · apply ConstantAtOffset.append (constantAtOffset_replicate _ tail)
      exact constantAtOffset_replicate _ _
  simpa [ConstantAtOffset, ConstantAtMultiples] using shifted

private theorem twoCrossPrefix_clean (a tail : Nat) (tail_mod : tail % 3 = 2) :
    ConstantAtMultiples 3 TagLetter.b (twoCrossPrefix a tail) := by
  have shifted : ConstantAtOffset 0 (twoCrossPrefix a tail) := by
    unfold twoCrossPrefix
    simp only [List.append_assoc]
    apply ConstantAtOffset.append
    · simpa [ConstantAtOffset, ConstantAtMultiples] using twoIdlePrefix_clean a tail
    · apply ConstantAtOffset.append
      · apply fourCBlock_clean
        simp [twoIdlePrefix_length, blockSpan, Nat.dvd_iff_mod_eq_zero]
        omega
      · exact constantAtOffset_replicate _ _
  simpa [ConstantAtOffset, ConstantAtMultiples] using shifted

private theorem oneBlockExpansion_clean (a tail : Nat) (tail_mod : tail % 3 = 2) :
    ConstantAtMultiples 3 TagLetter.b (oneBlockExpansion a tail) := by
  have shifted : ConstantAtOffset 0 (oneBlockExpansion a tail) := by
    unfold oneBlockExpansion
    simp only [List.append_assoc]
    apply ConstantAtOffset.append (constantAtOffset_replicate 0 tail)
    apply ConstantAtOffset.append
    · apply fourCBlock_clean
      simp [bRun, Nat.dvd_iff_mod_eq_zero]
      omega
    · apply ConstantAtOffset.append (constantAtOffset_replicate _ (blockBridge a))
      apply ConstantAtOffset.append
      · apply fourCBlock_clean
        simp [bRun, fourCBlock_length, blockBridge, Nat.dvd_iff_mod_eq_zero]
        omega
      · exact constantAtOffset_replicate _ _
  simpa [ConstantAtOffset, ConstantAtMultiples] using shifted

private theorem twoBlockExpansion_clean (a tail : Nat) (tail_mod : tail % 3 = 0) :
    ConstantAtMultiples 3 TagLetter.b (twoBlockExpansion a tail) := by
  have shifted : ConstantAtOffset 0 (twoBlockExpansion a tail) := by
    unfold twoBlockExpansion
    simp only [List.append_assoc]
    apply ConstantAtOffset.append (constantAtOffset_replicate 0 (blockBridge a - 2))
    apply ConstantAtOffset.append
    · apply fourCBlock_clean
      simp [bRun, blockBridge, Nat.dvd_iff_mod_eq_zero]
      omega
    · apply ConstantAtOffset.append (constantAtOffset_replicate _ tail)
      apply ConstantAtOffset.append (constantAtOffset_replicate _ 2)
      apply ConstantAtOffset.append
      · apply fourCBlock_clean
        simp [bRun, fourCBlock_length, blockBridge, Nat.dvd_iff_mod_eq_zero]
        omega
      · apply ConstantAtOffset.append (constantAtOffset_replicate _ (blockBridge a))
        apply ConstantAtOffset.append
        · apply fourCBlock_clean
          simp [bRun, fourCBlock_length, blockBridge, Nat.dvd_iff_mod_eq_zero]
          omega
        · exact constantAtOffset_replicate _ _
  simpa [ConstantAtOffset, ConstantAtMultiples] using shifted

private theorem oneBlock_idle_reaches (a tail count : Nat)
    (count_eq : tail + blockSpan a = count * 3) :
    TagReaches 3 (tagOutput (separatedBody (27 * a + 11)))
      (oneBlockQueue a tail) (oneBlockQueue a (blockRemainder a + count)) := by
  have tail_mod : tail % 3 = 1 := by
    simp [blockSpan] at count_eq
    omega
  have front_length : (oneIdlePrefix a tail).length = count * 3 := by
    rw [oneIdlePrefix_length, count_eq]
  have drainage := cleanPrefix_reaches (separatedBody (27 * a + 11))
    (oneIdlePrefix a tail)
    (fourCBlock (blockParameter a) ++ bRun (blockRemainder a)) count front_length
    (oneIdlePrefix_clean a tail tail_mod)
  have source_eq :
      oneIdlePrefix a tail ++
          (fourCBlock (blockParameter a) ++ bRun (blockRemainder a)) =
        oneBlockExpansion a tail := by
    simp [oneIdlePrefix, oneBlockExpansion, List.append_assoc]
  have target_eq :
      (fourCBlock (blockParameter a) ++ bRun (blockRemainder a)) ++ bRun count =
        oneBlockQueue a (blockRemainder a + count) := by
    simp [oneBlockQueue, fourCQueue, bRun, List.append_assoc]
  rw [source_eq, target_eq] at drainage
  exact (oneBlockQueue_reaches_expansion a tail).trans drainage

private theorem oneBlock_cross_reaches (a tail count : Nat) (count_eq : tail = count * 3) :
    TagReaches 3 (tagOutput (separatedBody (27 * a + 11)))
      (oneBlockQueue a tail) (twoBlockQueue a (blockRemainder a + count)) := by
  have drainage := cleanPrefix_reaches (separatedBody (27 * a + 11)) (bRun tail)
    (fourCBlock (blockParameter a) ++ bRun (blockBridge a) ++
      fourCBlock (blockParameter a) ++ bRun (blockRemainder a)) count
    (by simp [bRun, count_eq]) (by
      simpa [ConstantAtOffset, ConstantAtMultiples] using constantAtOffset_replicate 0 tail)
  have source_eq :
      bRun tail ++ (fourCBlock (blockParameter a) ++ bRun (blockBridge a) ++
          fourCBlock (blockParameter a) ++ bRun (blockRemainder a)) =
        oneBlockExpansion a tail := by
    simp [oneBlockExpansion, List.append_assoc]
  have target_eq :
      (fourCBlock (blockParameter a) ++ bRun (blockBridge a) ++
          fourCBlock (blockParameter a) ++ bRun (blockRemainder a)) ++ bRun count =
        twoBlockQueue a (blockRemainder a + count) := by
    simp [twoBlockQueue, bRun, List.append_assoc]
  rw [source_eq, target_eq] at drainage
  exact (oneBlockQueue_reaches_expansion a tail).trans drainage

private theorem oneBlock_terminal (a tail : Nat) (tail_mod : tail % 3 = 2) :
    TagHaltsFrom 3 (tagOutput (separatedBody (27 * a + 11))) (oneBlockQueue a tail) := by
  have final_halts := tagHaltsFrom_of_constantAtMultiples 3 (by omega)
    (tagOutput (separatedBody (27 * a + 11))) TagLetter.b rfl
    (oneBlockExpansion a tail) (oneBlockExpansion_clean a tail tail_mod)
  exact tagHaltsFrom_of_reaches (oneBlockQueue_reaches_expansion a tail) final_halts

private theorem twoBlock_idle_reaches (a tail count : Nat)
    (count_eq : tail + blockSpan a = count * 3) :
    TagReaches 3 (tagOutput (separatedBody (27 * a + 11)))
      (twoBlockQueue a tail) (twoBlockQueue a (blockRemainder a + count)) := by
  have tail_mod : tail % 3 = 1 := by
    simp [blockSpan] at count_eq
    omega
  have front_length : (twoIdlePrefix a tail).length = count * 3 := by
    rw [twoIdlePrefix_length, count_eq]
  have drainage := cleanPrefix_reaches (separatedBody (27 * a + 11))
    (twoIdlePrefix a tail)
    (fourCBlock (blockParameter a) ++ bRun (blockBridge a) ++
      fourCBlock (blockParameter a) ++ bRun (blockRemainder a)) count front_length
    (twoIdlePrefix_clean a tail)
  have source_eq :
      twoIdlePrefix a tail ++ (fourCBlock (blockParameter a) ++ bRun (blockBridge a) ++
          fourCBlock (blockParameter a) ++ bRun (blockRemainder a)) =
        twoBlockExpansion a tail := by
    simp [twoIdlePrefix, twoBlockExpansion, List.append_assoc]
  have target_eq :
      (fourCBlock (blockParameter a) ++ bRun (blockBridge a) ++
          fourCBlock (blockParameter a) ++ bRun (blockRemainder a)) ++ bRun count =
        twoBlockQueue a (blockRemainder a + count) := by
    simp [twoBlockQueue, bRun, List.append_assoc]
  rw [source_eq, target_eq] at drainage
  exact (twoBlockQueue_reaches_expansion a tail).trans drainage

private theorem twoBlock_cross_reaches (a tail count : Nat)
    (count_eq : tail + 2 * blockSpan a = count * 3) :
    TagReaches 3 (tagOutput (separatedBody (27 * a + 11)))
      (twoBlockQueue a tail) (oneBlockQueue a (blockRemainder a + count)) := by
  have tail_mod : tail % 3 = 2 := by
    simp [blockSpan] at count_eq
    omega
  have front_length : (twoCrossPrefix a tail).length = count * 3 := by
    rw [twoCrossPrefix_length, count_eq]
  have drainage := cleanPrefix_reaches (separatedBody (27 * a + 11))
    (twoCrossPrefix a tail) (fourCBlock (blockParameter a) ++ bRun (blockRemainder a))
    count front_length (twoCrossPrefix_clean a tail tail_mod)
  have source_eq :
      twoCrossPrefix a tail ++
          (fourCBlock (blockParameter a) ++ bRun (blockRemainder a)) =
        twoBlockExpansion a tail := by
    simp [twoCrossPrefix, twoIdlePrefix, twoBlockExpansion, List.append_assoc]
  have target_eq :
      (fourCBlock (blockParameter a) ++ bRun (blockRemainder a)) ++ bRun count =
        oneBlockQueue a (blockRemainder a + count) := by
    simp [oneBlockQueue, fourCQueue, bRun, List.append_assoc]
  rw [source_eq, target_eq] at drainage
  exact (twoBlockQueue_reaches_expansion a tail).trans drainage

private theorem twoBlock_terminal (a tail : Nat) (tail_mod : tail % 3 = 0) :
    TagHaltsFrom 3 (tagOutput (separatedBody (27 * a + 11))) (twoBlockQueue a tail) := by
  have final_halts := tagHaltsFrom_of_constantAtMultiples 3 (by omega)
    (tagOutput (separatedBody (27 * a + 11))) TagLetter.b rfl
    (twoBlockExpansion a tail) (twoBlockExpansion_clean a tail tail_mod)
  exact tagHaltsFrom_of_reaches (twoBlockQueue_reaches_expansion a tail) final_halts

private def centeredTail (a : Nat) (defect : Int) : Nat :=
  Int.toNat ((blockCenter a : Int) + defect)

private def centeredCount (a : Nat) (nextDefect : Int) : Nat :=
  Int.toNat ((blockCenter a : Int) + nextDefect - (blockRemainder a : Int))

/-- The queue represented by a centered one-block or two-block macro state. -/
def fourCCenteredQueue (a : Nat) (state : FourCCenteredState) : List TagLetter :=
  match state.1 with
  | .one => oneBlockQueue a (centeredTail a state.2)
  | .pair => twoBlockQueue a (centeredTail a state.2)

private theorem centeredTail_positive (a : Nat) {state : FourCCenteredState}
    (state_inside : insideSpan (fourCSpan a) state) :
    0 < (blockCenter a : Int) + state.2 := by
  simp [insideSpan, fourCSpan, blockCenter] at state_inside ⊢
  omega

private theorem centeredCount_positive (a : Nat) {state : FourCCenteredState}
    (state_inside : insideSpan (fourCSpan a) state) :
    0 < (blockCenter a : Int) + state.2 - (blockRemainder a : Int) := by
  simp [insideSpan, fourCSpan, blockCenter, blockRemainder] at state_inside ⊢
  omega

private theorem centeredTail_cast (a : Nat) {state : FourCCenteredState}
    (state_inside : insideSpan (fourCSpan a) state) :
    (centeredTail a state.2 : Int) = (blockCenter a : Int) + state.2 := by
  exact Int.toNat_of_nonneg (centeredTail_positive a state_inside).le

private theorem centeredCount_cast (a : Nat) {state : FourCCenteredState}
    (state_inside : insideSpan (fourCSpan a) state) :
    (centeredCount a state.2 : Int) =
      (blockCenter a : Int) + state.2 - (blockRemainder a : Int) := by
  exact Int.toNat_of_nonneg (centeredCount_positive a state_inside).le

private theorem remainder_add_centeredCount (a : Nat) {state : FourCCenteredState}
    (state_inside : insideSpan (fourCSpan a) state) :
    blockRemainder a + centeredCount a state.2 = centeredTail a state.2 := by
  rw [← Int.ofNat_inj]
  simp only [Int.natCast_add]
  rw [centeredCount_cast a state_inside, centeredTail_cast a state_inside]
  omega

private theorem oneIdle_count (a : Nat) (next : Int)
    (current_inside : insideSpan (fourCSpan a) (.one, 3 * next))
    (next_inside : insideSpan (fourCSpan a) (.one, next)) :
    centeredTail a (3 * next) + blockSpan a = centeredCount a next * 3 := by
  rw [← Int.ofNat_inj]
  simp only [Int.natCast_add, Int.natCast_mul]
  rw [centeredTail_cast a current_inside, centeredCount_cast a next_inside]
  simp [blockCenter, blockSpan, blockRemainder]
  omega

private theorem oneCross_count (a : Nat) (next : Int)
    (current_inside : insideSpan (fourCSpan a) (.one, 3 * next + fourCSpan a))
    (next_inside : insideSpan (fourCSpan a) (.pair, next)) :
    centeredTail a (3 * next + fourCSpan a) = centeredCount a next * 3 := by
  rw [← Int.ofNat_inj]
  simp only [Int.natCast_mul]
  rw [centeredTail_cast a current_inside, centeredCount_cast a next_inside]
  simp [fourCSpan, blockCenter, blockRemainder]
  omega

private theorem pairCross_count (a : Nat) (next : Int)
    (current_inside : insideSpan (fourCSpan a) (.pair, 3 * next - fourCSpan a))
    (next_inside : insideSpan (fourCSpan a) (.one, next)) :
    centeredTail a (3 * next - fourCSpan a) + 2 * blockSpan a =
      centeredCount a next * 3 := by
  rw [← Int.ofNat_inj]
  simp only [Int.natCast_add, Int.natCast_mul]
  rw [centeredTail_cast a current_inside, centeredCount_cast a next_inside]
  simp [fourCSpan, blockCenter, blockSpan, blockRemainder]
  omega

private theorem centeredStep_reaches (a : Nat) {next current : FourCCenteredState}
    (current_inside : insideSpan (fourCSpan a) current)
    (step : FourCCenteredStep (fourCSpan a) next current) :
    TagReaches 3 (tagOutput (separatedBody (27 * a + 11)))
      (fourCCenteredQueue a current) (fourCCenteredQueue a next) := by
  have next_inside := centeredStep_inside (by simp [fourCSpan]; omega) current_inside step
  cases step with
  | oneIdle nextDefect =>
      have count_eq := oneIdle_count a nextDefect current_inside next_inside
      have tail_eq := remainder_add_centeredCount a next_inside
      have reach := oneBlock_idle_reaches a (centeredTail a (3 * nextDefect))
        (centeredCount a nextDefect) count_eq
      simpa [fourCCenteredQueue, tail_eq] using reach
  | oneCross nextDefect =>
      have count_eq := oneCross_count a nextDefect current_inside next_inside
      have tail_eq := remainder_add_centeredCount a next_inside
      have reach := oneBlock_cross_reaches a
        (centeredTail a (3 * nextDefect + fourCSpan a)) (centeredCount a nextDefect) count_eq
      simpa [fourCCenteredQueue, tail_eq] using reach
  | pairIdle nextDefect =>
      have current_inside' : insideSpan (fourCSpan a) (.one, 3 * nextDefect) := by
        simpa [insideSpan] using current_inside
      have next_inside' : insideSpan (fourCSpan a) (.one, nextDefect) := by
        simpa [insideSpan] using next_inside
      have count_eq := oneIdle_count a nextDefect current_inside' next_inside'
      have tail_eq := remainder_add_centeredCount a next_inside
      have reach := twoBlock_idle_reaches a (centeredTail a (3 * nextDefect))
        (centeredCount a nextDefect) count_eq
      simpa [fourCCenteredQueue, tail_eq] using reach
  | pairCross nextDefect =>
      have count_eq := pairCross_count a nextDefect current_inside next_inside
      have tail_eq := remainder_add_centeredCount a next_inside
      have reach := twoBlock_cross_reaches a
        (centeredTail a (3 * nextDefect - fourCSpan a)) (centeredCount a nextDefect) count_eq
      simpa [fourCCenteredQueue, tail_eq] using reach

private theorem oneTerminal_tail_mod (a : Nat) (defect : Int)
    (state_inside : insideSpan (fourCSpan a) (.one, defect))
    (defect_mod : defect % 3 = 1) : centeredTail a defect % 3 = 2 := by
  have tail_cast := centeredTail_cast a state_inside
  rw [← Int.natCast_inj]
  rw [Int.natCast_mod, tail_cast]
  simp [blockCenter]
  omega

private theorem pairTerminal_tail_mod (a : Nat) (defect : Int)
    (state_inside : insideSpan (fourCSpan a) (.pair, defect))
    (defect_mod : defect % 3 = 2) : centeredTail a defect % 3 = 0 := by
  have tail_cast := centeredTail_cast a state_inside
  rw [← Int.natCast_inj]
  rw [Int.natCast_mod, tail_cast]
  simp [blockCenter]
  omega

private theorem centeredState_outcome (a : Nat) (state : FourCCenteredState)
    (state_inside : insideSpan (fourCSpan a) state) :
    TagHaltsFrom 3 (tagOutput (separatedBody (27 * a + 11)))
        (fourCCenteredQueue a state) ∨
      ∃ next, FourCCenteredStep (fourCSpan a) next state ∧
        TagReaches 3 (tagOutput (separatedBody (27 * a + 11)))
          (fourCCenteredQueue a state) (fourCCenteredQueue a next) := by
  rcases state with ⟨mode, defect⟩
  have mod_nonneg : 0 ≤ defect % 3 := Int.emod_nonneg defect (by omega)
  have mod_lt : defect % 3 < 3 := Int.emod_lt_of_pos defect (by omega)
  have mod_cases : defect % 3 = 0 ∨ defect % 3 = 1 ∨ defect % 3 = 2 := by omega
  have division := Int.emod_add_mul_ediv defect 3
  cases mode with
  | one =>
      rcases mod_cases with mod_zero | mod_one | mod_two
      · let nextDefect := defect / 3
        have defect_eq : defect = 3 * nextDefect := by
          dsimp [nextDefect]
          omega
        let next : FourCCenteredState := (.one, nextDefect)
        have step : FourCCenteredStep (fourCSpan a) next (.one, defect) := by
          simpa [next, defect_eq] using
            (FourCCenteredStep.oneIdle (span := fourCSpan a) nextDefect)
        exact Or.inr ⟨next, step, centeredStep_reaches a state_inside step⟩
      · exact Or.inl (by
          have tail_mod := oneTerminal_tail_mod a defect state_inside mod_one
          simpa [fourCCenteredQueue] using oneBlock_terminal a (centeredTail a defect) tail_mod)
      · let nextDefect := defect / 3 - (43 * (a : Int) + 20)
        have defect_eq : defect = 3 * nextDefect + fourCSpan a := by
          dsimp [nextDefect]
          simp [fourCSpan]
          omega
        let next : FourCCenteredState := (.pair, nextDefect)
        have step : FourCCenteredStep (fourCSpan a) next (.one, defect) := by
          simpa [next, defect_eq] using
            (FourCCenteredStep.oneCross (span := fourCSpan a) nextDefect)
        exact Or.inr ⟨next, step, centeredStep_reaches a state_inside step⟩
  | pair =>
      rcases mod_cases with mod_zero | mod_one | mod_two
      · let nextDefect := defect / 3
        have defect_eq : defect = 3 * nextDefect := by
          dsimp [nextDefect]
          omega
        let next : FourCCenteredState := (.pair, nextDefect)
        have step : FourCCenteredStep (fourCSpan a) next (.pair, defect) := by
          simpa [next, defect_eq] using
            (FourCCenteredStep.pairIdle (span := fourCSpan a) nextDefect)
        exact Or.inr ⟨next, step, centeredStep_reaches a state_inside step⟩
      · let nextDefect := defect / 3 + (43 * (a : Int) + 21)
        have defect_eq : defect = 3 * nextDefect - fourCSpan a := by
          dsimp [nextDefect]
          simp [fourCSpan]
          omega
        let next : FourCCenteredState := (.one, nextDefect)
        have step : FourCCenteredStep (fourCSpan a) next (.pair, defect) := by
          simpa [next, defect_eq] using
            (FourCCenteredStep.pairCross (span := fourCSpan a) nextDefect)
        exact Or.inr ⟨next, step, centeredStep_reaches a state_inside step⟩
      · exact Or.inl (by
          have tail_mod := pairTerminal_tail_mod a defect state_inside mod_two
          simpa [fourCCenteredQueue] using twoBlock_terminal a (centeredTail a defect) tail_mod)

private theorem centeredState_halts (a : Nat) (state : FourCCenteredState)
    (state_inside : insideSpan (fourCSpan a) state)
    (accessible : Acc (FourCCenteredStep (fourCSpan a)) state) :
    TagHaltsFrom 3 (tagOutput (separatedBody (27 * a + 11)))
      (fourCCenteredQueue a state) := by
  refine accessible.rec (motive := fun current _ =>
    insideSpan (fourCSpan a) current →
      TagHaltsFrom 3 (tagOutput (separatedBody (27 * a + 11)))
        (fourCCenteredQueue a current)) ?_ state_inside
  intro current _ downstream current_inside
  rcases centeredState_outcome a current current_inside with terminal | ⟨next, step, reach⟩
  · exact terminal
  · have next_inside := centeredStep_inside (by simp [fourCSpan]; omega) current_inside step
    exact tagHaltsFrom_of_reaches reach (downstream next step next_inside)

private theorem initial_centeredTail (a : Nat) :
    centeredTail a (fourCInitialDefect a) = 82 * a + 38 := by
  unfold centeredTail fourCInitialDefect blockCenter
  have nonnegative : 0 ≤ ((105 * a + 49 : Nat) : Int) + -(23 * (a : Int) + 11) := by
    norm_num
    omega
  rw [← Int.ofNat_inj]
  rw [Int.toNat_of_nonneg nonnegative]
  simp
  omega

private theorem initial_inside (a : Nat) :
    insideSpan (fourCSpan a) (.one, fourCInitialDefect a) := by
  simp [insideSpan, fourCSpan, fourCInitialDefect]
  omega

/-- The canonical four-`c` queue reached by every `n ≡ 11 (mod 27)` source halts. -/
theorem diagonalFourCQueue_tagHaltsFrom (a : Nat) :
    TagHaltsFrom 3 (tagOutput (separatedBody (27 * a + 11)))
      (fourCQueue (9 * a + 4) (82 * a + 38)) := by
  have halts := centeredState_halts a (.one, fourCInitialDefect a) (initial_inside a)
    (fourCCentered_initial_accessible a)
  simpa [fourCCenteredQueue, oneBlockQueue, blockParameter, initial_centeredTail] using halts

/-- Every source in the final open diagonal congruence class halts. -/
theorem elevenModuloTwentySeven_tagHaltsFrom (a : Nat) :
    TagHaltsFrom 3 (tagOutput (separatedBody (27 * a + 11)))
      (coupledInitial (27 * a + 11)) := by
  exact tagHaltsFrom_of_reaches (elevenModuloTwentySeven_reaches_fourCQueue a)
    (diagonalFourCQueue_tagHaltsFrom a)

/-- Every coupled diagonal source with separation `n ≡ 2 (mod 3)` halts. Combined with the
periodic-orbit theorem for the other two residues, this completes the diagonal classification. -/
theorem twoModuloThree_tagHaltsFrom (k : Nat) :
    TagHaltsFrom 3 (tagOutput (separatedBody (3 * k + 2)))
      (coupledInitial (3 * k + 2)) := by
  have k_mod_lt : k % 3 < 3 := Nat.mod_lt k (by omega)
  rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with
      k_mod | k_mod | k_mod
  · let j := k / 3
    have j_mod_lt : j % 3 < 3 := Nat.mod_lt j (by omega)
    rcases (show j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 by omega) with
        j_mod | j_mod | j_mod
    · have exponent_eq : 3 * k + 2 = 27 * (j / 3) + 2 := by
        dsimp [j]
        omega
      rw [exponent_eq]
      exact twoModuloTwentySeven_tagHaltsFrom (j / 3)
    · have exponent_eq : 3 * k + 2 = 27 * (j / 3) + 11 := by
        dsimp [j]
        omega
      rw [exponent_eq]
      exact elevenModuloTwentySeven_tagHaltsFrom (j / 3)
    · have exponent_eq : 3 * k + 2 = 27 * (j / 3) + 20 := by
        dsimp [j]
        omega
      rw [exponent_eq]
      exact twentyModuloTwentySeven_tagHaltsFrom (j / 3)
  · have exponent_eq : 3 * k + 2 = 9 * (k / 3) + 5 := by omega
    rw [exponent_eq]
    exact fiveResidue_tagHaltsFrom (k / 3)
  · have exponent_eq : 3 * k + 2 = 9 * (k / 3) + 8 := by omega
    rw [exponent_eq]
    exact eightResidue_tagHaltsFrom (k / 3)

private theorem zeroSeparation_initial_step :
    TagStep 3 (tagOutput (separatedBody 0)) (coupledInitial 0) (expandedQueue 0) := by
  exact ⟨stroke₃ .c .c .b, [], by decide, by decide⟩

private theorem zeroSeparation_expanded_step :
    TagStep 3 (tagOutput (separatedBody 0)) (expandedQueue 0) (cycleQueue 0) := by
  exact ⟨strokeBBC, [.c, .b], by decide, by decide⟩

/-- The degenerate zero-separation source enters the same two-state cycle as the positive
zero-residue family and does not halt. -/
theorem zeroSeparation_not_tagHaltsFrom :
    ¬TagHaltsFrom 3 (tagOutput (separatedBody 0)) (coupledInitial 0) := by
  have cycle :
      TagReachesIn 3 (tagOutput (separatedBody 0)) 2 (cycleQueue 0) (cycleQueue 0) := by
    simpa using Relation.ReachesIn.head (cycleQueue_step 0)
      (Relation.ReachesIn.head zeroSeparation_expanded_step (Relation.ReachesIn.refl _))
  have cycle_not_halts :
      ¬TagHaltsFrom 3 (tagOutput (separatedBody 0)) (cycleQueue 0) := by
    apply not_tagHaltsFrom_of_transGen_progress (fun candidate => candidate = cycleQueue 0)
    · intro candidate candidate_eq
      subst candidate
      exact ⟨cycleQueue 0, rfl, cycle.toTransGen (by omega)⟩
    · rfl
  intro initial_halts
  have cycle_halts := tagHaltsFrom_after_reaches
    ((Relation.ReflTransGen.single zeroSeparation_initial_step).trans
      (Relation.ReflTransGen.single zeroSeparation_expanded_step)) initial_halts
  exact cycle_not_halts cycle_halts

/-- Complete classification of the coupled diagonal separated-two-`c` source: it halts exactly
in residue two modulo three. -/
theorem diagonal_tagHaltsFrom_iff (n : Nat) :
    TagHaltsFrom 3 (tagOutput (separatedBody n)) (coupledInitial n) ↔ n % 3 = 2 := by
  constructor
  · intro halts
    by_contra residue_ne
    cases n with
    | zero => exact zeroSeparation_not_tagHaltsFrom halts
    | succ n =>
        have nonhalting := separated_not_tagHaltsFrom (n + 1) (by omega) residue_ne
        exact nonhalting (by simpa [coupledInitial] using halts)
  · intro residue_two
    have exponent_eq : n = 3 * (n / 3) + 2 := by omega
    rw [exponent_eq]
    exact twoModuloThree_tagHaltsFrom (n / 3)

end MatrixMortality.SeparatedTwoCDiagonal
