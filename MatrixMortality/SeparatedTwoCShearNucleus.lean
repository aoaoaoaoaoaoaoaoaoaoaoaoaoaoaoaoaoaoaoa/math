import MatrixMortality.SeparatedTwoCShear

/-!
# Finite nucleus for phase-mismatched sheared two-c queues

Two canonical pair queues reduce every phase mismatch to a signed inverse-ternary map. Its
central predecessor gap contains both initial defects, forcing every such queue to terminate.
-/

namespace MatrixMortality.SeparatedTwoCShear

open BranchingHistory PeriodicHistory SeparatedTwoCOrbit

/-- Whether the normalized sheared queue contains two or three equal-middle `c` pairs. -/
inductive ShearedPairMode
  | double
  | triple
  deriving DecidableEq

instance : Fintype ShearedPairMode where
  elems := {.double, .triple}
  complete := by
    intro mode
    cases mode with
    | double => simp
    | triple => simp

/-- A normalized sheared pair population and its centered outer-gap coordinate. -/
abbrev ShearedCenteredState := ShearedPairMode × Int

/-- The residue-restricted centered inverse-ternary map for a sheared pair queue. Missing
residues are head-clean terminal queues. -/
inductive ShearedCenteredStep (span : Int) :
    ShearedCenteredState → ShearedCenteredState → Prop
  | doubleIdle (next : Int) :
      ShearedCenteredStep span (.double, next) (.double, 3 * next)
  | doubleCross (next : Int) :
      ShearedCenteredStep span (.triple, next) (.double, 3 * next + span)
  | tripleIdle (next : Int) :
      ShearedCenteredStep span (.triple, next) (.triple, 3 * next)
  | tripleCross (next : Int) :
      ShearedCenteredStep span (.double, next) (.triple, 3 * next - span)

private def insideShearedSpan (span : Int) (state : ShearedCenteredState) : Prop :=
  match state.1 with
  | .double => 0 < state.2 ∧ 3 * state.2 < span
  | .triple => -span < 3 * state.2 ∧ state.2 < 0

private instance insideShearedSpan_decidable (span : Int) :
    DecidablePred (insideShearedSpan span) := by
  intro state
  unfold insideShearedSpan
  cases state.1 <;> infer_instance

private noncomputable def shearedCenteredCage (span : Int) : Finset ShearedCenteredState :=
  (Finset.univ.product (Finset.Icc (-span) span)).filter (insideShearedSpan span)

private theorem mem_shearedCenteredCage {span : Int} {state : ShearedCenteredState} :
    state ∈ shearedCenteredCage span ↔ insideShearedSpan span state := by
  constructor
  · intro state_mem
    exact (Finset.mem_filter.mp state_mem).2
  · intro state_inside
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩,
      state_inside⟩
    · cases state with
      | mk mode defect =>
          cases mode <;> simp [insideShearedSpan] at state_inside ⊢ <;> omega
    · cases state with
      | mk mode defect =>
          cases mode <;> simp [insideShearedSpan] at state_inside ⊢ <;> omega

private theorem shearedCenteredStep_inside {span : Int} (span_pos : 0 < span)
    {next current : ShearedCenteredState}
    (current_inside : insideShearedSpan span current)
    (step : ShearedCenteredStep span next current) :
    insideShearedSpan span next := by
  cases step <;> simp only [insideShearedSpan] at current_inside ⊢ <;> omega

private theorem shearedCenteredStep_predecessor_unique {span : Int}
    {next left right : ShearedCenteredState}
    (left_inside : insideShearedSpan span left)
    (right_inside : insideShearedSpan span right)
    (left_step : ShearedCenteredStep span next left)
    (right_step : ShearedCenteredStep span next right) : left = right := by
  cases left_step <;> cases right_step <;>
    simp only [insideShearedSpan, Prod.mk.injEq] at left_inside right_inside ⊢ <;> omega

private theorem shearedAcc_of_finite_injective_root {α : Type*} [DecidableEq α]
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
  apply shearedAcc_of_finite_injective_root relation (cage.erase root) next
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

/-- A positive double-pair defect in the central image gap `H/9 < d < 2H/9` is accessible
for the centered map. -/
theorem shearedCentered_double_accessible (span defect : Nat)
    (lower : span < 9 * defect) (upper : 9 * defect < 2 * span) :
    Acc (ShearedCenteredStep (span : Int)) (.double, (defect : Int)) := by
  have span_pos : 0 < (span : Int) := by omega
  apply shearedAcc_of_finite_injective_root (ShearedCenteredStep (span : Int))
    (shearedCenteredCage (span : Int)) (.double, (defect : Int))
  · rw [mem_shearedCenteredCage]
    simp [insideShearedSpan]
    omega
  · intro current next current_mem step
    rw [mem_shearedCenteredCage] at current_mem ⊢
    exact shearedCenteredStep_inside span_pos current_mem step
  · intro next left right left_mem right_mem left_step right_step
    rw [mem_shearedCenteredCage] at left_mem right_mem
    exact shearedCenteredStep_predecessor_unique left_mem right_mem left_step right_step
  · intro current current_mem step
    rw [mem_shearedCenteredCage] at current_mem
    cases step with
    | doubleIdle next =>
        simp only [insideShearedSpan] at current_mem
        omega
    | tripleCross next =>
        simp only [insideShearedSpan] at current_mem
        omega

/-- A negative triple-pair defect in the central image gap `H/9 < d < 2H/9` is accessible
for the centered map. -/
theorem shearedCentered_triple_accessible (span defect : Nat)
    (lower : span < 9 * defect) (upper : 9 * defect < 2 * span) :
    Acc (ShearedCenteredStep (span : Int)) (.triple, -(defect : Int)) := by
  have span_pos : 0 < (span : Int) := by omega
  apply shearedAcc_of_finite_injective_root (ShearedCenteredStep (span : Int))
    (shearedCenteredCage (span : Int)) (.triple, -(defect : Int))
  · rw [mem_shearedCenteredCage]
    simp [insideShearedSpan]
    omega
  · intro current next current_mem step
    rw [mem_shearedCenteredCage] at current_mem ⊢
    exact shearedCenteredStep_inside span_pos current_mem step
  · intro next left right left_mem right_mem left_step right_step
    rw [mem_shearedCenteredCage] at left_mem right_mem
    exact shearedCenteredStep_predecessor_unique left_mem right_mem left_step right_step
  · intro current current_mem step
    rw [mem_shearedCenteredCage] at current_mem
    cases step with
    | doubleCross next =>
        simp only [insideShearedSpan] at current_mem
        omega
    | tripleIdle next =>
        simp only [insideShearedSpan] at current_mem
        omega

/-- The fixed gap between the two terminal pairs in the sheared normal form. -/
def shearedPairBridge (middleQuotient shear : Nat) : Nat :=
  4 * middleQuotient + 2 * shear + 5

/-- The translation span of the centered sheared pair dynamics. -/
def shearedPairSpan (middleQuotient shear : Nat) : Nat :=
  7 * middleQuotient + 2 * shear + 9

private def shearedDoubleCenter (middleQuotient shear : Nat) : Nat :=
  2 * shearedPairBridge middleQuotient shear - 1

private def shearedTripleCenter (middleQuotient shear : Nat) : Nat :=
  2 * shearedPairBridge middleQuotient shear + 1

/-- The two-pair `D` normal form with a variable leading gap. -/
def shearedDoublePairQueue
    (shear separation middleQuotient outerGap : Nat) : List TagLetter :=
  bRun outerGap ++ [.c] ++ bRun (3 * middleQuotient + 2) ++ [.c] ++
    bRun (shearedPairBridge middleQuotient shear) ++ [.c] ++
      bRun (3 * middleQuotient + 2) ++ [.c] ++ bRun (separation + 1)

/-- The three-pair `T` normal form with a variable middle gap. -/
def shearedTriplePairQueue
    (shear separation middleQuotient middleGap : Nat) : List TagLetter :=
  bRun (4 * middleQuotient + 2 * shear + 3) ++ [.c] ++
    bRun (3 * middleQuotient + 2) ++ [.c] ++ bRun middleGap ++ [.c] ++
      bRun (3 * middleQuotient + 2) ++ [.c] ++
        bRun (shearedPairBridge middleQuotient shear) ++ [.c] ++
          bRun (3 * middleQuotient + 2) ++ [.c] ++ bRun (separation + 1)

private def shearedPairHistory (middleQuotient : Nat) : List (Stroke TagLetter 3) :=
  [strokeCBB] ++ List.replicate middleQuotient strokeBBB ++ [strokeCBB]

private theorem shearedLeadingPair_reaches
    (shear separation middleQuotient rest : Nat) (tail : List TagLetter)
    (middle_eq : separation + shear = 3 * middleQuotient + 2) :
    TagReaches 3 (tagOutput (shearedBody shear separation))
      ([.c] ++ bRun (3 * middleQuotient + 2) ++ [.c] ++ bRun (rest + 2) ++ tail)
      (bRun rest ++ tail ++ bRun (3 * shear + 2) ++ [.c] ++
        bRun (3 * middleQuotient + 2) ++ [.c] ++
          bRun (shearedPairBridge middleQuotient shear) ++ [.c] ++
            bRun (3 * middleQuotient + 2) ++ [.c] ++ bRun (separation + 1)) := by
  have reach := Undecidability.tagReaches_history (tagOutput (shearedBody shear separation))
    (shearedPairHistory middleQuotient) (bRun rest ++ tail)
  have source_eq :
      consumed (shearedPairHistory middleQuotient) ++ (bRun rest ++ tail) =
        [.c] ++ bRun (3 * middleQuotient + 2) ++ [.c] ++ bRun (rest + 2) ++ tail := by
    simp [shearedPairHistory, strokeCBB, stroke₃, Stroke.letters, bRun, List.append_assoc]
  have target_eq :
      (bRun rest ++ tail) ++
          produced (tagOutput (shearedBody shear separation))
            (shearedPairHistory middleQuotient) =
        bRun rest ++ tail ++ bRun (3 * shear + 2) ++ [.c] ++
          bRun (3 * middleQuotient + 2) ++ [.c] ++
            bRun (shearedPairBridge middleQuotient shear) ++ [.c] ++
              bRun (3 * middleQuotient + 2) ++ [.c] ++ bRun (separation + 1) := by
    simp [shearedPairHistory, shearedPairBridge, shearedBody, twoCBody, strokeCBB, stroke₃,
      tagOutput, nearyBody, bRun, List.append_assoc]
    rw [middle_eq]
    have bridge_eq : separation + 1 + (middleQuotient + (3 * shear + 2)) =
        4 * middleQuotient + 2 * shear + 5 := by omega
    rw [bridge_eq]
  rw [source_eq, target_eq] at reach
  exact reach

private theorem shearedCleanPrefix_reaches
    (body front tail : List TagLetter) (count : Nat)
    (front_length : front.length = count * 3)
    (front_clean : Undecidability.ConstantAtMultiples 3 TagLetter.b front) :
    TagReaches 3 (tagOutput body) (front ++ tail) (tail ++ bRun count) :=
  (cleanPrefix_reachesIn body front tail count front_length front_clean).toReaches

private theorem shearedDoubleCross_reaches
    (shear separation middleQuotient outerGap count : Nat)
    (middle_eq : separation + shear = 3 * middleQuotient + 2)
    (count_eq : outerGap = count * 3) :
    TagReaches 3 (tagOutput (shearedBody shear separation))
      (shearedDoublePairQueue shear separation middleQuotient outerGap)
      (shearedTriplePairQueue shear separation middleQuotient
        (separation + 3 * shear + 3 + count)) := by
  let activeTail := [.c] ++ bRun (3 * middleQuotient + 2) ++ [.c] ++
    bRun (shearedPairBridge middleQuotient shear) ++ [.c] ++
      bRun (3 * middleQuotient + 2) ++ [.c] ++ bRun (separation + 1)
  have drainage := shearedCleanPrefix_reaches (shearedBody shear separation)
    (bRun outerGap) activeTail count (by simp [bRun, count_eq])
    (by simpa [ConstantAtOffset, Undecidability.ConstantAtMultiples] using
      constantAtOffset_replicate 0 outerGap)
  have drainage' :
      TagReaches 3 (tagOutput (shearedBody shear separation))
        (shearedDoublePairQueue shear separation middleQuotient outerGap)
        (activeTail ++ bRun count) := by
    simpa [shearedDoublePairQueue, activeTail, List.append_assoc] using drainage
  have firing := shearedLeadingPair_reaches shear separation middleQuotient
    (4 * middleQuotient + 2 * shear + 3)
    ([.c] ++ bRun (3 * middleQuotient + 2) ++ [.c] ++
      bRun (separation + 1 + count)) middle_eq
  have firing' :
      TagReaches 3 (tagOutput (shearedBody shear separation))
        (activeTail ++ bRun count)
        (shearedTriplePairQueue shear separation middleQuotient
          (separation + 3 * shear + 3 + count)) := by
    have bridge_eq : 4 * middleQuotient + 2 * shear + 3 + 2 =
        shearedPairBridge middleQuotient shear := by
      simp [shearedPairBridge]
    have middleGap_eq : separation + 1 + count + (3 * shear + 2) =
        separation + 3 * shear + 3 + count := by omega
    simpa [activeTail, shearedTriplePairQueue, bRun, List.append_assoc, bridge_eq,
      middleGap_eq] using firing
  exact drainage'.trans firing'

private theorem shearedDoubleIdle_reaches
    (shear separation middleQuotient outerGap count : Nat)
    (middle_eq : separation + shear = 3 * middleQuotient + 2)
    (phase_nonzero : (middleQuotient + 2 * shear) % 3 ≠ 0)
    (count_eq : outerGap + (3 * middleQuotient + 2) +
      shearedPairBridge middleQuotient shear + 2 = count * 3) :
    TagReaches 3 (tagOutput (shearedBody shear separation))
      (shearedDoublePairQueue shear separation middleQuotient outerGap)
      (shearedDoublePairQueue shear separation middleQuotient
        (separation + 3 * shear + 1 + count)) := by
  let front := bRun outerGap ++ [.c] ++ bRun (3 * middleQuotient + 2) ++ [.c] ++
    bRun (shearedPairBridge middleQuotient shear)
  let activeTail := [.c] ++ bRun (3 * middleQuotient + 2) ++ [.c] ++
    bRun (separation + 1)
  have front_length : front.length = count * 3 := by
    simp [front, bRun, shearedPairBridge] at count_eq ⊢
    omega
  have front_clean : Undecidability.ConstantAtMultiples 3 TagLetter.b front := by
    have clean : ConstantAtOffset 0 front := by
      unfold front
      simp only [List.singleton_append, List.append_assoc]
      apply constantAtOffset_bRun_c
      · rw [Nat.dvd_iff_mod_eq_zero]
        simp [shearedPairBridge] at count_eq
        omega
      · apply constantAtOffset_bRun_c
        · rw [Nat.dvd_iff_mod_eq_zero]
          simp [shearedPairBridge] at count_eq
          omega
        · exact constantAtOffset_replicate _ _
    simpa [ConstantAtOffset, Undecidability.ConstantAtMultiples] using clean
  have drainage := shearedCleanPrefix_reaches (shearedBody shear separation)
    front activeTail count front_length front_clean
  have drainage' :
      TagReaches 3 (tagOutput (shearedBody shear separation))
        (shearedDoublePairQueue shear separation middleQuotient outerGap)
        (activeTail ++ bRun count) := by
    simpa [shearedDoublePairQueue, front, activeTail, List.append_assoc] using drainage
  have count_pos : 0 < count := by
    simp [shearedPairBridge] at count_eq
    omega
  have following_eq : separation + count - 1 + 2 = separation + 1 + count := by omega
  have firing := shearedLeadingPair_reaches shear separation middleQuotient
    (separation + count - 1) [] middle_eq
  have firing' :
      TagReaches 3 (tagOutput (shearedBody shear separation))
        (activeTail ++ bRun count)
        (shearedDoublePairQueue shear separation middleQuotient
          (separation + 3 * shear + 1 + count)) := by
    have outerGap_eq : separation + count - 1 + (3 * shear + 2) =
        separation + 3 * shear + 1 + count := by omega
    simpa [activeTail, shearedDoublePairQueue, shearedPairBridge, bRun, List.append_assoc,
      following_eq, outerGap_eq] using firing
  exact drainage'.trans firing'

private theorem shearedTripleIdle_reaches
    (shear separation middleQuotient middleGap count : Nat)
    (middle_eq : separation + shear = 3 * middleQuotient + 2)
    (phase_nonzero : (middleQuotient + 2 * shear) % 3 ≠ 0)
    (count_eq : shearedPairBridge middleQuotient shear +
      (3 * middleQuotient + 2) + middleGap = count * 3) :
    TagReaches 3 (tagOutput (shearedBody shear separation))
      (shearedTriplePairQueue shear separation middleQuotient middleGap)
      (shearedTriplePairQueue shear separation middleQuotient
        (separation + 3 * shear + 3 + count)) := by
  let front := bRun (4 * middleQuotient + 2 * shear + 3) ++ [.c] ++
    bRun (3 * middleQuotient + 2) ++ [.c] ++ bRun middleGap
  let activeTail := [.c] ++ bRun (3 * middleQuotient + 2) ++ [.c] ++
    bRun (shearedPairBridge middleQuotient shear) ++ [.c] ++
      bRun (3 * middleQuotient + 2) ++ [.c] ++ bRun (separation + 1)
  have front_length : front.length = count * 3 := by
    simp [front, shearedPairBridge, bRun] at count_eq ⊢
    omega
  have front_clean : Undecidability.ConstantAtMultiples 3 TagLetter.b front := by
    have clean : ConstantAtOffset 0 front := by
      unfold front
      simp only [List.singleton_append, List.append_assoc]
      apply constantAtOffset_bRun_c
      · rw [Nat.dvd_iff_mod_eq_zero]
        omega
      · apply constantAtOffset_bRun_c
        · rw [Nat.dvd_iff_mod_eq_zero]
          omega
        · exact constantAtOffset_replicate _ _
    simpa [ConstantAtOffset, Undecidability.ConstantAtMultiples] using clean
  have drainage := shearedCleanPrefix_reaches (shearedBody shear separation)
    front activeTail count front_length front_clean
  have drainage' :
      TagReaches 3 (tagOutput (shearedBody shear separation))
        (shearedTriplePairQueue shear separation middleQuotient middleGap)
        (activeTail ++ bRun count) := by
    simpa [shearedTriplePairQueue, front, activeTail, List.append_assoc] using drainage
  have firing := shearedLeadingPair_reaches shear separation middleQuotient
    (4 * middleQuotient + 2 * shear + 3)
    ([.c] ++ bRun (3 * middleQuotient + 2) ++ [.c] ++
      bRun (separation + 1 + count)) middle_eq
  have firing' :
      TagReaches 3 (tagOutput (shearedBody shear separation))
        (activeTail ++ bRun count)
        (shearedTriplePairQueue shear separation middleQuotient
          (separation + 3 * shear + 3 + count)) := by
    have bridge_eq : 4 * middleQuotient + 2 * shear + 3 + 2 =
        shearedPairBridge middleQuotient shear := by
      simp [shearedPairBridge]
    have middleGap_eq : separation + 1 + count + (3 * shear + 2) =
        separation + 3 * shear + 3 + count := by omega
    simpa [activeTail, shearedTriplePairQueue, bRun, List.append_assoc, bridge_eq,
      middleGap_eq] using firing
  exact drainage'.trans firing'

private theorem shearedTripleCross_reaches
    (shear separation middleQuotient middleGap count : Nat)
    (middle_eq : separation + shear = 3 * middleQuotient + 2)
    (phase_nonzero : (middleQuotient + 2 * shear) % 3 ≠ 0)
    (count_eq : 2 * shearedPairBridge middleQuotient shear +
      2 * (3 * middleQuotient + 2) + middleGap + 2 = count * 3) :
    TagReaches 3 (tagOutput (shearedBody shear separation))
      (shearedTriplePairQueue shear separation middleQuotient middleGap)
      (shearedDoublePairQueue shear separation middleQuotient
        (separation + 3 * shear + 1 + count)) := by
  let front := bRun (4 * middleQuotient + 2 * shear + 3) ++ [.c] ++
    bRun (3 * middleQuotient + 2) ++ [.c] ++ bRun middleGap ++ [.c] ++
      bRun (3 * middleQuotient + 2) ++ [.c] ++
        bRun (shearedPairBridge middleQuotient shear)
  let activeTail := [.c] ++ bRun (3 * middleQuotient + 2) ++ [.c] ++
    bRun (separation + 1)
  have front_length : front.length = count * 3 := by
    simp [front, shearedPairBridge, bRun] at count_eq ⊢
    omega
  have front_clean : Undecidability.ConstantAtMultiples 3 TagLetter.b front := by
    have clean : ConstantAtOffset 0 front := by
      unfold front
      simp only [List.singleton_append, List.append_assoc]
      apply constantAtOffset_bRun_c
      · rw [Nat.dvd_iff_mod_eq_zero]
        omega
      · apply constantAtOffset_bRun_c
        · rw [Nat.dvd_iff_mod_eq_zero]
          omega
        · apply constantAtOffset_bRun_c
          · rw [Nat.dvd_iff_mod_eq_zero]
            simp [shearedPairBridge] at count_eq
            omega
          · apply constantAtOffset_bRun_c
            · rw [Nat.dvd_iff_mod_eq_zero]
              simp [shearedPairBridge] at count_eq
              omega
            · exact constantAtOffset_replicate _ _
    simpa [ConstantAtOffset, Undecidability.ConstantAtMultiples] using clean
  have drainage := shearedCleanPrefix_reaches (shearedBody shear separation)
    front activeTail count front_length front_clean
  have drainage' :
      TagReaches 3 (tagOutput (shearedBody shear separation))
        (shearedTriplePairQueue shear separation middleQuotient middleGap)
        (activeTail ++ bRun count) := by
    simpa [shearedTriplePairQueue, front, activeTail, List.append_assoc] using drainage
  have count_pos : 0 < count := by
    simp [shearedPairBridge] at count_eq
    omega
  have following_eq : separation + count - 1 + 2 = separation + 1 + count := by omega
  have firing := shearedLeadingPair_reaches shear separation middleQuotient
    (separation + count - 1) [] middle_eq
  have firing' :
      TagReaches 3 (tagOutput (shearedBody shear separation))
        (activeTail ++ bRun count)
        (shearedDoublePairQueue shear separation middleQuotient
          (separation + 3 * shear + 1 + count)) := by
    have outerGap_eq : separation + count - 1 + (3 * shear + 2) =
        separation + 3 * shear + 1 + count := by omega
    simpa [activeTail, shearedDoublePairQueue, shearedPairBridge, bRun, List.append_assoc,
      following_eq, outerGap_eq] using firing
  exact drainage'.trans firing'

private def shearedCenteredGap
    (middleQuotient shear : Nat) (state : ShearedCenteredState) : Nat :=
  match state.1 with
  | .double => Int.toNat ((shearedDoubleCenter middleQuotient shear : Int) + state.2)
  | .triple => Int.toNat ((shearedTripleCenter middleQuotient shear : Int) + state.2)

private def shearedCenteredCount (middleQuotient shear : Nat) (defect : Int) : Nat :=
  Int.toNat ((5 * middleQuotient + 2 * shear + 6 : Nat) + defect)

/-- The concrete pair queue represented by a centered `D` or `T` macro state. -/
def shearedCenteredPairQueue (shear separation middleQuotient : Nat)
    (state : ShearedCenteredState) : List TagLetter :=
  match state.1 with
  | .double => shearedDoublePairQueue shear separation middleQuotient
      (shearedCenteredGap middleQuotient shear state)
  | .triple => shearedTriplePairQueue shear separation middleQuotient
      (shearedCenteredGap middleQuotient shear state)

private theorem shearedCenteredGap_positive (middleQuotient shear : Nat)
    {state : ShearedCenteredState}
    (state_inside : insideShearedSpan (shearedPairSpan middleQuotient shear : Int) state) :
    0 < match state.1 with
      | .double => (shearedDoubleCenter middleQuotient shear : Int) + state.2
      | .triple => (shearedTripleCenter middleQuotient shear : Int) + state.2 := by
  rcases state with ⟨mode, defect⟩
  cases mode <;>
    simp [insideShearedSpan, shearedPairSpan, shearedDoubleCenter, shearedTripleCenter,
      shearedPairBridge] at state_inside ⊢ <;>
    omega

private theorem shearedCenteredCount_positive (middleQuotient shear : Nat)
    {state : ShearedCenteredState}
    (state_inside : insideShearedSpan (shearedPairSpan middleQuotient shear : Int) state) :
    0 < (5 * middleQuotient + 2 * shear + 6 : Nat) + state.2 := by
  rcases state with ⟨mode, defect⟩
  cases mode <;>
    simp [insideShearedSpan, shearedPairSpan] at state_inside ⊢ <;>
    omega

private theorem shearedCenteredGap_cast (middleQuotient shear : Nat)
    {state : ShearedCenteredState}
    (state_inside : insideShearedSpan (shearedPairSpan middleQuotient shear : Int) state) :
    (shearedCenteredGap middleQuotient shear state : Int) =
      match state.1 with
      | .double => (shearedDoubleCenter middleQuotient shear : Int) + state.2
      | .triple => (shearedTripleCenter middleQuotient shear : Int) + state.2 := by
  rcases state with ⟨mode, defect⟩
  cases mode <;>
    exact Int.toNat_of_nonneg
      (shearedCenteredGap_positive middleQuotient shear state_inside).le

private theorem shearedCenteredCount_cast (middleQuotient shear : Nat)
    {state : ShearedCenteredState}
    (state_inside : insideShearedSpan (shearedPairSpan middleQuotient shear : Int) state) :
    (shearedCenteredCount middleQuotient shear state.2 : Int) =
      (5 * middleQuotient + 2 * shear + 6 : Nat) + state.2 := by
  exact Int.toNat_of_nonneg
    (shearedCenteredCount_positive middleQuotient shear state_inside).le

private theorem shearedDoubleIdle_count (middleQuotient shear : Nat) (next : Int)
    (current_inside : insideShearedSpan (shearedPairSpan middleQuotient shear : Int)
      (.double, 3 * next))
    (next_inside : insideShearedSpan (shearedPairSpan middleQuotient shear : Int)
      (.double, next)) :
    shearedCenteredGap middleQuotient shear (.double, 3 * next) +
        (3 * middleQuotient + 2) + shearedPairBridge middleQuotient shear + 2 =
      shearedCenteredCount middleQuotient shear next * 3 := by
  rw [← Int.ofNat_inj]
  simp only [Int.natCast_add, Int.natCast_mul]
  rw [shearedCenteredGap_cast middleQuotient shear current_inside,
    shearedCenteredCount_cast middleQuotient shear next_inside]
  simp [shearedDoubleCenter, shearedPairBridge]
  omega

private theorem shearedDoubleCross_count (middleQuotient shear : Nat) (next : Int)
    (current_inside : insideShearedSpan (shearedPairSpan middleQuotient shear : Int)
      (.double, 3 * next + shearedPairSpan middleQuotient shear))
    (next_inside : insideShearedSpan (shearedPairSpan middleQuotient shear : Int)
      (.triple, next)) :
    shearedCenteredGap middleQuotient shear
        (.double, 3 * next + shearedPairSpan middleQuotient shear) =
      shearedCenteredCount middleQuotient shear next * 3 := by
  rw [← Int.ofNat_inj]
  simp only [Int.natCast_mul]
  rw [shearedCenteredGap_cast middleQuotient shear current_inside,
    shearedCenteredCount_cast middleQuotient shear next_inside]
  simp [shearedDoubleCenter, shearedPairBridge, shearedPairSpan]
  omega

private theorem shearedTripleIdle_count (middleQuotient shear : Nat) (next : Int)
    (current_inside : insideShearedSpan (shearedPairSpan middleQuotient shear : Int)
      (.triple, 3 * next))
    (next_inside : insideShearedSpan (shearedPairSpan middleQuotient shear : Int)
      (.triple, next)) :
    shearedPairBridge middleQuotient shear + (3 * middleQuotient + 2) +
        shearedCenteredGap middleQuotient shear (.triple, 3 * next) =
      shearedCenteredCount middleQuotient shear next * 3 := by
  rw [← Int.ofNat_inj]
  simp only [Int.natCast_add, Int.natCast_mul]
  rw [shearedCenteredGap_cast middleQuotient shear current_inside,
    shearedCenteredCount_cast middleQuotient shear next_inside]
  simp [shearedTripleCenter, shearedPairBridge]
  omega

private theorem shearedTripleCross_count (middleQuotient shear : Nat) (next : Int)
    (current_inside : insideShearedSpan (shearedPairSpan middleQuotient shear : Int)
      (.triple, 3 * next - shearedPairSpan middleQuotient shear))
    (next_inside : insideShearedSpan (shearedPairSpan middleQuotient shear : Int)
      (.double, next)) :
    2 * shearedPairBridge middleQuotient shear + 2 * (3 * middleQuotient + 2) +
        shearedCenteredGap middleQuotient shear
          (.triple, 3 * next - shearedPairSpan middleQuotient shear) + 2 =
      shearedCenteredCount middleQuotient shear next * 3 := by
  rw [← Int.ofNat_inj]
  simp only [Int.natCast_add, Int.natCast_mul]
  rw [shearedCenteredGap_cast middleQuotient shear current_inside,
    shearedCenteredCount_cast middleQuotient shear next_inside]
  simp [shearedTripleCenter, shearedPairBridge, shearedPairSpan]
  omega

private theorem shearedCenteredDoubleTargetGap (shear separation middleQuotient : Nat)
    (defect : Int)
    (middle_eq : separation + shear = 3 * middleQuotient + 2)
    (state_inside : insideShearedSpan (shearedPairSpan middleQuotient shear : Int)
      (.double, defect)) :
    separation + 3 * shear + 1 + shearedCenteredCount middleQuotient shear defect =
      shearedCenteredGap middleQuotient shear (.double, defect) := by
  rw [← Int.ofNat_inj]
  simp only [Int.natCast_add]
  rw [shearedCenteredCount_cast middleQuotient shear state_inside,
    shearedCenteredGap_cast middleQuotient shear state_inside]
  simp [shearedDoubleCenter, shearedPairBridge]
  omega

private theorem shearedCenteredTripleTargetGap (shear separation middleQuotient : Nat)
    (defect : Int)
    (middle_eq : separation + shear = 3 * middleQuotient + 2)
    (state_inside : insideShearedSpan (shearedPairSpan middleQuotient shear : Int)
      (.triple, defect)) :
    separation + 3 * shear + 3 + shearedCenteredCount middleQuotient shear defect =
      shearedCenteredGap middleQuotient shear (.triple, defect) := by
  rw [← Int.ofNat_inj]
  simp only [Int.natCast_add]
  rw [shearedCenteredCount_cast middleQuotient shear state_inside,
    shearedCenteredGap_cast middleQuotient shear state_inside]
  simp [shearedTripleCenter, shearedPairBridge]
  omega

private theorem shearedCenteredStep_reaches (shear separation middleQuotient : Nat)
    (middle_eq : separation + shear = 3 * middleQuotient + 2)
    (phase_nonzero : (middleQuotient + 2 * shear) % 3 ≠ 0)
    {next current : ShearedCenteredState}
    (current_inside : insideShearedSpan (shearedPairSpan middleQuotient shear : Int) current)
    (step : ShearedCenteredStep (shearedPairSpan middleQuotient shear : Int) next current) :
    TagReaches 3 (tagOutput (shearedBody shear separation))
      (shearedCenteredPairQueue shear separation middleQuotient current)
      (shearedCenteredPairQueue shear separation middleQuotient next) := by
  have span_pos : 0 < (shearedPairSpan middleQuotient shear : Int) := by
    simp [shearedPairSpan]
    omega
  have next_inside := shearedCenteredStep_inside span_pos current_inside step
  cases step with
  | doubleIdle nextDefect =>
      have count_eq := shearedDoubleIdle_count middleQuotient shear nextDefect
        current_inside next_inside
      have target_eq := shearedCenteredDoubleTargetGap shear separation middleQuotient
        nextDefect middle_eq next_inside
      have reach := shearedDoubleIdle_reaches shear separation middleQuotient
        (shearedCenteredGap middleQuotient shear (.double, 3 * nextDefect))
        (shearedCenteredCount middleQuotient shear nextDefect) middle_eq phase_nonzero count_eq
      rw [target_eq] at reach
      simpa [shearedCenteredPairQueue] using reach
  | doubleCross nextDefect =>
      have count_eq := shearedDoubleCross_count middleQuotient shear nextDefect
        current_inside next_inside
      have target_eq := shearedCenteredTripleTargetGap shear separation middleQuotient
        nextDefect middle_eq next_inside
      have reach := shearedDoubleCross_reaches shear separation middleQuotient
        (shearedCenteredGap middleQuotient shear
          (.double, 3 * nextDefect + shearedPairSpan middleQuotient shear))
        (shearedCenteredCount middleQuotient shear nextDefect) middle_eq count_eq
      rw [target_eq] at reach
      simpa [shearedCenteredPairQueue] using reach
  | tripleIdle nextDefect =>
      have count_eq := shearedTripleIdle_count middleQuotient shear nextDefect
        current_inside next_inside
      have target_eq := shearedCenteredTripleTargetGap shear separation middleQuotient
        nextDefect middle_eq next_inside
      have reach := shearedTripleIdle_reaches shear separation middleQuotient
        (shearedCenteredGap middleQuotient shear (.triple, 3 * nextDefect))
        (shearedCenteredCount middleQuotient shear nextDefect) middle_eq phase_nonzero count_eq
      rw [target_eq] at reach
      simpa [shearedCenteredPairQueue] using reach
  | tripleCross nextDefect =>
      have count_eq := shearedTripleCross_count middleQuotient shear nextDefect
        current_inside next_inside
      have target_eq := shearedCenteredDoubleTargetGap shear separation middleQuotient
        nextDefect middle_eq next_inside
      have reach := shearedTripleCross_reaches shear separation middleQuotient
        (shearedCenteredGap middleQuotient shear
          (.triple, 3 * nextDefect - shearedPairSpan middleQuotient shear))
        (shearedCenteredCount middleQuotient shear nextDefect) middle_eq phase_nonzero count_eq
      rw [target_eq] at reach
      simpa [shearedCenteredPairQueue] using reach

private theorem shearedDoublePair_clean
    (shear separation middleQuotient outerGap : Nat)
    (near_inert : outerGap % 3 ≠ 0)
    (far_inert : (outerGap + shearedPairSpan middleQuotient shear) % 3 ≠ 0) :
    Undecidability.ConstantAtMultiples 3 TagLetter.b
      (shearedDoublePairQueue shear separation middleQuotient outerGap) := by
  have clean : ConstantAtOffset 0
      (shearedDoublePairQueue shear separation middleQuotient outerGap) := by
    unfold shearedDoublePairQueue
    simp only [List.singleton_append, List.append_assoc]
    apply constantAtOffset_bRun_c
    · rw [Nat.dvd_iff_mod_eq_zero]
      simpa using near_inert
    · apply constantAtOffset_bRun_c
      · rw [Nat.dvd_iff_mod_eq_zero]
        omega
      · apply constantAtOffset_bRun_c
        · rw [Nat.dvd_iff_mod_eq_zero]
          simp [shearedPairBridge, shearedPairSpan] at far_inert ⊢
          omega
        · apply constantAtOffset_bRun_c
          · rw [Nat.dvd_iff_mod_eq_zero]
            simp [shearedPairBridge, shearedPairSpan] at far_inert ⊢
            omega
          · exact constantAtOffset_replicate _ _
  simpa [ConstantAtOffset, Undecidability.ConstantAtMultiples] using clean

private theorem shearedTriplePair_clean
    (shear separation middleQuotient middleGap : Nat)
    (phase_nonzero : (middleQuotient + 2 * shear) % 3 ≠ 0)
    (middle_inert : (shearedPairBridge middleQuotient shear +
      (3 * middleQuotient + 2) + middleGap) % 3 ≠ 0)
    (far_inert : (shearedPairBridge middleQuotient shear +
      (3 * middleQuotient + 2) + middleGap +
        shearedPairSpan middleQuotient shear) % 3 ≠ 0) :
    Undecidability.ConstantAtMultiples 3 TagLetter.b
      (shearedTriplePairQueue shear separation middleQuotient middleGap) := by
  have clean : ConstantAtOffset 0
      (shearedTriplePairQueue shear separation middleQuotient middleGap) := by
    unfold shearedTriplePairQueue
    simp only [List.singleton_append, List.append_assoc]
    apply constantAtOffset_bRun_c
    · rw [Nat.dvd_iff_mod_eq_zero]
      omega
    · apply constantAtOffset_bRun_c
      · rw [Nat.dvd_iff_mod_eq_zero]
        omega
      · apply constantAtOffset_bRun_c
        · rw [Nat.dvd_iff_mod_eq_zero]
          simp [shearedPairBridge] at middle_inert ⊢
          omega
        · apply constantAtOffset_bRun_c
          · rw [Nat.dvd_iff_mod_eq_zero]
            simp [shearedPairBridge] at middle_inert ⊢
            omega
          · apply constantAtOffset_bRun_c
            · rw [Nat.dvd_iff_mod_eq_zero]
              simp [shearedPairBridge, shearedPairSpan] at far_inert ⊢
              omega
            · apply constantAtOffset_bRun_c
              · rw [Nat.dvd_iff_mod_eq_zero]
                simp [shearedPairBridge, shearedPairSpan] at far_inert ⊢
                omega
              · exact constantAtOffset_replicate _ _
  simpa [ConstantAtOffset, Undecidability.ConstantAtMultiples] using clean

private theorem shearedDoublePair_terminal
    (shear separation middleQuotient outerGap : Nat)
    (near_inert : outerGap % 3 ≠ 0)
    (far_inert : (outerGap + shearedPairSpan middleQuotient shear) % 3 ≠ 0) :
    TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
      (shearedDoublePairQueue shear separation middleQuotient outerGap) :=
  Undecidability.tagHaltsFrom_of_constantAtMultiples 3 (by omega)
    (tagOutput (shearedBody shear separation)) TagLetter.b rfl
    (shearedDoublePairQueue shear separation middleQuotient outerGap)
    (shearedDoublePair_clean shear separation middleQuotient outerGap near_inert far_inert)

private theorem shearedTriplePair_terminal
    (shear separation middleQuotient middleGap : Nat)
    (phase_nonzero : (middleQuotient + 2 * shear) % 3 ≠ 0)
    (middle_inert : (shearedPairBridge middleQuotient shear +
      (3 * middleQuotient + 2) + middleGap) % 3 ≠ 0)
    (far_inert : (shearedPairBridge middleQuotient shear +
      (3 * middleQuotient + 2) + middleGap +
        shearedPairSpan middleQuotient shear) % 3 ≠ 0) :
    TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
      (shearedTriplePairQueue shear separation middleQuotient middleGap) :=
  Undecidability.tagHaltsFrom_of_constantAtMultiples 3 (by omega)
    (tagOutput (shearedBody shear separation)) TagLetter.b rfl
    (shearedTriplePairQueue shear separation middleQuotient middleGap)
    (shearedTriplePair_clean shear separation middleQuotient middleGap phase_nonzero
      middle_inert far_inert)

private theorem shearedCenteredDouble_terminal
    (shear separation middleQuotient : Nat) (defect : Int)
    (state_inside : insideShearedSpan (shearedPairSpan middleQuotient shear : Int)
      (.double, defect))
    (no_idle : ¬∃ next : Int, defect = 3 * next)
    (no_cross : ¬∃ next : Int,
      defect = 3 * next + shearedPairSpan middleQuotient shear) :
    TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
      (shearedCenteredPairQueue shear separation middleQuotient (.double, defect)) := by
  let base := 5 * middleQuotient + 2 * shear + 6
  let outerGap := shearedCenteredGap middleQuotient shear (.double, defect)
  have outerGap_cast : (outerGap : Int) =
      (shearedDoubleCenter middleQuotient shear : Int) + defect := by
    exact shearedCenteredGap_cast middleQuotient shear state_inside
  have near_inert : outerGap % 3 ≠ 0 := by
    intro zero
    obtain ⟨quotient, quotient_eq⟩ :=
      (Nat.dvd_iff_mod_eq_zero.mpr zero : 3 ∣ outerGap)
    apply no_cross
    refine ⟨(quotient : Int) - (base : Int), ?_⟩
    have quotient_eq' := congrArg (fun number : Nat => (number : Int)) quotient_eq
    simp only [Int.natCast_mul] at quotient_eq'
    rw [outerGap_cast] at quotient_eq'
    simp [base, shearedDoubleCenter, shearedPairBridge, shearedPairSpan] at quotient_eq' ⊢
    omega
  have far_inert : (outerGap + shearedPairSpan middleQuotient shear) % 3 ≠ 0 := by
    intro zero
    obtain ⟨quotient, quotient_eq⟩ :=
      (Nat.dvd_iff_mod_eq_zero.mpr zero :
        3 ∣ outerGap + shearedPairSpan middleQuotient shear)
    apply no_idle
    refine ⟨(quotient : Int) - (base : Int), ?_⟩
    have quotient_eq' := congrArg (fun number : Nat => (number : Int)) quotient_eq
    simp only [Int.natCast_add, Int.natCast_mul] at quotient_eq'
    rw [outerGap_cast] at quotient_eq'
    simp [base, shearedDoubleCenter, shearedPairBridge, shearedPairSpan] at quotient_eq' ⊢
    omega
  exact shearedDoublePair_terminal shear separation middleQuotient outerGap
    near_inert far_inert

private theorem shearedCenteredTriple_terminal
    (shear separation middleQuotient : Nat) (defect : Int)
    (phase_nonzero : (middleQuotient + 2 * shear) % 3 ≠ 0)
    (state_inside : insideShearedSpan (shearedPairSpan middleQuotient shear : Int)
      (.triple, defect))
    (no_idle : ¬∃ next : Int, defect = 3 * next)
    (no_cross : ¬∃ next : Int,
      defect = 3 * next - shearedPairSpan middleQuotient shear) :
    TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
      (shearedCenteredPairQueue shear separation middleQuotient (.triple, defect)) := by
  let base := 5 * middleQuotient + 2 * shear + 6
  let middleGap := shearedCenteredGap middleQuotient shear (.triple, defect)
  have middleGap_cast : (middleGap : Int) =
      (shearedTripleCenter middleQuotient shear : Int) + defect := by
    exact shearedCenteredGap_cast middleQuotient shear state_inside
  have middle_inert : (shearedPairBridge middleQuotient shear +
      (3 * middleQuotient + 2) + middleGap) % 3 ≠ 0 := by
    intro zero
    obtain ⟨quotient, quotient_eq⟩ :=
      (Nat.dvd_iff_mod_eq_zero.mpr zero : 3 ∣ shearedPairBridge middleQuotient shear +
        (3 * middleQuotient + 2) + middleGap)
    apply no_idle
    refine ⟨(quotient : Int) - (base : Int), ?_⟩
    have quotient_eq' := congrArg (fun number : Nat => (number : Int)) quotient_eq
    simp only [Int.natCast_add, Int.natCast_mul] at quotient_eq'
    rw [middleGap_cast] at quotient_eq'
    simp [base, shearedTripleCenter, shearedPairBridge] at quotient_eq' ⊢
    omega
  have far_inert : (shearedPairBridge middleQuotient shear +
      (3 * middleQuotient + 2) + middleGap +
        shearedPairSpan middleQuotient shear) % 3 ≠ 0 := by
    intro zero
    obtain ⟨quotient, quotient_eq⟩ :=
      (Nat.dvd_iff_mod_eq_zero.mpr zero : 3 ∣ shearedPairBridge middleQuotient shear +
        (3 * middleQuotient + 2) + middleGap +
          shearedPairSpan middleQuotient shear)
    apply no_cross
    refine ⟨(quotient : Int) - (base : Int), ?_⟩
    have quotient_eq' := congrArg (fun number : Nat => (number : Int)) quotient_eq
    simp only [Int.natCast_add, Int.natCast_mul] at quotient_eq'
    rw [middleGap_cast] at quotient_eq'
    simp [base, shearedTripleCenter, shearedPairBridge, shearedPairSpan] at quotient_eq' ⊢
    omega
  exact shearedTriplePair_terminal shear separation middleQuotient middleGap phase_nonzero
    middle_inert far_inert

private theorem shearedCenteredState_outcome
    (shear separation middleQuotient : Nat)
    (middle_eq : separation + shear = 3 * middleQuotient + 2)
    (phase_nonzero : (middleQuotient + 2 * shear) % 3 ≠ 0)
    (state : ShearedCenteredState)
    (state_inside : insideShearedSpan (shearedPairSpan middleQuotient shear : Int) state) :
    TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
        (shearedCenteredPairQueue shear separation middleQuotient state) ∨
      ∃ next, ShearedCenteredStep (shearedPairSpan middleQuotient shear : Int) next state ∧
        TagReaches 3 (tagOutput (shearedBody shear separation))
          (shearedCenteredPairQueue shear separation middleQuotient state)
          (shearedCenteredPairQueue shear separation middleQuotient next) := by
  classical
  rcases state with ⟨mode, defect⟩
  cases mode with
  | double =>
      by_cases idle : ∃ next : Int, defect = 3 * next
      · obtain ⟨nextDefect, defect_eq⟩ := idle
        let next : ShearedCenteredState := (.double, nextDefect)
        have step : ShearedCenteredStep (shearedPairSpan middleQuotient shear : Int)
            next (.double, defect) := by
          simpa [next, defect_eq] using
            (ShearedCenteredStep.doubleIdle
              (span := (shearedPairSpan middleQuotient shear : Int)) nextDefect)
        exact Or.inr ⟨next, step, shearedCenteredStep_reaches shear separation middleQuotient
          middle_eq phase_nonzero state_inside step⟩
      · by_cases cross : ∃ next : Int,
          defect = 3 * next + shearedPairSpan middleQuotient shear
        · obtain ⟨nextDefect, defect_eq⟩ := cross
          let next : ShearedCenteredState := (.triple, nextDefect)
          have step : ShearedCenteredStep (shearedPairSpan middleQuotient shear : Int)
              next (.double, defect) := by
            simpa [next, defect_eq] using
              (ShearedCenteredStep.doubleCross
                (span := (shearedPairSpan middleQuotient shear : Int)) nextDefect)
          exact Or.inr ⟨next, step, shearedCenteredStep_reaches shear separation middleQuotient
            middle_eq phase_nonzero state_inside step⟩
        · exact Or.inl (shearedCenteredDouble_terminal shear separation middleQuotient defect
            state_inside idle cross)
  | triple =>
      by_cases idle : ∃ next : Int, defect = 3 * next
      · obtain ⟨nextDefect, defect_eq⟩ := idle
        let next : ShearedCenteredState := (.triple, nextDefect)
        have step : ShearedCenteredStep (shearedPairSpan middleQuotient shear : Int)
            next (.triple, defect) := by
          simpa [next, defect_eq] using
            (ShearedCenteredStep.tripleIdle
              (span := (shearedPairSpan middleQuotient shear : Int)) nextDefect)
        exact Or.inr ⟨next, step, shearedCenteredStep_reaches shear separation middleQuotient
          middle_eq phase_nonzero state_inside step⟩
      · by_cases cross : ∃ next : Int,
          defect = 3 * next - shearedPairSpan middleQuotient shear
        · obtain ⟨nextDefect, defect_eq⟩ := cross
          let next : ShearedCenteredState := (.double, nextDefect)
          have step : ShearedCenteredStep (shearedPairSpan middleQuotient shear : Int)
              next (.triple, defect) := by
            simpa [next, defect_eq] using
              (ShearedCenteredStep.tripleCross
                (span := (shearedPairSpan middleQuotient shear : Int)) nextDefect)
          exact Or.inr ⟨next, step, shearedCenteredStep_reaches shear separation middleQuotient
            middle_eq phase_nonzero state_inside step⟩
        · exact Or.inl (shearedCenteredTriple_terminal shear separation middleQuotient defect
            phase_nonzero state_inside idle cross)

private theorem shearedCenteredState_halts
    (shear separation middleQuotient : Nat)
    (middle_eq : separation + shear = 3 * middleQuotient + 2)
    (phase_nonzero : (middleQuotient + 2 * shear) % 3 ≠ 0)
    (state : ShearedCenteredState)
    (state_inside : insideShearedSpan (shearedPairSpan middleQuotient shear : Int) state)
    (accessible : Acc (ShearedCenteredStep (shearedPairSpan middleQuotient shear : Int)) state) :
    TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
      (shearedCenteredPairQueue shear separation middleQuotient state) := by
  refine accessible.rec (motive := fun current _ =>
    insideShearedSpan (shearedPairSpan middleQuotient shear : Int) current →
      TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
        (shearedCenteredPairQueue shear separation middleQuotient current)) ?_ state_inside
  intro current _ downstream current_inside
  rcases shearedCenteredState_outcome shear separation middleQuotient middle_eq phase_nonzero
      current current_inside with terminal | ⟨next, step, reach⟩
  · exact terminal
  · have next_inside := shearedCenteredStep_inside
      (by simp [shearedPairSpan]; omega) current_inside step
    exact Undecidability.tagHaltsFrom_of_reaches reach (downstream next step next_inside)

/-- The positive distance of a complementary residual from the triple-pair center. -/
def shearedComplementaryDefect (phase k u : Nat) : Nat :=
  4 * k + u + phase + 2

/-- The positive distance of a shear-residue-two residual from the double-pair center. -/
def shearedShearResidueTwoDefect (phase k u : Nat) : Nat :=
  3 * k + u + phase + 2

/-- The complementary residual defect lies strictly in the central predecessor-image gap. -/
theorem shearedComplementaryDefect_imageGap
    (phase shear k u : Nat) (shear_eq : shear + phase = 3 * u + 1) :
    shearedPairSpan (3 * k + phase) shear <
        9 * shearedComplementaryDefect phase k u ∧
      9 * shearedComplementaryDefect phase k u <
        2 * shearedPairSpan (3 * k + phase) shear := by
  simp [shearedPairSpan, shearedComplementaryDefect] at shear_eq ⊢
  omega

/-- The shear-residue-two residual defect lies strictly in the central predecessor-image gap. -/
theorem shearedShearResidueTwoDefect_imageGap
    (phase shear k u : Nat) (shear_eq : shear = 3 * u + 2) :
    shearedPairSpan (3 * k + phase) shear <
        9 * shearedShearResidueTwoDefect phase k u ∧
      9 * shearedShearResidueTwoDefect phase k u <
        2 * shearedPairSpan (3 * k + phase) shear := by
  simp [shearedPairSpan, shearedShearResidueTwoDefect] at shear_eq ⊢
  omega

/-- The complementary six-`c` residual is exactly the negative-defect triple-pair normal form. -/
theorem shearedComplementaryResidual_eq_centered
    (phase shear separation k u : Nat) (shear_eq : shear + phase = 3 * u + 1) :
    shearedComplementaryResidual phase separation k u =
      shearedCenteredPairQueue shear separation (3 * k + phase)
        (.triple, -(shearedComplementaryDefect phase k u : Int)) := by
  have leadingGap_eq : 4 * (3 * k + phase) + 2 * shear + 3 =
      12 * k + 6 * u + 2 * phase + 5 := by omega
  have middleRun_eq : 3 * (3 * k + phase) + 2 = 9 * k + 3 * phase + 2 := by
    omega
  have bridge_eq : shearedPairBridge (3 * k + phase) shear =
      12 * k + 6 * u + 2 * phase + 7 := by
    simp [shearedPairBridge]
    omega
  have middleGap_eq :
      shearedCenteredGap (3 * k + phase) shear
          (.triple, -(shearedComplementaryDefect phase k u : Int)) =
        20 * k + 11 * u + 3 * phase + 13 := by
    unfold shearedCenteredGap
    have nonnegative : 0 ≤ (shearedTripleCenter (3 * k + phase) shear : Int) +
        -(shearedComplementaryDefect phase k u : Int) := by
      simp [shearedTripleCenter, shearedPairBridge, shearedComplementaryDefect]
      omega
    rw [← Int.ofNat_inj]
    rw [Int.toNat_of_nonneg nonnegative]
    simp [shearedTripleCenter, shearedPairBridge, shearedComplementaryDefect]
    omega
  simp [shearedComplementaryResidual, shearedCenteredPairQueue,
    shearedTriplePairQueue, leadingGap_eq, middleRun_eq, bridge_eq, middleGap_eq]

/-- The shear-residue-two four-`c` residual is exactly the positive-defect double-pair normal
form. -/
theorem shearedShearResidueTwoResidual_eq_centered
    (phase shear separation k u : Nat) (shear_eq : shear = 3 * u + 2) :
    shearedShearResidueTwoResidual phase separation k u =
      shearedCenteredPairQueue shear separation (3 * k + phase)
        (.double, (shearedShearResidueTwoDefect phase k u : Int)) := by
  have middleRun_eq : 3 * (3 * k + phase) + 2 = 9 * k + 3 * phase + 2 := by
    omega
  have bridge_eq : shearedPairBridge (3 * k + phase) shear =
      12 * k + 6 * u + 4 * phase + 9 := by
    simp [shearedPairBridge]
    omega
  have outerGap_eq :
      shearedCenteredGap (3 * k + phase) shear
          (.double, (shearedShearResidueTwoDefect phase k u : Int)) =
        27 * k + 13 * u + 9 * phase + 19 := by
    unfold shearedCenteredGap
    have nonnegative : 0 ≤ (shearedDoubleCenter (3 * k + phase) shear : Int) +
        (shearedShearResidueTwoDefect phase k u : Int) := by
      simp [shearedDoubleCenter, shearedPairBridge, shearedShearResidueTwoDefect]
      omega
    rw [← Int.ofNat_inj]
    rw [Int.toNat_of_nonneg nonnegative]
    simp [shearedDoubleCenter, shearedPairBridge, shearedShearResidueTwoDefect]
    omega
  simp [shearedShearResidueTwoResidual, shearedCenteredPairQueue,
    shearedDoublePairQueue, middleRun_eq, bridge_eq, outerGap_eq]

/-- Every complementary residual halts, including the two joint phases left open by the direct
six-active-`c` drainage theorem. -/
theorem shearedComplementaryResidual_tagHaltsFrom
    (phase shear separation k u : Nat)
    (phase_lt : phase < 2)
    (shear_eq : shear + phase = 3 * u + 1)
    (middle_eq : separation + shear = 9 * k + 3 * phase + 2) :
    TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
      (shearedComplementaryResidual phase separation k u) := by
  let middleQuotient := 3 * k + phase
  let defect := shearedComplementaryDefect phase k u
  have middle_eq' : separation + shear = 3 * middleQuotient + 2 := by
    dsimp [middleQuotient]
    omega
  have phase_nonzero : (middleQuotient + 2 * shear) % 3 ≠ 0 := by
    dsimp [middleQuotient]
    omega
  have state_inside : insideShearedSpan (shearedPairSpan middleQuotient shear : Int)
      (.triple, -(defect : Int)) := by
    simp [insideShearedSpan, middleQuotient, defect, shearedPairSpan,
      shearedComplementaryDefect] at shear_eq ⊢
    omega
  have gap := shearedComplementaryDefect_imageGap phase shear k u shear_eq
  have accessible : Acc (ShearedCenteredStep (shearedPairSpan middleQuotient shear : Int))
      (.triple, -(defect : Int)) := by
    exact shearedCentered_triple_accessible (shearedPairSpan middleQuotient shear) defect
      (by simpa [middleQuotient, defect] using gap.1)
      (by simpa [middleQuotient, defect] using gap.2)
  rw [shearedComplementaryResidual_eq_centered phase shear separation k u shear_eq]
  exact shearedCenteredState_halts shear separation middleQuotient middle_eq' phase_nonzero
    (.triple, -(defect : Int)) state_inside accessible

/-- Every shear-residue-two residual halts, including the two quotient phases left open by the
direct four-`c` drainage theorem. -/
theorem shearedShearResidueTwoResidual_tagHaltsFrom
    (phase shear separation k u : Nat)
    (phase_lt : phase < 2)
    (shear_eq : shear = 3 * u + 2)
    (middle_eq : separation + shear = 9 * k + 3 * phase + 2) :
    TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
      (shearedShearResidueTwoResidual phase separation k u) := by
  let middleQuotient := 3 * k + phase
  let defect := shearedShearResidueTwoDefect phase k u
  have middle_eq' : separation + shear = 3 * middleQuotient + 2 := by
    dsimp [middleQuotient]
    omega
  have phase_nonzero : (middleQuotient + 2 * shear) % 3 ≠ 0 := by
    dsimp [middleQuotient]
    omega
  have state_inside : insideShearedSpan (shearedPairSpan middleQuotient shear : Int)
      (.double, (defect : Int)) := by
    simp [insideShearedSpan, middleQuotient, defect, shearedPairSpan,
      shearedShearResidueTwoDefect]
    omega
  have gap := shearedShearResidueTwoDefect_imageGap phase shear k u shear_eq
  have accessible : Acc (ShearedCenteredStep (shearedPairSpan middleQuotient shear : Int))
      (.double, (defect : Int)) := by
    exact shearedCentered_double_accessible (shearedPairSpan middleQuotient shear) defect
      (by simpa [middleQuotient, defect] using gap.1)
      (by simpa [middleQuotient, defect] using gap.2)
  rw [shearedShearResidueTwoResidual_eq_centered phase shear separation k u shear_eq]
  exact shearedCenteredState_halts shear separation middleQuotient middle_eq' phase_nonzero
    (.double, (defect : Int)) state_inside accessible

/-- Every source in a complementary phase mismatch halts; no joint quotient phase remains. -/
theorem shearedComplementaryMismatch_tagHaltsFrom
    (phase shear separation k u : Nat)
    (phase_lt : phase < 2)
    (shear_eq : shear + phase = 3 * u + 1)
    (middle_eq : separation + shear = 9 * k + 3 * phase + 2) :
    TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
      (shearedInitial shear separation) :=
  shearedInitial_tagHaltsFrom_of_complementaryResidual phase shear separation k u phase_lt
    shear_eq middle_eq
    (shearedComplementaryResidual_tagHaltsFrom phase shear separation k u phase_lt shear_eq
      middle_eq)

/-- Every source in a shear-residue-two phase mismatch halts; no quotient phase remains. -/
theorem shearedShearResidueTwoMismatch_tagHaltsFrom
    (phase shear separation k u : Nat)
    (phase_lt : phase < 2)
    (shear_eq : shear = 3 * u + 2)
    (middle_eq : separation + shear = 9 * k + 3 * phase + 2) :
    TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
      (shearedInitial shear separation) :=
  shearedInitial_tagHaltsFrom_of_shearResidueTwoResidual phase shear separation k u phase_lt
    shear_eq middle_eq
    (shearedShearResidueTwoResidual_tagHaltsFrom phase shear separation k u phase_lt shear_eq
      middle_eq)

/-- Every coupled sheared source whose middle quotient phase differs from the shear phase halts.
This closes all four mismatched phase families over middle residues two and five modulo nine. -/
theorem shearedPhaseMismatch_tagHaltsFrom
    (phase shear separation k : Nat)
    (phase_lt : phase < 2)
    (middle_eq : separation + shear = 9 * k + 3 * phase + 2)
    (phase_mismatch : shear % 3 ≠ phase) :
    TagHaltsFrom 3 (tagOutput (shearedBody shear separation))
      (shearedInitial shear separation) := by
  have phase_cases : phase = 0 ∨ phase = 1 := by omega
  have shear_mod_lt : shear % 3 < 3 := Nat.mod_lt shear (by omega)
  have shear_mod_cases : shear % 3 = 0 ∨ shear % 3 = 1 ∨ shear % 3 = 2 := by omega
  have shear_division := Nat.mod_add_div shear 3
  rcases phase_cases with rfl | rfl
  · rcases shear_mod_cases with shear_mod | shear_mod | shear_mod
    · omega
    · exact shearedComplementaryMismatch_tagHaltsFrom 0 shear separation k (shear / 3)
        (by omega) (by omega) middle_eq
    · exact shearedShearResidueTwoMismatch_tagHaltsFrom 0 shear separation k (shear / 3)
        (by omega) (by omega) middle_eq
  · rcases shear_mod_cases with shear_mod | shear_mod | shear_mod
    · exact shearedComplementaryMismatch_tagHaltsFrom 1 shear separation k (shear / 3)
        (by omega) (by omega) middle_eq
    · omega
    · exact shearedShearResidueTwoMismatch_tagHaltsFrom 1 shear separation k (shear / 3)
        (by omega) (by omega) middle_eq

end MatrixMortality.SeparatedTwoCShear
