import Mathlib.Data.Fintype.Pigeonhole
import MatrixMortality.SeparatedTwoCResidue

/-!
# Cantor-defect drainage for separated two-c tag systems

For the coupled width-three diagonal family `qₙ = bb c bⁿ c bⁿ`, this file proves termination
when `n = 9k+5`. Exact two-active-`c` macros conjugate the surviving queue dynamics to a map on
a finite defect interval. Live defects take one of the two inverse-Cantor branches
`E ↦ E/3` and `E ↦ (E+2H)/3`; residue two drains. Injectivity on the live interval and the
initial defect's location in the open middle third force every orbit to reach the draining
residue.
-/

namespace MatrixMortality.SeparatedTwoCResidue

open PeriodicHistory SeparatedTwoCOrbit Undecidability

/-- Two queues of equal length with the same letters at every width-three deletion head. -/
def HeadEquivalent (left right : List TagLetter) : Prop :=
  left.length = right.length ∧
    ∀ (index : Nat) (left_lt : index < left.length) (right_lt : index < right.length),
      3 ∣ index →
      left[index] = right[index]

theorem HeadEquivalent.symm {left right : List TagLetter}
    (equivalent : HeadEquivalent left right) : HeadEquivalent right left := by
  rcases equivalent with ⟨length_eq, heads_eq⟩
  refine ⟨length_eq.symm, ?_⟩
  intro index right_lt left_lt index_aligned
  exact (heads_eq index left_lt right_lt index_aligned).symm

theorem HeadEquivalent.drop_three {left right : List TagLetter}
    (equivalent : HeadEquivalent left right) :
    HeadEquivalent (left.drop 3) (right.drop 3) := by
  rcases equivalent with ⟨length_eq, heads_eq⟩
  constructor
  · simp [length_eq]
  · intro index left_lt right_lt index_aligned
    rw [List.getElem_drop, List.getElem_drop]
    have left_source_lt : 3 + index < left.length := by
      simp only [List.length_drop] at left_lt
      omega
    have right_source_lt : 3 + index < right.length := by
      simp only [List.length_drop] at right_lt
      omega
    exact heads_eq (3 + index) left_source_lt right_source_lt
      (Nat.dvd_add (Nat.dvd_refl 3) index_aligned)

theorem HeadEquivalent.append_same {left right : List TagLetter}
    (equivalent : HeadEquivalent left right) (suffix : List TagLetter) :
    HeadEquivalent (left ++ suffix) (right ++ suffix) := by
  rcases equivalent with ⟨length_eq, heads_eq⟩
  constructor
  · simp [length_eq]
  · intro index left_total_lt right_total_lt index_aligned
    by_cases in_left : index < left.length
    · have in_right : index < right.length := by omega
      rw [List.getElem_append_left in_left, List.getElem_append_left in_right]
      exact heads_eq index in_left in_right index_aligned
    · have left_le : left.length ≤ index := Nat.le_of_not_gt in_left
      have right_le : right.length ≤ index := by omega
      rw [List.getElem_append_right left_le, List.getElem_append_right right_le]
      simp [length_eq]

theorem HeadEquivalent.trans {left middle right : List TagLetter}
    (left_middle : HeadEquivalent left middle)
    (middle_right : HeadEquivalent middle right) : HeadEquivalent left right := by
  rcases left_middle with ⟨left_length, left_heads⟩
  rcases middle_right with ⟨right_length, right_heads⟩
  constructor
  · exact left_length.trans right_length
  · intro index left_lt right_lt index_aligned
    have middle_lt : index < middle.length := by omega
    exact (left_heads index left_lt middle_lt index_aligned).trans
      (right_heads index middle_lt right_lt index_aligned)

theorem headEquivalent_replace_inert (prior suffix : List TagLetter)
    (inert : ¬3 ∣ prior.length) :
    HeadEquivalent (prior ++ TagLetter.c :: suffix) (prior ++ TagLetter.b :: suffix) := by
  constructor
  · simp
  · intro index left_lt right_lt index_aligned
    by_cases in_prior : index < prior.length
    · rw [List.getElem_append_left in_prior, List.getElem_append_left in_prior]
    · have prior_le : prior.length ≤ index := Nat.le_of_not_gt in_prior
      have prior_ne : index ≠ prior.length := by
        intro index_eq
        exact inert (index_eq ▸ index_aligned)
      have offset_ne : index - prior.length ≠ 0 := by omega
      rw [List.getElem_append_right prior_le, List.getElem_append_right prior_le]
      simp only [List.getElem_cons]
      simp [offset_ne]

theorem HeadEquivalent.next {output : TagLetter → List TagLetter}
    {left right : List TagLetter} (equivalent : HeadEquivalent left right)
    (left_enough : 3 ≤ left.length) (right_enough : 3 ≤ right.length) :
    HeadEquivalent
      (left.drop 3 ++ output (left.get ⟨0, by omega⟩))
      (right.drop 3 ++ output (right.get ⟨0, by omega⟩)) := by
  have head_eq : left.get ⟨0, by omega⟩ = right.get ⟨0, by omega⟩ := by
    rcases equivalent with ⟨_, heads_eq⟩
    exact heads_eq 0 (by omega) (by omega) (Nat.dvd_zero 3)
  rw [head_eq]
  exact (equivalent.drop_three).append_same _

theorem TagHaltsFrom.of_headEquivalent {output : TagLetter → List TagLetter}
    {left right : List TagLetter} (halts : TagHaltsFrom 3 output left)
    (equivalent : HeadEquivalent left right) : TagHaltsFrom 3 output right := by
  induction halts generalizing right with
  | stop short =>
      exact .stop <| by
        rcases equivalent with ⟨length_eq, _⟩
        omega
  | @step left leftNext transition _ induction =>
      have left_enough : 3 ≤ left.length := tagStep_width_le transition
      have right_enough : 3 ≤ right.length := by
        rcases equivalent with ⟨length_eq, _⟩
        omega
      let canonicalLeft :=
        left.drop 3 ++ output (left.get ⟨0, by omega⟩)
      let canonicalRight :=
        right.drop 3 ++ output (right.get ⟨0, by omega⟩)
      have left_step : TagStep 3 output left canonicalLeft :=
        tagStep_one 3 (by omega) output left left_enough
      have right_step : TagStep 3 output right canonicalRight :=
        tagStep_one 3 (by omega) output right right_enough
      have leftNext_eq : leftNext = canonicalLeft :=
        tagStep_deterministic transition left_step
      subst leftNext
      exact .step right_step (induction (equivalent.next left_enough right_enough))

theorem tagHaltsFrom_headEquivalent_iff {output : TagLetter → List TagLetter}
    {left right : List TagLetter} (equivalent : HeadEquivalent left right) :
    TagHaltsFrom 3 output left ↔ TagHaltsFrom 3 output right :=
  ⟨fun halts => TagHaltsFrom.of_headEquivalent halts equivalent,
    fun halts => TagHaltsFrom.of_headEquivalent halts equivalent.symm⟩

def pairQueue (A tail : Nat) : List TagLetter :=
  [TagLetter.c] ++ bRun (3 * A - 1) ++ [TagLetter.c] ++ bRun tail

def afterPair (A tail : Nat) : List TagLetter :=
  bRun tail ++ [TagLetter.c] ++ bRun (3 * A - 1) ++ [TagLetter.c] ++
    bRun (4 * A + 1) ++ [TagLetter.c] ++ bRun (3 * A - 1) ++
      [TagLetter.c] ++ bRun (3 * A)

private def pairHistory (A : Nat) : List (Stroke TagLetter 3) :=
  [strokeCBB] ++ List.replicate (A - 1) strokeBBB ++ [strokeCBB]

theorem pairQueue_reaches_afterPair (A tail : Nat) (A_pos : 0 < A) (tail_two : 2 ≤ tail) :
    TagReaches 3 (tagOutput (separatedBody (3 * A - 1)))
      (pairQueue A tail) (afterPair A tail) := by
  have reach := tagReachesIn_history (tagOutput (separatedBody (3 * A - 1)))
    (pairHistory A) (bRun (tail - 2))
  have source_eq :
      consumed (pairHistory A) ++ bRun (tail - 2) = pairQueue A tail := by
    simp [pairHistory, pairQueue, strokeCBB, stroke₃, Stroke.letters, bRun,
      List.append_assoc]
    have firstRun : 3 * (A - 1) + 1 + 1 = 3 * A - 1 := by omega
    have lastRun : tail - 2 + 1 + 1 = tail := by omega
    rw [firstRun, lastRun]
  have target_eq :
      bRun (tail - 2) ++
          produced (tagOutput (separatedBody (3 * A - 1))) (pairHistory A) =
        afterPair A tail := by
    simp [pairHistory, afterPair, separatedBody, strokeCBB, stroke₃, tagOutput, nearyBody,
      bRun, List.append_assoc]
    have firstRun : tail - 2 + 1 + 1 = tail := by omega
    have middleRun : 3 * A - 1 + 1 + (A - 1 + 1 + 1) = 4 * A + 1 := by omega
    have lastRun : 3 * A - 1 + 1 = 3 * A := by omega
    rw [firstRun, middleRun, lastRun]
  rw [source_eq, target_eq] at reach
  exact reach.toReaches

def zeroAfter (A g : Nat) : List TagLetter :=
  [TagLetter.c] ++ bRun (3 * A - 1) ++ [TagLetter.c] ++ bRun (4 * A + 1) ++
    [TagLetter.c] ++ bRun (3 * A - 1) ++ [TagLetter.c] ++ bRun (3 * A + g)

theorem afterPair_zero_reaches (A g : Nat) :
    TagReaches 3 (tagOutput (separatedBody (3 * A - 1)))
      (afterPair A (3 * g)) (zeroAfter A g) := by
  let tailWord :=
    [TagLetter.c] ++ bRun (3 * A - 1) ++ [TagLetter.c] ++ bRun (4 * A + 1) ++
      [TagLetter.c] ++ bRun (3 * A - 1) ++ [TagLetter.c] ++ bRun (3 * A)
  have reach := tagReachesIn_history (tagOutput (separatedBody (3 * A - 1)))
    (List.replicate g strokeBBB) tailWord
  have source_eq :
      consumed (List.replicate g strokeBBB) ++ tailWord = afterPair A (3 * g) := by
    simp [tailWord, afterPair, bRun, List.append_assoc]
  have target_eq :
      tailWord ++ produced (tagOutput (separatedBody (3 * A - 1)))
          (List.replicate g strokeBBB) = zeroAfter A g := by
    simp [tailWord, zeroAfter, bRun, List.append_assoc]
  rw [source_eq, target_eq] at reach
  exact reach.toReaches

theorem zeroAfter_headEquivalent (A g : Nat) (A_mod : A % 3 = 2) :
    HeadEquivalent (zeroAfter A g) (pairQueue A (10 * A + g + 2)) := by
  let prior₃ :=
    [TagLetter.c] ++ bRun (3 * A - 1) ++ [TagLetter.c] ++ bRun (4 * A + 1)
  let suffix₃ := bRun (3 * A - 1) ++ [TagLetter.c] ++ bRun (3 * A + g)
  have prior₃_inert : ¬3 ∣ prior₃.length := by
    rw [Nat.dvd_iff_mod_eq_zero]
    simp [prior₃, bRun]
    omega
  have firstReplacement := headEquivalent_replace_inert prior₃ suffix₃ prior₃_inert
  let prior₄ := prior₃ ++ TagLetter.b :: bRun (3 * A - 1)
  let suffix₄ := bRun (3 * A + g)
  have prior₄_inert : ¬3 ∣ prior₄.length := by
    rw [Nat.dvd_iff_mod_eq_zero]
    simp [prior₄, prior₃, bRun]
    omega
  have secondReplacement := headEquivalent_replace_inert prior₄ suffix₄ prior₄_inert
  have firstReplacement' :
      HeadEquivalent (prior₃ ++ TagLetter.c :: suffix₃)
        (prior₄ ++ TagLetter.c :: suffix₄) := by
    simpa [prior₄, suffix₃, suffix₄, List.append_assoc] using firstReplacement
  have combined := firstReplacement'.trans secondReplacement
  have A_two : 2 ≤ A := by
    have A_bound : A % 3 < 3 := Nat.mod_lt A (by omega)
    omega
  have tail_eq :
      4 * A + 1 + (3 * A - 1 + 1) + (3 * A + g + 1) = 10 * A + g + 2 := by
    omega
  simpa [zeroAfter, pairQueue, prior₃, suffix₃, prior₄, suffix₄, bRun,
    List.append_assoc, tail_eq] using combined

private def twoHistory (a g : Nat) : List (Stroke TagLetter 3) :=
  List.replicate g strokeBBB ++ [strokeBBC] ++
    List.replicate (3 * a + 1) strokeBBB ++ [strokeBBC] ++
      List.replicate (4 * a + 3) strokeBBB

theorem afterPair_two_reaches (a g : Nat) :
    TagReaches 3 (tagOutput (separatedBody (3 * (3 * a + 2) - 1)))
      (afterPair (3 * a + 2) (3 * g + 2))
      (pairQueue (3 * a + 2) (16 * a + g + 12)) := by
  let tailWord :=
    [TagLetter.c] ++ bRun (3 * (3 * a + 2) - 1) ++ [TagLetter.c] ++
      bRun (3 * (3 * a + 2))
  have reach := tagReachesIn_history
    (tagOutput (separatedBody (3 * (3 * a + 2) - 1))) (twoHistory a g) tailWord
  have source_eq :
      consumed (twoHistory a g) ++ tailWord = afterPair (3 * a + 2) (3 * g + 2) := by
    simp [twoHistory, tailWord, afterPair, strokeBBC, stroke₃, Stroke.letters, bRun,
      List.append_assoc]
    have secondRun : 3 * (3 * a + 1) + 1 + 1 = 3 * (3 * a + 2) - 1 := by omega
    have thirdRun : 3 * (4 * a + 3) = 4 * (3 * a + 2) + 1 := by omega
    rw [secondRun, thirdRun]
  have target_eq :
      tailWord ++ produced (tagOutput (separatedBody (3 * (3 * a + 2) - 1)))
          (twoHistory a g) = pairQueue (3 * a + 2) (16 * a + g + 12) := by
    simp [twoHistory, tailWord, pairQueue, strokeBBC, stroke₃, tagOutput, nearyBody, bRun,
      List.append_assoc]
    omega
  rw [source_eq, target_eq] at reach
  exact reach.toReaches

private def deathQueue (a g : Nat) : List TagLetter :=
  bRun (3 * g) ++ ([.b, .c, .b] ++
    (bRun (9 * a + 3) ++ ([.b, .c, .b] ++
    (bRun (12 * a + 6) ++ ([.b, .b, .c] ++
    (bRun (9 * a + 3) ++ ([.b, .b, .c] ++
      bRun (9 * a + 6))))))))

private theorem afterPair_one_eq_death (a g : Nat) :
    afterPair (3 * a + 2) (3 * g + 1) = deathQueue a g := by
  simp [afterPair, deathQueue, bRun, List.append_assoc]
  have shortRun : 3 * (3 * a + 2) - 1 = 9 * a + 3 + 1 + 1 := by omega
  have longRun : 4 * (3 * a + 2) + 1 = 12 * a + 6 + 1 + 1 + 1 := by omega
  have finalRun : 3 * (3 * a + 2) = 9 * a + 6 := by omega
  rw [shortRun, longRun, finalRun]

private theorem clean_triple (middle last : TagLetter) :
    ConstantAtMultiples 3 TagLetter.b [TagLetter.b, middle, last] := by
  intro index index_lt index_aligned
  simp only [List.length_cons, List.length_nil] at index_lt
  have index_zero : index = 0 := by omega
  subst index
  rfl

private theorem deathQueue_clean (a g : Nat) :
    ConstantAtMultiples 3 TagLetter.b (deathQueue a g) := by
  unfold deathQueue
  refine ConstantAtMultiples.append (ConstantAtMultiples.replicate 3 _ TagLetter.b) ?_ ?_
  · refine ConstantAtMultiples.append (clean_triple .c .b) ?_ (by decide)
    refine ConstantAtMultiples.append (ConstantAtMultiples.replicate 3 _ TagLetter.b) ?_ ?_
    · refine ConstantAtMultiples.append (clean_triple .c .b) ?_ (by decide)
      refine ConstantAtMultiples.append (ConstantAtMultiples.replicate 3 _ TagLetter.b) ?_ ?_
      · refine ConstantAtMultiples.append (clean_triple .b .c) ?_ (by decide)
        refine ConstantAtMultiples.append (ConstantAtMultiples.replicate 3 _ TagLetter.b) ?_ ?_
        · refine ConstantAtMultiples.append (clean_triple .b .c)
            (ConstantAtMultiples.replicate 3 _ TagLetter.b) (by decide)
        · simp only [bRun, List.length_replicate]
          exact ⟨3 * a + 1, by omega⟩
      · simp only [bRun, List.length_replicate]
        exact ⟨4 * a + 2, by omega⟩
    · simp only [bRun, List.length_replicate]
      exact ⟨3 * a + 1, by omega⟩
  · simp only [bRun, List.length_replicate]
    exact ⟨g, by omega⟩

theorem afterPair_one_halts (a g : Nat) :
    TagHaltsFrom 3 (tagOutput (separatedBody (3 * (3 * a + 2) - 1)))
      (afterPair (3 * a + 2) (3 * g + 1)) := by
  rw [afterPair_one_eq_death]
  exact tagHaltsFrom_of_constantAtMultiples 3 (by omega)
    (tagOutput (separatedBody (3 * (3 * a + 2) - 1))) TagLetter.b rfl
    (deathQueue a g) (deathQueue_clean a g)

private theorem pairQueue_zero_halts (a g : Nat) (g_pos : 0 < g)
    (next_halts :
      TagHaltsFrom 3 (tagOutput (separatedBody (3 * (3 * a + 2) - 1)))
        (pairQueue (3 * a + 2) (10 * (3 * a + 2) + g + 2))) :
    TagHaltsFrom 3 (tagOutput (separatedBody (3 * (3 * a + 2) - 1)))
      (pairQueue (3 * a + 2) (3 * g)) := by
  have entry := pairQueue_reaches_afterPair (3 * a + 2) (3 * g) (by omega) (by omega)
  have traverse := afterPair_zero_reaches (3 * a + 2) g
  have equivalent := zeroAfter_headEquivalent (3 * a + 2) g (by omega)
  have actual_halts := (tagHaltsFrom_headEquivalent_iff equivalent).mpr next_halts
  exact tagHaltsFrom_of_reaches entry (tagHaltsFrom_of_reaches traverse actual_halts)

private theorem pairQueue_two_halts (a g : Nat)
    (next_halts :
      TagHaltsFrom 3 (tagOutput (separatedBody (3 * (3 * a + 2) - 1)))
        (pairQueue (3 * a + 2) (16 * a + g + 12))) :
    TagHaltsFrom 3 (tagOutput (separatedBody (3 * (3 * a + 2) - 1)))
      (pairQueue (3 * a + 2) (3 * g + 2)) := by
  have entry := pairQueue_reaches_afterPair (3 * a + 2) (3 * g + 2) (by omega) (by omega)
  have traverse := afterPair_two_reaches a g
  exact tagHaltsFrom_of_reaches entry (tagHaltsFrom_of_reaches traverse next_halts)

private theorem pairQueue_one_halts (a g : Nat) (g_pos : 0 < g) :
    TagHaltsFrom 3 (tagOutput (separatedBody (3 * (3 * a + 2) - 1)))
      (pairQueue (3 * a + 2) (3 * g + 1)) := by
  have entry := pairQueue_reaches_afterPair (3 * a + 2) (3 * g + 1) (by omega) (by omega)
  exact tagHaltsFrom_of_reaches entry (afterPair_one_halts a g)

/-- The two live inverse-Cantor branches on a defect interval of height `H`. -/
def cantorStep (H E : Nat) : Nat :=
  if E % 3 = 0 then E / 3 else (E + 2 * H) / 3

/-- A defect is live until it reaches the draining residue two modulo three. -/
def cantorLive (E : Nat) : Prop := E % 3 ≠ 2

theorem cantorLive_cases {E : Nat} (live : cantorLive E) : E % 3 = 0 ∨ E % 3 = 1 := by
  unfold cantorLive at live
  have bound : E % 3 < 3 := Nat.mod_lt E (by omega)
  omega

theorem cantorStep_eq_of_mod_zero {H E : Nat} (zero : E % 3 = 0) :
    3 * cantorStep H E = E := by
  rw [cantorStep, if_pos zero]
  exact Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr zero)

theorem cantorStep_eq_of_mod_one {H E : Nat} (H_one : H % 3 = 1)
    (one : E % 3 = 1) :
    3 * cantorStep H E = E + 2 * H := by
  rw [cantorStep, if_neg (by omega)]
  have divides : 3 ∣ E + 2 * H := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  exact Nat.mul_div_cancel' divides

theorem cantorStep_pos {H E : Nat} (H_one : H % 3 = 1)
    (E_pos : 0 < E) (live : cantorLive E) :
    0 < cantorStep H E := by
  rcases cantorLive_cases live with zero | one
  · have equation := cantorStep_eq_of_mod_zero (H := H) zero
    omega
  · have equation := cantorStep_eq_of_mod_one H_one one
    omega

theorem cantorStep_lt {H E : Nat} (H_one : H % 3 = 1)
    (E_lt : E < H) (live : cantorLive E) : cantorStep H E < H := by
  rcases cantorLive_cases live with zero | one
  · have equation := cantorStep_eq_of_mod_zero (H := H) zero
    omega
  · have equation := cantorStep_eq_of_mod_one H_one one
    omega

theorem cantorStep_outer {H E : Nat} (H_one : H % 3 = 1)
    (E_lt : E < H) (live : cantorLive E) :
    3 * cantorStep H E < H ∨ 2 * H < 3 * cantorStep H E := by
  rcases cantorLive_cases live with zero | one
  · left
    rw [cantorStep_eq_of_mod_zero zero]
    exact E_lt
  · right
    rw [cantorStep_eq_of_mod_one H_one one]
    omega

theorem cantorStep_injective_of_live {H left right : Nat} (H_one : H % 3 = 1)
    (left_lt : left < H) (right_lt : right < H)
    (left_live : cantorLive left) (right_live : cantorLive right)
    (step_eq : cantorStep H left = cantorStep H right) : left = right := by
  rcases cantorLive_cases left_live with left_zero | left_one
  · rcases cantorLive_cases right_live with right_zero | right_one
    · have left_eq := cantorStep_eq_of_mod_zero (H := H) left_zero
      have right_eq := cantorStep_eq_of_mod_zero (H := H) right_zero
      omega
    · have left_eq := cantorStep_eq_of_mod_zero (H := H) left_zero
      have right_eq := cantorStep_eq_of_mod_one H_one right_one
      have H_pos : 0 < H := by
        have H_bound : H % 3 < 3 := Nat.mod_lt H (by omega)
        omega
      omega
  · rcases cantorLive_cases right_live with right_zero | right_one
    · have left_eq := cantorStep_eq_of_mod_one H_one left_one
      have right_eq := cantorStep_eq_of_mod_zero (H := H) right_zero
      have H_pos : 0 < H := by
        have H_bound : H % 3 < 3 := Nat.mod_lt H (by omega)
        omega
      omega
    · have left_eq := cantorStep_eq_of_mod_one H_one left_one
      have right_eq := cantorStep_eq_of_mod_one H_one right_one
      omega

private theorem cantor_iterate_prefix_cancel {H E i d : Nat} (H_one : H % 3 = 1)
    (orbit_lt : ∀ n, (cantorStep H)^[n] E < H)
    (orbit_live : ∀ n, cantorLive ((cantorStep H)^[n] E))
    (collision : (cantorStep H)^[i] E = (cantorStep H)^[i + d] E) :
    E = (cantorStep H)^[d] E := by
  induction i with
  | zero => simpa using collision
  | succ i induction =>
      have stepped :
          cantorStep H ((cantorStep H)^[i] E) =
            cantorStep H ((cantorStep H)^[i + d] E) := by
        simpa only [Nat.succ_add, Function.iterate_succ_apply'] using collision
      have predecessor :
          (cantorStep H)^[i] E = (cantorStep H)^[i + d] E :=
        cantorStep_injective_of_live H_one (orbit_lt i) (orbit_lt (i + d))
          (orbit_live i) (orbit_live (i + d)) stepped
      exact induction predecessor

/-- Every live Cantor-defect orbit started in the open middle third of its finite interval
eventually reaches the draining residue two modulo three. -/
theorem exists_cantorDeath {H E : Nat} (H_one : H % 3 = 1)
    (E_pos : 0 < E) (E_lt : E < H) (middle_lower : H < 3 * E)
    (middle_upper : 3 * E < 2 * H) :
    ∃ n, ((cantorStep H)^[n] E) % 3 = 2 := by
  by_contra no_death
  have orbit_live : ∀ n, cantorLive ((cantorStep H)^[n] E) := by
    intro n
    unfold cantorLive
    exact fun death => no_death ⟨n, death⟩
  have orbit_pos : ∀ n, 0 < (cantorStep H)^[n] E := by
    intro n
    induction n with
    | zero => simpa using E_pos
    | succ n induction =>
        rw [Function.iterate_succ_apply']
        exact cantorStep_pos H_one induction (orbit_live n)
  have orbit_lt : ∀ n, (cantorStep H)^[n] E < H := by
    intro n
    induction n with
    | zero => simpa using E_lt
    | succ n induction =>
        rw [Function.iterate_succ_apply']
        exact cantorStep_lt H_one induction (orbit_live n)
  let finiteOrbit : Nat → Fin H := fun n => ⟨(cantorStep H)^[n] E, orbit_lt n⟩
  obtain ⟨left, right, distinct, collision⟩ :=
    Finite.exists_ne_map_eq_of_infinite finiteOrbit
  have value_collision :
      (cantorStep H)^[left] E = (cantorStep H)^[right] E :=
    congrArg Fin.val collision
  rcases lt_or_gt_of_ne distinct with left_lt | right_lt
  · obtain ⟨d, right_eq⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt left_lt)
    have d_pos : 0 < d := by omega
    subst right
    have cycle := cantor_iterate_prefix_cancel H_one orbit_lt orbit_live value_collision
    obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt d_pos)
    rw [Function.iterate_succ_apply'] at cycle
    have outer := cantorStep_outer H_one (orbit_lt predecessor) (orbit_live predecessor)
    omega
  · obtain ⟨d, left_eq⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt right_lt)
    have d_pos : 0 < d := by omega
    subst left
    have cycle := cantor_iterate_prefix_cancel H_one orbit_lt orbit_live value_collision.symm
    obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt d_pos)
    rw [Function.iterate_succ_apply'] at cycle
    have outer := cantorStep_outer H_one (orbit_lt predecessor) (orbit_live predecessor)
    omega

private theorem pairQueue_halts_of_defect_two (a E : Nat)
    (E_lt : E < 7 * (3 * a + 2) + 2) (E_two : E % 3 = 2) :
    TagHaltsFrom 3 (tagOutput (separatedBody (3 * (3 * a + 2) - 1)))
      (pairQueue (3 * a + 2) (15 * (3 * a + 2) + 3 - E)) := by
  let tail := 15 * (3 * a + 2) + 3 - E
  have E_le : E ≤ 15 * (3 * a + 2) + 3 := by omega
  have tail_mod : tail % 3 = 1 := by
    dsimp [tail]
    omega
  let g := tail / 3
  have decomposition := Nat.mod_add_div tail 3
  have tail_eq : tail = 3 * g + 1 := by
    dsimp [g]
    omega
  have tail_two : 2 ≤ tail := by
    dsimp [tail]
    omega
  have g_pos : 0 < g := by omega
  change TagHaltsFrom 3 (tagOutput (separatedBody (3 * (3 * a + 2) - 1)))
    (pairQueue (3 * a + 2) tail)
  rw [tail_eq]
  exact pairQueue_one_halts a g g_pos

private theorem pairQueue_halts_of_cantor_death (a E n : Nat)
    (E_pos : 0 < E) (E_lt : E < 7 * (3 * a + 2) + 2)
    (death :
      ((cantorStep (7 * (3 * a + 2) + 2))^[n] E) % 3 = 2) :
    TagHaltsFrom 3 (tagOutput (separatedBody (3 * (3 * a + 2) - 1)))
      (pairQueue (3 * a + 2) (15 * (3 * a + 2) + 3 - E)) := by
  induction n generalizing E with
  | zero =>
      simp only [Function.iterate_zero_apply] at death
      exact pairQueue_halts_of_defect_two a E E_lt death
  | succ n induction =>
      by_cases E_two : E % 3 = 2
      · exact pairQueue_halts_of_defect_two a E E_lt E_two
      · let H := 7 * (3 * a + 2) + 2
        let nextE := cantorStep H E
        have H_one : H % 3 = 1 := by
          dsimp [H]
          omega
        have live : cantorLive E := E_two
        have next_pos : 0 < nextE := cantorStep_pos H_one E_pos live
        have next_lt : nextE < 7 * (3 * a + 2) + 2 := by
          change nextE < H
          exact cantorStep_lt H_one E_lt live
        have next_death : ((cantorStep H)^[n] nextE) % 3 = 2 := by
          simpa only [Function.iterate_succ_apply] using death
        have next_halts := induction nextE next_pos next_lt next_death
        rcases cantorLive_cases live with E_zero | E_one
        · let tail := 15 * (3 * a + 2) + 3 - E
          have E_le : E ≤ 15 * (3 * a + 2) + 3 := by omega
          have tail_mod : tail % 3 = 0 := by
            dsimp [tail]
            omega
          let g := tail / 3
          have decomposition := Nat.mod_add_div tail 3
          have tail_eq : tail = 3 * g := by
            dsimp [g]
            omega
          have tail_two : 2 ≤ tail := by
            dsimp [tail]
            omega
          have g_pos : 0 < g := by omega
          have step_eq : 3 * nextE = E := by
            exact cantorStep_eq_of_mod_zero E_zero
          have next_tail_eq :
              15 * (3 * a + 2) + 3 - nextE =
                10 * (3 * a + 2) + g + 2 := by
            omega
          have normalized_next :
              TagHaltsFrom 3 (tagOutput (separatedBody (3 * (3 * a + 2) - 1)))
                (pairQueue (3 * a + 2) (10 * (3 * a + 2) + g + 2)) := by
            rw [← next_tail_eq]
            exact next_halts
          change TagHaltsFrom 3 (tagOutput (separatedBody (3 * (3 * a + 2) - 1)))
            (pairQueue (3 * a + 2) tail)
          rw [tail_eq]
          exact pairQueue_zero_halts a g g_pos normalized_next
        · let tail := 15 * (3 * a + 2) + 3 - E
          have E_le : E ≤ 15 * (3 * a + 2) + 3 := by omega
          have tail_mod : tail % 3 = 2 := by
            dsimp [tail]
            omega
          let g := tail / 3
          have decomposition := Nat.mod_add_div tail 3
          have tail_eq : tail = 3 * g + 2 := by
            dsimp [g]
            omega
          have step_eq : 3 * nextE = E + 2 * H := by
            exact cantorStep_eq_of_mod_one H_one E_one
          have next_tail_eq :
              15 * (3 * a + 2) + 3 - nextE = 16 * a + g + 12 := by
            dsimp [H] at step_eq
            omega
          have normalized_next :
              TagHaltsFrom 3 (tagOutput (separatedBody (3 * (3 * a + 2) - 1)))
                (pairQueue (3 * a + 2) (16 * a + g + 12)) := by
            rw [← next_tail_eq]
            exact next_halts
          change TagHaltsFrom 3 (tagOutput (separatedBody (3 * (3 * a + 2) - 1)))
            (pairQueue (3 * a + 2) tail)
          rw [tail_eq]
          exact pairQueue_two_halts a g normalized_next

/-- The coupled diagonal input with separation `n=9k+5` enters a finite Cantor-defect
orbit and halts when that orbit reaches residue two modulo three. -/
theorem fiveResidue_tagHaltsFrom (k : Nat) :
    TagHaltsFrom 3 (tagOutput (separatedBody (9 * k + 5)))
      (coupledInitial (9 * k + 5)) := by
  let A := 3 * k + 2
  let H := 7 * A + 2
  let E := 4 * A + 1
  have H_one : H % 3 = 1 := by
    dsimp [H, A]
    omega
  have E_pos : 0 < E := by
    dsimp [E, A]
    omega
  have E_lt : E < H := by
    dsimp [E, H, A]
    omega
  have middle_lower : H < 3 * E := by
    dsimp [E, H, A]
    omega
  have middle_upper : 3 * E < 2 * H := by
    dsimp [E, H, A]
    omega
  obtain ⟨steps, death⟩ :=
    exists_cantorDeath H_one E_pos E_lt middle_lower middle_upper
  have canonical := pairQueue_halts_of_cantor_death k E steps E_pos E_lt death
  have tail_eq : 15 * A + 3 - E = 10 * A + A + 2 := by
    dsimp [E]
    omega
  have next_halts :
      TagHaltsFrom 3 (tagOutput (separatedBody (3 * (3 * k + 2) - 1)))
        (pairQueue (3 * k + 2) (10 * (3 * k + 2) + (3 * k + 2) + 2)) := by
    rw [tail_eq] at canonical
    simpa only [A] using canonical
  have root := pairQueue_zero_halts k (3 * k + 2) (by omega) next_halts
  have exponent_eq : 3 * (3 * k + 2) - 1 = 9 * k + 5 := by omega
  have queue_eq :
      pairQueue (3 * k + 2) (3 * (3 * k + 2)) = coupledInitial (9 * k + 5) := by
    rw [coupledInitial_eq]
    unfold pairQueue
    rw [exponent_eq, show 3 * (3 * k + 2) = 9 * k + 5 + 1 by omega]
  rw [exponent_eq, queue_eq] at root
  exact root

end MatrixMortality.SeparatedTwoCResidue
