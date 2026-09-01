import MatrixMortality.GuardedMixedPrimeForkCrossing

/-!
# Mixed-prime fork quotient

The first proper critical overlap of Cassaigne's relation embeds into a genuine reduced fork at
length `312`. Its three raw macros have distinct slopes, but their affine actions are the first,
second, and fourth powers of one contraction. A generic centralizer theorem explains the
collapse: every full-triple conjugacy lift fixes one common rational point and is forbidden by
exact `bcbc` endpoint semantics.
-/

set_option autoImplicit false

namespace MatrixMortality.GuardedMixedPrimeFork

open MixedPrimeKernel GuardedMixedPrimeBridge
open BranchingHistory BranchingRecognizer

/-- Concatenation power in the raw-word monoid. -/
def wordPower (word : List Letter) (exponent : ℕ) : List Letter :=
  (List.replicate exponent word).flatten

@[simp]
theorem wordPower_zero (word : List Letter) : wordPower word 0 = [] := rfl

@[simp]
theorem wordPower_succ (word : List Letter) (exponent : ℕ) :
    wordPower word (exponent + 1) = word ++ wordPower word exponent := by
  simp [wordPower, List.replicate_succ]

theorem wordPower_one (word : List Letter) : wordPower word 1 = word := by
  simp [wordPower_succ]

theorem wordAction_wordPower_fixed
    (word : List Letter) (exponent : ℕ) (fixed : ℚ)
    (word_fixed : wordAction word fixed = fixed) :
    wordAction (wordPower word exponent) fixed = fixed := by
  induction exponent with
  | zero => simp [wordAction]
  | succ exponent induction =>
      rw [show exponent + 1 = exponent.succ by omega, Nat.succ_eq_add_one,
        wordPower_succ, wordAction_append, induction, word_fixed]

theorem wordScale_wordPower (word : List Letter) (exponent : ℕ) :
    wordScale (wordPower word exponent) = wordScale word ^ exponent := by
  induction exponent with
  | zero => simp [wordScale]
  | succ exponent induction =>
      rw [show exponent + 1 = exponent.succ by omega, Nat.succ_eq_add_one,
        wordPower_succ, wordScale_append, induction, pow_succ]
      ring

theorem wordPower_ne_nil (word : List Letter) (exponent : ℕ)
    (word_ne : word ≠ []) (exponent_pos : 0 < exponent) :
    wordPower word exponent ≠ [] := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : exponent ≠ 0)
  simp [wordPower_succ, word_ne]

/-- Every full-triple contextual conjugacy construction lies on the forbidden common-fixed
diagonal. -/
theorem centralizerFork_common_fixedPoint
    (root head tail : List Letter) (centralizerPower xPower yPower zPower : ℕ)
    (root_eq : root = head ++ tail) (root_ne : root ≠ [])
    (centralizerPower_pos : 0 < centralizerPower)
    (centralizer : ∀ state,
      wordAction (wordPower root centralizerPower ++ tail) state =
        wordAction (tail ++ wordPower root centralizerPower) state) :
    ∃ fixed,
      wordAction (tail ++ wordPower root xPower) fixed = fixed ∧
        wordAction (tail ++ wordPower root yPower) fixed = fixed ∧
          wordAction (wordPower root zPower ++ head) fixed = fixed := by
  let anchor := wordPower root centralizerPower
  let fixed := wordFixedPoint anchor
  have anchor_ne : anchor ≠ [] := by
    exact wordPower_ne_nil root centralizerPower root_ne centralizerPower_pos
  have anchor_fixed : wordAction anchor fixed = fixed :=
    wordAction_wordFixedPoint_of_ne_nil anchor anchor_ne
  have tail_commutes : ∀ state,
      wordAction anchor (wordAction tail state) =
        wordAction tail (wordAction anchor state) := by
    intro state
    simpa only [wordAction_append] using centralizer state
  have tail_fixed : wordAction tail fixed = fixed :=
    wordAction_wordFixedPoint_of_actions_commute anchor tail anchor_ne tail_commutes
  have root_fixedPoint := wordAction_wordFixedPoint_of_ne_nil root root_ne
  have rootFixed_anchor_fixed :
      wordAction anchor (wordFixedPoint root) = wordFixedPoint root := by
    exact wordAction_wordPower_fixed root centralizerPower (wordFixedPoint root)
      root_fixedPoint
  have fixed_eq_rootFixed : fixed = wordFixedPoint root := by
    exact wordAction_fixedPoint_unique_of_ne_nil anchor anchor_ne
      anchor_fixed rootFixed_anchor_fixed
  have root_fixed : wordAction root fixed = fixed := by
    rw [fixed_eq_rootFixed]
    exact root_fixedPoint
  have head_fixed : wordAction head fixed = fixed := by
    have decomposition : wordAction root fixed = wordAction head (wordAction tail fixed) := by
      rw [root_eq, wordAction_append]
    rw [tail_fixed] at decomposition
    exact decomposition.symm.trans root_fixed
  have rootPower_fixed (exponent : ℕ) :
      wordAction (wordPower root exponent) fixed = fixed :=
    wordAction_wordPower_fixed root exponent fixed root_fixed
  refine ⟨fixed, ?_, ?_, ?_⟩
  · rw [wordAction_append, rootPower_fixed, tail_fixed]
  · rw [wordAction_append, rootPower_fixed, tail_fixed]
  · rw [wordAction_append, head_fixed, rootPower_fixed]

/-- Middle of the published Cassaigne word after deleting its boundary translations. -/
def criticalForkMiddle : List Letter :=
  cassaigneRight.tail.dropLast

/-- Short macro in the first contextual fork generated by a critical Cassaigne overlap. -/
def criticalForkX : List Letter :=
  cassaigneRight.dropLast

/-- Long head completing the primitive conjugacy root. -/
def criticalForkZ : List Letter :=
  cassaigneLeft ++ criticalForkMiddle

/-- Primitive conjugacy root of the contextual fork. -/
def criticalForkRoot : List Letter :=
  criticalForkZ ++ criticalForkX

/-- Long data macro in the contextual fork. -/
def criticalForkY : List Letter :=
  criticalForkX ++ criticalForkRoot

/-- Left branch of the first proper Cassaigne critical pair. -/
def cassaigneCriticalLeft : List Letter :=
  cassaigneLeft ++ cassaigneRight.tail

/-- Right branch of the first proper Cassaigne critical pair. -/
def cassaigneCriticalRight : List Letter :=
  cassaigneRight.dropLast ++ cassaigneLeft

/-- Common prefix embedding the critical pair into the reduced fork. -/
def criticalForkPrefix : List Letter :=
  criticalForkX ++ criticalForkRoot ++ criticalForkRoot ++ criticalForkX

/-- Common suffix embedding the critical pair into the reduced fork. -/
def criticalForkSuffix : List Letter :=
  criticalForkMiddle ++ criticalForkX

theorem cassaigneRight_eq_boundary :
    cassaigneRight = [.translate] ++ criticalForkMiddle ++ [.translate] := by
  norm_num [criticalForkMiddle, cassaigneRight, List.replicate_succ]

theorem cassaigneRight_tail_eq :
    cassaigneRight.tail = criticalForkMiddle ++ [.translate] := by
  norm_num [criticalForkMiddle, cassaigneRight, List.replicate_succ]

theorem cassaigneRight_dropLast_eq :
    cassaigneRight.dropLast = [.translate] ++ criticalForkMiddle := by
  norm_num [criticalForkMiddle, cassaigneRight, List.replicate_succ]

theorem cassaigneFork_component_lengths :
    criticalForkMiddle.length = 25 ∧ criticalForkX.length = 26 ∧
      cassaigneLeft.length = 27 := by
  norm_num [criticalForkMiddle, criticalForkX, cassaigneLeft, cassaigneRight,
    List.replicate_succ]

/-- The two branches of the first proper Cassaigne overlap induce the same affine action. -/
theorem wordAction_cassaigneCritical (state : ℚ) :
    wordAction cassaigneCriticalLeft state =
      wordAction cassaigneCriticalRight state := by
  have left_rewrite := wordAction_context wordAction_cassaigne [] cassaigneRight.tail state
  have right_rewrite :=
    wordAction_context wordAction_cassaigne cassaigneRight.dropLast [] state
  have overlap :
      cassaigneRight ++ cassaigneRight.tail =
        cassaigneRight.dropLast ++ cassaigneRight := by
    rw [cassaigneRight_tail_eq, cassaigneRight_dropLast_eq,
      cassaigneRight_eq_boundary]
    simp [List.append_assoc]
  calc
    wordAction cassaigneCriticalLeft state =
        wordAction (cassaigneRight ++ cassaigneRight.tail) state := by
      simpa [cassaigneCriticalLeft] using left_rewrite
    _ = wordAction (cassaigneRight.dropLast ++ cassaigneRight) state := by rw [overlap]
    _ = wordAction cassaigneCriticalRight state := by
      simpa [cassaigneCriticalRight] using right_rewrite.symm

theorem criticalForkRoot_append_factorization :
    criticalForkRoot ++ criticalForkX =
        cassaigneCriticalLeft ++ criticalForkSuffix ∧
      criticalForkX ++ criticalForkRoot =
        cassaigneCriticalRight ++ criticalForkSuffix := by
  simp only [criticalForkRoot, criticalForkZ, criticalForkX, criticalForkSuffix,
    cassaigneCriticalLeft, cassaigneCriticalRight]
  rw [cassaigneRight_tail_eq, cassaigneRight_dropLast_eq]
  simp [List.append_assoc]

private theorem conjugacyFork_factorization
    {α : Type*} (x z root : List α) (root_eq : root = z ++ x) :
    (x ++ root) ++ z ++ x ++ (x ++ root) ++ x =
        (x ++ root ++ root ++ x) ++ root ++ x ∧
      x ++ z ++ (x ++ root) ++ x ++ (x ++ root) =
        (x ++ root ++ root ++ x) ++ x ++ root := by
  subst root
  simp [List.append_assoc]

theorem criticalFork_factorization :
    criticalForkY ++ criticalForkZ ++ criticalForkX ++ criticalForkY ++ criticalForkX =
        criticalForkPrefix ++ cassaigneCriticalLeft ++ criticalForkSuffix ∧
      criticalForkX ++ criticalForkZ ++ criticalForkY ++ criticalForkX ++ criticalForkY =
        criticalForkPrefix ++ cassaigneCriticalRight ++ criticalForkSuffix := by
  have fork_shape := conjugacyFork_factorization
    criticalForkX criticalForkZ criticalForkRoot rfl
  constructor
  · rw [show criticalForkY = criticalForkX ++ criticalForkRoot by rfl]
    calc
      _ = (criticalForkX ++ criticalForkRoot ++ criticalForkRoot ++ criticalForkX) ++
          criticalForkRoot ++ criticalForkX := fork_shape.1
      _ = criticalForkPrefix ++ (criticalForkRoot ++ criticalForkX) := by
        simp [criticalForkPrefix, List.append_assoc]
      _ = criticalForkPrefix ++
          (cassaigneCriticalLeft ++ criticalForkSuffix) := by
        rw [criticalForkRoot_append_factorization.1]
      _ = criticalForkPrefix ++ cassaigneCriticalLeft ++ criticalForkSuffix := by
        simp [List.append_assoc]
  · rw [show criticalForkY = criticalForkX ++ criticalForkRoot by rfl]
    calc
      _ = (criticalForkX ++ criticalForkRoot ++ criticalForkRoot ++ criticalForkX) ++
          criticalForkX ++ criticalForkRoot := fork_shape.2
      _ = criticalForkPrefix ++ (criticalForkX ++ criticalForkRoot) := by
        simp [criticalForkPrefix, List.append_assoc]
      _ = criticalForkPrefix ++
          (cassaigneCriticalRight ++ criticalForkSuffix) := by
        rw [criticalForkRoot_append_factorization.2]
      _ = criticalForkPrefix ++ cassaigneCriticalRight ++ criticalForkSuffix := by
        simp [List.append_assoc]

/-- The known five-rule congruence contains a genuine reduced-fork-shaped collision. -/
theorem wordAction_criticalFork (state : ℚ) :
    wordAction
        (criticalForkY ++ criticalForkZ ++ criticalForkX ++ criticalForkY ++ criticalForkX)
        state =
      wordAction
        (criticalForkX ++ criticalForkZ ++ criticalForkY ++ criticalForkX ++ criticalForkY)
        state := by
  rw [criticalFork_factorization.1, criticalFork_factorization.2]
  exact wordAction_context wordAction_cassaigneCritical
    criticalForkPrefix criticalForkSuffix state

/-- The contextual Cassaigne fork is a genuine pair of distinct raw words. -/
theorem criticalFork_ne :
    criticalForkY ++ criticalForkZ ++ criticalForkX ++ criticalForkY ++ criticalForkX ≠
      criticalForkX ++ criticalForkZ ++ criticalForkY ++ criticalForkX ++ criticalForkY := by
  rw [criticalFork_factorization.1, criticalFork_factorization.2]
  intro equal
  have prefixed_equal := List.append_cancel_right equal
  have cores_equal := List.append_cancel_left prefixed_equal
  have heads_equal := congrArg List.head? cores_equal
  norm_num [cassaigneCriticalLeft, cassaigneCriticalRight, cassaigneLeft,
    cassaigneRight, List.replicate_succ] at heads_equal
  exact Letter.noConfusion heads_equal

/-- Exact macro lengths and reduced relation length of the contextual Cassaigne fork. -/
theorem criticalFork_lengths :
    criticalForkX.length = 26 ∧ criticalForkY.length = 104 ∧
      criticalForkZ.length = 52 ∧
        (criticalForkY ++ criticalForkZ ++ criticalForkX ++ criticalForkY ++ criticalForkX).length =
          312 := by
  have middle_length := cassaigneFork_component_lengths.1
  have x_length := cassaigneFork_component_lengths.2.1
  have left_length := cassaigneFork_component_lengths.2.2
  simp only [criticalForkY, criticalForkZ, criticalForkRoot, List.length_append]
  omega

/-- The three contextual-fork macros have pairwise different affine slopes. -/
theorem criticalFork_scales_pairwise_ne :
    wordScale criticalForkX ≠ wordScale criticalForkY ∧
      wordScale criticalForkX ≠ wordScale criticalForkZ ∧
        wordScale criticalForkY ≠ wordScale criticalForkZ := by
  norm_num [criticalForkX, criticalForkY, criticalForkZ, criticalForkRoot,
    criticalForkMiddle, cassaigneLeft, cassaigneRight, wordScale, actionScale,
    List.replicate_succ]

/-- The contextual Cassaigne fork lies exactly on the forbidden common-fixed diagonal. -/
theorem criticalFork_common_fixedPoint :
    ∃ fixed,
      wordAction criticalForkX fixed = fixed ∧
        wordAction criticalForkY fixed = fixed ∧
          wordAction criticalForkZ fixed = fixed := by
  have centralizer : ∀ state,
      wordAction (wordPower criticalForkRoot 1 ++ criticalForkX) state =
        wordAction (criticalForkX ++ wordPower criticalForkRoot 1) state := by
    intro state
    rw [wordPower_one, criticalForkRoot_append_factorization.1,
      criticalForkRoot_append_factorization.2]
    exact wordAction_context wordAction_cassaigneCritical [] criticalForkSuffix state
  simpa only [criticalForkY, wordPower_zero, wordPower_one, List.append_nil,
    List.nil_append] using
    centralizerFork_common_fixedPoint criticalForkRoot criticalForkZ criticalForkX
      1 0 1 0 rfl (by decide) (by omega) centralizer

/-- The unique common fixed point of the contextual Cassaigne fork. -/
def criticalForkFixed : ℚ :=
  6560881480 / 3955045357

theorem criticalForkX_fixed :
    wordAction criticalForkX criticalForkFixed = criticalForkFixed := by
  norm_num [criticalForkX, criticalForkFixed, cassaigneRight, wordAction, action,
    List.replicate_succ]

/-- Exact version of the forbidden-diagonal certificate. -/
theorem criticalFork_common_fixedPoint_exact :
    wordAction criticalForkX criticalForkFixed = criticalForkFixed ∧
      wordAction criticalForkY criticalForkFixed = criticalForkFixed ∧
        wordAction criticalForkZ criticalForkFixed = criticalForkFixed := by
  obtain ⟨fixed, x_fixed, y_fixed, z_fixed⟩ := criticalFork_common_fixedPoint
  have x_ne : criticalForkX ≠ [] := by decide
  have fixed_eq : fixed = criticalForkFixed :=
    wordAction_fixedPoint_unique_of_ne_nil criticalForkX x_ne x_fixed criticalForkX_fixed
  subst fixed
  exact ⟨criticalForkX_fixed, y_fixed, z_fixed⟩

theorem criticalFork_scale_powers :
    wordScale criticalForkZ = wordScale criticalForkX ^ 2 ∧
      wordScale criticalForkY = wordScale criticalForkX ^ 4 := by
  norm_num [criticalForkX, criticalForkY, criticalForkZ, criticalForkRoot,
    criticalForkMiddle, cassaigneLeft, cassaigneRight, wordScale, actionScale,
    List.replicate_succ]

/-- At action level the three distinct macros are the first, second, and fourth powers of one
strict affine contraction. -/
theorem criticalFork_actions_eq_powers :
    (∀ state,
      wordAction criticalForkZ state =
        wordAction (wordPower criticalForkX 2) state) ∧
      (∀ state,
        wordAction criticalForkY state =
          wordAction (wordPower criticalForkX 4) state) := by
  have fixed := criticalFork_common_fixedPoint_exact
  constructor
  · apply wordAction_eq_of_common_fixedPoint_of_scale_eq
      criticalForkZ (wordPower criticalForkX 2) criticalForkFixed fixed.2.2
      (wordAction_wordPower_fixed criticalForkX 2 criticalForkFixed fixed.1)
    rw [wordScale_wordPower, criticalFork_scale_powers.1]
  · apply wordAction_eq_of_common_fixedPoint_of_scale_eq
      criticalForkY (wordPower criticalForkX 4) criticalForkFixed fixed.2.1
      (wordAction_wordPower_fixed criticalForkX 4 criticalForkFixed fixed.1)
    rw [wordScale_wordPower, criticalFork_scale_powers.2]

/-- Control code supplied by the contextual Cassaigne fork. -/
def criticalForkCode : PairedControl → List Letter
  | .toggle => criticalForkZ
  | .data .b => criticalForkX
  | .data .c => criticalForkY

theorem criticalForkCode_fixed (control : PairedControl) :
    wordAction (criticalForkCode control) criticalForkFixed = criticalForkFixed := by
  cases control with
  | toggle => exact criticalFork_common_fixedPoint_exact.2.2
  | data letter =>
      cases letter with
      | b => exact criticalFork_common_fixedPoint_exact.1
      | c => exact criticalFork_common_fixedPoint_exact.2.1

/-- The first fork found in the known kernel congruence cannot satisfy the complete endpoint
converse. -/
theorem no_bcbc_endpoint_criticalForkCode (source target : ℚ) :
    ¬ ∀ word,
      wordAction (encodedWord criticalForkCode word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0 :=
  no_bcbc_endpoint_of_common_macro_fixedPoint
    criticalForkCode source target criticalForkFixed criticalForkCode_fixed

end MatrixMortality.GuardedMixedPrimeFork
