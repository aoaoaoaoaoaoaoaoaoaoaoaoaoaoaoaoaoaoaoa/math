import MatrixMortality.GuardedMixedPrimeBridge
import MatrixMortality.TransverseSeparatedForkNoGo

/-!
# Mixed-prime macro fork rigidity

An exact block-coded endpoint realization of the `bcbc` suffix language must send the flat and
nested terminal-fork blocks to the same affine action. The proof cancels the fixed terminal prefix,
extracts one common fixed point, and uses equality of the two blocks' macro Parikh vectors. Hence
every candidate supplies either a literal morphic word equation or a genuine mixed-prime kernel
relation. A common affine fixed point for all three control macros makes the endpoint language
impossible.
-/

namespace MatrixMortality.GuardedMixedPrimeFork

open MixedPrimeKernel
open GuardedMixedPrimeBridge
open BranchingHistory BranchingRecognizer PeriodicHistory TransverseSeparatedForkNoGo

/-- Remove the compulsory leading data `c` from one canonical terminal-fork control. -/
private def terminalForkSuffix (bits : List Bool) : List PairedControl :=
  (terminalForkControl bits).tail

theorem action_injective (letter : Letter) : Function.Injective (action letter) := by
  cases letter <;> intro left right equal <;> norm_num [action] at equal ⊢ <;> linarith

theorem wordAction_injective (word : List Letter) : Function.Injective (wordAction word) := by
  induction word with
  | nil => exact Function.injective_id
  | cons letter word induction =>
      exact (action_injective letter).comp induction

/-- Multiplicative slope of one mixed-prime affine letter. -/
def actionScale : Letter → ℚ
  | .dilate => 2 / 3
  | .translate => 3 / 5

/-- Multiplicative slope of a mixed-prime affine word. -/
def wordScale (word : List Letter) : ℚ :=
  (word.map actionScale).prod

theorem wordAction_sub (word : List Letter) (left right : ℚ) :
    wordAction word left - wordAction word right = wordScale word * (left - right) := by
  induction word with
  | nil => simp [wordAction, wordScale]
  | cons letter word induction =>
      calc
        wordAction (letter :: word) left - wordAction (letter :: word) right =
            actionScale letter * (wordAction word left - wordAction word right) := by
          cases letter <;> norm_num [wordAction, action, actionScale] <;> ring
        _ = actionScale letter * (wordScale word * (left - right)) := by rw [induction]
        _ = wordScale (letter :: word) * (left - right) := by
          simp [wordScale]
          ring

theorem wordAction_eq_of_common_fixedPoint_of_scale_eq
    (left right : List Letter) (fixed : ℚ)
    (left_fixed : wordAction left fixed = fixed)
    (right_fixed : wordAction right fixed = fixed)
    (scale_eq : wordScale left = wordScale right) :
    ∀ state, wordAction left state = wordAction right state := by
  intro state
  calc
    wordAction left state = fixed + wordScale left * (state - fixed) := by
      linarith [wordAction_sub left state fixed]
    _ = fixed + wordScale right * (state - fixed) := by rw [scale_eq]
    _ = wordAction right state := by
      linarith [wordAction_sub right state fixed]

theorem wordScale_append (left right : List Letter) :
    wordScale (left ++ right) = wordScale left * wordScale right := by
  simp [wordScale, List.map_append, List.prod_append]

theorem wordScale_encodedWord
    (code : PairedControl → List Letter) (word : List PairedControl) :
    wordScale (encodedWord code word) =
      (word.map fun control => wordScale (code control)).prod := by
  induction word with
  | nil => simp [encodedWord, wordScale]
  | cons control word induction =>
      have induction_flat :
          wordScale (word.flatMap code) =
            (word.map fun current => wordScale (code current)).prod := by
        simpa [encodedWord] using induction
      rw [encodedWord, List.flatMap_cons, wordScale_append, induction_flat]
      rfl

theorem wordScale_pos (word : List Letter) : 0 < wordScale word := by
  induction word with
  | nil => norm_num [wordScale]
  | cons letter word induction =>
      cases letter <;> norm_num [wordScale, actionScale] <;> positivity

theorem wordScale_le_one (word : List Letter) : wordScale word ≤ 1 := by
  induction word with
  | nil => norm_num [wordScale]
  | cons letter word induction =>
      have tail_pos : 0 < wordScale word := wordScale_pos word
      cases letter with
      | dilate =>
          change (2 / 3 : ℚ) * wordScale word ≤ 1
          nlinarith
      | translate =>
          change (3 / 5 : ℚ) * wordScale word ≤ 1
          nlinarith

theorem wordScale_lt_one_of_ne_nil (word : List Letter) (word_ne : word ≠ []) :
    wordScale word < 1 := by
  obtain ⟨letter, tail, rfl⟩ := List.exists_cons_of_ne_nil word_ne
  have letter_pos : 0 < actionScale letter := by
    cases letter <;> norm_num [actionScale]
  have letter_lt : actionScale letter < 1 := by
    cases letter <;> norm_num [actionScale]
  have tail_le : wordScale tail ≤ 1 := wordScale_le_one tail
  simp only [wordScale, List.map_cons, List.prod_cons]
  calc
    actionScale letter * wordScale tail ≤ actionScale letter * 1 :=
      mul_le_mul_of_nonneg_left tail_le letter_pos.le
    _ < 1 := by simpa using letter_lt

theorem wordAction_fixedPoint_unique_of_ne_nil
    (word : List Letter) (word_ne : word ≠ []) {left right : ℚ}
    (left_fixed : wordAction word left = left)
    (right_fixed : wordAction word right = right) :
    left = right := by
  have scale_lt : wordScale word < 1 := wordScale_lt_one_of_ne_nil word word_ne
  have factor_ne : 1 - wordScale word ≠ 0 := by linarith
  have difference := wordAction_sub word left right
  rw [left_fixed, right_fixed] at difference
  have factor_zero : (1 - wordScale word) * (left - right) = 0 := by
    calc
      (1 - wordScale word) * (left - right) =
          (left - right) - wordScale word * (left - right) := by ring
      _ = 0 := sub_eq_zero.mpr difference
  exact sub_eq_zero.mp ((mul_eq_zero.mp factor_zero).resolve_left factor_ne)

theorem encodedWord_fixed_of_macro_fixed
    (code : PairedControl → List Letter) (fixed : ℚ)
    (macro_fixed : ∀ control, wordAction (code control) fixed = fixed) :
    ∀ word, wordAction (encodedWord code word) fixed = fixed := by
  intro word
  induction word with
  | nil => simp [encodedWord, wordAction]
  | cons control word induction =>
      have induction_flat : wordAction (word.flatMap code) fixed = fixed := by
        simpa [encodedWord] using induction
      rw [encodedWord, List.flatMap_cons, wordAction_append, induction_flat,
        macro_fixed control]

private theorem control_mem_flatForkControl (control : PairedControl) :
    control ∈ flatForkControl := by
  cases control with
  | toggle => decide
  | data letter => cases letter <;> decide

private theorem encodedWord_flatForkControl_ne_nil_of_exists
    (code : PairedControl → List Letter) (some_nonempty : ∃ control, code control ≠ []) :
    encodedWord code flatForkControl ≠ [] := by
  intro encoded_nil
  obtain ⟨control, control_ne⟩ := some_nonempty
  apply control_ne
  have all_nil : ∀ current ∈ flatForkControl, code current = [] := by
    apply List.flatMap_eq_nil_iff.mp
    simpa [encodedWord] using encoded_nil
  exact all_nil control (control_mem_flatForkControl control)

private theorem data_c_cons_terminalForkSuffix (bits : List Bool) :
    .data .c :: terminalForkSuffix bits = terminalForkControl bits := by
  simp [terminalForkSuffix, terminalForkControl,
    historyControl, strokeControl, strokeCBC, strokeBCB, stroke₃]

/-- Fixed terminal-prefix suffix left after removing the compulsory leading data `c`. -/
private def terminalForkPrefixSuffix : List PairedControl :=
  terminalPrefixControl.tail

private theorem terminalForkSuffix_nil :
    terminalForkSuffix [] = terminalForkPrefixSuffix ++ [.toggle] := by
  simp [terminalForkSuffix, terminalForkPrefixSuffix, terminalForkControl_eq,
    terminalPrefixControl, historyControl, strokeControl, strokeCBC, strokeBCB, stroke₃,
    bcbcFork]

private theorem terminalForkSuffix_false :
    terminalForkSuffix [false] =
      terminalForkPrefixSuffix ++ flatForkControl ++ [.toggle] := by
  simp [terminalForkSuffix, terminalForkPrefixSuffix, terminalForkControl_eq,
    terminalPrefixControl, flatForkControl, bcbcFork, forkBlock, historyControl, strokeControl,
    strokeCBC, strokeBCB, strokeBBB, stroke₃, flatBlock]

private theorem terminalForkSuffix_true :
    terminalForkSuffix [true] =
      terminalForkPrefixSuffix ++ nestedForkControl ++ [.toggle] := by
  simp [terminalForkSuffix, terminalForkPrefixSuffix, terminalForkControl_eq,
    terminalPrefixControl, nestedForkControl, bcbcFork, forkBlock, historyControl, strokeControl,
    strokeCBC, strokeBCB, strokeBBB, strokeCBB, stroke₃, nestedBlock]

private theorem terminalForkSuffix_endpoint
    (code : PairedControl → List Letter) (source target : ℚ)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0)
    (bits : List Bool) :
    wordAction (encodedWord code (terminalForkSuffix bits)) source = target := by
  apply (endpoint_exact (terminalForkSuffix bits)).mpr
  rw [data_c_cons_terminalForkSuffix]
  exact terminalForkControl_paired_zero bits

/-- Exact endpoint recognition forces the flat and nested fork macros to fix the toggled source. -/
theorem bcbc_fork_macro_common_fixedPoint
    (code : PairedControl → List Letter) (source target : ℚ)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0) :
    let fixed := wordAction (code .toggle) source
    wordAction (encodedWord code flatForkControl) fixed = fixed ∧
      wordAction (encodedWord code nestedForkControl) fixed = fixed := by
  dsimp only
  have empty_endpoint :
      wordAction (encodedWord code terminalForkPrefixSuffix)
          (wordAction (code .toggle) source) = target := by
    simpa [terminalForkSuffix_nil, encodedWord, List.flatMap_append, wordAction_append] using
      terminalForkSuffix_endpoint code source target endpoint_exact []
  have flat_endpoint :
      wordAction (encodedWord code terminalForkPrefixSuffix)
          (wordAction (encodedWord code flatForkControl)
            (wordAction (code .toggle) source)) = target := by
    simpa [terminalForkSuffix_false, encodedWord, List.flatMap_append, wordAction_append] using
      terminalForkSuffix_endpoint code source target endpoint_exact [false]
  have nested_endpoint :
      wordAction (encodedWord code terminalForkPrefixSuffix)
          (wordAction (encodedWord code nestedForkControl)
            (wordAction (code .toggle) source)) = target := by
    simpa [terminalForkSuffix_true, encodedWord, List.flatMap_append, wordAction_append] using
      terminalForkSuffix_endpoint code source target endpoint_exact [true]
  constructor
  · apply wordAction_injective (encodedWord code terminalForkPrefixSuffix)
    exact flat_endpoint.trans empty_endpoint.symm
  · apply wordAction_injective (encodedWord code terminalForkPrefixSuffix)
    exact nested_endpoint.trans empty_endpoint.symm

/-- The flat and nested fork controls have equal slopes under every block code. -/
theorem bcbc_fork_macro_scale_eq (code : PairedControl → List Letter) :
    wordScale (encodedWord code flatForkControl) =
      wordScale (encodedWord code nestedForkControl) := by
  rw [wordScale_encodedWord, wordScale_encodedWord]
  simp only [flatForkControl, nestedForkControl, historyControl, strokeControl,
    flatBlock, nestedBlock, strokeBBB, strokeCBC, strokeBCB, strokeCBB, stroke₃,
    List.map_append, List.prod_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil]
  ring

/-- Exact endpoint recognition forces the two fork macros to induce the same affine action. -/
theorem bcbc_fork_macro_actions_eq
    (code : PairedControl → List Letter) (source target : ℚ)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0) :
    ∀ state,
      wordAction (encodedWord code flatForkControl) state =
        wordAction (encodedWord code nestedForkControl) state := by
  obtain ⟨flat_fixed, nested_fixed⟩ :=
    bcbc_fork_macro_common_fixedPoint code source target endpoint_exact
  exact wordAction_eq_of_common_fixedPoint_of_scale_eq
    (encodedWord code flatForkControl) (encodedWord code nestedForkControl)
    (wordAction (code .toggle) source) flat_fixed nested_fixed
    (bcbc_fork_macro_scale_eq code)

/-- The forced flat and nested fork actions commute on every rational state. -/
theorem bcbc_fork_macro_actions_commute
    (code : PairedControl → List Letter) (source target state : ℚ)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0) :
    wordAction (encodedWord code flatForkControl)
        (wordAction (encodedWord code nestedForkControl) state) =
      wordAction (encodedWord code nestedForkControl)
        (wordAction (encodedWord code flatForkControl) state) := by
  have actions_eq := bcbc_fork_macro_actions_eq code source target endpoint_exact
  rw [actions_eq (wordAction (encodedWord code nestedForkControl) state), actions_eq state]

/-- Every exact endpoint code gives either a literal fork-word collapse or a genuine relation in
the mixed-prime affine action. -/
theorem bcbc_fork_macro_word_or_kernel
    (code : PairedControl → List Letter) (source target : ℚ)
    (endpoint_exact : ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0) :
    encodedWord code flatForkControl = encodedWord code nestedForkControl ∨
      (encodedWord code flatForkControl ≠ encodedWord code nestedForkControl ∧
        ∀ state,
          wordAction (encodedWord code flatForkControl) state =
            wordAction (encodedWord code nestedForkControl) state) := by
  by_cases words_eq :
      encodedWord code flatForkControl = encodedWord code nestedForkControl
  · exact Or.inl words_eq
  · exact Or.inr ⟨words_eq, bcbc_fork_macro_actions_eq code source target endpoint_exact⟩

/-- Three macros with one common affine fixed point cannot realize the `bcbc` suffix language. -/
theorem no_bcbc_endpoint_of_common_macro_fixedPoint
    (code : PairedControl → List Letter) (source target common : ℚ)
    (macro_fixed : ∀ control, wordAction (code control) common = common) :
    ¬ ∀ word,
      wordAction (encodedWord code word) source = target ↔
        pairedCoefficient ℚ 3 bcbcBody (.data .c :: word) = 0 := by
  intro endpoint_exact
  have macro_actions_ne := bcbc_macro_actions_pairwise_ne code source target endpoint_exact
  have some_nonempty : ∃ control, code control ≠ [] := by
    by_cases data_b_empty : code (.data .b) = []
    · have data_c_ne : code (.data .c) ≠ [] := by
        intro data_c_empty
        apply macro_actions_ne.1
        intro state
        simp [data_b_empty, data_c_empty, wordAction]
      exact ⟨.data .c, data_c_ne⟩
    · exact ⟨.data .b, data_b_empty⟩
  have flat_ne : encodedWord code flatForkControl ≠ [] :=
    encodedWord_flatForkControl_ne_nil_of_exists code some_nonempty
  obtain ⟨flat_fixed, _⟩ :=
    bcbc_fork_macro_common_fixedPoint code source target endpoint_exact
  have common_flat_fixed :
      wordAction (encodedWord code flatForkControl) common = common :=
    encodedWord_fixed_of_macro_fixed code common macro_fixed flatForkControl
  have toggled_source_eq : wordAction (code .toggle) source = common :=
    wordAction_fixedPoint_unique_of_ne_nil
      (encodedWord code flatForkControl) flat_ne flat_fixed common_flat_fixed
  have source_eq : source = common := by
    apply wordAction_injective (code .toggle)
    calc
      wordAction (code .toggle) source = common := toggled_source_eq
      _ = wordAction (code .toggle) common := (macro_fixed .toggle).symm
  have target_eq : target = common := by
    have empty_endpoint := terminalForkSuffix_endpoint code source target endpoint_exact []
    have empty_fixed :=
      encodedWord_fixed_of_macro_fixed code common macro_fixed (terminalForkSuffix [])
    rw [source_eq, empty_fixed] at empty_endpoint
    exact empty_endpoint.symm
  have collision_fixed :=
    encodedWord_fixed_of_macro_fixed code common macro_fixed dataBCollisionSuffix
  have collision_endpoint :
      wordAction (encodedWord code dataBCollisionSuffix) source = target := by
    rw [source_eq, target_eq, collision_fixed]
  exact pairedCoefficient_dataBCollisionSuffix_ne_zero
    ((endpoint_exact dataBCollisionSuffix).mp collision_endpoint)

end MatrixMortality.GuardedMixedPrimeFork
