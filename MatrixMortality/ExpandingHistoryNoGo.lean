import Mathlib.Computability.DFA
import Mathlib.Data.Set.Finite
import MatrixMortality.HistoryFracture
import MatrixMortality.Undecidability.UniversalNeary

/-!
# Expanding affine history cannot carry universal terminality

An expanding affine coordinate with finitely many control modes has a finite reverse orbit from
every bounded target section. This is the arithmetic core of the obstruction to replacing the
four-state paired compiler by one positional history coordinate and finite phase data.
-/

namespace MatrixMortality

open scoped Matrix

/-- Source-dependent coefficients for one affine history coordinate with a reset phase bit. -/
structure ResetAffineHistory (R : Type*) where
  /-- Positional multiplier of each data control. -/
  radix : TagLetter → R
  /-- Coefficient selecting the suffix phase. -/
  phaseWeight : TagLetter → R
  /-- Phase-independent digit translation. -/
  digitOffset : TagLetter → R
  /-- Initial value of the history coordinate. -/
  initial : R

namespace ResetAffineHistory

variable {R : Type*} [CommRing R]

/-- Three-state reset-affine data matrix. -/
def dataMatrix (parameters : ResetAffineHistory R) (letter : TagLetter) :
    Matrix (Fin 3) (Fin 3) R :=
  !![parameters.radix letter, parameters.phaseWeight letter, parameters.digitOffset letter;
     0, 0, -1;
     0, 0, 1]

/-- Three-state phase toggle. -/
def toggleMatrix : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0;
     0, -1, 0;
     0, 0, 1]

/-- Reset-affine matrices for the three paired controls. -/
def generator (parameters : ResetAffineHistory R) :
    PairedControl → Matrix (Fin 3) (Fin 3) R
  | .data letter => parameters.dataMatrix letter
  | .toggle => toggleMatrix

/-- Homogeneous initial column. -/
def column (parameters : ResetAffineHistory R) : Fin 3 → R :=
  ![parameters.initial, 1, 1]

/-- History coordinate read from right to left. -/
def value (parameters : ResetAffineHistory R) : List PairedControl → R
  | [] => parameters.initial
  | .toggle :: word => parameters.value word
  | .data letter :: word =>
      parameters.radix letter * parameters.value word +
        parameters.phaseWeight letter * historyPhaseSign R (suffixDecode word).1 +
          parameters.digitOffset letter

/-- Homogeneous reset-affine state. -/
def state (parameters : ResetAffineHistory R) (word : List PairedControl) : Fin 3 → R :=
  ![parameters.value word, historyPhaseSign R (suffixDecode word).1, 1]

/-- Exact orbit formula on the complete free monoid of controls. -/
theorem wordProduct_mulVec_column (parameters : ResetAffineHistory R)
    (word : List PairedControl) :
    wordProduct parameters.generator word *ᵥ parameters.column = parameters.state word := by
  induction word with
  | nil =>
      ext coordinate
      fin_cases coordinate <;>
        simp [wordProduct, column, state, value, suffixDecode, historyPhaseSign]
  | cons control word induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec, induction]
      cases decoded_eq : suffixDecode word with
      | mk phase decoded =>
          cases control with
          | toggle =>
              cases phase <;>
                ext coordinate <;>
                fin_cases coordinate <;>
                simp [generator, toggleMatrix, state, value, suffixDecode, decoded_eq,
                  PairPhase.flip, historyPhaseSign, Matrix.mulVec, Matrix.dotProduct,
                  Fin.sum_univ_succ]
          | data letter =>
              cases phase <;> cases letter <;>
                ext coordinate <;>
                fin_cases coordinate <;>
                simp [generator, dataMatrix, state, value, suffixDecode, decoded_eq,
                  PairPhase.tile, historyPhaseSign, Matrix.mulVec, Matrix.dotProduct,
                  Fin.sum_univ_succ] <;>
                ring

/-- Boundary row for an arbitrary affine target functional. -/
def row (left phase constant : R) : Fin 3 → R := ![left, phase, constant]

/-- Scalar coefficient emitted by a reset-affine history machine. -/
def coefficient (parameters : ResetAffineHistory R) (left phase constant : R)
    (word : List PairedControl) : R :=
  linearCoefficient parameters.generator (row left phase constant) parameters.column word

/-- Every coefficient is one affine equation in the history coordinate and phase sign. -/
theorem coefficient_eq (parameters : ResetAffineHistory R) (left phase constant : R)
    (word : List PairedControl) :
    parameters.coefficient left phase constant word =
      left * parameters.value word +
        phase * historyPhaseSign R (suffixDecode word).1 + constant := by
  rw [coefficient, linearCoefficient, parameters.wordProduct_mulVec_column]
  cases decoded_eq : suffixDecode word with
  | mk suffixPhase decoded =>
      cases suffixPhase <;>
        simp [row, state, decoded_eq, Matrix.dotProduct, Fin.sum_univ_succ]
      all_goals ring

/-- If one word and its leading toggle both vanish, the target functional cannot see phase. -/
theorem phaseWeight_eq_zero_of_toggle_pair (parameters : ResetAffineHistory ℚ)
    (left phase constant : ℚ) (word : List PairedControl)
    (word_zero : parameters.coefficient left phase constant word = 0)
    (toggle_zero : parameters.coefficient left phase constant (.toggle :: word) = 0) :
    phase = 0 := by
  rw [parameters.coefficient_eq] at word_zero toggle_zero
  cases decoded_eq : suffixDecode word with
  | mk suffixPhase decoded =>
      cases suffixPhase
      all_goals
        simp [value, suffixDecode, decoded_eq, PairPhase.flip,
          historyPhaseSign] at word_zero toggle_zero
        linarith

/-- When the history coordinate has zero coefficient, zero existence is the two-point phase
test; both phases are reached by the empty word and one toggle. -/
theorem exists_zero_of_left_zero_iff (parameters : ResetAffineHistory ℚ)
    (phase constant : ℚ) :
    (∃ word, parameters.coefficient 0 phase constant word = 0) ↔
      phase + constant = 0 ∨ -phase + constant = 0 := by
  constructor
  · rintro ⟨word, coefficient_zero⟩
    rw [parameters.coefficient_eq] at coefficient_zero
    cases decoded_eq : suffixDecode word with
    | mk suffixPhase decoded =>
        cases suffixPhase
        · left
          simpa [decoded_eq, historyPhaseSign] using coefficient_zero
        · right
          simpa [decoded_eq, historyPhaseSign] using coefficient_zero
  · rintro (rule_zero | erase_zero)
    · refine ⟨[], ?_⟩
      rw [parameters.coefficient_eq]
      simpa [suffixDecode, historyPhaseSign] using rule_zero
    · refine ⟨[.toggle], ?_⟩
      rw [parameters.coefficient_eq]
      simpa [suffixDecode, PairPhase.flip, historyPhaseSign] using erase_zero

end ResetAffineHistory

/-- A finite-mode affine history machine. A transition either leaves the integral coordinate
fixed or expands it by an integer factor of absolute value at least two. -/
structure ExpandingAffineHistory (Mode Control : Type*) where
  /-- Finite-control transition. -/
  nextMode : Mode → Control → Mode
  /-- Linear coefficient of the history-coordinate transition. -/
  scale : Mode → Control → ℤ
  /-- Translation of the history-coordinate transition. -/
  offset : Mode → Control → ℤ
  /-- Every transition is coordinate-stationary or uniformly expanding. -/
  stationary_or_expanding : ∀ mode control,
    (scale mode control = 1 ∧ offset mode control = 0) ∨
      2 ≤ (scale mode control).natAbs

namespace ExpandingAffineHistory

variable {Mode Control : Type*}

/-- A finite mode paired with the cleared integral history coordinate. -/
abbrev State (Mode : Type*) := Mode × ℤ

/-- One forward transition. -/
def step (machine : ExpandingAffineHistory Mode Control) (state : State Mode)
    (control : Control) : State Mode :=
  (machine.nextMode state.1 control,
    machine.scale state.1 control * state.2 + machine.offset state.1 control)

/-- Forward execution in control-list order. -/
def run (machine : ExpandingAffineHistory Mode Control) (state : State Mode) :
    List Control → State Mode :=
  List.foldl machine.step state

/-- One reverse step cannot escape a coordinate box containing every translation. -/
theorem predecessor_natAbs_le (machine : ExpandingAffineHistory Mode Control)
    (state : State Mode) (control : Control) (bound : Nat)
    (output_bounded : (machine.step state control).2.natAbs ≤ bound)
    (offset_bounded : (machine.offset state.1 control).natAbs ≤ bound) :
    state.2.natAbs ≤ bound := by
  rcases machine.stationary_or_expanding state.1 control with stationary | expanding
  · simpa [step, stationary.1, stationary.2] using output_bounded
  · have product_bounded :
        (machine.scale state.1 control * state.2).natAbs ≤ bound + bound := by
      calc
        (machine.scale state.1 control * state.2).natAbs =
            ((machine.scale state.1 control * state.2 +
                machine.offset state.1 control) -
              machine.offset state.1 control).natAbs := by ring_nf
        _ ≤ (machine.scale state.1 control * state.2 +
              machine.offset state.1 control).natAbs +
            (machine.offset state.1 control).natAbs :=
          Int.natAbs_sub_le _ _
        _ ≤ bound + bound := Nat.add_le_add output_bounded offset_bounded
    rw [Int.natAbs_mul] at product_bounded
    have doubled_le_product :
        2 * state.2.natAbs ≤
          (machine.scale state.1 control).natAbs * state.2.natAbs :=
      Nat.mul_le_mul_right state.2.natAbs expanding
    omega

/-- If the end of a run lies in a coordinate box containing every translation, its start lies in
the same box. -/
theorem start_natAbs_le_of_run_natAbs_le (machine : ExpandingAffineHistory Mode Control)
    (state : State Mode) (word : List Control) (bound : Nat)
    (offset_bounded : ∀ mode control, (machine.offset mode control).natAbs ≤ bound)
    (output_bounded : (machine.run state word).2.natAbs ≤ bound) :
    state.2.natAbs ≤ bound := by
  induction word generalizing state with
  | nil => simpa [run] using output_bounded
  | cons control word induction =>
      apply machine.predecessor_natAbs_le state control bound
      · apply induction (machine.step state control)
        simpa [run] using output_bounded
      · exact offset_bounded state.1 control

/-- States which can reach a prescribed target section. -/
def reverseOrbit (machine : ExpandingAffineHistory Mode Control)
    (target : Set (State Mode)) : Set (State Mode) :=
  {state | ∃ word, machine.run state word ∈ target}

/-- Every reverse orbit of a bounded target section stays in the same explicit coordinate box. -/
theorem reverseOrbit_subset_box (machine : ExpandingAffineHistory Mode Control)
    (target : Set (State Mode)) (bound : Nat)
    (offset_bounded : ∀ mode control, (machine.offset mode control).natAbs ≤ bound)
    (target_bounded : ∀ state ∈ target, state.2.natAbs ≤ bound) :
    machine.reverseOrbit target ⊆ {state | state.2.natAbs ≤ bound} := by
  rintro state ⟨word, reaches⟩
  exact machine.start_natAbs_le_of_run_natAbs_le state word bound offset_bounded
    (target_bounded (machine.run state word) reaches)

/-- The integral coordinate box is finite when the mode set is finite. -/
theorem coordinateBox_finite [Finite Mode] (bound : Nat) :
    Set.Finite {state : State Mode | state.2.natAbs ≤ bound} := by
  apply (Set.finite_univ.prod (Set.finite_Icc (-(bound : ℤ)) (bound : ℤ))).subset
  rintro ⟨mode, coordinate⟩ coordinate_bounded
  refine ⟨Set.mem_univ mode, ?_, ?_⟩
  · have cast_bounded : (coordinate.natAbs : ℤ) ≤ bound := by exact_mod_cast coordinate_bounded
    calc
      -(bound : ℤ) ≤ -(coordinate.natAbs : ℤ) := neg_le_neg cast_bounded
      _ = -|coordinate| := by simp
      _ ≤ coordinate := neg_abs_le coordinate
  · have cast_bounded : (coordinate.natAbs : ℤ) ≤ bound := by exact_mod_cast coordinate_bounded
    exact Int.le_natAbs.trans cast_bounded

/-- With finitely many modes, the complete reverse orbit of every bounded target section is
finite. No injectivity or finiteness of accepting histories is assumed. -/
theorem reverseOrbit_finite [Finite Mode]
    (machine : ExpandingAffineHistory Mode Control) (target : Set (State Mode)) (bound : Nat)
    (offset_bounded : ∀ mode control, (machine.offset mode control).natAbs ≤ bound)
    (target_bounded : ∀ state ∈ target, state.2.natAbs ≤ bound) :
    (machine.reverseOrbit target).Finite :=
  (coordinateBox_finite bound).subset
    (machine.reverseOrbit_subset_box target bound offset_bounded target_bounded)

/-- A state certified to lie in one integral coordinate box. -/
abbrev CagedState (Mode : Type*) (bound : Nat) :=
  {state : State Mode // state.2.natAbs ≤ bound}

/-- Refine a state into the box, rejecting it when it lies outside. -/
def cage (bound : Nat) (state : State Mode) : Option (CagedState Mode bound) :=
  if bounded : state.2.natAbs ≤ bound then some ⟨state, bounded⟩ else none

/-- Transition inside the coordinate box; escaping the box enters a dead state. -/
def cagedStep (machine : ExpandingAffineHistory Mode Control) (bound : Nat) :
    Option (CagedState Mode bound) → Control → Option (CagedState Mode bound)
  | none, _ => none
  | some state, control => cage bound (machine.step state.1 control)

/-- Run the boxed transition system. -/
def cagedRun (machine : ExpandingAffineHistory Mode Control) (bound : Nat)
    (state : State Mode) : List Control → Option (CagedState Mode bound) :=
  List.foldl (machine.cagedStep bound) (cage bound state)

/-- A run ending inside the box never leaves it and is reproduced by the caged machine. -/
theorem cagedRun_eq_some (machine : ExpandingAffineHistory Mode Control)
    (state : State Mode) (word : List Control) (bound : Nat)
    (offset_bounded : ∀ mode control, (machine.offset mode control).natAbs ≤ bound)
    (output_bounded : (machine.run state word).2.natAbs ≤ bound) :
    machine.cagedRun bound state word = some ⟨machine.run state word, output_bounded⟩ := by
  induction word generalizing state with
  | nil =>
      have start_bounded : state.2.natAbs ≤ bound := by
        simpa [run] using output_bounded
      simp [cagedRun, cage, run, start_bounded]
  | cons control word induction =>
      have tail_bounded :
          (machine.run (machine.step state control) word).2.natAbs ≤ bound := by
        simpa [run] using output_bounded
      have next_bounded : (machine.step state control).2.natAbs ≤ bound :=
        machine.start_natAbs_le_of_run_natAbs_le (machine.step state control) word bound
          offset_bounded tail_bounded
      have start_bounded : state.2.natAbs ≤ bound :=
        machine.predecessor_natAbs_le state control bound next_bounded
          (offset_bounded state.1 control)
      rw [cagedRun, List.foldl_cons]
      simp [cage, cagedStep, start_bounded, next_bounded]
      simpa [cage, cagedRun, run, next_bounded] using
        induction (machine.step state control) tail_bounded

private theorem step_eq_of_cagedStep_eq_some
    (machine : ExpandingAffineHistory Mode Control) (bound : Nat)
    (source target : CagedState Mode bound) (control : Control)
    (stepped : machine.cagedStep bound (some source) control = some target) :
    machine.step source.1 control = target.1 := by
  simp [cagedStep, cage] at stepped
  obtain ⟨_, state_eq⟩ := stepped
  exact congrArg Subtype.val state_eq

/-- Every live caged run projects to the original affine run. -/
theorem run_eq_of_cagedRun_eq_some (machine : ExpandingAffineHistory Mode Control)
    (state : State Mode) (word : List Control) (bound : Nat)
    (target : CagedState Mode bound)
    (caged : machine.cagedRun bound state word = some target) :
    machine.run state word = target.1 := by
  induction word using List.reverseRecOn generalizing target with
  | nil =>
      simp [cagedRun, cage] at caged
      obtain ⟨_, state_eq⟩ := caged
      exact congrArg Subtype.val state_eq
  | append_singleton word control induction =>
      have final_caged :
          machine.cagedStep bound (machine.cagedRun bound state word) control = some target := by
        simpa [cagedRun, List.foldl_append] using caged
      cases prefix_eq : machine.cagedRun bound state word with
      | none => simp [cagedStep, prefix_eq] at final_caged
      | some boxed =>
          have prefix_run : machine.run state word = boxed.1 :=
            induction boxed prefix_eq
          have final_caged' : machine.cagedStep bound (some boxed) control = some target := by
            simpa [prefix_eq] using final_caged
          have final_step : machine.step boxed.1 control = target.1 :=
            step_eq_of_cagedStep_eq_some machine bound boxed target control final_caged'
          calc
            machine.run state (word ++ [control]) =
                machine.step (machine.run state word) control := by
              simp [run, List.foldl_append]
            _ = target.1 := by rw [prefix_run, final_step]

/-- Words carrying one start state into a target section. -/
def targetLanguage (machine : ExpandingAffineHistory Mode Control) (start : State Mode)
    (target : Set (State Mode)) : Language Control :=
  {word | machine.run start word ∈ target}

/-- Finite-mode execution after forgetting the affine coordinate. -/
def modeRun (machine : ExpandingAffineHistory Mode Control) (start : Mode) :
    List Control → Mode :=
  List.foldl machine.nextMode start

/-- Words carrying one start mode into a prescribed mode section. -/
def modeLanguage (machine : ExpandingAffineHistory Mode Control) (start : Mode)
    (target : Set Mode) : Language Control :=
  {word | machine.modeRun start word ∈ target}

/-- The coordinate-forgetting mode automaton. -/
def modeDFA (machine : ExpandingAffineHistory Mode Control) (start : Mode)
    (target : Set Mode) : DFA Control Mode where
  step := machine.nextMode
  start := start
  accept := target

/-- Every whole-chart target language of a finite-mode machine is regular. -/
theorem modeLanguage_isRegular {Mode Control : Type} [Finite Mode]
    (machine : ExpandingAffineHistory Mode Control) (start : Mode) (target : Set Mode) :
    (machine.modeLanguage start target).IsRegular := by
  letI : Fintype Mode := Fintype.ofFinite Mode
  refine ⟨Mode, inferInstance, machine.modeDFA start target, ?_⟩
  rfl

/-- The finite automaton obtained by killing every transition which leaves the reverse box. -/
def cagedDFA (machine : ExpandingAffineHistory Mode Control) (start : State Mode)
    (target : Set (State Mode)) (bound : Nat) :
    DFA Control (Option (CagedState Mode bound)) where
  step := machine.cagedStep bound
  start := cage bound start
  accept := {state | ∃ caged, state = some caged ∧ caged.1 ∈ target}

/-- A bounded target language of a finite-mode expanding affine history machine is regular. -/
theorem targetLanguage_isRegular {Mode Control : Type} [Finite Mode]
    (machine : ExpandingAffineHistory Mode Control) (start : State Mode)
    (target : Set (State Mode)) (bound : Nat)
    (offset_bounded : ∀ mode control, (machine.offset mode control).natAbs ≤ bound)
    (target_bounded : ∀ state ∈ target, state.2.natAbs ≤ bound) :
    (machine.targetLanguage start target).IsRegular := by
  letI : Fintype (CagedState Mode bound) := (coordinateBox_finite bound).fintype
  refine ⟨Option (CagedState Mode bound), inferInstance,
    machine.cagedDFA start target bound, ?_⟩
  ext word
  constructor
  · rintro ⟨caged, evaluated, target_mem⟩
    have caged_run : machine.cagedRun bound start word = some caged := by
      simpa [cagedDFA, DFA.eval, DFA.evalFrom, cagedRun] using evaluated
    change machine.run start word ∈ target
    rw [machine.run_eq_of_cagedRun_eq_some start word bound caged caged_run]
    exact target_mem
  · intro target_mem
    have output_bounded := target_bounded (machine.run start word) target_mem
    refine ⟨⟨machine.run start word, output_bounded⟩, ?_, target_mem⟩
    simpa [cagedDFA, DFA.eval, DFA.evalFrom, cagedRun] using
      machine.cagedRun_eq_some start word bound offset_bounded output_bounded

end ExpandingAffineHistory

/-- Cleared integral data for the two-phase reset-affine architecture. -/
structure ClearedResetAffineHistory where
  /-- Source-dependent radix of each data control. -/
  radix : TagLetter → ℤ
  /-- Cleared phase-dependent digit of each data control. -/
  dataOffset : PairPhase → TagLetter → ℤ
  /-- Every data radix expands in both signs. -/
  radix_expanding : ∀ letter, 2 ≤ (radix letter).natAbs

namespace ClearedResetAffineHistory

/-- The cleared two-phase recurrence as a finite-mode expanding history machine. -/
def machine (parameters : ClearedResetAffineHistory) :
    ExpandingAffineHistory PairPhase PairedControl where
  nextMode phase control :=
    match control with
    | .toggle => phase.flip
    | .data _ => .erase
  scale _ control :=
    match control with
    | .toggle => 1
    | .data letter => parameters.radix letter
  offset phase control :=
    match control with
    | .toggle => 0
    | .data letter => parameters.dataOffset phase letter
  stationary_or_expanding phase control := by
    cases control with
    | toggle => exact Or.inl ⟨rfl, rfl⟩
    | data letter => exact Or.inr (parameters.radix_expanding letter)

@[simp] theorem machine_step_toggle (parameters : ClearedResetAffineHistory)
    (state : ExpandingAffineHistory.State PairPhase) :
    parameters.machine.step state .toggle = (state.1.flip, state.2) := by
  simp [machine, ExpandingAffineHistory.step]

@[simp] theorem machine_step_data (parameters : ClearedResetAffineHistory)
    (state : ExpandingAffineHistory.State PairPhase) (letter : TagLetter) :
    parameters.machine.step state (.data letter) =
      (.erase, parameters.radix letter * state.2 + parameters.dataOffset state.1 letter) := by
  simp [machine, ExpandingAffineHistory.step]

/-- Every bounded target section of a cleared reset-affine recurrence has a finite reverse
orbit. -/
theorem reverseOrbit_finite (parameters : ClearedResetAffineHistory)
    (target : Set (ExpandingAffineHistory.State PairPhase)) (bound : Nat)
    (offset_bounded : ∀ phase letter,
      (parameters.dataOffset phase letter).natAbs ≤ bound)
    (target_bounded : ∀ state ∈ target, state.2.natAbs ≤ bound) :
    (parameters.machine.reverseOrbit target).Finite := by
  apply ExpandingAffineHistory.reverseOrbit_finite parameters.machine target bound
  · intro phase control
    cases control with
    | toggle => simp [machine]
    | data letter => exact offset_bounded phase letter
  · exact target_bounded

end ClearedResetAffineHistory

namespace Undecidability.UniversalNeary

/-- Free-monoid zero existence for the paired compiler on the fixed universal Neary family. -/
noncomputable def universalPairedZero (index : Nat.Partrec.Code) : Prop :=
  ∃ word : List PairedControl,
    pairedCoefficient ℚ source.width (source.body index) word = 0

/-- The universal paired zero language is exactly halting, including the empty-word audit. -/
theorem universalPairedZero_iff_codeHalts (index : Nat.Partrec.Code) :
    universalPairedZero index ↔ CodeHalts index := by
  have zero_iff_nonempty :
      universalPairedZero index ↔
        WordSeries.HasNonemptyZero
          (pairedCoefficient ℚ source.width (source.body index)) := by
    constructor
    · rintro ⟨word, coefficient_zero⟩
      have word_nonempty : word ≠ [] := by
        intro word_empty
        subst word
        exact pairedCoefficient_nil_ne_zero source.width (source.body index) coefficient_zero
      exact ⟨word, word_nonempty, coefficient_zero⟩
    · rintro ⟨word, _, coefficient_zero⟩
      exact ⟨word, coefficient_zero⟩
  rw [zero_iff_nonempty, paired_zero_rat_iff_terminal_match,
    terminal_match_iff_tagHaltsFrom source.width (source.body index) source.width_large
      (source.body_long index) (source.body_divisible index),
    tagHaltsFrom_iff_codeHalts]

/-- No algorithm decides zero existence for the universal paired family. -/
theorem universalPairedZero_not_computable :
    ¬ComputablePred universalPairedZero := by
  intro paired_computable
  apply codeHalts_not_computable
  exact ComputablePred.of_eq paired_computable universalPairedZero_iff_codeHalts

/-- Any total computable predicate with exactly the universal paired zeros is impossible. -/
theorem no_computable_sameZero_predicate (candidate : Nat.Partrec.Code → Prop)
    (candidate_computable : ComputablePred candidate)
    (same_zero : ∀ index, candidate index ↔ universalPairedZero index) : False :=
  universalPairedZero_not_computable
    (ComputablePred.of_eq candidate_computable same_zero)

end Undecidability.UniversalNeary

end MatrixMortality
