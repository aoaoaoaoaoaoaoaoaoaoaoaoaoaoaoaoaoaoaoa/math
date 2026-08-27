import MatrixMortality.MixedBranchingHistory

/-!
# Integral recognition of equal-length branching

An integral singular three-state recognizer for the complete raw-control zero language of the
mixed width-three body `bcbcbb`.
-/

namespace MatrixMortality
namespace MixedBranchingRecognizer
open PeriodicHistory BranchingRecognizer
open scoped Matrix

/-! ## Integral three-state recognizer -/

private def carryB : ℤ := 3703455
private def carryC : ℤ := 5236172
private def toggleCentre : ℤ := 21436039
private def acceptingCarry : ℤ := 216186449

/-- Singular integral data generators. Their first coordinate is a transient guard and their
second coordinate is the persistent affine carry. -/
def recognizerData : TagLetter → Matrix (Fin 3) (Fin 3) ℤ
  | .b =>
      !![0, 2, 1;
         0, 5, carryB;
         0, 0, 1]
  | .c =>
      !![0, 2, -432372898;
         0, 7, carryC;
         0, 0, 1]

/-- The two singular data generators and the integral affine involution. -/
def recognizerGenerator : PairedControl → Matrix (Fin 3) (Fin 3) ℤ
  | .data letter => recognizerData letter
  | .toggle =>
      !![1, 0, 0;
         0, -1, toggleCentre;
         0, 0, 1]

/-- Boundary row selecting the refreshed guard. -/
def recognizerRow : Fin 3 → ℤ := ![1, 0, 0]

/-- Homogeneous state before the boundary toggle. -/
def recognizerDelta : Fin 3 → ℤ := ![1, 0, 1]

/-- Boundary column obtained by toggling `recognizerDelta`. -/
def recognizerColumn : Fin 3 → ℤ := ![1, toggleCentre, 1]

/-- Persistent integer carry driven from the right end of a raw control word. -/
def recognizerCarry : List PairedControl → ℤ
  | [] => 0
  | .data .b :: word => 5 * recognizerCarry word + carryB
  | .data .c :: word => 7 * recognizerCarry word + carryC
  | .toggle :: word => toggleCentre - recognizerCarry word

/-- Transient guard refreshed by every data control. -/
def recognizerGuard : List PairedControl → ℤ
  | [] => 1
  | .data .b :: word => 2 * recognizerCarry word + 1
  | .data .c :: word => 2 * (recognizerCarry word - acceptingCarry)
  | .toggle :: word => recognizerGuard word

/-- Exact affine state of every raw control word. -/
theorem recognizerProduct_mulVec_delta (word : List PairedControl) :
    wordProduct recognizerGenerator word *ᵥ recognizerDelta =
      ![recognizerGuard word, recognizerCarry word, 1] := by
  induction word with
  | nil =>
      ext coordinate
      fin_cases coordinate <;>
        simp [wordProduct, recognizerDelta, recognizerGuard, recognizerCarry]
  | cons control word induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec, induction]
      cases control with
      | toggle =>
          ext coordinate
          fin_cases coordinate <;>
            simp [recognizerGenerator, recognizerGuard, recognizerCarry, Matrix.mulVec,
              Matrix.dotProduct, Fin.sum_univ_succ, toggleCentre]
          ring
      | data letter =>
          cases letter <;> ext coordinate <;> fin_cases coordinate
          all_goals simp [recognizerGenerator, recognizerData, recognizerGuard,
            recognizerCarry, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ,
            carryB, carryC, acceptingCarry]
          all_goals ring

theorem recognizerColumn_eq_toggle_delta :
    recognizerColumn = recognizerGenerator .toggle *ᵥ recognizerDelta := by
  ext coordinate
  fin_cases coordinate <;>
    norm_num [recognizerColumn, recognizerGenerator, recognizerDelta, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_succ, toggleCentre]

/-- Scalar coefficient of the explicit integral representation. -/
def recognizerCoefficient (word : List PairedControl) : ℤ :=
  linearCoefficient recognizerGenerator recognizerRow recognizerColumn word

theorem recognizerCoefficient_eq_guard (word : List PairedControl) :
    recognizerCoefficient word = recognizerGuard (word ++ [.toggle]) := by
  have state : wordProduct recognizerGenerator word *ᵥ recognizerColumn =
      ![recognizerGuard (word ++ [.toggle]),
        recognizerCarry (word ++ [.toggle]), 1] := by
    calc
      wordProduct recognizerGenerator word *ᵥ recognizerColumn =
          wordProduct recognizerGenerator word *ᵥ
            (recognizerGenerator .toggle *ᵥ recognizerDelta) := by
              rw [← recognizerColumn_eq_toggle_delta]
      _ = (wordProduct recognizerGenerator word * recognizerGenerator .toggle) *ᵥ
          recognizerDelta := by rw [Matrix.mulVec_mulVec]
      _ = wordProduct recognizerGenerator (word ++ [.toggle]) *ᵥ recognizerDelta := by
        rw [wordProduct_append]
        simp [wordProduct]
      _ = _ := recognizerProduct_mulVec_delta (word ++ [.toggle])
  rw [recognizerCoefficient, linearCoefficient, state]
  simp [recognizerRow, Matrix.dotProduct, Fin.sum_univ_succ]

@[simp] theorem recognizerData_det (letter : TagLetter) :
    (recognizerData letter).det = 0 := by
  cases letter <;>
    norm_num [recognizerData, Matrix.det_fin_three, Matrix.vecHead, Matrix.vecTail,
      carryB, carryC]

@[simp] theorem recognizerToggle_det :
    (recognizerGenerator .toggle).det = -1 := by
  norm_num [recognizerGenerator, Matrix.det_fin_three, Matrix.vecHead, Matrix.vecTail,
    toggleCentre]

theorem recognizerToggle_involutive :
    recognizerGenerator .toggle * recognizerGenerator .toggle = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [recognizerGenerator, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ,
      toggleCentre] <;>
    split <;> simp_all

/-! ## Centred macro dynamics -/

/-- One data control, optionally preceded by the only toggle permitted in toggle-normal form. -/
private inductive CarryMacro where
  | b
  | tb
  | c
  | tc
  deriving DecidableEq

private def plainMacro : TagLetter → CarryMacro
  | .b => .b
  | .c => .c

private def flippedMacro : TagLetter → CarryMacro
  | .b => .tb
  | .c => .tc

private def CarryMacro.controls : CarryMacro → List PairedControl
  | .b => [.data .b]
  | .tb => [.toggle, .data .b]
  | .c => [.data .c]
  | .tc => [.toggle, .data .c]

private def expandMacros : List CarryMacro → List PairedControl
  | [] => []
  | token :: tokens => token.controls ++ expandMacros tokens

private def terminalToggle : Bool → List PairedControl
  | false => []
  | true => [.toggle]

private theorem ToggleNormal.exists_macro_expansion {word : List PairedControl}
    (normal : ToggleNormal word) :
    ∃ macros trailing,
      word = expandMacros macros ++ terminalToggle trailing := by
  induction normal with
  | nil => exact ⟨[], false, rfl⟩
  | toggle => exact ⟨[], true, rfl⟩
  | data letter _ induction =>
      obtain ⟨macros, trailing, rfl⟩ := induction
      exact ⟨plainMacro letter :: macros, trailing, by
        cases letter <;>
          simp [expandMacros, plainMacro, CarryMacro.controls, List.append_assoc]⟩
  | toggleData letter _ induction =>
      obtain ⟨macros, trailing, rfl⟩ := induction
      exact ⟨flippedMacro letter :: macros, trailing, by
        cases letter <;>
          simp [expandMacros, flippedMacro, CarryMacro.controls, List.append_assoc]⟩

private def centredCarry (word : List PairedControl) : ℤ :=
  2 * recognizerCarry word - toggleCentre

private def macroAction : CarryMacro → ℤ → ℤ
  | .b, state => 5 * state + 93151066
  | .tb, state => -5 * state - 93151066
  | .c, state => 7 * state + 139088578
  | .tc, state => -7 * state - 139088578

/-- Apply a macro word from its right end, matching matrix-product order. -/
private def macroEvaluate : List CarryMacro → ℤ → ℤ
  | [], base => base
  | token :: tokens, base => macroAction token (macroEvaluate tokens base)

private theorem centredCarry_macro (token : CarryMacro) (word : List PairedControl) :
    centredCarry (token.controls ++ word) = macroAction token (centredCarry word) := by
  cases token <;>
    simp [CarryMacro.controls, centredCarry, recognizerCarry, macroAction, carryB, carryC,
      toggleCentre] <;>
    ring

private theorem centredCarry_expansion (macros : List CarryMacro) (trailing : Bool) :
    centredCarry (expandMacros macros ++ terminalToggle trailing) =
      macroEvaluate macros (if trailing then toggleCentre else -toggleCentre) := by
  induction macros with
  | nil =>
      cases trailing <;>
        norm_num [expandMacros, terminalToggle, centredCarry, recognizerCarry,
          toggleCentre, macroEvaluate]
  | cons token tokens induction =>
      rw [expandMacros, List.append_assoc, centredCarry_macro, induction]
      rfl

private def initialState : ℤ := -21436039
private def targetState : ℤ := 410936859

private theorem carry_eq_accepting_iff_centred (word : List PairedControl) :
    recognizerCarry word = acceptingCarry ↔ centredCarry word = targetState := by
  simp [centredCarry, acceptingCarry, targetState, toggleCentre]
  omega

private theorem trailingBase_cases (trailing : Bool) :
    (if trailing then toggleCentre else -toggleCentre) = initialState ∨
      (if trailing then toggleCentre else -toggleCentre) = -initialState := by
  cases trailing <;> simp [toggleCentre, initialState]

/-! The following lemmas are the complete inverse congruence graph. Each omitted macro is
excluded over all integer predecessor states, rather than merely on a sampled orbit. -/

private theorem inverse_initial (token : CarryMacro) (tokens : List CarryMacro) (base : ℤ) :
    macroEvaluate (token :: tokens) base = initialState ↔
      token = .b ∧ macroEvaluate tokens base = -22917421 := by
  cases token <;> simp [macroEvaluate, macroAction, initialState] <;> omega

private theorem inverse_return₁ (token : CarryMacro) (tokens : List CarryMacro) (base : ℤ) :
    macroEvaluate (token :: tokens) base = -22917421 ↔
      token = .tb ∧ macroEvaluate tokens base = -14046729 := by
  cases token <;> simp [macroEvaluate, macroAction] <;> omega

private theorem inverse_return₂ (token : CarryMacro) (tokens : List CarryMacro) (base : ℤ) :
    macroEvaluate (token :: tokens) base = -14046729 ↔
      token = .b ∧ macroEvaluate tokens base = -21439559 := by
  cases token <;> simp [macroEvaluate, macroAction] <;> omega

private theorem inverse_return_fork (token : CarryMacro) (tokens : List CarryMacro) (base : ℤ) :
    macroEvaluate (token :: tokens) base = -21439559 ↔
      (token = .b ∧ macroEvaluate tokens base = -22918125) ∨
        (token = .c ∧ macroEvaluate tokens base = -22932591) := by
  cases token <;> simp [macroEvaluate, macroAction] <;> omega

private theorem inverse_returnA₄ (token : CarryMacro) (tokens : List CarryMacro) (base : ℤ) :
    macroEvaluate (token :: tokens) base = -22918125 ↔
      token = .tc ∧ macroEvaluate tokens base = -16595779 := by
  cases token <;> simp [macroEvaluate, macroAction] <;> omega

private theorem inverse_returnA₅ (token : CarryMacro) (tokens : List CarryMacro) (base : ℤ) :
    macroEvaluate (token :: tokens) base = -16595779 ↔
      token = .b ∧ macroEvaluate tokens base = -21949369 := by
  cases token <;> simp [macroEvaluate, macroAction] <;> omega

private theorem inverse_returnA₆ (token : CarryMacro) (tokens : List CarryMacro) (base : ℤ) :
    macroEvaluate (token :: tokens) base = -21949369 ↔
      (token = .c ∧ macroEvaluate tokens base = -23005421) ∨
        (token = .b ∧ macroEvaluate tokens base = -23020087) := by
  cases token <;> simp [macroEvaluate, macroAction] <;> omega

private theorem inverse_returnA_dead₁ (token : CarryMacro) (tokens : List CarryMacro)
    (base : ℤ) :
    macroEvaluate (token :: tokens) base = -23020087 ↔
      token = .tc ∧ macroEvaluate tokens base = -16581213 := by
  cases token <;> simp [macroEvaluate, macroAction] <;> omega

private theorem inverse_returnA_dead₂ (token : CarryMacro) (tokens : List CarryMacro)
    (base : ℤ) :
    macroEvaluate (token :: tokens) base ≠ -16581213 := by
  cases token <;> simp [macroEvaluate, macroAction] <;> omega

private theorem inverse_returnB₄ (token : CarryMacro) (tokens : List CarryMacro) (base : ℤ) :
    macroEvaluate (token :: tokens) base = -22932591 ↔
      token = .tb ∧ macroEvaluate tokens base = -14043695 := by
  cases token <;> simp [macroEvaluate, macroAction] <;> omega

private theorem inverse_returnB₅ (token : CarryMacro) (tokens : List CarryMacro) (base : ℤ) :
    macroEvaluate (token :: tokens) base = -14043695 ↔
      token = .c ∧ macroEvaluate tokens base = -21876039 := by
  cases token <;> simp [macroEvaluate, macroAction] <;> omega

private theorem inverse_returnB₆ (token : CarryMacro) (tokens : List CarryMacro) (base : ℤ) :
    macroEvaluate (token :: tokens) base = -21876039 ↔
      token = .b ∧ macroEvaluate tokens base = -23005421 := by
  cases token <;> simp [macroEvaluate, macroAction] <;> omega

private theorem inverse_return₇ (token : CarryMacro) (tokens : List CarryMacro) (base : ℤ) :
    macroEvaluate (token :: tokens) base = -23005421 ↔
      token = .tb ∧ macroEvaluate tokens base = -14029129 := by
  cases token <;> simp [macroEvaluate, macroAction] <;> omega

private theorem inverse_return₈ (token : CarryMacro) (tokens : List CarryMacro) (base : ℤ) :
    macroEvaluate (token :: tokens) base = -14029129 ↔
      token = .b ∧ macroEvaluate tokens base = initialState := by
  cases token <;> simp [macroEvaluate, macroAction, initialState] <;> omega

private theorem inverse_target (token : CarryMacro) (tokens : List CarryMacro) (base : ℤ) :
    macroEvaluate (token :: tokens) base = targetState ↔
      token = .tb ∧ macroEvaluate tokens base = -100817585 := by
  cases token <;> simp [macroEvaluate, macroAction, targetState] <;> omega

private theorem inverse_prefix₁ (token : CarryMacro) (tokens : List CarryMacro) (base : ℤ) :
    macroEvaluate (token :: tokens) base = -100817585 ↔
      token = .c ∧ macroEvaluate tokens base = -34272309 := by
  cases token <;> simp [macroEvaluate, macroAction] <;> omega

private theorem inverse_prefix₂ (token : CarryMacro) (tokens : List CarryMacro) (base : ℤ) :
    macroEvaluate (token :: tokens) base = -34272309 ↔
      (token = .b ∧ macroEvaluate tokens base = -25484675) ∨
        (token = .c ∧ macroEvaluate tokens base = -24765841) := by
  cases token <;> simp [macroEvaluate, macroAction] <;> omega

private theorem inverse_prefix_dead₁ (token : CarryMacro) (tokens : List CarryMacro)
    (base : ℤ) :
    macroEvaluate (token :: tokens) base = -24765841 ↔
      token = .tb ∧ macroEvaluate tokens base = -13677045 := by
  cases token <;> simp [macroEvaluate, macroAction] <;> omega

private theorem inverse_prefix_dead₂ (token : CarryMacro) (tokens : List CarryMacro)
    (base : ℤ) :
    macroEvaluate (token :: tokens) base ≠ -13677045 := by
  cases token <;> simp [macroEvaluate, macroAction] <;> omega

private theorem inverse_prefix₃ (token : CarryMacro) (tokens : List CarryMacro) (base : ℤ) :
    macroEvaluate (token :: tokens) base = -25484675 ↔
      token = .tc ∧ macroEvaluate tokens base = -16229129 := by
  cases token <;> simp [macroEvaluate, macroAction] <;> omega

private theorem inverse_prefix₄ (token : CarryMacro) (tokens : List CarryMacro) (base : ℤ) :
    macroEvaluate (token :: tokens) base = -16229129 ↔
      token = .b ∧ macroEvaluate tokens base = -21876039 := by
  cases token <;> simp [macroEvaluate, macroAction] <;> omega

private def returnBlockA : List CarryMacro :=
  [.b, .tb, .b, .b, .tc, .b, .c, .tb, .b]

private def returnBlockB : List CarryMacro :=
  [.b, .tb, .b, .c, .tb, .c, .b, .tb, .b]

private def returnBlock : Bool → List CarryMacro
  | false => returnBlockA
  | true => returnBlockB

private def returnMacros : List Bool → List CarryMacro
  | [] => []
  | bit :: bits => returnBlock bit ++ returnMacros bits

private def prefixMacros : List CarryMacro :=
  [.tb, .c, .b, .tc, .b, .b, .tb, .b]

private def AdmissibleBase (base : ℤ) : Prop :=
  base = initialState ∨ base = -initialState

private theorem reject_fixed_base {base target : ℤ} (base_ok : AdmissibleBase base)
    (positiveTarget : target ≠ initialState) (negativeTarget : target ≠ -initialState)
    (equality : base = target) : False := by
  rcases base_ok with rfl | rfl
  · exact positiveTarget equality.symm
  · exact negativeTarget equality.symm

/-- Peel one complete first-return block from every nonempty admissible computation ending at
the distinguished return state. -/
private theorem peel_return {tokens : List CarryMacro} {base : ℤ}
    (base_ok : AdmissibleBase base)
    (accepted : macroEvaluate tokens base = initialState) :
    tokens = [] ∨
      (∃ tail, tokens = returnBlockA ++ tail ∧
        macroEvaluate tail base = initialState) ∨
      (∃ tail, tokens = returnBlockB ++ tail ∧
        macroEvaluate tail base = initialState) := by
  cases tokens with
  | nil => exact Or.inl rfl
  | cons token₀ tokens₀ =>
      obtain ⟨rfl, state₁⟩ := (inverse_initial token₀ tokens₀ base).mp accepted
      cases tokens₀ with
      | nil =>
          exact False.elim (reject_fixed_base base_ok (by norm_num [initialState])
            (by norm_num [initialState]) state₁)
      | cons token₁ tokens₁ =>
          obtain ⟨rfl, state₂⟩ := (inverse_return₁ token₁ tokens₁ base).mp state₁
          cases tokens₁ with
          | nil =>
              exact False.elim (reject_fixed_base base_ok (by norm_num [initialState])
                (by norm_num [initialState]) state₂)
          | cons token₂ tokens₂ =>
              obtain ⟨rfl, state₃⟩ := (inverse_return₂ token₂ tokens₂ base).mp state₂
              cases tokens₂ with
              | nil =>
                  exact False.elim (reject_fixed_base base_ok (by norm_num [initialState])
                    (by norm_num [initialState]) state₃)
              | cons token₃ tokens₃ =>
                  rcases (inverse_return_fork token₃ tokens₃ base).mp state₃ with
                    branchA | branchB
                  · obtain ⟨rfl, state₄⟩ := branchA
                    cases tokens₃ with
                    | nil =>
                        exact False.elim (reject_fixed_base base_ok
                          (by norm_num [initialState]) (by norm_num [initialState]) state₄)
                    | cons token₄ tokens₄ =>
                        obtain ⟨rfl, state₅⟩ :=
                          (inverse_returnA₄ token₄ tokens₄ base).mp state₄
                        cases tokens₄ with
                        | nil =>
                            exact False.elim (reject_fixed_base base_ok
                              (by norm_num [initialState]) (by norm_num [initialState]) state₅)
                        | cons token₅ tokens₅ =>
                            obtain ⟨rfl, state₆⟩ :=
                              (inverse_returnA₅ token₅ tokens₅ base).mp state₅
                            cases tokens₅ with
                            | nil =>
                                exact False.elim (reject_fixed_base base_ok
                                  (by norm_num [initialState]) (by norm_num [initialState])
                                  state₆)
                            | cons token₆ tokens₆ =>
                                rcases (inverse_returnA₆ token₆ tokens₆ base).mp state₆ with
                                  success | dead
                                · obtain ⟨rfl, state₇⟩ := success
                                  cases tokens₆ with
                                  | nil =>
                                      exact False.elim (reject_fixed_base base_ok
                                        (by norm_num [initialState])
                                        (by norm_num [initialState]) state₇)
                                  | cons token₇ tokens₇ =>
                                      obtain ⟨rfl, state₈⟩ :=
                                        (inverse_return₇ token₇ tokens₇ base).mp state₇
                                      cases tokens₇ with
                                      | nil =>
                                          exact False.elim (reject_fixed_base base_ok
                                            (by norm_num [initialState])
                                            (by norm_num [initialState]) state₈)
                                      | cons token₈ tail =>
                                          obtain ⟨rfl, returned⟩ :=
                                            (inverse_return₈ token₈ tail base).mp state₈
                                          exact Or.inr (Or.inl ⟨tail, by
                                            simp [returnBlockA], returned⟩)
                                · obtain ⟨rfl, dead₁⟩ := dead
                                  cases tokens₆ with
                                  | nil =>
                                      exact False.elim (reject_fixed_base base_ok
                                        (by norm_num [initialState])
                                        (by norm_num [initialState]) dead₁)
                                  | cons token₇ tokens₇ =>
                                      obtain ⟨rfl, dead₂⟩ :=
                                        (inverse_returnA_dead₁ token₇ tokens₇ base).mp dead₁
                                      cases tokens₇ with
                                      | nil =>
                                          exact False.elim (reject_fixed_base base_ok
                                            (by norm_num [initialState])
                                            (by norm_num [initialState]) dead₂)
                                      | cons token₈ tail =>
                                          exact False.elim
                                            (inverse_returnA_dead₂ token₈ tail base dead₂)
                  · obtain ⟨rfl, state₄⟩ := branchB
                    cases tokens₃ with
                    | nil =>
                        exact False.elim (reject_fixed_base base_ok
                          (by norm_num [initialState]) (by norm_num [initialState]) state₄)
                    | cons token₄ tokens₄ =>
                        obtain ⟨rfl, state₅⟩ :=
                          (inverse_returnB₄ token₄ tokens₄ base).mp state₄
                        cases tokens₄ with
                        | nil =>
                            exact False.elim (reject_fixed_base base_ok
                              (by norm_num [initialState]) (by norm_num [initialState]) state₅)
                        | cons token₅ tokens₅ =>
                            obtain ⟨rfl, state₆⟩ :=
                              (inverse_returnB₅ token₅ tokens₅ base).mp state₅
                            cases tokens₅ with
                            | nil =>
                                exact False.elim (reject_fixed_base base_ok
                                  (by norm_num [initialState]) (by norm_num [initialState])
                                  state₆)
                            | cons token₆ tokens₆ =>
                                obtain ⟨rfl, state₇⟩ :=
                                  (inverse_returnB₆ token₆ tokens₆ base).mp state₆
                                cases tokens₆ with
                                | nil =>
                                    exact False.elim (reject_fixed_base base_ok
                                      (by norm_num [initialState])
                                      (by norm_num [initialState]) state₇)
                                | cons token₇ tokens₇ =>
                                    obtain ⟨rfl, state₈⟩ :=
                                      (inverse_return₇ token₇ tokens₇ base).mp state₇
                                    cases tokens₇ with
                                    | nil =>
                                        exact False.elim (reject_fixed_base base_ok
                                          (by norm_num [initialState])
                                          (by norm_num [initialState]) state₈)
                                    | cons token₈ tail =>
                                        obtain ⟨rfl, returned⟩ :=
                                          (inverse_return₈ token₈ tail base).mp state₈
                                        exact Or.inr (Or.inr ⟨tail, by
                                          simp [returnBlockB], returned⟩)

private theorem returnBlockA_to_initial (tokens : List CarryMacro) (base : ℤ) :
    macroEvaluate (returnBlockA ++ tokens) base = initialState ↔
      macroEvaluate tokens base = initialState := by
  simp [returnBlockA, macroEvaluate, macroAction, initialState]
  omega

private theorem returnBlockB_to_initial (tokens : List CarryMacro) (base : ℤ) :
    macroEvaluate (returnBlockB ++ tokens) base = initialState ↔
      macroEvaluate tokens base = initialState := by
  simp [returnBlockB, macroEvaluate, macroAction, initialState]
  omega

private theorem returnMacros_accept (bits : List Bool) :
    macroEvaluate (returnMacros bits) initialState = initialState := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      rw [returnMacros]
      cases bit
      · exact (returnBlockA_to_initial (returnMacros bits) initialState).mpr induction
      · exact (returnBlockB_to_initial (returnMacros bits) initialState).mpr induction

/-- The closed return graph accepts exactly concatenations of the two nine-macro returns; an
unmatched terminal toggle is excluded by carrying both possible terminal bases through the
proof. -/
private theorem classify_returns (tokens : List CarryMacro) (base : ℤ)
    (base_ok : AdmissibleBase base) :
    macroEvaluate tokens base = initialState ↔
      base = initialState ∧ ∃ bits, tokens = returnMacros bits := by
  constructor
  · intro accepted
    rcases peel_return base_ok accepted with empty | blockA | blockB
    · subst tokens
      refine ⟨?_, [], rfl⟩
      simpa [macroEvaluate] using accepted
    · obtain ⟨tail, equality, returned⟩ := blockA
      have classified := (classify_returns tail base base_ok).mp returned
      obtain ⟨base_eq, bits, rfl⟩ := classified
      refine ⟨base_eq, false :: bits, ?_⟩
      simpa [returnMacros, returnBlock] using equality
    · obtain ⟨tail, equality, returned⟩ := blockB
      have classified := (classify_returns tail base base_ok).mp returned
      obtain ⟨base_eq, bits, rfl⟩ := classified
      refine ⟨base_eq, true :: bits, ?_⟩
      simpa [returnMacros, returnBlock] using equality
  · rintro ⟨rfl, bits, rfl⟩
    exact returnMacros_accept bits
termination_by tokens.length
decreasing_by
  all_goals subst tokens
  all_goals simp [returnBlockA, returnBlockB]
  all_goals omega

/-- Peel the unique eight-macro entrance path. The only competing branch reaches a congruence
dead end before either admissible terminal base. -/
private theorem peel_prefix {tokens : List CarryMacro} {base : ℤ}
    (base_ok : AdmissibleBase base)
    (accepted : macroEvaluate tokens base = targetState) :
    ∃ tail, tokens = prefixMacros ++ tail ∧
      macroEvaluate tail base = initialState := by
  cases tokens with
  | nil =>
      exact False.elim (reject_fixed_base base_ok (by norm_num [initialState, targetState])
        (by norm_num [initialState, targetState]) accepted)
  | cons token₀ tokens₀ =>
      obtain ⟨rfl, state₁⟩ := (inverse_target token₀ tokens₀ base).mp accepted
      cases tokens₀ with
      | nil =>
          exact False.elim (reject_fixed_base base_ok (by norm_num [initialState])
            (by norm_num [initialState]) state₁)
      | cons token₁ tokens₁ =>
          obtain ⟨rfl, state₂⟩ := (inverse_prefix₁ token₁ tokens₁ base).mp state₁
          cases tokens₁ with
          | nil =>
              exact False.elim (reject_fixed_base base_ok (by norm_num [initialState])
                (by norm_num [initialState]) state₂)
          | cons token₂ tokens₂ =>
              rcases (inverse_prefix₂ token₂ tokens₂ base).mp state₂ with success | dead
              · obtain ⟨rfl, state₃⟩ := success
                cases tokens₂ with
                | nil =>
                    exact False.elim (reject_fixed_base base_ok
                      (by norm_num [initialState]) (by norm_num [initialState]) state₃)
                | cons token₃ tokens₃ =>
                    obtain ⟨rfl, state₄⟩ :=
                      (inverse_prefix₃ token₃ tokens₃ base).mp state₃
                    cases tokens₃ with
                    | nil =>
                        exact False.elim (reject_fixed_base base_ok
                          (by norm_num [initialState]) (by norm_num [initialState]) state₄)
                    | cons token₄ tokens₄ =>
                        obtain ⟨rfl, state₅⟩ :=
                          (inverse_prefix₄ token₄ tokens₄ base).mp state₄
                        cases tokens₄ with
                        | nil =>
                            exact False.elim (reject_fixed_base base_ok
                              (by norm_num [initialState]) (by norm_num [initialState]) state₅)
                        | cons token₅ tokens₅ =>
                            obtain ⟨rfl, state₆⟩ :=
                              (inverse_returnB₆ token₅ tokens₅ base).mp state₅
                            cases tokens₅ with
                            | nil =>
                                exact False.elim (reject_fixed_base base_ok
                                  (by norm_num [initialState]) (by norm_num [initialState])
                                  state₆)
                            | cons token₆ tokens₆ =>
                                obtain ⟨rfl, state₇⟩ :=
                                  (inverse_return₇ token₆ tokens₆ base).mp state₆
                                cases tokens₆ with
                                | nil =>
                                    exact False.elim (reject_fixed_base base_ok
                                      (by norm_num [initialState])
                                      (by norm_num [initialState]) state₇)
                                | cons token₇ tail =>
                                    obtain ⟨rfl, returned⟩ :=
                                      (inverse_return₈ token₇ tail base).mp state₇
                                    exact ⟨tail, by simp [prefixMacros], returned⟩
              · obtain ⟨rfl, dead₁⟩ := dead
                cases tokens₂ with
                | nil =>
                    exact False.elim (reject_fixed_base base_ok
                      (by norm_num [initialState]) (by norm_num [initialState]) dead₁)
                | cons token₃ tokens₃ =>
                    obtain ⟨rfl, dead₂⟩ :=
                      (inverse_prefix_dead₁ token₃ tokens₃ base).mp dead₁
                    cases tokens₃ with
                    | nil =>
                        exact False.elim (reject_fixed_base base_ok
                          (by norm_num [initialState]) (by norm_num [initialState]) dead₂)
                    | cons token₄ tail =>
                        exact False.elim (inverse_prefix_dead₂ token₄ tail base dead₂)

private theorem prefix_to_target (tokens : List CarryMacro) (base : ℤ) :
    macroEvaluate (prefixMacros ++ tokens) base = targetState ↔
      macroEvaluate tokens base = initialState := by
  simp [prefixMacros, macroEvaluate, macroAction, targetState, initialState]
  omega

/-- Complete target classification of the inverse graph. -/
private theorem classify_target (tokens : List CarryMacro) (base : ℤ)
    (base_ok : AdmissibleBase base) :
    macroEvaluate tokens base = targetState ↔
      base = initialState ∧
        ∃ bits, tokens = prefixMacros ++ returnMacros bits := by
  constructor
  · intro accepted
    obtain ⟨tail, rfl, returned⟩ := peel_prefix base_ok accepted
    obtain ⟨base_eq, bits, rfl⟩ :=
      (classify_returns tail base base_ok).mp returned
    exact ⟨base_eq, bits, rfl⟩
  · rintro ⟨rfl, bits, rfl⟩
    exact (prefix_to_target (returnMacros bits) initialState).mpr
      (returnMacros_accept bits)

@[simp] private theorem expandMacros_append (left right : List CarryMacro) :
    expandMacros (left ++ right) = expandMacros left ++ expandMacros right := by
  induction left with
  | nil => rfl
  | cons token tokens induction =>
      simp [expandMacros, induction, List.append_assoc]

private theorem expand_returnBlock (bit : Bool) :
    expandMacros (returnBlock bit) = historyControl (nullBlock bit) := by
  cases bit <;>
    simp [returnBlock, returnBlockA, returnBlockB, expandMacros, CarryMacro.controls,
      nullBlock, nullBlockA, nullBlockB, historyControl, strokeControl, strokeBBB,
      strokeBCB, strokeCBC, strokeCBB, stroke₃]

private theorem expand_returnMacros (bits : List Bool) :
    expandMacros (returnMacros bits) = historyControl (nullHistory bits) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      simp [returnMacros, nullHistory, expand_returnBlock, induction, historyControl_append]

private theorem expand_terminalMacros (bits : List Bool) :
    expandMacros (.c :: prefixMacros ++ returnMacros bits) =
      historyControl (terminalHistory bits) := by
  change CarryMacro.controls .c ++
      expandMacros (prefixMacros ++ returnMacros bits) = _
  rw [expandMacros_append, expand_returnMacros]
  simp [prefixMacros, expandMacros, CarryMacro.controls, terminalHistory, prefixHistory,
    historyControl_append, historyControl, strokeControl, strokeCBC, strokeBCB, strokeBBB,
    stroke₃, List.append_assoc]

private theorem terminalControl_eq_macro_expansion (bits : List Bool) :
    terminalControl bits =
      expandMacros (.c :: prefixMacros ++ returnMacros bits) ++ [.toggle] := by
  rw [terminalControl, expand_terminalMacros]

private theorem toggle_terminalControl_eq_macro_expansion (bits : List Bool) :
    .toggle :: terminalControl bits =
      expandMacros (.tc :: prefixMacros ++ returnMacros bits) ++ [.toggle] := by
  rw [terminalControl_eq_macro_expansion]
  simp [expandMacros, CarryMacro.controls]

/-- Appending the boundary toggle reverses the two possible terminal bases of a normal macro
word. -/
private theorem centredCarry_boundary_expansion (tokens : List CarryMacro)
    (trailing : Bool) :
    centredCarry
        ((expandMacros tokens ++ terminalToggle trailing) ++ [.toggle]) =
      macroEvaluate tokens (if trailing then initialState else -initialState) := by
  induction tokens with
  | nil =>
      cases trailing <;>
        norm_num [expandMacros, terminalToggle, centredCarry, recognizerCarry,
          toggleCentre, initialState, macroEvaluate]
  | cons token tokens induction =>
      calc
        centredCarry
            ((expandMacros (token :: tokens) ++ terminalToggle trailing) ++ [.toggle]) =
            centredCarry
              (token.controls ++
                ((expandMacros tokens ++ terminalToggle trailing) ++ [.toggle])) := by
                  simp [expandMacros, List.append_assoc]
        _ = macroAction token
              (centredCarry
                ((expandMacros tokens ++ terminalToggle trailing) ++ [.toggle])) :=
          centredCarry_macro token _
        _ = macroAction token
              (macroEvaluate tokens (if trailing then initialState else -initialState)) := by
          rw [induction]
        _ = macroEvaluate (token :: tokens)
              (if trailing then initialState else -initialState) := rfl

private theorem boundary_carry_accepts (tokens : List CarryMacro) (trailing : Bool) :
    recognizerCarry
        ((expandMacros tokens ++ terminalToggle trailing) ++ [.toggle]) = acceptingCarry ↔
      trailing = true ∧
        ∃ bits, tokens = prefixMacros ++ returnMacros bits := by
  rw [carry_eq_accepting_iff_centred, centredCarry_boundary_expansion]
  have base_ok : AdmissibleBase (if trailing then initialState else -initialState) := by
    cases trailing <;> simp [AdmissibleBase]
  rw [classify_target tokens _ base_ok]
  constructor
  · rintro ⟨base_eq, bits, equality⟩
    have trailing_eq : trailing = true := by
      cases trailing <;> simp [initialState] at base_eq ⊢
    exact ⟨trailing_eq, bits, equality⟩
  · rintro ⟨rfl, bits, equality⟩
    exact ⟨rfl, bits, equality⟩

private theorem guard_terminalControl_zero (bits : List Bool) :
    recognizerGuard (terminalControl bits ++ [.toggle]) = 0 := by
  rw [terminalControl_eq_macro_expansion]
  have carry := (boundary_carry_accepts
    (prefixMacros ++ returnMacros bits) true).mpr ⟨rfl, bits, rfl⟩
  have carry' : recognizerCarry
      ((expandMacros (prefixMacros ++ returnMacros bits) ++ [.toggle]) ++ [.toggle]) =
      acceptingCarry := by
    simpa [terminalToggle] using carry
  change 2 * (recognizerCarry
    ((expandMacros (prefixMacros ++ returnMacros bits) ++ [.toggle]) ++ [.toggle]) -
      acceptingCarry) = 0
  rw [carry']
  ring

private theorem guard_toggle_terminalControl_zero (bits : List Bool) :
    recognizerGuard ((.toggle :: terminalControl bits) ++ [.toggle]) = 0 := by
  simpa [recognizerGuard] using guard_terminalControl_zero bits

/-- On a toggle-normal word, the boundary guard vanishes exactly on the two raw spellings of
one mixed terminal history. -/
private theorem guard_boundary_zero_of_normal {word : List PairedControl}
    (normal : ToggleNormal word) :
    recognizerGuard (word ++ [.toggle]) = 0 ↔
      ∃ bits, word = terminalControl bits ∨
        word = .toggle :: terminalControl bits := by
  obtain ⟨tokens, trailing, rfl⟩ := normal.exists_macro_expansion
  cases tokens with
  | nil =>
      cases trailing <;>
        simp [expandMacros, terminalToggle, recognizerGuard,
          terminalControl_eq_macro_expansion, toggle_terminalControl_eq_macro_expansion,
          CarryMacro.controls]
  | cons token tokens =>
      cases token with
      | b =>
          constructor
          · intro zero
            simp [expandMacros, CarryMacro.controls, recognizerGuard, List.append_assoc] at zero
            omega
          · rintro ⟨bits, equality | equality⟩
            · rw [terminalControl_eq_macro_expansion] at equality
              simp [expandMacros, CarryMacro.controls] at equality
            · rw [toggle_terminalControl_eq_macro_expansion] at equality
              simp [expandMacros, CarryMacro.controls] at equality
      | tb =>
          constructor
          · intro zero
            simp [expandMacros, CarryMacro.controls, recognizerGuard, List.append_assoc] at zero
            omega
          · rintro ⟨bits, equality | equality⟩
            · rw [terminalControl_eq_macro_expansion] at equality
              simp [expandMacros, CarryMacro.controls] at equality
            · rw [toggle_terminalControl_eq_macro_expansion] at equality
              simp [expandMacros, CarryMacro.controls] at equality
      | c =>
          have carry_iff := boundary_carry_accepts tokens trailing
          constructor
          · intro zero
            have carry : recognizerCarry
                ((expandMacros tokens ++ terminalToggle trailing) ++ [.toggle]) =
                acceptingCarry := by
              have guardEquality :
                  2 * (recognizerCarry
                    ((expandMacros tokens ++ terminalToggle trailing) ++ [.toggle]) -
                      acceptingCarry) = 0 := by
                simpa [expandMacros, CarryMacro.controls, recognizerGuard,
                  List.append_assoc] using zero
              omega
            obtain ⟨rfl, bits, rfl⟩ := carry_iff.mp carry
            exact ⟨bits, Or.inl (terminalControl_eq_macro_expansion bits).symm⟩
          · rintro ⟨bits, equality | equality⟩
            · rw [equality]
              exact guard_terminalControl_zero bits
            · rw [toggle_terminalControl_eq_macro_expansion] at equality
              simp [expandMacros, CarryMacro.controls] at equality
      | tc =>
          have carry_iff := boundary_carry_accepts tokens trailing
          constructor
          · intro zero
            have carry : recognizerCarry
                ((expandMacros tokens ++ terminalToggle trailing) ++ [.toggle]) =
                acceptingCarry := by
              have guardEquality :
                  2 * (recognizerCarry
                    ((expandMacros tokens ++ terminalToggle trailing) ++ [.toggle]) -
                      acceptingCarry) = 0 := by
                simpa [expandMacros, CarryMacro.controls, recognizerGuard,
                  List.append_assoc] using zero
              omega
            obtain ⟨rfl, bits, rfl⟩ := carry_iff.mp carry
            exact ⟨bits, Or.inr (toggle_terminalControl_eq_macro_expansion bits).symm⟩
          · rintro ⟨bits, equality | equality⟩
            · rw [terminalControl_eq_macro_expansion] at equality
              simp [expandMacros, CarryMacro.controls] at equality
            · rw [equality]
              exact guard_toggle_terminalControl_zero bits

/-! ## Exact zero-language equivalence -/

private theorem recognizerProduct_scourToggles (word : List PairedControl) :
    wordProduct recognizerGenerator (scourToggles word) =
      wordProduct recognizerGenerator word := by
  induction word with
  | nil => rfl
  | cons control word induction =>
      cases control with
      | data letter =>
          simp only [scourToggles, wordProduct_cons]
          rw [induction]
      | toggle =>
          cases equality : scourToggles word with
          | nil =>
              have reduced := induction
              rw [equality] at reduced
              calc
                wordProduct recognizerGenerator (scourToggles (.toggle :: word)) =
                    recognizerGenerator .toggle := by
                      simp [scourToggles, equality, wordProduct]
                _ = recognizerGenerator .toggle *
                    wordProduct recognizerGenerator [] := by simp [wordProduct]
                _ = recognizerGenerator .toggle *
                    wordProduct recognizerGenerator word := by rw [reduced]
                _ = wordProduct recognizerGenerator (.toggle :: word) := by
                  rw [wordProduct_cons]
          | cons head tail =>
              cases head with
              | data letter =>
                  have reduced := induction
                  rw [equality] at reduced
                  calc
                    wordProduct recognizerGenerator (scourToggles (.toggle :: word)) =
                        recognizerGenerator .toggle *
                          wordProduct recognizerGenerator (.data letter :: tail) := by
                            simp [scourToggles, equality, wordProduct_cons]
                    _ = recognizerGenerator .toggle *
                          wordProduct recognizerGenerator word := by rw [reduced]
                    _ = wordProduct recognizerGenerator (.toggle :: word) := by
                      rw [wordProduct_cons]
              | toggle =>
                  have reduced := induction
                  rw [equality] at reduced
                  calc
                    wordProduct recognizerGenerator
                        (scourToggles (.toggle :: word)) =
                        wordProduct recognizerGenerator tail := by
                          simp [scourToggles, equality]
                    _ = (recognizerGenerator .toggle * recognizerGenerator .toggle) *
                          wordProduct recognizerGenerator tail := by
                            rw [recognizerToggle_involutive]
                            simp
                    _ = recognizerGenerator .toggle *
                          wordProduct recognizerGenerator (.toggle :: tail) := by
                            simp [wordProduct, Matrix.mul_assoc]
                    _ = recognizerGenerator .toggle *
                          wordProduct recognizerGenerator word := by rw [reduced]
                    _ = wordProduct recognizerGenerator (.toggle :: word) := by
                      rw [wordProduct_cons]

theorem recognizerCoefficient_scourToggles (word : List PairedControl) :
    recognizerCoefficient (scourToggles word) = recognizerCoefficient word := by
  simp [recognizerCoefficient, linearCoefficient, recognizerProduct_scourToggles]

/-- Complete zero language of the integral three-state recognizer, on every raw control word. -/
theorem recognizerCoefficient_eq_zero_iff (word : List PairedControl) :
    recognizerCoefficient word = 0 ↔
      ∃ bits, scourToggles word = terminalControl bits ∨
        scourToggles word = .toggle :: terminalControl bits := by
  rw [← recognizerCoefficient_scourToggles word,
    recognizerCoefficient_eq_guard]
  exact guard_boundary_zero_of_normal (scourToggles_normal word)

/-- The paired reduction has the same exact toggle-normal zero language. -/
theorem pairedCoefficient_eq_zero_iff (word : List PairedControl) :
    pairedCoefficient ℚ 3 mixedBody word = 0 ↔
      ∃ bits, scourToggles word = terminalControl bits ∨
        scourToggles word = .toggle :: terminalControl bits := by
  rw [pairedCoefficient_eq_sideCoefficient,
    sideCoefficient_eq_zero_iff_terminal_match_rat,
    mixed_terminal_match_iff]
  constructor
  · rintro ⟨bits, decoded⟩
    exact ⟨bits, (decode_eq_terminal_iff_scourToggles word bits).mp decoded⟩
  · rintro ⟨bits, reduced⟩
    exact ⟨bits, (decode_eq_terminal_iff_scourToggles word bits).mpr reduced⟩

/-- The explicit integral three-state representation recognizes precisely the complete paired
zero language for `β = 3` and body `bcbcbb`. -/
theorem recognizerCoefficient_eq_zero_iff_paired (word : List PairedControl) :
    recognizerCoefficient word = 0 ↔
      pairedCoefficient ℚ 3 mixedBody word = 0 := by
  rw [recognizerCoefficient_eq_zero_iff, pairedCoefficient_eq_zero_iff]

/-! ## Degeneracy audit -/

/-- Both data generators have exactly the same kernel condition: only the first homogeneous
coordinate can survive. -/
theorem recognizerData_mulVec_eq_zero_iff (letter : TagLetter) (vector : Fin 3 → ℤ) :
    recognizerData letter *ᵥ vector = 0 ↔ vector 1 = 0 ∧ vector 2 = 0 := by
  constructor
  · intro killed
    have second := congrFun killed (1 : Fin 3)
    have third := congrFun killed (2 : Fin 3)
    cases letter <;>
      simp [recognizerData, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ,
        carryB, carryC] at second third <;>
      omega
  · rintro ⟨second, third⟩
    cases letter <;> ext coordinate <;> fin_cases coordinate <;>
      simp [recognizerData, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ,
        carryB, carryC, second, third]

/-- The common data kernel is nontrivial. -/
theorem recognizerData_kills_guardAxis (letter : TagLetter) :
    recognizerData letter *ᵥ ![1, 0, 0] = 0 := by
  rw [recognizerData_mulVec_eq_zero_iff]
  simp

/-- Every suffix point lies in the affine chart with last coordinate one. -/
theorem recognizerSuffix_last (word : List PairedControl) :
    (wordProduct recognizerGenerator word *ᵥ recognizerColumn) 2 = 1 := by
  calc
    (wordProduct recognizerGenerator word *ᵥ recognizerColumn) 2 =
        (wordProduct recognizerGenerator (word ++ [.toggle]) *ᵥ recognizerDelta) 2 := by
          rw [wordProduct_append, recognizerColumn_eq_toggle_delta, Matrix.mulVec_mulVec]
          simp [wordProduct]
    _ = 1 := by rw [recognizerProduct_mulVec_delta]; rfl

/-- No generator product collapses to the zero matrix. -/
theorem recognizerProduct_ne_zero (word : List PairedControl) :
    wordProduct recognizerGenerator word ≠ 0 := by
  intro zeroProduct
  have last := recognizerSuffix_last word
  rw [zeroProduct] at last
  simp at last

/-- The two boundary vectors are genuine projective representatives. -/
theorem recognizerBoundaries_ne_zero :
    recognizerRow ≠ 0 ∧ recognizerColumn ≠ 0 := by
  constructor <;> intro zeroBoundary
  · have first := congrFun zeroBoundary (0 : Fin 3)
    simp [recognizerRow] at first
  · have last := congrFun zeroBoundary (2 : Fin 3)
    simp [recognizerColumn] at last

end MixedBranchingRecognizer
end MatrixMortality
