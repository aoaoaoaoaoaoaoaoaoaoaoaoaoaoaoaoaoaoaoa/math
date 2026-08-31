import MatrixMortality.LinearRepresentation
import MatrixMortality.PairedCompression
import MatrixMortality.PhaseFracture

/-!
# A guarded lift of a two-state terminal core

A single singular data control can expose a scalar incidence in an arbitrary integral two-state
orbit while the other data control remains nonsingular.  An odd homogeneous core coordinate
makes every word headed by the persistent control nonzero.  The resulting three-state zero
language is characterized exactly on the free raw-control monoid.

The final theorem is parametric in the Neary source: a source-indexed family of two-state cores
gives an exact three-state same-zero representation precisely when its scalar gate realizes the
paired zero language.  Thus the remaining construction problem is a two-state orbit-incidence
equation, not another choice of a one-dimensional affine target.
-/

namespace MatrixMortality
namespace GuardedTwoStateLift

open scoped Matrix

/-- Integral matrices acting on the terminal core. -/
abbrev CoreMatrix := Matrix (Fin 2) (Fin 2) ℤ

/-- Integral states of the terminal core. -/
abbrev CoreState := Fin 2 → ℤ

/-- The complete two-state data needed by the guarded lift. -/
structure TerminalCore where
  /-- Core action of each raw control. -/
  generator : PairedControl → CoreMatrix
  /-- Initial core state. -/
  column : CoreState
  /-- Functional exposed by the singular data control. -/
  gate : CoreState

/-- State reached in the two-dimensional core by a raw control word. -/
def coreState (core : TerminalCore) (word : List PairedControl) : CoreState :=
  wordProduct core.generator word *ᵥ core.column

@[simp] theorem coreState_nil (core : TerminalCore) : coreState core [] = core.column := by
  simp [coreState]

@[simp] theorem coreState_cons
    (core : TerminalCore) (control : PairedControl) (word : List PairedControl) :
    coreState core (control :: word) = core.generator control *ᵥ coreState core word := by
  rw [coreState, wordProduct_cons, ← Matrix.mulVec_mulVec]
  rfl

/-- A finite row-congruence check propagates the odd-coordinate invariant through the complete
raw core orbit. -/
theorem coreState_second_odd_of_rows
    (core : TerminalCore) (column_odd : Odd (core.column 1))
    (lower_left_even : ∀ control, Even (core.generator control 1 0))
    (lower_right_odd : ∀ control, Odd (core.generator control 1 1)) :
    ∀ word, Odd (coreState core word 1) := by
  intro word
  induction word with
  | nil => simpa using column_odd
  | cons control word induction =>
      rw [coreState_cons]
      have left_even :
          Even (core.generator control 1 0 * coreState core word 0) :=
        (lower_left_even control).mul_right _
      have right_odd :
          Odd (core.generator control 1 1 * coreState core word 1) :=
        (lower_right_odd control).mul induction
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using
        left_even.add_odd right_odd

/-- Three-state lift.  Data `b` preserves the guard and forces it odd, data `c` refreshes the
guard from the two-state incidence, and the toggle preserves the guard. -/
def generator (core : TerminalCore) : PairedControl → Matrix (Fin 3) (Fin 3) ℤ
  | .data .b =>
      !![2, 2, 1;
         0, core.generator (.data .b) 0 0, core.generator (.data .b) 0 1;
         0, core.generator (.data .b) 1 0, core.generator (.data .b) 1 1]
  | .data .c =>
      !![0, core.gate 0, core.gate 1;
         0, core.generator (.data .c) 0 0, core.generator (.data .c) 0 1;
         0, core.generator (.data .c) 1 0, core.generator (.data .c) 1 1]
  | .toggle =>
      !![1, 0, 0;
         0, core.generator .toggle 0 0, core.generator .toggle 0 1;
         0, core.generator .toggle 1 0, core.generator .toggle 1 1]

/-- Boundary row selecting the guard. -/
def row : Fin 3 → ℤ := ![1, 0, 0]

/-- Boundary column adjoining the initial guard to the two-state core column. -/
def column (core : TerminalCore) : Fin 3 → ℤ :=
  ![1, core.column 0, core.column 1]

/-- Guard computed from the right end of a raw control word. -/
def guard (core : TerminalCore) : List PairedControl → ℤ
  | [] => 1
  | .data .b :: word =>
      2 * guard core word + 2 * coreState core word 0 + coreState core word 1
  | .data .c :: word => core.gate ⬝ᵥ coreState core word
  | .toggle :: word => guard core word

/-- The exact language shape selected by the singular gate.  Leading toggles are invisible,
leading data `b` is rejected, and leading data `c` tests one scalar core incidence. -/
def gateLanguage (core : TerminalCore) : List PairedControl → Prop
  | [] => False
  | .data .b :: _ => False
  | .data .c :: word => core.gate ⬝ᵥ coreState core word = 0
  | .toggle :: word => gateLanguage core word

/-- A paired zero can never be headed by data `b`: every terminal-match tile word starts with the
distinguished `c` rule. -/
theorem pairedCoefficient_data_b_cons_ne_zero
    (beta : Nat) (body : List TagLetter) (beta_pos : 0 < beta)
    (word : List PairedControl) :
    pairedCoefficient ℚ beta body (.data .b :: word) ≠ 0 := by
  rw [pairedCoefficient_eq_sideCoefficient]
  intro coefficient_zero
  have terminal_match :=
    (sideCoefficient_eq_zero_iff_terminal_match_rat beta body
      (decodePairedWord (.data .b :: word))).mp coefficient_zero
  obtain ⟨tail, starts⟩ :=
    terminalMatch_starts_rule_c beta body beta_pos
      (decodePairedWord (.data .b :: word)) terminal_match
  cases suffix_eq : suffixDecode word with
  | mk phase decoded =>
      have decoded_shape :
          decodePairedWord (.data .b :: word) = phase.tile .b :: decoded := by
        simp [decodePairedWord, suffixDecode, suffix_eq]
      rw [decoded_shape] at starts
      have heads_equal := (List.cons.inj starts).1
      cases phase <;> cases heads_equal

/-- Once the data-`c` incidences agree, all other gate-language clauses agree with the paired
zero language automatically. -/
theorem gateLanguage_iff_paired_of_data_c_exact
    (core : TerminalCore) (beta : Nat) (body : List TagLetter) (beta_pos : 0 < beta)
    (data_c_exact : ∀ word,
      core.gate ⬝ᵥ coreState core word = 0 ↔
        pairedCoefficient ℚ beta body (.data .c :: word) = 0) :
    ∀ word, gateLanguage core word ↔ pairedCoefficient ℚ beta body word = 0 := by
  intro word
  induction word with
  | nil =>
      simp [gateLanguage, ternaryCode_nearyMarker_ne_zero]
  | cons control word induction =>
      cases control with
      | toggle =>
          rw [gateLanguage, pairedCoefficient_toggle_cons]
          exact induction
      | data letter =>
          cases letter with
          | b =>
              constructor
              · intro impossible
                exact False.elim impossible
              · exact pairedCoefficient_data_b_cons_ne_zero beta body beta_pos word
          | c => exact data_c_exact word

/-- Exact lifted state for every raw control word. -/
theorem wordProduct_mulVec_column (core : TerminalCore) (word : List PairedControl) :
    wordProduct (generator core) word *ᵥ column core =
      ![guard core word, coreState core word 0, coreState core word 1] := by
  induction word with
  | nil =>
      ext coordinate
      fin_cases coordinate <;>
        simp [wordProduct, column, guard, coreState]
  | cons control word induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec, induction]
      cases control with
      | toggle =>
          ext coordinate
          fin_cases coordinate <;>
            simp [generator, guard, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      | data letter =>
          cases letter with
          | b =>
              ext coordinate
              fin_cases coordinate
              · simp [generator, guard, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
                ring
              · simp [generator, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
              · simp [generator, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
          | c =>
              ext coordinate
              fin_cases coordinate <;>
                simp [generator, guard, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Scalar coefficient of the guarded three-state lift. -/
def coefficient (core : TerminalCore) (word : List PairedControl) : ℤ :=
  linearCoefficient (generator core) row (column core) word

/-- The lifted coefficient is exactly the guard. -/
theorem coefficient_eq_guard (core : TerminalCore) (word : List PairedControl) :
    coefficient core word = guard core word := by
  rw [coefficient, linearCoefficient, wordProduct_mulVec_column]
  simp [row, dotProduct, Fin.sum_univ_succ]

/-- An odd second core coordinate makes the guarded lift's zero set exactly its scalar gate
language. -/
theorem guard_eq_zero_iff_gateLanguage
    (core : TerminalCore) (core_odd : ∀ word, Odd (coreState core word 1))
    (word : List PairedControl) :
    guard core word = 0 ↔ gateLanguage core word := by
  induction word with
  | nil => simp [guard, gateLanguage]
  | cons control word induction =>
      cases control with
      | toggle => simpa [guard, gateLanguage] using induction
      | data letter =>
          cases letter with
          | b =>
              constructor
              · intro guard_zero
                obtain ⟨half, coordinate_eq⟩ := core_odd word
                simp only [guard] at guard_zero
                rw [coordinate_eq] at guard_zero
                omega
              · intro impossible
                exact False.elim impossible
          | c => rfl

/-- The three-state coefficient has exactly the scalar gate language on all raw words. -/
theorem coefficient_eq_zero_iff_gateLanguage
    (core : TerminalCore) (core_odd : ∀ word, Odd (coreState core word 1))
    (word : List PairedControl) :
    coefficient core word = 0 ↔ gateLanguage core word := by
  rw [coefficient_eq_guard]
  exact guard_eq_zero_iff_gateLanguage core core_odd word

/-- The persistent data control has twice the determinant of its two-state core block. -/
theorem data_b_det (core : TerminalCore) :
    (generator core (.data .b)).det = 2 * (core.generator (.data .b)).det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [generator]
  ring

/-- The gate control is necessarily singular. -/
@[simp] theorem data_c_det (core : TerminalCore) :
    (generator core (.data .c)).det = 0 := by
  rw [Matrix.det_fin_three]
  simp [generator]

/-- A nonsingular rational core block makes the persistent data control full rank after scalar
extension. -/
theorem data_b_rank_rat
    (core : TerminalCore)
    (core_det_ne : ((core.generator (.data .b)).det : ℤ) ≠ 0) :
    ((generator core (.data .b)).map (Int.castRingHom ℚ)).rank = 3 := by
  apply Matrix.rank_of_isUnit
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have determinant :
      ((generator core (.data .b)).map (Int.castRingHom ℚ)).det =
        2 * ((core.generator (.data .b)).det : ℚ) := by
    rw [Matrix.det_fin_three, Matrix.det_fin_two]
    simp [generator]
    ring
  rw [determinant]
  exact mul_ne_zero (by norm_num) (Int.cast_ne_zero.mpr core_det_ne)

/-- Conditional same-zero compiler for one Neary source.  Its only unresolved equation is the
two-state scalar gate realization stated by `gate_exact`. -/
theorem coefficient_eq_zero_iff_paired
    (core : TerminalCore) (core_odd : ∀ word, Odd (coreState core word 1))
    (beta : Nat) (body : List TagLetter)
    (gate_exact : ∀ word,
      gateLanguage core word ↔ pairedCoefficient ℚ beta body word = 0)
    (word : List PairedControl) :
    coefficient core word = 0 ↔ pairedCoefficient ℚ beta body word = 0 := by
  rw [coefficient_eq_zero_iff_gateLanguage core core_odd word]
  exact gate_exact word

/-- Under the parity invariant, the scalar gate equation is necessary and sufficient for exact
same-zero recognition.  This is the remaining terminal-geometry obligation for the lift. -/
theorem allWords_sameZero_iff_gate_exact
    (core : TerminalCore) (core_odd : ∀ word, Odd (coreState core word 1))
    (beta : Nat) (body : List TagLetter) :
    (∀ word,
      coefficient core word = 0 ↔ pairedCoefficient ℚ beta body word = 0) ↔
    (∀ word,
      gateLanguage core word ↔ pairedCoefficient ℚ beta body word = 0) := by
  constructor
  · intro same_zero word
    rw [← coefficient_eq_zero_iff_gateLanguage core core_odd word]
    exact same_zero word
  · intro gate_exact word
    exact coefficient_eq_zero_iff_paired core core_odd beta body gate_exact word

/-- For positive deletion width, exactness of the complete three-state lift is equivalent to the
single source-dependent terminal equation on data-`c` suffixes. -/
theorem allWords_sameZero_iff_data_c_gate
    (core : TerminalCore) (core_odd : ∀ word, Odd (coreState core word 1))
    (beta : Nat) (body : List TagLetter) (beta_pos : 0 < beta) :
    (∀ word,
      coefficient core word = 0 ↔ pairedCoefficient ℚ beta body word = 0) ↔
    (∀ word,
      core.gate ⬝ᵥ coreState core word = 0 ↔
        pairedCoefficient ℚ beta body (.data .c :: word) = 0) := by
  constructor
  · intro same_zero word
    calc
      core.gate ⬝ᵥ coreState core word = 0 ↔
          gateLanguage core (.data .c :: word) := Iff.rfl
      _ ↔ coefficient core (.data .c :: word) = 0 :=
        (coefficient_eq_zero_iff_gateLanguage
          core core_odd (.data .c :: word)).symm
      _ ↔ pairedCoefficient ℚ beta body (.data .c :: word) = 0 :=
        same_zero (.data .c :: word)
  · intro data_c_exact word
    apply coefficient_eq_zero_iff_paired core core_odd beta body
    exact gateLanguage_iff_paired_of_data_c_exact
      core beta body beta_pos data_c_exact

/-- Source-indexed form of the conditional compiler.  A computable concrete definition of
`family` instantiates this theorem as a uniform three-state construction. -/
theorem family_coefficient_eq_zero_iff_paired
    (family : Nat → List TagLetter → TerminalCore)
    (core_odd : ∀ beta body word, Odd (coreState (family beta body) word 1))
    (gate_exact : ∀ beta body word,
      gateLanguage (family beta body) word ↔ pairedCoefficient ℚ beta body word = 0)
    (beta : Nat) (body : List TagLetter) (word : List PairedControl) :
    coefficient (family beta body) word = 0 ↔
      pairedCoefficient ℚ beta body word = 0 :=
  coefficient_eq_zero_iff_paired
    (family beta body) (core_odd beta body) beta body (gate_exact beta body) word

/-- Uniform family form of the exact obstruction: a source-indexed guarded lift solves the paired
same-zero problem exactly when its two-state scalar gate does. -/
theorem family_sameZero_iff_gate_exact
    (family : Nat → List TagLetter → TerminalCore)
    (core_odd : ∀ beta body word, Odd (coreState (family beta body) word 1)) :
    (∀ beta body word,
      coefficient (family beta body) word = 0 ↔
        pairedCoefficient ℚ beta body word = 0) ↔
    (∀ beta body word,
      gateLanguage (family beta body) word ↔
        pairedCoefficient ℚ beta body word = 0) := by
  constructor
  · intro same_zero beta body
    exact (allWords_sameZero_iff_gate_exact
      (family beta body) (core_odd beta body) beta body).mp (same_zero beta body)
  · intro gate_exact beta body
    exact (allWords_sameZero_iff_gate_exact
      (family beta body) (core_odd beta body) beta body).mpr (gate_exact beta body)

/-- Uniform form of the sole terminal-geometry equation.  Width positivity discharges the empty,
toggle, and data-`b` cases for every source in the family. -/
theorem family_sameZero_iff_data_c_gate
    (family : Nat → List TagLetter → TerminalCore)
    (core_odd : ∀ beta body word, Odd (coreState (family beta body) word 1)) :
    (∀ beta body, 0 < beta → ∀ word,
      coefficient (family beta body) word = 0 ↔
        pairedCoefficient ℚ beta body word = 0) ↔
    (∀ beta body, 0 < beta → ∀ word,
      (family beta body).gate ⬝ᵥ coreState (family beta body) word = 0 ↔
        pairedCoefficient ℚ beta body (.data .c :: word) = 0) := by
  constructor
  · intro same_zero beta body beta_pos
    exact (allWords_sameZero_iff_data_c_gate
      (family beta body) (core_odd beta body) beta body beta_pos).mp
        (same_zero beta body beta_pos)
  · intro data_c_exact beta body beta_pos
    exact (allWords_sameZero_iff_data_c_gate
      (family beta body) (core_odd beta body) beta body beta_pos).mpr
        (data_c_exact beta body beta_pos)

end GuardedTwoStateLift
end MatrixMortality
