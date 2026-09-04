import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import MatrixMortality.ReturnFamily

/-!
# The reduction half of the Skolem wall

An integer linear recurrence of positive order is put in newest-first companion form. A
nonzero coefficient on the oldest term makes the rational companion invertible. The recurrence
has a zero exactly when the companion and its rank-one initial/observation cut form a mortal
two-generator family.
-/

namespace MatrixMortality.SkolemReduction

open scoped Matrix

/-- Finite data for an integer linear recurrence of order `tail + 1`. Coordinates are ordered
newest first, so the coefficient at `Fin.last tail` multiplies the oldest term. -/
structure IntegerRecurrence (tail : Nat) where
  /-- Coefficients of the next term, in newest-first order. -/
  coefficients : Fin (tail + 1) → ℤ
  /-- Initial window, in newest-first order. -/
  initial : Fin (tail + 1) → ℤ
  /-- The coefficient of the oldest term is nonzero. -/
  lastCoefficient_ne_zero : coefficients (Fin.last tail) ≠ 0

variable {tail : Nat}

namespace IntegerRecurrence

/-- One integral companion step. -/
def nextState (recurrence : IntegerRecurrence tail)
    (state : Fin (tail + 1) → ℤ) : Fin (tail + 1) → ℤ :=
  Fin.cases (∑ index, recurrence.coefficients index * state index)
    fun index => state index.castSucc

/-- The recurrence window after `n` steps. -/
def state (recurrence : IntegerRecurrence tail) (n : Nat) : Fin (tail + 1) → ℤ :=
  (recurrence.nextState^[n]) recurrence.initial

/-- The scalar recurrence sequence, read from the oldest coordinate after each step. -/
def term (recurrence : IntegerRecurrence tail) (n : Nat) : ℤ :=
  recurrence.state n (Fin.last tail)

theorem state_zero (recurrence : IntegerRecurrence tail) :
    recurrence.state 0 = recurrence.initial := rfl

theorem state_succ (recurrence : IntegerRecurrence tail) (n : Nat) :
    recurrence.state (n + 1) = recurrence.nextState (recurrence.state n) := by
  rw [state, Function.iterate_succ_apply']
  rfl

end IntegerRecurrence

/-! ## Rational companion -/

/-- Newest-first rational companion action. -/
def advance (coefficients : Fin (tail + 1) → ℚ)
    (state : Fin (tail + 1) → ℚ) : Fin (tail + 1) → ℚ :=
  Fin.cases (∑ index, coefficients index * state index)
    fun index => state index.castSucc

/-- Explicit inverse of the companion action. -/
def retreat (coefficients : Fin (tail + 1) → ℚ)
    (state : Fin (tail + 1) → ℚ) : Fin (tail + 1) → ℚ :=
  Fin.lastCases
    ((state 0 - ∑ index : Fin tail,
        coefficients index.castSucc * state index.succ) /
      coefficients (Fin.last tail))
    fun index => state index.succ

theorem retreat_advance (coefficients : Fin (tail + 1) → ℚ)
    (last_ne_zero : coefficients (Fin.last tail) ≠ 0)
    (state : Fin (tail + 1) → ℚ) :
    retreat coefficients (advance coefficients state) = state := by
  funext index
  refine Fin.lastCases ?_ (fun preceding => ?_) index
  · simp only [retreat, Fin.lastCases_last, advance, Fin.cases_zero]
    rw [Fin.sum_univ_castSucc]
    field_simp
    simp only [Fin.cases_succ]
    ring
  · simp [retreat, advance]

theorem advance_retreat (coefficients : Fin (tail + 1) → ℚ)
    (last_ne_zero : coefficients (Fin.last tail) ≠ 0)
    (state : Fin (tail + 1) → ℚ) :
    advance coefficients (retreat coefficients state) = state := by
  funext index
  refine Fin.cases ?_ (fun preceding => ?_) index
  · simp only [advance, Fin.cases_zero, Fin.sum_univ_castSucc, retreat,
      Fin.lastCases_castSucc, Fin.lastCases_last]
    field_simp
    ring
  · simp [advance, retreat]

/-- The rational companion action as a linear map. -/
def advanceLinear (coefficients : Fin (tail + 1) → ℚ) :
    (Fin (tail + 1) → ℚ) →ₗ[ℚ] Fin (tail + 1) → ℚ where
  toFun := advance coefficients
  map_add' left right := by
    funext index
    refine Fin.cases ?_ (fun preceding => ?_) index
    · simp [advance, Finset.sum_add_distrib, mul_add]
    · simp [advance]
  map_smul' scalar state := by
    funext index
    refine Fin.cases ?_ (fun preceding => ?_) index
    · simp [advance, Finset.mul_sum, mul_left_comm]
    · simp [advance]

/-- The explicit inverse companion action as a linear map. -/
def retreatLinear (coefficients : Fin (tail + 1) → ℚ) :
    (Fin (tail + 1) → ℚ) →ₗ[ℚ] Fin (tail + 1) → ℚ where
  toFun := retreat coefficients
  map_add' left right := by
    funext index
    refine Fin.lastCases ?_ (fun preceding => ?_) index
    · simp [retreat, Finset.sum_add_distrib, mul_add]
      ring
    · simp [retreat]
  map_smul' scalar state := by
    funext index
    refine Fin.lastCases ?_ (fun preceding => ?_) index
    · simp only [retreat, Fin.lastCases_last, Pi.smul_apply, smul_eq_mul]
      have sum_eq :
          (∑ index : Fin tail,
              coefficients index.castSucc * (scalar * state index.succ)) =
            scalar * ∑ index : Fin tail,
              coefficients index.castSucc * state index.succ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro index _index_mem
        ring
      rw [sum_eq]
      simp only [RingHom.id_apply]
      ring
    · simp [retreat]

/-- The companion action as an automorphism of the rational state space. -/
def companionEquiv (coefficients : Fin (tail + 1) → ℚ)
    (last_ne_zero : coefficients (Fin.last tail) ≠ 0) :
    (Fin (tail + 1) → ℚ) ≃ₗ[ℚ] Fin (tail + 1) → ℚ :=
  LinearEquiv.ofLinearMap (advanceLinear coefficients) (retreatLinear coefficients)
    (by
      apply LinearMap.ext
      intro state
      exact advance_retreat coefficients last_ne_zero state)
    (by
      apply LinearMap.ext
      intro state
      exact retreat_advance coefficients last_ne_zero state)

namespace IntegerRecurrence

/-- Rational companion matrix of the integer recurrence. -/
def companion (recurrence : IntegerRecurrence tail) : Square (Fin (tail + 1)) ℚ :=
  LinearMap.toMatrix' (advanceLinear fun index => (recurrence.coefficients index : ℚ))

theorem companion_mulVec (recurrence : IntegerRecurrence tail)
    (state : Fin (tail + 1) → ℚ) :
    recurrence.companion *ᵥ state =
      advance (fun index => recurrence.coefficients index) state := by
  simp [companion, advanceLinear]

/-- The nonzero oldest-term coefficient makes the rational companion invertible. -/
theorem companion_isUnit (recurrence : IntegerRecurrence tail) :
    IsUnit recurrence.companion := by
  rw [companion, LinearMap.isUnit_toMatrix'_iff]
  let equivalence := companionEquiv
    (fun index => recurrence.coefficients index)
    (by exact_mod_cast recurrence.lastCoefficient_ne_zero)
  exact ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv equivalence, rfl⟩

/-- The companion as an element of `GL_(tail+1)(ℚ)`. -/
noncomputable def companionGL (recurrence : IntegerRecurrence tail) :
    Matrix.GeneralLinearGroup (Fin (tail + 1)) ℚ :=
  recurrence.companion_isUnit.unit

@[simp]
theorem companionGL_coe (recurrence : IntegerRecurrence tail) :
    (recurrence.companionGL : Square (Fin (tail + 1)) ℚ) = recurrence.companion :=
  recurrence.companion_isUnit.unit_spec

/-- Rational initial column. -/
def initialColumn (recurrence : IntegerRecurrence tail) : Fin (tail + 1) → ℚ :=
  fun index => recurrence.initial index

/-- Observation row selecting the oldest coordinate. -/
def observer (_recurrence : IntegerRecurrence tail) : Fin (tail + 1) → ℚ :=
  fun index => if index = Fin.last tail then 1 else 0

/-- Rank-one input carrying the initial recurrence window. -/
def input (recurrence : IntegerRecurrence tail) : Matrix (Fin (tail + 1)) Unit ℚ :=
  Matrix.replicateCol Unit recurrence.initialColumn

/-- Rank-one output observing the scalar recurrence term. -/
def output (recurrence : IntegerRecurrence tail) : Matrix Unit (Fin (tail + 1)) ℚ :=
  Matrix.replicateRow Unit recurrence.observer

theorem companion_mulVec_state (recurrence : IntegerRecurrence tail) (n : Nat) :
    recurrence.companion *ᵥ (fun index => (recurrence.state n index : ℚ)) =
      fun index => (recurrence.state (n + 1) index : ℚ) := by
  rw [companion_mulVec, recurrence.state_succ]
  funext index
  refine Fin.cases ?_ (fun preceding => ?_) index
  · simp only [advance, IntegerRecurrence.nextState, Fin.cases_zero]
    norm_cast
  · simp [advance, IntegerRecurrence.nextState]

/-- Every companion power reproduces the corresponding integral recurrence window. -/
theorem companion_pow_mulVec_initial (recurrence : IntegerRecurrence tail) (n : Nat) :
    recurrence.companion ^ n *ᵥ recurrence.initialColumn =
      fun index => (recurrence.state n index : ℚ) := by
  induction n with
  | zero =>
      rw [pow_zero, Matrix.one_mulVec, recurrence.state_zero]
      rfl
  | succ n induction =>
      calc
        recurrence.companion ^ (n + 1) *ᵥ recurrence.initialColumn =
            recurrence.companion *ᵥ
              (recurrence.companion ^ n *ᵥ recurrence.initialColumn) := by
                rw [pow_succ']
                exact (Matrix.mulVec_mulVec recurrence.initialColumn
                  recurrence.companion (recurrence.companion ^ n)).symm
        _ = recurrence.companion *ᵥ
              (fun index => (recurrence.state n index : ℚ)) := by rw [induction]
        _ = fun index => (recurrence.state (n + 1) index : ℚ) :=
          recurrence.companion_mulVec_state n

theorem observer_dot_state (recurrence : IntegerRecurrence tail) (n : Nat) :
    recurrence.observer ⬝ᵥ (fun index => (recurrence.state n index : ℚ)) =
      recurrence.term n := by
  simp [observer, dotProduct, IntegerRecurrence.term]

/-- The scalar matrix coefficient `o Aⁿ u` is the `n`th recurrence term. -/
theorem observer_dot_companion_pow_initial (recurrence : IntegerRecurrence tail) (n : Nat) :
    recurrence.observer ⬝ᵥ
        (recurrence.companion ^ n *ᵥ recurrence.initialColumn) =
      recurrence.term n := by
  rw [recurrence.companion_pow_mulVec_initial, recurrence.observer_dot_state]

/-- The one-dimensional return at time `n` is exactly the `n`th recurrence term. -/
theorem returnMatrix_apply (recurrence : IntegerRecurrence tail) (n : Nat) :
    ReturnFamily.returnMatrix recurrence.companion recurrence.input recurrence.output n () () =
      recurrence.term n := by
  rw [ReturnFamily.returnMatrix, Matrix.mul_assoc]
  change
    (Matrix.replicateRow Unit recurrence.observer *
      (recurrence.companion ^ n * Matrix.replicateCol Unit recurrence.initialColumn)) () () = _
  rw [← Matrix.replicateCol_mulVec, Matrix.replicateRow_mul_replicateCol_apply,
    recurrence.observer_dot_companion_pow_initial]

theorem returnMatrix_eq_zero_iff (recurrence : IntegerRecurrence tail) (n : Nat) :
    ReturnFamily.returnMatrix recurrence.companion recurrence.input recurrence.output n = 0 ↔
      recurrence.term n = 0 := by
  constructor
  · intro matrix_zero
    have entry_zero := congrFun (congrFun matrix_zero ()) ()
    rw [recurrence.returnMatrix_apply] at entry_zero
    have cast_zero : (recurrence.term n : ℚ) = 0 := by simpa using entry_zero
    exact_mod_cast cast_zero
  · intro term_zero
    ext row column
    cases row
    cases column
    rw [recurrence.returnMatrix_apply]
    have cast_zero : (recurrence.term n : ℚ) = 0 := by exact_mod_cast term_zero
    simpa using cast_zero

/-- Skolem zero existence is exactly mortality of an invertible companion beside its
rank-one initial/observation cut. -/
theorem exists_term_eq_zero_iff_isMortal (recurrence : IntegerRecurrence tail) :
    (∃ n, recurrence.term n = 0) ↔
      IsMortal (ReturnFamily.pairGenerator recurrence.companion
        (recurrence.input * recurrence.output)) := by
  rw [ReturnFamily.rankOnePair_isMortal_iff recurrence.companion recurrence.input
    recurrence.output recurrence.companion_isUnit]
  exact exists_congr fun n => recurrence.returnMatrix_eq_zero_iff n |>.symm

/-- Correctness of a Boolean mortality classifier transports to the Skolem classifier built
from the explicit companion family. This statement does not assert computability of either
classifier; the pointwise equivalence above is its mathematical content. -/
theorem skolemDecision_of_mortalityDecision
    (mortalityDecision :
      (Option Unit → Square (Fin (tail + 1)) ℚ) → Bool)
    (mortalityDecision_spec : ∀ family,
      mortalityDecision family = true ↔ IsMortal family) :
    ∃ skolemDecision : IntegerRecurrence tail → Bool,
      ∀ recurrence, skolemDecision recurrence = true ↔
        ∃ n, recurrence.term n = 0 := by
  refine ⟨fun recurrence => mortalityDecision
    (ReturnFamily.pairGenerator recurrence.companion
      (recurrence.input * recurrence.output)), ?_⟩
  intro recurrence
  rw [mortalityDecision_spec, ← recurrence.exists_term_eq_zero_iff_isMortal]

end IntegerRecurrence

end MatrixMortality.SkolemReduction
