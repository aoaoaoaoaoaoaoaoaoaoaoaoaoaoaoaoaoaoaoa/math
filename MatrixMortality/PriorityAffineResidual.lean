import Mathlib.Algebra.Group.Int.Defs

/-!
# Priority-affine residual macros

A translation guarded by exact values in an initial segment of natural counters compiles into
one debit, one nested zero test, and one credit. This is the arithmetic seam behind the
priority-affine residual decision boundary; decidability of VASS with nested zero tests remains
an external theorem.
-/

namespace MatrixMortality

namespace PriorityAffineResidual

/-- Exact addition of an integer vector, with natural source and target states enforcing
nonnegativity. -/
def IntegerStep {dimension : Nat} (shift : Fin dimension → ℤ)
    (source target : Fin dimension → Nat) : Prop :=
  ∀ coordinate, (target coordinate : ℤ) = (source coordinate : ℤ) + shift coordinate

/-- A guard testing exact values on the first `cut` counters. -/
def PrefixGuard {dimension : Nat} (cut : Nat) (guard state : Fin dimension → Nat) : Prop :=
  ∀ coordinate, coordinate.val < cut → state coordinate = guard coordinate

/-- A nested zero test on the first `cut` counters. -/
def NestedZero {dimension : Nat} (cut : Nat) (state : Fin dimension → Nat) : Prop :=
  ∀ coordinate, coordinate.val < cut → state coordinate = 0

/-- Debit the guarded constants before applying the nested zero test. -/
def guardDebit {dimension : Nat} (cut : Nat) (guard : Fin dimension → Nat) :
    Fin dimension → ℤ :=
  fun coordinate => if coordinate.val < cut then -(guard coordinate : ℤ) else 0

/-- Restore the guarded constants and apply the desired affine translation. -/
def guardCredit {dimension : Nat} (cut : Nat) (guard : Fin dimension → Nat)
    (shift : Fin dimension → ℤ) : Fin dimension → ℤ :=
  fun coordinate =>
    if coordinate.val < cut then (guard coordinate : ℤ) + shift coordinate else shift coordinate

/-- Larger prefix tests imply every smaller nested zero test. -/
theorem nestedZero_mono {dimension : Nat} {smaller larger : Nat}
    {state : Fin dimension → Nat} (smaller_le : smaller ≤ larger)
    (zero : NestedZero larger state) : NestedZero smaller state := by
  intro coordinate coordinate_lt
  exact zero coordinate (Nat.lt_of_lt_of_le coordinate_lt smaller_le)

/-- Exact-value prefix guards are precisely debit, nested zero test, and credit macros. -/
theorem guardedTranslation_iff_nestedZeroMacro
    {dimension : Nat} (cut : Nat) (guard source target : Fin dimension → Nat)
    (shift : Fin dimension → ℤ) :
    PrefixGuard cut guard source ∧ IntegerStep shift source target ↔
      ∃ middle : Fin dimension → Nat,
        IntegerStep (guardDebit cut guard) source middle ∧
          NestedZero cut middle ∧
          IntegerStep (guardCredit cut guard shift) middle target := by
  constructor
  · rintro ⟨guarded, translated⟩
    let middle : Fin dimension → Nat :=
      fun coordinate => if coordinate.val < cut then 0 else source coordinate
    refine ⟨middle, ?_, ?_, ?_⟩
    · intro coordinate
      by_cases tested : coordinate.val < cut
      · simp [middle, guardDebit, tested, guarded coordinate tested]
      · simp [middle, guardDebit, tested]
    · intro coordinate tested
      simp [middle, tested]
    · intro coordinate
      by_cases tested : coordinate.val < cut
      · simp [middle, guardCredit, tested, ← guarded coordinate tested,
          translated coordinate]
      · simp [middle, guardCredit, tested, translated coordinate]
  · rintro ⟨middle, debited, zero, credited⟩
    constructor
    · intro coordinate tested
      have debit_eq := debited coordinate
      have middle_eq := zero coordinate tested
      simp [guardDebit, tested, middle_eq] at debit_eq
      omega
    · intro coordinate
      have debit_eq := debited coordinate
      have credit_eq := credited coordinate
      by_cases tested : coordinate.val < cut
      · simp [guardDebit, guardCredit, tested] at debit_eq credit_eq
        omega
      · simp [guardDebit, guardCredit, tested] at debit_eq credit_eq
        omega

end PriorityAffineResidual

end MatrixMortality
