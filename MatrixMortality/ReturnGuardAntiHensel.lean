import MatrixMortality.ReturnGuardSensitivity

/-!
# Anti-Hensel compatibility

Guard readiness is an annular condition: a normalized leading digit must remain nonzero.
Forcing the next incidence chooses one affine parameter digit.  That digit preserves the old
annulus exactly when one `2 × 2` cross-determinant is nonzero.

This is the missing qualification in a naïve Hensel argument.  A visible next observer
guarantees a unique incidence digit, but that same digit can annihilate the normalized digit
which kept an earlier ready condition exact.  Sequential guard synthesis therefore requires
nonvanishing of one compatibility determinant at every active valuation shell.
-/

namespace MatrixMortality.ReturnGuard

noncomputable section

/-- Cross-determinant of an old annular digit and a new affine incidence equation. -/
def liftCompatibility
    {K : Type*} [CommRing K]
    (oldValue oldSlope newValue newSlope : K) : K :=
  oldValue * newSlope - oldSlope * newValue

/-- The unique digit solving a visible affine incidence equation. -/
def incidenceDigit
    {K : Type*} [Field K] (newValue newSlope : K) : K :=
  -newValue / newSlope

/-- The selected incidence digit solves its affine equation. -/
theorem incidenceDigit_hits
    {K : Type*} [Field K]
    (newValue newSlope : K) (visible : newSlope ≠ 0) :
    newValue + incidenceDigit newValue newSlope * newSlope = 0 := by
  simp [incidenceDigit, div_mul_cancel₀ _ visible]

/-- A visible affine equation has no other incidence digit. -/
theorem incidenceDigit_eq_of_hits
    {K : Type*} [Field K]
    (newValue newSlope digit : K) (visible : newSlope ≠ 0)
    (hits : newValue + digit * newSlope = 0) :
    digit = incidenceDigit newValue newSlope := by
  apply (eq_div_iff visible).2
  linear_combination hits

/-- Evaluating the old annular digit at the selected new-incidence digit exposes the
compatibility determinant. -/
theorem oldDigit_at_incidenceDigit
    {K : Type*} [Field K]
    (oldValue oldSlope newValue newSlope : K)
    (visible : newSlope ≠ 0) :
    oldValue + incidenceDigit newValue newSlope * oldSlope =
      liftCompatibility oldValue oldSlope newValue newSlope / newSlope := by
  simp [incidenceDigit, liftCompatibility]
  field_simp
  ring

/-- Exact one-digit extension criterion.

The new observer is visible, so it selects one parameter digit.  A simultaneous extension
exists precisely when that digit does not kill the old normalized annular coefficient. -/
theorem exists_incidenceDigit_and_preserves_iff
    {K : Type*} [Field K]
    (oldValue oldSlope newValue newSlope : K)
    (visible : newSlope ≠ 0) :
    (∃ digit : K,
        newValue + digit * newSlope = 0 ∧
          oldValue + digit * oldSlope ≠ 0) ↔
      liftCompatibility oldValue oldSlope newValue newSlope ≠ 0 := by
  constructor
  · rintro ⟨digit, hits, survives⟩ compatibility_zero
    have digit_eq :=
      incidenceDigit_eq_of_hits newValue newSlope digit visible hits
    subst digit
    apply survives
    rw [oldDigit_at_incidenceDigit _ _ _ _ visible,
      compatibility_zero, zero_div]
  · intro compatibility_ne
    refine
      ⟨incidenceDigit newValue newSlope,
        incidenceDigit_hits newValue newSlope visible, ?_⟩
    rw [oldDigit_at_incidenceDigit _ _ _ _ visible]
    exact div_ne_zero compatibility_ne visible

/-- Vanishing compatibility is a complete obstruction, not merely failure of one guessed
digit.  The unique digit required by the new incidence necessarily destroys the old annulus. -/
theorem no_incidenceDigit_preserves_of_liftCompatibility_eq_zero
    {K : Type*} [Field K]
    (oldValue oldSlope newValue newSlope : K)
    (visible : newSlope ≠ 0)
    (incompatible :
      liftCompatibility oldValue oldSlope newValue newSlope = 0) :
    ¬∃ digit : K,
        newValue + digit * newSlope = 0 ∧
          oldValue + digit * oldSlope ≠ 0 := by
  rw [exists_incidenceDigit_and_preserves_iff _ _ _ _ visible,
    incompatible]
  simp

end
end MatrixMortality.ReturnGuard
