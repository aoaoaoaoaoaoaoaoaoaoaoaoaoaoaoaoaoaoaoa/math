import MatrixMortality.SingularReturnFamily

/-!
# Periodic return compression

A projectively periodic transition has only finitely many return matrices up to nonzero scalar.
Interface compression therefore replaces the transition and its factored cut by the finite family
of residue returns without any splitting hypotheses on the cut.
-/

namespace MatrixMortality.PeriodicReturn

open scoped Matrix

variable {K Large Small : Type*} [Field K]
  [Fintype Large] [DecidableEq Large] [Nonempty Large]
  [Fintype Small] [DecidableEq Small]

/-- The return-time residue in a positive period. -/
def residue (period : Nat) (period_pos : 0 < period) (wait : Nat) : Fin period :=
  ⟨wait % period, Nat.mod_lt wait period_pos⟩

omit [Nonempty Large] in
/-- A projectively periodic power is its residue power times the quotient scalar. -/
theorem pow_eq_smul_residue
    (ambient : Square Large K) (period : Nat) (scalar : K)
    (periodic : ambient ^ period = scalar • 1) (wait : Nat) :
    ambient ^ wait = scalar ^ (wait / period) • ambient ^ (wait % period) := by
  conv_lhs => rw [← Nat.div_add_mod wait period]
  rw [pow_add, show ambient ^ (period * (wait / period)) =
      (ambient ^ period) ^ (wait / period) by rw [pow_mul], periodic]
  simp [smul_pow]

omit [Nonempty Large] in
/-- A nonzero projective period makes the transition invertible. -/
theorem ambient_isUnit
    (ambient : Square Large K) (period : Nat) (period_pos : 0 < period) (scalar : K)
    (scalar_ne_zero : scalar ≠ 0) (periodic : ambient ^ period = scalar • 1) :
    IsUnit ambient := by
  rw [isUnit_iff_exists_inv]
  refine ⟨scalar⁻¹ • ambient ^ (period - 1), ?_⟩
  rw [Matrix.mul_smul, ← pow_succ']
  have period_eq : period - 1 + 1 = period := Nat.succ_pred_eq_of_pos period_pos
  rw [period_eq, periodic, smul_smul, inv_mul_cancel₀ scalar_ne_zero]
  simp

/-- The residue return indexed by one time in a positive period. -/
def residueReturn
    (ambient : Square Large K) (input : Matrix Large Small K)
    (output : Matrix Small Large K) (period : Nat) (index : Fin period) : Square Small K :=
  ReturnFamily.returnMatrix ambient input output index

omit [Nonempty Large] [Fintype Small] [DecidableEq Small] in
/-- Every return is a scalar multiple of its residue return. -/
theorem returnMatrix_eq_smul_residue
    (ambient : Square Large K) (input : Matrix Large Small K)
    (output : Matrix Small Large K) (period : Nat) (period_pos : 0 < period)
    (scalar : K) (periodic : ambient ^ period = scalar • 1) (wait : Nat) :
    ReturnFamily.returnMatrix ambient input output wait =
      scalar ^ (wait / period) •
        residueReturn ambient input output period (residue period period_pos wait) := by
  rw [ReturnFamily.returnMatrix,
    pow_eq_smul_residue ambient period scalar periodic wait]
  simp [residueReturn, residue, ReturnFamily.returnMatrix,
    Matrix.mul_smul, Matrix.smul_mul]

/-- A transition with nonzero scalar period and one factored cut is mortal exactly when its
finite family of residue returns is mortal. No rank or splitting hypothesis is required. -/
theorem pairGenerator_isMortal_iff_residue
    (ambient : Square Large K) (input : Matrix Large Small K)
    (output : Matrix Small Large K) (period : Nat) (period_pos : 0 < period)
    (scalar : K) (scalar_ne_zero : scalar ≠ 0)
    (periodic : ambient ^ period = scalar • 1) :
    IsMortal (ReturnFamily.pairGenerator ambient (input * output)) ↔
      IsMortal (residueReturn ambient input output period) := by
  have ambient_unit := ambient_isUnit ambient period period_pos scalar scalar_ne_zero periodic
  rw [ReturnFamily.pairGenerator_isMortal_iff_returnFamily ambient input output
    (fun exponent => (ambient_unit.pow exponent).ne_zero)]
  let scale : Nat → K := fun wait => scalar ^ (wait / period)
  have scale_ne_zero : ∀ wait, scale wait ≠ 0 := fun wait =>
    pow_ne_zero _ scalar_ne_zero
  have returns_eq :
      ReturnFamily.returnMatrix ambient input output =
        fun wait => scale wait •
          (residueReturn ambient input output period ∘ residue period period_pos) wait := by
    funext wait
    exact returnMatrix_eq_smul_residue ambient input output period period_pos scalar periodic wait
  rw [returns_eq, isMortal_smulMatrix_iff scale scale_ne_zero]
  apply ReturnFamily.isMortal_comp_rightInverse_iff
    (residueReturn ambient input output period) (residue period period_pos) Fin.val
  intro index
  apply Fin.ext
  simp [residue, Nat.mod_eq_of_lt index.isLt]

end MatrixMortality.PeriodicReturn
