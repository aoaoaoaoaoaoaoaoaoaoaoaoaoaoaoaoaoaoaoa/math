import MatrixMortality.MatrixSemigroup

/-!
# Two-seed propagation for two-dimensional pumps

Cayley-Hamilton confines every power of a two-by-two matrix to the scalar span of the identity
and the matrix itself. Consequently, two contextual matrix expressions containing one repeated
pump agree at every exponent as soon as they agree at exponents zero and one.
-/

set_option autoImplicit false

namespace MatrixMortality.TwoSeedPumpPropagation

open scoped Matrix

/-- With invertible contexts, a two-sided contextual equality is exactly a centralizer test for
the connector determined at exponent zero. -/
theorem group_context_eq_iff_commute
    {G : Type*} [Group G] (leftPrefix leftSuffix rightPrefix rightSuffix middle : G)
    (at_zero : leftPrefix * leftSuffix = rightPrefix * rightSuffix) :
    leftPrefix * middle * leftSuffix = rightPrefix * middle * rightSuffix ↔
      Commute middle (leftPrefix⁻¹ * rightPrefix) := by
  let connector := leftPrefix⁻¹ * rightPrefix
  have suffix_eq : leftSuffix = connector * rightSuffix := by
    dsimp [connector]
    calc
      leftSuffix = leftPrefix⁻¹ * (leftPrefix * leftSuffix) := by group
      _ = leftPrefix⁻¹ * (rightPrefix * rightSuffix) := by rw [at_zero]
      _ = (leftPrefix⁻¹ * rightPrefix) * rightSuffix := by group
  constructor
  · intro contextual_eq
    rw [Commute]
    calc
      middle * connector =
          leftPrefix⁻¹ * (leftPrefix * middle * leftSuffix) * rightSuffix⁻¹ := by
        rw [suffix_eq]
        group
      _ = leftPrefix⁻¹ * (rightPrefix * middle * rightSuffix) * rightSuffix⁻¹ := by
        rw [contextual_eq]
      _ = connector * middle := by
        dsimp [connector]
        group
  · intro commutes
    rw [Commute] at commutes
    rw [suffix_eq]
    calc
      leftPrefix * middle * (connector * rightSuffix) =
          leftPrefix * (middle * connector) * rightSuffix := by group
      _ = leftPrefix * (connector * middle) * rightSuffix := by rw [commutes]
      _ = rightPrefix * middle * rightSuffix := by
        dsimp [connector]
        group

/-- In a group, contextual equality at exponents zero and one propagates because the connector
commutes with the pump. -/
theorem group_context_pow_eq_of_zero_one
    {G : Type*} [Group G] (leftPrefix leftSuffix rightPrefix rightSuffix pump : G)
    (at_zero : leftPrefix * leftSuffix = rightPrefix * rightSuffix)
    (at_one : leftPrefix * pump * leftSuffix = rightPrefix * pump * rightSuffix)
    (exponent : ℕ) :
    leftPrefix * pump ^ exponent * leftSuffix =
      rightPrefix * pump ^ exponent * rightSuffix := by
  rw [group_context_eq_iff_commute _ _ _ _ _ at_zero]
  have commutes :=
    (group_context_eq_iff_commute _ _ _ _ _ at_zero).mp at_one
  exact commutes.pow_left exponent

/-- The explicit two-dimensional Cayley-Hamilton identity over a commutative ring. -/
theorem finTwo_cayleyHamilton
    {R : Type*} [CommRing R] (pump : Matrix (Fin 2) (Fin 2) R) :
    pump ^ 2 =
      pump.trace • pump - pump.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.trace_fin_two, Matrix.det_fin_two] <;>
    ring

/-- Every power of a two-by-two matrix lies in the scalar span of the identity and that matrix. -/
theorem finTwo_pow_mem_span_one_self
    {R : Type*} [CommRing R] (pump : Matrix (Fin 2) (Fin 2) R) (exponent : ℕ) :
    ∃ constant linear : R,
      pump ^ exponent =
        constant • (1 : Matrix (Fin 2) (Fin 2) R) + linear • pump := by
  induction exponent with
  | zero =>
      refine ⟨1, 0, ?_⟩
      simp
  | succ exponent induction =>
      obtain ⟨constant, linear, power_eq⟩ := induction
      refine ⟨-linear * pump.det, constant + linear * pump.trace, ?_⟩
      rw [pow_succ, power_eq, add_mul, Matrix.smul_mul, Matrix.smul_mul, one_mul,
        ← pow_two pump, finTwo_cayleyHamilton]
      ext row column
      simp
      ring

/-- Two linear observations of a two-dimensional pump which agree on the identity and the pump
agree on every pump power. -/
theorem finTwo_linearContext_pow_eq_of_zero_one
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (pump : Matrix (Fin 2) (Fin 2) R)
    (left right : Matrix (Fin 2) (Fin 2) R →ₗ[R] M)
    (at_zero : left 1 = right 1) (at_one : left pump = right pump)
    (exponent : ℕ) :
    left (pump ^ exponent) = right (pump ^ exponent) := by
  obtain ⟨constant, linear, power_eq⟩ := finTwo_pow_mem_span_one_self pump exponent
  rw [power_eq, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
    at_zero, at_one]

/-- Equality of two contextual pump expressions at exponents zero and one propagates to every
natural exponent. -/
theorem finTwo_contextual_pow_eq_of_zero_one
    {R : Type*} [CommRing R]
    (leftPrefix leftSuffix rightPrefix rightSuffix pump : Matrix (Fin 2) (Fin 2) R)
    (at_zero : leftPrefix * leftSuffix = rightPrefix * rightSuffix)
    (at_one : leftPrefix * pump * leftSuffix = rightPrefix * pump * rightSuffix)
    (exponent : ℕ) :
    leftPrefix * pump ^ exponent * leftSuffix =
      rightPrefix * pump ^ exponent * rightSuffix := by
  obtain ⟨constant, linear, power_eq⟩ := finTwo_pow_mem_span_one_self pump exponent
  rw [power_eq]
  calc
    leftPrefix * (constant • 1 + linear • pump) * leftSuffix =
        constant • (leftPrefix * leftSuffix) +
          linear • (leftPrefix * pump * leftSuffix) := by
      simp [mul_add, add_mul, mul_assoc]
    _ = constant • (rightPrefix * rightSuffix) +
          linear • (rightPrefix * pump * rightSuffix) := by
      rw [at_zero, at_one]
    _ = rightPrefix * (constant • 1 + linear • pump) * rightSuffix := by
      simp [mul_add, add_mul, mul_assoc]

/-- The product of a repeated word is the corresponding power of its product. -/
theorem wordProduct_flatten_replicate
    {Alphabet M : Type*} [Monoid M] (generators : Alphabet → M)
    (word : List Alphabet) (exponent : ℕ) :
    wordProduct generators (List.replicate exponent word).flatten =
      wordProduct generators word ^ exponent := by
  induction exponent with
  | zero => simp
  | succ exponent induction =>
      rw [List.replicate_succ, List.flatten_cons, wordProduct_append, induction, pow_succ']

/-- For two-dimensional matrix interpretations, equality of side-specific word pumps at depths
zero and one propagates to every depth. -/
theorem wordProduct_pump_eq_of_zero_one
    {Alphabet R : Type*} [CommRing R]
    (generators : Alphabet → Matrix (Fin 2) (Fin 2) R)
    (leftPrefix leftSuffix rightPrefix rightSuffix pump : List Alphabet)
    (at_zero :
      wordProduct generators (leftPrefix ++ leftSuffix) =
        wordProduct generators (rightPrefix ++ rightSuffix))
    (at_one :
      wordProduct generators (leftPrefix ++ pump ++ leftSuffix) =
        wordProduct generators (rightPrefix ++ pump ++ rightSuffix))
    (exponent : ℕ) :
    wordProduct generators
        (leftPrefix ++ (List.replicate exponent pump).flatten ++ leftSuffix) =
      wordProduct generators
        (rightPrefix ++ (List.replicate exponent pump).flatten ++ rightSuffix) := by
  have zero_normalized :
      wordProduct generators leftPrefix * wordProduct generators leftSuffix =
        wordProduct generators rightPrefix * wordProduct generators rightSuffix := by
    simpa only [wordProduct_append] using at_zero
  have one_normalized :
      wordProduct generators leftPrefix * wordProduct generators pump *
          wordProduct generators leftSuffix =
        wordProduct generators rightPrefix * wordProduct generators pump *
          wordProduct generators rightSuffix := by
    simpa only [wordProduct_append, mul_assoc] using at_one
  simp only [wordProduct_append, wordProduct_flatten_replicate]
  exact finTwo_contextual_pow_eq_of_zero_one
    (wordProduct generators leftPrefix) (wordProduct generators leftSuffix)
    (wordProduct generators rightPrefix) (wordProduct generators rightSuffix)
    (wordProduct generators pump) zero_normalized one_normalized exponent

end MatrixMortality.TwoSeedPumpPropagation
