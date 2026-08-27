import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.Coprime.Lemmas
import MatrixMortality.ReturnGuardDynamics

/-!
# Rational-rail obstruction for the amalgamated valuation guard

A rational ready-tail chart with affine wait update satisfies a functional equation.  Clearing
its denominator produces a polynomial identity.  Composition by `scale * X^degree` forces the
composed numerator to divide the original denominator; degree comparison then excludes every
nonidentity affine wait update under the guard's unit hypotheses.
-/

namespace MatrixMortality.ReturnGuard.Rail

open MatrixMortality.PadicValuation Polynomial

noncomputable section

/-- Polynomial substitution `X ↦ scale * X^degree`. -/
def scalePower (scale : ℚ) (degree : Nat) (polynomial : ℚ[X]) : ℚ[X] :=
  polynomial.comp (C scale * X ^ degree)

/-- Cleared left side of the rail functional equation. -/
def leftTerm
    (depth degree : Nat) (center offset scale : ℚ)
    (numerator denominator : ℚ[X]) : ℚ[X] :=
  ((C center + C offset * X ^ depth) * denominator +
      C offset * (X - 1) * numerator) *
    scalePower scale degree numerator

/-- Cleared affine-wait term. -/
def directTerm
    (degree : Nat) (scale : ℚ)
    (numerator denominator : ℚ[X]) : ℚ[X] :=
  C scale * X ^ degree * denominator *
    scalePower scale degree numerator

/-- Cleared reciprocal-tail term. -/
def reciprocalTerm
    (depth degree : Nat) (scale : ℚ)
    (denominator : ℚ[X]) : ℚ[X] :=
  C (scale ^ depth) * X ^ (depth * degree) * denominator *
    scalePower scale degree denominator

/-- Cross-multiplied rational-rail functional equation. -/
def Identity
    (depth degree : Nat) (center offset scale : ℚ)
    (numerator denominator : ℚ[X]) : Prop :=
  leftTerm depth degree center offset scale numerator denominator =
    directTerm degree scale numerator denominator +
      reciprocalTerm depth degree scale denominator

/-- One defined sample of the rational ready-tail rail equation. -/
def RailAt
    (depth degree : Nat) (center offset scale : ℚ)
    (numerator denominator : ℚ[X]) (point : ℚ) : Prop :=
  denominator.eval point ≠ 0 ∧
    (scalePower scale degree numerator).eval point ≠ 0 ∧
      center +
          offset *
            (point ^ depth +
              (point - 1) *
                (numerator.eval point / denominator.eval point)) =
        scale * point ^ degree +
          scale ^ depth * point ^ (depth * degree) *
            ((scalePower scale degree denominator).eval point /
              (scalePower scale degree numerator).eval point)

/-- Polynomial defect obtained by clearing the two rail denominators. -/
def defectPolynomial
    (depth degree : Nat) (center offset scale : ℚ)
    (numerator denominator : ℚ[X]) : ℚ[X] :=
  leftTerm depth degree center offset scale numerator denominator -
    directTerm degree scale numerator denominator -
      reciprocalTerm depth degree scale denominator

/-- A defined rail sample is a root of the cleared polynomial defect. -/
theorem isRoot_defectPolynomial_of_railAt
    (depth degree : Nat) (center offset scale : ℚ)
    (numerator denominator : ℚ[X]) (point : ℚ)
    (rail : RailAt depth degree center offset scale numerator denominator point) :
    IsRoot
      (defectPolynomial depth degree center offset scale numerator denominator)
      point := by
  rcases rail with ⟨denominator_ne, substituted_numerator_ne, equation⟩
  have substituted_eval_ne :
      numerator.eval (scale * point ^ degree) ≠ 0 := by
    simpa [scalePower, eval_comp] using substituted_numerator_ne
  simp only [IsRoot, defectPolynomial, leftTerm, directTerm, reciprocalTerm,
    eval_sub, eval_add, eval_mul, eval_C, eval_pow, eval_X,
    scalePower] at equation ⊢
  rw [eval_comp, eval_comp] at equation ⊢
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_one] at equation ⊢
  field_simp [denominator_ne, substituted_eval_ne] at equation ⊢
  linear_combination equation

/-- Infinitely many defined rail samples force the rational functional identity. -/
theorem identity_of_infinite_railAt
    (depth degree : Nat) (center offset scale : ℚ)
    (numerator denominator : ℚ[X])
    (infinite :
      Set.Infinite
        {point |
          RailAt depth degree center offset scale numerator denominator point}) :
    Identity depth degree center offset scale numerator denominator := by
  let defect :=
    defectPolynomial depth degree center offset scale numerator denominator
  have roots_infinite : Set.Infinite {point | IsRoot defect point} := by
    apply infinite.mono
    intro point rail
    exact
      isRoot_defectPolynomial_of_railAt depth degree center offset scale
        numerator denominator point rail
  have defect_zero : defect = 0 :=
    eq_zero_of_infinite_isRoot defect roots_infinite
  dsimp [defect, defectPolynomial] at defect_zero
  simp only [Identity]
  linear_combination defect_zero

/-- Composition preserves coprimality of a reduced numerator and denominator. -/
theorem scalePower_isCoprime
    (scale : ℚ) (degree : Nat) {numerator denominator : ℚ[X]}
    (coprime : IsCoprime numerator denominator) :
    IsCoprime
      (scalePower scale degree numerator)
      (scalePower scale degree denominator) := by
  simpa [scalePower] using
    coprime.map (Polynomial.compRingHom (C scale * X ^ degree))

/-- Constant coefficient is unchanged by every positive-degree scale-power substitution. -/
theorem scalePower_coeff_zero
    (scale : ℚ) (degree : Nat) (degree_positive : 0 < degree)
    (polynomial : ℚ[X]) :
    (scalePower scale degree polynomial).coeff 0 = polynomial.coeff 0 := by
  rw [coeff_zero_eq_eval_zero, scalePower, eval_comp]
  simp [zero_pow degree_positive.ne', ← coeff_zero_eq_eval_zero]

/-- A polynomial with nonzero constant coefficient remains coprime to `X` after substitution. -/
theorem scalePower_isCoprime_X
    (scale : ℚ) (degree : Nat) (degree_positive : 0 < degree)
    {polynomial : ℚ[X]} (constant_ne_zero : polynomial.coeff 0 ≠ 0) :
    IsCoprime (scalePower scale degree polynomial) X := by
  rcases EuclideanDomain.dvd_or_coprime
      (X : ℚ[X]) (scalePower scale degree polynomial) irreducible_X with
    divides | coprime
  · have coefficient_zero :=
      Polynomial.X_dvd_iff.mp divides
    rw [scalePower_coeff_zero scale degree degree_positive] at coefficient_zero
    exact (constant_ne_zero coefficient_zero).elim
  · exact coprime.symm

/-- Scale-power substitution preserves nonzero polynomials at positive degree and nonzero scale. -/
theorem scalePower_ne_zero
    (scale : ℚ) (degree : Nat) (scale_ne_zero : scale ≠ 0)
    (degree_positive : 0 < degree) {polynomial : ℚ[X]}
    (polynomial_ne_zero : polynomial ≠ 0) :
    scalePower scale degree polynomial ≠ 0 := by
  intro composition_zero
  rcases Polynomial.comp_eq_zero_iff.mp composition_zero with
    polynomial_zero | ⟨_, substituted_constant⟩
  · exact polynomial_ne_zero polynomial_zero
  · have substituted_degree :
        (C scale * X ^ degree : ℚ[X]).natDegree = degree :=
      natDegree_C_mul_X_pow degree scale scale_ne_zero
    have constant_degree :
        (C scale * X ^ degree : ℚ[X]).natDegree = 0 := by
      rw [substituted_constant, natDegree_C]
    omega

/-- Exact degree multiplication under scale-power substitution. -/
theorem natDegree_scalePower
    (scale : ℚ) (degree : Nat) (scale_ne_zero : scale ≠ 0)
    {polynomial : ℚ[X]} (polynomial_ne_zero : polynomial ≠ 0) :
    (scalePower scale degree polynomial).natDegree =
      polynomial.natDegree * degree := by
  rw [scalePower]
  have leading_ne :
      polynomial.leadingCoeff *
          (C scale * X ^ degree : ℚ[X]).leadingCoeff ^
            polynomial.natDegree ≠ 0 := by
    rw [leadingCoeff_C_mul_X_pow]
    exact mul_ne_zero
      (leadingCoeff_ne_zero.mpr polynomial_ne_zero)
      (pow_ne_zero _ scale_ne_zero)
  rw [Polynomial.natDegree_comp_eq_of_mul_ne_zero leading_ne,
    natDegree_C_mul_X_pow degree scale scale_ne_zero]

/-- A rail identity forces the substituted numerator to divide the original denominator. -/
theorem scalePower_numerator_dvd_denominator
    (depth degree : Nat) (degree_positive : 0 < degree)
    (center offset scale : ℚ) (scale_ne_zero : scale ≠ 0)
    (numerator denominator : ℚ[X])
    (numerator_constant_ne_zero : numerator.coeff 0 ≠ 0)
    (coprime : IsCoprime numerator denominator)
    (identity :
      Identity depth degree center offset scale numerator denominator) :
    scalePower scale degree numerator ∣ denominator := by
  let substitutedNumerator := scalePower scale degree numerator
  let substitutedDenominator := scalePower scale degree denominator
  have divides_terminal :
      substitutedNumerator ∣
        reciprocalTerm depth degree scale denominator := by
    refine ⟨
      (C center + C offset * X ^ depth) * denominator +
          C offset * (X - 1) * numerator -
        C scale * X ^ degree * denominator, ?_⟩
    dsimp [substitutedNumerator, substitutedDenominator]
    simp only [Identity, leftTerm, directTerm, reciprocalTerm] at identity
    calc
      C (scale ^ depth) * X ^ (depth * degree) * denominator *
          scalePower scale degree denominator =
        (((C center + C offset * X ^ depth) * denominator +
            C offset * (X - 1) * numerator) *
            scalePower scale degree numerator) -
          C scale * X ^ degree * denominator *
            scalePower scale degree numerator := by
              rw [identity]
              ring
      _ = scalePower scale degree numerator *
          ((C center + C offset * X ^ depth) * denominator +
            C offset * (X - 1) * numerator -
            C scale * X ^ degree * denominator) := by
              ring
  have substituted_coprime :
      IsCoprime substitutedNumerator substitutedDenominator := by
    exact scalePower_isCoprime scale degree coprime
  have divides_prefix :
      substitutedNumerator ∣
        C (scale ^ depth) * X ^ (depth * degree) * denominator := by
    apply substituted_coprime.dvd_of_dvd_mul_right
    simpa [reciprocalTerm, mul_assoc] using divides_terminal
  have constant_unit : IsUnit (C (scale ^ depth) : ℚ[X]) := by
    rw [Polynomial.isUnit_C]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero depth scale_ne_zero)
  have coprime_constant :
      IsCoprime substitutedNumerator (C (scale ^ depth) : ℚ[X]) := by
    simpa using
      (isCoprime_mul_unit_left_right constant_unit substitutedNumerator 1).mpr
        isCoprime_one_right
  have coprime_power :
      IsCoprime substitutedNumerator (X ^ (depth * degree) : ℚ[X]) :=
    (scalePower_isCoprime_X scale degree degree_positive
      numerator_constant_ne_zero).pow_right
  have coprime_prefix :
      IsCoprime substitutedNumerator
        (C (scale ^ depth) * X ^ (depth * degree) : ℚ[X]) :=
    coprime_constant.mul_right coprime_power
  apply coprime_prefix.dvd_of_dvd_mul_left
  simpa [mul_assoc] using divides_prefix

/-- The denominator degree must dominate `degree` copies of the numerator degree. -/
theorem degree_mul_numerator_le_denominator
    (depth degree : Nat) (degree_positive : 0 < degree)
    (center offset scale : ℚ) (scale_ne_zero : scale ≠ 0)
    (numerator denominator : ℚ[X])
    (numerator_ne_zero : numerator ≠ 0)
    (denominator_ne_zero : denominator ≠ 0)
    (numerator_constant_ne_zero : numerator.coeff 0 ≠ 0)
    (coprime : IsCoprime numerator denominator)
    (identity :
      Identity depth degree center offset scale numerator denominator) :
    numerator.natDegree * degree ≤ denominator.natDegree := by
  rw [← natDegree_scalePower scale degree scale_ne_zero numerator_ne_zero]
  exact natDegree_le_of_dvd
    (scalePower_numerator_dvd_denominator depth degree degree_positive
      center offset scale scale_ne_zero numerator denominator
      numerator_constant_ne_zero coprime identity)
    denominator_ne_zero

/-- Exact degree of the cleared reciprocal term. -/
theorem natDegree_reciprocalTerm
    (depth degree : Nat) (degree_positive : 0 < degree)
    (scale : ℚ) (scale_ne_zero : scale ≠ 0)
    (denominator : ℚ[X]) (denominator_ne_zero : denominator ≠ 0) :
    (reciprocalTerm depth degree scale denominator).natDegree =
      depth * degree + denominator.natDegree +
        denominator.natDegree * degree := by
  have scale_power_ne :
      scalePower scale degree denominator ≠ 0 :=
    scalePower_ne_zero scale degree scale_ne_zero degree_positive denominator_ne_zero
  have leading_ne :
      (C (scale ^ depth) * X ^ (depth * degree) : ℚ[X]) ≠ 0 := by
    exact mul_ne_zero
      (C_ne_zero.mpr (pow_ne_zero depth scale_ne_zero))
      (pow_ne_zero _ X_ne_zero)
  rw [reciprocalTerm,
    natDegree_mul (mul_ne_zero leading_ne denominator_ne_zero) scale_power_ne,
    natDegree_mul leading_ne denominator_ne_zero,
    natDegree_C_mul_X_pow (depth * degree) (scale ^ depth)
      (pow_ne_zero depth scale_ne_zero),
    natDegree_scalePower scale degree scale_ne_zero denominator_ne_zero]

/-- Exact degree of the cleared direct term. -/
theorem natDegree_directTerm
    (degree : Nat) (degree_positive : 0 < degree)
    (scale : ℚ) (scale_ne_zero : scale ≠ 0)
    (numerator denominator : ℚ[X])
    (numerator_ne_zero : numerator ≠ 0)
    (denominator_ne_zero : denominator ≠ 0) :
    (directTerm degree scale numerator denominator).natDegree =
      degree + denominator.natDegree + numerator.natDegree * degree := by
  have scale_power_ne :
      scalePower scale degree numerator ≠ 0 :=
    scalePower_ne_zero scale degree scale_ne_zero degree_positive numerator_ne_zero
  have leading_ne : (C scale * X ^ degree : ℚ[X]) ≠ 0 := by
    exact mul_ne_zero (C_ne_zero.mpr scale_ne_zero) (pow_ne_zero _ X_ne_zero)
  rw [directTerm,
    natDegree_mul (mul_ne_zero leading_ne denominator_ne_zero) scale_power_ne,
    natDegree_mul leading_ne denominator_ne_zero,
    natDegree_C_mul_X_pow degree scale scale_ne_zero,
    natDegree_scalePower scale degree scale_ne_zero numerator_ne_zero]

/-- Uniform degree bound for the cleared left side. -/
theorem natDegree_leftTerm_le
    (depth degree : Nat) (center offset scale : ℚ)
    (scale_ne_zero : scale ≠ 0)
    (numerator denominator : ℚ[X]) (numerator_ne_zero : numerator ≠ 0) :
    (leftTerm depth degree center offset scale numerator denominator).natDegree ≤
      max (depth + denominator.natDegree) (1 + numerator.natDegree) +
        numerator.natDegree * degree := by
  have coefficient_le :
      (C center + C offset * X ^ depth : ℚ[X]).natDegree ≤ depth := by
    apply le_trans (natDegree_add_le _ _)
    apply max_le
    · simp
    · exact natDegree_C_mul_X_pow_le offset depth
  have first_le :
      ((C center + C offset * X ^ depth) * denominator :
          ℚ[X]).natDegree ≤
        depth + denominator.natDegree :=
    natDegree_mul_le.trans (add_le_add_left coefficient_le _)
  have x_sub_one_le : (X - 1 : ℚ[X]).natDegree ≤ 1 := by
    apply le_trans (natDegree_sub_le _ _)
    simp
  have second_le :
      (C offset * (X - 1) * numerator : ℚ[X]).natDegree ≤
        1 + numerator.natDegree := by
    apply le_trans natDegree_mul_le
    have coefficient_product_le :
        (C offset * (X - 1) : ℚ[X]).natDegree ≤ 1 := by
      apply le_trans natDegree_mul_le
      simpa using x_sub_one_le
    exact add_le_add_left coefficient_product_le _
  have bracket_le :
      ((C center + C offset * X ^ depth) * denominator +
          C offset * (X - 1) * numerator : ℚ[X]).natDegree ≤
        max (depth + denominator.natDegree)
          (1 + numerator.natDegree) :=
    (natDegree_add_le _ _).trans (max_le_max first_le second_le)
  apply le_trans natDegree_mul_le
  rw [natDegree_scalePower scale degree scale_ne_zero numerator_ne_zero]
  exact add_le_add_left bracket_le _

/-- Arithmetic degree gap behind the rational-rail obstruction. -/
theorem degreeGap
    {depth degree numeratorDegree denominatorDegree : Nat}
    (depth_two : 2 ≤ depth) (degree_positive : 0 < degree)
    (denominator_large : numeratorDegree * degree ≤ denominatorDegree)
    (growth : 1 < degree ∨ numeratorDegree < denominatorDegree) :
    max
        (max (depth + denominatorDegree) (1 + numeratorDegree) +
          numeratorDegree * degree)
        (degree + denominatorDegree + numeratorDegree * degree) <
      depth * degree + denominatorDegree +
        denominatorDegree * degree := by
  rcases growth with degree_growth | denominator_growth
  · simp only [max_lt_iff]
    constructor
    · rcases max_choice (depth + denominatorDegree)
          (1 + numeratorDegree) with maximum | maximum
      · rw [maximum]
        nlinarith
      · rw [maximum]
        nlinarith
    · nlinarith
  · simp only [max_lt_iff]
    constructor
    · rcases max_choice (depth + denominatorDegree)
          (1 + numeratorDegree) with maximum | maximum
      · rw [maximum]
        nlinarith
      · rw [maximum]
        nlinarith
    · nlinarith

/-- No rail identity can have genuine scale-power growth or excess denominator degree. -/
theorem not_identity_of_degreeGrowth
    (depth degree : Nat) (depth_two : 2 ≤ depth)
    (degree_positive : 0 < degree)
    (center offset scale : ℚ) (scale_ne_zero : scale ≠ 0)
    (numerator denominator : ℚ[X])
    (numerator_ne_zero : numerator ≠ 0)
    (denominator_ne_zero : denominator ≠ 0)
    (numerator_constant_ne_zero : numerator.coeff 0 ≠ 0)
    (coprime : IsCoprime numerator denominator)
    (growth :
      1 < degree ∨ numerator.natDegree < denominator.natDegree) :
    ¬Identity depth degree center offset scale numerator denominator := by
  intro identity
  have denominator_large :=
    degree_mul_numerator_le_denominator depth degree degree_positive
      center offset scale scale_ne_zero numerator denominator
      numerator_ne_zero denominator_ne_zero numerator_constant_ne_zero
      coprime identity
  have gap :=
    degreeGap depth_two degree_positive denominator_large growth
  have reciprocal_degree :=
    natDegree_reciprocalTerm depth degree degree_positive scale scale_ne_zero
      denominator denominator_ne_zero
  have direct_degree :=
    natDegree_directTerm degree degree_positive scale scale_ne_zero numerator denominator
      numerator_ne_zero denominator_ne_zero
  have left_degree :=
    natDegree_leftTerm_le depth degree center offset scale scale_ne_zero
      numerator denominator numerator_ne_zero
  have difference_degree :
      (leftTerm depth degree center offset scale numerator denominator -
          directTerm degree scale numerator denominator).natDegree <
        (reciprocalTerm depth degree scale denominator).natDegree := by
    apply lt_of_le_of_lt (natDegree_sub_le _ _)
    rw [reciprocal_degree, direct_degree]
    exact lt_of_le_of_lt (max_le_max left_degree le_rfl) gap
  have reciprocal_eq :
      reciprocalTerm depth degree scale denominator =
        leftTerm depth degree center offset scale numerator denominator -
          directTerm degree scale numerator denominator := by
    simp only [Identity] at identity
    rw [identity]
    ring
  rw [reciprocal_eq] at difference_degree
  exact (lt_irrefl _ difference_degree).elim

/-- Every surviving rational rail has degree one and equal numerator/denominator degrees. -/
theorem identity_forces_linear_equalDegree
    (depth degree : Nat) (depth_two : 2 ≤ depth)
    (degree_positive : 0 < degree)
    (center offset scale : ℚ) (scale_ne_zero : scale ≠ 0)
    (numerator denominator : ℚ[X])
    (numerator_ne_zero : numerator ≠ 0)
    (denominator_ne_zero : denominator ≠ 0)
    (numerator_constant_ne_zero : numerator.coeff 0 ≠ 0)
    (coprime : IsCoprime numerator denominator)
    (identity :
      Identity depth degree center offset scale numerator denominator) :
    degree = 1 ∧ numerator.natDegree = denominator.natDegree := by
  have denominator_large :=
    degree_mul_numerator_le_denominator depth degree degree_positive
      center offset scale scale_ne_zero numerator denominator
      numerator_ne_zero denominator_ne_zero numerator_constant_ne_zero
      coprime identity
  have degree_one : degree = 1 := by
    by_contra degree_ne
    have degree_growth : 1 < degree := by omega
    exact
      not_identity_of_degreeGrowth depth degree depth_two degree_positive
        center offset scale scale_ne_zero numerator denominator
        numerator_ne_zero denominator_ne_zero numerator_constant_ne_zero
        coprime (Or.inl degree_growth) identity
  refine ⟨degree_one, ?_⟩
  subst degree
  have numerator_le : numerator.natDegree ≤ denominator.natDegree := by
    simpa using denominator_large
  apply le_antisymm numerator_le
  by_contra denominator_not_le
  have denominator_growth :
      numerator.natDegree < denominator.natDegree :=
    lt_of_not_ge denominator_not_le
  exact
    not_identity_of_degreeGrowth depth 1 depth_two (by omega)
      center offset scale scale_ne_zero numerator denominator
      numerator_ne_zero denominator_ne_zero numerator_constant_ne_zero
      coprime (Or.inr denominator_growth) identity

/-- In the surviving linear case, the denominator is a scalar multiple of the
substituted numerator. -/
theorem denominator_eq_constant_mul_scalePower
    (depth : Nat) (center offset scale : ℚ) (scale_ne_zero : scale ≠ 0)
    (numerator denominator : ℚ[X])
    (numerator_ne_zero : numerator ≠ 0)
    (denominator_ne_zero : denominator ≠ 0)
    (numerator_constant_ne_zero : numerator.coeff 0 ≠ 0)
    (coprime : IsCoprime numerator denominator)
    (equal_degree : numerator.natDegree = denominator.natDegree)
    (identity :
      Identity depth 1 center offset scale numerator denominator) :
    ∃ ratio : ℚ, ratio ≠ 0 ∧
      denominator = C ratio * scalePower scale 1 numerator := by
  have divides :=
    scalePower_numerator_dvd_denominator depth 1 (by omega)
      center offset scale scale_ne_zero numerator denominator
      numerator_constant_ne_zero coprime identity
  obtain ⟨factor, factor_eq⟩ := divides
  have composition_ne :
      scalePower scale 1 numerator ≠ 0 :=
    scalePower_ne_zero scale 1 scale_ne_zero (by omega) numerator_ne_zero
  have factor_ne : factor ≠ 0 := by
    intro factor_zero
    apply denominator_ne_zero
    rw [factor_eq, factor_zero, mul_zero]
  have factor_degree_zero : factor.natDegree = 0 := by
    have product_degree := natDegree_mul composition_ne factor_ne
    rw [← factor_eq,
      natDegree_scalePower scale 1 scale_ne_zero numerator_ne_zero,
      equal_degree] at product_degree
    omega
  have factor_eq_constant := eq_C_of_natDegree_eq_zero factor_degree_zero
  refine ⟨factor.coeff 0, ?_, ?_⟩
  · intro coefficient_zero
    apply factor_ne
    rw [factor_eq_constant, coefficient_zero, C_0]
  · rw [factor_eq, factor_eq_constant, mul_comm]
    simp

/-- The constant coefficient of a rail identity fixes the boundary ratio. -/
theorem identity_constant_balance
    (depth degree : Nat) (depth_positive : 0 < depth)
    (degree_positive : 0 < degree)
    (center offset scale : ℚ)
    (numerator denominator : ℚ[X])
    (numerator_constant_ne_zero : numerator.coeff 0 ≠ 0)
    (identity :
      Identity depth degree center offset scale numerator denominator) :
    center * denominator.coeff 0 =
      offset * numerator.coeff 0 := by
  have evaluated :=
    congrArg (Polynomial.eval 0) identity
  simp only [leftTerm, directTerm, reciprocalTerm] at evaluated
  simp [eval_mul, scalePower, eval_comp, depth_positive.ne',
    degree_positive.ne'] at evaluated
  rcases evaluated with balance | numerator_zero
  · rw [← coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero] at balance
    linarith
  · exact (numerator_constant_ne_zero (by
      simpa [coeff_zero_eq_eval_zero] using numerator_zero)).elim

/-- Leading coefficient under the surviving linear scale substitution. -/
theorem leadingCoeff_scalePower_one
    (scale : ℚ) (scale_ne_zero : scale ≠ 0)
    (polynomial : ℚ[X]) :
    (scalePower scale 1 polynomial).leadingCoeff =
      polynomial.leadingCoeff * scale ^ polynomial.natDegree := by
  have substituted_degree :
      (C scale * X ^ (1 : Nat) : ℚ[X]).natDegree = 1 :=
    natDegree_C_mul_X_pow 1 scale scale_ne_zero
  rw [scalePower, leadingCoeff_comp (by omega),
    leadingCoeff_C_mul_X_pow]

/-- The high-degree part of the left bracket comes solely from the depth term. -/
theorem leftBracket_degree_leading
    (depth : Nat) (depth_two : 2 ≤ depth)
    (center offset : ℚ) (offset_ne_zero : offset ≠ 0)
    (numerator denominator : ℚ[X])
    (denominator_ne_zero : denominator ≠ 0)
    (equal_degree : numerator.natDegree = denominator.natDegree) :
    let bracket :=
      (C center + C offset * X ^ depth) * denominator +
        C offset * (X - 1) * numerator
    bracket.natDegree = depth + denominator.natDegree ∧
      bracket.leadingCoeff = offset * denominator.leadingCoeff := by
  let major := C offset * X ^ depth * denominator
  let remainder :=
    C center * denominator + C offset * (X - 1) * numerator
  have major_degree :
      major.natDegree = depth + denominator.natDegree := by
    dsimp [major]
    rw [natDegree_mul
        (mul_ne_zero (C_ne_zero.mpr offset_ne_zero)
          (pow_ne_zero _ X_ne_zero))
        denominator_ne_zero,
      natDegree_C_mul_X_pow depth offset offset_ne_zero]
  have first_le :
      (C center * denominator : ℚ[X]).natDegree ≤
        denominator.natDegree := by
    apply le_trans natDegree_mul_le
    simp
  have x_sub_one_le : (X - 1 : ℚ[X]).natDegree ≤ 1 := by
    apply le_trans (natDegree_sub_le _ _)
    simp
  have second_le :
      (C offset * (X - 1) * numerator : ℚ[X]).natDegree ≤
        1 + denominator.natDegree := by
    apply le_trans natDegree_mul_le
    have coefficient_product_le :
        (C offset * (X - 1) : ℚ[X]).natDegree ≤ 1 := by
      apply le_trans natDegree_mul_le
      simpa using x_sub_one_le
    rw [← equal_degree]
    exact add_le_add_left coefficient_product_le _
  have remainder_le :
      remainder.natDegree ≤ 1 + denominator.natDegree := by
    dsimp [remainder]
    apply le_trans (natDegree_add_le _ _)
    apply max_le
    · exact first_le.trans (Nat.le_add_left _ _)
    · exact second_le
  have remainder_lt_major : remainder.natDegree < major.natDegree := by
    rw [major_degree]
    omega
  have bracket_eq :
      (C center + C offset * X ^ depth) * denominator +
          C offset * (X - 1) * numerator =
        major + remainder := by
    dsimp [major, remainder]
    ring
  dsimp only
  constructor
  · rw [bracket_eq,
      natDegree_add_eq_left_of_natDegree_lt remainder_lt_major,
      major_degree]
  · rw [bracket_eq,
      leadingCoeff_add_of_degree_lt' (degree_lt_degree remainder_lt_major)]
    dsimp [major]
    simp [leadingCoeff_mul]

/-- The top coefficient of a rail identity balances the chart and substituted-tail scales. -/
theorem identity_leading_balance
    (depth : Nat) (depth_two : 2 ≤ depth)
    (center offset scale : ℚ)
    (offset_ne_zero : offset ≠ 0) (scale_ne_zero : scale ≠ 0)
    (numerator denominator : ℚ[X])
    (numerator_ne_zero : numerator ≠ 0)
    (denominator_ne_zero : denominator ≠ 0)
    (equal_degree : numerator.natDegree = denominator.natDegree)
    (identity :
      Identity depth 1 center offset scale numerator denominator) :
    offset * numerator.leadingCoeff =
      scale ^ depth * denominator.leadingCoeff := by
  let bracket :=
    (C center + C offset * X ^ depth) * denominator +
      C offset * (X - 1) * numerator
  have bracket_data :=
    leftBracket_degree_leading depth depth_two center offset offset_ne_zero
      numerator denominator denominator_ne_zero equal_degree
  have bracket_leading :
      bracket.leadingCoeff = offset * denominator.leadingCoeff :=
    bracket_data.2
  have reciprocal_degree :=
    natDegree_reciprocalTerm depth 1 (by omega) scale scale_ne_zero
      denominator denominator_ne_zero
  have direct_degree :=
    natDegree_directTerm 1 (by omega) scale scale_ne_zero
      numerator denominator numerator_ne_zero denominator_ne_zero
  have direct_lt_reciprocal :
      (directTerm 1 scale numerator denominator).natDegree <
        (reciprocalTerm depth 1 scale denominator).natDegree := by
    rw [direct_degree, reciprocal_degree, equal_degree]
    omega
  have leading_equality := congrArg Polynomial.leadingCoeff identity
  rw [leadingCoeff_add_of_degree_lt
      (degree_lt_degree direct_lt_reciprocal)] at leading_equality
  have left_leading :
      (leftTerm depth 1 center offset scale numerator denominator).leadingCoeff =
        offset * denominator.leadingCoeff *
          (numerator.leadingCoeff * scale ^ numerator.natDegree) := by
    change (bracket * scalePower scale 1 numerator).leadingCoeff = _
    rw [leadingCoeff_mul, bracket_leading,
      leadingCoeff_scalePower_one scale scale_ne_zero numerator]
  have reciprocal_leading :
      (reciprocalTerm depth 1 scale denominator).leadingCoeff =
        scale ^ depth * denominator.leadingCoeff *
          (denominator.leadingCoeff * scale ^ denominator.natDegree) := by
    rw [reciprocalTerm, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_C_mul_X_pow, leadingCoeff_scalePower_one
        scale scale_ne_zero denominator]
  rw [left_leading, reciprocal_leading, ← equal_degree] at leading_equality
  have denominator_leading_ne :
      denominator.leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr denominator_ne_zero
  have scale_power_ne :
      scale ^ numerator.natDegree ≠ 0 :=
    pow_ne_zero _ scale_ne_zero
  apply mul_right_cancel₀ denominator_leading_ne
  apply mul_right_cancel₀ scale_power_ne
  simpa [mul_assoc, mul_left_comm, mul_comm] using leading_equality

/-- Every rational rail identity has a linear wait update and forces the center to be a
specific power of the update scale. -/
theorem identity_forces_linear_center
    (depth degree : Nat) (depth_two : 2 ≤ depth)
    (degree_positive : 0 < degree)
    (center offset scale : ℚ)
    (offset_ne_zero : offset ≠ 0) (scale_ne_zero : scale ≠ 0)
    (numerator denominator : ℚ[X])
    (numerator_ne_zero : numerator ≠ 0)
    (denominator_ne_zero : denominator ≠ 0)
    (numerator_constant_ne_zero : numerator.coeff 0 ≠ 0)
    (coprime : IsCoprime numerator denominator)
    (identity :
      Identity depth degree center offset scale numerator denominator) :
    degree = 1 ∧
      center = scale ^ (depth + numerator.natDegree) := by
  obtain ⟨degree_one, equal_degree⟩ :=
    identity_forces_linear_equalDegree depth degree depth_two degree_positive
      center offset scale scale_ne_zero numerator denominator
      numerator_ne_zero denominator_ne_zero numerator_constant_ne_zero
      coprime identity
  subst degree
  obtain ⟨ratio, ratio_ne_zero, denominator_eq⟩ :=
    denominator_eq_constant_mul_scalePower depth center offset scale scale_ne_zero
      numerator denominator numerator_ne_zero denominator_ne_zero
      numerator_constant_ne_zero coprime equal_degree identity
  have constant_balance :=
    identity_constant_balance depth 1 (by omega) (by omega)
      center offset scale numerator denominator numerator_constant_ne_zero identity
  rw [denominator_eq, coeff_C_mul,
    scalePower_coeff_zero scale 1 (by omega) numerator] at constant_balance
  have constant_reduced : center * ratio = offset := by
    apply mul_right_cancel₀ numerator_constant_ne_zero
    simpa [mul_assoc] using constant_balance
  have leading_balance :=
    identity_leading_balance depth depth_two center offset scale
      offset_ne_zero scale_ne_zero numerator denominator numerator_ne_zero
      denominator_ne_zero equal_degree identity
  rw [denominator_eq, leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_scalePower_one scale scale_ne_zero numerator] at leading_balance
  have numerator_leading_ne :
      numerator.leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr numerator_ne_zero
  have leading_reduced :
      offset = ratio * scale ^ (depth + numerator.natDegree) := by
    apply mul_right_cancel₀ numerator_leading_ne
    simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using leading_balance
  refine ⟨rfl, ?_⟩
  apply mul_right_cancel₀ ratio_ne_zero
  calc
    center * ratio = offset := constant_reduced
    _ = ratio * scale ^ (depth + numerator.natDegree) := leading_reduced
    _ = scale ^ (depth + numerator.natDegree) * ratio := mul_comm _ _

/-- A nonunit update scale excludes every rational affine-wait rail. -/
theorem no_rational_affineWait_rail
    (prime : Nat) [Fact prime.Prime]
    (depth degree : Nat) (depth_two : 2 ≤ depth)
    (degree_positive : 0 < degree)
    (center offset scale : ℚ)
    (center_unit : PadicValuation.IsUnit prime center)
    (offset_ne_zero : offset ≠ 0)
    {scale_value : ℤ}
    (scale_has_value : HasValue prime scale scale_value)
    (scale_value_ne_zero : scale_value ≠ 0)
    (numerator denominator : ℚ[X])
    (numerator_ne_zero : numerator ≠ 0)
    (denominator_ne_zero : denominator ≠ 0)
    (numerator_constant_ne_zero : numerator.coeff 0 ≠ 0)
    (coprime : IsCoprime numerator denominator) :
    ¬Identity depth degree center offset scale numerator denominator := by
  intro identity
  have center_eq :=
    (identity_forces_linear_center depth degree depth_two degree_positive
      center offset scale offset_ne_zero scale_has_value.1
      numerator denominator numerator_ne_zero denominator_ne_zero
      numerator_constant_ne_zero coprime identity).2
  have valuation_eq := congrArg (padicValRat prime) center_eq
  rw [center_unit.2,
    padicValRat.pow scale, scale_has_value.2] at valuation_eq
  have exponent_ne :
      ((depth + numerator.natDegree : Nat) : ℤ) ≠ 0 := by
    exact_mod_cast (show depth + numerator.natDegree ≠ 0 by omega)
  exact
    (mul_ne_zero exponent_ne scale_value_ne_zero) valuation_eq.symm

/-- A reduced rational chart with nonunit affine-wait scale cannot realize the guarded rail at
infinitely many defined points. -/
theorem no_infinite_rational_affineWait_rail
    (prime : Nat) [Fact prime.Prime]
    (depth degree : Nat) (depth_two : 2 ≤ depth)
    (degree_positive : 0 < degree)
    (center offset scale : ℚ)
    (center_unit : PadicValuation.IsUnit prime center)
    (offset_ne_zero : offset ≠ 0)
    {scale_value : ℤ}
    (scale_has_value : HasValue prime scale scale_value)
    (scale_value_ne_zero : scale_value ≠ 0)
    (numerator denominator : ℚ[X])
    (numerator_ne_zero : numerator ≠ 0)
    (denominator_ne_zero : denominator ≠ 0)
    (numerator_constant_ne_zero : numerator.coeff 0 ≠ 0)
    (coprime : IsCoprime numerator denominator) :
    ¬Set.Infinite
      {point |
        RailAt depth degree center offset scale numerator denominator point} := by
  intro infinite
  exact
    no_rational_affineWait_rail prime depth degree depth_two degree_positive
      center offset scale center_unit offset_ne_zero scale_has_value
      scale_value_ne_zero numerator denominator numerator_ne_zero
      denominator_ne_zero numerator_constant_ne_zero coprime
      (identity_of_infinite_railAt depth degree center offset scale
        numerator denominator infinite)

/-- The same obstruction applies when the infinitely many rail samples are prime powers. -/
theorem no_infinite_primePower_affineWait_rail
    (prime : Nat) [Fact prime.Prime]
    (depth degree : Nat) (depth_two : 2 ≤ depth)
    (degree_positive : 0 < degree)
    (center offset scale : ℚ)
    (center_unit : PadicValuation.IsUnit prime center)
    (offset_ne_zero : offset ≠ 0)
    {scale_value : ℤ}
    (scale_has_value : HasValue prime scale scale_value)
    (scale_value_ne_zero : scale_value ≠ 0)
    (numerator denominator : ℚ[X])
    (numerator_ne_zero : numerator ≠ 0)
    (denominator_ne_zero : denominator ≠ 0)
    (numerator_constant_ne_zero : numerator.coeff 0 ≠ 0)
    (coprime : IsCoprime numerator denominator) :
    ¬Set.Infinite
      {exponent : Nat |
        RailAt depth degree center offset scale numerator denominator
          ((prime : ℚ) ^ exponent)} := by
  intro infinite
  let samples : Set Nat :=
    {exponent |
      RailAt depth degree center offset scale numerator denominator
        ((prime : ℚ) ^ exponent)}
  let powers : Nat → ℚ := fun exponent => (prime : ℚ) ^ exponent
  have powers_injective : Function.Injective powers := by
    exact
      (pow_right_strictMono₀ (by
        exact_mod_cast (Fact.out : prime.Prime).one_lt)).injective
  have image_infinite : (powers '' samples).Infinite :=
    infinite.image powers_injective.injOn
  have image_subset :
      powers '' samples ⊆
        {point |
          RailAt depth degree center offset scale numerator denominator point} := by
    rintro point ⟨exponent, exponent_mem, rfl⟩
    exact exponent_mem
  exact
    no_infinite_rational_affineWait_rail prime depth degree depth_two
      degree_positive center offset scale center_unit offset_ne_zero
      scale_has_value scale_value_ne_zero numerator denominator
      numerator_ne_zero denominator_ne_zero numerator_constant_ne_zero
      coprime (image_infinite.mono image_subset)

end
end MatrixMortality.ReturnGuard.Rail
