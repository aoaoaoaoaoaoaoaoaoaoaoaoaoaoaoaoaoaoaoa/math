import MatrixMortality.ReturnSquareTax

/-!
# Quadratic-pencil no-go theorems

A three-state diagonal ambient action exposes at most three simple spectral modes. Its rank-two
return pencil therefore has the form `C₀ + t C₁ + t² C₂`, with singular coefficient matrices
when each mode crosses the input and output interfaces through one state. This file proves two
exact rigidity theorems for proposed binary-stack completions:

* a quadratic pencil with three singular coefficients cannot exchange `t` and `κt²`;
* a quadratic pencil verifying squaring at both `t` and `qt` is only blind diagonal scaling.

Both results hold over every linear ordered field. They concern exact projective behavior, not
same-zero replacements.
-/

namespace MatrixMortality.ReturnSquareNoGo

open scoped Matrix

/-- Matrix pencil in the three simple modes `1,t,t²`. -/
def quadraticPencil {K : Type*} [CommRing K]
    (constant linear quadratic : Square (Fin 2) K)
    (t : K) : Square (Fin 2) K :=
  constant + t • linear + t ^ 2 • quadratic

/-- Homogeneous incidence saying that a matrix sends affine `source` to affine `target`.

The relation deliberately admits the zero output. This only strengthens the two impossibility
theorems below. -/
def mapsAffine {K : Type*} [CommRing K]
    (matrix : Square (Fin 2) K) (source target : K) : Prop :=
  Matrix.mulVec matrix ![source, 1] 0 =
    target * Matrix.mulVec matrix ![source, 1] 1

/-- Coefficient normal form of every quadratic pencil exchanging `t` and `κt²`. -/
theorem swap_coefficients
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (κ a₀ a₁ a₂ b₀ b₁ b₂ c₀ c₁ c₂ d₀ d₁ d₂ : K)
    (κ_ne_zero : κ ≠ 0)
    (push : ∀ t : K,
      (a₀ + a₁ * t + a₂ * t ^ 2) * t +
          (b₀ + b₁ * t + b₂ * t ^ 2) =
        κ * t ^ 2 *
          ((c₀ + c₁ * t + c₂ * t ^ 2) * t +
            (d₀ + d₁ * t + d₂ * t ^ 2)))
    (pop : ∀ t : K,
      (a₀ + a₁ * t + a₂ * t ^ 2) * (κ * t ^ 2) +
          (b₀ + b₁ * t + b₂ * t ^ 2) =
        t *
          ((c₀ + c₁ * t + c₂ * t ^ 2) * (κ * t ^ 2) +
            (d₀ + d₁ * t + d₂ * t ^ 2))) :
    a₀ = -d₀ ∧ a₁ = -d₁ ∧ a₂ = -d₂ ∧
      b₀ = 0 ∧ b₁ = d₀ ∧ b₂ = κ * d₀ + d₁ ∧
      c₀ = -d₁ - d₂ / κ ∧ c₁ = -d₂ ∧ c₂ = 0 := by
  have push₀ := push 0
  have push₁ := push 1
  have push₂ := push (-1)
  have push₃ := push 2
  have push₄ := push (-2)
  have push₅ := push 3
  have pop₁ := pop 1
  have pop₂ := pop (-1)
  have pop₃ := pop 2
  have pop₄ := pop (-2)
  norm_num at push₀ push₁ push₂ push₃ push₄ push₅ pop₁ pop₂ pop₃ pop₄
  ring_nf at push₀ push₁ push₂ push₃ push₄ push₅ pop₁ pop₂ pop₃ pop₄
  have pushLinear : a₀ + b₁ = 0 := by
    linarith [push₀, push₁, push₂, push₃, push₄, push₅]
  have pushQuadratic : a₁ + b₂ - κ * d₀ = 0 := by
    linarith [push₀, push₁, push₂, push₃, push₄, push₅]
  have pushCubic : a₂ - κ * c₀ - κ * d₁ = 0 := by
    linarith [push₀, push₁, push₂, push₃, push₄, push₅]
  have pushQuintic : -κ * c₂ = 0 := by
    linarith [push₀, push₁, push₂, push₃, push₄, push₅]
  have popLinear : b₁ - d₀ = 0 := by
    linarith [pop₁, pop₂, pop₃, pop₄]
  have popQuadratic : κ * a₀ + b₂ - d₁ = 0 := by
    linarith [pop₁, pop₂, pop₃, pop₄]
  have popCubic : κ * a₁ - κ * c₀ - d₂ = 0 := by
    linarith [pop₁, pop₂, pop₃, pop₄]
  have popQuartic : κ * a₂ - κ * c₁ = 0 := by
    linarith [pop₁, pop₂, pop₃, pop₄]
  have b₀_eq : b₀ = 0 := push₀
  clear push₀ push₁ push₂ push₃ push₄ push₅ pop₁ pop₂ pop₃ pop₄ push pop
  have b₁_eq : b₁ = d₀ := by linarith
  rw [b₁_eq] at pushLinear
  have a₀_eq : a₀ = -d₀ := by linarith
  rw [a₀_eq] at popQuadratic
  ring_nf at popQuadratic
  have b₂_eq : b₂ = κ * d₀ + d₁ := by linarith
  rw [b₂_eq] at pushQuadratic
  ring_nf at pushQuadratic
  have a₁_eq : a₁ = -d₁ := by linarith
  rw [a₁_eq] at popCubic
  ring_nf at popCubic
  have c₀_mul : κ * c₀ = -κ * d₁ - d₂ := by linarith
  have c₀_eq : c₀ = -d₁ - d₂ / κ := by
    field_simp
    linarith
  have a₂_eq : a₂ = -d₂ := by
    rw [c₀_mul] at pushCubic
    linarith
  have c₁_eq : c₁ = -d₂ := by
    rw [a₂_eq] at popQuartic
    ring_nf at popQuartic
    apply (mul_left_cancel₀ κ_ne_zero)
    linarith [popQuartic]
  have c₂_eq : c₂ = 0 := by
    apply (mul_left_cancel₀ κ_ne_zero)
    linarith [pushQuintic]
  exact ⟨a₀_eq, a₁_eq, a₂_eq, b₀_eq, b₁_eq, b₂_eq, c₀_eq, c₁_eq, c₂_eq⟩

/-- Three singular simple modes cannot exactly exchange `t` with `κt²`.

For `2 × 2` matrices, determinant zero is equivalent to rank at most one over a field. Thus this
excludes every diagonal three-state realization in which each spectral mode crosses the return
interface through one state. -/
theorem threeMode_swap_eq_zero
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (κ : K) (constant linear quadratic : Square (Fin 2) K)
    (κ_ne_zero : κ ≠ 0)
    (push : ∀ t, mapsAffine (quadraticPencil constant linear quadratic t) t (κ * t ^ 2))
    (pop : ∀ t, mapsAffine (quadraticPencil constant linear quadratic t) (κ * t ^ 2) t)
    (constant_singular : constant.det = 0)
    (linear_singular : linear.det = 0)
    (quadratic_singular : quadratic.det = 0) :
    constant = 0 ∧ linear = 0 ∧ quadratic = 0 := by
  have coefficients :=
    swap_coefficients κ
      (constant 0 0) (linear 0 0) (quadratic 0 0)
      (constant 0 1) (linear 0 1) (quadratic 0 1)
      (constant 1 0) (linear 1 0) (quadratic 1 0)
      (constant 1 1) (linear 1 1) (quadratic 1 1)
      κ_ne_zero
      (fun t => by
        simpa [mapsAffine, quadraticPencil, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ, mul_comm] using push t)
      (fun t => by
        simpa [mapsAffine, quadraticPencil, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ, mul_comm] using pop t)
  rcases coefficients with
    ⟨constant₀₀, linear₀₀, quadratic₀₀, constant₀₁, linear₀₁, quadratic₀₁,
      constant₁₀, linear₁₀, quadratic₁₀⟩
  rw [Matrix.det_fin_two] at constant_singular linear_singular quadratic_singular
  have constant₁₁ : constant 1 1 = 0 := by
    rw [constant₀₀, constant₀₁, constant₁₀] at constant_singular
    nlinarith [sq_nonneg (constant 1 1)]
  have quadratic₁₁ : quadratic 1 1 = 0 := by
    rw [quadratic₀₀, quadratic₀₁, quadratic₁₀] at quadratic_singular
    nlinarith [sq_nonneg (quadratic 1 1)]
  have linear₁₁ : linear 1 1 = 0 := by
    rw [linear₀₀, linear₀₁, linear₁₀, constant₁₁, quadratic₁₁] at linear_singular
    nlinarith [sq_nonneg (linear 1 1)]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [constant₀₀, constant₀₁, constant₁₀, constant₁₁, linear₁₁,
        quadratic₁₁]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [linear₀₀, linear₀₁, linear₁₀, linear₁₁, constant₁₁, quadratic₁₁]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [quadratic₀₀, quadratic₀₁, quadratic₁₀, quadratic₁₁, constant₁₁,
        linear₁₁]

/-- Coefficient normal form forced by verified squaring at both scales `t` and `qt`. -/
theorem verifiedPush_coefficients
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (q a₀ a₁ a₂ b₀ b₁ b₂ c₀ c₁ c₂ d₀ d₁ d₂ : K)
    (q_ne_zero : q ≠ 0) (q_ne_one : q ≠ 1)
    (first : ∀ t : K,
      (a₀ + a₁ * t + a₂ * t ^ 2) * t +
          (b₀ + b₁ * t + b₂ * t ^ 2) =
        t ^ 2 *
          ((c₀ + c₁ * t + c₂ * t ^ 2) * t +
            (d₀ + d₁ * t + d₂ * t ^ 2)))
    (second : ∀ t : K,
      (a₀ + a₁ * (q * t) + a₂ * (q * t) ^ 2) * t +
          (b₀ + b₁ * (q * t) + b₂ * (q * t) ^ 2) =
        q * t ^ 2 *
          ((c₀ + c₁ * (q * t) + c₂ * (q * t) ^ 2) * t +
            (d₀ + d₁ * (q * t) + d₂ * (q * t) ^ 2))) :
    a₀ = 0 ∧ a₁ = d₀ ∧ a₂ = d₁ ∧
      b₀ = 0 ∧ b₁ = 0 ∧ b₂ = 0 ∧
      c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ d₂ = 0 := by
  have first₀ := first 0
  have first₁ := first 1
  have first₂ := first (-1)
  have first₃ := first 2
  have first₄ := first (-2)
  have first₅ := first 3
  have second₁ := second 1
  have second₂ := second (-1)
  have second₃ := second 2
  have second₄ := second (-2)
  have second₅ := second 3
  norm_num at first₀ first₁ first₂ first₃ first₄ first₅
  norm_num at second₁ second₂ second₃ second₄ second₅
  ring_nf at first₀ first₁ first₂ first₃ first₄ first₅
  ring_nf at second₁ second₂ second₃ second₄ second₅
  have firstLinear : a₀ + b₁ = 0 := by
    linarith [first₀, first₁, first₂, first₃, first₄, first₅]
  have firstQuadratic : a₁ + b₂ - d₀ = 0 := by
    linarith [first₀, first₁, first₂, first₃, first₄, first₅]
  have firstCubic : a₂ - c₀ - d₁ = 0 := by
    linarith [first₀, first₁, first₂, first₃, first₄, first₅]
  have firstQuartic : -c₁ - d₂ = 0 := by
    linarith [first₀, first₁, first₂, first₃, first₄, first₅]
  have firstQuintic : -c₂ = 0 := by
    linarith [first₀, first₁, first₂, first₃, first₄, first₅]
  have secondLinear : a₀ + q * b₁ = 0 := by
    linarith [second₁, second₂, second₃, second₄, second₅]
  have secondQuadratic : q * a₁ + q ^ 2 * b₂ - q * d₀ = 0 := by
    linarith [second₁, second₂, second₃, second₄, second₅]
  have secondCubic : q ^ 2 * a₂ - q * c₀ - q ^ 2 * d₁ = 0 := by
    linarith [second₁, second₂, second₃, second₄, second₅]
  have secondQuartic : -q ^ 2 * c₁ - q ^ 3 * d₂ = 0 := by
    linarith [second₁, second₂, second₃, second₄, second₅]
  have b₀_eq : b₀ = 0 := first₀
  have b₁_factor : (q - 1) * b₁ = 0 := by
    linear_combination secondLinear - firstLinear
  have b₁_eq : b₁ = 0 :=
    (mul_eq_zero.mp b₁_factor).resolve_left (sub_ne_zero.mpr q_ne_one)
  have a₀_eq : a₀ = 0 := by linarith
  have secondQuadraticFactor : q * (a₁ + q * b₂ - d₀) = 0 := by
    linear_combination secondQuadratic
  have secondQuadraticReduced : a₁ + q * b₂ - d₀ = 0 :=
    (mul_eq_zero.mp secondQuadraticFactor).resolve_left q_ne_zero
  have b₂_factor : (q - 1) * b₂ = 0 := by
    linear_combination secondQuadraticReduced - firstQuadratic
  have b₂_eq : b₂ = 0 :=
    (mul_eq_zero.mp b₂_factor).resolve_left (sub_ne_zero.mpr q_ne_one)
  have a₁_eq : a₁ = d₀ := by linarith
  have secondQuarticFactor : q ^ 2 * (c₁ + q * d₂) = 0 := by
    linear_combination -secondQuartic
  have secondQuarticReduced : c₁ + q * d₂ = 0 :=
    (mul_eq_zero.mp secondQuarticFactor).resolve_left (pow_ne_zero 2 q_ne_zero)
  have d₂_factor : (q - 1) * d₂ = 0 := by
    linear_combination secondQuarticReduced + firstQuartic
  have d₂_eq : d₂ = 0 :=
    (mul_eq_zero.mp d₂_factor).resolve_left (sub_ne_zero.mpr q_ne_one)
  have c₁_eq : c₁ = 0 := by linarith
  have c₂_eq : c₂ = 0 := by
    simpa only [neg_eq_zero] using firstQuintic
  have secondCubicFactor : q * (q * a₂ - c₀ - q * d₁) = 0 := by
    linear_combination secondCubic
  have secondCubicReduced : q * a₂ - c₀ - q * d₁ = 0 :=
    (mul_eq_zero.mp secondCubicFactor).resolve_left q_ne_zero
  have c₀_factor : (q - 1) * c₀ = 0 := by
    linear_combination secondCubicReduced - q * firstCubic
  have c₀_eq : c₀ = 0 :=
    (mul_eq_zero.mp c₀_factor).resolve_left (sub_ne_zero.mpr q_ne_one)
  have a₂_eq : a₂ = d₁ := by linarith
  exact ⟨a₀_eq, a₁_eq, a₂_eq, b₀_eq, b₁_eq, b₂_eq, c₀_eq, c₁_eq, c₂_eq,
    d₂_eq⟩

/-- Blind diagonal scaling by the scalar linear polynomial `constant + linear*t`. -/
def blindScale {K : Type*} [CommRing K]
    (constant linear t : K) : Square (Fin 2) K :=
  !![(constant + linear * t) * t, 0;
     0, constant + linear * t]

/-- Two exact squaring checks force a quadratic pencil to be blind diagonal scaling.

The resulting projective map is `z ↦ t*z` on every input, so it verifies no equality beyond the
two prescribed identities. -/
theorem verifiedPush_eq_blindScale
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (q : K) (constant linear quadratic : Square (Fin 2) K)
    (q_ne_zero : q ≠ 0) (q_ne_one : q ≠ 1)
    (first : ∀ t,
      mapsAffine (quadraticPencil constant linear quadratic t) t (t ^ 2))
    (second : ∀ t,
      mapsAffine (quadraticPencil constant linear quadratic (q * t)) t (q * t ^ 2)) :
    ∀ t, quadraticPencil constant linear quadratic t =
      blindScale (constant 1 1) (linear 1 1) t := by
  have coefficients :=
    verifiedPush_coefficients q
      (constant 0 0) (linear 0 0) (quadratic 0 0)
      (constant 0 1) (linear 0 1) (quadratic 0 1)
      (constant 1 0) (linear 1 0) (quadratic 1 0)
      (constant 1 1) (linear 1 1) (quadratic 1 1)
      q_ne_zero q_ne_one
      (fun t => by
        simpa [mapsAffine, quadraticPencil, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ, mul_comm] using first t)
      (fun t => by
        simpa [mapsAffine, quadraticPencil, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ, mul_comm] using second t)
  rcases coefficients with
    ⟨constant₀₀, linear₀₀, quadratic₀₀, constant₀₁, linear₀₁, quadratic₀₁,
      constant₁₀, linear₁₀, quadratic₁₀, quadratic₁₁⟩
  intro t
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quadraticPencil, blindScale, constant₀₀, linear₀₀, quadratic₀₀,
      constant₀₁, linear₀₁, quadratic₀₁, constant₁₀, linear₁₀, quadratic₁₀,
      quadratic₁₁]
  all_goals ring

end MatrixMortality.ReturnSquareNoGo
