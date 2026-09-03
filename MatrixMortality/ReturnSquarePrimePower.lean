import MatrixMortality.PolynomialPencil
import MatrixMortality.PrimitiveDivisor
import MatrixMortality.ReturnSquareDynamics

/-!
# Arithmetic classification of ReturnSquare

The normalized bridge polynomial of a ReturnSquare word has constant coefficient `T` and top
coefficient `(-1)^k T²`, where `T` is the product of its return scales. The rational-root
theorem therefore confines every negative rational parameter to the prime support of the base.
-/

namespace MatrixMortality.ReturnSquare

open scoped Matrix Polynomial

noncomputable section

/-- Constant coefficient of the normalized negative-parameter return pencil. -/
def normalizedConstant {R : Type*} [CommRing R] (t : R) : Square (Fin 2) R :=
  !![t, 0;
     t ^ 2 - 1, t ^ 2 - 1]

/-- Linear coefficient of the normalized negative-parameter return pencil. -/
def normalizedSlope {R : Type*} [CommRing R] (t : R) : Square (Fin 2) R :=
  !![-t ^ 2, -(t ^ 2 - t);
     0, 0]

/-- Normalized negative-parameter return matrix. -/
def normalizedTransfer {R : Type*} [CommRing R] (d t : R) : Square (Fin 2) R :=
  normalizedConstant t + d • normalizedSlope t

/-- Change-of-basis matrix whose first column is the reset vector and whose second column is
killed by the terminal covector at parameter `c=-d`. No invertibility assumption is needed for
the intertwining identity. -/
def negativeBasis {R : Type*} [CommRing R] (d : R) : Square (Fin 2) R :=
  !![1, 1;
     1, d]

theorem normalizedTransfer_eq {R : Type*} [CommRing R] (d t : R) :
    normalizedTransfer d t =
      !![t - d * t ^ 2, -d * (t ^ 2 - t);
         t ^ 2 - 1, t ^ 2 - 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normalizedTransfer, normalizedConstant, normalizedSlope,
      Matrix.add_apply]
  all_goals ring

/-- The normalized pencil is conjugate to the original return wherever the basis is invertible;
the multiplication identity itself remains valid at `d=1`. -/
theorem transfer_neg_mul_negativeBasis {R : Type*} [CommRing R] (d t : R) :
    transfer (-d) t * negativeBasis d =
      negativeBasis d * normalizedTransfer d t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transfer, negativeBasis, normalizedTransfer_eq, Matrix.mul_apply,
      Fin.sum_univ_succ]
  all_goals ring

/-- Intertwining extends from one return to every return word. -/
theorem transferWord_mul_negativeBasis {R : Type*} [CommRing R]
    (d : R) (scales : List R) :
    wordProduct (fun t => transfer (-d) t) scales * negativeBasis d =
      negativeBasis d * wordProduct (normalizedTransfer d) scales := by
  induction scales with
  | nil => simp
  | cons t scales induction =>
      rw [wordProduct_cons, Matrix.mul_assoc, induction, ← Matrix.mul_assoc,
        transfer_neg_mul_negativeBasis, Matrix.mul_assoc, wordProduct_cons]

/-- The reset column is the first column of the normalizing basis. -/
theorem negativeBasis_mulVec_first {R : Type*} [CommRing R] (d : R) :
    negativeBasis d *ᵥ ![1, 0] = ![1, 1] := by
  ext i
  fin_cases i <;>
    simp [negativeBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The terminal covector becomes `(1-d,0)` in normalized coordinates. -/
theorem terminal_vecMul_negativeBasis {R : Type*} [CommRing R] (d : R) :
    Matrix.vecMul ![-d, 1] (negativeBasis d) = ![1 - d, 0] := by
  ext j
  fin_cases j <;>
    simp [negativeBasis, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  all_goals ring

/-- Exact bridge normalization, including the degenerate value `d=1`. -/
theorem bridgeScalar_neg_eq (d : ℚ) (scales : List ℚ) :
    bridgeScalar ![1, 1] ![-d, 1]
        (wordProduct (fun t => transfer (-d) t) scales) =
      (1 - d) * (wordProduct (normalizedTransfer d) scales) 0 0 := by
  rw [bridgeScalar, ← negativeBasis_mulVec_first d, Matrix.mulVec_mulVec,
    transferWord_mul_negativeBasis, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    terminal_vecMul_negativeBasis]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ]

/-- Integer affine-pencil whose evaluation is `normalizedTransfer`. -/
def normalizedPencil (t : ℤ) : Square (Fin 2) ℤ[X] :=
  PolynomialPencil.affine (normalizedConstant t) (normalizedSlope t)

/-- Polynomial carried by a normalized bridge word. -/
def bridgePolynomial (scales : List ℤ) : ℤ[X] :=
  PolynomialPencil.product normalizedConstant normalizedSlope scales 0 0

/-- Product of normalized constant matrices on the distinguished entry. -/
theorem normalizedConstant_word_entry (scales : List ℤ) :
    (wordProduct normalizedConstant scales) 0 0 = scales.prod := by
  induction scales with
  | nil => simp [wordProduct]
  | cons t scales induction =>
      rw [wordProduct_cons, Matrix.mul_apply]
      simp [normalizedConstant, Fin.sum_univ_succ, induction]

/-- Every normalized-slope word has zero lower-left entry. -/
theorem normalizedSlope_word_lowerLeft (scales : List ℤ) :
    (wordProduct normalizedSlope scales) 1 0 = 0 := by
  induction scales with
  | nil => simp [wordProduct]
  | cons t scales _ =>
      rw [wordProduct_cons, Matrix.mul_apply]
      simp [normalizedSlope, Fin.sum_univ_succ]

/-- Product of normalized slope matrices on the distinguished entry. -/
theorem normalizedSlope_word_entry (scales : List ℤ) :
    (wordProduct normalizedSlope scales) 0 0 =
      (-1 : ℤ) ^ scales.length * scales.prod ^ 2 := by
  induction scales with
  | nil => simp [wordProduct]
  | cons t scales induction =>
      rw [wordProduct_cons, Matrix.mul_apply]
      simp [normalizedSlope, Fin.sum_univ_succ, induction, List.prod_cons,
        normalizedSlope_word_lowerLeft, List.length_cons, pow_succ]
      ring

/-- Constant coefficient of a bridge polynomial. -/
theorem bridgePolynomial_coeff_zero (scales : List ℤ) :
    (bridgePolynomial scales).coeff 0 = scales.prod := by
  have coefficient :=
    congrFun (congrFun
      (PolynomialPencil.product_coeff_zero normalizedConstant normalizedSlope scales) 0) 0
  rw [bridgePolynomial, coefficient, normalizedConstant_word_entry]

/-- Coefficient at the largest possible degree of a bridge polynomial. -/
theorem bridgePolynomial_coeff_length (scales : List ℤ) :
    (bridgePolynomial scales).coeff scales.length =
      (-1 : ℤ) ^ scales.length * scales.prod ^ 2 := by
  have coefficient :=
    congrFun (congrFun
      (PolynomialPencil.product_coeff_length normalizedConstant normalizedSlope scales) 0) 0
  rw [bridgePolynomial, coefficient, normalizedSlope_word_entry]

/-- Degree bound inherited from the affine-pencil word. -/
theorem bridgePolynomial_natDegree_le (scales : List ℤ) :
    (bridgePolynomial scales).natDegree ≤ scales.length :=
  PolynomialPencil.product_natDegree_le_length
    normalizedConstant normalizedSlope scales 0 0

/-- A nonzero scale product makes the displayed top coefficient the actual leading
coefficient. -/
theorem bridgePolynomial_leadingCoeff (scales : List ℤ)
    (product_ne : scales.prod ≠ 0) :
    (bridgePolynomial scales).leadingCoeff =
      (-1 : ℤ) ^ scales.length * scales.prod ^ 2 := by
  have coefficient_ne :
      (bridgePolynomial scales).coeff scales.length ≠ 0 := by
    rw [bridgePolynomial_coeff_length]
    exact mul_ne_zero (by simp) (pow_ne_zero 2 product_ne)
  have degree_eq : (bridgePolynomial scales).natDegree = scales.length :=
    Polynomial.eq_natDegree_of_le_mem_support
      (bridgePolynomial_natDegree_le scales)
      (Polynomial.mem_support_iff.mpr coefficient_ne)
  rw [← Polynomial.coeff_natDegree, degree_eq, bridgePolynomial_coeff_length]

/-- Evaluation of the bridge polynomial is the distinguished normalized matrix coefficient. -/
theorem bridgePolynomial_eval₂ (scales : List ℤ) (d : ℚ) :
    Polynomial.eval₂ (Int.castRingHom ℚ) d (bridgePolynomial scales) =
      (wordProduct
        (fun t : ℤ => normalizedTransfer d (t : ℚ)) scales) 0 0 := by
  have evaluated :=
    PolynomialPencil.eval₂_product (Int.castRingHom ℚ)
      normalizedConstant normalizedSlope scales d
  have entry := congrFun (congrFun evaluated 0) 0
  rw [bridgePolynomial]
  calc
    Polynomial.eval₂ (Int.castRingHom ℚ) d
        (PolynomialPencil.product normalizedConstant normalizedSlope scales 0 0) =
        (wordProduct
          (fun t : ℤ =>
            (normalizedConstant t).map (Int.castRingHom ℚ) +
              d • (normalizedSlope t).map (Int.castRingHom ℚ)) scales) 0 0 := entry
    _ = (wordProduct
          (fun t : ℤ => normalizedTransfer d (t : ℚ)) scales) 0 0 := by
      have family :
          (fun t : ℤ =>
            (normalizedConstant t).map (Int.castRingHom ℚ) +
              d • (normalizedSlope t).map (Int.castRingHom ℚ)) =
            fun t : ℤ => normalizedTransfer d (t : ℚ) := by
        funext t
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [normalizedTransfer, normalizedConstant, normalizedSlope,
            Matrix.add_apply, Matrix.smul_apply]
      rw [family]

/-- Casting an integer scale word commutes with the transfer word product. -/
theorem transferWord_map_intCast (d : ℚ) (scales : List ℤ) :
    wordProduct (fun t : ℚ => transfer (-d) t)
        (List.map (fun t : ℤ => (t : ℚ)) scales) =
      wordProduct (fun t : ℤ => transfer (-d) (t : ℚ)) scales := by
  induction scales with
  | nil => simp
  | cons t scales induction =>
      rw [List.map_cons, wordProduct_cons, wordProduct_cons, induction]

/-- Casting an integer scale word commutes with the normalized word product. -/
theorem normalizedWord_map_intCast (d : ℚ) (scales : List ℤ) :
    wordProduct (normalizedTransfer d)
        (List.map (fun t : ℤ => (t : ℚ)) scales) =
      wordProduct (fun t : ℤ => normalizedTransfer d (t : ℚ)) scales := by
  induction scales with
  | nil => simp
  | cons t scales induction =>
      rw [List.map_cons, wordProduct_cons, wordProduct_cons, induction]

/-- Positive return scales attached to a wait word. -/
def waitScales (q : ℤ) (waits : List Nat) : List ℤ :=
  waits.map fun wait => q ^ (wait + 1)

/-- Total exponent in the product of a wait-scale word. -/
def waitExponent : List Nat → Nat
  | [] => 0
  | wait :: waits => wait + 1 + waitExponent waits

theorem waitScales_prod (q : ℤ) (waits : List Nat) :
    (waitScales q waits).prod = q ^ waitExponent waits := by
  induction waits with
  | nil => simp [waitScales, waitExponent]
  | cons wait waits induction =>
      rw [show waitScales q (wait :: waits) =
        q ^ (wait + 1) :: waitScales q waits by rfl]
      rw [List.prod_cons, induction, waitExponent, pow_add]
      ring

/-- ReturnSquare bridge coefficients are evaluations of the normalized bridge polynomial. -/
theorem positiveBridge_neg_eq_polynomial (q : ℤ) (d : ℚ) (waits : List Nat) :
    positiveBridge (q : ℚ) (-d) waits =
      (1 - d) *
        Polynomial.eval₂ (Int.castRingHom ℚ) d
          (bridgePolynomial (waitScales q waits)) := by
  have transfer_word :
      wordProduct (positiveTransfer (q : ℚ) (-d)) waits =
        wordProduct
          (fun t : ℤ => transfer (-d) (t : ℚ)) (waitScales q waits) := by
    induction waits with
    | nil => simp [waitScales]
    | cons wait waits induction =>
        rw [show waitScales q (wait :: waits) =
          q ^ (wait + 1) :: waitScales q waits by rfl]
        rw [wordProduct_cons, wordProduct_cons, induction]
        simp [positiveTransfer]
  rw [positiveBridge, transfer_word]
  have normalized :=
    bridgeScalar_neg_eq d (List.map (fun t : ℤ => (t : ℚ)) (waitScales q waits))
  rw [transferWord_map_intCast] at normalized
  rw [normalizedWord_map_intCast] at normalized
  rw [normalized, bridgePolynomial_eval₂]

/-! ## Rational-root support -/

/-- Rational roots of a bridge polynomial whose scale product is a prime power have numerator
and denominator supported on that prime. Coprimality forces one side to be `1`. -/
theorem rational_root_prime_support
    (p exponent : Nat) (prime : p.Prime) (scales : List ℤ) (d : ℚ)
    (product_eq : scales.prod = (p ^ exponent : Nat))
    (root :
      Polynomial.eval₂ (Int.castRingHom ℚ) d (bridgePolynomial scales) = 0) :
    ∃ numeratorExponent denominatorExponent : Nat,
      (IsFractionRing.num ℤ d).natAbs = p ^ numeratorExponent ∧
      ((IsFractionRing.den ℤ d : ℤ).natAbs) = p ^ denominatorExponent ∧
      (numeratorExponent = 0 ∨ denominatorExponent = 0) := by
  have product_ne : scales.prod ≠ 0 := by
    rw [product_eq]
    exact_mod_cast pow_ne_zero exponent prime.ne_zero
  have algebraic_root :
      Polynomial.aeval d (bridgePolynomial scales) = 0 := by
    simpa [Polynomial.aeval_def] using root
  have numerator_dvd_int :
      IsFractionRing.num ℤ d ∣ scales.prod := by
    simpa [bridgePolynomial_coeff_zero] using
      (num_dvd_of_is_root algebraic_root)
  have numerator_dvd :
      (IsFractionRing.num ℤ d).natAbs ∣ p ^ exponent := by
    have absolute := Int.natAbs_dvd_natAbs.mpr numerator_dvd_int
    rw [product_eq] at absolute
    simpa only [Int.natAbs_natCast] using absolute
  obtain ⟨numeratorExponent, _, numerator_eq⟩ :=
    (Nat.dvd_prime_pow prime).mp numerator_dvd
  have denominator_dvd_int :
      (IsFractionRing.den ℤ d : ℤ) ∣
        (-1 : ℤ) ^ scales.length * scales.prod ^ 2 := by
    simpa [bridgePolynomial_leadingCoeff scales product_ne] using
      (den_dvd_of_is_root algebraic_root)
  have denominator_dvd :
      (IsFractionRing.den ℤ d : ℤ).natAbs ∣ p ^ (2 * exponent) := by
    have absolute := Int.natAbs_dvd_natAbs.mpr denominator_dvd_int
    have absolute_value :
        ((-1 : ℤ) ^ scales.length * scales.prod ^ 2).natAbs =
          p ^ (2 * exponent) := by
      rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one,
        one_pow, one_mul, product_eq]
      rw [Int.natAbs_pow, Int.natAbs_natCast]
      rw [← pow_mul]
      congr 1
      omega
    rw [absolute_value] at absolute
    exact absolute
  obtain ⟨denominatorExponent, _, denominator_eq⟩ :=
    (Nat.dvd_prime_pow prime).mp denominator_dvd
  refine ⟨numeratorExponent, denominatorExponent, numerator_eq, denominator_eq, ?_⟩
  by_contra neither_zero
  push Not at neither_zero
  have prime_dvd_numerator :
      p ∣ (IsFractionRing.num ℤ d).natAbs := by
    rw [numerator_eq]
    exact dvd_pow_self p neither_zero.1
  have prime_dvd_denominator :
      p ∣ (IsFractionRing.den ℤ d : ℤ).natAbs := by
    rw [denominator_eq]
    exact dvd_pow_self p neither_zero.2
  have prime_unit : IsUnit (p : ℤ) :=
    IsFractionRing.num_den_reduced ℤ d
      (Int.natCast_dvd.mpr prime_dvd_numerator)
      (Int.natCast_dvd.mpr prime_dvd_denominator)
  rw [Int.isUnit_iff] at prime_unit
  have p_two : 2 ≤ p := prime.two_le
  rcases prime_unit with p_one | p_neg_one
  · omega
  · omega

/-- Absolute value of the canonical fraction-ring numerator/denominator representation. -/
theorem abs_eq_fractionRing_natAbs_div (d : ℚ) :
    |d| =
      ((IsFractionRing.num ℤ d).natAbs : ℚ) /
        ((IsFractionRing.den ℤ d : ℤ).natAbs : ℚ) := by
  calc
    |d| =
        |((IsFractionRing.num ℤ d : ℤ) : ℚ) /
          (((IsFractionRing.den ℤ d : ℤ) : ℚ))| := by
      simpa using congrArg abs (IsFractionRing.mk'_num_den' ℤ d).symm
    _ =
        |((IsFractionRing.num ℤ d : ℤ) : ℚ)| /
          |(((IsFractionRing.den ℤ d : ℤ) : ℚ))| := by
      rw [abs_div]
    _ =
        ((IsFractionRing.num ℤ d).natAbs : ℚ) /
          ((IsFractionRing.den ℤ d : ℤ).natAbs : ℚ) := by
      have abs_cast (value : ℤ) : |(value : ℚ)| = (value.natAbs : ℚ) := by
        rw [← Int.cast_abs, ← Nat.cast_natAbs]
      rw [abs_cast, abs_cast]

/-- Positive rational roots supported on one prime are either a nonnegative power of that prime
or the reciprocal of one. -/
theorem positive_rational_root_prime_shape
    (p exponent : Nat) (prime : p.Prime) (scales : List ℤ) (d : ℚ)
    (positive : 0 < d)
    (product_eq : scales.prod = (p ^ exponent : Nat))
    (root :
      Polynomial.eval₂ (Int.castRingHom ℚ) d (bridgePolynomial scales) = 0) :
    ∃ power : Nat, d = (p : ℚ) ^ power ∨ d = ((p : ℚ) ^ power)⁻¹ := by
  obtain ⟨numeratorExponent, denominatorExponent, numerator_eq, denominator_eq,
      numerator_zero | denominator_zero⟩ :=
    rational_root_prime_support p exponent prime scales d product_eq root
  · refine ⟨denominatorExponent, Or.inr ?_⟩
    calc
      d = |d| := (abs_of_pos positive).symm
      _ =
          ((IsFractionRing.num ℤ d).natAbs : ℚ) /
            ((IsFractionRing.den ℤ d : ℤ).natAbs : ℚ) :=
        abs_eq_fractionRing_natAbs_div d
      _ = ((p : ℚ) ^ denominatorExponent)⁻¹ := by
        rw [numerator_eq, denominator_eq, numerator_zero]
        norm_num
  · refine ⟨numeratorExponent, Or.inl ?_⟩
    calc
      d = |d| := (abs_of_pos positive).symm
      _ =
          ((IsFractionRing.num ℤ d).natAbs : ℚ) /
            ((IsFractionRing.den ℤ d : ℤ).natAbs : ℚ) :=
        abs_eq_fractionRing_natAbs_div d
      _ = (p : ℚ) ^ numeratorExponent := by
        rw [numerator_eq, denominator_eq, denominator_zero]
        norm_num

/-- Every positive power of a prime lies beyond the uniform negative-parameter wall. -/
theorem prime_power_beyond_negative_wall
    (p power : Nat) (prime : p.Prime) (power_positive : 0 < power) :
    1 + ((p : ℚ) - 1) / (p : ℚ) ^ 2 < (p : ℚ) ^ power := by
  have p_two_nat : 2 ≤ p := prime.two_le
  have p_two : (2 : ℚ) ≤ p := by exact_mod_cast p_two_nat
  have p_pos : (0 : ℚ) < p := by linarith
  have p_sq_pos : (0 : ℚ) < (p : ℚ) ^ 2 := sq_pos_of_pos p_pos
  have ratio_lt_one : ((p : ℚ) - 1) / (p : ℚ) ^ 2 < 1 := by
    rw [div_lt_one p_sq_pos]
    nlinarith [sq_nonneg ((p : ℚ) - 1)]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero power_positive.ne'
  have one_le_power : (1 : ℚ) ≤ (p : ℚ) ^ k :=
    one_le_pow₀ (by linarith)
  have power_ge_p : (p : ℚ) ≤ (p : ℚ) ^ (k + 1) := by
    rw [pow_succ]
    simpa using mul_le_mul_of_nonneg_right one_le_power p_pos.le
  calc
    1 + ((p : ℚ) - 1) / (p : ℚ) ^ 2 < 2 := by linarith
    _ ≤ (p : ℚ) := p_two
    _ ≤ (p : ℚ) ^ Nat.succ k := by
      simpa [Nat.succ_eq_add_one] using power_ge_p

/-- At a prime base, every vanishing nondegenerate negative bridge has parameter either a prime
power or the reciprocal of one. -/
theorem positiveBridge_zero_prime_shape
    (p : Nat) (prime : p.Prime) (d : ℚ) (positive : 0 < d) (d_ne_one : d ≠ 1)
    (waits : List Nat) (bridge_zero : positiveBridge (p : ℚ) (-d) waits = 0) :
    ∃ power : Nat, d = (p : ℚ) ^ power ∨ d = ((p : ℚ) ^ power)⁻¹ := by
  have polynomial_zero :
      Polynomial.eval₂ (Int.castRingHom ℚ) d
        (bridgePolynomial (waitScales (p : ℤ) waits)) = 0 := by
    have bridge_zero' :
        positiveBridge ((p : ℤ) : ℚ) (-d) waits = 0 := by
      simpa using bridge_zero
    rw [positiveBridge_neg_eq_polynomial (p : ℤ)] at bridge_zero'
    exact (mul_eq_zero.mp bridge_zero').resolve_left (sub_ne_zero.mpr d_ne_one.symm)
  have product_eq :
      (waitScales (p : ℤ) waits).prod = (p ^ waitExponent waits : Nat) := by
    rw [waitScales_prod]
    norm_cast
  exact positive_rational_root_prime_shape p (waitExponent waits) prime
    (waitScales (p : ℤ) waits) d positive product_eq polynomial_zero

/-- Complete ReturnSquare classification when the geometric base is prime. -/
theorem physical_isMortal_prime_iff (p : Nat) (prime : p.Prime) (c : ℚ) :
    IsMortal
        (ReturnFamily.pairGenerator (ambient (p : ℚ)) (cut c)) ↔
      ∃ power : Nat, c = -((p : ℚ) ^ power)⁻¹ := by
  have p_two_nat : 2 ≤ p := prime.two_le
  have p_two_int : 2 ≤ (p : ℤ) := by exact_mod_cast p_two_nat
  constructor
  · intro mortal
    by_cases c_neg_one : c = -1
    · exact ⟨0, by simp [c_neg_one]⟩
    have c_add_one_ne : c + 1 ≠ 0 := by
      intro sum_zero
      apply c_neg_one
      linarith only [sum_zero]
    have c_negative : c < 0 := by
      by_contra not_negative
      have c_nonnegative : 0 ≤ c := le_of_not_gt not_negative
      exact not_physical_isMortal_of_nonneg (p : ℤ) c p_two_int c_nonnegative mortal
    obtain ⟨waits, bridge_zero⟩ :=
      (physical_isMortal_iff_positiveBridge (p : ℤ) c (by positivity)).mp mortal
    let d := -c
    have d_positive : 0 < d := by dsimp [d]; linarith
    have d_ne_one : d ≠ 1 := by
      intro d_one
      apply c_neg_one
      dsimp [d] at d_one
      linarith only [d_one]
    have bridge_zero_neg : positiveBridge (p : ℚ) (-d) waits = 0 := by
      simpa [d] using bridge_zero
    obtain ⟨power, power_shape | reciprocal_shape⟩ :=
      positiveBridge_zero_prime_shape p prime d d_positive d_ne_one waits bridge_zero_neg
    · have power_positive : 0 < power := by
        apply Nat.pos_of_ne_zero
        intro power_zero
        rw [power_zero, pow_zero] at power_shape
        exact d_ne_one power_shape
      have beyond :=
        prime_power_beyond_negative_wall p power prime power_positive
      have immortal :=
        not_physical_isMortal_of_beyond_negative_wall
          (p : ℤ) ((p : ℚ) ^ power) p_two_int beyond
      have c_eq : c = -((p : ℚ) ^ power) := by
        dsimp [d] at power_shape
        linarith only [power_shape]
      rw [c_eq] at mortal
      exact (immortal mortal).elim
    · exact ⟨power, by dsimp [d] at reciprocal_shape; linarith⟩
  · rintro ⟨power, rfl⟩
    rcases power with _ | power
    · refine ⟨([none, none] : List (Option Unit)), by simp, ?_⟩
      simpa [wordProduct, ReturnFamily.pairGenerator, separatedGenerator,
        Matrix.mul_assoc] using (cut_neg_one_sq (R := ℚ))
    · have power_gt_one : (1 : ℚ) < (p : ℚ) ^ (power + 1) := by
        rw [pow_succ]
        have one_le : (1 : ℚ) ≤ (p : ℚ) ^ power :=
          one_le_pow₀ (by exact_mod_cast prime.one_le)
        have p_two : (2 : ℚ) ≤ p := by exact_mod_cast p_two_nat
        nlinarith
      have power_ne : (p : ℚ) ^ (power + 1) ≠ 0 := by positivity
      have c_add_one_ne : -((p : ℚ) ^ (power + 1))⁻¹ + 1 ≠ 0 := by
        have inverse_ne_one :
            ((p : ℚ) ^ (power + 1))⁻¹ ≠ 1 :=
          inv_ne_one.mpr power_gt_one.ne'
        intro sum_zero
        apply inverse_ne_one
        linarith only [sum_zero]
      apply (physical_isMortal_iff_positiveBridge
        (p : ℤ) (-((p : ℚ) ^ (power + 1))⁻¹)
        (by positivity)).mpr
      refine ⟨[power], ?_⟩
      rw [positiveBridge_singleton]
      field_simp
      norm_num [Int.cast_natCast]

/-! ## Integral finite-quotient walls -/

/-- Denominator-cleared physical cut at parameter `c=-D⁻¹`. -/
def integralScaledCut (D : ℤ) : Square (Fin 3) ℤ :=
  !![-D, D, D - 1;
     -1, D, 0;
     -D, D, D - 1]

/-- Integer pair obtained after clearing the cut denominator. -/
def integralGenerator (q D : ℤ) : Option Unit → Square (Fin 3) ℤ :=
  ReturnFamily.pairGenerator (ambient q) (integralScaledCut D)

theorem cast_integralScaledCut (D : ℤ) (D_ne : D ≠ 0) :
    castMatrix (integralScaledCut D) =
      (D : ℚ) • cut (-((D : ℚ)⁻¹)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [integralScaledCut, cut_eq, castMatrix, Matrix.smul_apply]
  all_goals field_simp
  all_goals ring

theorem cast_ambient (q : ℤ) :
    castMatrix (ambient q) = ambient (q : ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ambient, castMatrix, Matrix.diagonal_apply]

/-- Clearing the single rational cut denominator preserves mortality exactly. -/
theorem integralGenerator_isMortal_iff (q D : ℤ) (D_ne : D ≠ 0) :
    IsMortal (integralGenerator q D) ↔
      IsMortal
        (ReturnFamily.pairGenerator (ambient (q : ℚ)) (cut (-((D : ℚ)⁻¹)))) := by
  let scale : Option Unit → ℚ
    | none => D
    | some _ => 1
  let rational :=
    ReturnFamily.pairGenerator (ambient (q : ℚ)) (cut (-((D : ℚ)⁻¹)))
  have scale_ne : ∀ label, scale label ≠ 0 := by
    intro label
    cases label with
    | none =>
        have cast_ne : (D : ℚ) ≠ 0 := by exact_mod_cast D_ne
        simpa [scale] using cast_ne
    | some _ => simp [scale]
  have cast_family :
      castMatrix ∘ integralGenerator q D =
        fun label => scale label • rational label := by
    funext label
    cases label with
    | none =>
        simpa [integralGenerator, rational, scale] using cast_integralScaledCut D D_ne
    | some point =>
        simp [integralGenerator, rational, scale, cast_ambient]
  rw [← isMortal_cast_iff (integralGenerator q D), cast_family,
    isMortal_smulMatrix_iff scale scale_ne rational]

/-- Common projective ray when the ambient geometric scale becomes `1`. -/
def positiveRay {R : Type*} [One R] : Fin 3 → R :=
  ![1, 1, 1]

/-- Alternating projective ray when the ambient geometric scale becomes `-1`. -/
def alternatingRay {R : Type*} [One R] [Neg R] : Fin 3 → R :=
  ![1, -1, 1]

theorem mapped_integralGenerator_positiveRay
    (q D : ℤ) (ell : Nat)
    (q_one : (q : ZMod ell) = 1) (label : Option Unit) :
    Matrix.mulVec
        ((integralGenerator q D label).map (Int.castRingHom (ZMod ell)))
        positiveRay =
      (match label with
        | none => (D : ZMod ell) - 1
        | some _ => 1) • positiveRay := by
  cases label with
  | none =>
      ext i
      fin_cases i <;>
        simp [integralGenerator, integralScaledCut, positiveRay, Matrix.mulVec,
          dotProduct, Fin.sum_univ_succ]
      all_goals ring
  | some point =>
      ext i
      fin_cases i <;>
        simp [integralGenerator, ambient, positiveRay, Matrix.mulVec,
          dotProduct, Matrix.diagonal_apply, q_one]

/-- A prime quotient in which `q=1` but `D≠1` certifies immortality of the cleared pair. -/
theorem not_integralGenerator_isMortal_of_mod_one
    (q D : ℤ) (ell : Nat) (ell_prime : ell.Prime)
    (q_one : (q : ZMod ell) = 1) (D_ne_one : (D : ZMod ell) ≠ 1) :
    ¬IsMortal (integralGenerator q D) := by
  let _ : Fact ell.Prime := ⟨ell_prime⟩
  let quotient :=
    ((Int.castRingHom (ZMod ell)).mapMatrix (m := Fin 3)).toMonoidWithZeroHom
  apply not_isMortal_of_map_not_isMortal quotient (integralGenerator q D)
  apply not_isMortal_of_common_eigenvector
    (quotient ∘ integralGenerator q D) positiveRay
    (fun label => match label with
      | none => (D : ZMod ell) - 1
      | some _ => 1)
  · intro ray_zero
    have entry := congrFun ray_zero 0
    norm_num [positiveRay] at entry
  · intro label
    cases label with
    | none => exact sub_ne_zero.mpr D_ne_one
    | some _ => simp
  · intro label
    simpa [quotient, Function.comp_def] using
      mapped_integralGenerator_positiveRay q D ell q_one label

/-- Two-ray state transition for the `q=-1` quotient. `false` is the positive ray. -/
def signedRayTransition : Option Unit → Bool → Bool
  | none, _ => false
  | some _, state => !state

/-- Nonzero transition scale for the `q=-1` quotient. -/
def signedRayWeight {R : Type*} [Ring R] (D : R) : Option Unit → Bool → R
  | none, false => D - 1
  | none, true => -(D + 1)
  | some _, _ => 1

/-- The two rays form a closed automaton when the ambient scale is `-1`. -/
theorem mapped_integralGenerator_signedRay
    (q D : ℤ) (ell : Nat)
    (q_neg_one : (q : ZMod ell) = -1) (label : Option Unit) (state : Bool) :
    Matrix.mulVec
        ((integralGenerator q D label).map (Int.castRingHom (ZMod ell)))
        (if state then alternatingRay else positiveRay) =
      signedRayWeight (D : ZMod ell) label state •
        (if signedRayTransition label state then alternatingRay else positiveRay) := by
  cases label with
  | none =>
      cases state <;>
        ext i <;>
        fin_cases i <;>
        simp [integralGenerator, integralScaledCut, positiveRay, alternatingRay,
          signedRayWeight, signedRayTransition, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ]
      all_goals ring
  | some point =>
      cases state <;>
        ext i <;>
        fin_cases i <;>
        simp [integralGenerator, ambient, positiveRay, alternatingRay,
          signedRayWeight, signedRayTransition, Matrix.mulVec, dotProduct,
          Matrix.diagonal_apply, q_neg_one]

/-- A prime quotient with `q=-1` and `D≠±1` certifies immortality through a two-ray
automaton. -/
theorem not_integralGenerator_isMortal_of_mod_neg_one
    (q D : ℤ) (ell : Nat) (ell_prime : ell.Prime)
    (q_neg_one : (q : ZMod ell) = -1)
    (D_ne_one : (D : ZMod ell) ≠ 1) (D_ne_neg_one : (D : ZMod ell) ≠ -1) :
    ¬IsMortal (integralGenerator q D) := by
  let _ : Fact ell.Prime := ⟨ell_prime⟩
  let quotient :=
    ((Int.castRingHom (ZMod ell)).mapMatrix (m := Fin 3)).toMonoidWithZeroHom
  apply not_isMortal_of_map_not_isMortal quotient (integralGenerator q D)
  apply not_isMortal_of_ray_action
    (quotient ∘ integralGenerator q D)
    (fun state => if state then alternatingRay else positiveRay)
    signedRayTransition (signedRayWeight (D : ZMod ell)) false
  · intro state ray_zero
    have entry := congrFun ray_zero 0
    cases state <;> norm_num [positiveRay, alternatingRay] at entry
  · intro label state
    cases label with
    | none =>
        cases state
        · exact sub_ne_zero.mpr D_ne_one
        · apply neg_ne_zero.mpr
          intro sum_zero
          apply D_ne_neg_one
          simpa using (add_eq_zero_iff_eq_neg.mp sum_zero)
    | some _ => simp [signedRayWeight]
  · intro label state
    simpa [quotient, Function.comp_def] using
      mapped_integralGenerator_signedRay q D ell q_neg_one label state

/-! ## Prime-power walls and conditional classification -/

/-- A finite field provides either a fixed-ray wall (`q=1`) or the exceptional two-ray wall
(`q=-1`) for the denominator-cleared parameter `c=-D⁻¹`. -/
def HasFiniteWall (q D : ℤ) : Prop :=
  ∃ ell : Nat, ell.Prime ∧
    (((q : ZMod ell) = 1 ∧ (D : ZMod ell) ≠ 1) ∨
      ((q : ZMod ell) = -1 ∧ (D : ZMod ell) ≠ 1 ∧ (D : ZMod ell) ≠ -1))

/-- A primitive divisor of `pʳ-1` supplies the fixed-ray wall for every exponent not divisible
by `r`. This is the sole interface between Bang–Zsigmondy arithmetic and ReturnSquare. -/
theorem hasFiniteWall_of_primitivePrimeDivisor
    (ell p r power : Nat) (primitive : IsPrimitivePrimeDivisor ell p r)
    (not_divides : ¬r ∣ power) :
    HasFiniteWall (p ^ r : Nat) (p ^ power : Nat) := by
  refine ⟨ell, primitive.prime, Or.inl ⟨?_, ?_⟩⟩
  · norm_cast
    simpa using
      (ZMod.natCast_eq_natCast_iff (p ^ r) 1 ell).mpr primitive.modEq_one
  · norm_cast
    exact fun equality =>
      primitive.not_modEq_one_of_not_dvd not_divides
        ((ZMod.natCast_eq_natCast_iff (p ^ power) 1 ell).mp (by simpa using equality))

/-- The exceptional Zsigmondy pair `2⁶-1` still has enough lower-order primitive divisors:
orders two and three jointly detect every exponent not divisible by six. -/
theorem hasFiniteWall_two_pow_six (power : Nat) (not_divides : ¬6 ∣ power) :
    HasFiniteWall (2 ^ 6 : Nat) (2 ^ power : Nat) := by
  have primitive_two : IsPrimitivePrimeDivisor 3 2 2 := by
    simp only [IsPrimitivePrimeDivisor]
    refine ⟨by decide, by decide, by decide, by decide, ?_⟩
    intro earlier earlier_positive earlier_lt
    interval_cases earlier
    all_goals norm_num
  have primitive_three : IsPrimitivePrimeDivisor 7 2 3 := by
    simp only [IsPrimitivePrimeDivisor]
    refine ⟨by decide, by decide, by decide, by decide, ?_⟩
    intro earlier earlier_positive earlier_lt
    interval_cases earlier
    all_goals norm_num
  by_cases two_divides : 2 ∣ power
  · have three_not_divides : ¬3 ∣ power := by
      intro three_divides
      exact not_divides
        (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) two_divides three_divides)
    refine ⟨7, by decide, Or.inl ⟨by decide, ?_⟩⟩
    norm_cast
    exact fun equality =>
      primitive_three.not_modEq_one_of_not_dvd three_not_divides
        ((ZMod.natCast_eq_natCast_iff (2 ^ power) 1 7).mp (by simpa using equality))
  · refine ⟨3, by decide, Or.inl ⟨by decide, ?_⟩⟩
    norm_cast
    exact fun equality =>
      primitive_two.not_modEq_one_of_not_dvd two_divides
        ((ZMod.natCast_eq_natCast_iff (2 ^ power) 1 3).mp (by simpa using equality))

/-- Every square base has a finite wall at every odd exponent. For odd `p`, an odd prime
divisor of `(p²+1)/2` makes the ambient scale `-1`; the terminal scale has square `-1` and
therefore avoids both signed rays. This also discharges Zsigmondy’s power-of-two exception. -/
theorem hasFiniteWall_prime_square
    (p power : Nat) (prime : p.Prime) (not_divides : ¬2 ∣ power) :
    HasFiniteWall (p ^ 2 : Nat) (p ^ power : Nat) := by
  by_cases p_two : p = 2
  · subst p
    have primitive_two : IsPrimitivePrimeDivisor 3 2 2 := by
      simp only [IsPrimitivePrimeDivisor]
      refine ⟨by decide, by decide, by decide, by decide, ?_⟩
      intro earlier earlier_positive earlier_lt
      interval_cases earlier
      all_goals norm_num
    exact hasFiniteWall_of_primitivePrimeDivisor
      3 2 2 power primitive_two not_divides
  have p_odd : Odd p := prime.odd_of_ne_two p_two
  obtain ⟨k, rfl⟩ := p_odd
  let halfSum := ((2 * k + 1) ^ 2 + 1) / 2
  have two_dvd_sum : 2 ∣ (2 * k + 1) ^ 2 + 1 := by
    use 2 * k ^ 2 + 2 * k + 1
    ring
  have halfSum_eq : halfSum = 2 * k ^ 2 + 2 * k + 1 := by
    dsimp [halfSum]
    apply Nat.div_eq_of_eq_mul_left (by decide : 0 < 2)
    ring
  have p_three : 3 ≤ 2 * k + 1 := by
    have := prime.two_le
    omega
  have halfSum_gt_one : 1 < halfSum := by
    rw [halfSum_eq]
    nlinarith
  let ell := halfSum.minFac
  have ell_prime : ell.Prime := Nat.minFac_prime halfSum_gt_one.ne'
  have ell_dvd_halfSum : ell ∣ halfSum := Nat.minFac_dvd halfSum
  have ell_dvd_sum : ell ∣ (2 * k + 1) ^ 2 + 1 :=
    ell_dvd_halfSum.trans (Nat.div_dvd_of_dvd two_dvd_sum)
  have halfSum_odd : Odd halfSum := by
    rw [halfSum_eq]
    exact ⟨k ^ 2 + k, by ring⟩
  have ell_ne_two : ell ≠ 2 := by
    intro ell_two
    have two_dvd_halfSum : 2 ∣ halfSum := ell_two ▸ ell_dvd_halfSum
    exact (Nat.not_even_iff_odd.mpr halfSum_odd)
      (even_iff_two_dvd.mpr two_dvd_halfSum)
  have neg_one_ne_one : (-1 : ZMod ell) ≠ 1 := by
    intro equality
    have two_zero : (2 : ZMod ell) = 0 := by
      calc
        (2 : ZMod ell) = 1 + 1 := by norm_num
        _ = -1 + 1 := by rw [equality]
        _ = 0 := by ring
    have ell_dvd_two : ell ∣ 2 :=
      (ZMod.natCast_eq_zero_iff 2 ell).mp two_zero
    exact ell_ne_two
      (Nat.le_antisymm (Nat.le_of_dvd (by decide) ell_dvd_two) ell_prime.two_le)
  have p_sq_neg_one : ((2 * k + 1 : ZMod ell) ^ 2) = -1 := by
    have sum_zero : (((2 * k + 1) ^ 2 + 1 : Nat) : ZMod ell) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr ell_dvd_sum
    norm_num [Nat.cast_add, Nat.cast_pow] at sum_zero ⊢
    exact eq_neg_of_add_eq_zero_left sum_zero
  have power_odd : Odd power :=
    Nat.not_even_iff_odd.mp fun even =>
      not_divides (even_iff_two_dvd.mp even)
  have terminal_sq_neg_one :
      (((2 * k + 1 : ZMod ell) ^ power) ^ 2) = -1 := by
    calc
      (((2 * k + 1 : ZMod ell) ^ power) ^ 2) =
          (((2 * k + 1 : ZMod ell) ^ 2) ^ power) := by
            rw [← pow_mul, ← pow_mul]
            congr 1
            omega
      _ = (-1) ^ power := by rw [p_sq_neg_one]
      _ = -1 := power_odd.neg_one_pow
  refine ⟨ell, ell_prime, Or.inr ⟨?_, ?_, ?_⟩⟩
  · norm_cast
    simpa using p_sq_neg_one
  · norm_cast
    intro terminal_one
    have terminal_one' : ((2 * (k : ZMod ell) + 1) ^ power) = 1 := by
      simpa using terminal_one
    have square_one : (((2 * k + 1 : ZMod ell) ^ power) ^ 2) = 1 := by
      rw [terminal_one', one_pow]
    exact neg_one_ne_one (terminal_sq_neg_one.symm.trans square_one)
  · norm_cast
    intro terminal_neg_one
    have terminal_neg_one' : ((2 * (k : ZMod ell) + 1) ^ power) = -1 := by
      simpa using terminal_neg_one
    have square_one : (((2 * k + 1 : ZMod ell) ^ power) ^ 2) = 1 := by
      rw [terminal_neg_one']
      ring
    exact neg_one_ne_one (terminal_sq_neg_one.symm.trans square_one)

/-- Every nonresonant exponent at a prime-power base admits a finite quotient wall. Exponent
two uses the signed-ray wall; `2⁶-1` uses its order-two and order-three factors; all other
exponents use Bang–Zsigmondy. -/
theorem hasFiniteWall_primePower
    (p r power : Nat) (prime : p.Prime) (r_positive : 0 < r)
    (not_divides : ¬r ∣ power) :
    HasFiniteWall (p ^ r : Nat) (p ^ power : Nat) := by
  have r_ne_one : r ≠ 1 := by
    intro r_one
    subst r
    exact not_divides (one_dvd power)
  by_cases r_two : r = 2
  · subst r
    exact hasFiniteWall_prime_square p power prime not_divides
  have r_gt_two : 2 < r := by omega
  by_cases exceptional : p = 2 ∧ r = 6
  · obtain ⟨rfl, rfl⟩ := exceptional
    exact hasFiniteWall_two_pow_six power not_divides
  obtain ⟨ell, primitive⟩ :=
    exists_primitivePrimeDivisor prime.one_lt r_gt_two
      (not_and_or.mp exceptional)
  exact hasFiniteWall_of_primitivePrimeDivisor
    ell p r power primitive not_divides

/-- A finite wall excludes the corresponding rational ReturnSquare parameter. -/
theorem not_physical_isMortal_of_finiteWall
    (q D : ℤ) (D_ne : D ≠ 0) (wall : HasFiniteWall q D) :
    ¬IsMortal
      (ReturnFamily.pairGenerator (ambient (q : ℚ)) (cut (-((D : ℚ)⁻¹)))) := by
  intro mortal
  have integral_mortal :=
    (integralGenerator_isMortal_iff q D D_ne).mpr mortal
  obtain ⟨ell, ell_prime, fixed | alternating⟩ := wall
  · exact not_integralGenerator_isMortal_of_mod_one
      q D ell ell_prime fixed.1 fixed.2 integral_mortal
  · exact not_integralGenerator_isMortal_of_mod_neg_one
      q D ell ell_prime alternating.1 alternating.2.1 alternating.2.2 integral_mortal

/-- Positive bridge zeros at base `p^r` remain supported on the underlying prime `p`. -/
theorem positiveBridge_zero_primePower_shape
    (p r : Nat) (prime : p.Prime) (d : ℚ) (positive : 0 < d) (d_ne_one : d ≠ 1)
    (waits : List Nat)
    (bridge_zero : positiveBridge ((p ^ r : Nat) : ℚ) (-d) waits = 0) :
    ∃ power : Nat, d = (p : ℚ) ^ power ∨ d = ((p : ℚ) ^ power)⁻¹ := by
  let q : ℤ := p ^ r
  have bridge_zero' : positiveBridge (q : ℚ) (-d) waits = 0 := by
    simpa [q] using bridge_zero
  have polynomial_zero :
      Polynomial.eval₂ (Int.castRingHom ℚ) d
        (bridgePolynomial (waitScales q waits)) = 0 := by
    rw [positiveBridge_neg_eq_polynomial q] at bridge_zero'
    exact (mul_eq_zero.mp bridge_zero').resolve_left (sub_ne_zero.mpr d_ne_one.symm)
  have product_eq :
      (waitScales q waits).prod =
        (p ^ (r * waitExponent waits) : Nat) := by
    rw [waitScales_prod]
    dsimp [q]
    norm_cast
    rw [pow_mul]
  exact positive_rational_root_prime_shape p (r * waitExponent waits) prime
    (waitScales q waits) d positive product_eq polynomial_zero

/-- Every exact one-return resonance is mortal, for an arbitrary integral base at least two. -/
theorem physical_isMortal_of_resonance
    (q : ℤ) (q_at_least_two : 2 ≤ q) (power : Nat) :
    IsMortal
      (ReturnFamily.pairGenerator (ambient (q : ℚ))
        (cut (-((q : ℚ) ^ power)⁻¹))) := by
  rcases power with _ | power
  · refine ⟨([none, none] : List (Option Unit)), by simp, ?_⟩
    simpa [wordProduct, ReturnFamily.pairGenerator, separatedGenerator,
      Matrix.mul_assoc] using (cut_neg_one_sq (R := ℚ))
  · have q_two : (2 : ℚ) ≤ q := by exact_mod_cast q_at_least_two
    have power_gt_one : (1 : ℚ) < (q : ℚ) ^ (power + 1) := by
      rw [pow_succ]
      have one_le : (1 : ℚ) ≤ (q : ℚ) ^ power :=
        one_le_pow₀ (by linarith)
      nlinarith
    have power_ne : (q : ℚ) ^ (power + 1) ≠ 0 := by positivity
    have c_add_one_ne : -((q : ℚ) ^ (power + 1))⁻¹ + 1 ≠ 0 := by
      have inverse_ne_one :
          ((q : ℚ) ^ (power + 1))⁻¹ ≠ 1 :=
        inv_ne_one.mpr power_gt_one.ne'
      intro sum_zero
      apply inverse_ne_one
      linarith only [sum_zero]
    apply (physical_isMortal_iff_positiveBridge
      q (-((q : ℚ) ^ (power + 1))⁻¹)
      (by omega)).mpr
    refine ⟨[power], ?_⟩
    rw [positiveBridge_singleton]
    field_simp
    ring

end

end MatrixMortality.ReturnSquare
