import MatrixMortality.ReturnSquareTailAdjugate

/-!
# Pure-denominator ReturnSquare tails

For `A=1`, the integral adjugate tail has two exact denominator-adic leading terms.  They force
every denominator prime deeper than twice the complete tail weight onto one common geometric
exponent.
-/

namespace MatrixMortality.ReturnSquare

open scoped Matrix
open PadicValuation

/-- Integral adjugate tail state for the pure fraction `1/B`, evaluated from right to left. -/
def fractionIntegralTailPredecessorState
    (q B : ℤ) : List Nat → Fin 2 → ℤ
  | [] => ![B, 1]
  | wait :: tail =>
      fractionPullbackAdjugate 1 B (q ^ (wait + 1)) *ᵥ
        fractionIntegralTailPredecessorState q B tail

private theorem waitScale_square_mul_tailPower
    (q : ℤ) (wait : Nat) (tail : List Nat) :
    (q ^ (wait + 1)) ^ 2 * q ^ (2 * waitExponent tail) =
      q ^ (2 * waitExponent (wait :: tail)) := by
  rw [← pow_mul, ← pow_add]
  congr 1
  simp [waitExponent]
  omega

/-- Exact denominator-adic leading terms of both integral tail coordinates. -/
theorem fractionIntegralTailPredecessorState_decomposition
    (q B : ℤ) (tail : List Nat) :
    ∃ upperCorrection lowerCorrection : ℤ,
      fractionIntegralTailPredecessorState q B tail 0 = B * upperCorrection ∧
      fractionIntegralTailPredecessorState q B tail 1 =
        (-1 : ℤ) ^ tail.length * q ^ (2 * waitExponent tail) +
          B * lowerCorrection := by
  induction tail with
  | nil =>
      refine ⟨1, 0, ?_, ?_⟩
      · simp [fractionIntegralTailPredecessorState]
      · simp [fractionIntegralTailPredecessorState, waitExponent]
  | cons wait tail induction =>
      obtain ⟨upperCorrection, lowerCorrection, upper_eq, lower_eq⟩ := induction
      let scale := q ^ (wait + 1)
      let leading := (-1 : ℤ) ^ tail.length * q ^ (2 * waitExponent tail)
      refine ⟨
        scale * fractionIntegralTailPredecessorState q B tail 0 -
          fractionIntegralTailPredecessorState q B tail 1,
        scale * upperCorrection + (scale ^ 2 - 1) * leading +
          ((B - 1) * scale ^ 2 - B) * lowerCorrection,
        ?_, ?_⟩
      · simp [fractionIntegralTailPredecessorState, fractionPullbackAdjugate,
          Matrix.mulVec, dotProduct, Fin.sum_univ_succ, scale]
        ring
      · simp [fractionIntegralTailPredecessorState, fractionPullbackAdjugate,
          Matrix.mulVec, dotProduct, Fin.sum_univ_succ, scale]
        rw [upper_eq, lower_eq]
        have power_eq := waitScale_square_mul_tailPower q wait tail
        simp only [pow_succ]
        dsimp [leading]
        rw [← power_eq]
        ring

/-- The upper coordinate divided by `B` after a nonempty tail. -/
def fractionIntegralTailUpperQuotient
    (q B : ℤ) (wait : Nat) (tail : List Nat) : ℤ :=
  q ^ (wait + 1) * fractionIntegralTailPredecessorState q B tail 0 -
    fractionIntegralTailPredecessorState q B tail 1

/-- The displayed upper quotient is exact. -/
theorem fractionIntegralTailPredecessorState_zero_cons
    (q B : ℤ) (wait : Nat) (tail : List Nat) :
    fractionIntegralTailPredecessorState q B (wait :: tail) 0 =
      B * fractionIntegralTailUpperQuotient q B wait tail := by
  simp [fractionIntegralTailPredecessorState, fractionIntegralTailUpperQuotient,
    fractionPullbackAdjugate, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- The upper quotient omits exactly the leftmost tail scale from its denominator-adic leading
term. -/
theorem fractionIntegralTailUpperQuotient_decomposition
    (q B : ℤ) (wait : Nat) (tail : List Nat) :
    ∃ correction : ℤ,
      fractionIntegralTailUpperQuotient q B wait tail =
        (-1 : ℤ) ^ (tail.length + 1) * q ^ (2 * waitExponent tail) +
          B * correction := by
  obtain ⟨upperCorrection, lowerCorrection, upper_eq, lower_eq⟩ :=
    fractionIntegralTailPredecessorState_decomposition q B tail
  refine ⟨q ^ (wait + 1) * upperCorrection - lowerCorrection, ?_⟩
  rw [fractionIntegralTailUpperQuotient, upper_eq, lower_eq]
  simp only [pow_succ]
  ring

/-- Casting the integral recursion recovers the rational adjugate tail state. -/
theorem cast_fractionIntegralTailPredecessorState
    (q B : ℤ) (tail : List Nat) :
    (fun index => (fractionIntegralTailPredecessorState q B tail index : ℚ)) =
      fractionTailPredecessorState (q : ℚ) 1 B tail := by
  induction tail with
  | nil =>
      ext index
      fin_cases index <;>
        simp [fractionIntegralTailPredecessorState, fractionTailPredecessorState,
          wordProduct]
  | cons wait tail induction =>
      rw [fractionTailPredecessorState, wordProduct_cons, ← Matrix.mulVec_mulVec]
      change
        (fun index =>
          (fractionIntegralTailPredecessorState q B (wait :: tail) index : ℚ)) =
          fractionPullbackAdjugate 1 (B : ℚ) ((q : ℚ) ^ (wait + 1)) *ᵥ
            fractionTailPredecessorState (q : ℚ) 1 B tail
      rw [← induction]
      ext index
      fin_cases index <;>
        simp [fractionIntegralTailPredecessorState, fractionPullbackAdjugate,
          Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The adjugate pullback has the same determinant as the original two-dimensional pullback. -/
theorem fractionPullbackAdjugate_det
    {R : Type*} [CommRing R] (A B t : R) :
    (fractionPullbackAdjugate A B t).det = B * (B - A) * t * (t ^ 2 - 1) := by
  rw [Matrix.det_fin_two]
  simp [fractionPullbackAdjugate]
  ring

/-- At an integral base at least two and a nondegenerate pure denominator, no adjugate tail
kills the terminal vector. -/
theorem fractionIntegralTailPredecessorState_ne_zero
    (q B : ℤ) (q_at_least_two : 2 ≤ q) (B_ne : B ≠ 0) (B_sub_one_ne : B - 1 ≠ 0)
    (tail : List Nat) :
    fractionIntegralTailPredecessorState q B tail ≠ 0 := by
  have q_ne : q ≠ 0 := by omega
  have q_ne_rat : (q : ℚ) ≠ 0 := by exact_mod_cast q_ne
  have B_ne_rat : (B : ℚ) ≠ 0 := by exact_mod_cast B_ne
  have B_sub_one_ne_rat : (B : ℚ) - 1 ≠ 0 := by exact_mod_cast B_sub_one_ne
  have tail_word_unit :
      IsUnit (wordProduct
        (fun wait =>
          fractionPullbackAdjugate (1 : ℚ) B ((q : ℚ) ^ (wait + 1))) tail) := by
    apply wordProduct_isUnit
    intro wait
    apply (fractionPullbackAdjugate (1 : ℚ) B
      ((q : ℚ) ^ (wait + 1))).isUnit_iff_isUnit_det.mpr
    rw [fractionPullbackAdjugate_det]
    apply isUnit_iff_ne_zero.mpr
    have q_gt_one : (1 : ℚ) < q := by exact_mod_cast show (1 : ℤ) < q by omega
    have scale_gt_one : (1 : ℚ) < (q : ℚ) ^ (wait + 1) :=
      one_lt_pow₀ q_gt_one (Nat.succ_ne_zero wait)
    have scale_sq_ne : ((q : ℚ) ^ (wait + 1)) ^ 2 - 1 ≠ 0 := by
      nlinarith [sq_nonneg ((q : ℚ) ^ (wait + 1) - 1)]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero B_ne_rat B_sub_one_ne_rat)
        (pow_ne_zero (wait + 1) q_ne_rat)) scale_sq_ne
  have terminal_ne : (![B, 1] : Fin 2 → ℚ) ≠ 0 := by
    intro terminal_zero
    have second_zero := congrFun terminal_zero 1
    norm_num at second_zero
  have rational_state_ne :
      fractionTailPredecessorState (q : ℚ) 1 B tail ≠ 0 := by
    exact unit_mulVec_ne_zero tail_word_unit terminal_ne
  intro integral_zero
  apply rational_state_ne
  rw [← cast_fractionIntegralTailPredecessorState q B tail]
  funext index
  rw [congrFun integral_zero index]
  norm_num

private theorem signedPower_hasValue
    {prime : Nat} [Fact prime.Prime]
    (q : ℤ) (qValue : ℤ)
    (q_shell : HasValue prime (q : ℚ) qValue)
    (exponent parity : Nat) :
    HasValue prime
      (((-1 : ℤ) ^ parity * q ^ exponent : ℤ) : ℚ)
      ((exponent : ℤ) * qValue) := by
  have power_shell :
      HasValue prime ((q : ℚ) ^ exponent) ((exponent : ℤ) * qValue) := by
    refine ⟨pow_ne_zero exponent q_shell.1, ?_⟩
    rw [padicValRat.pow, q_shell.2]
  rcases neg_one_pow_eq_or ℤ parity with sign_one | sign_neg_one
  · simpa [sign_one] using power_shell
  · simpa [sign_neg_one] using neg_hasValue power_shell

private theorem signedPower_add_denominator_mul_hasValue
    {prime : Nat} [Fact prime.Prime]
    (q B : ℤ) (qValue BValue : ℤ)
    (q_shell : HasValue prime (q : ℚ) qValue)
    (B_shell : HasValue prime (B : ℚ) BValue)
    (exponent parity : Nat) (correction : ℤ)
    (leading_lt : (exponent : ℤ) * qValue < BValue) :
    HasValue prime
      (((-1 : ℤ) ^ parity * q ^ exponent + B * correction : ℤ) : ℚ)
      ((exponent : ℤ) * qValue) := by
  have leading_shell := signedPower_hasValue q qValue q_shell exponent parity
  by_cases correction_zero : correction = 0
  · simpa [correction_zero] using leading_shell
  · have correction_shell :
        HasValue prime (correction : ℚ) (padicValInt prime correction : ℤ) := by
      refine ⟨by exact_mod_cast correction_zero, ?_⟩
      exact padicValRat.of_int
    have denominator_term_shell := mul_hasValue B_shell correction_shell
    have correction_value_nonnegative : 0 ≤ (padicValInt prime correction : ℤ) := by
      exact_mod_cast Nat.zero_le (padicValInt prime correction)
    have leading_below_correction :
        (exponent : ℤ) * qValue <
          BValue + (padicValInt prime correction : ℤ) := by
      omega
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow] using
      add_hasValue_left leading_shell denominator_term_shell
        leading_below_correction

private theorem denominatorValue_le_signedPower_add_denominator_mul
    {prime : Nat} [Fact prime.Prime]
    (q B : ℤ) (qValue BValue : ℤ)
    (q_shell : HasValue prime (q : ℚ) qValue)
    (B_shell : HasValue prime (B : ℚ) BValue)
    (exponent parity : Nat) (correction : ℤ)
    (denominator_le_leading : BValue ≤ (exponent : ℤ) * qValue)
    (sum_ne :
      (((-1 : ℤ) ^ parity * q ^ exponent + B * correction : ℤ) : ℚ) ≠ 0) :
    BValue ≤ padicValRat prime
      (((-1 : ℤ) ^ parity * q ^ exponent + B * correction : ℤ) : ℚ) := by
  have leading_shell := signedPower_hasValue q qValue q_shell exponent parity
  have cast_sum :
      (((-1 : ℤ) ^ parity * q ^ exponent + B * correction : ℤ) : ℚ) =
        (((-1 : ℤ) ^ parity * q ^ exponent : ℤ) : ℚ) +
          (B : ℚ) * correction := by
    push_cast
    ring
  rw [cast_sum] at sum_ne ⊢
  by_cases correction_zero : correction = 0
  · simp only [correction_zero, Int.cast_zero, mul_zero, add_zero]
    rw [leading_shell.2]
    exact denominator_le_leading
  · have correction_shell :
        HasValue prime (correction : ℚ) (padicValInt prime correction : ℤ) := by
      refine ⟨by exact_mod_cast correction_zero, ?_⟩
      exact padicValRat.of_int
    have denominator_term_shell := mul_hasValue B_shell correction_shell
    have correction_value_nonnegative : 0 ≤ (padicValInt prime correction : ℤ) := by
      exact_mod_cast Nat.zero_le (padicValInt prime correction)
    have minimum_bound :=
      padicValRat.min_le_padicValRat_add (p := prime) sum_ne
    rw [leading_shell.2, denominator_term_shell.2] at minimum_bound
    omega

/-- A denominator prime deeper than twice the complete tail weight determines the exact source
exponent in every integral pure-denominator ray incidence. -/
theorem fractionIntegralTail_deep_incidence_synchronizes
    {prime : Nat} [Fact prime.Prime]
    (q B : ℤ) (qValue BValue : ℤ)
    (q_shell : HasValue prime (q : ℚ) qValue)
    (B_shell : HasValue prime (B : ℚ) BValue)
    (q_positive : 0 < qValue)
    (headExponent first : Nat) (rest : List Nat)
    (deep :
      2 * (waitExponent (first :: rest) : ℤ) * qValue < BValue)
    (incidence :
      fractionIntegralTailPredecessorState q B (first :: rest) 0 =
        q ^ headExponent *
          fractionIntegralTailPredecessorState q B (first :: rest) 1) :
    BValue = ((headExponent : ℤ) + 2 * (first + 1)) * qValue := by
  let fullWeight := waitExponent (first :: rest)
  let restWeight := waitExponent rest
  have fullWeight_eq :
      (fullWeight : ℤ) = (first + 1 : Nat) + restWeight := by
    simp [fullWeight, restWeight, waitExponent]
  have rest_below_denominator :
      2 * (restWeight : ℤ) * qValue < BValue := by
    have firstWeight_positive : 0 < ((first + 1 : Nat) : ℤ) := by
      exact_mod_cast Nat.succ_pos first
    have restWeight_nonnegative : 0 ≤ (restWeight : ℤ) := by positivity
    nlinarith
  obtain ⟨_, lowerCorrection, _, lower_eq⟩ :=
    fractionIntegralTailPredecessorState_decomposition q B (first :: rest)
  obtain ⟨quotientCorrection, quotient_eq⟩ :=
    fractionIntegralTailUpperQuotient_decomposition q B first rest
  have lower_shell :
      HasValue prime
        (fractionIntegralTailPredecessorState q B (first :: rest) 1 : ℚ)
        (2 * (fullWeight : ℤ) * qValue) := by
    rw [lower_eq]
    have shell := signedPower_add_denominator_mul_hasValue
      q B qValue BValue q_shell B_shell
        (2 * fullWeight) (first :: rest).length lowerCorrection
        (by simpa [fullWeight] using deep)
    simpa [fullWeight] using shell
  have quotient_shell :
      HasValue prime
        (fractionIntegralTailUpperQuotient q B first rest : ℚ)
        (2 * (restWeight : ℤ) * qValue) := by
    rw [quotient_eq]
    have shell := signedPower_add_denominator_mul_hasValue
      q B qValue BValue q_shell B_shell
        (2 * restWeight) (rest.length + 1) quotientCorrection
        (by simpa [restWeight] using rest_below_denominator)
    simpa [restWeight] using shell
  have upper_shell :
      HasValue prime
        (fractionIntegralTailPredecessorState q B (first :: rest) 0 : ℚ)
        (BValue + 2 * (restWeight : ℤ) * qValue) := by
    rw [fractionIntegralTailPredecessorState_zero_cons]
    simpa only [Int.cast_mul] using mul_hasValue B_shell quotient_shell
  have head_power_shell :
      HasValue prime ((q : ℚ) ^ headExponent)
        ((headExponent : ℤ) * qValue) := by
    refine ⟨pow_ne_zero headExponent q_shell.1, ?_⟩
    rw [padicValRat.pow, q_shell.2]
  have right_shell := mul_hasValue head_power_shell lower_shell
  have incidence_rat :
      (fractionIntegralTailPredecessorState q B (first :: rest) 0 : ℚ) =
        (q : ℚ) ^ headExponent *
          (fractionIntegralTailPredecessorState q B (first :: rest) 1 : ℚ) := by
    exact_mod_cast incidence
  have valuation_eq :
      BValue + 2 * (restWeight : ℤ) * qValue =
        (headExponent : ℤ) * qValue +
          2 * (fullWeight : ℤ) * qValue := by
    calc
      BValue + 2 * (restWeight : ℤ) * qValue =
          padicValRat prime
            (fractionIntegralTailPredecessorState q B (first :: rest) 0 : ℚ) :=
        upper_shell.2.symm
      _ = padicValRat prime
          ((q : ℚ) ^ headExponent *
            (fractionIntegralTailPredecessorState q B (first :: rest) 1 : ℚ)) :=
        congrArg (padicValRat prime) incidence_rat
      _ = (headExponent : ℤ) * qValue +
          2 * (fullWeight : ℤ) * qValue := right_shell.2
  rw [fullWeight_eq] at valuation_eq
  push_cast at valuation_eq ⊢
  linear_combination valuation_eq

/-- The synchronized source exponent is larger than twice the weight remaining after the first
tail wait. -/
theorem fractionIntegralTail_deep_incidence_headExponent_gt
    {prime : Nat} [Fact prime.Prime]
    (q B : ℤ) (qValue BValue : ℤ)
    (q_shell : HasValue prime (q : ℚ) qValue)
    (B_shell : HasValue prime (B : ℚ) BValue)
    (q_positive : 0 < qValue)
    (headExponent first : Nat) (rest : List Nat)
    (deep :
      2 * (waitExponent (first :: rest) : ℤ) * qValue < BValue)
    (incidence :
      fractionIntegralTailPredecessorState q B (first :: rest) 0 =
        q ^ headExponent *
          fractionIntegralTailPredecessorState q B (first :: rest) 1) :
    2 * (waitExponent rest : ℤ) < headExponent := by
  have synchronized := fractionIntegralTail_deep_incidence_synchronizes
    q B qValue BValue q_shell B_shell q_positive headExponent first rest
      deep incidence
  rw [synchronized] at deep
  simp only [waitExponent] at deep
  push_cast at deep ⊢
  nlinarith

private theorem integral_incidence_of_positiveBridge_pureDenominator_zero
    (q B : ℤ) (q_ne : q ≠ 0) (B_ne : B ≠ 0) (B_sub_one_ne : B - 1 ≠ 0)
    (head : Nat) (tail : List Nat)
    (bridge_zero :
      positiveBridge (q : ℚ) (-(1 / (B : ℚ))) (head :: tail) = 0) :
    fractionIntegralTailPredecessorState q B tail 0 =
      q ^ (head + 1) * fractionIntegralTailPredecessorState q B tail 1 := by
  have q_ne_rat : (q : ℚ) ≠ 0 := by exact_mod_cast q_ne
  have B_ne_rat : (B : ℚ) ≠ 0 := by exact_mod_cast B_ne
  have B_sub_one_ne_rat : (B : ℚ) - 1 ≠ 0 := by exact_mod_cast B_sub_one_ne
  have rational_incidence :=
    (positiveBridge_fraction_cons_zero_iff_tailAdjugate
      (q : ℚ) 1 B head tail B_ne_rat B_sub_one_ne_rat q_ne_rat).mp bridge_zero
  have cast_state := cast_fractionIntegralTailPredecessorState q B tail
  have cast_zero := congrFun cast_state 0
  have cast_one := congrFun cast_state 1
  rw [← cast_zero, ← cast_one] at rational_incidence
  simp only [one_mul] at rational_incidence
  exact_mod_cast rational_incidence

/-- For the actual ReturnSquare bridge, a sufficiently deep pure denominator prime both
synchronizes that denominator with the head and first tail exponents and bounds the rest of the
tail. -/
theorem positiveBridge_pureDenominator_deep_valuation_certificate
    {prime : Nat} [Fact prime.Prime]
    (q B : ℤ) (qValue BValue : ℤ)
    (q_shell : HasValue prime (q : ℚ) qValue)
    (B_shell : HasValue prime (B : ℚ) BValue)
    (q_positive : 0 < qValue)
    (head first : Nat) (rest : List Nat)
    (deep :
      2 * (waitExponent (first :: rest) : ℤ) * qValue < BValue)
    (bridge_zero :
      positiveBridge (q : ℚ) (-(1 / (B : ℚ)))
        (head :: first :: rest) = 0) :
    BValue = ((head + 1 : Nat) + 2 * (first + 1) : Nat) * qValue ∧
      2 * (waitExponent rest : ℤ) < head + 1 := by
  have q_ne : q ≠ 0 := by exact_mod_cast q_shell.1
  have B_ne : B ≠ 0 := by exact_mod_cast B_shell.1
  have B_sub_one_ne : B - 1 ≠ 0 := by
    intro B_sub_one_zero
    have B_eq_one : B = 1 := sub_eq_zero.mp B_sub_one_zero
    have BValue_zero : BValue = 0 := by
      rw [B_eq_one] at B_shell
      simpa using B_shell.2.symm
    have tailWeight_positive :
        0 < (waitExponent (first :: rest) : ℤ) := by
      exact_mod_cast show 0 < waitExponent (first :: rest) by
        simp [waitExponent]
    have weightedTail_positive :
        0 < 2 * (waitExponent (first :: rest) : ℤ) * qValue := by
      positivity
    nlinarith
  have integral_incidence :
      fractionIntegralTailPredecessorState q B (first :: rest) 0 =
        q ^ (head + 1) *
          fractionIntegralTailPredecessorState q B (first :: rest) 1 := by
    exact integral_incidence_of_positiveBridge_pureDenominator_zero
      q B q_ne B_ne B_sub_one_ne head (first :: rest) bridge_zero
  constructor
  · have synchronized := fractionIntegralTail_deep_incidence_synchronizes
      q B qValue BValue q_shell B_shell q_positive (head + 1) first rest
        deep integral_incidence
    push_cast at synchronized ⊢
    exact synchronized
  · exact fractionIntegralTail_deep_incidence_headExponent_gt
      q B qValue BValue q_shell B_shell q_positive (head + 1) first rest
        deep integral_incidence

/-- Two denominator primes which are both deep along one mortal bridge have the same normalized
depth. The cross-multiplied form avoids division and remains integral. -/
theorem positiveBridge_pureDenominator_two_deep_primes_synchronize
    {leftPrime rightPrime : Nat}
    [Fact leftPrime.Prime] [Fact rightPrime.Prime]
    (q B : ℤ)
    (leftQValue leftBValue rightQValue rightBValue : ℤ)
    (leftQ_shell : HasValue leftPrime (q : ℚ) leftQValue)
    (leftB_shell : HasValue leftPrime (B : ℚ) leftBValue)
    (rightQ_shell : HasValue rightPrime (q : ℚ) rightQValue)
    (rightB_shell : HasValue rightPrime (B : ℚ) rightBValue)
    (leftQ_positive : 0 < leftQValue)
    (rightQ_positive : 0 < rightQValue)
    (head first : Nat) (rest : List Nat)
    (left_deep :
      2 * (waitExponent (first :: rest) : ℤ) * leftQValue < leftBValue)
    (right_deep :
      2 * (waitExponent (first :: rest) : ℤ) * rightQValue < rightBValue)
    (bridge_zero :
      positiveBridge (q : ℚ) (-(1 / (B : ℚ)))
        (head :: first :: rest) = 0) :
    leftBValue * rightQValue = rightBValue * leftQValue := by
  have left_certificate :=
    positiveBridge_pureDenominator_deep_valuation_certificate
      (prime := leftPrime) q B leftQValue leftBValue
        leftQ_shell leftB_shell leftQ_positive head first rest left_deep bridge_zero
  have right_certificate :=
    positiveBridge_pureDenominator_deep_valuation_certificate
      (prime := rightPrime) q B rightQValue rightBValue
        rightQ_shell rightB_shell rightQ_positive head first rest right_deep bridge_zero
  linear_combination left_certificate.1 * rightQValue -
    right_certificate.1 * leftQValue

/-- If the complete tail has reached the denominator shell but the proper rest has not, the
source exponent is at most twice the rest weight. This is the complementary strict chamber to
the deep synchronization theorem. -/
theorem fractionIntegralTail_middle_incidence_headExponent_le
    {prime : Nat} [Fact prime.Prime]
    (q B : ℤ) (qValue BValue : ℤ)
    (q_shell : HasValue prime (q : ℚ) qValue)
    (B_shell : HasValue prime (B : ℚ) BValue)
    (q_positive : 0 < qValue)
    (headExponent first : Nat) (rest : List Nat)
    (rest_deep :
      2 * (waitExponent rest : ℤ) * qValue < BValue)
    (full_shallow :
      BValue ≤ 2 * (waitExponent (first :: rest) : ℤ) * qValue)
    (incidence :
      fractionIntegralTailPredecessorState q B (first :: rest) 0 =
        q ^ headExponent *
          fractionIntegralTailPredecessorState q B (first :: rest) 1) :
    headExponent ≤ 2 * waitExponent rest := by
  let fullWeight := waitExponent (first :: rest)
  let restWeight := waitExponent rest
  obtain ⟨_, lowerCorrection, _, lower_eq⟩ :=
    fractionIntegralTailPredecessorState_decomposition q B (first :: rest)
  obtain ⟨quotientCorrection, quotient_eq⟩ :=
    fractionIntegralTailUpperQuotient_decomposition q B first rest
  have quotient_shell :
      HasValue prime
        (fractionIntegralTailUpperQuotient q B first rest : ℚ)
        (2 * (restWeight : ℤ) * qValue) := by
    rw [quotient_eq]
    have shell := signedPower_add_denominator_mul_hasValue
      q B qValue BValue q_shell B_shell
        (2 * restWeight) (rest.length + 1) quotientCorrection
        (by simpa [restWeight] using rest_deep)
    simpa [restWeight] using shell
  have upper_shell :
      HasValue prime
        (fractionIntegralTailPredecessorState q B (first :: rest) 0 : ℚ)
        (BValue + 2 * (restWeight : ℤ) * qValue) := by
    rw [fractionIntegralTailPredecessorState_zero_cons]
    simpa only [Int.cast_mul] using mul_hasValue B_shell quotient_shell
  have incidence_rat :
      (fractionIntegralTailPredecessorState q B (first :: rest) 0 : ℚ) =
        (q : ℚ) ^ headExponent *
          (fractionIntegralTailPredecessorState q B (first :: rest) 1 : ℚ) := by
    exact_mod_cast incidence
  have lower_ne :
      (fractionIntegralTailPredecessorState q B (first :: rest) 1 : ℚ) ≠ 0 := by
    intro lower_zero
    apply upper_shell.1
    rw [incidence_rat, lower_zero, mul_zero]
  have lower_sum_ne := lower_ne
  rw [lower_eq] at lower_sum_ne
  have lower_bound :
      BValue ≤ padicValRat prime
        (fractionIntegralTailPredecessorState q B (first :: rest) 1 : ℚ) := by
    rw [lower_eq]
    have bound := denominatorValue_le_signedPower_add_denominator_mul
      q B qValue BValue q_shell B_shell
        (2 * fullWeight) (first :: rest).length lowerCorrection
        (by simpa [fullWeight] using full_shallow) lower_sum_ne
    simpa [fullWeight] using bound
  have head_power_shell :
      HasValue prime ((q : ℚ) ^ headExponent)
        ((headExponent : ℤ) * qValue) := by
    refine ⟨pow_ne_zero headExponent q_shell.1, ?_⟩
    rw [padicValRat.pow, q_shell.2]
  have lower_shell :
      HasValue prime
        (fractionIntegralTailPredecessorState q B (first :: rest) 1 : ℚ)
        (padicValRat prime
          (fractionIntegralTailPredecessorState q B (first :: rest) 1 : ℚ)) :=
    ⟨lower_ne, rfl⟩
  have right_shell := mul_hasValue head_power_shell lower_shell
  have valuation_eq :
      BValue + 2 * (restWeight : ℤ) * qValue =
        (headExponent : ℤ) * qValue +
          padicValRat prime
            (fractionIntegralTailPredecessorState q B (first :: rest) 1 : ℚ) := by
    calc
      BValue + 2 * (restWeight : ℤ) * qValue =
          padicValRat prime
            (fractionIntegralTailPredecessorState q B (first :: rest) 0 : ℚ) :=
        upper_shell.2.symm
      _ = padicValRat prime
          ((q : ℚ) ^ headExponent *
            (fractionIntegralTailPredecessorState q B (first :: rest) 1 : ℚ)) :=
        congrArg (padicValRat prime) incidence_rat
      _ = (headExponent : ℤ) * qValue +
          padicValRat prime
            (fractionIntegralTailPredecessorState q B (first :: rest) 1 : ℚ) :=
        right_shell.2
  have head_bound_int : (headExponent : ℤ) ≤ 2 * restWeight := by
    nlinarith
  exact_mod_cast head_bound_int

/-- In the physical middle chamber, the positive head exponent is bounded by twice the proper
rest weight. -/
theorem positiveBridge_pureDenominator_middle_valuation_certificate
    {prime : Nat} [Fact prime.Prime]
    (q B : ℤ) (qValue BValue : ℤ)
    (q_shell : HasValue prime (q : ℚ) qValue)
    (B_shell : HasValue prime (B : ℚ) BValue)
    (q_positive : 0 < qValue)
    (head first : Nat) (rest : List Nat)
    (rest_deep :
      2 * (waitExponent rest : ℤ) * qValue < BValue)
    (full_shallow :
      BValue ≤ 2 * (waitExponent (first :: rest) : ℤ) * qValue)
    (bridge_zero :
      positiveBridge (q : ℚ) (-(1 / (B : ℚ)))
        (head :: first :: rest) = 0) :
    head + 1 ≤ 2 * waitExponent rest := by
  have q_ne : q ≠ 0 := by exact_mod_cast q_shell.1
  have B_ne : B ≠ 0 := by exact_mod_cast B_shell.1
  have B_sub_one_ne : B - 1 ≠ 0 := by
    intro B_sub_one_zero
    have B_eq_one : B = 1 := sub_eq_zero.mp B_sub_one_zero
    have BValue_zero : BValue = 0 := by
      rw [B_eq_one] at B_shell
      simpa using B_shell.2.symm
    have rest_term_nonnegative :
        0 ≤ 2 * (waitExponent rest : ℤ) * qValue := by positivity
    nlinarith
  have integral_incidence :=
    integral_incidence_of_positiveBridge_pureDenominator_zero
      q B q_ne B_ne B_sub_one_ne head (first :: rest) bridge_zero
  exact fractionIntegralTail_middle_incidence_headExponent_le
    q B qValue BValue q_shell B_shell q_positive (head + 1) first rest
      rest_deep full_shallow integral_incidence

/-- The first tail scale divides one fixed rest coordinate times the visible source defect. -/
theorem fractionIntegralTail_incidence_firstScale_dvd
    (q B : ℤ) (headExponent first : Nat) (rest : List Nat)
    (incidence :
      fractionIntegralTailPredecessorState q B (first :: rest) 0 =
        q ^ headExponent *
          fractionIntegralTailPredecessorState q B (first :: rest) 1) :
    q ^ (first + 1) ∣
      B * (q ^ headExponent - 1) *
        fractionIntegralTailPredecessorState q B rest 1 := by
  refine ⟨
    (q ^ headExponent - B) *
        fractionIntegralTailPredecessorState q B rest 0 +
      q ^ headExponent * (B - 1) * q ^ (first + 1) *
        fractionIntegralTailPredecessorState q B rest 1,
    ?_⟩
  simp [fractionIntegralTailPredecessorState, fractionPullbackAdjugate,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at incidence
  linear_combination incidence

/-- Since a positive source power minus one is coprime to every power of the base, the first
tail scale already divides the fixed lower coordinate of the rest, up to `B`. -/
theorem fractionIntegralTail_incidence_firstScale_dvd_restLower
    (q B : ℤ) (headExponent first : Nat) (rest : List Nat)
    (headExponent_positive : 0 < headExponent)
    (incidence :
      fractionIntegralTailPredecessorState q B (first :: rest) 0 =
        q ^ headExponent *
          fractionIntegralTailPredecessorState q B (first :: rest) 1) :
    q ^ (first + 1) ∣
      B * fractionIntegralTailPredecessorState q B rest 1 := by
  have raw_divisibility := fractionIntegralTail_incidence_firstScale_dvd
    q B headExponent first rest incidence
  have base_dvd_source : q ∣ q ^ headExponent :=
    dvd_pow_self q headExponent_positive.ne'
  have source_coprime_base : IsCoprime (q ^ headExponent - 1) q :=
    IsCoprime.sub_one_left_of_dvd base_dvd_source
  have scale_coprime_source :
      IsCoprime (q ^ (first + 1)) (q ^ headExponent - 1) :=
    source_coprime_base.symm.pow_left
  apply scale_coprime_source.dvd_of_dvd_mul_left
  simpa only [mul_assoc, mul_left_comm, mul_comm] using raw_divisibility

/-- Physical bridge specialization of the first-tail-scale divisor gate. -/
theorem positiveBridge_pureDenominator_firstTailScale_dvd_restLower
    (q B : ℤ) (q_ne : q ≠ 0) (B_ne : B ≠ 0) (B_sub_one_ne : B - 1 ≠ 0)
    (head first : Nat) (rest : List Nat)
    (bridge_zero :
      positiveBridge (q : ℚ) (-(1 / (B : ℚ)))
        (head :: first :: rest) = 0) :
    q ^ (first + 1) ∣
      B * fractionIntegralTailPredecessorState q B rest 1 := by
  have integral_incidence :=
    integral_incidence_of_positiveBridge_pureDenominator_zero
      q B q_ne B_ne B_sub_one_ne head (first :: rest) bridge_zero
  exact fractionIntegralTail_incidence_firstScale_dvd_restLower
    q B (head + 1) first rest (Nat.succ_pos head) integral_incidence

/-- A vanishing bridge either already has the one-return denominator or its first tail scale
divides a fixed nonzero rest coordinate. -/
theorem positiveBridge_pureDenominator_resonance_or_firstTailScale_dvd
    (q B : ℤ) (q_at_least_two : 2 ≤ q)
    (B_ne : B ≠ 0) (B_sub_one_ne : B - 1 ≠ 0)
    (head first : Nat) (rest : List Nat)
    (bridge_zero :
      positiveBridge (q : ℚ) (-(1 / (B : ℚ)))
        (head :: first :: rest) = 0) :
    B = q ^ (head + 1) ∨
      (fractionIntegralTailPredecessorState q B rest 1 ≠ 0 ∧
        q ^ (first + 1) ∣
          B * fractionIntegralTailPredecessorState q B rest 1) := by
  have q_ne : q ≠ 0 := by omega
  have integral_incidence :=
    integral_incidence_of_positiveBridge_pureDenominator_zero
      q B q_ne B_ne B_sub_one_ne head (first :: rest) bridge_zero
  by_cases lower_zero : fractionIntegralTailPredecessorState q B rest 1 = 0
  · left
    have rest_state_ne := fractionIntegralTailPredecessorState_ne_zero
      q B q_at_least_two B_ne B_sub_one_ne rest
    have upper_ne : fractionIntegralTailPredecessorState q B rest 0 ≠ 0 := by
      intro upper_zero
      apply rest_state_ne
      funext index
      fin_cases index
      · exact upper_zero
      · exact lower_zero
    have scale_upper_ne :
        q ^ (first + 1) *
            fractionIntegralTailPredecessorState q B rest 0 ≠ 0 :=
      mul_ne_zero (pow_ne_zero (first + 1) q_ne) upper_ne
    apply mul_right_cancel₀ scale_upper_ne
    simpa [fractionIntegralTailPredecessorState, fractionPullbackAdjugate,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, lower_zero,
      mul_assoc, mul_left_comm, mul_comm] using integral_incidence
  · right
    exact ⟨lower_zero,
      fractionIntegralTail_incidence_firstScale_dvd_restLower
        q B (head + 1) first rest (Nat.succ_pos head) integral_incidence⟩

/-- One denominator prime whose depth exceeds twice the proper-rest weight gives a finite
pivot: either the complete tail is deep and synchronized, or the head is bounded and the first
tail scale divides one fixed rest coordinate. -/
theorem positiveBridge_pureDenominator_rest_deep_pivot_certificate
    {prime : Nat} [Fact prime.Prime]
    (q B : ℤ) (qValue BValue : ℤ)
    (q_at_least_two : 2 ≤ q)
    (q_shell : HasValue prime (q : ℚ) qValue)
    (B_shell : HasValue prime (B : ℚ) BValue)
    (q_positive : 0 < qValue)
    (head first : Nat) (rest : List Nat)
    (rest_deep :
      2 * (waitExponent rest : ℤ) * qValue < BValue)
    (bridge_zero :
      positiveBridge (q : ℚ) (-(1 / (B : ℚ)))
        (head :: first :: rest) = 0) :
    (BValue = ((head + 1 : Nat) + 2 * (first + 1) : Nat) * qValue ∧
        2 * (waitExponent rest : ℤ) < head + 1) ∨
      (head + 1 ≤ 2 * waitExponent rest ∧
        (B = q ^ (head + 1) ∨
          (fractionIntegralTailPredecessorState q B rest 1 ≠ 0 ∧
            q ^ (first + 1) ∣
              B * fractionIntegralTailPredecessorState q B rest 1))) := by
  by_cases full_deep :
      2 * (waitExponent (first :: rest) : ℤ) * qValue < BValue
  · exact Or.inl (positiveBridge_pureDenominator_deep_valuation_certificate
      q B qValue BValue q_shell B_shell q_positive head first rest
        full_deep bridge_zero)
  · have full_shallow :
        BValue ≤ 2 * (waitExponent (first :: rest) : ℤ) * qValue :=
      le_of_not_gt full_deep
    have head_bound := positiveBridge_pureDenominator_middle_valuation_certificate
      q B qValue BValue q_shell B_shell q_positive head first rest
        rest_deep full_shallow bridge_zero
    have q_ne : q ≠ 0 := by exact_mod_cast q_shell.1
    have B_ne : B ≠ 0 := by exact_mod_cast B_shell.1
    have B_sub_one_ne : B - 1 ≠ 0 := by
      intro B_sub_one_zero
      have B_eq_one : B = 1 := sub_eq_zero.mp B_sub_one_zero
      have BValue_zero : BValue = 0 := by
        rw [B_eq_one] at B_shell
        simpa using B_shell.2.symm
      have rest_term_nonnegative :
          0 ≤ 2 * (waitExponent rest : ℤ) * qValue := by positivity
      nlinarith
    have first_scale_certificate :=
      positiveBridge_pureDenominator_resonance_or_firstTailScale_dvd
        q B q_at_least_two B_ne B_sub_one_ne head first rest bridge_zero
    exact Or.inr ⟨head_bound, first_scale_certificate⟩

end MatrixMortality.ReturnSquare
