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
  have power_shell :
      HasValue prime ((q : ℚ) ^ exponent) ((exponent : ℤ) * qValue) := by
    refine ⟨pow_ne_zero exponent q_shell.1, ?_⟩
    rw [padicValRat.pow, q_shell.2]
  have leading_shell :
      HasValue prime (((-1 : ℤ) ^ parity * q ^ exponent : ℤ) : ℚ)
        ((exponent : ℤ) * qValue) := by
    rcases neg_one_pow_eq_or ℤ parity with sign_one | sign_neg_one
    · simpa [sign_one] using power_shell
    · simpa [sign_neg_one] using neg_hasValue power_shell
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
  have q_ne_rat : (q : ℚ) ≠ 0 := by exact_mod_cast q_ne
  have B_ne_rat : (B : ℚ) ≠ 0 := by exact_mod_cast B_ne
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
  have B_sub_one_ne_rat : (B : ℚ) - 1 ≠ 0 := by exact_mod_cast B_sub_one_ne
  have rational_incidence :=
    (positiveBridge_fraction_cons_zero_iff_tailAdjugate
      (q : ℚ) 1 B head (first :: rest)
        B_ne_rat B_sub_one_ne_rat q_ne_rat).mp bridge_zero
  have cast_state :=
    cast_fractionIntegralTailPredecessorState q B (first :: rest)
  have cast_zero := congrFun cast_state 0
  have cast_one := congrFun cast_state 1
  rw [← cast_zero, ← cast_one] at rational_incidence
  simp only [one_mul] at rational_incidence
  have integral_incidence :
      fractionIntegralTailPredecessorState q B (first :: rest) 0 =
        q ^ (head + 1) *
          fractionIntegralTailPredecessorState q B (first :: rest) 1 := by
    exact_mod_cast rational_incidence
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

end MatrixMortality.ReturnSquare
