import MatrixMortality.PadicValuation
import MatrixMortality.ReturnSquareClassification

/-!
# Composite-base ReturnSquare obstructions

This file isolates arithmetic conditions that survive when the ReturnSquare base has several
prime factors. They are necessary conditions only; the arbitrary-composite classification
remains open.
-/

namespace MatrixMortality.ReturnSquare

open scoped Matrix Polynomial
open PadicValuation

noncomputable section

/-- The rational-root theorem before any prime-power specialization. The canonical numerator
divides the scale product, while the canonical denominator divides its square. -/
theorem rational_root_num_den_dvd_scale_product
    (scales : List ℤ) (d : ℚ) (product_ne : scales.prod ≠ 0)
    (root :
      Polynomial.eval₂ (Int.castRingHom ℚ) d (bridgePolynomial scales) = 0) :
    (IsFractionRing.num ℤ d).natAbs ∣ scales.prod.natAbs ∧
      ((IsFractionRing.den ℤ d : ℤ).natAbs) ∣ scales.prod.natAbs ^ 2 := by
  have algebraic_root : Polynomial.aeval d (bridgePolynomial scales) = 0 := by
    simpa [Polynomial.aeval_def] using root
  have numerator_dvd_int : IsFractionRing.num ℤ d ∣ scales.prod := by
    simpa [bridgePolynomial_coeff_zero] using num_dvd_of_is_root algebraic_root
  have denominator_dvd_int :
      (IsFractionRing.den ℤ d : ℤ) ∣
        (-1 : ℤ) ^ scales.length * scales.prod ^ 2 := by
    simpa [bridgePolynomial_leadingCoeff scales product_ne] using
      den_dvd_of_is_root algebraic_root
  refine ⟨Int.natAbs_dvd_natAbs.mpr numerator_dvd_int, ?_⟩
  have absolute := Int.natAbs_dvd_natAbs.mpr denominator_dvd_int
  have absolute_value :
      ((-1 : ℤ) ^ scales.length * scales.prod ^ 2).natAbs =
        scales.prod.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one,
      one_pow, one_mul, Int.natAbs_pow]
  rwa [absolute_value] at absolute

/-- Geometric powers are essential to the composite-base obstruction. The arbitrary scale word
`[2,4,2,14]` has the nonresonant normalized root `d=7/8`. -/
theorem arbitraryScales_seven_eighths_zero :
    (wordProduct (normalizedTransfer (7 / 8 : ℚ)) [2, 4, 2, 14]) 0 0 = 0 ∧
      ∀ t ∈ ([2, 4, 2, 14] : List ℚ), (7 / 8 : ℚ) ≠ t⁻¹ := by
  constructor
  · norm_num [wordProduct, normalizedTransfer_eq, Matrix.mul_apply, Fin.sum_univ_succ]
  · norm_num [List.mem_cons]

private theorem normalizedWord_cons_entry_zero
    {α : Type*} (d : ℚ) (scale : α → ℚ) (head : α) (tail : List α) :
    (wordProduct (fun letter => normalizedTransfer d (scale letter)) (head :: tail)) 0 0 =
      scale head * ((1 - d * scale head) *
          (wordProduct (fun letter => normalizedTransfer d (scale letter)) tail) 0 0 -
        d * (scale head - 1) *
          (wordProduct (fun letter => normalizedTransfer d (scale letter)) tail) 1 0) := by
  rw [wordProduct_cons, Matrix.mul_apply]
  simp [normalizedTransfer_eq, Fin.sum_univ_succ]
  ring

private theorem normalizedWord_cons_entry_one
    {α : Type*} (d : ℚ) (scale : α → ℚ) (head : α) (tail : List α) :
    (wordProduct (fun letter => normalizedTransfer d (scale letter)) (head :: tail)) 1 0 =
      (scale head ^ 2 - 1) *
        ((wordProduct (fun letter => normalizedTransfer d (scale letter)) tail) 0 0 +
          (wordProduct (fun letter => normalizedTransfer d (scale letter)) tail) 1 0) := by
  rw [wordProduct_cons, Matrix.mul_apply]
  simp [normalizedTransfer_eq, Fin.sum_univ_succ]
  ring

private theorem pow_hasValue
    {prime : Nat} [Fact prime.Prime] {value : ℚ} {valuation : ℤ}
    (value_shell : HasValue prime value valuation) (exponent : Nat) :
    HasValue prime (value ^ exponent) (exponent * valuation) := by
  refine ⟨pow_ne_zero exponent value_shell.1, ?_⟩
  rw [padicValRat.pow, value_shell.2]

private theorem positive_pow_hasValue
    {prime : Nat} [Fact prime.Prime] {value : ℚ} {valuation : ℤ}
    (value_shell : HasValue prime value valuation) (valuation_positive : 0 < valuation)
    (exponent : Nat) (exponent_positive : 0 < exponent) :
    IsPositive prime (value ^ exponent) := by
  have shell := pow_hasValue value_shell exponent
  exact ⟨shell.1, shell.2.symm ▸ mul_pos (by exact_mod_cast exponent_positive) valuation_positive⟩

private def PositiveBridgeState
    (prime : Nat) (rootValue totalValue : ℤ) (upper lower : ℚ) : Prop :=
  IsUnit prime lower ∧
    (totalValue ≤ rootValue → HasValue prime upper totalValue) ∧
    (rootValue < totalValue →
      upper = 0 ∨
        ∃ upperValue : ℤ, rootValue < upperValue ∧
          HasValue prime upper upperValue)

private theorem positiveBridgeState_step
    {prime : Nat} [Fact prime.Prime]
    {d t upper lower : ℚ} {rootValue scaleValue totalValue : ℤ}
    (d_shell : HasValue prime d rootValue) (root_positive : 0 < rootValue)
    (t_shell : HasValue prime t scaleValue) (scale_positive : 0 < scaleValue)
    (total_positive : 0 < totalValue)
    (state : PositiveBridgeState prime rootValue totalValue upper lower) :
    PositiveBridgeState prime rootValue (scaleValue + totalValue)
      (t * ((1 - d * t) * upper - d * (t - 1) * lower))
      ((t ^ 2 - 1) * (upper + lower)) := by
  have t_positive : IsPositive prime t := ⟨t_shell.1, t_shell.2.symm ▸ scale_positive⟩
  have dt_shell : HasValue prime (d * t) (rootValue + scaleValue) :=
    mul_hasValue d_shell t_shell
  have dt_positive : IsPositive prime (d * t) :=
    ⟨dt_shell.1, dt_shell.2.symm ▸ add_pos root_positive scale_positive⟩
  have one_sub_dt_unit : IsUnit prime (1 - d * t) :=
    one_sub_positive dt_positive
  have t_sub_one_unit : IsUnit prime (t - 1) :=
    positive_sub_one t_positive
  have t_sq_positive : IsPositive prime (t ^ 2) :=
    positive_pow_hasValue t_shell scale_positive 2 (by omega)
  have t_sq_sub_one_unit : IsUnit prime (t ^ 2 - 1) :=
    positive_sub_one t_sq_positive
  have upper_zero_or_positive : upper = 0 ∨ IsPositive prime upper := by
    by_cases total_le : totalValue ≤ rootValue
    · have upper_shell := state.2.1 total_le
      exact Or.inr ⟨upper_shell.1, upper_shell.2.symm ▸ total_positive⟩
    · have root_lt_total : rootValue < totalValue := lt_of_not_ge total_le
      obtain upper_zero | ⟨upperValue, root_lt_upper, upper_shell⟩ :=
        state.2.2 root_lt_total
      · exact Or.inl upper_zero
      · exact Or.inr
          ⟨upper_shell.1, upper_shell.2.symm ▸ lt_trans root_positive root_lt_upper⟩
  have upper_add_lower_unit : IsUnit prime (upper + lower) := by
    obtain rfl | upper_positive := upper_zero_or_positive
    · simpa using state.1
    · rw [add_comm]
      exact unit_add_positive state.1 upper_positive
  have lower_next_unit :
      IsUnit prime ((t ^ 2 - 1) * (upper + lower)) := by
    simpa using mul_hasValue t_sq_sub_one_unit upper_add_lower_unit
  refine ⟨lower_next_unit, ?_, ?_⟩
  · intro next_le
    have total_lt_root : totalValue < rootValue := by omega
    have upper_shell := state.2.1 total_lt_root.le
    have left_shell :
        HasValue prime ((1 - d * t) * upper) totalValue := by
      simpa using mul_hasValue one_sub_dt_unit upper_shell
    have right_shell :
        HasValue prime (d * (t - 1) * lower) rootValue := by
      simpa using mul_hasValue (mul_hasValue d_shell t_sub_one_unit) state.1
    have difference_shell :
        HasValue prime
          ((1 - d * t) * upper - d * (t - 1) * lower) totalValue := by
      have shell := sub_hasValue_min left_shell.1 right_shell.1 (by
          rw [left_shell.2, right_shell.2]
          exact ne_of_lt total_lt_root)
      rw [left_shell.2, right_shell.2, min_eq_left total_lt_root.le] at shell
      exact shell
    exact mul_hasValue t_shell difference_shell
  · intro root_lt_next
    rcases lt_trichotomy totalValue rootValue with total_lt_root | total_eq_root | root_lt_total
    · have upper_shell := state.2.1 total_lt_root.le
      have left_shell :
          HasValue prime ((1 - d * t) * upper) totalValue := by
        simpa using mul_hasValue one_sub_dt_unit upper_shell
      have right_shell :
          HasValue prime (d * (t - 1) * lower) rootValue := by
        simpa using mul_hasValue (mul_hasValue d_shell t_sub_one_unit) state.1
      have difference_shell :
          HasValue prime
            ((1 - d * t) * upper - d * (t - 1) * lower) totalValue := by
        have shell := sub_hasValue_min left_shell.1 right_shell.1 (by
            rw [left_shell.2, right_shell.2]
            exact ne_of_lt total_lt_root)
        rw [left_shell.2, right_shell.2, min_eq_left total_lt_root.le] at shell
        exact shell
      exact Or.inr ⟨scaleValue + totalValue, root_lt_next,
        mul_hasValue t_shell difference_shell⟩
    · subst totalValue
      have upper_shell := state.2.1 le_rfl
      have left_shell :
          HasValue prime ((1 - d * t) * upper) rootValue := by
        simpa using mul_hasValue one_sub_dt_unit upper_shell
      have right_shell :
          HasValue prime (d * (t - 1) * lower) rootValue := by
        simpa using mul_hasValue (mul_hasValue d_shell t_sub_one_unit) state.1
      by_cases difference_zero :
          (1 - d * t) * upper - d * (t - 1) * lower = 0
      · exact Or.inl (by rw [difference_zero, mul_zero])
      · let differenceValue :=
          padicValRat prime
            ((1 - d * t) * upper - d * (t - 1) * lower)
        have root_le_difference : rootValue ≤ differenceValue := by
          dsimp [differenceValue]
          simpa [left_shell.2, right_shell.2] using
            min_le_sub (prime := prime) difference_zero
        have difference_shell :
            HasValue prime
              ((1 - d * t) * upper - d * (t - 1) * lower)
              differenceValue :=
          ⟨difference_zero, rfl⟩
        refine Or.inr ⟨scaleValue + differenceValue, ?_,
          mul_hasValue t_shell difference_shell⟩
        omega
    · obtain upper_zero | ⟨upperValue, root_lt_upper, upper_shell⟩ :=
        state.2.2 root_lt_total
      · subst upper
        have right_shell :
            HasValue prime (d * (t - 1) * lower) rootValue := by
          simpa using mul_hasValue (mul_hasValue d_shell t_sub_one_unit) state.1
        have difference_shell :
            HasValue prime
              ((1 - d * t) * 0 - d * (t - 1) * lower) rootValue := by
          simpa using neg_hasValue right_shell
        exact Or.inr ⟨scaleValue + rootValue, by omega,
          mul_hasValue t_shell difference_shell⟩
      · have left_shell :
            HasValue prime ((1 - d * t) * upper) upperValue := by
          simpa using mul_hasValue one_sub_dt_unit upper_shell
        have right_shell :
            HasValue prime (d * (t - 1) * lower) rootValue := by
          simpa using mul_hasValue (mul_hasValue d_shell t_sub_one_unit) state.1
        have difference_shell :
            HasValue prime
              ((1 - d * t) * upper - d * (t - 1) * lower) rootValue := by
          have shell := sub_hasValue_min left_shell.1 right_shell.1 (by
              rw [left_shell.2, right_shell.2]
              exact ne_of_gt root_lt_upper)
          rw [left_shell.2, right_shell.2, min_eq_right root_lt_upper.le] at shell
          exact shell
        exact Or.inr ⟨scaleValue + rootValue, by omega,
          mul_hasValue t_shell difference_shell⟩

private def normalizedWaitWord (q d : ℚ) (waits : List Nat) : Square (Fin 2) ℚ :=
  wordProduct (fun wait => normalizedTransfer d (q ^ (wait + 1))) waits

private theorem normalizedWaitWord_cons_entry_zero
    (q d : ℚ) (wait : Nat) (waits : List Nat) :
    normalizedWaitWord q d (wait :: waits) 0 0 =
      q ^ (wait + 1) *
        ((1 - d * q ^ (wait + 1)) * normalizedWaitWord q d waits 0 0 -
          d * (q ^ (wait + 1) - 1) * normalizedWaitWord q d waits 1 0) := by
  simpa only [normalizedWaitWord] using
    normalizedWord_cons_entry_zero d (fun wait => q ^ (wait + 1)) wait waits

private theorem normalizedWaitWord_cons_entry_one
    (q d : ℚ) (wait : Nat) (waits : List Nat) :
    normalizedWaitWord q d (wait :: waits) 1 0 =
      ((q ^ (wait + 1)) ^ 2 - 1) *
        (normalizedWaitWord q d waits 0 0 + normalizedWaitWord q d waits 1 0) := by
  simpa only [normalizedWaitWord] using
    normalizedWord_cons_entry_one d (fun wait => q ^ (wait + 1)) wait waits

private theorem normalizedWaitWord_positive_state
    {prime : Nat} [Fact prime.Prime]
    (q d : ℚ) (scaleValue rootValue : ℤ)
    (q_shell : HasValue prime q scaleValue) (scale_positive : 0 < scaleValue)
    (d_shell : HasValue prime d rootValue) (root_positive : 0 < rootValue)
    (waits : List Nat) (waits_nonempty : waits ≠ []) :
    PositiveBridgeState prime rootValue
      (waitExponent waits * scaleValue)
      (normalizedWaitWord q d waits 0 0)
      (normalizedWaitWord q d waits 1 0) := by
  induction waits with
  | nil => exact (waits_nonempty rfl).elim
  | cons wait waits induction =>
      let t := q ^ (wait + 1)
      let waitValue : ℤ := (wait + 1) * scaleValue
      have wait_positive : 0 < waitValue := by
        dsimp [waitValue]
        exact mul_pos (by exact_mod_cast Nat.succ_pos wait) scale_positive
      have t_shell : HasValue prime t waitValue := by
        simpa [t, waitValue] using pow_hasValue q_shell (wait + 1)
      cases waits with
      | nil =>
          have t_positive : IsPositive prime t :=
            ⟨t_shell.1, t_shell.2.symm ▸ wait_positive⟩
          have dt_shell : HasValue prime (d * t) (rootValue + waitValue) :=
            mul_hasValue d_shell t_shell
          have dt_positive : IsPositive prime (d * t) :=
            ⟨dt_shell.1, dt_shell.2.symm ▸ add_pos root_positive wait_positive⟩
          have one_sub_dt_unit : IsUnit prime (1 - d * t) :=
            one_sub_positive dt_positive
          have upper_shell : HasValue prime (t * (1 - d * t)) waitValue := by
            simpa using mul_hasValue t_shell one_sub_dt_unit
          have t_sq_positive : IsPositive prime (t ^ 2) :=
            positive_pow_hasValue t_shell wait_positive 2 (by omega)
          have lower_unit : IsUnit prime (t ^ 2 - 1) :=
            positive_sub_one t_sq_positive
          have upper_eq : normalizedWaitWord q d [wait] 0 0 =
              t * (1 - d * t) := by
            simp [normalizedWaitWord, t, normalizedTransfer_eq]
            ring
          have lower_eq : normalizedWaitWord q d [wait] 1 0 = t ^ 2 - 1 := by
            simp [normalizedWaitWord, t, normalizedTransfer_eq]
          rw [upper_eq, lower_eq]
          refine ⟨lower_unit, ?_, ?_⟩
          · intro _
            simpa [waitValue, waitExponent] using upper_shell
          · intro root_lt_wait
            exact Or.inr ⟨waitValue, root_lt_wait, upper_shell⟩
      | cons next rest =>
          have tail_nonempty : next :: rest ≠ [] := by simp
          have tail_state := induction tail_nonempty
          have tail_positive :
              0 < (waitExponent (next :: rest) : ℤ) * scaleValue := by
            have exponent_positive : 0 < waitExponent (next :: rest) := by
              simp [waitExponent]
            exact mul_pos (by exact_mod_cast exponent_positive) scale_positive
          have stepped :=
            positiveBridgeState_step d_shell root_positive t_shell wait_positive
              tail_positive tail_state
          dsimp [waitValue] at stepped
          rw [normalizedWaitWord_cons_entry_zero q d wait (next :: rest),
            normalizedWaitWord_cons_entry_one q d wait (next :: rest)]
          simpa [t, waitExponent, add_mul] using stepped

/-- A zero normalized word at a prime where both the base and parameter have positive valuation
forces the parameter valuation to equal the complete valuation of the proper tail. In
particular, the normalizing root cannot be created by a singleton word. -/
theorem normalizedWord_zero_positive_valuation_eq_tail
    {prime : Nat} [Fact prime.Prime]
    (q d : ℚ) (scaleValue rootValue : ℤ)
    (q_shell : HasValue prime q scaleValue) (scale_positive : 0 < scaleValue)
    (d_shell : HasValue prime d rootValue) (root_positive : 0 < rootValue)
    (head : Nat) (tail : List Nat)
    (word_zero :
      (wordProduct
        (fun wait => normalizedTransfer d (q ^ (wait + 1)))
        (head :: tail)) 0 0 = 0) :
    tail ≠ [] ∧ rootValue = waitExponent tail * scaleValue := by
  have tail_nonempty : tail ≠ [] := by
    intro tail_empty
    subst tail
    let t := q ^ (head + 1)
    let headValue : ℤ := (head + 1) * scaleValue
    have head_value_positive : 0 < headValue := by
      dsimp [headValue]
      exact mul_pos (by exact_mod_cast Nat.succ_pos head) scale_positive
    have t_shell : HasValue prime t headValue := by
      simpa [t, headValue] using pow_hasValue q_shell (head + 1)
    have dt_shell : HasValue prime (d * t) (rootValue + headValue) :=
      mul_hasValue d_shell t_shell
    have dt_positive : IsPositive prime (d * t) :=
      ⟨dt_shell.1, dt_shell.2.symm ▸ add_pos root_positive head_value_positive⟩
    have one_sub_dt_unit : IsUnit prime (1 - d * t) :=
      one_sub_positive dt_positive
    have singleton_ne : t * (1 - d * t) ≠ 0 :=
      mul_ne_zero t_shell.1 one_sub_dt_unit.1
    have singleton_eq :
        (wordProduct
          (fun wait => normalizedTransfer d (q ^ (wait + 1))) [head]) 0 0 =
          t * (1 - d * t) := by
      simpa [normalizedWaitWord] using
        normalizedWaitWord_cons_entry_zero q d head []
    exact singleton_ne (singleton_eq.symm.trans word_zero)
  have tail_state :=
    normalizedWaitWord_positive_state q d scaleValue rootValue
      q_shell scale_positive d_shell root_positive tail tail_nonempty
  let t := q ^ (head + 1)
  let headValue : ℤ := (head + 1) * scaleValue
  have head_value_positive : 0 < headValue := by
    dsimp [headValue]
    exact mul_pos (by exact_mod_cast Nat.succ_pos head) scale_positive
  have t_shell : HasValue prime t headValue := by
    simpa [t, headValue] using pow_hasValue q_shell (head + 1)
  have t_positive : IsPositive prime t :=
    ⟨t_shell.1, t_shell.2.symm ▸ head_value_positive⟩
  have dt_shell : HasValue prime (d * t) (rootValue + headValue) :=
    mul_hasValue d_shell t_shell
  have dt_positive : IsPositive prime (d * t) :=
    ⟨dt_shell.1, dt_shell.2.symm ▸ add_pos root_positive head_value_positive⟩
  have one_sub_dt_unit : IsUnit prime (1 - d * t) :=
    one_sub_positive dt_positive
  have t_sub_one_unit : IsUnit prime (t - 1) :=
    positive_sub_one t_positive
  have difference_zero :
      (1 - d * t) * normalizedWaitWord q d tail 0 0 -
        d * (t - 1) * normalizedWaitWord q d tail 1 0 = 0 := by
    have product_zero :
        t * ((1 - d * t) * normalizedWaitWord q d tail 0 0 -
          d * (t - 1) * normalizedWaitWord q d tail 1 0) = 0 := by
      rw [← normalizedWaitWord_cons_entry_zero q d head tail]
      simpa [normalizedWaitWord] using word_zero
    exact (mul_eq_zero.mp product_zero).resolve_left t_shell.1
  have cancellation :
      (1 - d * t) * normalizedWaitWord q d tail 0 0 =
        d * (t - 1) * normalizedWaitWord q d tail 1 0 :=
    sub_eq_zero.mp difference_zero
  have right_shell :
      HasValue prime
        (d * (t - 1) * normalizedWaitWord q d tail 1 0) rootValue := by
    simpa using
      mul_hasValue (mul_hasValue d_shell t_sub_one_unit) tail_state.1
  have upper_eq :
      normalizedWaitWord q d tail 0 0 =
        (d * (t - 1) * normalizedWaitWord q d tail 1 0) /
          (1 - d * t) := by
    apply (eq_div_iff one_sub_dt_unit.1).2
    simpa [mul_comm] using cancellation
  have upper_shell :
      HasValue prime (normalizedWaitWord q d tail 0 0) rootValue := by
    rw [upper_eq]
    simpa using div_hasValue right_shell one_sub_dt_unit
  refine ⟨tail_nonempty, ?_⟩
  by_cases total_le : (waitExponent tail : ℤ) * scaleValue ≤ rootValue
  · have exact_shell := tail_state.2.1 total_le
    exact upper_shell.2.symm.trans exact_shell.2
  · have root_lt_total :
        rootValue < (waitExponent tail : ℤ) * scaleValue :=
      lt_of_not_ge total_le
    obtain upper_zero | ⟨upperValue, root_lt_upper, high_shell⟩ :=
      tail_state.2.2 root_lt_total
    · exact (upper_shell.1 upper_zero).elim
    · have root_eq_upper : rootValue = upperValue :=
        upper_shell.2.symm.trans high_shell.2
      exact (ne_of_lt root_lt_upper root_eq_upper).elim

private theorem normalizedWaitWord_int_eq
    (q : ℤ) (d : ℚ) (waits : List Nat) :
    normalizedWaitWord (q : ℚ) d waits =
      wordProduct (fun t : ℤ => normalizedTransfer d (t : ℚ))
        (waitScales q waits) := by
  induction waits with
  | nil => simp [normalizedWaitWord, waitScales]
  | cons wait waits induction =>
      rw [show waitScales q (wait :: waits) =
        q ^ (wait + 1) :: waitScales q waits by rfl]
      rw [normalizedWaitWord, wordProduct_cons, wordProduct_cons]
      change normalizedTransfer d ((q : ℚ) ^ (wait + 1)) *
          wordProduct
            (fun wait => normalizedTransfer d ((q : ℚ) ^ (wait + 1))) waits =
        normalizedTransfer d ((q ^ (wait + 1) : ℤ) : ℚ) *
          wordProduct (fun t : ℤ => normalizedTransfer d (t : ℚ))
            (waitScales q waits)
      change wordProduct
          (fun wait => normalizedTransfer d ((q : ℚ) ^ (wait + 1))) waits =
        wordProduct (fun t : ℤ => normalizedTransfer d (t : ℚ))
          (waitScales q waits) at induction
      rw [Int.cast_pow, induction]

private theorem positiveBridge_neg_eq_normalizedWaitWord
    (q : ℤ) (d : ℚ) (waits : List Nat) :
    positiveBridge (q : ℚ) (-d) waits =
      (1 - d) * normalizedWaitWord (q : ℚ) d waits 0 0 := by
  rw [positiveBridge_neg_eq_polynomial, bridgePolynomial_eval₂]
  rw [normalizedWaitWord_int_eq]

/-- Every nondegenerate rational bridge zero at an arbitrary nonzero integral base is supported
on the prime divisors of that base. The exponents remain unrestricted at this stage. -/
theorem positiveBridge_zero_num_den_dvd_base
    (q : ℤ) (q_ne : q ≠ 0) (d : ℚ) (d_ne_one : d ≠ 1)
    (waits : List Nat) (bridge_zero : positiveBridge (q : ℚ) (-d) waits = 0) :
    (IsFractionRing.num ℤ d).natAbs ∣ q.natAbs ^ waitExponent waits ∧
      ((IsFractionRing.den ℤ d : ℤ).natAbs) ∣
        q.natAbs ^ (2 * waitExponent waits) := by
  have polynomial_zero :
      Polynomial.eval₂ (Int.castRingHom ℚ) d
        (bridgePolynomial (waitScales q waits)) = 0 := by
    rw [positiveBridge_neg_eq_polynomial] at bridge_zero
    exact (mul_eq_zero.mp bridge_zero).resolve_left (sub_ne_zero.mpr d_ne_one.symm)
  have product_ne : (waitScales q waits).prod ≠ 0 := by
    rw [waitScales_prod]
    exact pow_ne_zero (waitExponent waits) q_ne
  have divisibility :=
    rational_root_num_den_dvd_scale_product
      (waitScales q waits) d product_ne polynomial_zero
  rw [waitScales_prod, Int.natAbs_pow] at divisibility
  refine ⟨divisibility.1, ?_⟩
  have power_eq :
      (q.natAbs ^ waitExponent waits) ^ 2 =
        q.natAbs ^ (2 * waitExponent waits) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [power_eq] at divisibility
  exact divisibility.2

/-- Prime-support form of `positiveBridge_zero_num_den_dvd_base`: every prime occurring in the
canonical numerator or denominator divides the ReturnSquare base. -/
theorem positiveBridge_zero_fraction_prime_dvd_base
    (q : ℤ) (q_ne : q ≠ 0) (d : ℚ) (d_ne_one : d ≠ 1)
    (waits : List Nat) (bridge_zero : positiveBridge (q : ℚ) (-d) waits = 0)
    (prime : Nat) (prime_spec : prime.Prime)
    (divides_fraction :
      prime ∣ (IsFractionRing.num ℤ d).natAbs ∨
        prime ∣ ((IsFractionRing.den ℤ d : ℤ).natAbs)) :
    prime ∣ q.natAbs := by
  obtain ⟨numerator_dvd, denominator_dvd⟩ :=
    positiveBridge_zero_num_den_dvd_base q q_ne d d_ne_one waits bridge_zero
  rcases divides_fraction with divides_numerator | divides_denominator
  · exact prime_spec.dvd_of_dvd_pow
      (dvd_trans divides_numerator numerator_dvd)
  · exact prime_spec.dvd_of_dvd_pow
      (dvd_trans divides_denominator denominator_dvd)

/-- For any prime dividing an integral ReturnSquare base, a positive parameter valuation at a
vanishing nondegenerate bridge is fixed by the complete proper-tail wait. Consequently every
prime occurring in the canonical numerator occurs to the same tail exponent relative to its
multiplicity in the base. -/
theorem positiveBridge_zero_positive_valuation_eq_tail
    (q : ℤ) (q_ne : q ≠ 0) (prime : Nat) (prime_spec : prime.Prime)
    (prime_dvd : (prime : ℤ) ∣ q) (d : ℚ) (d_ne_one : d ≠ 1)
    (head : Nat) (tail : List Nat)
    (bridge_zero : positiveBridge (q : ℚ) (-d) (head :: tail) = 0)
    (valuation_positive : 0 < padicValRat prime d) :
    tail ≠ [] ∧
      padicValRat prime d =
        waitExponent tail * (padicValInt prime q : ℤ) := by
  let _ : Fact prime.Prime := ⟨prime_spec⟩
  have q_shell :
      HasValue prime (q : ℚ) (padicValInt prime q : ℤ) := by
    refine ⟨?_, padicValRat.of_int⟩
    exact_mod_cast q_ne
  have scale_positive : 0 < (padicValInt prime q : ℤ) := by
    have valuation_ne : padicValInt prime q ≠ 0 := by
      intro valuation_zero
      rcases padicValInt.eq_zero_iff.mp valuation_zero with
        prime_one | q_zero | not_dvd
      · exact prime_spec.ne_one prime_one
      · exact q_ne q_zero
      · exact not_dvd prime_dvd
    exact_mod_cast Nat.pos_of_ne_zero valuation_ne
  have d_ne : d ≠ 0 := by
    intro d_zero
    subst d
    simp at valuation_positive
  have d_shell : HasValue prime d (padicValRat prime d) := ⟨d_ne, rfl⟩
  have normalized_zero : normalizedWaitWord (q : ℚ) d (head :: tail) 0 0 = 0 := by
    rw [positiveBridge_neg_eq_normalizedWaitWord] at bridge_zero
    exact (mul_eq_zero.mp bridge_zero).resolve_left (sub_ne_zero.mpr d_ne_one.symm)
  exact normalizedWord_zero_positive_valuation_eq_tail
    (q : ℚ) d (padicValInt prime q : ℤ) (padicValRat prime d)
    q_shell scale_positive d_shell valuation_positive head tail
    (by simpa [normalizedWaitWord] using normalized_zero)

/-- Positive valuations at two distinct base primes are synchronized: their ratio is the ratio
of the corresponding valuations of the base. -/
theorem positiveBridge_zero_positive_valuations_cross_mul
    (q : ℤ) (q_ne : q ≠ 0)
    (leftPrime rightPrime : Nat)
    (left_prime : leftPrime.Prime) (right_prime : rightPrime.Prime)
    (left_dvd : (leftPrime : ℤ) ∣ q) (right_dvd : (rightPrime : ℤ) ∣ q)
    (d : ℚ) (d_ne_one : d ≠ 1) (head : Nat) (tail : List Nat)
    (bridge_zero : positiveBridge (q : ℚ) (-d) (head :: tail) = 0)
    (left_positive : 0 < padicValRat leftPrime d)
    (right_positive : 0 < padicValRat rightPrime d) :
    padicValRat leftPrime d * (padicValInt rightPrime q : ℤ) =
      padicValRat rightPrime d * (padicValInt leftPrime q : ℤ) := by
  have left_shape :=
    (positiveBridge_zero_positive_valuation_eq_tail
      q q_ne leftPrime left_prime left_dvd d d_ne_one head tail bridge_zero
      left_positive).2
  have right_shape :=
    (positiveBridge_zero_positive_valuation_eq_tail
      q q_ne rightPrime right_prime right_dvd d d_ne_one head tail bridge_zero
      right_positive).2
  rw [left_shape, right_shape]
  ring

end

end MatrixMortality.ReturnSquare
