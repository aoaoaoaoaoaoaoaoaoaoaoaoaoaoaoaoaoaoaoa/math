import MatrixMortality.ReturnSquarePureDenominatorDescent

/-!
# Effective finite certificates for ReturnSquare

The positive-numerator weight certificate and the pure-denominator real descent are assembled
into explicit finite candidate sets.  Exact bridge evaluation on these sets decides mortality;
the exceptional parameter `-1` remains the zero-power one-return resonance.
-/

namespace MatrixMortality.ReturnSquare

private def waitWordsAtMost (bound : Nat) : Nat → Finset (List Nat)
  | 0 => {[]}
  | depth + 1 =>
      waitWordsAtMost bound depth ∪
        (Finset.range bound).biUnion fun head =>
          (waitWordsAtMost bound depth).image fun tail => head :: tail

private theorem mem_waitWordsAtMost_iff
    (bound depth : Nat) (waits : List Nat) :
    waits ∈ waitWordsAtMost bound depth ↔
      waits.length ≤ depth ∧ ∀ wait ∈ waits, wait < bound := by
  induction depth generalizing waits with
  | zero =>
      constructor
      · intro waits_mem
        have waits_eq : waits = [] := by simpa [waitWordsAtMost] using waits_mem
        subst waits
        simp
      · rintro ⟨length_zero, _⟩
        have waits_eq : waits = [] :=
          List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero length_zero)
        subst waits
        simp [waitWordsAtMost]
  | succ depth induction =>
      rw [waitWordsAtMost, Finset.mem_union]
      constructor
      · rintro (shorter | extended)
        · obtain ⟨length_le, entries_lt⟩ := (induction waits).mp shorter
          exact ⟨by omega, entries_lt⟩
        · obtain ⟨head, head_mem, image_mem⟩ := Finset.mem_biUnion.mp extended
          obtain ⟨tail, tail_mem, waits_eq⟩ := Finset.mem_image.mp image_mem
          subst waits
          obtain ⟨tail_length_le, tail_entries_lt⟩ := (induction tail).mp tail_mem
          refine ⟨by simp; omega, ?_⟩
          intro wait wait_mem
          rcases List.mem_cons.mp wait_mem with wait_eq | wait_mem_tail
          · subst wait
            exact Finset.mem_range.mp head_mem
          · exact tail_entries_lt wait wait_mem_tail
      · rintro ⟨length_le, entries_lt⟩
        rcases waits with _ | ⟨head, tail⟩
        · exact Or.inl ((induction []).mpr ⟨by simp, by simp⟩)
        · apply Or.inr
          apply Finset.mem_biUnion.mpr
          refine ⟨head, Finset.mem_range.mpr (entries_lt head (by simp)), ?_⟩
          apply Finset.mem_image.mpr
          refine ⟨tail, (induction tail).mpr ⟨?_, ?_⟩, rfl⟩
          · simp at length_le
            exact length_le
          · intro wait wait_mem
            exact entries_lt wait (by simp [wait_mem])

/-- Lists shorter than `bound` whose entries are all smaller than `bound`. -/
def boundedWaitWords (bound : Nat) (_bound_at_least_two : 1 < bound) :
    Finset (List Nat) :=
  waitWordsAtMost bound (bound - 1)

/-- Extensional specification of the finite bounded-word enumerator. -/
theorem mem_boundedWaitWords_iff
    (bound : Nat) (bound_at_least_two : 1 < bound) (waits : List Nat) :
    waits ∈ boundedWaitWords bound bound_at_least_two ↔
      waits.length < bound ∧ ∀ wait ∈ waits, wait < bound := by
  rw [boundedWaitWords, mem_waitWordsAtMost_iff]
  constructor
  · rintro ⟨length_le, entries_lt⟩
    exact ⟨by omega, entries_lt⟩
  · rintro ⟨length_lt, entries_lt⟩
    exact ⟨by omega, entries_lt⟩

private theorem index_succ_le_pow
    (q n : Nat) (q_at_least_two : 2 ≤ q) :
    n + 1 ≤ q ^ (n + 1) := by
  induction n with
  | zero =>
      simpa using (le_trans (by decide : 1 ≤ 2) q_at_least_two)
  | succ n induction =>
      calc
        n + 1 + 1 ≤ 2 * (n + 1) := by omega
        _ ≤ 2 * q ^ (n + 1) := Nat.mul_le_mul_left 2 induction
        _ ≤ q * q ^ (n + 1) := Nat.mul_le_mul_right (q ^ (n + 1)) q_at_least_two
        _ = q ^ (n + 1) * q := Nat.mul_comm _ _
        _ = q ^ (n + 1 + 1) := (pow_succ q (n + 1)).symm

/-- Exact finite search set for a pure-denominator parameter. -/
def pureDenominatorZeroCandidates
    (q B : Nat) (B_at_least_two : 1 < B) : Finset (List Nat) :=
  (boundedWaitWords B B_at_least_two).filter fun waits =>
    positiveBridge (q : ℚ) (-(1 / (B : ℚ))) waits = 0

/-- Every pure-denominator zero lies in the displayed finite search set. -/
theorem positiveBridge_pureDenominator_zero_mem_candidates
    (q B : Nat) (q_at_least_four : 4 ≤ q) (B_at_least_two : 1 < B)
    (waits : List Nat)
    (bridge_zero : positiveBridge (q : ℚ) (-(1 / (B : ℚ))) waits = 0) :
    waits ∈ pureDenominatorZeroCandidates q B B_at_least_two := by
  have q_at_least_four_rat : (4 : ℚ) ≤ q := by exact_mod_cast q_at_least_four
  have B_at_least_two_rat : (2 : ℚ) ≤ B := by exact_mod_cast B_at_least_two
  have B_ne_one_rat : (B : ℚ) ≠ 1 := by exact_mod_cast B_at_least_two.ne'
  have waits_nonempty : waits ≠ [] := by
    intro waits_empty
    subst waits
    rw [positiveBridge_nil] at bridge_zero
    have B_ne : (B : ℚ) ≠ 0 := by positivity
    apply B_ne_one_rat
    have quotient_one : (1 : ℚ) / B = 1 := by linarith
    exact ((div_eq_one_iff_eq B_ne).mp quotient_one).symm
  obtain ⟨head, tail, waits_eq⟩ := List.exists_cons_of_ne_nil waits_nonempty
  subst waits
  have cost_bound := positiveBridge_pureDenominator_zero_add_cost_le
    (q : ℚ) B q_at_least_four_rat B_at_least_two_rat head tail bridge_zero
  have length_bound := positiveBridge_pureDenominator_zero_length_bound
    (q : ℚ) B q_at_least_four_rat B_at_least_two_rat head tail bridge_zero
  have source_index_le :
      ((head + 1 : Nat) : ℚ) ≤ (q : ℚ) ^ (head + 1) := by
    exact_mod_cast index_succ_le_pow q head (by omega)
  have source_index_le' :
      (head : ℚ) + 1 ≤ (q : ℚ) ^ (head + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using source_index_le
  have source_at_least_four : (4 : ℚ) ≤ (q : ℚ) ^ (head + 1) := by
    have q_nonnegative : (0 : ℚ) ≤ q := by positivity
    have one_le_tail_power : (1 : ℚ) ≤ (q : ℚ) ^ head :=
      one_le_pow₀ (by exact_mod_cast show 1 ≤ q by omega)
    rw [pow_succ]
    nlinarith
  have tail_term_nonnegative :
      0 ≤ (tail.length : ℚ) * ((q : ℚ) - 1) :=
    mul_nonneg (by positivity) (by linarith)
  have head_lt_B : head < B := by
    exact_mod_cast show (head : ℚ) < B by
      linarith [source_index_le', length_bound, tail_term_nonnegative]
  have waits_length_lt_B : (head :: tail).length < B := by
    have q_sub_one_at_least_one : (1 : ℚ) ≤ (q : ℚ) - 1 := by
      linarith [q_at_least_four_rat]
    have tail_length_nonnegative : (0 : ℚ) ≤ tail.length := by positivity
    have cast_length_lt : ((head :: tail).length : ℚ) < B := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      nlinarith
    exact_mod_cast cast_length_lt
  have every_wait_lt_B : ∀ wait ∈ head :: tail, wait < B := by
    intro wait wait_mem
    rcases List.mem_cons.mp wait_mem with wait_eq | wait_mem_tail
    · simpa [wait_eq] using head_lt_B
    · have scale_lt := positiveBridge_pureDenominator_zero_tail_scale_lt
        (q : ℚ) B q_at_least_four_rat B_at_least_two_rat head wait tail
          bridge_zero wait_mem_tail
      have wait_index_le :
          ((wait + 1 : Nat) : ℚ) ≤ (q : ℚ) ^ (wait + 1) := by
        exact_mod_cast index_succ_le_pow q wait (by omega)
      have wait_index_le' :
          (wait : ℚ) + 1 ≤ (q : ℚ) ^ (wait + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using wait_index_le
      exact_mod_cast show (wait : ℚ) < B by linarith [wait_index_le']
  apply Finset.mem_filter.mpr
  exact ⟨(mem_boundedWaitWords_iff B B_at_least_two (head :: tail)).mpr
    ⟨waits_length_lt_B, every_wait_lt_B⟩, bridge_zero⟩

/-- Pure-denominator mortality is exactly nonemptiness of one explicit finite filtered set. -/
theorem exists_positiveBridge_pureDenominator_zero_iff_candidates_nonempty
    (q B : Nat) (q_at_least_four : 4 ≤ q) (B_at_least_two : 1 < B) :
    (∃ waits, positiveBridge (q : ℚ) (-(1 / (B : ℚ))) waits = 0) ↔
      (pureDenominatorZeroCandidates q B B_at_least_two).Nonempty := by
  constructor
  · rintro ⟨waits, bridge_zero⟩
    exact ⟨waits, positiveBridge_pureDenominator_zero_mem_candidates
      q B q_at_least_four B_at_least_two waits bridge_zero⟩
  · rintro ⟨waits, waits_mem⟩
    exact ⟨waits, (Finset.mem_filter.mp waits_mem).2⟩

/-- Integral adjugate tail state for an arbitrary reduced positive fraction `A/B`. -/
def fractionIntegralAdjugateTailState
    (q A B : ℤ) : List Nat → Fin 2 → ℤ
  | [] => ![B, 1]
  | wait :: tail =>
      Matrix.mulVec (fractionPullbackAdjugate A B (q ^ (wait + 1)))
        (fractionIntegralAdjugateTailState q A B tail)

/-- Casting the general integral state recovers the rational adjugate state. -/
theorem cast_fractionIntegralAdjugateTailState
    (q A B : ℤ) (tail : List Nat) :
    (fun index => (fractionIntegralAdjugateTailState q A B tail index : ℚ)) =
      fractionTailPredecessorState (q : ℚ) A B tail := by
  induction tail with
  | nil =>
      ext index
      fin_cases index <;>
        simp [fractionIntegralAdjugateTailState, fractionTailPredecessorState,
          wordProduct]
  | cons wait tail induction =>
      rw [fractionTailPredecessorState, wordProduct_cons, ← Matrix.mulVec_mulVec]
      change
        (fun index =>
          (fractionIntegralAdjugateTailState q A B (wait :: tail) index : ℚ)) =
          Matrix.mulVec
            (fractionPullbackAdjugate (A : ℚ) B ((q : ℚ) ^ (wait + 1)))
            (fractionTailPredecessorState (q : ℚ) A B tail)
      rw [← induction]
      ext index
      fin_cases index <;>
        simp [fractionIntegralAdjugateTailState, fractionPullbackAdjugate,
          Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- A nondegenerate general integral adjugate word cannot kill its terminal state. -/
theorem fractionIntegralAdjugateTailState_ne_zero
    (q A B : ℤ) (q_at_least_two : 2 ≤ q) (B_ne : B ≠ 0)
    (B_sub_A_ne : B - A ≠ 0) (tail : List Nat) :
    fractionIntegralAdjugateTailState q A B tail ≠ 0 := by
  have q_ne : q ≠ 0 := by omega
  have q_ne_rat : (q : ℚ) ≠ 0 := by exact_mod_cast q_ne
  have B_ne_rat : (B : ℚ) ≠ 0 := by exact_mod_cast B_ne
  have B_sub_A_ne_rat : (B : ℚ) - A ≠ 0 := by exact_mod_cast B_sub_A_ne
  have tail_word_unit :
      IsUnit (wordProduct
        (fun wait =>
          fractionPullbackAdjugate (A : ℚ) B ((q : ℚ) ^ (wait + 1))) tail) := by
    apply wordProduct_isUnit
    intro wait
    apply (fractionPullbackAdjugate (A : ℚ) B
      ((q : ℚ) ^ (wait + 1))).isUnit_iff_isUnit_det.mpr
    rw [fractionPullbackAdjugate_det]
    apply isUnit_iff_ne_zero.mpr
    have q_gt_one : (1 : ℚ) < q := by exact_mod_cast show (1 : ℤ) < q by omega
    have scale_gt_one : (1 : ℚ) < (q : ℚ) ^ (wait + 1) :=
      one_lt_pow₀ q_gt_one (Nat.succ_ne_zero wait)
    have scale_sq_ne : ((q : ℚ) ^ (wait + 1)) ^ 2 - 1 ≠ 0 := by
      nlinarith [sq_nonneg ((q : ℚ) ^ (wait + 1) - 1)]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero B_ne_rat B_sub_A_ne_rat)
        (pow_ne_zero (wait + 1) q_ne_rat)) scale_sq_ne
  have terminal_ne : (![B, 1] : Fin 2 → ℚ) ≠ 0 := by
    intro terminal_zero
    have second_zero := congrFun terminal_zero 1
    norm_num at second_zero
  have rational_state_ne :
      fractionTailPredecessorState (q : ℚ) A B tail ≠ 0 := by
    exact unit_mulVec_ne_zero tail_word_unit terminal_ne
  intro integral_zero
  apply rational_state_ne
  rw [← cast_fractionIntegralAdjugateTailState q A B tail]
  funext index
  rw [congrFun integral_zero index]
  norm_num

private theorem length_le_waitExponent (tail : List Nat) :
    tail.length ≤ waitExponent tail := by
  induction tail with
  | nil => simp [waitExponent]
  | cons wait tail induction =>
      simp only [List.length_cons, waitExponent]
      omega

private theorem wait_succ_le_waitExponent_of_mem
    (wait : Nat) (tail : List Nat) (wait_mem : wait ∈ tail) :
    wait + 1 ≤ waitExponent tail := by
  induction tail with
  | nil => simp at wait_mem
  | cons first tail induction =>
      rcases List.mem_cons.mp wait_mem with wait_eq | wait_mem_tail
      · subst first
        simp [waitExponent]
      · have tail_bound := induction wait_mem_tail
        simp only [waitExponent]
        omega

/-- Fixed-weight tails, followed by every head smaller than the integral upper adjugate
coordinate, form the complete positive-numerator search space. -/
def positiveNumeratorSearchSpace
    (q A B : Nat) (weight : Nat) (weight_positive : 0 < weight) :
    Finset (List Nat) :=
  ((boundedWaitWords (weight + 1) (by omega)).filter fun tail =>
      waitExponent tail = weight).biUnion fun tail =>
    (Finset.range
      (fractionIntegralAdjugateTailState q A B tail 0).natAbs).image fun head =>
        head :: tail

/-- Exact bridge zeros inside the finite positive-numerator search space. -/
def positiveNumeratorZeroCandidates
    (q A B : Nat) (weight : Nat) (weight_positive : 0 < weight) :
    Finset (List Nat) :=
  (positiveNumeratorSearchSpace q A B weight weight_positive).filter fun waits =>
    positiveBridge (q : ℚ) (-((A : ℚ) / B)) waits = 0

/-- Every bridge zero with a positive numerator valuation lies in the fixed-weight candidate
set, with its head bounded by the exact upper integral adjugate coordinate. -/
theorem positiveBridge_positiveNumerator_zero_mem_candidates
    (q A B : Nat) (q_at_least_two : 2 ≤ q) (A_positive : 0 < A)
    (B_positive : 0 < B) (A_ne_B : A ≠ B)
    (prime : Nat) (prime_spec : prime.Prime) (prime_dvd_q : prime ∣ q)
    (weight : Nat) (weight_positive : 0 < weight)
    (valuation_positive : 0 < padicValRat prime ((A : ℚ) / B))
    (valuation_shape :
      padicValRat prime ((A : ℚ) / B) =
        (weight : ℤ) * (padicValInt prime (q : ℤ) : ℤ))
    (waits : List Nat)
    (bridge_zero : positiveBridge (q : ℚ) (-((A : ℚ) / B)) waits = 0) :
    waits ∈ positiveNumeratorZeroCandidates q A B weight weight_positive := by
  have q_ne_int : (q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < q))
  have prime_dvd_q_int : (prime : ℤ) ∣ (q : ℤ) := by exact_mod_cast prime_dvd_q
  have B_ne_rat : (B : ℚ) ≠ 0 := by positivity
  have B_sub_A_ne_rat : (B : ℚ) - A ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast A_ne_B.symm)
  have fraction_ne_one : (A : ℚ) / B ≠ 1 := by
    intro fraction_one
    apply A_ne_B
    exact_mod_cast (div_eq_one_iff_eq B_ne_rat).mp fraction_one
  have waits_nonempty : waits ≠ [] := by
    intro waits_empty
    subst waits
    rw [positiveBridge_nil] at bridge_zero
    apply fraction_ne_one
    linarith
  obtain ⟨head, tail, waits_eq⟩ := List.exists_cons_of_ne_nil waits_nonempty
  subst waits
  obtain ⟨tail_nonempty, tail_weight, incidence⟩ :=
    positiveBridge_fraction_zero_positive_valuation_tail_certificate
      (q : ℤ) q_ne_int prime prime_spec prime_dvd_q_int
      (A : ℚ) B B_ne_rat B_sub_A_ne_rat fraction_ne_one
      head weight tail bridge_zero valuation_positive
      (by
        have valuation_ne : padicValInt prime (q : ℤ) ≠ 0 := by
          intro valuation_zero
          rcases padicValInt.eq_zero_iff.mp valuation_zero with
            prime_one | q_zero | not_dvd
          · exact prime_spec.ne_one prime_one
          · exact q_ne_int q_zero
          · exact not_dvd prime_dvd_q_int
        exact_mod_cast Nat.pos_of_ne_zero valuation_ne)
      valuation_shape
  have tail_length_lt : tail.length < weight + 1 := by
    have length_le := length_le_waitExponent tail
    rw [tail_weight] at length_le
    omega
  have tail_entries_lt : ∀ wait ∈ tail, wait < weight + 1 := by
    intro wait wait_mem
    have wait_le := wait_succ_le_waitExponent_of_mem wait tail wait_mem
    rw [tail_weight] at wait_le
    omega
  have tail_mem_bounded :
      tail ∈ boundedWaitWords (weight + 1) (by omega) :=
    (mem_boundedWaitWords_iff (weight + 1) (by omega) tail).mpr
      ⟨tail_length_lt, tail_entries_lt⟩
  have tail_mem_weighted :
      tail ∈ (boundedWaitWords (weight + 1) (by omega)).filter fun candidate =>
        waitExponent candidate = weight :=
    Finset.mem_filter.mpr ⟨tail_mem_bounded, tail_weight⟩
  have cast_state := cast_fractionIntegralAdjugateTailState
    (q : ℤ) A B tail
  have incidence_int :
      fractionIntegralAdjugateTailState q A B tail 0 =
        (A : ℤ) * (q : ℤ) ^ (head + 1) *
          fractionIntegralAdjugateTailState q A B tail 1 := by
    change
      fractionTailPredecessorState ((q : ℤ) : ℚ) ((A : ℤ) : ℚ) ((B : ℤ) : ℚ)
          tail 0 =
        ((A : ℤ) : ℚ) * ((q : ℤ) : ℚ) ^ (head + 1) *
          fractionTailPredecessorState ((q : ℤ) : ℚ) ((A : ℤ) : ℚ) ((B : ℤ) : ℚ)
            tail 1 at incidence
    have incidence_zero := congrFun cast_state 0
    have incidence_one := congrFun cast_state 1
    rw [← incidence_zero, ← incidence_one] at incidence
    exact_mod_cast incidence
  have B_ne_int : (B : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt B_positive
  have B_sub_A_ne_int : (B : ℤ) - A ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast A_ne_B.symm)
  have state_ne := fractionIntegralAdjugateTailState_ne_zero
    q A B (by exact_mod_cast q_at_least_two) B_ne_int B_sub_A_ne_int tail
  have lower_ne : fractionIntegralAdjugateTailState q A B tail 1 ≠ 0 := by
    intro lower_zero
    apply state_ne
    funext index
    fin_cases index
    · change fractionIntegralAdjugateTailState q A B tail 0 = 0
      rw [incidence_int, lower_zero, mul_zero]
    · change fractionIntegralAdjugateTailState q A B tail 1 = 0
      exact lower_zero
  have upper_ne : fractionIntegralAdjugateTailState q A B tail 0 ≠ 0 := by
    rw [incidence_int]
    exact mul_ne_zero
      (mul_ne_zero (by exact_mod_cast Nat.ne_of_gt A_positive)
        (pow_ne_zero (head + 1) (by exact_mod_cast Nat.ne_of_gt (by omega : 0 < q))))
      lower_ne
  have source_power_dvd_upper :
      (q : ℤ) ^ (head + 1) ∣
        fractionIntegralAdjugateTailState q A B tail 0 := by
    refine ⟨(A : ℤ) * fractionIntegralAdjugateTailState q A B tail 1, ?_⟩
    rw [incidence_int]
    ring
  have source_power_dvd_upper_abs :
      q ^ (head + 1) ∣
        (fractionIntegralAdjugateTailState q A B tail 0).natAbs := by
    exact Int.natAbs_dvd_natAbs.mpr source_power_dvd_upper
  have upper_abs_positive :
      0 < (fractionIntegralAdjugateTailState q A B tail 0).natAbs :=
    Int.natAbs_pos.mpr upper_ne
  have source_power_le_upper_abs :
      q ^ (head + 1) ≤
        (fractionIntegralAdjugateTailState q A B tail 0).natAbs :=
    Nat.le_of_dvd upper_abs_positive source_power_dvd_upper_abs
  have head_lt_upper_abs :
      head < (fractionIntegralAdjugateTailState q A B tail 0).natAbs := by
    have head_succ_le := index_succ_le_pow q head q_at_least_two
    omega
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_biUnion.mpr ⟨tail, tail_mem_weighted, ?_⟩, bridge_zero⟩
  exact Finset.mem_image.mpr ⟨head, Finset.mem_range.mpr head_lt_upper_abs, rfl⟩

/-- Positive-numerator bridge mortality is exactly nonemptiness of one explicit finite filtered
set once any positive base-prime valuation supplies its fixed tail weight. -/
theorem exists_positiveBridge_positiveNumerator_zero_iff_candidates_nonempty
    (q A B : Nat) (q_at_least_two : 2 ≤ q) (A_positive : 0 < A)
    (B_positive : 0 < B) (A_ne_B : A ≠ B)
    (prime : Nat) (prime_spec : prime.Prime) (prime_dvd_q : prime ∣ q)
    (weight : Nat) (weight_positive : 0 < weight)
    (valuation_positive : 0 < padicValRat prime ((A : ℚ) / B))
    (valuation_shape :
      padicValRat prime ((A : ℚ) / B) =
        (weight : ℤ) * (padicValInt prime (q : ℤ) : ℤ)) :
    (∃ waits, positiveBridge (q : ℚ) (-((A : ℚ) / B)) waits = 0) ↔
      (positiveNumeratorZeroCandidates q A B weight weight_positive).Nonempty := by
  constructor
  · rintro ⟨waits, bridge_zero⟩
    exact ⟨waits, positiveBridge_positiveNumerator_zero_mem_candidates
      q A B q_at_least_two A_positive B_positive A_ne_B
      prime prime_spec prime_dvd_q weight weight_positive
      valuation_positive valuation_shape waits bridge_zero⟩
  · rintro ⟨waits, waits_mem⟩
    exact ⟨waits, (Finset.mem_filter.mp waits_mem).2⟩

/-- Union of the finitely many arithmetically possible positive-numerator weight chambers. The
valuation equation leaves at most one nonempty chamber. -/
def positiveNumeratorAllZeroCandidates
    (q A B prime : Nat) : Finset (List Nat) :=
  (Finset.range (padicValRat prime ((A : ℚ) / B)).natAbs.succ).biUnion fun weight =>
    if weight_positive : 0 < weight then
      if _valuation_shape :
          padicValRat prime ((A : ℚ) / B) =
            (weight : ℤ) * (padicValInt prime (q : ℤ) : ℤ) then
        positiveNumeratorZeroCandidates q A B weight weight_positive
      else ∅
    else ∅

/-- A prime divisor of a reduced positive numerator gives a strictly positive rational
valuation. -/
theorem reducedPositiveFraction_valuation_positive
    (A B prime : Nat) (A_positive : 0 < A) (B_positive : 0 < B)
    (coprime : A.Coprime B) (prime_spec : prime.Prime) (prime_dvd_A : prime ∣ A) :
    0 < padicValRat prime ((A : ℚ) / B) := by
  let _ : Fact prime.Prime := ⟨prime_spec⟩
  have A_ne_rat : (A : ℚ) ≠ 0 := by positivity
  have B_ne_rat : (B : ℚ) ≠ 0 := by positivity
  have prime_not_dvd_B : ¬prime ∣ B :=
    prime_spec.coprime_iff_not_dvd.mp
      (Nat.Coprime.coprime_dvd_left prime_dvd_A coprime)
  have numerator_valuation_positive : 0 < padicValNat prime A := by
    have valuation_ne : padicValNat prime A ≠ 0 := by
      intro valuation_zero
      rcases padicValNat.eq_zero_iff.mp valuation_zero with
        prime_one | numerator_zero | prime_not_dvd_A
      · exact prime_spec.ne_one prime_one
      · exact (Nat.ne_of_gt A_positive) numerator_zero
      · exact prime_not_dvd_A prime_dvd_A
    exact Nat.pos_of_ne_zero valuation_ne
  have denominator_valuation_zero : padicValNat prime B = 0 :=
    padicValNat.eq_zero_of_not_dvd prime_not_dvd_B
  rw [padicValRat.div A_ne_rat B_ne_rat, padicValRat.of_nat, padicValRat.of_nat,
    denominator_valuation_zero]
  have cast_positive : (0 : ℤ) < (padicValNat prime A : ℤ) := by
    exact_mod_cast numerator_valuation_positive
  simpa using cast_positive

/-- A reduced numerator prime outside the base support excludes every bridge zero. -/
theorem not_exists_positiveBridge_zero_of_numerator_prime_not_dvd_base
    (q A B prime : Nat) (q_at_least_two : 2 ≤ q)
    (_A_positive : 0 < A) (B_positive : 0 < B) (A_ne_B : A ≠ B)
    (coprime : A.Coprime B) (prime_spec : prime.Prime)
    (prime_dvd_A : prime ∣ A) (prime_not_dvd_q : ¬prime ∣ q) :
    ¬∃ waits, positiveBridge (q : ℚ) (-((A : ℚ) / B)) waits = 0 := by
  rintro ⟨waits, bridge_zero⟩
  have q_ne_int : (q : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (by omega : 0 < q)
  have B_ne_int : (0 : ℤ) < B := by exact_mod_cast B_positive
  have coprime_int : Nat.Coprime (A : ℤ).natAbs (B : ℤ).natAbs := by
    simpa using coprime
  have rational_numerator_eq : ((A : ℚ) / B).num = (A : ℤ) := by
    exact Rat.num_div_eq_of_coprime B_ne_int coprime_int
  have canonical_numerator_abs_eq :
      (IsFractionRing.num ℤ ((A : ℚ) / B)).natAbs = A := by
    have associated := Rat.isFractionRingNum ((A : ℚ) / B)
    rw [Int.associated_iff_natAbs, rational_numerator_eq] at associated
    simpa using associated
  have fraction_ne_one : (A : ℚ) / B ≠ 1 := by
    intro fraction_one
    apply A_ne_B
    have B_ne_rat : (B : ℚ) ≠ 0 := by positivity
    exact_mod_cast (div_eq_one_iff_eq B_ne_rat).mp fraction_one
  have prime_dvd_base := positiveBridge_zero_fraction_prime_dvd_base
    (q : ℤ) q_ne_int ((A : ℚ) / B) fraction_ne_one waits bridge_zero
    prime prime_spec (Or.inl (by simpa [canonical_numerator_abs_eq] using prime_dvd_A))
  exact prime_not_dvd_q (by exact_mod_cast prime_dvd_base)

/-- Every bridge zero with one positive base-prime valuation lies in the finite union over all
arithmetically possible tail weights. -/
theorem positiveBridge_positiveNumerator_zero_mem_all_candidates
    (q A B : Nat) (q_at_least_two : 2 ≤ q) (A_positive : 0 < A)
    (B_positive : 0 < B) (A_ne_B : A ≠ B)
    (prime : Nat) (prime_spec : prime.Prime) (prime_dvd_q : prime ∣ q)
    (valuation_positive : 0 < padicValRat prime ((A : ℚ) / B))
    (waits : List Nat)
    (bridge_zero : positiveBridge (q : ℚ) (-((A : ℚ) / B)) waits = 0) :
    waits ∈ positiveNumeratorAllZeroCandidates q A B prime := by
  have q_ne_int : (q : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (by omega : 0 < q)
  have prime_dvd_q_int : (prime : ℤ) ∣ (q : ℤ) := by exact_mod_cast prime_dvd_q
  have B_ne_rat : (B : ℚ) ≠ 0 := by positivity
  have fraction_ne_one : (A : ℚ) / B ≠ 1 := by
    intro fraction_one
    apply A_ne_B
    exact_mod_cast (div_eq_one_iff_eq B_ne_rat).mp fraction_one
  have waits_nonempty : waits ≠ [] := by
    intro waits_empty
    subst waits
    rw [positiveBridge_nil] at bridge_zero
    apply fraction_ne_one
    linarith
  obtain ⟨head, tail, waits_eq⟩ := List.exists_cons_of_ne_nil waits_nonempty
  subst waits
  obtain ⟨tail_nonempty, valuation_shape⟩ :=
    positiveBridge_zero_positive_valuation_eq_tail
      (q : ℤ) q_ne_int prime prime_spec prime_dvd_q_int
      ((A : ℚ) / B) fraction_ne_one head tail bridge_zero valuation_positive
  have weight_positive : 0 < waitExponent tail := by
    obtain ⟨first, rest, tail_eq⟩ := List.exists_cons_of_ne_nil tail_nonempty
    subst tail
    simp [waitExponent]
  have base_valuation_positive :
      0 < (padicValInt prime (q : ℤ) : ℤ) := by
    have valuation_ne : padicValInt prime (q : ℤ) ≠ 0 := by
      intro valuation_zero
      rcases padicValInt.eq_zero_iff.mp valuation_zero with
        prime_one | q_zero | not_dvd
      · exact prime_spec.ne_one prime_one
      · exact q_ne_int q_zero
      · exact not_dvd prime_dvd_q_int
    exact_mod_cast Nat.pos_of_ne_zero valuation_ne
  have weight_le_value :
      (waitExponent tail : ℤ) ≤ padicValRat prime ((A : ℚ) / B) := by
    rw [valuation_shape]
    have weight_nonnegative : (0 : ℤ) ≤ waitExponent tail := by positivity
    nlinarith
  have weight_le_value_abs :
      waitExponent tail ≤ (padicValRat prime ((A : ℚ) / B)).natAbs := by
    have cast_bound :
        (waitExponent tail : ℤ) ≤
          ((padicValRat prime ((A : ℚ) / B)).natAbs : ℤ) := by
      rw [Int.natAbs_of_nonneg valuation_positive.le]
      exact weight_le_value
    exact_mod_cast cast_bound
  have candidate_mem := positiveBridge_positiveNumerator_zero_mem_candidates
    q A B q_at_least_two A_positive B_positive A_ne_B
    prime prime_spec prime_dvd_q (waitExponent tail) weight_positive
    valuation_positive valuation_shape (head :: tail) bridge_zero
  rw [positiveNumeratorAllZeroCandidates]
  refine Finset.mem_biUnion.mpr ⟨waitExponent tail, ?_, ?_⟩
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le weight_le_value_abs)
  · simp only [dif_pos weight_positive, dif_pos valuation_shape]
    exact candidate_mem

/-- Positive-numerator bridge mortality is exactly nonemptiness of the finite union over all
valuation-compatible tail weights. -/
theorem exists_positiveBridge_positiveNumerator_zero_iff_all_candidates_nonempty
    (q A B : Nat) (q_at_least_two : 2 ≤ q) (A_positive : 0 < A)
    (B_positive : 0 < B) (A_ne_B : A ≠ B)
    (prime : Nat) (prime_spec : prime.Prime) (prime_dvd_q : prime ∣ q)
    (valuation_positive : 0 < padicValRat prime ((A : ℚ) / B)) :
    (∃ waits, positiveBridge (q : ℚ) (-((A : ℚ) / B)) waits = 0) ↔
      (positiveNumeratorAllZeroCandidates q A B prime).Nonempty := by
  constructor
  · rintro ⟨waits, bridge_zero⟩
    exact ⟨waits, positiveBridge_positiveNumerator_zero_mem_all_candidates
      q A B q_at_least_two A_positive B_positive A_ne_B
      prime prime_spec prime_dvd_q valuation_positive waits bridge_zero⟩
  · rintro ⟨waits, waits_mem⟩
    rw [positiveNumeratorAllZeroCandidates] at waits_mem
    obtain ⟨weight, _, weight_mem⟩ := Finset.mem_biUnion.mp waits_mem
    by_cases weight_positive : 0 < weight
    · simp only [dif_pos weight_positive] at weight_mem
      by_cases valuation_shape :
          padicValRat prime ((A : ℚ) / B) =
            (weight : ℤ) * (padicValInt prime (q : ℤ) : ℤ)
      · simp only [dif_pos valuation_shape] at weight_mem
        exact ⟨waits, (Finset.mem_filter.mp weight_mem).2⟩
      · simp only [dif_neg valuation_shape] at weight_mem
        simp at weight_mem
    · simp only [dif_neg weight_positive] at weight_mem
      simp at weight_mem

/-- The parameter `-1` is the exact zero-power resonance; its empty bridge already vanishes. -/
theorem exists_positiveBridge_neg_one_zero (q : ℚ) :
    ∃ waits, positiveBridge q (-1) waits = 0 := by
  exact ⟨[], by simp [positiveBridge_nil]⟩

/-- Pure-denominator physical mortality is decided by the explicit bounded candidate set. -/
theorem physical_isMortal_pureDenominator_iff_candidates_nonempty
    (q B : Nat) (q_at_least_four : 4 ≤ q) (B_at_least_two : 1 < B) :
    IsMortal
        (ReturnFamily.pairGenerator (ambient (q : ℚ))
          (cut (-(1 / (B : ℚ))))) ↔
      (pureDenominatorZeroCandidates q B B_at_least_two).Nonempty := by
  have q_ne_int : (q : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (by omega : 0 < q)
  have B_ne_rat : (B : ℚ) ≠ 0 := by positivity
  have parameter_ne_neg_one : -(1 / (B : ℚ)) + 1 ≠ 0 := by
    intro parameter_zero
    have quotient_one : (1 : ℚ) / B = 1 := by linarith
    have B_eq_one : (B : ℚ) = 1 := ((div_eq_one_iff_eq B_ne_rat).mp quotient_one).symm
    exact (by exact_mod_cast B_at_least_two.ne' : (B : ℚ) ≠ 1) B_eq_one
  change
    IsMortal
        (ReturnFamily.pairGenerator (ambient (((q : ℤ) : ℚ)))
          (cut (-(1 / (B : ℚ))))) ↔
      (pureDenominatorZeroCandidates q B B_at_least_two).Nonempty
  rw [physical_isMortal_iff_positiveBridge
    (q : ℤ) (-(1 / (B : ℚ))) q_ne_int]
  exact exists_positiveBridge_pureDenominator_zero_iff_candidates_nonempty
    q B q_at_least_four B_at_least_two

/-- The pure-denominator ReturnSquare instance has a decision procedure which evaluates only
the finite displayed candidate set. -/
def physicalPureDenominatorDecidable
    (q B : Nat) (q_at_least_four : 4 ≤ q) (B_at_least_two : 1 < B) :
    Decidable
      (IsMortal
        (ReturnFamily.pairGenerator (ambient (q : ℚ))
          (cut (-(1 / (B : ℚ)))))) :=
  decidable_of_iff
    (pureDenominatorZeroCandidates q B B_at_least_two).Nonempty
    (physical_isMortal_pureDenominator_iff_candidates_nonempty
      q B q_at_least_four B_at_least_two).symm

/-- A positive-numerator physical instance is decided by the fixed-weight candidate set. -/
theorem physical_isMortal_positiveNumerator_iff_candidates_nonempty
    (q A B : Nat) (q_at_least_two : 2 ≤ q) (A_positive : 0 < A)
    (B_positive : 0 < B) (A_ne_B : A ≠ B)
    (prime : Nat) (prime_spec : prime.Prime) (prime_dvd_q : prime ∣ q)
    (weight : Nat) (weight_positive : 0 < weight)
    (valuation_positive : 0 < padicValRat prime ((A : ℚ) / B))
    (valuation_shape :
      padicValRat prime ((A : ℚ) / B) =
        (weight : ℤ) * (padicValInt prime (q : ℤ) : ℤ)) :
    IsMortal
        (ReturnFamily.pairGenerator (ambient (q : ℚ))
          (cut (-((A : ℚ) / B)))) ↔
      (positiveNumeratorZeroCandidates q A B weight weight_positive).Nonempty := by
  have q_ne_int : (q : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (by omega : 0 < q)
  have B_ne_rat : (B : ℚ) ≠ 0 := by positivity
  have parameter_ne_neg_one : -((A : ℚ) / B) + 1 ≠ 0 := by
    intro parameter_zero
    apply A_ne_B
    have fraction_one : (A : ℚ) / B = 1 := by linarith
    exact_mod_cast (div_eq_one_iff_eq B_ne_rat).mp fraction_one
  change
    IsMortal
        (ReturnFamily.pairGenerator (ambient (((q : ℤ) : ℚ)))
          (cut (-((A : ℚ) / B)))) ↔
      (positiveNumeratorZeroCandidates q A B weight weight_positive).Nonempty
  rw [physical_isMortal_iff_positiveBridge
    (q : ℤ) (-((A : ℚ) / B)) q_ne_int]
  exact exists_positiveBridge_positiveNumerator_zero_iff_candidates_nonempty
    q A B q_at_least_two A_positive B_positive A_ne_B
    prime prime_spec prime_dvd_q weight weight_positive
    valuation_positive valuation_shape

/-- The positive-numerator ReturnSquare instance has a decision procedure which enumerates
only fixed-weight tails and their exact integral head bounds. -/
def physicalPositiveNumeratorDecidable
    (q A B : Nat) (q_at_least_two : 2 ≤ q) (A_positive : 0 < A)
    (B_positive : 0 < B) (A_ne_B : A ≠ B)
    (prime : Nat) (prime_spec : prime.Prime) (prime_dvd_q : prime ∣ q)
    (weight : Nat) (weight_positive : 0 < weight)
    (valuation_positive : 0 < padicValRat prime ((A : ℚ) / B))
    (valuation_shape :
      padicValRat prime ((A : ℚ) / B) =
        (weight : ℤ) * (padicValInt prime (q : ℤ) : ℤ)) :
    Decidable
      (IsMortal
        (ReturnFamily.pairGenerator (ambient (q : ℚ))
          (cut (-((A : ℚ) / B))))) :=
  decidable_of_iff
    (positiveNumeratorZeroCandidates q A B weight weight_positive).Nonempty
    (physical_isMortal_positiveNumerator_iff_candidates_nonempty
      q A B q_at_least_two A_positive B_positive A_ne_B
      prime prime_spec prime_dvd_q weight weight_positive
      valuation_positive valuation_shape).symm

/-- After prime-support preprocessing, every positive-numerator physical instance is decided by
one finite union whose range is computed directly from the parameter valuation. -/
theorem physical_isMortal_positiveNumerator_iff_all_candidates_nonempty
    (q A B : Nat) (q_at_least_two : 2 ≤ q) (A_positive : 0 < A)
    (B_positive : 0 < B) (A_ne_B : A ≠ B)
    (prime : Nat) (prime_spec : prime.Prime) (prime_dvd_q : prime ∣ q)
    (valuation_positive : 0 < padicValRat prime ((A : ℚ) / B)) :
    IsMortal
        (ReturnFamily.pairGenerator (ambient (q : ℚ))
          (cut (-((A : ℚ) / B)))) ↔
      (positiveNumeratorAllZeroCandidates q A B prime).Nonempty := by
  have q_ne_int : (q : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (by omega : 0 < q)
  have B_ne_rat : (B : ℚ) ≠ 0 := by positivity
  have parameter_ne_neg_one : -((A : ℚ) / B) + 1 ≠ 0 := by
    intro parameter_zero
    apply A_ne_B
    have fraction_one : (A : ℚ) / B = 1 := by linarith
    exact_mod_cast (div_eq_one_iff_eq B_ne_rat).mp fraction_one
  change
    IsMortal
        (ReturnFamily.pairGenerator (ambient (((q : ℤ) : ℚ)))
          (cut (-((A : ℚ) / B)))) ↔
      (positiveNumeratorAllZeroCandidates q A B prime).Nonempty
  rw [physical_isMortal_iff_positiveBridge
    (q : ℤ) (-((A : ℚ) / B)) q_ne_int]
  exact exists_positiveBridge_positiveNumerator_zero_iff_all_candidates_nonempty
    q A B q_at_least_two A_positive B_positive A_ne_B
    prime prime_spec prime_dvd_q valuation_positive

/-- Effective decision procedure for every prime-supported positive-numerator ReturnSquare
instance. -/
def physicalPositiveNumeratorAllDecidable
    (q A B : Nat) (q_at_least_two : 2 ≤ q) (A_positive : 0 < A)
    (B_positive : 0 < B) (A_ne_B : A ≠ B)
    (prime : Nat) (prime_spec : prime.Prime) (prime_dvd_q : prime ∣ q)
    (valuation_positive : 0 < padicValRat prime ((A : ℚ) / B)) :
    Decidable
      (IsMortal
        (ReturnFamily.pairGenerator (ambient (q : ℚ))
          (cut (-((A : ℚ) / B))))) :=
  decidable_of_iff
    (positiveNumeratorAllZeroCandidates q A B prime).Nonempty
    (physical_isMortal_positiveNumerator_iff_all_candidates_nonempty
      q A B q_at_least_two A_positive B_positive A_ne_B
      prime prime_spec prime_dvd_q valuation_positive).symm

/-- Uniform decision procedure for every reduced positive rational ReturnSquare parameter at
base at least four. The numerator-one branch uses global real descent, a supported numerator
prime uses the fixed-weight adjugate search, and an unsupported numerator prime is rejected by
the rational-root support theorem. -/
def physicalPositiveFractionDecidable
    (q A B : Nat) (q_at_least_four : 4 ≤ q)
    (A_positive : 0 < A) (B_positive : 0 < B) (coprime : A.Coprime B) :
    Decidable
      (IsMortal
        (ReturnFamily.pairGenerator (ambient (q : ℚ))
          (cut (-((A : ℚ) / B))))) := by
  by_cases A_one : A = 1
  · subst A
    by_cases B_one : B = 1
    · subst B
      exact isTrue (by
        simpa using physical_isMortal_of_resonance (q : ℤ)
          (by exact_mod_cast show 2 ≤ q by omega) 0)
    · have B_at_least_two : 1 < B := by omega
      exact physicalPureDenominatorDecidable q B q_at_least_four B_at_least_two
  · have A_at_least_two : 2 ≤ A := by omega
    have A_ne_B : A ≠ B := by
      intro A_eq_B
      subst B
      have A_eq_one : A = 1 := by simpa using coprime
      exact A_one A_eq_one
    let prime := A.minFac
    have prime_spec : prime.Prime := Nat.minFac_prime A_one
    have prime_dvd_A : prime ∣ A := Nat.minFac_dvd A
    by_cases prime_dvd_q : prime ∣ q
    · have valuation_positive := reducedPositiveFraction_valuation_positive
        A B prime A_positive B_positive coprime prime_spec prime_dvd_A
      exact physicalPositiveNumeratorAllDecidable
        q A B (by omega) A_positive B_positive A_ne_B
        prime prime_spec prime_dvd_q valuation_positive
    · apply isFalse
      intro mortal
      have q_ne_int : (q : ℤ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt (by omega : 0 < q)
      have B_ne_rat : (B : ℚ) ≠ 0 := by positivity
      have parameter_ne_neg_one : -((A : ℚ) / B) + 1 ≠ 0 := by
        intro parameter_zero
        apply A_ne_B
        have fraction_one : (A : ℚ) / B = 1 := by linarith
        exact_mod_cast (div_eq_one_iff_eq B_ne_rat).mp fraction_one
      have bridge_exists :
          ∃ waits, positiveBridge (q : ℚ) (-((A : ℚ) / B)) waits = 0 := by
        have equivalence := physical_isMortal_iff_positiveBridge
          (q : ℤ) (-((A : ℚ) / B)) q_ne_int
        apply equivalence.mp
        simpa using mortal
      exact not_exists_positiveBridge_zero_of_numerator_prime_not_dvd_base
        q A B prime (by omega) A_positive B_positive A_ne_B coprime
        prime_spec prime_dvd_A prime_dvd_q bridge_exists

/-- The exceptional parameter `-1` is handled exactly as the zero-power resonance. -/
theorem physical_isMortal_neg_one_resonance
    (q : Nat) (q_at_least_two : 2 ≤ q) :
    IsMortal
      (ReturnFamily.pairGenerator (ambient (q : ℚ)) (cut (-1))) := by
  simpa using physical_isMortal_of_resonance (q : ℤ)
    (by exact_mod_cast q_at_least_two) 0

end MatrixMortality.ReturnSquare
