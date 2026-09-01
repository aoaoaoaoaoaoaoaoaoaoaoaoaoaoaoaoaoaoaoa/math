import MatrixMortality.ParabolicFirstBOneRun
import MatrixMortality.ParabolicWaitBounds

/-!
# Physical reduction to the x=211 valuation-density funnel

The exact core equation and the native first- and last-`b` decompositions supply the density
envelope consumed by `ParabolicFirstBOneFunnel`. Composing that envelope with the run and
position extinctions, finite classifier, and terminal certificate leaves only the inner-wait
bound as an upstream obligation.
-/

namespace MatrixMortality.ParabolicBlade

private theorem tagEncode_length_le (body : List TagLetter) :
    body.length ≤ (tagEncode 3 body).length := by
  induction body with
  | nil => simp
  | cons first tail induction =>
      cases first <;>
        simp only [tagEncode_cons, tagCode, List.length_append,
          List.length_cons, List.length_nil, List.length_replicate] <;>
        omega

private theorem firstBOneX211_first_b_index_le_last_b_index
    (j h : Nat) (stem rest : List TagLetter)
    (decomposition :
      List.replicate j .c ++ .b :: rest = stem ++ .b :: List.replicate h .c) :
    j ≤ stem.length := by
  by_contra index_not_bounded
  have stem_lt : stem.length < j := by omega
  have indexed_letter :=
    congrArg (fun word : List TagLetter => word[j]?) decomposition
  rw [List.getElem?_append_right stem_lt.le] at indexed_letter
  have difference_positive : 0 < j - stem.length := Nat.sub_pos_of_lt stem_lt
  have difference_ne : j - stem.length ≠ 0 := difference_positive.ne'
  obtain ⟨q, difference_eq⟩ := Nat.exists_eq_succ_of_ne_zero difference_ne
  rw [difference_eq, List.getElem?_cons_succ, List.getElem?_replicate] at indexed_letter
  split at indexed_letter
  · simp at indexed_letter
  · simp at indexed_letter

/-- The first- and last-`b` decompositions give the exact scale floor used by the bounded
density envelope. -/
theorem firstBOneX211_tail_scale_lower
    (j h : Nat) (tail stem rest : List TagLetter)
    (first_b : tail = List.replicate j .c ++ .b :: rest)
    (last_b : tail = stem ++ .b :: List.replicate h .c) :
    3 ^ (j + 5 + h) ≤ 3 ^ (tagEncode 3 tail).length := by
  have index_order : j ≤ stem.length :=
    firstBOneX211_first_b_index_le_last_b_index j h stem rest
      (first_b.symm.trans last_b)
  have stem_length := tagEncode_length_le stem
  have trailing_c_length :
      (tagEncode 3 (List.replicate h .c)).length = h := by
    clear first_b last_b index_order stem_length
    induction h with
    | zero => rfl
    | succ h induction =>
        rw [List.replicate_succ, tagEncode_cons, List.length_append]
        simp only [tagCode, List.length_singleton, induction]
        omega
  have encoded_length :
      (tagEncode 3 tail).length = (tagEncode 3 stem).length + 5 + h := by
    rw [last_b, tagEncode_append, List.length_append, tagEncode_cons,
      List.length_append]
    have b_length : (tagCode 3 .b).length = 5 := by decide
    rw [b_length, trailing_c_length]
    omega
  apply Nat.pow_le_pow_right (by norm_num)
  omega

private theorem firstBOneX211_cb_scale (tail : List TagLetter) :
    3 ^ (tagEncode 3 ([.c, .b] ++ tail)).length =
      729 * 3 ^ (tagEncode 3 tail).length := by
  rw [tagEncode_append, List.length_append, pow_add]
  norm_num [tagEncode, spell, tagCode]

private theorem firstBOneX211_cb_complement (tail : List TagLetter) :
    tagComplementCode ([.c, .b] ++ tail) =
      39 * 3 ^ (tagEncode 3 tail).length + tagComplementCode tail := by
  rw [tagComplementCode_append]
  have stem_complement : tagComplementCode [.c, .b] = 39 := by decide
  rw [stem_complement]

/-- At a physical `cb` zero, the tail complement satisfies the exact normalized x=211
balance equation. -/
theorem firstBOneX211_core_balance
    (tail : List TagLetter) (y z : Nat)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
        (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) 211 y z = 0) :
    let T : Nat := 3 ^ (tagEncode 3 tail).length
    let E : Nat := tagComplementCode tail
    ((39 * T + E : Nat) : ℤ) * firstBOneX211J y z =
      (T : ℤ) * firstBOneX211A y z - firstBOneX211B y z := by
  let body := [.c, .b] ++ tail
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E : Nat := tagComplementCode tail
  let S : Nat := 3 ^ (tagEncode 3 body).length
  let C : Nat := ternaryCode (tagEncode 3 body)
  let D : Nat := tagComplementCode body
  have scale_eq : S = 729 * T := by
    dsimp [S, T, body]
    exact firstBOneX211_cb_scale tail
  have complement_eq : D = 39 * T + E := by
    dsimp [D, T, E, body]
    exact firstBOneX211_cb_complement tail
  have code_lt : C < S := by
    dsimp [C, S, body]
    exact ternaryCode_lt_pow_length (tagEncode 3 ([.c, .b] ++ tail))
  have complement_nat : D = S - C - 1 := rfl
  have coordinate_sum : C + D + 1 = S := by omega
  have code_eq_int : (C : ℤ) = 729 * T - 1 - (39 * T + E) := by
    have coordinate_sum_int : (C : ℤ) + D + 1 = S := by
      exact_mod_cast coordinate_sum
    have scale_eq_int : (S : ℤ) = 729 * T := by exact_mod_cast scale_eq
    have complement_eq_int : (D : ℤ) = 39 * T + E := by
      exact_mod_cast complement_eq
    omega
  have scale_cast :
      (S : ℚ) = (3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length := by
    dsimp [S, body]
    norm_num
  rw [← scale_cast] at core_zero
  change bZeroBDefectCOneCodeCore (S : ℚ) (C : ℚ) 211 y z = 0 at core_zero
  have core_zero_int :
      bZeroBDefectCOneCodeCore (S : ℤ) (C : ℤ) 211 y z = 0 := by
    unfold bZeroBDefectCOneCodeCore at core_zero ⊢
    exact_mod_cast core_zero
  rw [scale_eq, code_eq_int] at core_zero_int
  change ((39 * T + E : Nat) : ℤ) * firstBOneX211J y z =
    (T : ℤ) * firstBOneX211A y z - firstBOneX211B y z
  push_cast at core_zero_int ⊢
  unfold bZeroBDefectCOneCodeCore at core_zero_int
  unfold firstBOneX211J firstBOneX211A firstBOneX211B firstBOneX211Q
  linear_combination core_zero_int

/-- A physical x=211 `cb` zero has middle wait at least two. This is independent of every
trailing-run and inner-wait bound. -/
theorem firstBOneX211_wait_two_le_of_core_zero
    (tail : List TagLetter) (y z : Nat)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
        (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) 211 y z = 0) :
    2 ≤ y := by
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E : Nat := tagComplementCode tail
  have scale_positive : (1 : ℤ) ≤ T := by
    dsimp [T]
    exact_mod_cast one_le_pow₀ (by norm_num : 0 < 3)
  have balance := firstBOneX211_core_balance tail y z core_zero
  change ((39 * T + E : Nat) : ℤ) * firstBOneX211J y z =
    (T : ℤ) * firstBOneX211A y z - firstBOneX211B y z at balance
  have left_nonnegative :
      (0 : ℤ) ≤ ((39 * T + E : Nat) : ℤ) * firstBOneX211J y z := by
    have complement_nonnegative : (0 : ℤ) ≤ ((39 * T + E : Nat) : ℤ) :=
      Int.natCast_nonneg _
    have coefficient_positive : (0 : ℤ) < firstBOneX211J y z := by
      unfold firstBOneX211J
      positivity
    exact mul_nonneg complement_nonnegative coefficient_positive.le
  by_contra wait_not_two
  have wait_cases : y = 0 ∨ y = 1 := by omega
  rcases wait_cases with rfl | rfl
  · have factor_positive :
        (0 : ℤ) < 5216979348711180 * z + 487663725961773 := by
      positivity
    have scaled_nonnegative :
        (0 : ℤ) ≤ ((T : ℤ) - 1) *
          (5216979348711180 * z + 487663725961773) := by
      exact mul_nonneg (sub_nonneg.mpr scale_positive) factor_positive.le
    norm_num [firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J] at balance left_nonnegative
    nlinarith
  · have factor_positive :
        (0 : ℤ) < 5216747778809100 * z + 487675262773629 := by
      positivity
    have scaled_nonnegative :
        (0 : ℤ) ≤ ((T : ℤ) - 1) *
          (5216747778809100 * z + 487675262773629) := by
      exact mul_nonneg (sub_nonneg.mpr scale_positive) factor_positive.le
    norm_num [firstBOneX211A, firstBOneX211B, firstBOneX211Q,
      firstBOneX211J] at balance left_nonnegative
    nlinarith

/-- A physical x=211 zero with exact first- and last-`b` decompositions satisfies the cleared
density envelope used by the finite classifier. -/
theorem firstBOneX211DensityEnvelope_of_core_zero
    (j h : Nat) (tail stem rest : List TagLetter) (y z : Nat)
    (first_b : tail = List.replicate j .c ++ .b :: rest)
    (last_b : tail = stem ++ .b :: List.replicate h .c)
    (y_positive : 2 ≤ y)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
        (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) 211 y z = 0) :
    FirstBOneX211DensityEnvelope h j y z := by
  let p : Nat := 3 ^ j
  let T₀ : Nat := 3 ^ (j + 5 + h)
  let T : Nat := 3 ^ (tagEncode 3 tail).length
  let E : Nat := tagComplementCode tail
  have p_positive : 0 < p := by dsimp [p]; positivity
  have threshold_positive : 0 < T₀ := by dsimp [T₀]; positivity
  have scale_positive : 0 < T := by dsimp [T]; positivity
  have scale_lower : T₀ ≤ T := by
    dsimp [T₀, T]
    exact firstBOneX211_tail_scale_lower j h tail stem rest first_b last_b
  have balance := firstBOneX211_core_balance tail y z core_zero
  change ((39 * T + E : Nat) : ℤ) * firstBOneX211J y z =
    (T : ℤ) * firstBOneX211A y z - firstBOneX211B y z at balance
  push_cast at balance
  have complement_balance :
      (E : ℤ) * firstBOneX211J y z =
        (T : ℤ) * (firstBOneX211A y z - 39 * firstBOneX211J y z) -
          firstBOneX211B y z := by
    nlinarith [balance]
  have density := tagComplementCode_first_b_density j rest
  rw [← first_b] at density
  change 13 * T ≤ 81 * p * E ∧ 242 * p * E < 39 * T at density
  have density_lower : (13 : ℤ) * T ≤ 81 * p * E := by
    exact_mod_cast density.1
  have density_upper : (242 : ℤ) * p * E < 39 * T := by
    exact_mod_cast density.2
  have scale_lower_int : (T₀ : ℤ) ≤ T := by exact_mod_cast scale_lower
  have j_positive : (0 : ℤ) < firstBOneX211J y z := by
    unfold firstBOneX211J
    positivity
  have b_nonnegative : (0 : ℤ) ≤ firstBOneX211B y z := by
    have y_positive_int : (2 : ℤ) ≤ y := by exact_mod_cast y_positive
    have wait_nonnegative : (0 : ℤ) ≤ 8 * y - 9 := by omega
    have root_positive :
        (0 : ℤ) < 465621956 * z + 42879529 := by positivity
    unfold firstBOneX211B firstBOneX211Q
    exact mul_nonneg wait_nonnegative root_positive.le
  change
    (39 * (81 * (p : ℤ)) + 13) * firstBOneX211J y z ≤
        81 * p * firstBOneX211A y z ∧
      242 * p * ((T₀ : ℤ) * firstBOneX211A y z - firstBOneX211B y z) ≤
        (T₀ : ℤ) * (39 * (242 * p) + 39) * firstBOneX211J y z
  constructor
  · have density_lower_scaled :
        (13 : ℤ) * T * firstBOneX211J y z ≤
          81 * p * E * firstBOneX211J y z :=
      mul_le_mul_of_nonneg_right density_lower j_positive.le
    have scale_positive_int : (0 : ℤ) < T := by exact_mod_cast scale_positive
    have scaled_target :
        (T : ℤ) * (13 * firstBOneX211J y z) ≤
          T * (81 * p *
            (firstBOneX211A y z - 39 * firstBOneX211J y z)) := by
      calc
        (T : ℤ) * (13 * firstBOneX211J y z) =
            13 * T * firstBOneX211J y z := by ring
        _ ≤ 81 * p * E * firstBOneX211J y z := density_lower_scaled
        _ = 81 * p * ((T : ℤ) *
            (firstBOneX211A y z - 39 * firstBOneX211J y z) -
              firstBOneX211B y z) := by
          rw [← complement_balance]
          ring
        _ ≤ T * (81 * p *
            (firstBOneX211A y z - 39 * firstBOneX211J y z)) := by
          have coefficient_nonnegative : (0 : ℤ) ≤ 81 * p := by positivity
          nlinarith
    have target := (Int.mul_le_mul_left scale_positive_int).mp scaled_target
    nlinarith
  · let H : ℤ :=
      242 * p * (firstBOneX211A y z - 39 * firstBOneX211J y z) -
        39 * firstBOneX211J y z
    have actual_negative : (T : ℤ) * H < 242 * p * firstBOneX211B y z := by
      have density_upper_scaled := mul_lt_mul_of_pos_right density_upper j_positive
      have actual_expanded :
          242 * p * ((T : ℤ) *
              (firstBOneX211A y z - 39 * firstBOneX211J y z) -
                firstBOneX211B y z) <
            39 * T * firstBOneX211J y z := by
        calc
          242 * p * ((T : ℤ) *
              (firstBOneX211A y z - 39 * firstBOneX211J y z) -
                firstBOneX211B y z) =
              242 * p * (E * firstBOneX211J y z) := by
            rw [complement_balance]
          _ = (242 * p * E) * firstBOneX211J y z := by ring
          _ < (39 * T) * firstBOneX211J y z := density_upper_scaled
          _ = 39 * T * firstBOneX211J y z := by ring
      dsimp [H]
      nlinarith
    have target : (T₀ : ℤ) * H ≤ 242 * p * firstBOneX211B y z := by
      by_cases h_nonnegative : 0 ≤ H
      · have scaled := mul_le_mul_of_nonneg_right scale_lower_int h_nonnegative
        nlinarith
      · have threshold_nonnegative : (0 : ℤ) ≤ T₀ := by positivity
        have right_nonnegative :
            (0 : ℤ) ≤ 242 * p * firstBOneX211B y z := by positivity
        nlinarith
    dsimp [H] at target
    nlinarith

/-- The lower density-envelope inequality forces the middle wait into the finite classifier's
sharp lower range. -/
theorem firstBOneX211_y_lower_of_density_envelope
    (h j y z : Nat) (density : FirstBOneX211DensityEnvelope h j y z) :
    22529 ≤ y := by
  let p : ℤ := 3 ^ j
  have p_positive : 0 < p := by dsimp [p]; positivity
  have j_positive : (0 : ℤ) < firstBOneX211J y z := by
    unfold firstBOneX211J
    positivity
  have lower := density.1
  change (39 * (81 * p) + 13) * firstBOneX211J y z ≤
    81 * p * firstBOneX211A y z at lower
  have scaled_strict :
      p * (3159 * firstBOneX211J y z) <
        p * (81 * firstBOneX211A y z) := by
    calc
      p * (3159 * firstBOneX211J y z) =
          39 * (81 * p) * firstBOneX211J y z := by ring
      _ < (39 * (81 * p) + 13) * firstBOneX211J y z := by nlinarith
      _ ≤ 81 * p * firstBOneX211A y z := lower
      _ = p * (81 * firstBOneX211A y z) := by ring
  have root_strict := (Int.mul_lt_mul_left p_positive).mp scaled_strict
  by_contra wait_not_bounded
  have wait_upper : y ≤ 22528 := by omega
  have wait_upper_int : (y : ℤ) ≤ 22528 := by exact_mod_cast wait_upper
  have z_nonnegative : (0 : ℤ) ≤ z := by positivity
  have coefficient_nonpositive :
      (18757162068480 : ℤ) * y - 422575327245605580 ≤ 0 := by
    nlinarith
  have coefficient_product_nonpositive :
      ((18757162068480 : ℤ) * y - 422575327245605580) * z ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg coefficient_nonpositive z_nonnegative
  have polynomial_identity :
      81 * firstBOneX211A y z - 3159 * firstBOneX211J y z =
        ((18757162068480 : ℤ) * y - 422575327245605580) * z -
          934481760336 * y - 39500761802903613 := by
    unfold firstBOneX211A firstBOneX211Q firstBOneX211J
    ring
  have polynomial_negative :
      81 * firstBOneX211A y z - 3159 * firstBOneX211J y z < 0 := by
    rw [polynomial_identity]
    nlinarith
  nlinarith

/-- The density envelope by itself contains an unbounded inner-wait ray, so it cannot supply the
finite `z` cutoff used by the valuation classifier. -/
theorem firstBOneX211DensityEnvelope_unbounded_inner_ray
    (z : Nat) (inner_large : 394 ≤ z) :
    FirstBOneX211DensityEnvelope 0 0 39726 z := by
  unfold FirstBOneX211DensityEnvelope firstBOneX211A firstBOneX211B
    firstBOneX211Q firstBOneX211J
  norm_num
  constructor <;> nlinarith

/-- Every bounded trailing valuation envelope already excludes middle waits zero and one. -/
theorem firstBOneX211_wait_positive_of_valuation_envelope
    (h y z : Nat) (run_bound : h ≤ 5)
    (valuation : FirstBOneX211ValuationEnvelope h y z) :
    2 ≤ y := by
  by_contra wait_not_positive
  have wait_upper : y ≤ 1 := by omega
  obtain ⟨uOrder, vOrder, order_lower, order_sum, vOrder_bound,
    wait_shell, inner_shell⟩ := valuation
  have order_upper : uOrder ≤ h + 16 := by omega
  interval_cases h <;>
    interval_cases y <;>
    interval_cases uOrder <;>
    norm_num [ExactThreeOrder, firstBOneX211RootResidue] at wait_shell

/-- The physical x=211 `cb` chamber is empty once the bounded valuation envelope and the three
remaining numerical bounds are supplied. -/
theorem bZeroBDefectCOneCodeCore_x211_ne_zero_of_valuation_envelope
    (j h : Nat) (tail stem rest : List TagLetter) (y z : Nat)
    (first_b : tail = List.replicate j .c ++ .b :: rest)
    (last_b : tail = stem ++ .b :: List.replicate h .c)
    (run_bound : h ≤ 5) (position_bound : j ≤ 13)
    (inner_bound : z < 3 ^ 13)
    (valuation : FirstBOneX211ValuationEnvelope h y z) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
      (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) 211 y z ≠ 0 := by
  intro core_zero
  have core_zero_first_b :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^
          (tagEncode 3 (List.replicate 1 .c ++ .b :: tail)).length)
        (ternaryCode (tagEncode 3 (List.replicate 1 .c ++ .b :: tail)))
        211 y z = 0 := by
    simpa using core_zero
  have wait_upper :=
    bZeroBDefectCOne_y_le_of_first_b 1 tail 211 y z core_zero_first_b
  have wait_positive :=
    firstBOneX211_wait_positive_of_valuation_envelope h y z run_bound valuation
  have density :=
    firstBOneX211DensityEnvelope_of_core_zero j h tail stem rest y z
      first_b last_b wait_positive core_zero
  have wait_lower := firstBOneX211_y_lower_of_density_envelope h j y z density
  obtain ⟨candidate, position_zero⟩ :=
    firstBOneX211Candidate_of_envelopes h j y z run_bound position_bound
      wait_lower wait_upper inner_bound valuation density
  subst j
  have tail_eq : tail = .b :: rest := by simpa using first_b
  rw [tail_eq] at core_zero
  exact firstBOneX211Candidate_core_ne_zero rest h y z candidate (by simpa using core_zero)

/-- The physical x=211 `cb` chamber is empty under the trailing-run and inner-wait bounds; the
next-`b` position is forced below thirteen by the valuation and density envelopes. -/
theorem bZeroBDefectCOneCodeCore_x211_ne_zero_of_valuation_envelope_without_position_bound
    (j h : Nat) (tail stem rest : List TagLetter) (y z : Nat)
    (first_b : tail = List.replicate j .c ++ .b :: rest)
    (last_b : tail = stem ++ .b :: List.replicate h .c)
    (run_bound : h ≤ 5) (inner_bound : z < 3 ^ 13)
    (valuation : FirstBOneX211ValuationEnvelope h y z) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
      (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) 211 y z ≠ 0 := by
  intro core_zero
  have core_zero_first_b :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^
          (tagEncode 3 (List.replicate 1 .c ++ .b :: tail)).length)
        (ternaryCode (tagEncode 3 (List.replicate 1 .c ++ .b :: tail)))
        211 y z = 0 := by
    simpa using core_zero
  have wait_upper :=
    bZeroBDefectCOne_y_le_of_first_b 1 tail 211 y z core_zero_first_b
  have wait_positive :=
    firstBOneX211_wait_positive_of_valuation_envelope h y z run_bound valuation
  have density :=
    firstBOneX211DensityEnvelope_of_core_zero j h tail stem rest y z
      first_b last_b wait_positive core_zero
  have wait_lower := firstBOneX211_y_lower_of_density_envelope h j y z density
  obtain ⟨candidate, position_zero⟩ :=
    firstBOneX211Candidate_of_envelopes_without_position_bound h j y z run_bound
      wait_lower wait_upper inner_bound valuation density
  subst j
  have tail_eq : tail = .b :: rest := by simpa using first_b
  rw [tail_eq] at core_zero
  exact firstBOneX211Candidate_core_ne_zero rest h y z candidate (by simpa using core_zero)

/-- No physical x=211 `cb` zero survives inside the explicit trailing-run, next-`b`-position,
and inner-wait box. -/
theorem bZeroBDefectCOneCodeCore_x211_ne_zero_of_bounds
    (j h : Nat) (tail stem rest : List TagLetter) (y z : Nat)
    (first_b : tail = List.replicate j .c ++ .b :: rest)
    (last_b : tail = stem ++ .b :: List.replicate h .c)
    (run_bound : h ≤ 5) (position_bound : j ≤ 13)
    (inner_bound : z < 3 ^ 13) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
      (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) 211 y z ≠ 0 := by
  intro core_zero
  have valuation :=
    firstBOneX211ValuationEnvelope_of_core_zero tail stem h y z last_b run_bound
      inner_bound core_zero
  exact bZeroBDefectCOneCodeCore_x211_ne_zero_of_valuation_envelope
    j h tail stem rest y z first_b last_b run_bound position_bound inner_bound valuation
    core_zero

/-- No physical x=211 `cb` zero survives under the trailing-run and inner-wait bounds. -/
theorem bZeroBDefectCOneCodeCore_x211_ne_zero_of_run_and_inner_bounds
    (j h : Nat) (tail stem rest : List TagLetter) (y z : Nat)
    (first_b : tail = List.replicate j .c ++ .b :: rest)
    (last_b : tail = stem ++ .b :: List.replicate h .c)
    (run_bound : h ≤ 5) (inner_bound : z < 3 ^ 13) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
      (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) 211 y z ≠ 0 := by
  intro core_zero
  have valuation :=
    firstBOneX211ValuationEnvelope_of_core_zero tail stem h y z last_b run_bound
      inner_bound core_zero
  exact
    bZeroBDefectCOneCodeCore_x211_ne_zero_of_valuation_envelope_without_position_bound
      j h tail stem rest y z first_b last_b run_bound inner_bound valuation core_zero

/-- No physical x=211 `cb` zero survives under the inner-wait bound. The trailing-run and
next-`b` bounds are both consequences of the exact physical coordinates. -/
theorem bZeroBDefectCOneCodeCore_x211_ne_zero_of_inner_bound
    (j h : Nat) (tail stem rest : List TagLetter) (y z : Nat)
    (first_b : tail = List.replicate j .c ++ .b :: rest)
    (last_b : tail = stem ++ .b :: List.replicate h .c)
    (inner_bound : z < 3 ^ 13) :
    bZeroBDefectCOneCodeCore
      ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
      (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) 211 y z ≠ 0 := by
  intro core_zero
  have wait_positive := firstBOneX211_wait_two_le_of_core_zero tail y z core_zero
  have density :=
    firstBOneX211DensityEnvelope_of_core_zero j h tail stem rest y z
      first_b last_b wait_positive core_zero
  have wait_lower := firstBOneX211_y_lower_of_density_envelope h j y z density
  have core_zero_first_b :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^
          (tagEncode 3 (List.replicate 1 .c ++ .b :: tail)).length)
        (ternaryCode (tagEncode 3 (List.replicate 1 .c ++ .b :: tail)))
        211 y z = 0 := by
    simpa using core_zero
  have wait_upper :=
    bZeroBDefectCOne_y_le_of_first_b 1 tail 211 y z core_zero_first_b
  by_cases run_bounded : h ≤ 5
  · exact bZeroBDefectCOneCodeCore_x211_ne_zero_of_run_and_inner_bounds
      j h tail stem rest y z first_b last_b run_bounded inner_bound core_zero
  · have run_large : 6 ≤ h := by omega
    let A : ℤ := (3 : ℤ) ^ (tagEncode 3 stem).length
    let G : ℤ := tagComplementCode stem
    have run_core := firstBOneX211RunCore_of_core_zero stem h y z (by
      rw [← last_b]
      exact core_zero)
    change bZeroBDefectCOneCodeCore (firstBOneX211RunScale h A)
      (firstBOneX211RunScale h A - 1 - firstBOneX211RunComplement h A G)
        211 y z = 0 at run_core
    have G_three : (3 : ℤ) ∣ G := by
      dsimp [G]
      exact_mod_cast tagComplementCode_three_dvd stem
    exact bZeroBDefectCOneCodeCore_x211_ne_zero_of_large_run_coordinates
      h j y z A G run_large wait_lower wait_upper inner_bound G_three density run_core

end MatrixMortality.ParabolicBlade
