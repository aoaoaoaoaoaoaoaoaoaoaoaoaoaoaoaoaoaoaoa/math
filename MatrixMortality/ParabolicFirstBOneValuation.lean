import MatrixMortality.PadicValuation
import MatrixMortality.ParabolicFirstBOneFunnel
import MatrixMortality.ParabolicFirstBOneSFFT
import MatrixMortality.ParabolicTrailing

/-!
# Physical 3-adic closure of the x=211 chamber

For a body whose first two letters are `cb` and whose final `b` is followed by at most five
`c`s, a zero of the physical x=211 core forces the exact valuation envelope consumed by
`ParabolicFirstBOneFunnel`. The proof derives the two coordinate shells from the SFFT product
equation and exact congruences at their universal roots.
-/

namespace MatrixMortality.ParabolicBlade

/-- Exact divisibility by `3 ^ order` is the nonzero integer valuation equation. -/
theorem exactThreeOrder_iff_padicValInt (value : ℤ) (order : Nat) :
    ExactThreeOrder value order ↔ value ≠ 0 ∧ padicValInt 3 value = order := by
  constructor
  · rintro ⟨divisible, not_next⟩
    have value_ne : value ≠ 0 := by
      intro value_zero
      exact not_next (value_zero ▸ dvd_zero ((3 : ℤ) ^ (order + 1)))
    have lower : order ≤ padicValInt 3 value :=
      (padicValInt_dvd_iff order value).mp divisible |>.resolve_left value_ne
    have upper : padicValInt 3 value < order + 1 := by
      by_contra not_upper
      apply not_next
      exact (padicValInt_dvd_iff (order + 1) value).mpr
        (Or.inr (Nat.le_of_not_gt not_upper))
    exact ⟨value_ne, Nat.le_antisymm (Nat.lt_succ_iff.mp upper) lower⟩
  · rintro ⟨value_ne, valuation⟩
    constructor
    · exact (padicValInt_dvd_iff order value).mpr (Or.inr valuation.ge)
    · intro next_divisible
      have next_le :=
        (padicValInt_dvd_iff (order + 1) value).mp next_divisible |>.resolve_left value_ne
      rw [valuation] at next_le
      omega

/-- Multiplication by a 3-adic unit preserves divisibility by every power of three. -/
theorem three_pow_dvd_mul_iff_of_three_unit (factor value : ℤ) (order : Nat)
    (factor_unit : ¬(3 : ℤ) ∣ factor) :
    (3 : ℤ) ^ order ∣ factor * value ↔ (3 : ℤ) ^ order ∣ value := by
  have factor_ne : factor ≠ 0 := by
    intro factor_zero
    exact factor_unit (factor_zero ▸ dvd_zero (3 : ℤ))
  constructor
  · intro product_divisible
    by_cases value_zero : value = 0
    · exact value_zero ▸ dvd_zero ((3 : ℤ) ^ order)
    · have product_ne : factor * value ≠ 0 := mul_ne_zero factor_ne value_zero
      have order_le_product : order ≤ padicValInt 3 (factor * value) :=
        (padicValInt_dvd_iff order (factor * value)).mp product_divisible |>.resolve_left
          product_ne
      have factor_valuation : padicValInt 3 factor = 0 :=
        padicValInt.eq_zero_of_not_dvd factor_unit
      have product_valuation := padicValInt.mul (p := 3) factor_ne value_zero
      rw [factor_valuation, zero_add] at product_valuation
      exact (padicValInt_dvd_iff order value).mpr
        (Or.inr (product_valuation ▸ order_le_product))
  · intro value_divisible
    exact dvd_mul_of_dvd_right value_divisible factor

/-- A unit-scaled congruence modulo a deeper power preserves every shallower exact order. -/
theorem exactThreeOrder_congruent_unit_iff
    (actual factor value : ℤ) (order cap : Nat) (order_lt : order < cap)
    (factor_unit : ¬(3 : ℤ) ∣ factor)
    (congruent : (3 : ℤ) ^ cap ∣ actual - factor * value) :
    ExactThreeOrder actual order ↔ ExactThreeOrder value order := by
  have order_le : order ≤ cap := order_lt.le
  have next_le : order + 1 ≤ cap := order_lt
  have residual_order : (3 : ℤ) ^ order ∣ actual - factor * value :=
    dvd_trans (pow_dvd_pow (3 : ℤ) order_le) congruent
  have residual_next : (3 : ℤ) ^ (order + 1) ∣ actual - factor * value :=
    dvd_trans (pow_dvd_pow (3 : ℤ) next_le) congruent
  have factor_order := three_pow_dvd_mul_iff_of_three_unit factor value order factor_unit
  have factor_next := three_pow_dvd_mul_iff_of_three_unit factor value (order + 1) factor_unit
  constructor
  · rintro ⟨actual_order, actual_not_next⟩
    constructor
    · apply factor_order.mp
      have sum_divisible := dvd_add actual_order (dvd_neg.mpr residual_order)
      have identity : actual + -(actual - factor * value) = factor * value := by ring
      rw [identity] at sum_divisible
      exact sum_divisible
    · intro value_next
      apply actual_not_next
      have product_next := factor_next.mpr value_next
      have sum_divisible := dvd_add product_next residual_next
      have identity : factor * value + (actual - factor * value) = actual := by ring
      rw [identity] at sum_divisible
      exact sum_divisible
  · rintro ⟨value_order, value_not_next⟩
    constructor
    · have product_order := factor_order.mpr value_order
      have sum_divisible := dvd_add product_order residual_order
      have identity : factor * value + (actual - factor * value) = actual := by ring
      rw [identity] at sum_divisible
      exact sum_divisible
    · intro actual_next
      apply value_not_next
      apply factor_next.mp
      have difference_divisible := dvd_sub actual_next residual_next
      have identity : actual - (actual - factor * value) = factor * value := by ring
      rw [identity] at difference_divisible
      exact difference_divisible

/-- A unit-scaled congruence modulo `3 ^ cap` preserves divisibility at the cap. -/
theorem three_pow_dvd_congruent_unit_iff
    (actual factor value : ℤ) (cap : Nat)
    (factor_unit : ¬(3 : ℤ) ∣ factor)
    (congruent : (3 : ℤ) ^ cap ∣ actual - factor * value) :
    (3 : ℤ) ^ cap ∣ actual ↔ (3 : ℤ) ^ cap ∣ value := by
  have factor_cap := three_pow_dvd_mul_iff_of_three_unit factor value cap factor_unit
  constructor
  · intro actual_cap
    apply factor_cap.mp
    have difference_divisible := dvd_sub actual_cap congruent
    have identity : actual - (actual - factor * value) = factor * value := by ring
    rw [identity] at difference_divisible
    exact difference_divisible
  · intro value_cap
    have product_cap := factor_cap.mpr value_cap
    have sum_divisible := dvd_add product_cap congruent
    have identity : factor * value + (actual - factor * value) = actual := by ring
    rw [identity] at sum_divisible
    exact sum_divisible

private theorem fixed_content_order : padicValInt 3 (67908593862 : ℤ) = 14 := by
  have exact : ExactThreeOrder 67908593862 14 := by
    norm_num [ExactThreeOrder]
  exact (exactThreeOrder_iff_padicValInt 67908593862 14).mp exact |>.2

private theorem product_orders
    (U V D W : ℤ) (h : Nat) (u_ne : U ≠ 0) (v_ne : V ≠ 0)
    (d_exact : ExactThreeOrder D (h + 1)) (w_exact : ExactThreeOrder W 1)
    (product_eq : U * V = 67908593862 * D * W) :
    padicValInt 3 U + padicValInt 3 V = h + 16 := by
  have d_value := (exactThreeOrder_iff_padicValInt D (h + 1)).mp d_exact
  have w_value := (exactThreeOrder_iff_padicValInt W 1).mp w_exact
  have left_value := padicValInt.mul (p := 3) u_ne v_ne
  have coefficient_d_ne : (67908593862 : ℤ) * D ≠ 0 :=
    mul_ne_zero (by norm_num) d_value.1
  have coefficient_d_value :=
    padicValInt.mul (p := 3) (by norm_num : (67908593862 : ℤ) ≠ 0) d_value.1
  have right_value := padicValInt.mul (p := 3) coefficient_d_ne w_value.1
  have valuations_equal := congrArg (padicValInt 3) product_eq
  rw [left_value, right_value, coefficient_d_value, fixed_content_order,
    d_value.2, w_value.2] at valuations_equal
  omega

/-- Scale coordinate of a `cb · stem · b c^h` body after the stem scale is named `A`. -/
def firstBOneX211RunScale (h : Nat) (A : ℤ) : ℤ := 729 * (243 * 3 ^ h * A)

/-- Complement coordinate of a `cb · stem · b c^h` body after the stem coordinates are
named `A` and `G`. -/
def firstBOneX211RunComplement (h : Nat) (A G : ℤ) : ℤ :=
  39 * (243 * 3 ^ h * A) + 3 ^ (h + 1) * (81 * G + 13)

private theorem trailing_c_encoded_length (h : Nat) :
    (tagEncode 3 (List.replicate h .c)).length = h := by
  induction h with
  | zero => rfl
  | succ h induction =>
      rw [List.replicate_succ, tagEncode_cons, List.length_append]
      simp [tagCode, induction]
      omega

private theorem trailing_encoded_length (stem : List TagLetter) (h : Nat) :
    (tagEncode 3 (stem ++ .b :: List.replicate h .c)).length =
      (tagEncode 3 stem).length + 5 + h := by
  rw [tagEncode_append, List.length_append]
  simp only [tagEncode_cons, List.length_append]
  rw [trailing_c_encoded_length]
  norm_num [tagCode]
  omega

/-- Exact scale coordinates supplied by the final-`b` decomposition. -/
theorem firstBOneX211RunScale_of_stem (stem : List TagLetter) (h : Nat) :
    (3 : ℤ) ^ (tagEncode 3 ([.c, .b] ++
        (stem ++ .b :: List.replicate h .c))).length =
      firstBOneX211RunScale h (3 ^ (tagEncode 3 stem).length) := by
  rw [tagEncode_append, List.length_append, trailing_encoded_length, pow_add, pow_add,
    pow_add]
  norm_num [tagEncode, spell, tagCode, firstBOneX211RunScale]
  ring

/-- Exact complement coordinates supplied by the final-`b` decomposition. -/
theorem firstBOneX211RunComplement_of_stem (stem : List TagLetter) (h : Nat) :
    (tagComplementCode ([.c, .b] ++
        (stem ++ .b :: List.replicate h .c)) : ℤ) =
      firstBOneX211RunComplement h (3 ^ (tagEncode 3 stem).length)
        (tagComplementCode stem) := by
  rw [tagComplementCode_append]
  have cb_complement : tagComplementCode [.c, .b] = 39 := by decide
  rw [cb_complement, tagComplementCode_append_b_c_run]
  have tail_scale :
      (3 : ℤ) ^ (tagEncode 3 (stem ++ .b :: List.replicate h .c)).length =
        243 * 3 ^ h * (3 : ℤ) ^ (tagEncode 3 stem).length := by
    rw [trailing_encoded_length, pow_add, pow_add]
    norm_num
    ring
  push_cast
  rw [tail_scale]
  unfold firstBOneX211RunComplement
  ring

/-- A rational physical core with a displayed final `b` is exactly the integral run-coordinate
core. -/
theorem firstBOneX211RunCore_of_core_zero
    (stem : List TagLetter) (h y z : Nat)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^ (tagEncode 3
          ([.c, .b] ++ (stem ++ .b :: List.replicate h .c))).length)
        (ternaryCode (tagEncode 3
          ([.c, .b] ++ (stem ++ .b :: List.replicate h .c)))) 211 y z = 0) :
    bZeroBDefectCOneCodeCore
      (firstBOneX211RunScale h ((3 : ℤ) ^ (tagEncode 3 stem).length))
      (firstBOneX211RunScale h ((3 : ℤ) ^ (tagEncode 3 stem).length) - 1 -
        firstBOneX211RunComplement h ((3 : ℤ) ^ (tagEncode 3 stem).length)
          (tagComplementCode stem)) 211 y z = 0 := by
  let body := [.c, .b] ++ (stem ++ .b :: List.replicate h .c)
  let S : Nat := 3 ^ (tagEncode 3 body).length
  let C : Nat := ternaryCode (tagEncode 3 body)
  let D : Nat := tagComplementCode body
  have scale_eq_int :
      (S : ℤ) = firstBOneX211RunScale h ((3 : ℤ) ^ (tagEncode 3 stem).length) := by
    change ((3 ^ (tagEncode 3 ([.c, .b] ++
        (stem ++ .b :: List.replicate h .c))).length : Nat) : ℤ) =
      firstBOneX211RunScale h ((3 : ℤ) ^ (tagEncode 3 stem).length)
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      firstBOneX211RunScale_of_stem stem h
  have complement_eq_int :
      (D : ℤ) = firstBOneX211RunComplement h ((3 : ℤ) ^ (tagEncode 3 stem).length)
        (tagComplementCode stem) := by
    dsimp [D, body]
    exact firstBOneX211RunComplement_of_stem stem h
  have code_lt : C < S := by
    dsimp [C, S, body]
    exact ternaryCode_lt_pow_length
      (tagEncode 3 ([.c, .b] ++ (stem ++ .b :: List.replicate h .c)))
  have complement_nat : D = S - C - 1 := rfl
  have coordinate_sum : C + D + 1 = S := by omega
  have coordinate_sum_int : (C : ℤ) + D + 1 = S := by
    exact_mod_cast coordinate_sum
  have code_eq_int :
      (C : ℤ) = firstBOneX211RunScale h ((3 : ℤ) ^ (tagEncode 3 stem).length) - 1 -
        firstBOneX211RunComplement h ((3 : ℤ) ^ (tagEncode 3 stem).length)
          (tagComplementCode stem) := by
    omega
  have scale_cast :
      (S : ℚ) =
        (3 : ℚ) ^
          (tagEncode 3 ([.c, .b] ++
            (stem ++ .b :: List.replicate h .c))).length := by
    dsimp [S, body]
    norm_num
  rw [← scale_cast] at core_zero
  change bZeroBDefectCOneCodeCore (S : ℚ) (C : ℚ) 211 y z = 0 at core_zero
  have core_zero_int :
      bZeroBDefectCOneCodeCore (S : ℤ) (C : ℤ) 211 y z = 0 := by
    unfold bZeroBDefectCOneCodeCore at core_zero ⊢
    exact_mod_cast core_zero
  rw [scale_eq_int, code_eq_int] at core_zero_int
  exact core_zero_int

/-- Every encoded-body complement is divisible by three. -/
theorem tagComplementCode_three_dvd (body : List TagLetter) :
    3 ∣ tagComplementCode body := by
  induction body using List.reverseRecOn with
  | nil => simp [tagComplementCode]
  | append_singleton body letter induction =>
      cases letter with
      | b =>
          rw [tagComplementCode_append_b]
          omega
      | c =>
          rw [tagComplementCode_append_c]
          exact dvd_mul_right 3 (tagComplementCode body)

private theorem u_root_congruence
    (h : Nat) (A G : ℤ) (h_le : h ≤ 5) (G_three : (3 : ℤ) ∣ G) :
    (3 : ℤ) ^ (h + 7) ∣
      8 * bZeroBDefectCOneSfftN
          (firstBOneX211RunScale h A) (firstBOneX211RunComplement h A G) *
          firstBOneX211RootResidue h -
        3 * bZeroBDefectCOneSfftC
          (firstBOneX211RunScale h A)
          (firstBOneX211RunComplement h A G) := by
  obtain ⟨g, rfl⟩ := G_three
  interval_cases h <;>
    norm_num [firstBOneX211RunScale, firstBOneX211RunComplement, bZeroBDefectCOneSfftN,
      bZeroBDefectCOneSfftC, firstBOneX211RootResidue] <;>
    omega

private theorem v_root_congruence (h : Nat) (A G : ℤ) (h_le : h ≤ 5) :
    (3 : ℤ) ^ 13 ∣
      4 * bZeroBDefectCOneSfftN
          (firstBOneX211RunScale h A) (firstBOneX211RunComplement h A G) *
          420724 -
        bZeroBDefectCOneSfftM
          (firstBOneX211RunScale h A)
          (firstBOneX211RunComplement h A G) := by
  interval_cases h <;>
    norm_num [firstBOneX211RunScale, firstBOneX211RunComplement, bZeroBDefectCOneSfftN,
      bZeroBDefectCOneSfftM] <;>
    omega

private theorem v_root_exact (h : Nat) (A G : ℤ) (h_le : h ≤ 5) :
    ExactThreeOrder (bZeroBDefectCOneSfftV
      (firstBOneX211RunScale h A)
      (firstBOneX211RunComplement h A G) 420724) 13 := by
  interval_cases h <;>
    norm_num [ExactThreeOrder, firstBOneX211RunScale,
      firstBOneX211RunComplement, bZeroBDefectCOneSfftV,
      bZeroBDefectCOneSfftN, bZeroBDefectCOneSfftM] <;>
    omega

private theorem complement_exact (h : Nat) (A G : ℤ) (h_le : h ≤ 5) :
    ExactThreeOrder (firstBOneX211RunComplement h A G) (h + 1) := by
  interval_cases h <;>
    norm_num [ExactThreeOrder, firstBOneX211RunComplement] <;>
    omega

private theorem w_exact (h : Nat) (A G : ℤ) (h_le : h ≤ 5) :
    ExactThreeOrder (bZeroBDefectCOneSfftW
      (firstBOneX211RunScale h A)
      (firstBOneX211RunComplement h A G)) 1 := by
  interval_cases h <;>
    norm_num [ExactThreeOrder, firstBOneX211RunScale,
      firstBOneX211RunComplement, bZeroBDefectCOneSfftW] <;>
    omega

private theorem n_unit (h : Nat) (A G : ℤ) (h_le : h ≤ 5) :
    ¬(3 : ℤ) ∣ bZeroBDefectCOneSfftN
      (firstBOneX211RunScale h A)
      (firstBOneX211RunComplement h A G) := by
  interval_cases h <;>
    norm_num [firstBOneX211RunScale, firstBOneX211RunComplement,
      bZeroBDefectCOneSfftN] <;>
    omega

private theorem valuation_envelope_coordinates
    (h y z : Nat) (A G : ℤ) (h_le : h ≤ 5) (z_upper : z < 3 ^ 13)
    (G_three : (3 : ℤ) ∣ G)
    (core_zero :
      bZeroBDefectCOneCodeCore (firstBOneX211RunScale h A)
        (firstBOneX211RunScale h A - 1 - firstBOneX211RunComplement h A G) 211 y z = 0) :
    FirstBOneX211ValuationEnvelope h y z := by
  let S := firstBOneX211RunScale h A
  let D := firstBOneX211RunComplement h A G
  let N := bZeroBDefectCOneSfftN S D
  let U := bZeroBDefectCOneSfftU S D (y : ℤ)
  let V := bZeroBDefectCOneSfftV S D (z : ℤ)
  let W := bZeroBDefectCOneSfftW S D
  have d_exact : ExactThreeOrder D (h + 1) := by
    dsimp [D]
    exact complement_exact h A G h_le
  have w_has_order : ExactThreeOrder W 1 := by
    dsimp [W, S, D]
    exact w_exact h A G h_le
  have n_not_divisible : ¬(3 : ℤ) ∣ N := by
    dsimp [N, S, D]
    exact n_unit h A G h_le
  have eight_n_unit : ¬(3 : ℤ) ∣ 8 * N := by
    intro divisible
    obtain ⟨q, product_eq⟩ := divisible
    apply n_not_divisible
    refine ⟨3 * N - q, ?_⟩
    omega
  have four_n_unit : ¬(3 : ℤ) ∣ 4 * N := by
    intro divisible
    obtain ⟨q, product_eq⟩ := divisible
    apply n_not_divisible
    refine ⟨q - N, ?_⟩
    omega
  have product_eq : U * V = 67908593862 * D * W := by
    dsimp [U, V, S, D, W]
    exact bZeroBDefectCOneSfft_eq_of_core_zero
      (firstBOneX211RunScale h A) (firstBOneX211RunComplement h A G) y z core_zero
  have d_ne : D ≠ 0 := (exactThreeOrder_iff_padicValInt D (h + 1)).mp d_exact |>.1
  have w_ne : W ≠ 0 := (exactThreeOrder_iff_padicValInt W 1).mp w_has_order |>.1
  have right_ne : (67908593862 : ℤ) * D * W ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) d_ne) w_ne
  have product_ne : U * V ≠ 0 := product_eq ▸ right_ne
  have u_ne : U ≠ 0 := left_ne_zero_of_mul product_ne
  have v_ne : V ≠ 0 := right_ne_zero_of_mul product_ne
  let uOrder := padicValInt 3 U
  let vOrder := padicValInt 3 V
  have order_sum : uOrder + vOrder = h + 16 := by
    dsimp [uOrder, vOrder]
    exact product_orders U V D W h u_ne v_ne d_exact w_has_order product_eq
  have u_congruent :
      (3 : ℤ) ^ (h + 7) ∣
        U - 8 * N * ((y : ℤ) - firstBOneX211RootResidue h) := by
    have raw := u_root_congruence h A G h_le G_three
    dsimp [U, N, S, D]
    convert raw using 1
    unfold bZeroBDefectCOneSfftU
    ring
  have v_congruent :
      (3 : ℤ) ^ 13 ∣ V - 4 * N * ((z : ℤ) - 420724) := by
    have raw := v_root_congruence h A G h_le
    dsimp [V, N, S, D]
    convert raw using 1
    · norm_num
    · unfold bZeroBDefectCOneSfftV
      ring
  have v_cap_transfer :
      (3 : ℤ) ^ 13 ∣ V ↔ (3 : ℤ) ^ 13 ∣ (z : ℤ) - 420724 :=
    three_pow_dvd_congruent_unit_iff V (4 * N) ((z : ℤ) - 420724) 13
      four_n_unit v_congruent
  have v_shell :
      vOrder ≤ 13 ∧
        ((vOrder = 13 ∧ z = 420724) ∨
          (vOrder < 13 ∧ ExactThreeOrder ((z : ℤ) - 420724) vOrder)) := by
    by_cases z_eq : z = 420724
    · subst z
      have top_exact : ExactThreeOrder V 13 := by
        dsimp [V, S, D]
        exact v_root_exact h A G h_le
      have top_value := (exactThreeOrder_iff_padicValInt V 13).mp top_exact
      have order_eq : vOrder = 13 := by
        dsimp [vOrder]
        exact top_value.2
      exact ⟨order_eq.le, Or.inl ⟨order_eq, rfl⟩⟩
    · have order_lt : vOrder < 13 := by
        by_contra order_not_lt
        have cap_divisible : (3 : ℤ) ^ 13 ∣ V :=
          (padicValInt_dvd_iff 13 V).mpr
            (Or.inr (by dsimp [vOrder] at order_not_lt ⊢; omega))
        have difference_divisible := v_cap_transfer.mp cap_divisible
        norm_num only [Nat.reducePow] at difference_divisible
        obtain ⟨q, difference_eq⟩ := difference_divisible
        have z_upper_int : (z : ℤ) < 1594323 := by exact_mod_cast z_upper
        have z_nonnegative : (0 : ℤ) ≤ z := by positivity
        have z_eq_int : (z : ℤ) = 420724 := by omega
        exact z_eq (by exact_mod_cast z_eq_int)
      have actual_exact : ExactThreeOrder V vOrder :=
        (exactThreeOrder_iff_padicValInt V vOrder).mpr ⟨v_ne, rfl⟩
      have difference_exact : ExactThreeOrder ((z : ℤ) - 420724) vOrder :=
        (exactThreeOrder_congruent_unit_iff V (4 * N) ((z : ℤ) - 420724)
          vOrder 13 order_lt four_n_unit v_congruent).mp actual_exact
      exact ⟨order_lt.le, Or.inr ⟨order_lt, difference_exact⟩⟩
  have u_lower : h + 3 ≤ uOrder := by omega
  have u_shell :
      (uOrder < h + 7 ∧
          ExactThreeOrder ((y : ℤ) - firstBOneX211RootResidue h) uOrder) ∨
        (h + 7 ≤ uOrder ∧
          (3 : ℤ) ^ (h + 7) ∣ (y : ℤ) - firstBOneX211RootResidue h) := by
    by_cases u_shallow : uOrder < h + 7
    · have actual_exact : ExactThreeOrder U uOrder :=
        (exactThreeOrder_iff_padicValInt U uOrder).mpr ⟨u_ne, rfl⟩
      have difference_exact :=
        (exactThreeOrder_congruent_unit_iff U (8 * N)
          ((y : ℤ) - firstBOneX211RootResidue h) uOrder (h + 7)
          u_shallow eight_n_unit u_congruent).mp actual_exact
      exact Or.inl ⟨u_shallow, difference_exact⟩
    · have u_deep : h + 7 ≤ uOrder := by omega
      have actual_divisible : (3 : ℤ) ^ (h + 7) ∣ U :=
        (padicValInt_dvd_iff (h + 7) U).mpr
          (Or.inr (by dsimp [uOrder] at u_deep ⊢; exact u_deep))
      have difference_divisible :=
        (three_pow_dvd_congruent_unit_iff U (8 * N)
          ((y : ℤ) - firstBOneX211RootResidue h) (h + 7)
          eight_n_unit u_congruent).mp actual_divisible
      exact Or.inr ⟨u_deep, difference_divisible⟩
  exact ⟨uOrder, vOrder, u_lower, order_sum, v_shell.1, u_shell, v_shell.2⟩

/--
A physical x=211 core zero in the `cb` chamber forces the complete bounded valuation envelope
when the final `b` has at most five trailing `c`s and `z < 3^13`.
-/
theorem firstBOneX211ValuationEnvelope_of_core_zero
    (tail stem : List TagLetter) (h y z : Nat)
    (last_b : tail = stem ++ .b :: List.replicate h .c)
    (h_le : h ≤ 5) (z_upper : z < 3 ^ 13)
    (core_zero :
      bZeroBDefectCOneCodeCore
        ((3 : ℚ) ^ (tagEncode 3 ([.c, .b] ++ tail)).length)
        (ternaryCode (tagEncode 3 ([.c, .b] ++ tail))) 211 y z = 0) :
    FirstBOneX211ValuationEnvelope h y z := by
  subst tail
  let A : ℤ := (3 : ℤ) ^ (tagEncode 3 stem).length
  let G : ℤ := tagComplementCode stem
  have core_zero_int := firstBOneX211RunCore_of_core_zero stem h y z core_zero
  change bZeroBDefectCOneCodeCore (firstBOneX211RunScale h A)
    (firstBOneX211RunScale h A - 1 - firstBOneX211RunComplement h A G)
      211 y z = 0 at core_zero_int
  have G_three : (3 : ℤ) ∣ G := by
    dsimp [G]
    exact_mod_cast tagComplementCode_three_dvd stem
  exact valuation_envelope_coordinates h y z A G h_le z_upper G_three core_zero_int

end MatrixMortality.ParabolicBlade
