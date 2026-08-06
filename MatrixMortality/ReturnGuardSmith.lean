import MatrixMortality.ReturnGuardContinued

/-!
# Smith split and unimodular endpoint decoder

At critical depth two, complementary endpoint contents split the cyclotomic factor `q - 1`
into positive factors `u v`.  This file records a signed coprime split, the resulting
unimodular decoder, and the exact maximal-cancellation recurrence.  The decoder contracts in a
fixed weighted Archimedean norm whenever `v ≥ 2`; hence the sole noncontracting throat is `v = 1`.

The final section repairs a frame error in the motivating calculation.  One residual step has
an exact cocycle only when the same wait scale is used at both ends.  A change to the next wait
is a separate rational gauge.  Keeping those maps separate prevents an invalid concatenating
cocycle from entering the theorem bank.
-/

/-- If `core` lies in `shift`, then the part of `core` coprime to `left` must lie in
`right` whenever `left * right = fixed * shift`. -/
theorem Nat.quotient_gcd_dvd_right_of_dvd_of_mul_eq_mul
    {core left right fixed shift : Nat}
    (left_positive : 0 < left) (core_dvd_shift : core ∣ shift)
    (product_eq : left * right = fixed * shift) :
    core / Nat.gcd core left ∣ right := by
  let common := Nat.gcd core left
  let coreQuotient := core / common
  let leftQuotient := left / common
  have common_positive : 0 < common :=
    Nat.gcd_pos_of_pos_right core left_positive
  have core_eq : core = coreQuotient * common := by
    dsimp [coreQuotient, common]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left core left)).symm
  have left_eq : left = leftQuotient * common := by
    dsimp [leftQuotient, common]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_right core left)).symm
  obtain ⟨shiftQuotient, shift_eq⟩ := core_dvd_shift
  have cancelled : leftQuotient * right = fixed * coreQuotient * shiftQuotient := by
    apply Nat.eq_of_mul_eq_mul_right common_positive
    calc
      leftQuotient * right * common = left * right := by rw [left_eq]; ring
      _ = fixed * shift := product_eq
      _ = fixed * (core * shiftQuotient) := by rw [shift_eq]
      _ = (fixed * coreQuotient * shiftQuotient) * common := by rw [core_eq]; ring
  have coprime : Nat.Coprime coreQuotient leftQuotient :=
    Nat.coprime_div_gcd_div_gcd common_positive
  apply coprime.dvd_of_dvd_mul_left
  use fixed * shiftQuotient
  calc
    leftQuotient * right = fixed * coreQuotient * shiftQuotient := cancelled
    _ = coreQuotient * (fixed * shiftQuotient) := by ring

/-- A factor is bounded by the left allocation times its complementary gcd quotient. -/
theorem Nat.le_mul_quotient_gcd
    {core left : Nat} (left_positive : 0 < left) :
    core ≤ left * (core / Nat.gcd core left) := by
  let common := Nat.gcd core left
  have common_le : common ≤ left := Nat.gcd_le_right left left_positive
  have core_eq : core = core / common * common := by
    dsimp [common]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left core left)).symm
  calc
    core = core / common * common := core_eq
    _ ≤ core / common * left := Nat.mul_le_mul_left (core / common) common_le
    _ = left * (core / Nat.gcd core left) := by dsimp [common]; ring

namespace MatrixMortality.ReturnGuard

open scoped Matrix

/-- Signed coprime split of `content * complement = fixed * shift`, with positive shift
coordinates.  The invariant is the four displayed products; no quotient state is retained. -/
structure SmithRubanSplit
    (fixed shift content complement : ℤ) where
  /-- Positive portion of the forward content supported on the moving shift. -/
  u : ℤ
  /-- Signed fixed-support portion of the forward content. -/
  eta : ℤ
  /-- Signed fixed-support portion of the reverse content. -/
  theta : ℤ
  /-- Positive portion of the reverse content supported on the moving shift. -/
  v : ℤ
  u_pos : 0 < u
  v_pos : 0 < v
  content_eq : content = eta * u
  complement_eq : complement = theta * v
  fixed_eq : fixed = eta * theta
  shift_eq : shift = u * v
  u_coprime_theta : IsCoprime u theta

/-- Unimodular decoder attached to one signed Smith split of `q - 1`. -/
def smithRubanDecoder
    {R : Type*} [CommRing R] (q u v : R) : Square (Fin 2) R :=
  !![v, q ^ 2; 1, (q + 1) * u]

/-- Decoder output before primitive reduction. -/
def smithRubanQuotient
    (q scale u v eta sourceDenominator targetDenominator : ℤ) : Fin 2 → ℤ :=
  ![
    scale * v * sourceDenominator + q ^ 2 * eta * targetDenominator,
    scale * sourceDenominator + (q + 1) * u * eta * targetDenominator]

/-- Weighted Archimedean norm in which every nonmaximal Smith branch contracts. -/
def smithRubanWeight (point : Fin 2 → ℝ) : ℝ :=
  |point 0| + 4 * |point 1|

theorem smithRubanDecoder_det
    {q fixed content complement : ℤ}
    (split : SmithRubanSplit fixed (q - 1) content complement) :
    (smithRubanDecoder q split.u split.v).det = -1 := by
  rw [Matrix.det_fin_two]
  simp [smithRubanDecoder]
  calc
    split.v * ((q + 1) * split.u) - q ^ 2 =
        (q + 1) * (split.u * split.v) - q ^ 2 := by ring
    _ = (q + 1) * (q - 1) - q ^ 2 := by rw [← split.shift_eq]
    _ = -1 := by ring

/-- The Smith decoder is exactly a positive shear followed by one Gauss continuant generator.
This exposes its two Smith coordinates as continued-fraction data without adding state. -/
theorem smithRubanDecoder_continuant_cut
    {R : Type*} [CommRing R] {q u v : R}
    (shift_eq : q - 1 = u * v) :
    smithRubanDecoder q u v =
      !![1, v; 0, 1] * !![0, 1; 1, (q + 1) * u] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [smithRubanDecoder, Matrix.mul_apply, Fin.sum_univ_succ]
  calc
    q ^ 2 = 1 + (q + 1) * (q - 1) := by ring
    _ = 1 + (q + 1) * (u * v) := by rw [shift_eq]
    _ = 1 + v * ((q + 1) * u) := by ring

theorem smithRubanDecoder_mulVec
    (q scale u v eta sourceDenominator targetDenominator : ℤ) :
    smithRubanDecoder q u v *ᵥ
        ![scale * sourceDenominator, eta * targetDenominator] =
      smithRubanQuotient q scale u v eta sourceDenominator targetDenominator := by
  ext i
  fin_cases i <;>
    simp [smithRubanDecoder, smithRubanQuotient, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_succ] <;>
    ring

theorem smithRubanDecoder_weight_contraction
    {q u v : ℝ} (q_lower : 3 ≤ q) (u_lower : 1 ≤ u) (v_lower : 2 ≤ v)
    (split : u * v = q - 1) (point : Fin 2 → ℝ) :
    4 * smithRubanWeight (smithRubanDecoder q u v *ᵥ point) ≤
      3 * q ^ 2 * smithRubanWeight point := by
  have u_nonneg : 0 ≤ u := by linarith
  have v_nonneg : 0 ≤ v := by linarith
  have v_le : v ≤ q - 1 := by
    have gap : 0 ≤ (u - 1) * v :=
      mul_nonneg (sub_nonneg.mpr u_lower) v_nonneg
    nlinarith
  have first_coefficient : 4 * (v + 4) ≤ 3 * q ^ 2 := by
    have gap : 0 ≤ (q - 3) * (3 * q + 5) :=
      mul_nonneg (sub_nonneg.mpr q_lower) (by linarith)
    nlinarith
  have twice_u_le : 2 * u ≤ q - 1 := by
    have gap : 0 ≤ (v - 2) * u :=
      mul_nonneg (sub_nonneg.mpr v_lower) u_nonneg
    nlinarith
  have second_coefficient :
      4 * (q ^ 2 + 4 * ((q + 1) * u)) ≤ 12 * q ^ 2 := by
    have q_plus_nonneg : 0 ≤ q + 1 := by linarith
    have scaled := mul_le_mul_of_nonneg_left twice_u_le q_plus_nonneg
    nlinarith [sq_nonneg q]
  have first_abs :
      |v * point 0 + q ^ 2 * point 1| ≤
        v * |point 0| + q ^ 2 * |point 1| := by
    calc
      |v * point 0 + q ^ 2 * point 1| ≤
          |v * point 0| + |q ^ 2 * point 1| := abs_add _ _
      _ = v * |point 0| + q ^ 2 * |point 1| := by
        rw [abs_mul, abs_mul, abs_of_nonneg v_nonneg,
          abs_of_nonneg (sq_nonneg q)]
  have second_abs :
      |point 0 + (q + 1) * u * point 1| ≤
        |point 0| + (q + 1) * u * |point 1| := by
    calc
      |point 0 + (q + 1) * u * point 1| ≤
          |point 0| + |(q + 1) * u * point 1| := abs_add _ _
      _ = |point 0| + (q + 1) * u * |point 1| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ q + 1),
          abs_of_nonneg u_nonneg]
  have bound : 4 *
        (|v * point 0 + q ^ 2 * point 1| +
          4 * |point 0 + (q + 1) * u * point 1|) ≤
      3 * q ^ 2 * (|point 0| + 4 * |point 1|) := by
    calc
      4 *
          (|v * point 0 + q ^ 2 * point 1| +
            4 * |point 0 + (q + 1) * u * point 1|) ≤
        4 *
          (v * |point 0| + q ^ 2 * |point 1| +
            4 * (|point 0| + (q + 1) * u * |point 1|)) := by
              gcongr
      _ = 4 * (v + 4) * |point 0| +
          4 * (q ^ 2 + 4 * ((q + 1) * u)) * |point 1| := by ring
      _ ≤ 3 * q ^ 2 * |point 0| + 12 * q ^ 2 * |point 1| := by
        gcongr
      _ = 3 * q ^ 2 * (|point 0| + 4 * |point 1|) := by ring
  simpa [smithRubanWeight, smithRubanDecoder, Matrix.mulVec,
    Matrix.dotProduct, Fin.sum_univ_succ] using bound

theorem smithRubanQuotient_inverse
    {q u v : ℤ} (shift_eq : q - 1 = u * v)
    (scale eta sourceDenominator targetDenominator : ℤ) :
    eta * targetDenominator =
        smithRubanQuotient q scale u v eta sourceDenominator targetDenominator 0 -
          v * smithRubanQuotient q scale u v eta sourceDenominator targetDenominator 1 ∧
      scale * sourceDenominator =
        q ^ 2 * smithRubanQuotient q scale u v eta sourceDenominator targetDenominator 1 -
          (q + 1) * u *
            smithRubanQuotient q scale u v eta sourceDenominator targetDenominator 0 := by
  simp only [smithRubanQuotient, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  constructor
  · calc
      eta * targetDenominator =
          eta * targetDenominator * (q ^ 2 - (q + 1) * (u * v)) := by
            rw [← shift_eq]
            ring
      _ = scale * v * sourceDenominator + q ^ 2 * eta * targetDenominator -
          v * (scale * sourceDenominator +
            (q + 1) * u * eta * targetDenominator) := by ring
  · calc
      scale * sourceDenominator =
          scale * sourceDenominator * (q ^ 2 - (q + 1) * (u * v)) := by
            rw [← shift_eq]
            ring
      _ = q ^ 2 *
          (scale * sourceDenominator + (q + 1) * u * eta * targetDenominator) -
        (q + 1) * u *
          (scale * v * sourceDenominator + q ^ 2 * eta * targetDenominator) := by ring

/-- The unimodular Smith quotient preserves primitivity. -/
theorem smithRubanQuotient_isCoprime
    {q u v left right : ℤ} (shift_eq : q - 1 = u * v)
    (primitive : IsCoprime left right) :
    IsCoprime
      (smithRubanQuotient q 1 u v 1 left right 0)
      (smithRubanQuotient q 1 u v 1 left right 1) := by
  obtain ⟨leftCoefficient, rightCoefficient, bezout⟩ := primitive
  refine ⟨rightCoefficient - leftCoefficient * ((q + 1) * u),
    leftCoefficient * q ^ 2 - rightCoefficient * v, ?_⟩
  have inverse := smithRubanQuotient_inverse shift_eq 1 1 left right
  calc
    (rightCoefficient - leftCoefficient * ((q + 1) * u)) *
          smithRubanQuotient q 1 u v 1 left right 0 +
        (leftCoefficient * q ^ 2 - rightCoefficient * v) *
          smithRubanQuotient q 1 u v 1 left right 1 =
      leftCoefficient *
          (q ^ 2 * smithRubanQuotient q 1 u v 1 left right 1 -
            (q + 1) * u * smithRubanQuotient q 1 u v 1 left right 0) +
        rightCoefficient *
          (smithRubanQuotient q 1 u v 1 left right 0 -
            v * smithRubanQuotient q 1 u v 1 left right 1) := by ring
    _ = leftCoefficient * left + rightCoefficient * right := by
      rw [← inverse.2, ← inverse.1]
      simp
    _ = 1 := bezout

/-- On the positive rational cone, the Smith decoder strictly raises primitive-pair height.
This is the rational positive-matrix descent criterion in the reverse orientation. -/
theorem smithRubanQuotient_height_gain_of_pos
    {q u v left right : ℤ}
    (q_positive : 0 < q) (v_positive : 0 < v)
    (left_positive : 0 < left) (right_positive : 0 < right) :
    integralPairHeight left right <
      integralPairHeight
        (smithRubanQuotient q 1 u v 1 left right 0)
        (smithRubanQuotient q 1 u v 1 left right 1) := by
  let first := smithRubanQuotient q 1 u v 1 left right 0
  have q_square_positive : 0 < q ^ 2 := sq_pos_of_pos q_positive
  have first_eq : first = v * left + q ^ 2 * right := by
    simp [first, smithRubanQuotient]
  have left_lt_first : left < first := by
    rw [first_eq]
    nlinarith [mul_pos v_positive left_positive,
      mul_pos q_square_positive right_positive]
  have right_lt_first : right < first := by
    rw [first_eq]
    nlinarith [mul_pos v_positive left_positive,
      mul_pos q_square_positive right_positive]
  rw [integralPairHeight, integralPairHeight]
  have left_abs_lt : left.natAbs < first.natAbs :=
    Int.natAbs_lt_natAbs_of_nonneg_of_lt left_positive.le left_lt_first
  have right_abs_lt : right.natAbs < first.natAbs :=
    Int.natAbs_lt_natAbs_of_nonneg_of_lt right_positive.le right_lt_first
  apply lt_of_lt_of_le (max_lt_iff.mpr ⟨left_abs_lt, right_abs_lt⟩)
  exact le_max_left _ _

theorem smithRubanQuotient_commonDivisor_iff
    {q u v : ℤ} (shift_eq : q - 1 = u * v)
    (scale eta sourceDenominator targetDenominator divisor : ℤ) :
    (divisor ∣ smithRubanQuotient q scale u v eta sourceDenominator targetDenominator 0 ∧
      divisor ∣ smithRubanQuotient q scale u v eta sourceDenominator targetDenominator 1) ↔
      divisor ∣ scale * sourceDenominator ∧
        divisor ∣ eta * targetDenominator := by
  let quotient := smithRubanQuotient q scale u v eta sourceDenominator targetDenominator
  have inverse := smithRubanQuotient_inverse shift_eq scale eta sourceDenominator targetDenominator
  constructor
  · rintro ⟨first, second⟩
    refine ⟨?_, ?_⟩
    · rw [inverse.2]
      exact dvd_sub (second.mul_left (q ^ 2))
        (first.mul_left ((q + 1) * u))
    · rw [inverse.1]
      exact dvd_sub first (second.mul_left v)
  · rintro ⟨source, target⟩
    refine ⟨?_, ?_⟩
    · dsimp [quotient]
      simp only [smithRubanQuotient, Matrix.cons_val_zero]
      exact dvd_add
        (by simpa [mul_assoc, mul_comm, mul_left_comm] using source.mul_left v)
        (by simpa [mul_assoc, mul_comm, mul_left_comm] using target.mul_left (q ^ 2))
    · dsimp [quotient]
      simp only [smithRubanQuotient, Matrix.cons_val_one, Matrix.head_cons]
      exact dvd_add source
        (by simpa [mul_assoc, mul_comm, mul_left_comm] using
          target.mul_left ((q + 1) * u))

theorem exists_smithRubanSplit
    {fixed shift content complement : ℤ}
    (shift_pos : 0 < shift)
    (content_ne : content ≠ 0)
    (product_eq : content * complement = fixed * shift) :
    Nonempty (SmithRubanSplit fixed shift content complement) := by
  have gcd_pos : 0 < Int.gcd content fixed :=
    Int.gcd_pos_of_ne_zero_left fixed content_ne
  obtain ⟨contentCore, fixedCore, core_coprime, content_eq, fixed_eq⟩ :=
    Int.exists_gcd_one gcd_pos
  have gcd_ne : (Int.gcd content fixed : ℤ) ≠ 0 := by
    exact_mod_cast gcd_pos.ne'
  have contentCore_ne : contentCore ≠ 0 := by
    intro core_zero
    rw [core_zero, zero_mul] at content_eq
    exact content_ne content_eq
  have contentCore_fixedCore_coprime : IsCoprime contentCore fixedCore :=
    Int.gcd_eq_one_iff_coprime.mp core_coprime
  by_cases contentCore_pos : 0 < contentCore
  · let u := contentCore
    let eta : ℤ := Int.gcd content fixed
    let theta := fixedCore
    have eta_ne : eta ≠ 0 := gcd_ne
    have cancelled : u * complement = theta * shift := by
      apply mul_left_cancel₀ eta_ne
      calc
        eta * (u * complement) = content * complement := by
          rw [content_eq]
          ring
        _ = fixed * shift := product_eq
        _ = eta * (theta * shift) := by
          rw [fixed_eq]
          ring
    have u_dvd_shift : u ∣ shift := by
      apply contentCore_fixedCore_coprime.dvd_of_dvd_mul_left
      use complement
      exact cancelled.symm
    obtain ⟨v, shift_eq⟩ := u_dvd_shift
    have v_pos : 0 < v := by
      rw [shift_eq] at shift_pos
      exact (mul_pos_iff_of_pos_left contentCore_pos).mp shift_pos
    have complement_eq : complement = theta * v := by
      apply mul_left_cancel₀ contentCore_ne
      rw [cancelled, shift_eq]
      ring
    exact ⟨{
      u := u
      eta := eta
      theta := theta
      v := v
      u_pos := contentCore_pos
      v_pos := v_pos
      content_eq := by simpa [u, eta, mul_comm] using content_eq
      complement_eq := complement_eq
      fixed_eq := by simpa [eta, theta, mul_comm] using fixed_eq
      shift_eq := by simpa [u] using shift_eq
      u_coprime_theta := contentCore_fixedCore_coprime }⟩
  · have contentCore_neg : contentCore < 0 := by omega
    let u := -contentCore
    let eta : ℤ := -(Int.gcd content fixed : ℤ)
    let theta := -fixedCore
    have eta_ne : eta ≠ 0 := neg_ne_zero.mpr gcd_ne
    have u_ne : u ≠ 0 := neg_ne_zero.mpr contentCore_ne
    have u_pos : 0 < u := neg_pos.mpr contentCore_neg
    have signed_content_eq : content = eta * u := by
      calc
        content = contentCore * (Int.gcd content fixed : ℤ) := content_eq
        _ = eta * u := by dsimp [eta, u]; ring
    have signed_fixed_eq : fixed = eta * theta := by
      calc
        fixed = fixedCore * (Int.gcd content fixed : ℤ) := fixed_eq
        _ = eta * theta := by dsimp [eta, theta]; ring
    have cancelled : u * complement = theta * shift := by
      apply mul_left_cancel₀ eta_ne
      calc
        eta * (u * complement) = content * complement := by
          rw [signed_content_eq]
          ring
        _ = fixed * shift := product_eq
        _ = eta * (theta * shift) := by
          rw [signed_fixed_eq]
          ring
    have signed_coprime : IsCoprime u theta :=
      contentCore_fixedCore_coprime.neg_left.neg_right
    have u_dvd_shift : u ∣ shift := by
      apply signed_coprime.dvd_of_dvd_mul_left
      use complement
      exact cancelled.symm
    obtain ⟨v, shift_eq⟩ := u_dvd_shift
    have v_pos : 0 < v := by
      rw [shift_eq] at shift_pos
      exact (mul_pos_iff_of_pos_left u_pos).mp shift_pos
    have complement_eq : complement = theta * v := by
      apply mul_left_cancel₀ u_ne
      rw [cancelled, shift_eq]
      ring
    exact ⟨{
      u := u
      eta := eta
      theta := theta
      v := v
      u_pos := u_pos
      v_pos := v_pos
      content_eq := signed_content_eq
      complement_eq := complement_eq
      fixed_eq := signed_fixed_eq
      shift_eq := by simpa [u] using shift_eq
      u_coprime_theta := signed_coprime }⟩

theorem PrimitiveEndpointReduction.smithRubanSplit
    {prime wait : Nat} [Fact prime.Prime]
    {centerNumerator driftNumerator scale : ℤ}
    {source target : ℤ × ℤ} {content complement : ℤ}
    (reduction : PrimitiveEndpointReduction prime 2 centerNumerator
      driftNumerator scale wait source target content)
    (complementary : content * complement =
      driftNumerator * scale * ((prime : ℤ) ^ wait - 1)) :
    Nonempty (SmithRubanSplit (driftNumerator * scale)
      ((prime : ℤ) ^ wait - 1) content complement) := by
  apply exists_smithRubanSplit
  · have power_gt_one : 1 < prime ^ wait :=
      one_lt_pow (Fact.out : prime.Prime).one_lt reduction.wait_positive.ne'
    have power_gt_one_int : (1 : ℤ) < (prime : ℤ) ^ wait := by
      exact_mod_cast power_gt_one
    omega
  · exact reduction.content_ne
  · exact complementary

/-- Any prescribed divisor of the cyclotomic factor splits between forward normalization and
reverse content.  The quotient after its gcd with the forward content divides the reverse
content, with multiplicity. -/
theorem PrimitiveEndpointReduction.coreQuotient_dvd_complement
    {prime wait : Nat} {centerNumerator driftNumerator scale : ℤ}
    {source target : ℤ × ℤ} {content complement : ℤ} {core : Nat}
    (reduction : PrimitiveEndpointReduction prime 2 centerNumerator
      driftNumerator scale wait source target content)
    (complementary : content * complement =
      driftNumerator * scale * ((prime : ℤ) ^ wait - 1))
    (core_dvd : core ∣ ((prime : ℤ) ^ wait - 1).natAbs) :
    core / Nat.gcd core content.natAbs ∣ complement.natAbs := by
  apply Nat.quotient_gcd_dvd_right_of_dvd_of_mul_eq_mul
    (Int.natAbs_pos.mpr reduction.content_ne) core_dvd
  have absolute := congrArg Int.natAbs complementary
  simpa only [Int.natAbs_mul] using absolute

theorem PrimitiveEndpointReduction.coreQuotient_coprime_targetDenominator
    {prime wait : Nat} {centerNumerator driftNumerator scale : ℤ}
    {source target : ℤ × ℤ} {content complement : ℤ} {core : Nat}
    (reduction : PrimitiveEndpointReduction prime 2 centerNumerator
      driftNumerator scale wait source target content)
    (complementary : content * complement =
      driftNumerator * scale * ((prime : ℤ) ^ wait - 1))
    (core_dvd : core ∣ ((prime : ℤ) ^ wait - 1).natAbs) :
    IsCoprime target.2
      ((core / Nat.gcd core content.natAbs : Nat) : ℤ) := by
  let quotient : Nat := core / Nat.gcd core content.natAbs
  have quotient_dvd := reduction.coreQuotient_dvd_complement
    complementary core_dvd
  change IsCoprime target.2 (quotient : ℤ)
  have quotient_dvd_int : (quotient : ℤ) ∣ complement := by
    obtain ⟨factor, factor_eq⟩ := quotient_dvd
    use Int.sign complement * factor
    calc
      complement = Int.sign complement * complement.natAbs :=
        (Int.sign_mul_natAbs complement).symm
      _ = Int.sign complement * ((quotient * factor : Nat) : ℤ) := by
        dsimp [quotient]
        rw [factor_eq]
      _ = (quotient : ℤ) * (Int.sign complement * factor) := by push_cast; ring
  exact IsCoprime.of_isCoprime_of_dvd_right
    (reduction.denominator_coprime_complement complementary) quotient_dvd_int

theorem PrimitiveEndpointReduction.core_le_content_mul_coreQuotient
    {prime wait : Nat} {centerNumerator driftNumerator scale : ℤ}
    {source target : ℤ × ℤ} {content : ℤ} (core : Nat)
    (reduction : PrimitiveEndpointReduction prime 2 centerNumerator
      driftNumerator scale wait source target content) :
    core ≤ content.natAbs * (core / Nat.gcd core content.natAbs) := by
  exact Nat.le_mul_quotient_gcd (Int.natAbs_pos.mpr reduction.content_ne)

theorem PrimitiveEndpointReduction.source_eq_smithRubanQuotient
    {prime wait : Nat} {centerNumerator driftNumerator scale : ℤ}
    {source target : ℤ × ℤ} {content complement : ℤ}
    (reduction : PrimitiveEndpointReduction prime 2 centerNumerator
      driftNumerator scale wait source target content)
    (split : SmithRubanSplit (driftNumerator * scale)
      ((prime : ℤ) ^ wait - 1) content complement) :
    source.1 = split.u *
      smithRubanQuotient ((prime : ℤ) ^ wait) scale split.u split.v split.eta
        source.2 target.2 0 := by
  have source_eq := reduction.source_eq_power_mul_prequotient
  simp only [endpointPrequotient] at source_eq
  rw [show 2 * wait = wait + wait by omega, pow_add] at source_eq
  have content_eq := split.content_eq
  have shift_eq := split.shift_eq
  rw [content_eq] at source_eq
  simp only [smithRubanQuotient, Matrix.cons_val_zero]
  linear_combination source_eq + scale * source.2 * shift_eq

theorem PrimitiveEndpointReduction.smithRuban_commonDivisor_dvd_fixed
    {prime wait : Nat} {centerNumerator driftNumerator scale : ℤ}
    {source target : ℤ × ℤ} {content complement divisor : ℤ}
    (reduction : PrimitiveEndpointReduction prime 2 centerNumerator
      driftNumerator scale wait source target content)
    (split : SmithRubanSplit (driftNumerator * scale)
      ((prime : ℤ) ^ wait - 1) content complement)
    (divides_first : divisor ∣
      smithRubanQuotient ((prime : ℤ) ^ wait) scale split.u split.v split.eta
        source.2 target.2 0)
    (divides_second : divisor ∣
      smithRubanQuotient ((prime : ℤ) ^ wait) scale split.u split.v split.eta
        source.2 target.2 1) :
    divisor ∣ scale * split.eta := by
  have inverse := smithRubanQuotient_commonDivisor_iff split.shift_eq scale split.eta
    source.2 target.2 divisor
  obtain ⟨source_dvd, target_dvd⟩ := inverse.mp ⟨divides_first, divides_second⟩
  obtain ⟨left, right, bezout⟩ := reduction.denominators_coprime
  obtain ⟨sourceFactor, sourceFactor_eq⟩ := source_dvd
  obtain ⟨targetFactor, targetFactor_eq⟩ := target_dvd
  use left * split.eta * sourceFactor + right * scale * targetFactor
  calc
    scale * split.eta = scale * split.eta * 1 := by ring
    _ = scale * split.eta * (left * source.2 + right * target.2) := by rw [bezout]
    _ = left * split.eta * (scale * source.2) +
        right * scale * (split.eta * target.2) := by ring
    _ = left * split.eta * (divisor * sourceFactor) +
        right * scale * (divisor * targetFactor) := by
          rw [sourceFactor_eq, targetFactor_eq]
    _ = divisor *
      (left * split.eta * sourceFactor + right * scale * targetFactor) := by ring

theorem PrimitiveEndpointReduction.smithRuban_resetDefect
    {prime wait : Nat} {centerNumerator driftNumerator scale : ℤ}
    {source target : ℤ × ℤ} {content complement : ℤ}
    (reduction : PrimitiveEndpointReduction prime 2 centerNumerator
      driftNumerator scale wait source target content)
    (split : SmithRubanSplit (driftNumerator * scale)
      ((prime : ℤ) ^ wait - 1) content complement) :
    scale *
        (target.1 -
          (centerNumerator + driftNumerator - scale) * target.2) =
      split.theta * split.v *
        smithRubanQuotient ((prime : ℤ) ^ wait) scale split.u split.v split.eta
          source.2 target.2 1 := by
  have complementary : content * complement =
      driftNumerator * scale * ((prime : ℤ) ^ wait - 1) := by
    calc
      content * complement =
          (split.eta * split.u) * (split.theta * split.v) :=
        congrArg₂ (fun left right ↦ left * right) split.content_eq split.complement_eq
      _ = (split.eta * split.theta) * (split.u * split.v) := by ring
      _ = (driftNumerator * scale) * ((prime : ℤ) ^ wait - 1) :=
        congrArg₂ (fun left right ↦ left * right) split.fixed_eq.symm split.shift_eq.symm
  rw [reduction.resetDefect_eq_complement_mul complementary]
  have sum_eq : geometricPowerSum ((prime : ℤ) ^ wait) 2 =
      1 + (prime : ℤ) ^ wait := by
    simp [geometricPowerSum, add_comm]
  have prequotient_eq : endpointPrequotient content target =
      (split.eta * split.u) * target.2 := by
    exact congrArg (fun value ↦ value * target.2) split.content_eq
  have bracket_eq :
      scale * source.2 +
          geometricPowerSum ((prime : ℤ) ^ wait) 2 *
            endpointPrequotient content target =
        smithRubanQuotient ((prime : ℤ) ^ wait) scale split.u split.v split.eta
          source.2 target.2 1 := by
    simp only [smithRubanQuotient, Matrix.cons_val_one, Matrix.head_cons]
    calc
      scale * source.2 +
          geometricPowerSum ((prime : ℤ) ^ wait) 2 *
            endpointPrequotient content target =
        scale * source.2 +
          (1 + (prime : ℤ) ^ wait) *
            ((split.eta * split.u) * target.2) :=
        congrArg₂ (fun left right ↦ left + right) rfl
          (congrArg₂ (fun left right ↦ left * right) sum_eq prequotient_eq)
      _ = scale * source.2 +
          ((prime : ℤ) ^ wait + 1) * split.u * split.eta * target.2 := by ring
  exact congrArg₂ (fun left right ↦ left * right) split.complement_eq bracket_eq

/-- Quotient carried by the unique noncontracting branch `v = 1`. -/
def maximalCancellationQuotient
    (q scale eta sourceDenominator targetDenominator : ℤ) : ℤ :=
  scale * sourceDenominator + q ^ 2 * eta * targetDenominator

theorem PrimitiveEndpointReduction.maximalCancellation
    {prime wait : Nat} {centerNumerator driftNumerator scale : ℤ}
    {source target : ℤ × ℤ} {content complement : ℤ}
    (reduction : PrimitiveEndpointReduction prime 2 centerNumerator
      driftNumerator scale wait source target content)
    (split : SmithRubanSplit (driftNumerator * scale)
      ((prime : ℤ) ^ wait - 1) content complement)
    (maximal : split.v = 1) :
    source.1 = ((prime : ℤ) ^ wait - 1) *
        maximalCancellationQuotient ((prime : ℤ) ^ wait) scale split.eta
          source.2 target.2 ∧
      split.eta * target.1 =
        driftNumerator *
            maximalCancellationQuotient ((prime : ℤ) ^ wait) scale split.eta
              source.2 target.2 +
          (centerNumerator - scale) * split.eta * target.2 := by
  let q : ℤ := (prime : ℤ) ^ wait
  let quotient := maximalCancellationQuotient q scale split.eta source.2 target.2
  have u_eq : split.u = q - 1 := by
    have shift_eq := split.shift_eq
    rw [maximal, mul_one] at shift_eq
    exact shift_eq.symm
  have quotient_eq : quotient =
      smithRubanQuotient q scale split.u split.v split.eta source.2 target.2 0 := by
    simp [quotient, maximalCancellationQuotient, smithRubanQuotient, maximal]
  have source_eq := reduction.source_eq_smithRubanQuotient split
  change source.1 = split.u *
    smithRubanQuotient q scale split.u split.v split.eta source.2 target.2 0 at source_eq
  have first : source.1 = (q - 1) * quotient := by
    rw [source_eq, quotient_eq, u_eq]
  refine ⟨first, ?_⟩
  have numerator_eq := reduction.target_eq_drift_add_prequotient
  simp only [endpointPrequotient] at numerator_eq
  have content_eq := split.content_eq
  rw [content_eq, first, u_eq] at numerator_eq
  have shift_ne : q - 1 ≠ 0 := by
    rw [← u_eq]
    exact ne_of_gt split.u_pos
  apply mul_left_cancel₀ shift_ne
  linear_combination numerator_eq

theorem maximalCancellation_chain
    {nextQ eta drift centerDifference targetNumerator targetDenominator
      quotient nextQuotient : ℤ}
    (transition : eta * targetNumerator =
      drift * quotient + centerDifference * eta * targetDenominator)
    (nextSource : targetNumerator = (nextQ - 1) * nextQuotient) :
    eta * (nextQ - 1) * nextQuotient =
      drift * quotient + centerDifference * eta * targetDenominator := by
  calc
    eta * (nextQ - 1) * nextQuotient = eta * targetNumerator := by
      rw [nextSource]
      ring
    _ = drift * quotient + centerDifference * eta * targetDenominator := transition

/-- Wait-adapted homogeneous frame on an integral residual pair. -/
def returnWaitFrame
    {R : Type*} [CommRing R] (q numerator denominator : R) : Fin 2 → R :=
  ![denominator, q ^ 2 * numerator - denominator]

/-- Exact lagged-frame transfer for one depth-two residual step.  The same wait scale appears
on both source and target; changing the target to its next wait requires a separate gauge. -/
def laggedReturnCocycle
    {R : Type*} [CommRing R]
    (q centerDifference driftNumerator scale : R) : Square (Fin 2) R :=
  !![
    centerDifference + driftNumerator * q ^ 2, centerDifference;
    scale * (1 - q), scale * (1 - q)]

theorem laggedReturnCocycle_mulVec
    {R : Type*} [CommRing R]
    {q centerDifference driftNumerator scale numerator denominator
      targetNumerator targetDenominator content : R}
    (denominator_eq :
      content * targetDenominator =
        centerDifference * numerator + driftNumerator * denominator)
    (difference :
      q ^ 2 * content * targetNumerator - content * targetDenominator =
        scale * (1 - q) * numerator) :
    laggedReturnCocycle q centerDifference driftNumerator scale *ᵥ
        returnWaitFrame q numerator denominator =
      (q ^ 2 * content) • returnWaitFrame q targetNumerator targetDenominator := by
  ext i
  fin_cases i
  · simp [laggedReturnCocycle, returnWaitFrame, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_succ, smul_eq_mul]
    linear_combination -(q ^ 2) * denominator_eq
  · simp [laggedReturnCocycle, returnWaitFrame, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_succ, smul_eq_mul]
    linear_combination -(q ^ 2) * difference

theorem integralStep_laggedReturnCocycle
    {prime wait : Nat} {centerNumerator driftNumerator scale : ℤ}
    {numerator denominator targetNumerator targetDenominator content : ℤ}
    (step : IntegralStep prime 2 centerNumerator driftNumerator scale wait
      numerator denominator (content * targetNumerator) (content * targetDenominator)) :
    laggedReturnCocycle ((prime : ℤ) ^ wait) (centerNumerator - scale)
        driftNumerator scale *ᵥ
        returnWaitFrame ((prime : ℤ) ^ wait) numerator denominator =
      (((prime : ℤ) ^ wait) ^ 2 * content) •
        returnWaitFrame ((prime : ℤ) ^ wait) targetNumerator targetDenominator := by
  apply laggedReturnCocycle_mulVec
  · simpa only [terminalDefect] using step.2
  · have difference := integralStep_difference step
    rw [show 2 * wait = wait + wait by omega, pow_add] at difference
    simpa only [pow_two, mul_assoc] using difference

/-- Rational gauge changing a residual frame from wait scale `q` to wait scale `nextQ`. -/
def returnWaitFrameChange (q nextQ : ℚ) : Square (Fin 2) ℚ :=
  !![1, 0; nextQ ^ 2 / q ^ 2 - 1, nextQ ^ 2 / q ^ 2]

theorem returnWaitFrameChange_mulVec
    {q : ℚ} (nextQ numerator denominator : ℚ) (q_ne : q ≠ 0) :
    returnWaitFrameChange q nextQ *ᵥ returnWaitFrame q numerator denominator =
      returnWaitFrame nextQ numerator denominator := by
  ext i
  fin_cases i
  all_goals
    simp [returnWaitFrameChange, returnWaitFrame, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_succ]
  field_simp [q_ne]
  ring

/-- One fixed integral basis diagonalizes every wait-frame gauge.  The moving factor is the
pure base-prime dilation `nextQ² / q²`, not an independent shear. -/
theorem returnWaitFrameChange_diagonal
    (q nextQ : ℚ) :
    !![1, 0; 1, 1] * returnWaitFrameChange q nextQ * !![1, 0; -1, 1] =
      !![1, 0; 0, nextQ ^ 2 / q ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [returnWaitFrameChange, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The honest variable-wait cocycle is the lagged transfer followed by an explicit frame
gauge.  Omitting this factor silently identifies two different target frames. -/
def gaugedReturnCocycle
    (q nextQ centerDifference driftNumerator scale : ℚ) : Square (Fin 2) ℚ :=
  returnWaitFrameChange q nextQ *
    laggedReturnCocycle q centerDifference driftNumerator scale

theorem gaugedReturnCocycle_mulVec
    {q nextQ centerDifference driftNumerator scale numerator denominator
      targetNumerator targetDenominator content : ℚ}
    (q_ne : q ≠ 0)
    (denominator_eq :
      content * targetDenominator =
        centerDifference * numerator + driftNumerator * denominator)
    (difference :
      q ^ 2 * content * targetNumerator - content * targetDenominator =
        scale * (1 - q) * numerator) :
    gaugedReturnCocycle q nextQ centerDifference driftNumerator scale *ᵥ
        returnWaitFrame q numerator denominator =
      (q ^ 2 * content) •
        returnWaitFrame nextQ targetNumerator targetDenominator := by
  rw [gaugedReturnCocycle, ← Matrix.mulVec_mulVec,
    laggedReturnCocycle_mulVec denominator_eq difference,
    Matrix.mulVec_smul, returnWaitFrameChange_mulVec nextQ _ _ q_ne]

private theorem odd_of_isCoprime_of_even_left
    {left right : ℤ} (coprime : IsCoprime left right) (left_even : Even left) :
    Odd right := by
  rw [← Int.not_even_iff_odd]
  intro right_even
  obtain ⟨leftCoefficient, rightCoefficient, bezout⟩ := coprime
  have two_dvd_one : (2 : ℤ) ∣ 1 := by
    rw [← bezout]
    exact dvd_add
      (left_even.two_dvd.mul_left leftCoefficient)
      (right_even.two_dvd.mul_left rightCoefficient)
  norm_num at two_dvd_one

/-- In the even-resultant stratum, maximal cancellation has an odd target numerator and hence
cannot be terminal. -/
theorem PrimitiveEndpointReduction.maximalCancellation_targetNumerator_odd
    {prime wait : Nat}
    {centerNumerator driftNumerator scale : ℤ}
    {source target : ℤ × ℤ} {content complement : ℤ}
    (prime_odd : Odd prime)
    (reduction : PrimitiveEndpointReduction prime 2 centerNumerator
      driftNumerator scale wait source target content)
    (split : SmithRubanSplit (driftNumerator * scale)
      ((prime : ℤ) ^ wait - 1) content complement)
    (reset_even : Even (centerNumerator + driftNumerator - scale))
    (maximal : split.v = 1) :
    Odd target.1 := by
  let q : ℤ := (prime : ℤ) ^ wait
  let centerDifference := centerNumerator - scale
  let quotient :=
    maximalCancellationQuotient q scale split.eta source.2 target.2
  have q_odd : Odd q := by
    dsimp [q]
    exact_mod_cast prime_odd.pow
  have shift_even : Even (q - 1) :=
    q_odd.sub_odd ⟨0, by ring⟩
  have maximal_equations := reduction.maximalCancellation split maximal
  change source.1 = (q - 1) * quotient ∧
    split.eta * target.1 =
      driftNumerator * quotient + centerDifference * split.eta * target.2 at maximal_equations
  have source_even : Even source.1 := by
    rw [maximal_equations.1]
    exact shift_even.mul_right quotient
  have source_denominator_odd : Odd source.2 :=
    odd_of_isCoprime_of_even_left reduction.source_coprime source_even
  have u_eq : split.u = q - 1 := by
    have shift_eq := split.shift_eq
    change q - 1 = split.u * split.v at shift_eq
    rw [maximal, mul_one] at shift_eq
    exact shift_eq.symm
  have u_even : Even split.u := u_eq.symm ▸ shift_even
  have theta_odd : Odd split.theta :=
    odd_of_isCoprime_of_even_left split.u_coprime_theta u_even
  have eta_ne : split.eta ≠ 0 := by
    intro eta_zero
    apply reduction.content_ne
    rw [split.content_eq, eta_zero, zero_mul]
  have target_eq :
      target.1 = split.theta * source.2 +
        (driftNumerator * q ^ 2 + centerDifference) * target.2 := by
    apply mul_left_cancel₀ eta_ne
    calc
      split.eta * target.1 =
          driftNumerator * quotient +
            centerDifference * split.eta * target.2 := maximal_equations.2
      _ = split.eta *
          (split.theta * source.2 +
            (driftNumerator * q ^ 2 + centerDifference) * target.2) := by
        dsimp [quotient, maximalCancellationQuotient]
        linear_combination source.2 * split.fixed_eq
  have coefficient_even :
      Even (driftNumerator * q ^ 2 + centerDifference) := by
    have fixed_sum_even : Even (driftNumerator + centerDifference) := by
      convert reset_even using 1
      dsimp [centerDifference]
      ring
    have square_shift_even : Even (q ^ 2 - 1) :=
      q_odd.pow.sub_odd ⟨0, by ring⟩
    rw [show
      driftNumerator * q ^ 2 + centerDifference =
        (driftNumerator + centerDifference) + driftNumerator * (q ^ 2 - 1) by ring]
    exact fixed_sum_even.add (square_shift_even.mul_left driftNumerator)
  rw [target_eq]
  exact (theta_odd.mul source_denominator_odd).add_even
    (coefficient_even.mul_right target.2)

/-- A maximal Smith allocation forces the following allocation onto the even, hence
nonmaximal, side of the split. -/
theorem PrimitiveEndpointReduction.maximalCancellation_next_v_even
    {prime wait nextWait : Nat}
    {centerNumerator driftNumerator scale : ℤ}
    {source target nextTarget : ℤ × ℤ}
    {content complement nextContent nextComplement : ℤ}
    (prime_odd : Odd prime)
    (reduction : PrimitiveEndpointReduction prime 2 centerNumerator
      driftNumerator scale wait source target content)
    (split : SmithRubanSplit (driftNumerator * scale)
      ((prime : ℤ) ^ wait - 1) content complement)
    (nextReduction : PrimitiveEndpointReduction prime 2 centerNumerator
      driftNumerator scale nextWait target nextTarget nextContent)
    (nextSplit : SmithRubanSplit (driftNumerator * scale)
      ((prime : ℤ) ^ nextWait - 1) nextContent nextComplement)
    (reset_even : Even (centerNumerator + driftNumerator - scale))
    (maximal : split.v = 1) :
    Even nextSplit.v := by
  have target_numerator_odd :=
    reduction.maximalCancellation_targetNumerator_odd prime_odd split reset_even maximal
  have next_power_odd : Odd ((prime : ℤ) ^ nextWait) := by
    exact_mod_cast prime_odd.pow
  have next_shift_even : Even ((prime : ℤ) ^ nextWait - 1) :=
    next_power_odd.sub_odd ⟨0, by ring⟩
  have denominator_product_odd : Odd
      ((prime : ℤ) ^ (2 * nextWait) * (nextContent * nextTarget.2)) := by
    rw [nextReduction.step.denominator]
    exact target_numerator_odd.sub_even
      ((next_shift_even.mul_left scale).mul_right target.2)
  have prequotient_odd : Odd (nextContent * nextTarget.2) :=
    (Int.odd_mul.mp denominator_product_odd).2
  have content_odd : Odd nextContent := (Int.odd_mul.mp prequotient_odd).1
  have u_odd : Odd nextSplit.u := by
    rw [nextSplit.content_eq] at content_odd
    exact (Int.odd_mul.mp content_odd).2
  have split_product_even : Even (nextSplit.u * nextSplit.v) := by
    rw [← nextSplit.shift_eq]
    exact next_shift_even
  exact (Int.even_mul.mp split_product_even).resolve_left
    (Int.not_even_iff_odd.mpr u_odd)

end MatrixMortality.ReturnGuard
