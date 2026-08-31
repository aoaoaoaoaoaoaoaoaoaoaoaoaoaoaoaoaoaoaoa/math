import MatrixMortality.NearySideNormal
import MatrixMortality.PairedBinaryPrefixTax

/-!
# Tilted same-zero separator boundary

The side-normal ternary representation remains injective after adding a sufficiently negative
multiple of its length scale. A uniform row on the three non-affine paired coordinates therefore
changes every nonzero coefficient while preserving its zero language exactly.
-/

namespace MatrixMortality

open scoped Matrix

namespace ChangedSeparatorTail

/-- Affine ternary evaluation with a common tail value `ratio`. -/
def tiltedTernaryCode (ratio : ℚ) (word : List Bool) : ℚ :=
  ternaryCode word + ratio * 3 ^ word.length

/-- Every nonzero ternary digit contributes at least the all-ones word of the same length. -/
theorem ternaryScale_le_two_mul_code_add_one (word : List Bool) :
    3 ^ word.length ≤ 2 * ternaryCode word + 1 := by
  induction word with
  | nil => norm_num
  | cons bit tail induction =>
      rw [ternaryCode_cons]
      simp only [List.length_cons, pow_succ]
      cases bit <;> simp [ternaryDigit] <;> omega

/-- Below `-3/2`, successive length bands of the tilted ternary code are disjoint. -/
theorem tiltedTernaryCode_lt_of_length_lt
    (ratio : ℚ) (ratio_lt : ratio < -3 / 2)
    (short long : List Bool) (length_lt : short.length < long.length) :
    tiltedTernaryCode ratio long < tiltedTernaryCode ratio short := by
  have short_scale_positive : (0 : ℚ) < 3 ^ short.length := by positivity
  have ratio_add_one_negative : ratio + 1 < 0 := by linarith
  have long_code_lt :
      (ternaryCode long : ℚ) < 3 ^ long.length := by
    exact_mod_cast ternaryCode_lt_pow_length long
  have scale_nat : 3 ^ (short.length + 1) ≤ 3 ^ long.length := by
    exact Nat.pow_le_pow_right (by norm_num) length_lt
  have scale : (3 : ℚ) * 3 ^ short.length ≤ 3 ^ long.length := by
    have scale_cast :
        (3 : ℚ) ^ (short.length + 1) ≤ 3 ^ long.length := by
      exact_mod_cast scale_nat
    simpa [pow_succ, mul_comm] using scale_cast
  have scaled :
      (ratio + 1) * 3 ^ long.length ≤
        (ratio + 1) * ((3 : ℚ) * 3 ^ short.length) :=
    mul_le_mul_of_nonpos_left scale ratio_add_one_negative.le
  have long_upper :
      tiltedTernaryCode ratio long < (ratio + 1) * 3 ^ long.length := by
    rw [tiltedTernaryCode]
    nlinarith
  have separated :
      (ratio + 1) * ((3 : ℚ) * 3 ^ short.length) <
        ratio * 3 ^ short.length := by
    nlinarith
  have short_lower :
      ratio * 3 ^ short.length ≤ tiltedTernaryCode ratio short := by
    rw [tiltedTernaryCode]
    have code_nonnegative : (0 : ℚ) ≤ ternaryCode short := by positivity
    linarith
  calc
    tiltedTernaryCode ratio long < (ratio + 1) * 3 ^ long.length := long_upper
    _ ≤ (ratio + 1) * ((3 : ℚ) * 3 ^ short.length) := scaled
    _ < ratio * 3 ^ short.length := separated
    _ ≤ tiltedTernaryCode ratio short := short_lower

/-- A sufficiently negative common tail keeps the finite-word ternary code injective. -/
theorem tiltedTernaryCode_injective (ratio : ℚ) (ratio_lt : ratio < -3 / 2) :
    Function.Injective (tiltedTernaryCode ratio) := by
  intro first second equal
  have lengths_equal : first.length = second.length := by
    rcases lt_trichotomy first.length second.length with shorter | same | longer
    · have values_lt := tiltedTernaryCode_lt_of_length_lt ratio ratio_lt first second shorter
      exact False.elim (values_lt.ne equal.symm)
    · exact same
    · have values_lt := tiltedTernaryCode_lt_of_length_lt ratio ratio_lt second first longer
      exact False.elim (values_lt.ne equal)
  apply ternaryCode_injective
  have cast_equal : (ternaryCode first : ℚ) = ternaryCode second := by
    simpa [tiltedTernaryCode, lengths_equal] using equal
  exact_mod_cast cast_equal

/-- A row whose three phase-dependent coordinates share one common tail ratio. -/
def uniformTailRow (ratio : ℚ) : Fin 4 → ℚ := ![1, ratio, ratio, ratio]

theorem uniformTailRow_dot_phaseVector
    (ratio : ℚ) (phase : PairPhase) (vector : Fin 3 → ℚ) :
    uniformTailRow ratio ⬝ᵥ phaseVector ℚ phase vector =
      vector 0 + ratio * (vector 1 + vector 2) := by
  cases phase <;>
    simp [uniformTailRow, phaseVector, controllerVector, pairControllerEquiv,
      dotProduct, Fin.sum_univ_succ] <;>
    ring

/-- The uniform paired row evaluates a side-normal word pair by the tilted code difference. -/
theorem uniformTailRow_sidePcp
    (ratio : ℚ) (phase : PairPhase) (upper lower : List Bool) :
    uniformTailRow ratio ⬝ᵥ
        phaseVector ℚ phase
          (sidePcpMatrix ℚ upper lower *ᵥ sideTailBasis ℚ) =
      tiltedTernaryCode ratio upper - tiltedTernaryCode ratio lower := by
  rw [uniformTailRow_dot_phaseVector]
  simp [sidePcpMatrix, sideTailBasis, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, tiltedTernaryCode]
  ring

/-- The changed row has exactly the ordinary side-normal zero set. -/
theorem uniformTailRow_sidePcp_eq_zero_iff
    (ratio : ℚ) (ratio_lt : ratio < -3 / 2)
    (phase : PairPhase) (upper lower : List Bool) :
    uniformTailRow ratio ⬝ᵥ
          phaseVector ℚ phase
            (sidePcpMatrix ℚ upper lower *ᵥ sideTailBasis ℚ) = 0 ↔
      upper = lower := by
  rw [uniformTailRow_sidePcp, sub_eq_zero]
  exact (tiltedTernaryCode_injective ratio ratio_lt).eq_iff

/-- Scale of the body-dependent lower `c` word. -/
def lowerCScale (β : Nat) (body : List TagLetter) : ℚ :=
  nearySideLowerCScale β body

/-- Code of the body-dependent lower `c` word. -/
def lowerCCode (β : Nat) (body : List TagLetter) : ℚ :=
  nearySideLowerC β body

/-- Tail ratio selected by the rank-nine transfer equations. -/
def nearyTailRatio (β : Nat) (body : List TagLetter) : ℚ :=
  (lowerCScale β body - 3 * lowerCCode β body) /
    (lowerCScale β body - 3)

theorem lowerCScale_gt_three (β : Nat) (body : List TagLetter) :
    3 < lowerCScale β body := by
  rw [lowerCScale, nearySideLowerCScale_eq_nine_mul]
  have power_one : (1 : ℚ) ≤ 3 ^ (tagEncode β body).length.succ :=
    one_le_pow₀ (by norm_num)
  nlinarith

theorem five_mul_lowerCScale_sub_nine_lt_six_mul_lowerCCode
    (β : Nat) (body : List TagLetter) :
    5 * lowerCScale β body - 9 < 6 * lowerCCode β body := by
  let encoded := tagEncode β body
  have code_bound_nat := ternaryScale_le_two_mul_code_add_one encoded
  have code_bound :
      (3 : ℚ) ^ encoded.length ≤ 2 * ternaryCode encoded + 1 := by
    exact_mod_cast code_bound_nat
  rw [lowerCScale, lowerCCode, nearySideLowerCScale_eq_nine_mul,
    nearySideLowerC_eq_nine_mul_add_seven]
  change
    5 * (9 * (3 : ℚ) ^ encoded.length.succ) - 9 <
      6 * (9 * ternaryCode (true :: encoded) + 7)
  rw [ternaryCode_cons]
  norm_num [ternaryDigit, pow_succ]
  nlinarith

/-- Every Neary instance selects an injective tilted ternary tail. -/
theorem nearyTailRatio_lt_neg_three_halves (β : Nat) (body : List TagLetter) :
    nearyTailRatio β body < -3 / 2 := by
  have denominator_positive : 0 < lowerCScale β body - 3 := by
    linarith [lowerCScale_gt_three β body]
  rw [nearyTailRatio, div_lt_iff₀ denominator_positive]
  nlinarith [five_mul_lowerCScale_sub_nine_lt_six_mul_lowerCCode β body]

/-- Scalar recognized by the changed row and the ordinary paired right boundary. -/
def tiltedPairedCoefficient (ratio : ℚ) (β : Nat) (body : List TagLetter)
    (word : List PairedControl) : ℚ :=
  uniformTailRow ratio ⬝ᵥ
    pairedProduct ℚ β body word *ᵥ pairedColumn ℚ β

theorem tiltedPairedCoefficient_eq_zero_iff
    (ratio : ℚ) (ratio_lt : ratio < -3 / 2)
    (β : Nat) (body : List TagLetter) (word : List PairedControl) :
    tiltedPairedCoefficient ratio β body word = 0 ↔
      pairedCoefficient ℚ β body word = 0 := by
  rw [tiltedPairedCoefficient, pairedCoefficient,
    pairedProduct_mulVec_column]
  let decoded := decodePairedWord word
  let upper := spell (nearyUpper β) decoded ++ nearyMarker β
  let lower := spell (nearyLower β body) decoded
  have side_normal :
      sideTileProduct ℚ β body decoded *ᵥ
          sideTerminalColumn ℚ (nearyMarker β) =
        sidePcpMatrix ℚ upper lower *ᵥ sideTailBasis ℚ := by
    rw [sideTerminalColumn, Matrix.mulVec_mulVec,
      sideTileProduct_eq_sidePcpMatrix, ← sidePcpMatrix_append]
    simp [upper, lower]
  rw [show decodePairedWord word = decoded by rfl, side_normal]
  rw [uniformTailRow_sidePcp_eq_zero_iff ratio ratio_lt]
  rw [pairedRow_dot_phaseVector]
  change upper = lower ↔
    (sidePcpMatrix ℚ upper lower *ᵥ sideTailBasis ℚ) 0 = 0
  rw [sidePcpMatrix_mulVec_sideTailBasis_head_rat, sub_eq_zero, Nat.cast_inj]
  exact ternaryCode_injective.eq_iff.symm

/-- Pointwise same-zero equivalence at the Neary-selected ratio. -/
theorem nearyTiltedPairedCoefficient_eq_zero_iff
    (β : Nat) (body : List TagLetter) (word : List PairedControl) :
    tiltedPairedCoefficient (nearyTailRatio β body) β body word = 0 ↔
      pairedCoefficient ℚ β body word = 0 :=
  tiltedPairedCoefficient_eq_zero_iff
    (nearyTailRatio β body) (nearyTailRatio_lt_neg_three_halves β body) β body word

/-- Changed-row coefficient after absorbing one trailing phase toggle. -/
def tiltedTrailingToggleCoefficient (ratio : ℚ) (β : Nat)
    (body : List TagLetter) (word : List PairedControl) : ℚ :=
  uniformTailRow ratio ⬝ᵥ
    pairedProduct ℚ β body word *ᵥ pairedTrailingToggleColumn ℚ β

theorem tiltedTrailingToggleCoefficient_eq_append
    (ratio : ℚ) (β : Nat) (body : List TagLetter) (word : List PairedControl) :
    tiltedTrailingToggleCoefficient ratio β body word =
      tiltedPairedCoefficient ratio β body (word ++ [.toggle]) := by
  rw [tiltedTrailingToggleCoefficient, tiltedPairedCoefficient,
    pairedTrailingToggleColumn, pairedProduct, pairedProduct, wordProduct_append]
  simp only [wordProduct_cons, wordProduct_nil, mul_one, pairedGenerator]
  rw [Matrix.mulVec_mulVec]

/-- The changed trailing-toggle separator preserves every control word's zero value exactly. -/
theorem nearyTiltedTrailingToggleCoefficient_eq_zero_iff
    (β : Nat) (body : List TagLetter) (word : List PairedControl) :
    tiltedTrailingToggleCoefficient (nearyTailRatio β body) β body word = 0 ↔
      pairedTrailingToggleCoefficient ℚ β body word = 0 := by
  rw [tiltedTrailingToggleCoefficient_eq_append,
    nearyTiltedPairedCoefficient_eq_zero_iff,
    pairedTrailingToggleCoefficient_eq_append]

/-- The changed rank-one separator preserves existential zero reachability. -/
theorem nearyTiltedTrailingToggle_hasNonemptyZero_iff
    (β : Nat) (body : List TagLetter) :
    WordSeries.HasNonemptyZero
        (tiltedTrailingToggleCoefficient (nearyTailRatio β body) β body) ↔
      WordSeries.HasNonemptyZero
        (pairedTrailingToggleCoefficient ℚ β body) := by
  constructor
  · rintro ⟨word, word_nonempty, zero⟩
    exact ⟨word, word_nonempty,
      (nearyTiltedTrailingToggleCoefficient_eq_zero_iff β body word).mp zero⟩
  · rintro ⟨word, word_nonempty, zero⟩
    exact ⟨word, word_nonempty,
      (nearyTiltedTrailingToggleCoefficient_eq_zero_iff β body word).mpr zero⟩

end ChangedSeparatorTail

end MatrixMortality
