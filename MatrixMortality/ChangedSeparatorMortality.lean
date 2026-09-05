import MatrixMortality.ChangedSeparatorTailMoments
import MatrixMortality.ChangedSeparatorZeroMoment
import MatrixMortality.ChangedSeparatorMomentOne
import MatrixMortality.ChangedSeparatorMomentTwo
import MatrixMortality.SingularReturnFamily

/-!
# Mortality of the rank-nine changed-separator pair

The nonzero geometric eigenline excludes pure transition zeros. Singular return compression then
reduces the physical pair to four interface roles: the paired toggle, the two paired data
matrices, and the changed rank-one separator. The separator's normalized row has the same zero
language as the ordinary paired boundary, and canonical denominator clearing preserves the
result over the integers.
-/

namespace MatrixMortality

open scoped Matrix

namespace ChangedSeparatorRealization

/-- Final coordinate basis spanning the geometric tail. -/
def tailBasis : Fin 9 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- The physical transition scales its geometric tail basis. -/
theorem transition_mulVec_tailBasis (β : Nat) (body : List TagLetter) :
    transition β body *ᵥ tailBasis = tailEigenvalue β body • tailBasis := by
  funext i
  fin_cases i <;>
    simp [transition, chainTransition, tailEigenvalue, tailBasis,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Every transition power scales the geometric tail basis by the matching eigenvalue power. -/
theorem transition_pow_mulVec_tailBasis (β : Nat) (body : List TagLetter) (n : Nat) :
    transition β body ^ n *ᵥ tailBasis =
      tailEigenvalue β body ^ n • tailBasis := by
  induction n with
  | zero => simp
  | succ n induction =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, transition_mulVec_tailBasis,
        Matrix.mulVec_smul, induction, smul_smul]
      simp [pow_succ, mul_comm]

/-- No pure word in the transition generator vanishes. -/
theorem transition_pow_ne_zero (β : Nat) (body : List TagLetter) (n : Nat) :
    transition β body ^ n ≠ 0 := by
  intro power_zero
  have action := transition_pow_mulVec_tailBasis β body n
  rw [power_zero, Matrix.zero_mulVec] at action
  have tail_entry := congrFun action 8
  apply pow_ne_zero n (tailEigenvalue_ne_zero β body)
  simpa [tailBasis] using tail_entry.symm

/-- Nonzero scalar carried by the changed tail row. -/
def separatorScale (β : Nat) (body : List TagLetter) : ℚ :=
  2 * ChangedSeparatorTail.lowerCScale β body *
      (ChangedSeparatorTail.lowerCScale β body - 3) /
    denominator β body

theorem separatorScale_ne_zero (β : Nat) (body : List TagLetter) :
    separatorScale β body ≠ 0 := by
  have scale_ne : ChangedSeparatorTail.lowerCScale β body ≠ 0 := by
    linarith [ChangedSeparatorTail.lowerCScale_gt_three β body]
  have gap_ne : ChangedSeparatorTail.lowerCScale β body - 3 ≠ 0 := by
    linarith [ChangedSeparatorTail.lowerCScale_gt_three β body]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) scale_ne) gap_ne)
    (denominator_ne_zero β body)

/-- The realized tail row is a nonzero scaling of the injective uniform-tail boundary. -/
theorem chainTailRow_eq_separatorScale_smul (β : Nat) (body : List TagLetter) :
    chainTailRow (widthScale β) (ChangedSeparatorTail.lowerCCode β body)
        (ChangedSeparatorTail.lowerCScale β body) =
      separatorScale β body •
        ChangedSeparatorTail.uniformTailRow
          (ChangedSeparatorTail.nearyTailRatio β body) := by
  have gap_ne : ChangedSeparatorTail.lowerCScale β body - 3 ≠ 0 := by
    linarith [ChangedSeparatorTail.lowerCScale_gt_three β body]
  funext i
  fin_cases i
  · simp [chainTailRow, separatorScale, denominator,
      ChangedSeparatorTail.uniformTailRow]
  all_goals
    simp [chainTailRow, separatorScale, denominator,
      ChangedSeparatorTail.uniformTailRow, ChangedSeparatorTail.nearyTailRatio]
    field_simp [gap_ne]


/-- Rank-one changed separator normalized to its same-zero row. -/
def tiltedSeparator (β : Nat) (body : List TagLetter) : Square (Fin 4) ℚ :=
  Matrix.vecMulVec (pairedTrailingToggleColumn ℚ β)
    (ChangedSeparatorTail.uniformTailRow
      (ChangedSeparatorTail.nearyTailRatio β body))

/-- The realized separator is a nonzero scaling of its normalized same-zero separator. -/
theorem separator_eq_separatorScale_smul (β : Nat) (body : List TagLetter) :
    separator β body = separatorScale β body • tiltedSeparator β body := by
  rw [separator, chainTailSeparator, chainTailColumn_eq_pairedTrailingToggleColumn,
    chainTailRow_eq_separatorScale_smul]
  ext i j
  simp [tiltedSeparator, Matrix.vecMulVec]
  ring


/-- Normalized four-generator interface family carried by the return sequence. -/
def tiltedFamily (β : Nat) (body : List TagLetter) :
    Option PairedControl → Square (Fin 4) ℚ :=
  separatedGenerator (tiltedSeparator β body) (pairedGenerator ℚ β body)

/-- Nonzero scalar suppressed when each return is reduced to its finite role. -/
def returnScale (β : Nat) (body : List TagLetter) : Nat → ℚ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | Nat.succ (Nat.succ (Nat.succ n)) =>
      tailEigenvalue β body ^ n * separatorScale β body

theorem returnScale_ne_zero (β : Nat) (body : List TagLetter) (n : Nat) :
    returnScale β body n ≠ 0 := by
  cases n with
  | zero => simp [returnScale]
  | succ n =>
      cases n with
      | zero => simp [returnScale]
      | succ n =>
          cases n with
          | zero => simp [returnScale]
          | succ n =>
              exact mul_ne_zero (pow_ne_zero n (tailEigenvalue_ne_zero β body))
                (separatorScale_ne_zero β body)

/-- Every return is a nonzero scaling of exactly one finite paired role. -/
theorem returnMatrix_eq_scaled_tiltedFamily
    (β : Nat) (β_pos : 0 < β) (body : List TagLetter) (b_mem : .b ∈ body)
    (n : Nat) :
    ReturnFamily.returnMatrix (transition β body) (input β body) (output β body) n =
      returnScale β body n • tiltedFamily β body (returnLabel n) := by
  cases n with
  | zero =>
      simpa [ReturnFamily.returnMatrix, returnScale, tiltedFamily, returnLabel,
        separatedGenerator, pairedGenerator] using zero_moment β β_pos body b_mem
  | succ n =>
      cases n with
      | zero =>
          simpa [ReturnFamily.returnMatrix, returnScale, tiltedFamily, returnLabel,
            separatedGenerator, pairedGenerator] using moment_one β β_pos body b_mem
      | succ n =>
          cases n with
          | zero =>
              simpa [ReturnFamily.returnMatrix, returnScale, tiltedFamily, returnLabel,
                separatedGenerator, pairedGenerator] using moment_two β β_pos body b_mem
          | succ n =>
              change
                output β body * transition β body ^ (n + 1 + 1 + 1) * input β body = _
              rw [show n + 1 + 1 + 1 = n + 3 by omega,
                moment_add_three β β_pos body b_mem n,
                separator_eq_separatorScale_smul]
              simp [returnScale, returnLabel, tiltedFamily, separatedGenerator, smul_smul]

/-- The infinite return alphabet is mortal exactly when its finite normalized role family is. -/
theorem returnFamily_mortal_iff_tiltedFamily
    (β : Nat) (β_pos : 0 < β) (body : List TagLetter) (b_mem : .b ∈ body) :
    IsMortal
        (ReturnFamily.returnMatrix (transition β body) (input β body) (output β body)) ↔
      IsMortal (tiltedFamily β body) := by
  have returns_eq :
      ReturnFamily.returnMatrix (transition β body) (input β body) (output β body) =
        fun n => returnScale β body n • tiltedFamily β body (returnLabel n) := by
    funext n
    exact returnMatrix_eq_scaled_tiltedFamily β β_pos body b_mem n
  rw [returns_eq]
  have scaling :=
    isMortal_smulMatrix_iff (returnScale β body) (returnScale_ne_zero β body)
      (tiltedFamily β body ∘ returnLabel)
  rw [show (fun n => returnScale β body n • tiltedFamily β body (returnLabel n)) =
      fun n => returnScale β body n • (tiltedFamily β body ∘ returnLabel) n by rfl,
    scaling]
  exact ReturnFamily.isMortal_comp_rightInverse_iff
    (tiltedFamily β body) returnLabel returnIndex returnLabel_returnIndex

/-- The ordinary paired trailing-toggle coefficient does not vanish on the empty word. -/
theorem pairedTrailingToggleCoefficient_nil_ne_zero
    (β : Nat) (body : List TagLetter) :
    pairedTrailingToggleCoefficient ℚ β body [] ≠ 0 := by
  rw [pairedTrailingToggleCoefficient_eq_append]
  simp only [List.nil_append, pairedCoefficient, pairedProduct, wordProduct_cons,
    wordProduct_nil, mul_one, pairedGenerator]
  have marker_ne : (ternaryCode (nearyMarker β) : ℚ) ≠ 0 := by
    exact_mod_cast ternaryCode_nearyMarker_ne_zero β
  simpa [pairedRow, pairedToggleMatrix_eq_explicit, pairedColumn, phaseVector,
    controllerVector, pairControllerEquiv, sideTerminalColumn_zero,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using marker_ne

/-- The tilted trailing-toggle coefficient does not vanish on the empty word. -/
theorem tiltedTrailingToggleCoefficient_nil_ne_zero
    (β : Nat) (body : List TagLetter) :
    ChangedSeparatorTail.tiltedTrailingToggleCoefficient
        (ChangedSeparatorTail.nearyTailRatio β body) β body [] ≠ 0 := by
  intro tilted_zero
  have ordinary_zero :=
    (ChangedSeparatorTail.nearyTiltedTrailingToggleCoefficient_eq_zero_iff
      β body []).mp tilted_zero
  exact pairedTrailingToggleCoefficient_nil_ne_zero β body ordinary_zero

/-- The normalized changed-separator family has exactly the ordinary paired zero language. -/
theorem tiltedFamily_mortal_iff_paired_zero (β : Nat) (body : List TagLetter) :
    IsMortal (tiltedFamily β body) ↔
      WordSeries.HasNonemptyZero (pairedCoefficient ℚ β body) := by
  rw [tiltedFamily, tiltedSeparator, mortal_adjoin_outer_iff]
  change
    WordSeries.HasZero
        (ChangedSeparatorTail.tiltedTrailingToggleCoefficient
          (ChangedSeparatorTail.nearyTailRatio β body) β body) ↔ _
  rw [← WordSeries.hasNonemptyZero_iff_hasZero_of_nil_ne _
      (tiltedTrailingToggleCoefficient_nil_ne_zero β body),
    ChangedSeparatorTail.nearyTiltedTrailingToggle_hasNonemptyZero_iff,
    pairedTrailingToggle_hasNonemptyZero_iff]

/-- The rational rank-nine pair is mortal exactly when the paired scalar series vanishes. -/
theorem generator_mortal_iff_paired_zero
    (β : Nat) (β_pos : 0 < β) (body : List TagLetter) (b_mem : .b ∈ body) :
    IsMortal (generator β body) ↔
      WordSeries.HasNonemptyZero (pairedCoefficient ℚ β body) := by
  rw [generator, cut,
    ReturnFamily.pairGenerator_isMortal_iff_returnFamily
      (transition β body) (input β body) (output β body)
        (transition_pow_ne_zero β body),
    returnFamily_mortal_iff_tiltedFamily β β_pos body b_mem,
    tiltedFamily_mortal_iff_paired_zero]

/-- Canonical denominator clearing preserves the exact scalar-zero criterion. -/
theorem integralGenerator_mortal_iff_paired_zero
    (β : Nat) (β_pos : 0 < β) (body : List TagLetter) (b_mem : .b ∈ body) :
    IsMortal (integralGenerator β body) ↔
      WordSeries.HasNonemptyZero (pairedCoefficient ℚ β body) := by
  rw [integralGenerator, clearRationalFamily_isMortal_iff,
    generator_mortal_iff_paired_zero β β_pos body b_mem]

/-- Every regular Neary source is compiled to an equivalent pair of `9 × 9` integer matrices. -/
theorem integralGenerator_mortal_iff_tagHaltsFrom
    (β : Nat) (body : List TagLetter) (β_large : 2 < β)
    (body_long : β - 1 ≤ body.length) (body_divisible : β - 1 ∣ body.length)
    (b_mem : .b ∈ body) :
    IsMortal (integralGenerator β body) ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  rw [integralGenerator_mortal_iff_paired_zero β (by omega) body b_mem,
    paired_zero_rat_iff_terminal_match]
  exact terminal_match_iff_tagHaltsFrom β body β_large body_long body_divisible

theorem integral_generator_count : Fintype.card (Option Unit) = 2 := by decide

end ChangedSeparatorRealization

end MatrixMortality
