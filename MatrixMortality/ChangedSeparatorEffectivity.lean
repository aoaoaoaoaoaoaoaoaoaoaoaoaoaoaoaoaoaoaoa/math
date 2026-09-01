import MatrixMortality.ChangedSeparatorMortality
import MatrixMortality.Undecidability.NearyProblems

/-!
# Effective rank-nine changed-separator pair

The rational chain chart is evaluated in primitive-recursive unreduced fractions. Each of its two
finite matrices is then cleared with one common nonzero denominator. This gives an explicit
primitive-recursive integer emitter without computing normalized rational numerators or gcds.
-/

namespace MatrixMortality

open scoped Matrix

namespace ChangedSeparatorRealization

private abbrev Body := List TagLetter
private abbrev Effective := EffectiveFraction Body

private noncomputable def effectiveWidthScale (β : Nat) : Effective :=
  EffectiveFraction.ofNat (3 ^ β)

private noncomputable def effectiveLowerCCode (β : Nat) : Effective :=
  EffectiveFraction.ofNatFunction
    (fun body => ternaryCode (nearyLower β body (.rule .c)))
    (ternaryCode_primrec.comp (Undecidability.nearyLower_primrec β (.rule .c)))

private noncomputable def effectiveLowerCScale (β : Nat) : Effective :=
  EffectiveFraction.ofNatFunction
    (fun body => 3 ^ (nearyLower β body (.rule .c)).length)
    (MatrixMortality.Primrec.nat_pow.comp (Primrec.const 3)
      (Primrec.list_length.comp (Undecidability.nearyLower_primrec β (.rule .c))))

private theorem effectiveWidthScale_value (β : Nat) (body : Body) :
    (effectiveWidthScale β).value body = widthScale β := by
  simp [effectiveWidthScale, widthScale]

private theorem effectiveLowerCCode_value (β : Nat) (body : Body) :
    (effectiveLowerCCode β).value body = ChangedSeparatorTail.lowerCCode β body := by
  simp [effectiveLowerCCode, ChangedSeparatorTail.lowerCCode,
    nearySideLowerC]

private theorem effectiveLowerCScale_value (β : Nat) (body : Body) :
    (effectiveLowerCScale β).value body = ChangedSeparatorTail.lowerCScale β body := by
  simp [effectiveLowerCScale, ChangedSeparatorTail.lowerCScale,
    nearySideLowerCScale]

private theorem chainDenominator_value (ρ V K : Effective) (body : Body) :
    (chainDenominator ρ V K).value body =
      chainDenominator (ρ.value body) (V.value body) (K.value body) := by
  simp [chainDenominator]

private theorem chainTailEigenvalue_value (ρ V K : Effective) (body : Body) :
    (chainTailEigenvalue ρ V K).value body =
      chainTailEigenvalue (ρ.value body) (V.value body) (K.value body) := by
  simp [chainTailEigenvalue, chainDenominator_value]

private theorem chainTransition_value (ρ V K : Effective) (body : Body)
    (row column : Fin 9) :
    (chainTransition ρ V K row column).value body =
      chainTransition (ρ.value body) (V.value body) (K.value body) row column := by
  fin_cases row <;> fin_cases column <;>
    simp [chainTransition, chainTailEigenvalue_value]

set_option maxHeartbeats 800000 in
private theorem chainInput_value (ρ V K : Effective) (body : Body)
    (row : Fin 9) (column : Fin 4) :
    (chainInput ρ V K row column).value body =
      chainInput (ρ.value body) (V.value body) (K.value body) row column := by
  fin_cases row <;> fin_cases column <;>
    simp [chainInput]

set_option maxHeartbeats 800000 in
private theorem chainOutput_value (ρ V K : Effective) (body : Body)
    (row : Fin 4) (column : Fin 9) :
    (chainOutput ρ V K row column).value body =
      chainOutput (ρ.value body) (V.value body) (K.value body) row column := by
  fin_cases row <;> fin_cases column <;>
    simp [chainOutput]

private noncomputable def effectiveTransition (β : Nat) : Square (Fin 9) Effective :=
  chainTransition (effectiveWidthScale β) (effectiveLowerCCode β)
    (effectiveLowerCScale β)

private noncomputable def effectiveInput (β : Nat) : Matrix (Fin 9) (Fin 4) Effective :=
  chainInput (effectiveWidthScale β) (effectiveLowerCCode β)
    (effectiveLowerCScale β)

private noncomputable def effectiveOutput (β : Nat) : Matrix (Fin 4) (Fin 9) Effective :=
  chainOutput (effectiveWidthScale β) (effectiveLowerCCode β)
    (effectiveLowerCScale β)

private noncomputable def effectiveCutEntry (β : Nat) (row column : Fin 9) : Effective :=
  effectiveInput β row 0 * effectiveOutput β 0 column +
    effectiveInput β row 1 * effectiveOutput β 1 column +
    effectiveInput β row 2 * effectiveOutput β 2 column +
    effectiveInput β row 3 * effectiveOutput β 3 column

private theorem effectiveTransition_value (β : Nat) (body : Body) (row column : Fin 9) :
    (effectiveTransition β row column).value body = transition β body row column := by
  simp [effectiveTransition, transition, chainTransition_value,
    effectiveWidthScale_value, effectiveLowerCCode_value, effectiveLowerCScale_value]

private theorem effectiveInput_value (β : Nat) (body : Body)
    (row : Fin 9) (column : Fin 4) :
    (effectiveInput β row column).value body = input β body row column := by
  simp [effectiveInput, input, chainInput_value,
    effectiveWidthScale_value, effectiveLowerCCode_value, effectiveLowerCScale_value]

private theorem effectiveOutput_value (β : Nat) (body : Body)
    (row : Fin 4) (column : Fin 9) :
    (effectiveOutput β row column).value body = output β body row column := by
  simp [effectiveOutput, output, chainOutput_value,
    effectiveWidthScale_value, effectiveLowerCCode_value, effectiveLowerCScale_value]

private theorem effectiveCutEntry_value (β : Nat) (body : Body) (row column : Fin 9) :
    (effectiveCutEntry β row column).value body = cut β body row column := by
  simp [effectiveCutEntry, effectiveInput_value, effectiveOutput_value, cut,
    Matrix.mul_apply, Fin.sum_univ_succ]
  ring

/-- Unreduced effective fraction denoting one entry of the rational changed-separator pair. -/
noncomputable def effectiveFractionGenerator (β : Nat) (label : Option Unit)
    (row column : Fin 9) : EffectiveFraction (List TagLetter) :=
  match label with
  | none => effectiveCutEntry β row column
  | some _ => effectiveTransition β row column

theorem effectiveFractionGenerator_value (β : Nat) (body : List TagLetter)
    (label : Option Unit) (row column : Fin 9) :
    (effectiveFractionGenerator β label row column).value body =
      generator β body label row column := by
  cases label with
  | none => exact effectiveCutEntry_value β body row column
  | some point =>
      cases point
      exact effectiveTransition_value β body row column

/-- Row-major flattening of the effective pair's entries. -/
noncomputable def effectiveFlatGenerator (β : Nat) (label : Option Unit) :
    Fin 81 → EffectiveFraction (List TagLetter) :=
  fun index =>
    let position := (@finProdFinEquiv 9 9).symm index
    effectiveFractionGenerator β label position.1 position.2

/-- A single nonzero common denominator for one effective `9 × 9` generator. -/
noncomputable def effectiveClearing (β : Nat) (label : Option Unit) :
    ClearedFin (effectiveFlatGenerator β label) :=
  clearFin (effectiveFlatGenerator β label)

/-- Primitive-recursive integer entries obtained by certified unreduced denominator clearing. -/
noncomputable def effectiveIntegralGenerator (β : Nat) (body : List TagLetter) :
    Option Unit → Square (Fin 9) Int :=
  fun label row column =>
    ((effectiveClearing β label).entry
      (@finProdFinEquiv 9 9 (row, column))).value body

/-- The emitted integer matrix is a nonzero rational scaling of the exact chart generator. -/
theorem castMatrix_effectiveIntegralGenerator (β : Nat) (body : List TagLetter)
    (label : Option Unit) :
    castMatrix (effectiveIntegralGenerator β body label) =
      ((effectiveClearing β label).denominator.value body : ℚ) •
        generator β body label := by
  ext row column
  change
    (((effectiveClearing β label).entry
        (@finProdFinEquiv 9 9 (row, column))).value body : ℚ) = _
  rw [(effectiveClearing β label).cast_entry
    (@finProdFinEquiv 9 9 (row, column)) body]
  simp [effectiveFlatGenerator, effectiveFractionGenerator_value]

private theorem effectiveClearing_denominator_ne_zero (β : Nat) (body : List TagLetter)
    (label : Option Unit) :
    ((effectiveClearing β label).denominator.value body : ℚ) ≠ 0 := by
  exact_mod_cast (effectiveClearing β label).denominator_ne_zero body

/-- Effective unreduced clearing preserves and reflects mortality of the rational pair. -/
theorem effectiveIntegralGenerator_mortal_iff_generator (β : Nat)
    (body : List TagLetter) :
    IsMortal (effectiveIntegralGenerator β body) ↔ IsMortal (generator β body) := by
  have cast_family :
      castMatrix ∘ effectiveIntegralGenerator β body =
        fun label =>
          ((effectiveClearing β label).denominator.value body : ℚ) •
            generator β body label := by
    funext label
    exact castMatrix_effectiveIntegralGenerator β body label
  calc
    IsMortal (effectiveIntegralGenerator β body) ↔
        IsMortal (castMatrix ∘ effectiveIntegralGenerator β body) :=
      (isMortal_cast_iff (effectiveIntegralGenerator β body)).symm
    _ ↔ IsMortal
          (fun label =>
            ((effectiveClearing β label).denominator.value body : ℚ) •
              generator β body label) := by rw [cast_family]
    _ ↔ IsMortal (generator β body) :=
      isMortal_smulMatrix_iff
        (fun label => ((effectiveClearing β label).denominator.value body : ℚ))
        (effectiveClearing_denominator_ne_zero β body) (generator β body)

/-- The primitive-recursive integer pair has exactly the restricted-tag halting language. -/
theorem effectiveIntegralGenerator_mortal_iff_tagHaltsFrom
    (β : Nat) (body : List TagLetter) (β_large : 2 < β)
    (body_long : β - 1 ≤ body.length) (body_divisible : β - 1 ∣ body.length)
    (b_mem : .b ∈ body) :
    IsMortal (effectiveIntegralGenerator β body) ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  rw [effectiveIntegralGenerator_mortal_iff_generator,
    generator_mortal_iff_paired_zero β (by omega) body b_mem,
    paired_zero_rat_iff_terminal_match]
  exact terminal_match_iff_tagHaltsFrom β body β_large body_long body_divisible

/-- Every fixed entry of the effective integer pair is primitive recursive in the body. -/
theorem effectiveIntegralGenerator_entry_primrec (β : Nat) (label : Option Unit)
    (row column : Fin 9) :
    Primrec fun body => effectiveIntegralGenerator β body label row column :=
  ((effectiveClearing β label).entry
    (@finProdFinEquiv 9 9 (row, column))).value_primrec

end ChangedSeparatorRealization

end MatrixMortality
