import MatrixMortality.AsymmetricSeparatorEvaluation
import MatrixMortality.EffectiveMatrix
import MatrixMortality.Undecidability.NearyProblems

/-!
# Primitive-recursive integer eight-state pair

The body code and length scale are primitive recursive. Evaluating the fixed chart in
unreduced fractions and clearing its two matrices therefore gives a total primitive-recursive
integer reduction. Source restrictions enter only its correctness theorem.
-/

namespace MatrixMortality.AsymmetricSeparatorRealization

private abbrev Body := List TagLetter
private abbrev Effective := EffectiveFraction Body

private noncomputable def effectiveWidth (β : Nat) : Effective := EffectiveFraction.ofNat (3 ^ β)

private noncomputable def effectiveBodyCode (β : Nat) : Effective :=
  EffectiveFraction.ofNatFunction (fun body => ternaryCode (tagEncode β body))
    (ternaryCode_primrec.comp (tagEncode_primrec β))

private noncomputable def effectiveBodyScale (β : Nat) : Effective :=
  EffectiveFraction.ofNatFunction (fun body => 3 ^ (tagEncode β body).length)
    (MatrixMortality.Primrec.nat_pow.comp (Primrec.const 3)
      (Primrec.list_length.comp (tagEncode_primrec β)))

private noncomputable def effectiveSlope (β : Nat) : Effective :=
  -1 - effectiveBodyCode β / (effectiveBodyScale β - 1)

private noncomputable def effectiveLowerScale (β : Nat) : Effective := 27 * effectiveBodyScale β

private theorem effectiveWidth_value (β : Nat) (body : Body) :
    (effectiveWidth β).value body = (3 : ℚ) ^ β := by simp [effectiveWidth]

private theorem effectiveSlope_value (β : Nat) (body : Body) :
    (effectiveSlope β).value body = bodySlope β body := by
  simp [effectiveSlope, effectiveBodyCode, effectiveBodyScale, bodySlope, periodicTernaryCode]

private theorem effectiveLowerScale_value (β : Nat) (body : Body) :
    (effectiveLowerScale β).value body = ChangedSeparatorTail.lowerCScale β body := by
  simp [effectiveLowerScale, effectiveBodyScale, source_scale]

/-- The same physical chart evaluated in certified primitive-recursive fractions. -/
noncomputable def effectiveFractionGenerator (β : Nat) : Option Unit → Square (Fin 8) Effective :=
  chartGenerator (effectiveWidth β) (effectiveSlope β) (effectiveLowerScale β)

theorem effectiveFractionGenerator_value (β : Nat) (body : Body)
    (label : Option Unit) (row column : Fin 8) :
    (effectiveFractionGenerator β label row column).value body =
      generator β body label row column := by
  simp [effectiveFractionGenerator, chartGenerator_value, effectiveWidth_value,
    effectiveSlope_value, effectiveLowerScale_value, generator]

/-- The two integer eight-dimensional matrices, with independent nonzero denominator clearing. -/
noncomputable def effectiveIntegralGenerator (β : Nat) : Body → Option Unit → Square (Fin 8) Int :=
  EffectiveMatrix.integral (effectiveFractionGenerator β)

theorem effectiveIntegralGenerator_entry_primrec (β : Nat) (label : Option Unit)
    (row column : Fin 8) :
    Primrec fun body => effectiveIntegralGenerator β body label row column :=
  EffectiveMatrix.integral_entry_primrec (effectiveFractionGenerator β) label row column

/-- Integerization preserves and reflects mortality for every body, including off-source inputs. -/
theorem effectiveIntegralGenerator_mortal_iff_generator (β : Nat) (body : Body) :
    IsMortal (effectiveIntegralGenerator β body) ↔ IsMortal (generator β body) := by
  have value_eq : EffectiveMatrix.value (effectiveFractionGenerator β) body = generator β body := by
    funext label row column
    exact effectiveFractionGenerator_value β body label row column
  exact (EffectiveMatrix.integral_mortal_iff (effectiveFractionGenerator β) body).trans
    (by rw [value_eq])

/-- The primitive-recursive integer pair has exactly the restricted-tag halting language. -/
theorem effectiveIntegralGenerator_mortal_iff_tagHaltsFrom (β : Nat) (body : Body)
    (width : 2 < β) (body_long : β - 1 ≤ body.length)
    (body_divisible : β - 1 ∣ body.length) (starts_bcb : body.take 3 = [.b, .c, .b]) :
    IsMortal (effectiveIntegralGenerator β body) ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) :=
  (effectiveIntegralGenerator_mortal_iff_generator β body).trans
    (generator_mortal_iff_tagHaltsFrom β body width body_long body_divisible starts_bcb)

end MatrixMortality.AsymmetricSeparatorRealization
