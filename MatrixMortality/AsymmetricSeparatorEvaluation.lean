import MatrixMortality.AsymmetricSeparatorMortality

/-!
# Effective evaluation of the eight-state chart

Evaluation of certified unreduced fractions commutes with every operation in the fixed chart.
No regularity assumption is needed: total fraction division agrees with rational division
even off the source locus.
-/

namespace MatrixMortality.AsymmetricSeparatorRealization

open scoped Matrix
open ChangedSeparatorRealization (chainDataB chainDataC chainTailColumn)

section Evaluation

variable {α : Type*} [Primcodable α]

private theorem tailParameter_value (q : EffectiveFraction α) (body : α) :
    (tailParameter q).value body = tailParameter (q.value body) := by simp [tailParameter]

private theorem lowerCode_value (q K : EffectiveFraction α) (body : α) :
    (lowerCode q K).value body = lowerCode (q.value body) (K.value body) := by simp [lowerCode]

private theorem separatorScale_value (ρ q : EffectiveFraction α) (body : α) :
    (separatorScale ρ q).value body = separatorScale (ρ.value body) (q.value body) := by
  simp [separatorScale, tailParameter_value]

private theorem tailScale_value (ρ q : EffectiveFraction α) (body : α) :
    (tailScale ρ q).value body = tailScale (ρ.value body) (q.value body) := by
  simp [tailScale, separatorScale_value]

private theorem toggleScale_value (ρ q K : EffectiveFraction α) (body : α) :
    (toggleScale ρ q K).value body =
      toggleScale (ρ.value body) (q.value body) (K.value body) := by
  simp [toggleScale, toggleDenominator, tailParameter_value]

private theorem separatorRow_value (q : EffectiveFraction α) (body : α) (column : Fin 4) :
    (separatorRow q column).value body = separatorRow (q.value body) column := by
  fin_cases column <;> simp [separatorRow]

private theorem chainTailColumn_value (ρ : EffectiveFraction α) (body : α) (row : Fin 4) :
    (chainTailColumn ρ row).value body = chainTailColumn (ρ.value body) row := by
  fin_cases row <;> simp [chainTailColumn]

private theorem separator_value (ρ q : EffectiveFraction α) (body : α) (row column : Fin 4) :
    (separator ρ q row column).value body = separator (ρ.value body) (q.value body) row column := by
  simp [separator, separatorScale_value, chainTailColumn_value, separatorRow_value]

private theorem residualZero_value (ρ q K : EffectiveFraction α) (body : α)
    (row column : Fin 4) :
    (residualZero ρ q K row column).value body =
      residualZero (ρ.value body) (q.value body) (K.value body) row column := by
  fin_cases row <;> fin_cases column <;>
    simp [residualZero, Equiv.swap_apply_def, toggleScale_value, tailScale_value, separator_value]

private theorem residualOne_value (ρ q : EffectiveFraction α) (body : α) (row column : Fin 4) :
    (residualOne ρ q row column).value body =
      residualOne (ρ.value body) (q.value body) row column := by
  fin_cases row <;> fin_cases column <;>
    simp [residualOne, chainDataB, tailScale_value, separator_value]

private theorem residualTwo_value (ρ q K : EffectiveFraction α) (body : α)
    (row column : Fin 4) :
    (residualTwo ρ q K row column).value body =
      residualTwo (ρ.value body) (q.value body) (K.value body) row column := by
  fin_cases row <;> fin_cases column <;>
    simp [residualTwo, chainDataC, lowerCode_value, separator_value]

private theorem sectionInverse_value (ρ q : EffectiveFraction α) (body : α)
    (row : Fin 2) (column : Fin 4) :
    (sectionInverse ρ q row column).value body =
      sectionInverse (ρ.value body) (q.value body) row column := by
  fin_cases row <;> fin_cases column <;> simp [sectionInverse, tailParameter_value]

private theorem inputTwo_value (ρ q K : EffectiveFraction α) (body : α)
    (row : Fin 2) (column : Fin 4) :
    (inputTwo ρ q K row column).value body =
      inputTwo (ρ.value body) (q.value body) (K.value body) row column := by
  fin_cases row <;> fin_cases column <;> simp [inputTwo, tailParameter_value]

private theorem inputOne_value (ρ q K : EffectiveFraction α) (body : α)
    (row : Fin 2) (column : Fin 4) :
    (inputOne ρ q K row column).value body =
      inputOne (ρ.value body) (q.value body) (K.value body) row column := by
  simp [inputOne, contractFour, contractTwo, columnSection,
    sectionInverse_value, residualOne_value, inputTwo_value]

private theorem staticResidual_value (ρ q K : EffectiveFraction α) (body : α)
    (row column : Fin 4) :
    (staticResidual ρ q K row column).value body =
      staticResidual (ρ.value body) (q.value body) (K.value body) row column := by
  simp [staticResidual, contractTwo, columnSection,
    residualZero_value, residualOne_value, inputTwo_value, inputOne_value]

private theorem kernelColumn_value (ρ : EffectiveFraction α) (body : α) (row : Fin 4) :
    (kernelColumn ρ row).value body = kernelColumn (ρ.value body) row := by
  fin_cases row <;> simp [kernelColumn]

private theorem staticColumn_value (ρ q K : EffectiveFraction α) (body : α) (row : Fin 4) :
    (staticColumn ρ q K row).value body =
      staticColumn (ρ.value body) (q.value body) (K.value body) row := by
  simp [staticColumn, toggleScale_value, staticResidual_value, kernelColumn_value]

private theorem staticRow_value (ρ q K : EffectiveFraction α) (body : α) (column : Fin 4) :
    (staticRow ρ q K column).value body =
      staticRow (ρ.value body) (q.value body) (K.value body) column := by
  fin_cases column <;> simp [staticRow, toggleScale_value]

private theorem inputZero_value (ρ q K : EffectiveFraction α) (body : α)
    (row : Fin 2) (column : Fin 4) :
    (inputZero ρ q K row column).value body =
      inputZero (ρ.value body) (q.value body) (K.value body) row column := by
  simp [inputZero, contractFour,
    sectionInverse_value, staticResidual_value, staticColumn_value, staticRow_value]

private theorem input_value (ρ q K : EffectiveFraction α) (body : α)
    (row : Fin 8) (column : Fin 4) :
    (input ρ q K row column).value body =
      input (ρ.value body) (q.value body) (K.value body) row column := by
  fin_cases row <;>
    simp [input, ThreeStepRealization.input, inputZero_value, inputOne_value, inputTwo_value,
      staticRow_value, tailScale_value, separatorScale_value, separatorRow_value]

private theorem output_value (ρ q K : EffectiveFraction α) (body : α)
    (row : Fin 4) (column : Fin 8) :
    (output ρ q K row column).value body =
      output (ρ.value body) (q.value body) (K.value body) row column := by
  fin_cases column <;>
    simp [output, ThreeStepRealization.output, columnSection, residualZero_value,
      residualOne_value, residualTwo_value, staticColumn_value, chainTailColumn_value]

private theorem transition_value (ρ q : EffectiveFraction α) (body : α) (row column : Fin 8) :
    (transition ρ q row column).value body =
      transition (ρ.value body) (q.value body) row column := by
  fin_cases row <;> fin_cases column <;>
    simp [transition, ThreeStepRealization.transition, tailScale_value]

/-- The effective interpreter evaluates every physical matrix entry to the rational chart. -/
theorem chartGenerator_value (ρ q K : EffectiveFraction α) (body : α)
    (label : Option Unit) (row column : Fin 8) :
    (chartGenerator ρ q K label row column).value body =
      chartGenerator (ρ.value body) (q.value body) (K.value body) label row column := by
  cases label with
  | none => simp [chartGenerator, contractFour, input_value, output_value]
  | some point => exact transition_value ρ q body row column

end Evaluation

end MatrixMortality.AsymmetricSeparatorRealization
