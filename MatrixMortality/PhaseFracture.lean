import MatrixMortality.PairedMortality
import MatrixMortality.LinearRepresentation

/-!
# Phase-fracture obstruction

The paired compiler remembers which Neary role a data letter must perform in one private
coordinate.  Any same-zero realization that projectively identifies an erase-phase suffix with
the suffix obtained by prefixing `c` therefore loses a real zero-language distinction.
-/

namespace MatrixMortality

open scoped Matrix

/-- A finite linear representation has exactly the zeros of a scalar word series. -/
def RepresentsZeroSet {α ι K : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (series : List α → K) (generators : α → Matrix ι ι K)
    (row column : ι → K) : Prop :=
  ∀ word, linearCoefficient generators row column word = 0 ↔ series word = 0

/-- Prefixing a toggle does not change the paired scalar coefficient. -/
theorem pairedCoefficient_toggle_cons (β : Nat) (body : List TagLetter)
    (word : List PairedControl) :
    pairedCoefficient ℚ β body (.toggle :: word) = pairedCoefficient ℚ β body word := by
  simp only [pairedCoefficient, pairedProduct, wordProduct_cons, pairedGenerator,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  congr 1
  ext coordinate
  fin_cases coordinate <;>
    simp [pairedRow, pairedToggleMatrix_eq_explicit, Matrix.vecMul, Matrix.dotProduct,
      Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_succ]

/-- A leading `c` read in erase phase cannot vanish: its two decoded words begin with different
binary letters. -/
theorem pairedCoefficient_data_c_cons_ne_zero_of_erase
    (β : Nat) (body : List TagLetter) (word : List PairedControl)
    (erase : (suffixDecode word).1 = .erase) :
    pairedCoefficient ℚ β body (.data .c :: word) ≠ 0 := by
  rw [pairedCoefficient_eq_sideCoefficient]
  intro coefficient_zero
  have terminal_match :=
    (sideCoefficient_eq_zero_iff_terminal_match_rat β body
      (decodePairedWord (.data .c :: word))).mp coefficient_zero
  simp [decodePairedWord, suffixDecode, erase, PairPhase.tile, spell, nearyUpper, nearyLower,
    tagCode] at terminal_match

/-- Normalize the suffix phase to erase without changing the paired coefficient. -/
theorem exists_erase_phase_eq_coefficient (β : Nat) (body : List TagLetter)
    (word : List PairedControl) :
    ∃ erased : List PairedControl,
      (suffixDecode erased).1 = .erase ∧
        pairedCoefficient ℚ β body erased = pairedCoefficient ℚ β body word := by
  cases phase_eq : (suffixDecode word).1 with
  | erase =>
      exact ⟨word, phase_eq, rfl⟩
  | rule =>
      refine ⟨.toggle :: word, ?_, pairedCoefficient_toggle_cons β body word⟩
      simp [suffixDecode, phase_eq, PairPhase.flip]

/-- No same-zero realization can projectively forget an erase-phase `c` transition.

The scalar may depend on the suffix.  The conclusion is dimension-free: dimension three enters
only in an attempted construction of the forbidden projective identification.
-/
theorem no_zero_of_erase_c_projective_identification
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : Nat) (body : List TagLetter)
    (generators : PairedControl → Matrix ι ι ℚ) (row column : ι → ℚ)
    (same_zero : RepresentsZeroSet (pairedCoefficient ℚ β body) generators row column)
    (erase_c_projective :
      ∀ word : List PairedControl, (suffixDecode word).1 = .erase →
        ∃ scalar : ℚ,
          generators (.data .c) *ᵥ (wordProduct generators word *ᵥ column) =
            scalar • (wordProduct generators word *ᵥ column)) :
    ¬WordSeries.HasZero (pairedCoefficient ℚ β body) := by
  rintro ⟨word, source_zero⟩
  obtain ⟨erased, erased_phase, erased_coefficient⟩ :=
    exists_erase_phase_eq_coefficient β body word
  have erased_source_zero : pairedCoefficient ℚ β body erased = 0 := by
    rw [erased_coefficient, source_zero]
  have erased_target_zero : linearCoefficient generators row column erased = 0 :=
    (same_zero erased).2 erased_source_zero
  obtain ⟨scalar, projective⟩ := erase_c_projective erased erased_phase
  have prefixed_target_zero :
      linearCoefficient generators row column (.data .c :: erased) = 0 := by
    rw [linearCoefficient, wordProduct_cons, ← Matrix.mulVec_mulVec, projective]
    rw [Matrix.dotProduct_smul]
    simp [show row ⬝ᵥ wordProduct generators erased *ᵥ column = 0 by
      simpa [linearCoefficient] using erased_target_zero]
  have prefixed_source_zero :
      pairedCoefficient ℚ β body (.data .c :: erased) = 0 :=
    (same_zero (.data .c :: erased)).1 prefixed_target_zero
  exact pairedCoefficient_data_c_cons_ne_zero_of_erase β body erased erased_phase
    prefixed_source_zero

end MatrixMortality
