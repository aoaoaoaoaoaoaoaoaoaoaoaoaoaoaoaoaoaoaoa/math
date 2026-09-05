import MatrixMortality.AsymmetricSeparatorWrongPhase

/-!
# Existential zero transport for the asymmetric separator

The changed row accepts exactly the erase-phase zeros of the paired source. A leading toggle
puts every original witness in that phase without changing its first coordinate. Absorbing a
trailing toggle then gives the boundary used by the eight-state chart.
-/

namespace MatrixMortality.AsymmetricSeparatorRealization

open scoped Matrix
open ChangedSeparatorTail

/-- The asymmetric row applied to the inherited paired boundary. -/
def pairedScalar (β : Nat) (body : List TagLetter) (word : List PairedControl) : ℚ :=
  separatorRow (bodySlope β body) ⬝ᵥ pairedProduct ℚ β body word *ᵥ pairedColumn ℚ β

/-- The chart's scalar series, with one trailing toggle absorbed into its column. -/
def trailingScalar (β : Nat) (body : List TagLetter) (word : List PairedControl) : ℚ :=
  separatorRow (bodySlope β body) ⬝ᵥ
    pairedProduct ℚ β body word *ᵥ pairedTrailingToggleColumn ℚ β

private theorem separatorRow_sidePcp (slope : ℚ) (phase : PairPhase)
    (upper lower : List Bool) :
    separatorRow slope ⬝ᵥ phaseVector ℚ phase
        (sidePcpMatrix ℚ upper lower *ᵥ sideTailBasis ℚ) =
      tiltedTernaryCode slope upper -
        tiltedTernaryCode (if phase = .erase then slope else 16 + 9 * slope) lower := by
  cases phase <;>
    simp [separatorRow, phaseVector, controllerVector, pairControllerEquiv,
      sidePcpMatrix, sideTailBasis, dotProduct, Fin.sum_univ_succ,
      tiltedTernaryCode] <;> ring

/-- Pointwise, precisely the erase-phase source zeros survive the asymmetric row. -/
theorem pairedScalar_eq_zero_iff (β : Nat) (positive : 0 < β) (body : List TagLetter)
    (starts_bcb : body.take 3 = [.b, .c, .b]) (word : List PairedControl) :
    pairedScalar β body word = 0 ↔
      (suffixDecode word).1 = .erase ∧ pairedCoefficient ℚ β body word = 0 := by
  have body_nonempty : body ≠ [] := by
    intro empty
    have impossible : ([] : List TagLetter) = [.b, .c, .b] := by
      simpa only [empty, List.take_nil] using starts_bcb
    exact (by decide : ([] : List TagLetter) ≠ [.b, .c, .b]) impossible
  let decoded := decodePairedWord word
  let upper := spell (nearyUpper β) decoded ++ nearyMarker β
  let lower := spell (nearyLower β body) decoded
  have side_normal :
      sideTileProduct ℚ β body decoded *ᵥ sideTerminalColumn ℚ (nearyMarker β) =
        sidePcpMatrix ℚ upper lower *ᵥ sideTailBasis ℚ := by
    rw [sideTerminalColumn, Matrix.mulVec_mulVec,
      sideTileProduct_eq_sidePcpMatrix, ← sidePcpMatrix_append]
    simp [upper, lower]
  have ordinary : pairedCoefficient ℚ β body word = 0 ↔ upper = lower := by
    rw [pairedCoefficient, pairedProduct_mulVec_column]
    change pairedRow ℚ ⬝ᵥ phaseVector ℚ (suffixDecode word).1
      (sideTileProduct ℚ β body decoded *ᵥ sideTerminalColumn ℚ (nearyMarker β)) = 0 ↔ _
    rw [side_normal, pairedRow_dot_phaseVector,
      sidePcpMatrix_mulVec_sideTailBasis_head_rat, sub_eq_zero, Nat.cast_inj]
    exact ternaryCode_injective.eq_iff
  rw [pairedScalar, pairedProduct_mulVec_column]
  change separatorRow (bodySlope β body) ⬝ᵥ phaseVector ℚ (suffixDecode word).1
    (sideTileProduct ℚ β body decoded *ᵥ sideTerminalColumn ℚ (nearyMarker β)) = 0 ↔ _
  rw [side_normal, separatorRow_sidePcp, sub_eq_zero, ordinary]
  cases phase_eq : (suffixDecode word).1 with
  | erase =>
      simp only [↓reduceIte, true_and]
      exact (tiltedTernaryCode_injective _
        (bodySlope_lt_neg_three_halves β body body_nonempty)).eq_iff
  | rule =>
      simp only [reduceCtorEq, ↓reduceIte, false_and, iff_false]
      exact wrongPhase_ne β positive body starts_bcb upper decoded

/-- A leading toggle recovers any zero rejected only because of its phase. -/
theorem pairedScalar_hasNonemptyZero_iff (β : Nat) (positive : 0 < β)
    (body : List TagLetter) (starts_bcb : body.take 3 = [.b, .c, .b]) :
    WordSeries.HasNonemptyZero (pairedScalar β body) ↔
      WordSeries.HasNonemptyZero (pairedCoefficient ℚ β body) := by
  constructor
  · rintro ⟨word, nonempty, zero⟩
    exact ⟨word, nonempty, (pairedScalar_eq_zero_iff β positive body starts_bcb word).mp zero |>.2⟩
  · rintro ⟨word, nonempty, zero⟩
    cases phase_eq : (suffixDecode word).1 with
    | erase =>
        exact ⟨word, nonempty,
          (pairedScalar_eq_zero_iff β positive body starts_bcb word).mpr ⟨phase_eq, zero⟩⟩
    | rule =>
        refine ⟨.toggle :: word, by simp,
          (pairedScalar_eq_zero_iff β positive body starts_bcb _).mpr ⟨?_, ?_⟩⟩
        · simp [suffixDecode, phase_eq, PairPhase.flip]
        · simpa only [pairedCoefficient_eq_sideCoefficient, decodePairedWord, suffixDecode]
            using zero

/-- Column absorption is right-appending a toggle, independently of the separator row. -/
theorem trailingScalar_eq_append (β : Nat) (body : List TagLetter) (word : List PairedControl) :
    trailingScalar β body word = pairedScalar β body (word ++ [.toggle]) := by
  rw [trailingScalar, pairedScalar, pairedTrailingToggleColumn,
    pairedProduct, pairedProduct, wordProduct_append]
  simp only [wordProduct_cons, wordProduct_nil, mul_one, pairedGenerator]
  rw [Matrix.mulVec_mulVec]

/-- The exact asymmetric chart boundary preserves existential source zeros. -/
theorem trailingScalar_hasNonemptyZero_iff (β : Nat) (positive : 0 < β)
    (body : List TagLetter) (starts_bcb : body.take 3 = [.b, .c, .b]) :
    WordSeries.HasNonemptyZero (trailingScalar β body) ↔
      WordSeries.HasNonemptyZero (pairedCoefficient ℚ β body) := by
  have absorption : WordSeries.HasNonemptyZero (trailingScalar β body) ↔
      WordSeries.HasNonemptyZero (pairedScalar β body) := by
    constructor
    · rintro ⟨word, _, zero⟩
      refine ⟨word ++ [.toggle], by simp, ?_⟩
      exact (trailingScalar_eq_append β body word).symm.trans zero
    · rintro ⟨word, _, zero⟩
      refine ⟨word ++ [.toggle], by simp, ?_⟩
      have doubled : pairedScalar β body (word ++ [.toggle, .toggle]) =
          pairedScalar β body word :=
        congrArg (fun product : Square (Fin 4) ℚ =>
          separatorRow (bodySlope β body) ⬝ᵥ product *ᵥ pairedColumn ℚ β)
            (pairedProduct_append_toggle_toggle ℚ β body word)
      have append_eq : (word ++ [.toggle]) ++ [.toggle] =
          word ++ [PairedControl.toggle, .toggle] := by simp
      rw [trailingScalar_eq_append, append_eq, doubled]
      exact zero
  exact absorption.trans (pairedScalar_hasNonemptyZero_iff β positive body starts_bcb)

/-- A lone separator cannot manufacture a zero from the empty control word. -/
theorem trailingScalar_nil_ne_zero (β : Nat) (positive : 0 < β)
    (body : List TagLetter) (starts_bcb : body.take 3 = [.b, .c, .b]) :
    trailingScalar β body [] ≠ 0 := by
  intro zero
  have paired_zero : pairedScalar β body [.toggle] = 0 := by
    simpa only [trailingScalar_eq_append, List.nil_append] using zero
  have ordinary_zero :=
    (pairedScalar_eq_zero_iff β positive body starts_bcb [.toggle]).mp paired_zero
  have code_zero : (ternaryCode (nearyMarker β) : ℚ) = 0 := by
    simpa [pairedCoefficient_eq_sideCoefficient, decodePairedWord, suffixDecode]
      using ordinary_zero.2
  exact ternaryCode_nearyMarker_ne_zero β (by exact_mod_cast code_zero)

end MatrixMortality.AsymmetricSeparatorRealization
