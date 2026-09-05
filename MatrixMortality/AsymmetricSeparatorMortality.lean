import MatrixMortality.AsymmetricSeparatorMoments
import MatrixMortality.AsymmetricSeparatorCoefficients
import MatrixMortality.PairedReturnRoles

/-!
# Mortality of the eight-state asymmetric pair

Every return is a nonzero multiple of one of four paired roles. Singular return compression
handles unrestricted physical words; the rank-one interface and asymmetric zero transport
then recover exactly the original restricted-tag halting predicate.
-/

namespace MatrixMortality.AsymmetricSeparatorRealization

open scoped Matrix
open ChangedSeparatorRealization (chainDataB chainDataC chainTailColumn
  chainDataB_eq_pairedDataMatrix chainDataC_eq_pairedDataMatrix
  chainTailColumn_eq_pairedTrailingToggleColumn returnLabel returnIndex returnLabel_returnIndex)

/-- Operation-only physical pair, shared by rational semantics and the effective interpreter. -/
def chartGenerator {R : Type*} [FractionArithmetic R] (ρ q K : R) :
    Option Unit → Square (Fin 8) R
  | none => contractFour (input ρ q K) (output ρ q K)
  | some _ => transition ρ q

/-- The two rational eight-dimensional matrices associated with a source body. -/
def generator (β : Nat) (body : List TagLetter) : Option Unit → Square (Fin 8) ℚ :=
  chartGenerator (3 ^ β) (bodySlope β body) (ChangedSeparatorTail.lowerCScale β body)

theorem chartGenerator_eq_pair (ρ q K : ℚ) :
    chartGenerator ρ q K = ReturnFamily.pairGenerator
      (transition ρ q) (input ρ q K * output ρ q K) := by
  funext label
  cases label with
  | none => exact contractFour_eq_mul _ _
  | some point => rfl

/-- The four normalized roles seen between physical cuts. -/
def interfaceFamily (β : Nat) (body : List TagLetter) :
    Option PairedControl → Square (Fin 4) ℚ :=
  separatedGenerator
    (Matrix.vecMulVec (pairedTrailingToggleColumn ℚ β) (separatorRow (bodySlope β body)))
    (pairedGenerator ℚ β body)

/-- Scalar discarded when a return is relabelled by its normalized role. -/
def returnScale (ρ q K : ℚ) : Nat → ℚ
  | 0 => toggleScale ρ q K
  | 1 => 1
  | 2 => 1
  | Nat.succ (Nat.succ (Nat.succ n)) =>
      ((1 / tailScale ρ q) ^ (n + 3) * tailScale ρ q ^ 2) * separatorScale ρ q

theorem returnScale_ne_zero (ρ q K : ℚ) (regular : RegularChart ρ q K) (n : Nat) :
    returnScale ρ q K n ≠ 0 := by
  have separator_ne_zero : separatorScale ρ q ≠ 0 :=
    div_ne_zero (by norm_num)
      (mul_ne_zero regular.parameter_ne_zero regular.width_ne_zero)
  cases n with
  | zero => exact regular.toggle_ne_zero
  | succ n =>
      cases n with
      | zero => exact one_ne_zero
      | succ n =>
          cases n with
          | zero => exact one_ne_zero
          | succ n => exact mul_ne_zero (tail_scalar_ne_zero ρ q K regular n) separator_ne_zero

private theorem separator_eq_scaled_outer (β : Nat) (body : List TagLetter) :
    separator (3 ^ β) (bodySlope β body) =
      separatorScale (3 ^ β) (bodySlope β body) •
        Matrix.vecMulVec (pairedTrailingToggleColumn ℚ β) (separatorRow (bodySlope β body)) := by
  have column_eq : chainTailColumn ((3 : ℚ) ^ β) = pairedTrailingToggleColumn ℚ β :=
    chainTailColumn_eq_pairedTrailingToggleColumn β
  ext row column
  simp only [separator, Matrix.of_apply, column_eq, Matrix.smul_apply,
    Matrix.vecMulVec, smul_eq_mul]
  ring

/-- The entire infinite return alphabet is pointwise a nonzero scaling of four roles. -/
theorem returnMatrix_eq_scaled_interface (β : Nat) (width : 3 ≤ β)
    (body : List TagLetter) (b_mem : .b ∈ body) (n : Nat) :
    ReturnFamily.returnMatrix (transition (3 ^ β) (bodySlope β body))
        (input (3 ^ β) (bodySlope β body) (ChangedSeparatorTail.lowerCScale β body))
        (output (3 ^ β) (bodySlope β body) (ChangedSeparatorTail.lowerCScale β body)) n =
      returnScale (3 ^ β) (bodySlope β body) (ChangedSeparatorTail.lowerCScale β body) n •
        interfaceFamily β body (returnLabel n) := by
  have regular := regularChart_of_b_mem β width body b_mem
  cases n with
  | zero =>
      simpa [ReturnFamily.returnMatrix, returnScale, interfaceFamily, returnLabel,
        separatedGenerator, pairedGenerator] using moment_zero _ _ _ regular
  | succ n =>
      cases n with
      | zero =>
          have data_eq : chainDataB ((3 : ℚ) ^ β) = pairedDataMatrix ℚ β body .b :=
            chainDataB_eq_pairedDataMatrix β body
          simpa [ReturnFamily.returnMatrix, returnScale, interfaceFamily, returnLabel,
            separatedGenerator, pairedGenerator, data_eq] using moment_one _ _ _ regular
      | succ n =>
          cases n with
          | zero =>
              have data_eq := chainDataC_eq_pairedDataMatrix β body
              simpa [ReturnFamily.returnMatrix, returnScale, interfaceFamily, returnLabel,
                separatedGenerator, pairedGenerator,
                lowerCode_bodySlope β body (List.ne_nil_of_mem b_mem), data_eq]
                using moment_two _ _ _ regular
          | succ n =>
              change _ * _ ^ (n + 1 + 1 + 1) * _ = _
              rw [show n + 1 + 1 + 1 = n + 3 by omega, moment_add_three,
                separator_eq_scaled_outer]
              simp [returnScale, interfaceFamily, returnLabel, separatedGenerator, smul_smul]

/-- The normalized interface is mortal exactly when the original source scalar has a zero. -/
theorem interfaceFamily_mortal_iff_paired_zero (β : Nat) (positive : 0 < β)
    (body : List TagLetter) (starts_bcb : body.take 3 = [.b, .c, .b]) :
    IsMortal (interfaceFamily β body) ↔
      WordSeries.HasNonemptyZero (pairedCoefficient ℚ β body) := by
  rw [interfaceFamily, mortal_adjoin_outer_iff]
  change WordSeries.HasZero (trailingScalar β body) ↔ _
  exact (WordSeries.hasNonemptyZero_iff_hasZero_of_nil_ne _
    (trailingScalar_nil_ne_zero β positive body starts_bcb)).symm.trans
      (trailingScalar_hasNonemptyZero_iff β positive body starts_bcb)

/-- Unrestricted products of the rational pair recognize exactly the source zero language. -/
theorem generator_mortal_iff_paired_zero (β : Nat) (width : 3 ≤ β)
    (body : List TagLetter) (starts_bcb : body.take 3 = [.b, .c, .b]) :
    IsMortal (generator β body) ↔
      WordSeries.HasNonemptyZero (pairedCoefficient ℚ β body) := by
  have b_mem : .b ∈ body :=
    List.mem_of_mem_take (by rw [starts_bcb]; simp)
  have regular := regularChart_of_b_mem β width body b_mem
  rw [generator, chartGenerator_eq_pair,
    ReturnFamily.pairGenerator_isMortal_iff_returnFamily _ _ _
      (transition_pow_ne_zero _ _ _ regular)]
  have returns_eq :
      ReturnFamily.returnMatrix (transition (3 ^ β) (bodySlope β body))
        (input (3 ^ β) (bodySlope β body) (ChangedSeparatorTail.lowerCScale β body))
        (output (3 ^ β) (bodySlope β body) (ChangedSeparatorTail.lowerCScale β body)) =
      fun n => returnScale (3 ^ β) (bodySlope β body)
        (ChangedSeparatorTail.lowerCScale β body) n • (interfaceFamily β body ∘ returnLabel) n := by
    funext n
    exact returnMatrix_eq_scaled_interface β width body b_mem n
  rw [returns_eq, isMortal_smulMatrix_iff _ (returnScale_ne_zero _ _ _ regular)]
  exact (ReturnFamily.isMortal_comp_rightInverse_iff (interfaceFamily β body)
    returnLabel returnIndex returnLabel_returnIndex).trans
      (interfaceFamily_mortal_iff_paired_zero β (by omega) body starts_bcb)

/-- The rational pair is equivalent to the inherited restricted-tag halting predicate. -/
theorem generator_mortal_iff_tagHaltsFrom (β : Nat) (body : List TagLetter)
    (width : 2 < β) (body_long : β - 1 ≤ body.length)
    (body_divisible : β - 1 ∣ body.length) (starts_bcb : body.take 3 = [.b, .c, .b]) :
    IsMortal (generator β body) ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  rw [generator_mortal_iff_paired_zero β width body starts_bcb,
    paired_zero_rat_iff_terminal_match]
  exact terminal_match_iff_tagHaltsFrom β body width body_long body_divisible

end MatrixMortality.AsymmetricSeparatorRealization
