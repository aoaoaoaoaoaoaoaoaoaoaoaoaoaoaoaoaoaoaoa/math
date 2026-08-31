import MatrixMortality.BranchingHistory

/-!
# Transverse-kernel history coding

A mixed-radix code assigns disjoint residues to the four paired roles. Two rank-two data
controls with distinct kernels update that code on every raw paired-control word. On minimum
Neary bodies, one terminal row therefore recognizes exactly the paired zero language. The two
branching `bcbc` terminal histories prove that no source-dependent row can extend this fixed
orbit to all admissible bodies.
-/

namespace MatrixMortality

namespace TransverseHistory

open scoped Matrix

/-! ## Mixed-radix role code -/

/-- Radix selected by the data letter of a role. -/
def roleRadix : NearyTile → Nat
  | .rule .b | .erase .b => 4
  | .rule .c | .erase .c => 8

/-- Digit selected jointly by the data letter and paired phase. -/
def roleDigit : NearyTile → Nat
  | .rule .b => 1
  | .rule .c => 2
  | .erase .b => 3
  | .erase .c => 4

/-- Residue modulo four, which distinguishes all four roles. -/
def roleResidue : NearyTile → Nat
  | .rule .b => 1
  | .rule .c => 2
  | .erase .b => 3
  | .erase .c => 0

theorem roleResidue_injective : Function.Injective roleResidue := by
  intro left right equality
  cases left with
  | rule leftLetter =>
      cases right with
      | rule rightLetter =>
          cases leftLetter <;> cases rightLetter <;> simp_all [roleResidue]
      | erase rightLetter =>
          cases leftLetter <;> cases rightLetter <;> simp_all [roleResidue]
  | erase leftLetter =>
      cases right with
      | rule rightLetter =>
          cases leftLetter <;> cases rightLetter <;> simp_all [roleResidue]
      | erase rightLetter =>
          cases leftLetter <;> cases rightLetter <;> simp_all [roleResidue]

/-- Variable-radix code with the first role in the low-order block. -/
def code : List NearyTile → Nat
  | [] => 0
  | tile :: word => roleRadix tile * code word + roleDigit tile

@[simp] theorem code_cons_mod_four (tile : NearyTile) (word : List NearyTile) :
    code (tile :: word) % 4 = roleResidue tile := by
  cases tile with
  | rule letter =>
      cases letter <;> simp [code, roleRadix, roleDigit, roleResidue]; omega
  | erase letter =>
      cases letter <;> simp [code, roleRadix, roleDigit, roleResidue]; omega

theorem code_injective : Function.Injective code := by
  intro left
  induction left with
  | nil =>
      intro right equality
      cases right with
      | nil => rfl
      | cons head tail =>
          cases head with
          | rule letter => cases letter <;> simp [code, roleRadix, roleDigit] at equality
          | erase letter => cases letter <;> simp [code, roleRadix, roleDigit] at equality
  | cons leftHead leftTail induction =>
      intro right equality
      cases right with
      | nil =>
          cases leftHead with
          | rule letter => cases letter <;> simp [code, roleRadix, roleDigit] at equality
          | erase letter => cases letter <;> simp [code, roleRadix, roleDigit] at equality
      | cons rightHead rightTail =>
          have residueEquality : roleResidue leftHead = roleResidue rightHead := by
            have reduced := congrArg (· % 4) equality
            rw [code_cons_mod_four, code_cons_mod_four] at reduced
            exact reduced
          have headEquality := roleResidue_injective residueEquality
          subst rightHead
          have tailCodeEquality : code leftTail = code rightTail := by
            cases leftHead with
            | rule letter =>
                cases letter <;> simp [code, roleRadix, roleDigit] at equality <;> omega
            | erase letter =>
                cases letter <;> simp [code, roleRadix, roleDigit] at equality <;> omega
          rw [induction tailCodeEquality]

/-! ## Integral transverse controls -/

/-- The two rank-two data controls have distinct coordinate kernels. -/
def dataMatrix (R : Type*) [CommRing R] : TagLetter → Matrix (Fin 3) (Fin 3) R
  | .b =>
      !![0, 8, 17;
         0, 4, 9;
         0, 0, 1]
  | .c =>
      !![8, 0, 25;
         4, 0, 13;
         0, 0, 1]

/-- The phase involution in transverse quotient coordinates. -/
def toggleMatrix (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![3, -4, 0;
     2, -3, 0;
     0, 0, 1]

/-- Three integral controls for the complete paired-control monoid. -/
def generator (R : Type*) [CommRing R] : PairedControl → Matrix (Fin 3) (Fin 3) R
  | .data letter => dataMatrix R letter
  | .toggle => toggleMatrix R

/-- Homogeneous state corresponding to code `k` and one paired phase. -/
def state (R : Type*) [CommRing R] (decoded : PairPhase × List NearyTile) : Fin 3 → R :=
  ![8 * (code decoded.2 : R) - historyPhaseSign R decoded.1,
    4 * (code decoded.2 : R) - historyPhaseSign R decoded.1,
    1]

/-- Initial rule-phase state. -/
def column (R : Type*) [CommRing R] : Fin 3 → R := ![-1, -1, 1]

/-- The exact transverse state recurrence on every raw control word. -/
theorem product_mulVec_column (R : Type*) [CommRing R] (word : List PairedControl) :
    wordProduct (generator R) word *ᵥ column R = state R (suffixDecode word) := by
  induction word with
  | nil =>
      ext coordinate
      fin_cases coordinate <;>
        simp [wordProduct, column, state, suffixDecode, code, historyPhaseSign]
  | cons control word induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec, induction]
      cases decodedEquality : suffixDecode word with
      | mk phase decoded =>
          cases control with
          | toggle =>
              cases phase <;>
                ext coordinate <;>
                fin_cases coordinate <;>
                simp [generator, toggleMatrix, state, suffixDecode, decodedEquality,
                  PairPhase.flip, historyPhaseSign, Matrix.mulVec, dotProduct,
                  Fin.sum_univ_succ] <;>
                ring
          | data letter =>
              cases phase <;> cases letter <;>
                ext coordinate <;>
                fin_cases coordinate <;>
                simp [generator, dataMatrix, state, suffixDecode, decodedEquality,
                  PairPhase.tile, historyPhaseSign, code, roleRadix, roleDigit, Matrix.mulVec,
                  dotProduct, Fin.sum_univ_succ] <;>
                ring

/-- A terminal row selecting one prescribed mixed-radix history code. -/
def row (R : Type*) [CommRing R] (target : Nat) : Fin 3 → R :=
  ![1, -1, -(4 * target : R)]

/-- Scalar series recognized by the transverse controls. -/
def coefficient (target : Nat) (word : List PairedControl) : ℚ :=
  linearCoefficient (generator ℚ) (row ℚ target) (column ℚ) word

theorem coefficient_eq (target : Nat) (word : List PairedControl) :
    coefficient target word = 4 * ((code (decodePairedWord word) : ℚ) - target) := by
  rw [coefficient, linearCoefficient, product_mulVec_column]
  cases decodedEquality : suffixDecode word with
  | mk phase decoded =>
      cases phase <;>
        simp [row, state, decodePairedWord, decodedEquality, dotProduct,
          Fin.sum_univ_succ] <;>
        ring

theorem coefficient_zero_iff_decode_eq (target : List NearyTile)
    (word : List PairedControl) :
    coefficient (code target) word = 0 ↔ decodePairedWord word = target := by
  rw [coefficient_eq]
  constructor
  · intro zero
    have rationalEquality :
        (code (decodePairedWord word) : ℚ) = code target := by
      linarith
    have codeEquality : code (decodePairedWord word) = code target := by
      exact_mod_cast rationalEquality
    exact code_injective codeEquality
  · intro decodedEquality
    rw [decodedEquality]
    ring

/-- On every minimum body, the transverse controls have exactly the paired zero language. -/
theorem minimalBody_zero_iff_paired_zero (β : Nat) (body : List TagLetter)
    (βLarge : 2 < β) (bodyLength : body.length = β - 1) (word : List PairedControl) :
    coefficient (code (minimalBodyWord body)) word = 0 ↔
      pairedCoefficient ℚ β body word = 0 := by
  rw [coefficient_zero_iff_decode_eq, pairedCoefficient_eq_sideCoefficient,
    sideCoefficient_eq_zero_iff_terminal_match_rat]
  constructor
  · intro decodedEquality
    rw [decodedEquality]
    exact minimalBody_terminal_match β body βLarge bodyLength
  · intro terminalMatch
    exact minimalBody_terminal_word_unique β body (by omega) bodyLength
      (decodePairedWord word) terminalMatch

/-! ## Terminal-row obstruction -/

/-- Scalar series obtained by retaining the fixed transverse controls and initial column while
allowing an arbitrary terminal row. -/
def rowCoefficient (terminalRow : Fin 3 → ℚ) (word : List PairedControl) : ℚ :=
  linearCoefficient (generator ℚ) terminalRow (column ℚ) word

theorem rowCoefficient_eq (terminalRow : Fin 3 → ℚ) (word : List PairedControl) :
    rowCoefficient terminalRow word =
      terminalRow ⬝ᵥ state ℚ (suffixDecode word) := by
  rw [rowCoefficient, linearCoefficient, product_mulVec_column]

private theorem terminal_phase_pair
    (β : Nat) (body : List TagLetter) (terminalRow : Fin 3 → ℚ)
    (sameZero : ∀ word,
      rowCoefficient terminalRow word = 0 ↔ pairedCoefficient ℚ β body word = 0)
    (target : List NearyTile)
    (terminalMatch :
      spell (nearyUpper β) target ++ nearyMarker β = spell (nearyLower β body) target) :
    terminalRow ⬝ᵥ state ℚ (.rule, target) = 0 ∧
      terminalRow ⬝ᵥ state ℚ (.erase, target) = 0 := by
  obtain ⟨control, decoded⟩ := decodePairedWord_surjective target
  have toggledDecoded : decodePairedWord (.toggle :: control) = target := by
    simpa [decodePairedWord, suffixDecode] using decoded
  have controlPairedZero : pairedCoefficient ℚ β body control = 0 := by
    rw [pairedCoefficient_eq_sideCoefficient, decoded]
    exact (sideCoefficient_eq_zero_iff_terminal_match_rat β body target).mpr terminalMatch
  have toggledPairedZero : pairedCoefficient ℚ β body (.toggle :: control) = 0 := by
    rw [pairedCoefficient_eq_sideCoefficient, toggledDecoded]
    exact (sideCoefficient_eq_zero_iff_terminal_match_rat β body target).mpr terminalMatch
  have controlZero := (sameZero control).mpr controlPairedZero
  have toggledZero := (sameZero (.toggle :: control)).mpr toggledPairedZero
  rw [rowCoefficient_eq] at controlZero toggledZero
  cases decodedState : suffixDecode control with
  | mk phase decodedWord =>
      have decodedWordEquality : decodedWord = target := by
        simpa [decodePairedWord, decodedState] using decoded
      subst decodedWord
      cases phase with
      | rule =>
          exact ⟨by simpa [decodedState] using controlZero, by
            simpa [suffixDecode, decodedState, PairPhase.flip] using toggledZero⟩
      | erase =>
          exact ⟨by
            simpa [suffixDecode, decodedState, PairPhase.flip] using toggledZero,
            by simpa [decodedState] using controlZero⟩

private theorem row_eq_zero_of_phase_pairs
    (terminalRow : Fin 3 → ℚ) (first second : List NearyTile)
    (codesDifferent : code first ≠ code second)
    (firstRule : terminalRow ⬝ᵥ state ℚ (.rule, first) = 0)
    (firstErase : terminalRow ⬝ᵥ state ℚ (.erase, first) = 0)
    (secondRule : terminalRow ⬝ᵥ state ℚ (.rule, second) = 0)
    (secondErase : terminalRow ⬝ᵥ state ℚ (.erase, second) = 0) :
    terminalRow = 0 := by
  simp [state, historyPhaseSign, dotProduct, Fin.sum_univ_succ] at firstRule firstErase
  simp [state, historyPhaseSign, dotProduct, Fin.sum_univ_succ] at secondRule secondErase
  have phaseSum : terminalRow 0 + terminalRow 1 = 0 := by
    linear_combination (1 / 2 : ℚ) * firstErase - (1 / 2 : ℚ) * firstRule
  have secondPhaseSum : terminalRow 0 + terminalRow 1 = 0 := by
    linear_combination (1 / 2 : ℚ) * secondErase - (1 / 2 : ℚ) * secondRule
  have firstCode :
      4 * (code first : ℚ) * terminalRow 0 + terminalRow 2 = 0 := by
    linear_combination firstRule - (4 * (code first : ℚ) - 1) * phaseSum
  have secondCode :
      4 * (code second : ℚ) * terminalRow 0 + terminalRow 2 = 0 := by
    linear_combination secondRule - (4 * (code second : ℚ) - 1) * secondPhaseSum
  have codeCastDifferent : (code first : ℚ) ≠ code second := by
    exact_mod_cast codesDifferent
  have codeDifference : (code first : ℚ) - code second ≠ 0 :=
    sub_ne_zero.mpr codeCastDifferent
  have firstCoordinateProduct :
      ((code first : ℚ) - code second) * terminalRow 0 = 0 := by
    linear_combination (1 / 4 : ℚ) * firstCode - (1 / 4 : ℚ) * secondCode
  have firstCoordinate : terminalRow 0 = 0 :=
    (mul_eq_zero.mp firstCoordinateProduct).resolve_left codeDifference
  funext coordinate
  fin_cases coordinate
  · exact firstCoordinate
  · simpa [firstCoordinate] using phaseSum
  · simpa [firstCoordinate] using firstCode

/-- No terminal row on the fixed transverse-history orbit recognizes the width-three `bcbc`
paired zero language. Two distinct terminal histories force the row to vanish on both phase
lines and hence to be the zero row; the checked near-fork is then a false zero. -/
theorem no_bcbc_terminal_row_section (terminalRow : Fin 3 → ℚ) :
    ¬(∀ word,
      rowCoefficient terminalRow word = 0 ↔
        pairedCoefficient ℚ 3 BranchingHistory.bcbcBody word = 0) := by
  intro sameZero
  let flat := BranchingHistory.bcbcTerminalFork [false]
  let nested := BranchingHistory.bcbcTerminalFork [true]
  have wordsDifferent : flat ≠ nested := by
    intro wordsEqual
    have bitsEqual := BranchingHistory.bcbcTerminalFork_injective wordsEqual
    simp at bitsEqual
  have codesDifferent : code flat ≠ code nested := by
    intro codesEqual
    exact wordsDifferent (code_injective codesEqual)
  have flatPhases := terminal_phase_pair 3 BranchingHistory.bcbcBody terminalRow sameZero flat
    (BranchingHistory.bcbcTerminalFork_match [false])
  have nestedPhases := terminal_phase_pair 3 BranchingHistory.bcbcBody terminalRow sameZero nested
    (BranchingHistory.bcbcTerminalFork_match [true])
  have rowZero : terminalRow = 0 :=
    row_eq_zero_of_phase_pairs terminalRow flat nested codesDifferent
      flatPhases.1 flatPhases.2 nestedPhases.1 nestedPhases.2
  have falseZero :
      rowCoefficient terminalRow BranchingHistory.bcbcNearForkControl = 0 := by
    rw [rowZero]
    simp [rowCoefficient, linearCoefficient]
  exact BranchingHistory.bcbc_terminal_nearFork.2
    ((sameZero BranchingHistory.bcbcNearForkControl).mp falseZero)

/-- Even a source-dependent family of terminal rows cannot uniformize the fixed transverse
orbit on all admissible Neary bodies. The obstruction is set-theoretic and therefore also
excludes every computable row family. -/
theorem no_sourceUniform_terminal_row_section
    (terminalRow : Nat → List TagLetter → Fin 3 → ℚ) :
    ¬(∀ β body, 2 < β → β - 1 ≤ body.length → β - 1 ∣ body.length → ∀ word,
      rowCoefficient (terminalRow β body) word = 0 ↔
        pairedCoefficient ℚ β body word = 0) := by
  intro sameZero
  exact no_bcbc_terminal_row_section (terminalRow 3 BranchingHistory.bcbcBody)
    (sameZero 3 BranchingHistory.bcbcBody (by decide) (by decide) (by decide))

/-! ## Exact transverse kernels -/

theorem data_mulVec_eq_zero_iff (letter : TagLetter) (vector : Fin 3 → ℚ) :
    dataMatrix ℚ letter *ᵥ vector = 0 ↔
      match letter with
      | .b => vector 1 = 0 ∧ vector 2 = 0
      | .c => vector 0 = 0 ∧ vector 2 = 0 := by
  cases letter with
  | b =>
      constructor
      · intro zero
        have coordinate1 := congrFun zero 1
        have coordinate2 := congrFun zero 2
        simp [dataMatrix, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ] at coordinate1 coordinate2
        constructor <;> linarith
      · rintro ⟨middleZero, lastZero⟩
        ext coordinate
        fin_cases coordinate <;>
          simp [dataMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
            middleZero, lastZero]
  | c =>
      constructor
      · intro zero
        have coordinate1 := congrFun zero 1
        have coordinate2 := congrFun zero 2
        simp [dataMatrix, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ] at coordinate1 coordinate2
        constructor <;> linarith
      · rintro ⟨firstZero, lastZero⟩
        ext coordinate
        fin_cases coordinate <;>
          simp [dataMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
            firstZero, lastZero]

end TransverseHistory

end MatrixMortality
