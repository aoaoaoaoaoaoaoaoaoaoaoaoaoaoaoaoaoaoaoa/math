import MatrixMortality.HistoryFracture

/-!
# Transverse-kernel history coding

A mixed-radix code assigns disjoint residues to the four paired roles. Two rank-two data
controls with distinct kernels update that code on every raw paired-control word. On minimum
Neary bodies, one terminal row therefore recognizes exactly the paired zero language.
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
