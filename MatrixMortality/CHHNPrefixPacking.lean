import MatrixMortality.PrefixPacking

/-!
# CHHN prefix packings

The root-plus-chain complete prefix codes at `(h, k) = (2, 2)` and `(1, 4)` realize the
generator–dimension trade `M_d(hk+1) ≤ M_{kd}(h+1)` at the two endpoints used here:
`M_d(5) ≤ M_{2d}(3)` and `M_d(5) ≤ M_{4d}(2)`.
-/

namespace MatrixMortality.CHHNPrefixPacking

open scoped Matrix

/-- Two-state ternary chain transition. -/
def ternaryNext (state : Fin 2) (letter : Fin 3) : Fin 2 :=
  ![![0, 0, 1], ![0, 0, 0]] state letter

/-- Leaves of the two-state ternary chain, in source-label order. -/
def ternaryEmission (state : Fin 2) (letter : Fin 3) : Option (Fin 5) :=
  ![![some 0, some 1, none], ![some 2, some 3, some 4]] state letter

/-- Ternary codewords `0, 1, 20, 21, 22`. -/
def ternaryCodeword (label : Fin 5) : List (Fin 3) :=
  ![[0], [1], [2, 0], [2, 1], [2, 2]] label

/-- Complete ternary code with two internal states and five leaves. -/
def ternaryFiveCode : PrefixPacking.CompleteCode (Fin 2) (Fin 3) (Fin 5) where
  root := 0
  next := ternaryNext
  emission := ternaryEmission
  code := ternaryCodeword
  code_nonempty label := by fin_cases label <;> decide
  decode_code label := by fin_cases label <;> rfl
  sync := [0]
  sync_state state := by fin_cases state <;> rfl
  source_card := by decide

/-- Four-state binary chain transition. -/
def binaryNext (state : Fin 4) (letter : Bool) : Fin 4 :=
  if letter then ![1, 2, 3, 0] state else 0

/-- Leaves of the four-state binary chain, in source-label order. -/
def binaryEmission (state : Fin 4) (letter : Bool) : Option (Fin 5) :=
  if letter then ![none, none, none, some 4] state
  else ![some 0, some 1, some 2, some 3] state

/-- Binary codewords `0, 10, 110, 1110, 1111`. -/
def binaryCodeword (label : Fin 5) : List Bool :=
  ![[false], [true, false], [true, true, false],
    [true, true, true, false], [true, true, true, true]] label

/-- Complete binary code with four internal states and five leaves. -/
def binaryFiveCode : PrefixPacking.CompleteCode (Fin 4) Bool (Fin 5) where
  root := 0
  next := binaryNext
  emission := binaryEmission
  code := binaryCodeword
  code_nonempty label := by fin_cases label <;> decide
  decode_code label := by fin_cases label <;> rfl
  sync := [false]
  sync_state state := by fin_cases state <;> rfl
  source_card := by decide

/-- Three packed generators in dimension `2d` obtained from five generators in dimension `d`. -/
def ternaryPack {Index R : Type*} [Fintype Index] [DecidableEq Index] [CommSemiring R]
    (source : Fin 5 → Square Index R) : Fin 3 → Square (Fin 2 × Index) R :=
  (ternaryFiveCode.machine source).generator

/-- Two packed generators in dimension `4d` obtained from five generators in dimension `d`. -/
def binaryPack {Index R : Type*} [Fintype Index] [DecidableEq Index] [CommSemiring R]
    (source : Fin 5 → Square Index R) : Bool → Square (Fin 4 × Index) R :=
  (binaryFiveCode.machine source).generator

/-- The CHHN trade `M_d(5) ≤ M_{2d}(3)`. -/
theorem ternaryPack_isMortal_iff
    {Index R : Type*} [Fintype Index] [DecidableEq Index] [Nonempty Index]
    [CommSemiring R] [Nontrivial R] (source : Fin 5 → Square Index R) :
    IsMortal (ternaryPack source) ↔ IsMortal source :=
  ternaryFiveCode.machine_isMortal_iff_source source

/-- The CHHN trade `M_d(5) ≤ M_{4d}(2)`. -/
theorem binaryPack_isMortal_iff
    {Index R : Type*} [Fintype Index] [DecidableEq Index] [Nonempty Index]
    [CommSemiring R] [Nontrivial R] (source : Fin 5 → Square Index R) :
    IsMortal (binaryPack source) ↔ IsMortal source :=
  binaryFiveCode.machine_isMortal_iff_source source

end MatrixMortality.CHHNPrefixPacking
