import MatrixMortality.MatrixSemigroup
import MatrixMortality.PairedCompression

/-!
# Binary compression of the paired source

The four side-normal Neary roles split as a rule/erasure bit and a tag-letter bit. A six-state
linear representation reads those bits in pairs. Its unfinished upper channel is shared because a
rule and its erasure role have the same upper word. Every binary word is interpreted: complete
pairs emit roles in reverse order, and one trailing bit changes only the residual phase.
-/

namespace MatrixMortality

open scoped Matrix

/-- The first bit of a binary block selects rule or erasure. -/
def pairedBinaryPhase : Bool → PairPhase
  | false => .rule
  | true => .erase

/-- The second bit of a binary block selects the tag letter. -/
def pairedBinaryLetter : Bool → TagLetter
  | false => .b
  | true => .c

/-- The role emitted by one complete two-bit block. -/
def pairedBinaryTile (phaseBit letterBit : Bool) : NearyTile :=
  (pairedBinaryPhase phaseBit).tile (pairedBinaryLetter letterBit)

/-- Binary code inverse to `pairedBinaryTile`. -/
def pairedBinaryCode : NearyTile → List Bool
  | .rule .b => [false, false]
  | .rule .c => [false, true]
  | .erase .b => [true, false]
  | .erase .c => [true, true]

/-- The two six-state generators. The first bit selects a role phase; the second completes the
role and updates the shared side-normal payload. -/
def pairedBinaryGenerator (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter) :
    Bool → Matrix (Fin 6) (Fin 6) R
  | false =>
      !![(1 : R), 0, 0, 0, 0, 0;
         0, 0, 0, 1, 0, 0;
         0, 0, 0, 0, 1, 0;
         ternaryCode (nearyLower β body (.rule .b)),
           (3 : R) ^ (nearyLower β body (.rule .b)).length, 0, 0, 0, 0;
         ternaryCode (nearyUpper β (.rule .b)), 0,
           (3 : R) ^ (nearyUpper β (.rule .b)).length, 0, 0, 0;
         ternaryCode (nearyLower β body (.erase .b)),
           (3 : R) ^ (nearyLower β body (.erase .b)).length, 0, 0, 0, 0]
  | true =>
      !![(1 : R), 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 1;
         0, 0, 0, 0, 1, 0;
         ternaryCode (nearyLower β body (.rule .c)),
           (3 : R) ^ (nearyLower β body (.rule .c)).length, 0, 0, 0, 0;
         ternaryCode (nearyUpper β (.rule .c)), 0,
           (3 : R) ^ (nearyUpper β (.rule .c)).length, 0, 0, 0;
         ternaryCode (nearyLower β body (.erase .c)),
           (3 : R) ^ (nearyLower β body (.erase .c)).length, 0, 0, 0, 0]

/-- Embed a payload row at a block boundary or after its first bit. -/
def pairedBinaryRow (R : Type*) [CommRing R] :
    Option PairPhase → (Fin 3 → R) → Fin 6 → R
  | none, vector => ![vector 0, vector 1, vector 2, 0, 0, 0]
  | some .rule, vector => ![vector 0, 0, 0, vector 1, vector 2, 0]
  | some .erase, vector => ![vector 0, 0, 0, 0, vector 2, vector 1]

private theorem vecSix_last {α : Type*} (a b c d e f : α) :
    (![a, b, c, d, e, f] : Fin 6 → α) 5 = f := rfl

theorem pairedBinaryRow_start (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (vector : Fin 3 → R) (bit : Bool) :
    pairedBinaryRow R none vector ᵥ* pairedBinaryGenerator R β body bit =
      pairedBinaryRow R (some (pairedBinaryPhase bit)) vector := by
  cases bit <;>
    funext i <;>
    fin_cases i <;>
    simp [pairedBinaryRow, pairedBinaryGenerator, pairedBinaryPhase, Matrix.vecHead,
      Matrix.vecTail, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_succ, vecSix_last]

theorem pairedBinaryRow_finish (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (vector : Fin 3 → R) (phase : PairPhase) (bit : Bool) :
    pairedBinaryRow R (some phase) vector ᵥ* pairedBinaryGenerator R β body bit =
      pairedBinaryRow R none
        (sidePcpMatrix R (nearyUpper β (phase.tile (pairedBinaryLetter bit)))
          (nearyLower β body (phase.tile (pairedBinaryLetter bit))) *ᵥ vector) := by
  cases phase <;>
    cases bit <;>
    funext i <;>
    fin_cases i <;>
    simp [pairedBinaryRow, pairedBinaryGenerator, pairedBinaryLetter, PairPhase.tile,
      sidePcpMatrix, nearyUpper, Matrix.vecHead, Matrix.vecTail, Matrix.vecMul,
      Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ, vecSix_last]
  all_goals ring

theorem pairedBinaryRow_pair (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (vector : Fin 3 → R) (phaseBit letterBit : Bool) :
    pairedBinaryRow R none vector ᵥ*
        (pairedBinaryGenerator R β body phaseBit *
          pairedBinaryGenerator R β body letterBit) =
      pairedBinaryRow R none
        (sidePcpMatrix R (nearyUpper β (pairedBinaryTile phaseBit letterBit))
          (nearyLower β body (pairedBinaryTile phaseBit letterBit)) *ᵥ vector) := by
  rw [← Matrix.vecMul_vecMul, pairedBinaryRow_start, pairedBinaryRow_finish]
  rfl

/-- Decode all complete blocks, in the role order represented by the resulting coefficient. -/
def decodePairedBinary : List Bool → List NearyTile
  | phaseBit :: letterBit :: rest =>
      decodePairedBinary rest ++ [pairedBinaryTile phaseBit letterBit]
  | _ => []

/-- The phase retained by an unfinished final block. -/
def pairedBinaryResidual : List Bool → Option PairPhase
  | _ :: _ :: rest => pairedBinaryResidual rest
  | [phaseBit] => some (pairedBinaryPhase phaseBit)
  | [] => none

private theorem pair_induction {α : Type*} {motive : List α → Prop}
    (nil : motive []) (singleton : ∀ head, motive [head])
    (pair : ∀ first second rest, motive rest → motive (first :: second :: rest)) :
    ∀ word, motive word
  | [] => nil
  | [head] => singleton head
  | first :: second :: rest =>
      pair first second rest (pair_induction nil singleton pair rest)

theorem pairedBinaryRow_wordProduct (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (vector : Fin 3 → R) (word : List Bool) :
    pairedBinaryRow R none vector ᵥ* wordProduct (pairedBinaryGenerator R β body) word =
      pairedBinaryRow R (pairedBinaryResidual word)
        (sideTileProduct R β body (decodePairedBinary word) *ᵥ vector) := by
  induction word using pair_induction generalizing vector with
  | nil =>
      simp [pairedBinaryResidual, decodePairedBinary, sideTileProduct]
  | singleton phaseBit =>
      simp only [wordProduct_cons, wordProduct_nil, mul_one]
      rw [pairedBinaryRow_start]
      simp [pairedBinaryResidual, decodePairedBinary, sideTileProduct]
  | pair phaseBit letterBit rest induction =>
      simp only [wordProduct_cons]
      rw [← Matrix.vecMul_vecMul, pairedBinaryRow_start, ← Matrix.vecMul_vecMul,
        pairedBinaryRow_finish, induction]
      simp only [decodePairedBinary, pairedBinaryResidual]
      rw [sideTileProduct_append]
      simp only [sideTileProduct, wordProduct_cons, wordProduct_nil, mul_one,
        Matrix.mulVec_mulVec]
      simp only [pairedBinaryTile]

/-- The fixed left boundary, containing the original three-state terminal column. -/
def pairedBinaryBoundaryRow (R : Type*) [CommRing R] (β : Nat) : Fin 6 → R :=
  pairedBinaryRow R none (sideTerminalColumn R (nearyMarker β))

/-- The first standard column extracts the completed coefficient in every residual phase. -/
def pairedBinaryBoundaryColumn (R : Type*) [CommRing R] : Fin 6 → R :=
  ![1, 0, 0, 0, 0, 0]

theorem pairedBinaryGenerator_transpose_fixes_boundaryColumn
    (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter) (bit : Bool) :
    (pairedBinaryGenerator R β body bit)ᵀ *ᵥ pairedBinaryBoundaryColumn R =
      pairedBinaryBoundaryColumn R := by
  cases bit <;>
    funext i <;>
    fin_cases i <;>
    simp [pairedBinaryGenerator, pairedBinaryBoundaryColumn, Matrix.vecHead, Matrix.vecTail,
      Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]

theorem pairedBinaryRow_dot_boundaryColumn (R : Type*) [CommRing R]
    (phase : Option PairPhase) (vector : Fin 3 → R) :
    pairedBinaryRow R phase vector ⬝ᵥ pairedBinaryBoundaryColumn R = vector 0 := by
  cases phase with
  | none => simp [pairedBinaryRow, pairedBinaryBoundaryColumn, Matrix.single_dotProduct]
  | some phase =>
      cases phase <;>
        simp [pairedBinaryRow, pairedBinaryBoundaryColumn, Matrix.single_dotProduct]

/-- Scalar series represented by the binary six-state compiler. -/
def pairedBinaryCoefficient (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (word : List Bool) : R :=
  pairedBinaryBoundaryRow R β ⬝ᵥ
    wordProduct (pairedBinaryGenerator R β body) word *ᵥ pairedBinaryBoundaryColumn R

theorem pairedBinaryCoefficient_eq_sideCoefficient (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (word : List Bool) :
    pairedBinaryCoefficient R β body word =
      sideCoefficient R β body (decodePairedBinary word) := by
  rw [pairedBinaryCoefficient, Matrix.dotProduct_mulVec, pairedBinaryBoundaryRow,
    pairedBinaryRow_wordProduct, pairedBinaryRow_dot_boundaryColumn]
  rfl

@[simp] theorem pairedBinaryCoefficient_nil (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) :
    pairedBinaryCoefficient R β body [] = (ternaryCode (nearyMarker β) : R) := by
  rw [pairedBinaryCoefficient_eq_sideCoefficient]
  simp [decodePairedBinary, sideCoefficient, sideTileProduct, sideTerminalColumn,
    sidePcpMatrix, sideTailBasis, Matrix.vecHead, Matrix.vecTail, Matrix.mulVec,
    Matrix.dotProduct, Fin.sum_univ_succ]

theorem pairedBinaryCoefficient_nil_ne_zero (β : Nat) (body : List TagLetter) :
    pairedBinaryCoefficient ℤ β body [] ≠ 0 := by
  rw [pairedBinaryCoefficient_nil]
  exact_mod_cast ternaryCode_nearyMarker_ne_zero β

theorem decodePairedBinary_surjective : Function.Surjective decodePairedBinary := by
  intro word
  induction' word using List.reverseRecOn with word tile induction
  · exact ⟨[], rfl⟩
  · obtain ⟨bits, decoded⟩ := induction
    refine ⟨pairedBinaryCode tile ++ bits, ?_⟩
    cases tile with
    | rule letter | erase letter =>
        cases letter <;>
          simp [pairedBinaryCode, decodePairedBinary, pairedBinaryTile, pairedBinaryPhase,
            pairedBinaryLetter, PairPhase.tile, decoded]

theorem pairedBinary_zero_iff_terminal_match (β : Nat) (body : List TagLetter) :
    WordSeries.HasNonemptyZero (pairedBinaryCoefficient ℤ β body) ↔
      ∃ word : List NearyTile,
        spell (nearyUpper β) word ++ nearyMarker β = spell (nearyLower β body) word := by
  constructor
  · rintro ⟨bits, _, coefficient_zero⟩
    refine ⟨decodePairedBinary bits, ?_⟩
    exact (sideCoefficient_eq_zero_iff_terminal_match β body _).mp
      (by simpa [pairedBinaryCoefficient_eq_sideCoefficient] using coefficient_zero)
  · rintro ⟨word, terminal_match⟩
    obtain ⟨bits, decoded⟩ := decodePairedBinary_surjective word
    have word_nonempty : word ≠ [] := by
      intro word_empty
      have marker_empty : nearyMarker β = [] := by
        simpa [word_empty, spell] using terminal_match
      simp [nearyMarker] at marker_empty
    have bits_nonempty : bits ≠ [] := by
      intro bits_empty
      apply word_nonempty
      calc
        word = decodePairedBinary bits := decoded.symm
        _ = decodePairedBinary [] := by rw [bits_empty]
        _ = [] := rfl
    refine ⟨bits, bits_nonempty, ?_⟩
    rw [pairedBinaryCoefficient_eq_sideCoefficient, decoded]
    exact (sideCoefficient_eq_zero_iff_terminal_match β body word).mpr terminal_match

theorem pairedBinary_zero_iff_tagHaltsFrom (β : Nat) (body : List TagLetter)
    (β_large : 2 < β) (body_long : β - 1 ≤ body.length)
    (body_divisible : β - 1 ∣ body.length) :
    WordSeries.HasNonemptyZero (pairedBinaryCoefficient ℤ β body) ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  rw [pairedBinary_zero_iff_terminal_match]
  exact terminal_match_iff_tagHaltsFrom β body β_large body_long body_divisible

end MatrixMortality
