import MatrixMortality.NearyEncoding
import MatrixMortality.PCPEncoding

/-!
# Paired-role compression

Neary's rule and erasure tile for a fixed tag letter have the same upper word.  In a basis
separating the two PCP channels, they therefore agree on a two-dimensional plane.  This file
implements the resulting four-dimensional quotient explicitly and proves its coefficient
identity for every word over the two data generators and the phase toggle.
-/

namespace MatrixMortality

open scoped Matrix

/-- The PCP representation after separating its lower- and upper-word channels. -/
def sidePcpMatrix (R : Type*) [CommRing R] (x y : List Bool) : Matrix (Fin 3) (Fin 3) R :=
  !![(1 : R), ternaryCode y, ternaryCode x;
     0, (3 : R) ^ y.length, 0;
     0, 0, (3 : R) ^ x.length]

/-- The unimodular change of basis separating the two word channels. -/
def sideChange (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![(1 : R), 0, 0;
     0, 1, 1;
     0, 0, 1]

/-- The inverse of `sideChange`. -/
def sideChangeInv (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![(1 : R), 0, 0;
     0, 1, -1;
     0, 0, 1]

theorem sideChangeInv_mul_sideChange (R : Type*) [CommRing R] :
    sideChangeInv R * sideChange R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sideChangeInv, sideChange, Matrix.vecHead, Matrix.vecTail, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem sideChange_mul_sideChangeInv (R : Type*) [CommRing R] :
    sideChange R * sideChangeInv R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sideChangeInv, sideChange, Matrix.vecHead, Matrix.vecTail, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem sidePcpMatrix_eq_conjugate (R : Type*) [CommRing R] (x y : List Bool) :
    sidePcpMatrix R x y = sideChangeInv R * pcpMatrix R x y * sideChange R := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sidePcpMatrix, sideChangeInv, sideChange, pcpMatrix, Matrix.vecHead,
      Matrix.vecTail, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

@[simp] theorem sidePcpMatrix_nil (R : Type*) [CommRing R] :
    sidePcpMatrix R [] [] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sidePcpMatrix, Matrix.vecHead, Matrix.vecTail]

theorem sidePcpMatrix_append (R : Type*) [CommRing R] (x y x' y' : List Bool) :
    sidePcpMatrix R (x ++ x') (y ++ y') =
      sidePcpMatrix R x y * sidePcpMatrix R x' y' := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sidePcpMatrix, Matrix.vecHead, Matrix.vecTail, Matrix.mul_apply,
      Fin.sum_univ_succ, ternaryCode_append]
  all_goals ring

/-- The transformed right selector `P⁻¹e₃`. -/
def sideTailBasis (R : Type*) [CommRing R] : Fin 3 → R := ![0, -1, 1]

/-- The transformed fixed-boundary column. -/
def sideTerminalColumn (R : Type*) [CommRing R] (marker : List Bool) : Fin 3 → R :=
  sidePcpMatrix R marker [] *ᵥ sideTailBasis R

/-- Product of the side-normal matrices named by a Neary role word. -/
def sideTileProduct (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter)
    (word : List NearyTile) : Matrix (Fin 3) (Fin 3) R :=
  (word.map fun tile => sidePcpMatrix R (nearyUpper β tile) (nearyLower β body tile)).prod

theorem sideTileProduct_eq_sidePcpMatrix (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (word : List NearyTile) :
    sideTileProduct R β body word =
      sidePcpMatrix R (spell (nearyUpper β) word) (spell (nearyLower β body) word) := by
  induction word with
  | nil => simp [sideTileProduct, spell]
  | cons tile word ih =>
      simp only [sideTileProduct, spell, List.map_cons, List.prod_cons]
      rw [show (word.map fun next =>
          sidePcpMatrix R (nearyUpper β next) (nearyLower β body next)).prod =
        sideTileProduct R β body word from rfl]
      rw [ih, ← sidePcpMatrix_append]
      rfl

/-- The upper-word plane in side-normal coordinates. -/
def UpperSide {R : Type*} [CommRing R] (vector : Fin 3 → R) : Prop := vector 1 = 0

/-- A rule and its erasure role agree on the complete two-dimensional upper-word plane. -/
theorem rule_erase_agree_on_upperSide (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (letter : TagLetter) (vector : Fin 3 → R)
    (upperSide : UpperSide vector) :
    sidePcpMatrix R (nearyUpper β (.rule letter)) (nearyLower β body (.rule letter)) *ᵥ
        vector =
      sidePcpMatrix R (nearyUpper β (.erase letter)) (nearyLower β body (.erase letter)) *ᵥ
        vector := by
  change vector 1 = 0 at upperSide
  funext i
  fin_cases i <;>
    simp [sidePcpMatrix, nearyUpper, Matrix.vecHead, Matrix.vecTail,
      Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ, upperSide]

/-- Which member of a rule/erasure pair a data generator selects. -/
inductive PairPhase where
  | rule
  | erase
  deriving DecidableEq, Repr

/-- Toggle the suffix-controlled member of a role pair. -/
def PairPhase.flip : PairPhase → PairPhase
  | .rule => .erase
  | .erase => .rule

/-- Recover the selected Neary role. -/
def PairPhase.tile : PairPhase → TagLetter → NearyTile
  | .rule, letter => .rule letter
  | .erase, letter => .erase letter

/-- Two paired data generators and one phase toggle. -/
inductive PairedControl where
  | data : TagLetter → PairedControl
  | toggle
  deriving DecidableEq, Fintype, Repr

/-- Embed one three-dimensional phase vector in the explicit four-dimensional quotient. -/
def phaseVector (R : Type*) [CommRing R] : PairPhase → (Fin 3 → R) → Fin 4 → R
  | .rule, vector => ![vector 0, vector 1, vector 2, 0]
  | .erase, vector => ![vector 0, 0, vector 2, vector 1]

/-- The data generator selecting the rule or erasure role according to the current phase. -/
def pairedDataMatrix (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter)
    (letter : TagLetter) : Matrix (Fin 4) (Fin 4) R :=
  !![(1 : R), ternaryCode (nearyLower β body (.rule letter)),
      ternaryCode (nearyUpper β (.rule letter)),
      ternaryCode (nearyLower β body (.erase letter));
     0, 0, 0, 0;
     0, 0, (3 : R) ^ (nearyUpper β (.rule letter)).length, 0;
     0, (3 : R) ^ (nearyLower β body (.rule letter)).length, 0,
      (3 : R) ^ (nearyLower β body (.erase letter)).length]

/-- The integral phase-swap matrix. -/
def pairedToggleMatrix (R : Type*) [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  !![(1 : R), 0, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0;
     0, 1, 0, 0]

/-- The phase toggle is the permutation matrix swapping the two lower-word coordinates. -/
theorem pairedToggleMatrix_eq_permMatrix (R : Type*) [CommRing R] :
    pairedToggleMatrix R = (Equiv.swap (1 : Fin 4) 3).permMatrix R := by
  ext i j
  change pairedToggleMatrix R i j =
    (Equiv.swap (1 : Fin 4) 3).toPEquiv.toMatrix i j
  rw [PEquiv.equiv_toPEquiv_toMatrix]
  fin_cases i <;> fin_cases j <;>
    simp [pairedToggleMatrix, Equiv.swap_apply_def, Matrix.one_apply, Matrix.vecHead,
      Matrix.vecTail]

/-- The three compressed control generators. -/
def pairedGenerator (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter) :
    PairedControl → Matrix (Fin 4) (Fin 4) R
  | .data letter => pairedDataMatrix R β body letter
  | .toggle => pairedToggleMatrix R

/-- Multiply a word over the compressed control alphabet. -/
def pairedProduct (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter)
    (word : List PairedControl) : Matrix (Fin 4) (Fin 4) R :=
  (word.map (pairedGenerator R β body)).prod

theorem pairedToggleMatrix_mulVec_phaseVector (R : Type*) [CommRing R]
    (phase : PairPhase) (vector : Fin 3 → R) :
    pairedToggleMatrix R *ᵥ phaseVector R phase vector = phaseVector R phase.flip vector := by
  funext i
  cases phase <;> fin_cases i <;>
    simp [pairedToggleMatrix, phaseVector, PairPhase.flip, Matrix.vecHead, Matrix.vecTail,
      Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]

theorem pairedDataMatrix_mulVec_phaseVector (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (letter : TagLetter) (phase : PairPhase)
    (vector : Fin 3 → R) :
    pairedDataMatrix R β body letter *ᵥ phaseVector R phase vector =
      phaseVector R .erase
        (sidePcpMatrix R (nearyUpper β (phase.tile letter))
          (nearyLower β body (phase.tile letter)) *ᵥ vector) := by
  funext i
  cases phase <;> fin_cases i <;>
    simp [pairedDataMatrix, phaseVector, PairPhase.tile, nearyUpper, Matrix.vecHead,
      Matrix.vecTail, sidePcpMatrix, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]
  all_goals ring

/-- Right-to-left control decoding, retaining the phase seen by a further letter on the left. -/
def suffixDecode : List PairedControl → PairPhase × List NearyTile
  | [] => (.rule, [])
  | .toggle :: word =>
      let decoded := suffixDecode word
      (decoded.1.flip, decoded.2)
  | .data letter :: word =>
      let decoded := suffixDecode word
      (.erase, decoded.1.tile letter :: decoded.2)

/-- The role word assigned to an arbitrary compressed control word. -/
def decodePairedWord (word : List PairedControl) : List NearyTile := (suffixDecode word).2

/-- The fixed-boundary column in the compressed representation. -/
def pairedColumn (R : Type*) [CommRing R] (β : Nat) : Fin 4 → R :=
  phaseVector R .rule (sideTerminalColumn R (nearyMarker β))

/-- The left row selecting the common first coordinate. -/
def pairedRow (R : Type*) [CommRing R] : Fin 4 → R := ![1, 0, 0, 0]

/-- The first standard column fixed by every compressed control generator. -/
def pairedAnchor (R : Type*) [CommRing R] : Fin 4 → R := ![1, 0, 0, 0]

theorem pairedProduct_mulVec_column (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (word : List PairedControl) :
    pairedProduct R β body word *ᵥ pairedColumn R β =
      phaseVector R (suffixDecode word).1
        (sideTileProduct R β body (decodePairedWord word) *ᵥ
          sideTerminalColumn R (nearyMarker β)) := by
  induction word with
  | nil => simp [pairedProduct, pairedColumn, suffixDecode, decodePairedWord, sideTileProduct]
  | cons control word ih =>
      cases control with
      | toggle =>
          simp only [pairedProduct, List.map_cons, List.prod_cons, pairedGenerator]
          rw [← Matrix.mulVec_mulVec]
          change pairedToggleMatrix R *ᵥ
            (pairedProduct R β body word *ᵥ pairedColumn R β) = _
          rw [ih, pairedToggleMatrix_mulVec_phaseVector]
          rfl
      | data letter =>
          simp only [pairedProduct, List.map_cons, List.prod_cons, pairedGenerator]
          rw [← Matrix.mulVec_mulVec]
          change pairedDataMatrix R β body letter *ᵥ
            (pairedProduct R β body word *ᵥ pairedColumn R β) = _
          rw [ih, pairedDataMatrix_mulVec_phaseVector]
          simp only [suffixDecode, decodePairedWord, sideTileProduct, List.map_cons,
            List.prod_cons]
          rw [Matrix.mulVec_mulVec]

theorem pairedRow_dot_phaseVector (R : Type*) [CommRing R] (phase : PairPhase)
    (vector : Fin 3 → R) : pairedRow R ⬝ᵥ phaseVector R phase vector = vector 0 := by
  cases phase <;>
    simp [pairedRow, phaseVector, Matrix.single_dotProduct]

/-- The scalar coefficient recognized by the compressed control representation. -/
def pairedCoefficient (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter)
    (word : List PairedControl) : R :=
  pairedRow R ⬝ᵥ pairedProduct R β body word *ᵥ pairedColumn R β

/-- The corresponding coefficient of one side-normal role word. -/
def sideCoefficient (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter)
    (word : List NearyTile) : R :=
  (sideTileProduct R β body word *ᵥ sideTerminalColumn R (nearyMarker β)) 0

theorem pairedCoefficient_eq_sideCoefficient (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (word : List PairedControl) :
    pairedCoefficient R β body word = sideCoefficient R β body (decodePairedWord word) := by
  rw [pairedCoefficient, pairedProduct_mulVec_column,
    pairedRow_dot_phaseVector]
  rfl

@[simp] theorem pairedCoefficient_nil (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) :
    pairedCoefficient R β body [] = (ternaryCode (nearyMarker β) : R) := by
  simp [pairedCoefficient, pairedProduct, pairedColumn, pairedRow, phaseVector,
    sideTerminalColumn, sidePcpMatrix, sideTailBasis, Matrix.vecHead, Matrix.vecTail,
    Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]

theorem sidePcpMatrix_mulVec_sideTailBasis_head (x y : List Bool) :
    (sidePcpMatrix ℤ x y *ᵥ sideTailBasis ℤ) 0 =
      (ternaryCode x : ℤ) - ternaryCode y := by
  simp [sidePcpMatrix, sideTailBasis, Matrix.vecHead, Matrix.vecTail, Matrix.mulVec,
    Matrix.dotProduct, Fin.sum_univ_succ]
  ring

theorem sidePcpMatrix_mulVec_sideTailBasis_head_rat (x y : List Bool) :
    (sidePcpMatrix ℚ x y *ᵥ sideTailBasis ℚ) 0 =
      (ternaryCode x : ℚ) - ternaryCode y := by
  simp [sidePcpMatrix, sideTailBasis, Matrix.vecHead, Matrix.vecTail, Matrix.mulVec,
    Matrix.dotProduct, Fin.sum_univ_succ]
  ring

theorem sideCoefficient_eq_zero_iff_terminal_match (β : Nat) (body : List TagLetter)
    (word : List NearyTile) :
    sideCoefficient ℤ β body word = 0 ↔
      spell (nearyUpper β) word ++ nearyMarker β = spell (nearyLower β body) word := by
  rw [sideCoefficient, sideTerminalColumn, Matrix.mulVec_mulVec,
    sideTileProduct_eq_sidePcpMatrix, ← sidePcpMatrix_append]
  rw [sidePcpMatrix_mulVec_sideTailBasis_head, sub_eq_zero, Int.ofNat_inj]
  simpa using ternaryCode_injective.eq_iff

theorem sideCoefficient_eq_zero_iff_terminal_match_rat (β : Nat) (body : List TagLetter)
    (word : List NearyTile) :
    sideCoefficient ℚ β body word = 0 ↔
      spell (nearyUpper β) word ++ nearyMarker β = spell (nearyLower β body) word := by
  rw [sideCoefficient, sideTerminalColumn, Matrix.mulVec_mulVec,
    sideTileProduct_eq_sidePcpMatrix, ← sidePcpMatrix_append]
  rw [sidePcpMatrix_mulVec_sideTailBasis_head_rat, sub_eq_zero, Nat.cast_inj]
  simpa using ternaryCode_injective.eq_iff

theorem decodePairedWord_surjective : Function.Surjective decodePairedWord := by
  intro word
  induction word with
  | nil => exact ⟨[], rfl⟩
  | cons tile word ih =>
      obtain ⟨control, hcontrol⟩ := ih
      cases hstate : suffixDecode control with
      | mk phase decoded =>
          have decoded_eq : decoded = word := by
            simpa [decodePairedWord, hstate] using hcontrol
          cases tile with
          | rule letter =>
              cases phase with
              | rule =>
                  refine ⟨.data letter :: control, ?_⟩
                  simp [decodePairedWord, suffixDecode, hstate, PairPhase.tile, decoded_eq]
              | erase =>
                  refine ⟨.data letter :: .toggle :: control, ?_⟩
                  simp [decodePairedWord, suffixDecode, hstate, PairPhase.tile, PairPhase.flip,
                    decoded_eq]
          | erase letter =>
              cases phase with
              | rule =>
                  refine ⟨.data letter :: .toggle :: control, ?_⟩
                  simp [decodePairedWord, suffixDecode, hstate, PairPhase.tile, PairPhase.flip,
                    decoded_eq]
              | erase =>
                  refine ⟨.data letter :: control, ?_⟩
                  simp [decodePairedWord, suffixDecode, hstate, PairPhase.tile, decoded_eq]

/-- Nonempty scalar zero reachability for the three compressed matrices. -/
def HasPairedZero (β : Nat) (body : List TagLetter) : Prop :=
  ∃ word : List PairedControl, word ≠ [] ∧ pairedCoefficient ℤ β body word = 0

theorem paired_zero_iff_terminal_match (β : Nat) (body : List TagLetter) :
    HasPairedZero β body ↔
      ∃ word : List NearyTile,
        spell (nearyUpper β) word ++ nearyMarker β = spell (nearyLower β body) word := by
  constructor
  · rintro ⟨control, _, coefficient_zero⟩
    refine ⟨decodePairedWord control, ?_⟩
    exact (sideCoefficient_eq_zero_iff_terminal_match β body _).mp
      (by simpa [pairedCoefficient_eq_sideCoefficient] using coefficient_zero)
  · rintro ⟨word, terminal_match⟩
    obtain ⟨control, decoded⟩ := decodePairedWord_surjective word
    have word_nonempty : word ≠ [] := by
      intro word_empty
      have marker_empty : nearyMarker β = [] := by
        simpa [word_empty, spell] using terminal_match
      simp [nearyMarker] at marker_empty
    have control_nonempty : control ≠ [] := by
      intro control_empty
      apply word_nonempty
      calc
        word = decodePairedWord control := decoded.symm
        _ = decodePairedWord [] := by rw [control_empty]
        _ = [] := rfl
    refine ⟨control, control_nonempty, ?_⟩
    rw [pairedCoefficient_eq_sideCoefficient, decoded]
    exact (sideCoefficient_eq_zero_iff_terminal_match β body word).mpr terminal_match

theorem paired_zero_iff_tagHaltsFrom (β : Nat) (body : List TagLetter)
    (β_large : 2 < β) (body_long : β - 1 ≤ body.length)
    (body_divisible : β - 1 ∣ body.length) :
    HasPairedZero β body ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  rw [paired_zero_iff_terminal_match]
  exact terminal_match_iff_tagHaltsFrom β body β_large body_long body_divisible

end MatrixMortality
