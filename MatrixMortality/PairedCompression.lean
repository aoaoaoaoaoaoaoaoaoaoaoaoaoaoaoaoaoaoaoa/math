import MatrixMortality.TwoStatePushout

/-!
# Paired-role compression

Neary's rule and erasure tile for a fixed tag letter have the same upper word.  In a basis
separating the two PCP channels, they therefore agree on a two-dimensional plane.  This file
implements the resulting four-dimensional quotient explicitly and proves its coefficient
identity for every word over the two data generators and the phase toggle.
-/

namespace MatrixMortality

open scoped Matrix

/-- Two paired data generators and one phase toggle. -/
inductive PairedControl where
  | data : TagLetter → PairedControl
  | toggle
  deriving DecidableEq, Fintype, Repr

/-- The data generator selecting the rule or erasure role according to the current phase. -/
def pairedDataMatrix (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter)
    (letter : TagLetter) : Matrix (Fin 4) (Fin 4) R :=
  twoStateDataMatrix R
    (fun symbol => nearyUpper β (.rule symbol))
    (fun phase symbol => nearyLower β body (phase.tile symbol))
    (fun _ _ => .erase)
    letter

/-- Coordinate normal form of the paired data generator.

The implementation is the generic finite-controller pushout; this theorem is the stable
certificate consumed by coordinate calculations. -/
theorem pairedDataMatrix_eq_explicit (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (letter : TagLetter) :
    pairedDataMatrix R β body letter =
      !![(1 : R), ternaryCode (nearyLower β body (.rule letter)),
          ternaryCode (nearyUpper β (.rule letter)),
          ternaryCode (nearyLower β body (.erase letter));
         0, 0, 0, 0;
         0, 0, (3 : R) ^ (nearyUpper β (.rule letter)).length, 0;
         0, (3 : R) ^ (nearyLower β body (.rule letter)).length, 0,
          (3 : R) ^ (nearyLower β body (.erase letter)).length] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairedDataMatrix, twoStateDataMatrix, controllerMatrix, pairControllerEquiv,
      PairPhase.tile, Matrix.reindex_apply, Matrix.vecHead, Matrix.vecTail]

/-- The integral phase-swap matrix. -/
def pairedToggleMatrix (R : Type*) [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  Matrix.reindex pairControllerEquiv pairControllerEquiv
    (controllerStateMatrix R PairPhase.flip)

/-- Coordinate normal form of the paired phase toggle. -/
theorem pairedToggleMatrix_eq_explicit (R : Type*) [CommRing R] :
    pairedToggleMatrix R =
      !![(1 : R), 0, 0, 0;
         0, 0, 0, 1;
         0, 0, 1, 0;
         0, 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairedToggleMatrix, controllerStateMatrix, controllerMatrix, pairControllerEquiv,
      PairPhase.flip, Matrix.reindex_apply, Matrix.vecHead, Matrix.vecTail]

/-- The phase toggle swaps one-based coordinates two and four,
equivalently `Fin 4` indices `1` and `3`. -/
theorem pairedToggleMatrix_eq_permMatrix (R : Type*) [CommRing R] :
    pairedToggleMatrix R = (Equiv.swap (1 : Fin 4) 3).permMatrix R := by
  ext i j
  change pairedToggleMatrix R i j =
    (Equiv.swap (1 : Fin 4) 3).toPEquiv.toMatrix i j
  rw [PEquiv.equiv_toPEquiv_toMatrix]
  fin_cases i <;> fin_cases j <;>
    simp [pairedToggleMatrix, controllerStateMatrix, controllerMatrix, pairControllerEquiv,
      PairPhase.flip, Equiv.swap_apply_def, Matrix.one_apply, Matrix.vecHead, Matrix.vecTail]

/-- The three compressed control generators. -/
def pairedGenerator (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter) :
    PairedControl → Matrix (Fin 4) (Fin 4) R
  | .data letter => pairedDataMatrix R β body letter
  | .toggle => pairedToggleMatrix R

/-- Multiply a word over the compressed control alphabet. -/
def pairedProduct (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter)
    (word : List PairedControl) : Matrix (Fin 4) (Fin 4) R :=
  wordProduct (pairedGenerator R β body) word

theorem pairedToggleMatrix_mulVec_phaseVector (R : Type*) [CommRing R]
    (phase : PairPhase) (vector : Fin 3 → R) :
    pairedToggleMatrix R *ᵥ phaseVector R phase vector = phaseVector R phase.flip vector := by
  rw [pairedToggleMatrix, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  simp only [Equiv.symm_symm]
  rw [phaseVector_comp_pairControllerEquiv,
    controllerStateMatrix_mulVec_controllerVector]
  rfl

theorem pairedDataMatrix_mulVec_phaseVector (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (letter : TagLetter) (phase : PairPhase)
    (vector : Fin 3 → R) :
    pairedDataMatrix R β body letter *ᵥ phaseVector R phase vector =
      phaseVector R .erase
        (sidePcpMatrix R (nearyUpper β (phase.tile letter))
          (nearyLower β body (phase.tile letter)) *ᵥ vector) := by
  rw [pairedDataMatrix, twoStateDataMatrix_mulVec_phaseVector]
  cases phase <;> rfl

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
          simp only [pairedProduct, wordProduct_cons, pairedGenerator]
          rw [← Matrix.mulVec_mulVec]
          change pairedToggleMatrix R *ᵥ
            (pairedProduct R β body word *ᵥ pairedColumn R β) = _
          rw [ih, pairedToggleMatrix_mulVec_phaseVector]
          rfl
      | data letter =>
          simp only [pairedProduct, wordProduct_cons, pairedGenerator]
          rw [← Matrix.mulVec_mulVec]
          change pairedDataMatrix R β body letter *ᵥ
            (pairedProduct R β body word *ᵥ pairedColumn R β) = _
          rw [ih, pairedDataMatrix_mulVec_phaseVector]
          simp only [suffixDecode, decodePairedWord, sideTileProduct, wordProduct_cons]
          rw [Matrix.mulVec_mulVec]

theorem pairedRow_dot_phaseVector (R : Type*) [CommRing R] (phase : PairPhase)
    (vector : Fin 3 → R) : pairedRow R ⬝ᵥ phaseVector R phase vector = vector 0 := by
  simpa [pairedRow, Matrix.dotProduct, Fin.sum_univ_succ] using phaseHead R phase vector

/-- The scalar coefficient recognized by the compressed control representation. -/
def pairedCoefficient (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter)
    (word : List PairedControl) : R :=
  pairedRow R ⬝ᵥ pairedProduct R β body word *ᵥ pairedColumn R β

theorem pairedCoefficient_eq_sideCoefficient (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (word : List PairedControl) :
    pairedCoefficient R β body word = sideCoefficient R β body (decodePairedWord word) := by
  rw [pairedCoefficient, pairedProduct_mulVec_column,
    pairedRow_dot_phaseVector]
  rfl

@[simp] theorem pairedCoefficient_nil (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) :
    pairedCoefficient R β body [] = (ternaryCode (nearyMarker β) : R) := by
  rw [pairedCoefficient_eq_sideCoefficient]
  simp [decodePairedWord, suffixDecode]

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
