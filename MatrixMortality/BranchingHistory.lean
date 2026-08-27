import MatrixMortality.PeriodicHistory

/-!
# Branching fracture of positional history sections

The adjacent width-three body `bcbc` admits two distinct null-history blocks of the same
length. Arbitrary binary concatenations remain null, giving an injective family of terminal
role words with `2^n` members at one length. A phase-blind affine section of the injective
positional decoder selects at most one word per length and therefore cannot recognize this
terminal language.
-/

namespace MatrixMortality

namespace BranchingHistory

open PeriodicHistory
open scoped Matrix

/-- The adjacent width-three Neary body `bcbc`. -/
def bcbcBody : List TagLetter := [.b, .c, .b, .c]

/-- The stroke `bcb`. -/
def strokeBCB : Stroke TagLetter 3 := stroke₃ .b .c .b

/-- A null history preserves the boundary queue `[b]` under `bcbc` production. -/
def bcbcNull (history : List (Stroke TagLetter 3)) : Prop :=
  consumed history ++ [.b] = [.b] ++ produced (tagOutput bcbcBody) history

private theorem consumed_append (left right : List (Stroke TagLetter 3)) :
    consumed (left ++ right) = consumed left ++ consumed right := by
  simp [consumed]

private theorem produced_append (left right : List (Stroke TagLetter 3)) :
    produced (tagOutput bcbcBody) (left ++ right) =
      produced (tagOutput bcbcBody) left ++ produced (tagOutput bcbcBody) right := by
  simp [produced]

theorem bcbcNull_append {left right : List (Stroke TagLetter 3)}
    (leftNull : bcbcNull left) (rightNull : bcbcNull right) :
    bcbcNull (left ++ right) := by
  rw [bcbcNull, consumed_append, produced_append]
  calc
    (consumed left ++ consumed right) ++ [.b] =
        consumed left ++ (consumed right ++ [.b]) := by simp [List.append_assoc]
    _ = consumed left ++ ([.b] ++ produced (tagOutput bcbcBody) right) := by
      rw [rightNull]
    _ = (consumed left ++ [.b]) ++ produced (tagOutput bcbcBody) right := by
      simp [List.append_assoc]
    _ = ([.b] ++ produced (tagOutput bcbcBody) left) ++
        produced (tagOutput bcbcBody) right := by rw [leftNull]
    _ = [.b] ++ (produced (tagOutput bcbcBody) left ++
        produced (tagOutput bcbcBody) right) := by simp

/-- Two short excursions concatenated into one four-stroke null block. -/
def flatBlock : List (Stroke TagLetter 3) :=
  [strokeBBB, strokeCBC, strokeBBB, strokeCBC]

/-- One four-stroke nested excursion. -/
def nestedBlock : List (Stroke TagLetter 3) :=
  [strokeBBB, strokeBCB, strokeCBB, strokeCBC]

/-- Select one of the two equal-length null blocks. -/
def forkBlock : Bool → List (Stroke TagLetter 3)
  | false => flatBlock
  | true => nestedBlock

@[simp] theorem flatBlock_null : bcbcNull flatBlock := by rfl

@[simp] theorem nestedBlock_null : bcbcNull nestedBlock := by rfl

@[simp] theorem forkBlock_null (bit : Bool) : bcbcNull (forkBlock bit) := by
  cases bit <;> simp [forkBlock]

@[simp] theorem forkBlock_length (bit : Bool) : (forkBlock bit).length = 4 := by
  cases bit <;> rfl

theorem forkBlock_injective : Function.Injective forkBlock := by
  intro left right equality
  cases left <;> cases right <;>
    simp [forkBlock, flatBlock, nestedBlock, strokeBCB, strokeCBC, strokeCBB, strokeBBB,
      stroke₃] at equality ⊢

/-- Concatenate the null block selected by each input bit. -/
def bcbcFork : List Bool → List (Stroke TagLetter 3)
  | [] => []
  | bit :: bits => forkBlock bit ++ bcbcFork bits

@[simp] theorem bcbcFork_null (bits : List Bool) : bcbcNull (bcbcFork bits) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      exact bcbcNull_append (forkBlock_null bit) induction

@[simp] theorem bcbcFork_length (bits : List Bool) :
    (bcbcFork bits).length = 4 * bits.length := by
  induction bits with
  | nil => rfl
  | cons bit bits induction => simp [bcbcFork, induction]; omega

/-- The twelve-role encoding of one selected null block. -/
def forkRoleBlock (bit : Bool) : List NearyTile := tileHistory (forkBlock bit)

@[simp] theorem forkRoleBlock_length (bit : Bool) : (forkRoleBlock bit).length = 12 := by
  cases bit <;> decide

theorem forkRoleBlock_injective : Function.Injective forkRoleBlock := by
  intro left right equality
  cases left <;> cases right <;>
    simp [forkRoleBlock, forkBlock, flatBlock, nestedBlock, strokeBCB, strokeCBC, strokeCBB,
      strokeBBB, stroke₃, tileHistory, strokeTiles] at equality ⊢

/-- Concatenate the role blocks selected by a bit word. -/
def bcbcForkRoles : List Bool → List NearyTile
  | [] => []
  | bit :: bits => forkRoleBlock bit ++ bcbcForkRoles bits

@[simp] theorem bcbcForkRoles_length (bits : List Bool) :
    (bcbcForkRoles bits).length = 12 * bits.length := by
  induction bits with
  | nil => rfl
  | cons bit bits induction => simp [bcbcForkRoles, induction]; omega

theorem bcbcForkRoles_injective : Function.Injective bcbcForkRoles := by
  intro left
  induction left with
  | nil =>
      intro right equality
      cases right with
      | nil => rfl
      | cons bit bits =>
          have lengths := congrArg List.length equality
          simp at lengths
  | cons leftBit leftBits induction =>
      intro right equality
      cases right with
      | nil =>
          have lengths := congrArg List.length equality
          simp at lengths
      | cons rightBit rightBits =>
          have block_eq := congrArg (List.take 12) equality
          simp [bcbcForkRoles] at block_eq
          have bit_eq := forkRoleBlock_injective block_eq
          subst rightBit
          have tail_eq := congrArg (List.drop 12) equality
          simp [bcbcForkRoles] at tail_eq
          exact congrArg (List.cons leftBit) (induction tail_eq)

private theorem tileHistory_append (left right : List (Stroke TagLetter 3)) :
    tileHistory (left ++ right) = tileHistory left ++ tileHistory right := by
  simp [tileHistory, List.map_append]

theorem bcbcForkRoles_eq_tileHistory (bits : List Bool) :
    bcbcForkRoles bits = tileHistory (bcbcFork bits) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      rw [bcbcForkRoles, bcbcFork, tileHistory_append, induction]
      rfl

/-- The fixed terminal prefix followed by a binary null-history fork. -/
def bcbcTerminalFork (bits : List Bool) : List NearyTile :=
  tileHistory [strokeCBC, strokeBCB] ++ bcbcForkRoles bits

@[simp] theorem bcbcTerminalFork_length (bits : List Bool) :
    (bcbcTerminalFork bits).length = 6 + 12 * bits.length := by
  simp [bcbcTerminalFork, strokeCBC, strokeBCB, stroke₃, strokeTiles]
  omega

theorem bcbcTerminalFork_injective : Function.Injective bcbcTerminalFork := by
  intro left right equality
  apply bcbcForkRoles_injective
  have tails := congrArg (List.drop 6) equality
  simpa [bcbcTerminalFork, tileHistory, strokeTiles, strokeCBC, strokeBCB, stroke₃]
    using tails

theorem bcbcTerminalFork_match (bits : List Bool) :
    spell (nearyUpper 3) (bcbcTerminalFork bits) ++ nearyMarker 3 =
      spell (nearyLower 3 bcbcBody) (bcbcTerminalFork bits) := by
  rw [bcbcTerminalFork, bcbcForkRoles_eq_tileHistory, ← tileHistory_append]
  apply (terminal_match_tileHistory_iff 3 bcbcBody (by decide)
    strokeCBC (strokeBCB :: bcbcFork bits)).mpr
  simpa [strokeCBC, strokeBCB, stroke₃, Stroke.letters, consumed_cons, produced_cons,
    bcbcBody, tagOutput, nearyBody, bcbcNull, List.append_assoc] using bcbcFork_null bits

/-- No single affine row section of the injective positional decoder recognizes the complete
`bcbc` terminal language. The two one-bit forks are distinct terminal words of equal length,
whereas one affine equation fixes one positional code at each length. -/
theorem no_affine_positional_section (κ α : ℚ) :
    ¬(∀ word : List NearyTile,
      κ + forwardHistoryCode word - α * 5 ^ word.length = 0 ↔
        spell (nearyUpper 3) word ++ nearyMarker 3 =
          spell (nearyLower 3 bcbcBody) word) := by
  intro same_zero
  have flat_zero := (same_zero (bcbcTerminalFork [false])).mpr
    (bcbcTerminalFork_match [false])
  have nested_zero := (same_zero (bcbcTerminalFork [true])).mpr
    (bcbcTerminalFork_match [true])
  have same_length :
      (bcbcTerminalFork [false]).length = (bcbcTerminalFork [true]).length := by simp
  have code_cast :
      (forwardHistoryCode (bcbcTerminalFork [false]) : ℚ) =
        forwardHistoryCode (bcbcTerminalFork [true]) := by
    rw [same_length] at flat_zero
    linarith
  have code_eq :
      forwardHistoryCode (bcbcTerminalFork [false]) =
        forwardHistoryCode (bcbcTerminalFork [true]) := by
    exact_mod_cast code_cast
  have word_eq := forwardHistoryCode_injective code_eq
  have bits_eq := bcbcTerminalFork_injective word_eq
  simp at bits_eq

/-! ## Near-fork collision -/

/-- The stroke `ccb`. -/
def strokeCCB : Stroke TagLetter 3 := stroke₃ .c .c .b

/-- A same-length nonterminal neighbor of the fixed `bcbc` terminal prefix. -/
def bcbcNearForkRoles : List NearyTile := tileHistory [strokeBCB, strokeCCB]

/-- A canonical control preimage of the fixed terminal prefix `cbc,bcb`. -/
def bcbcTerminalControl : List PairedControl :=
  [.data .c, .toggle, .data .b, .data .c,
    .data .b, .toggle, .data .c, .data .b, .toggle]

/-- A canonical control preimage of the nonterminal near-fork `bcb,ccb`. -/
def bcbcNearForkControl : List PairedControl :=
  [.data .b, .toggle, .data .c, .data .b,
    .data .c, .toggle, .data .c, .data .b, .toggle]

/-- Two erase-`b` roles used by the local cancellation witness. -/
def bcbcEraseSquareControl : List PairedControl := [.data .b, .data .b]

/-- The near-fork suffix `E_c E_b` followed by the terminal phase toggle. -/
def bcbcNearForkSuffixControl : List PairedControl :=
  [.data .c, .data .b, .toggle]

/-- The control product `DZ` in the stroke notation of the carry collision. -/
def bcbcForkLeftControl : List PairedControl :=
  [.data .b, .toggle, .data .c, .data .b,
    .data .c, .toggle, .data .b, .data .b]

/-- The control product `FX` in the stroke notation of the carry collision. -/
def bcbcForkRightControl : List PairedControl :=
  [.data .c, .toggle, .data .b, .data .c,
    .data .b, .toggle, .data .b, .data .b]

private theorem bcbcTerminalControl_decode :
    decodePairedWord bcbcTerminalControl = bcbcTerminalFork [] := by decide

private theorem bcbcNearForkControl_decode :
    decodePairedWord bcbcNearForkControl = bcbcNearForkRoles := by decide

/-- The fixed prefix control is a zero, while its six-role near-fork is not. -/
theorem bcbc_terminal_nearFork :
    pairedCoefficient ℚ 3 bcbcBody bcbcTerminalControl = 0 ∧
      pairedCoefficient ℚ 3 bcbcBody bcbcNearForkControl ≠ 0 := by
  constructor
  · rw [pairedCoefficient_eq_sideCoefficient, bcbcTerminalControl_decode]
    exact (sideCoefficient_eq_zero_iff_terminal_match_rat 3 bcbcBody _).mpr
      (bcbcTerminalFork_match [])
  · rw [pairedCoefficient_eq_sideCoefficient]
    intro zero
    have terminal :=
      (sideCoefficient_eq_zero_iff_terminal_match_rat 3 bcbcBody _).mp zero
    rw [bcbcNearForkControl_decode] at terminal
    have nearFork_not_terminal :
        spell (nearyUpper 3) bcbcNearForkRoles ++ nearyMarker 3 ≠
          spell (nearyLower 3 bcbcBody) bcbcNearForkRoles := by decide
    exact nearFork_not_terminal terminal

/-- A local `DZ=FX` fork identity and recovery through two erase-`b` steps make the terminal
prefix and the nonterminal near-fork reach the same state. The result is dimension-independent
and requires neither global cancellation nor invertible controls. -/
theorem bcbcNearFork_state_eq_of_local_fork {ι R : Type*} [Fintype ι]
    [DecidableEq ι] [Semiring R] (generators : PairedControl → Matrix ι ι R)
    (column witness : ι → R)
    (image :
      (wordProduct generators bcbcEraseSquareControl) *ᵥ witness =
        (wordProduct generators bcbcNearForkSuffixControl) *ᵥ column)
    (fork :
      (wordProduct generators bcbcForkLeftControl) *ᵥ witness =
        (wordProduct generators bcbcForkRightControl) *ᵥ witness) :
    (wordProduct generators bcbcNearForkControl) *ᵥ column =
      (wordProduct generators bcbcTerminalControl) *ᵥ column := by
  simp only [bcbcEraseSquareControl, bcbcNearForkSuffixControl, wordProduct,
    List.map, List.prod_cons, List.prod_nil, mul_one] at image
  simp only [bcbcForkLeftControl, bcbcForkRightControl, wordProduct, List.map,
    List.prod_cons, List.prod_nil, mul_one] at fork
  simp only [bcbcNearForkControl, bcbcTerminalControl, wordProduct, List.map,
    List.prod_cons, List.prod_nil, mul_one]
  simp only [← Matrix.mulVec_mulVec] at image fork ⊢
  rw [← image]
  exact fork

/-- No rational same-zero representation can satisfy the local fork and recovery identities. -/
theorem no_bcbc_sameZero_of_local_fork {ι : Type*} [Fintype ι] [DecidableEq ι]
    (generators : PairedControl → Matrix ι ι ℚ) (row column witness : ι → ℚ)
    (image :
      (wordProduct generators bcbcEraseSquareControl) *ᵥ witness =
        (wordProduct generators bcbcNearForkSuffixControl) *ᵥ column)
    (fork :
      (wordProduct generators bcbcForkLeftControl) *ᵥ witness =
        (wordProduct generators bcbcForkRightControl) *ᵥ witness) :
    ¬(∀ word,
      linearCoefficient generators row column word = 0 ↔
        pairedCoefficient ℚ 3 bcbcBody word = 0) := by
  intro same_zero
  have terminal_zero :
      linearCoefficient generators row column bcbcTerminalControl = 0 :=
    (same_zero bcbcTerminalControl).mpr bcbc_terminal_nearFork.1
  have states_equal :=
    bcbcNearFork_state_eq_of_local_fork generators column witness image fork
  have nearFork_zero :
      linearCoefficient generators row column bcbcNearForkControl = 0 := by
    rw [linearCoefficient, states_equal]
    exact terminal_zero
  exact bcbc_terminal_nearFork.2
    ((same_zero bcbcNearForkControl).mp nearFork_zero)

/-! ## Failure of the one-coordinate phase-line carry -/

/-- Erase-`b` matrix in the parametric phase-line carry family. -/
def phaseLineDataB (ρ : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 0, 0;
     0, 2 / (ρ + 1), ρ * (ρ + 1) ^ 2 / 4;
     0, 0, 0]

/-- Erase-`c` matrix in the parametric phase-line carry family. -/
def phaseLineDataC (ρ : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, ρ + 1, -(ρ * (ρ + 1) ^ 2 / 4);
     0, 2 / (ρ + 1), ρ * (ρ + 1) ^ 2 / 4;
     0, 0, 0]

/-- Phase swap in the parametric phase-line carry family. -/
def phaseLineToggle : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

/-- The proposed three common controls for a one-coordinate `bcbc` carry. -/
def phaseLineGenerator (ρ : ℚ) : PairedControl → Matrix (Fin 3) (Fin 3) ℚ
  | .data .b => phaseLineDataB ρ
  | .data .c => phaseLineDataC ρ
  | .toggle => phaseLineToggle

private def phaseLineDNormal (ρ : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 2, ρ * (ρ + 1) ^ 3 / 4;
     0, ρ, ρ ^ 2 * (ρ + 1) ^ 3 / 8;
     0, 0, 0]

private def phaseLineFNormal (ρ : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 1, -(ρ * (ρ + 1) ^ 2 * (ρ ^ 2 + ρ + 2) / 8);
     0, ρ, ρ ^ 2 * (ρ + 1) ^ 3 / 8;
     0, 0, 0]

private def phaseLineGNormal (ρ : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 2 - ρ, ρ * (ρ + 1) ^ 3 * (2 - ρ) / 8;
     0, ρ, ρ ^ 2 * (ρ + 1) ^ 3 / 8;
     0, 0, 0]

private theorem phaseLineD_eq (ρ : ℚ) (ρ_ne : ρ ≠ -1) :
    phaseLineDataB ρ * (phaseLineToggle * (phaseLineDataC ρ * phaseLineDataB ρ)) =
      phaseLineDNormal ρ := by
  have denominator : ρ + 1 ≠ 0 := by
    intro zero
    apply ρ_ne
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseLineDataB, phaseLineDataC, phaseLineToggle, phaseLineDNormal,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail]
  all_goals field_simp [denominator] <;> ring

private theorem phaseLineF_eq (ρ : ℚ) (ρ_ne : ρ ≠ -1) :
    phaseLineDataC ρ * (phaseLineToggle * (phaseLineDataB ρ * phaseLineDataC ρ)) =
      phaseLineFNormal ρ := by
  have denominator : ρ + 1 ≠ 0 := by
    intro zero
    apply ρ_ne
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseLineDataB, phaseLineDataC, phaseLineToggle, phaseLineFNormal,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail]
  all_goals field_simp [denominator]
  all_goals ring

private theorem phaseLineG_eq (ρ : ℚ) (ρ_ne : ρ ≠ -1) :
    phaseLineDataC ρ * (phaseLineToggle * (phaseLineDataC ρ * phaseLineDataB ρ)) =
      phaseLineGNormal ρ := by
  have denominator : ρ + 1 ≠ 0 := by
    intro zero
    apply ρ_ne
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseLineDataB, phaseLineDataC, phaseLineToggle, phaseLineGNormal,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail]
  all_goals field_simp [denominator]
  all_goals ring

private theorem phaseLineDG_eq_FD (ρ : ℚ) :
    phaseLineDNormal ρ * phaseLineGNormal ρ =
      phaseLineFNormal ρ * phaseLineDNormal ρ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseLineDNormal, phaseLineFNormal, phaseLineGNormal, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    ring

private def phaseLineDControl : List PairedControl :=
  [.data .b, .toggle, .data .c, .data .b]

private def phaseLineFControl : List PairedControl :=
  [.data .c, .toggle, .data .b, .data .c]

private def phaseLineGControl : List PairedControl :=
  [.data .c, .toggle, .data .c, .data .b]

/-- Every parameter away from its denominator pole makes the phase-line family identify the
terminal prefix with the nonterminal near-fork as full matrices, not merely as projective maps. -/
theorem phaseLine_terminal_eq_nearFork (ρ : ℚ) (ρ_ne : ρ ≠ -1) :
    wordProduct (phaseLineGenerator ρ) bcbcTerminalControl =
      wordProduct (phaseLineGenerator ρ) bcbcNearForkControl := by
  rw [show bcbcTerminalControl =
      phaseLineFControl ++ phaseLineDControl ++ [.toggle] by rfl]
  rw [show bcbcNearForkControl =
      phaseLineDControl ++ phaseLineGControl ++ [.toggle] by rfl]
  rw [wordProduct_append, wordProduct_append, wordProduct_append, wordProduct_append]
  simp only [phaseLineDControl, phaseLineFControl, phaseLineGControl, phaseLineGenerator,
    wordProduct, List.map, List.prod_cons, List.prod_nil, mul_one]
  rw [phaseLineD_eq ρ ρ_ne, phaseLineF_eq ρ ρ_ne, phaseLineG_eq ρ ρ_ne]
  rw [phaseLineDG_eq_FD]

/-- No choice of row and column turns the parametric phase-line family into a same-zero
recognizer for `bcbc`. -/
theorem no_phaseLine_bcbc_sameZero (ρ : ℚ) (ρ_ne : ρ ≠ -1)
    (row column : Fin 3 → ℚ) :
    ¬(∀ word,
      linearCoefficient (phaseLineGenerator ρ) row column word = 0 ↔
        pairedCoefficient ℚ 3 bcbcBody word = 0) := by
  intro same_zero
  have terminal_zero :
      linearCoefficient (phaseLineGenerator ρ) row column bcbcTerminalControl = 0 :=
    (same_zero bcbcTerminalControl).mpr bcbc_terminal_nearFork.1
  have nearFork_zero :
      linearCoefficient (phaseLineGenerator ρ) row column bcbcNearForkControl = 0 := by
    rw [linearCoefficient, ← phaseLine_terminal_eq_nearFork ρ ρ_ne]
    exact terminal_zero
  exact bcbc_terminal_nearFork.2
    ((same_zero bcbcNearForkControl).mp nearFork_zero)

end BranchingHistory

end MatrixMortality
