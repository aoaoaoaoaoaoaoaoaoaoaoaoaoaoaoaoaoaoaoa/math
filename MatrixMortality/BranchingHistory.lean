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

/-- The adjacent width-three Neary body `bcbc`. -/
def bcbcBody : List TagLetter := [.b, .c, .b, .c]

/-- The stroke `bcb`. -/
def strokeBCB : Stroke TagLetter 3 := stroke₃ .b .c .b

/-- A null history preserves the boundary queue `[b]` under `bcbc` production. -/
def bcbcNull (history : List (Stroke TagLetter 3)) : Prop :=
  consumed history ++ [.b] = [.b] ++ produced (tagOutput bcbcBody) history

private theorem consumed_append (left right : List (Stroke TagLetter 3)) :
    consumed (left ++ right) = consumed left ++ consumed right := by
  simp [consumed, List.map_append]

private theorem produced_append (left right : List (Stroke TagLetter 3)) :
    produced (tagOutput bcbcBody) (left ++ right) =
      produced (tagOutput bcbcBody) left ++ produced (tagOutput bcbcBody) right := by
  simp [produced, List.map_append]

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
        produced (tagOutput bcbcBody) right) := by simp [List.append_assoc]

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
  simpa [bcbcTerminalFork] using tails

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

end BranchingHistory

end MatrixMortality
