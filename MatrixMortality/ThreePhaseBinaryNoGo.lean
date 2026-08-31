import MatrixMortality.ParabolicRetunedObstruction

/-!
# Three-phase binary factorization obstruction

The four Neary role pairs have an exact positional factorization through three binary phases.
The other four vertices of the resulting binary cube are malformed roles.  On the admissible
nonhalting instance `(β, body) = (3, bbcc)`, six cube vertices satisfy the terminal equation.
The factorization therefore cannot supply the arbitrary-word converse for the direct cyclic
decoder.
-/

namespace MatrixMortality

namespace ThreePhaseBinaryNoGo

/-- The cyclic positions of one physical block. -/
inductive BlockPhase where
  | rule
  | body
  | letter
  deriving DecidableEq, Repr

/-- One physical three-bit block, separated into its rule, body, and letter phases. -/
structure Block where
  /-- Bit selected at the rule phase. -/
  rule : Bool
  /-- Bit selected at the body phase. -/
  body : Bool
  /-- Bit selected at the letter phase. -/
  letter : Bool
  deriving DecidableEq, Repr

/-- Bit read at one position of a physical block. -/
def Block.bit (block : Block) : BlockPhase → Bool
  | .rule => block.rule
  | .body => block.body
  | .letter => block.letter

/-- The body fragment left after the common `11` prefix and final `0` of the rule-`c` word. -/
def ruleCMiddle (β : Nat) (body : List TagLetter) : List Bool :=
  (tagEncode β body).tail ++ [true]

/-- Upper fragment emitted at one position. -/
def phaseUpper (β : Nat) : BlockPhase → Bool → List Bool
  | .rule, _ => []
  | .body, _ => []
  | .letter, bit => tagCode β (if bit then .c else .b)

/-- Lower fragment emitted at one position. -/
def phaseLower (β : Nat) (body : List TagLetter) : BlockPhase → Bool → List Bool
  | .rule, bit => if bit then [] else [true, true]
  | .body, bit => if bit then ruleCMiddle β body else []
  | .letter, _ => [false]

/-- Upper word emitted by the three consecutive positions of one block. -/
def upper (β : Nat) (block : Block) : List Bool :=
  phaseUpper β .rule block.rule ++ phaseUpper β .body block.body ++
    phaseUpper β .letter block.letter

/-- Lower word emitted by the three consecutive positions of one block. -/
def lower (β : Nat) (body : List TagLetter) (block : Block) : List Bool :=
  phaseLower β body .rule block.rule ++ phaseLower β body .body block.body ++
    phaseLower β body .letter block.letter

/-- Three-state PCP factor carried by one physical position. -/
def phaseMatrix (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter)
    (phase : BlockPhase) (bit : Bool) : Matrix (Fin 3) (Fin 3) R :=
  sidePcpMatrix R (phaseUpper β phase bit) (phaseLower β body phase bit)

/-- Product of the three position-dependent factors selected by one block. -/
def blockMatrix (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter)
    (block : Block) : Matrix (Fin 3) (Fin 3) R :=
  phaseMatrix R β body .rule block.rule * phaseMatrix R β body .body block.body *
    phaseMatrix R β body .letter block.letter

/-- Every cube vertex is exactly the PCP matrix of its emitted word pair. -/
theorem blockMatrix_eq_sidePcpMatrix (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (block : Block) :
    blockMatrix R β body block = sidePcpMatrix R (upper β block) (lower β body block) := by
  rw [blockMatrix, phaseMatrix, phaseMatrix, phaseMatrix, upper, lower,
    ← sidePcpMatrix_append, ← sidePcpMatrix_append]

/-- Code of the rule-`b` role. -/
def ruleB : Block := ⟨false, false, false⟩

/-- Code of the rule-`c` role. -/
def ruleC : Block := ⟨false, true, true⟩

/-- Code of the erase-`b` role. -/
def eraseB : Block := ⟨true, false, false⟩

/-- Code of the erase-`c` role. -/
def eraseC : Block := ⟨true, false, true⟩

@[simp] theorem upper_ruleB (β : Nat) : upper β ruleB = nearyUpper β (.rule .b) := by
  rfl

@[simp] theorem upper_ruleC (β : Nat) : upper β ruleC = nearyUpper β (.rule .c) := by
  rfl

@[simp] theorem upper_eraseB (β : Nat) : upper β eraseB = nearyUpper β (.erase .b) := by
  rfl

@[simp] theorem upper_eraseC (β : Nat) : upper β eraseC = nearyUpper β (.erase .c) := by
  rfl

@[simp] theorem lower_ruleB (β : Nat) (body : List TagLetter) :
    lower β body ruleB = nearyLower β body (.rule .b) := by
  rfl

@[simp] theorem lower_ruleC (β : Nat) (body : List TagLetter) (body_nonempty : body ≠ []) :
    lower β body ruleC = nearyLower β body (.rule .c) := by
  obtain ⟨letter, tail, rfl⟩ := List.exists_cons_of_ne_nil body_nonempty
  cases letter <;>
    simp [lower, phaseLower, ruleC, ruleCMiddle, nearyLower, tagEncode_cons, tagCode,
      List.append_assoc]

@[simp] theorem lower_eraseB (β : Nat) (body : List TagLetter) :
    lower β body eraseB = nearyLower β body (.erase .b) := by
  rfl

@[simp] theorem lower_eraseC (β : Nat) (body : List TagLetter) :
    lower β body eraseC = nearyLower β body (.erase .c) := by
  rfl

/-- The `000` block is exactly the rule-`b` matrix. -/
theorem blockMatrix_ruleB (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter) :
    blockMatrix R β body ruleB =
      sidePcpMatrix R (nearyUpper β (.rule .b)) (nearyLower β body (.rule .b)) := by
  rw [blockMatrix_eq_sidePcpMatrix, upper_ruleB, lower_ruleB]

/-- The `011` block is exactly the rule-`c` matrix for every nonempty body. -/
theorem blockMatrix_ruleC (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter)
    (body_nonempty : body ≠ []) :
    blockMatrix R β body ruleC =
      sidePcpMatrix R (nearyUpper β (.rule .c)) (nearyLower β body (.rule .c)) := by
  rw [blockMatrix_eq_sidePcpMatrix, upper_ruleC, lower_ruleC β body body_nonempty]

/-- The `100` block is exactly the erase-`b` matrix. -/
theorem blockMatrix_eraseB (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter) :
    blockMatrix R β body eraseB =
      sidePcpMatrix R (nearyUpper β (.erase .b)) (nearyLower β body (.erase .b)) := by
  rw [blockMatrix_eq_sidePcpMatrix, upper_eraseB, lower_eraseB]

/-- The `101` block is exactly the erase-`c` matrix. -/
theorem blockMatrix_eraseC (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter) :
    blockMatrix R β body eraseC =
      sidePcpMatrix R (nearyUpper β (.erase .c)) (nearyLower β body (.erase .c)) := by
  rw [blockMatrix_eq_sidePcpMatrix, upper_eraseC, lower_eraseC]

/-- Six malformed cube vertices forming a terminal match on the nonhalting poison source. -/
def poisonWord : List Block :=
  [⟨false, false, true⟩,
   ⟨true, false, false⟩,
   ⟨true, false, false⟩,
   ⟨false, true, false⟩,
   ⟨true, false, true⟩,
   ⟨true, false, true⟩]

/-- The expanded three-phase alphabet accepts a six-block false terminal witness. -/
theorem poisonWord_terminal_match :
    spell (upper 3) poisonWord ++ nearyMarker 3 =
      spell (lower 3 ParabolicRetuned.poisonBody) poisonWord := by
  decide

/-- Exact factorization of the four lawful roles does not preserve terminal solvability: the
expanded cube accepts the poison instance although the original Neary source does not. -/
theorem poison_false_positive :
    (∃ word : List Block,
      spell (upper 3) word ++ nearyMarker 3 =
        spell (lower 3 ParabolicRetuned.poisonBody) word) ∧
      ¬∃ word : List NearyTile,
        spell (nearyUpper 3) word ++ nearyMarker 3 =
          spell (nearyLower 3 ParabolicRetuned.poisonBody) word := by
  constructor
  · exact ⟨poisonWord, poisonWord_terminal_match⟩
  · exact ParabolicRetuned.poison_no_terminal_match

end ThreePhaseBinaryNoGo

end MatrixMortality
