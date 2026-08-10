import MatrixMortality.ParabolicRetunedBoundary
import MatrixMortality.Undecidability.TagExecution

/-!
# Malformed terminal obstruction for the retuned blade

One gap-thirty `b` atom acts as an extra tag production.  For the admissible nonhalting source
`(β, body) = (3, bbcc)`, an explicit word using that atom has terminal sparse semantics and the
same fixed terminal row as a lawful context.  Every annihilator of that row therefore creates a
malformed zero.
-/

namespace MatrixMortality

open scoped Matrix

namespace ParabolicRetuned

private abbrev PseudoTile := NearyTile ⊕ Unit

private def ordinary (tile : NearyTile) : PseudoTile := Sum.inl tile

private def poisonB : PseudoTile := Sum.inr ()

private def pseudoLetter : PseudoTile → TagLetter
  | .inl tile => tile.letter
  | .inr _ => .b

private def pseudoGap : PseudoTile → Nat
  | .inl tile => tileGap tile
  | .inr _ => 30

private def pseudoUpper : PseudoTile → List Bool
  | .inl tile => nearyUpper 3 tile
  | .inr _ => tagCode 3 .b

private def pseudoLower (body : List TagLetter) : PseudoTile → List Bool
  | .inl tile => nearyLower 3 body tile
  | .inr _ => [true, true, true, true, false]

private def pseudoReduced (body : List TagLetter) (tile : PseudoTile) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  atom 3 body (pseudoLetter tile) (pseudoGap tile)

private def pseudoPhysical (body : List TagLetter) (tile : PseudoTile) :
    Matrix (Fin 4) (Fin 4) ℚ :=
  dataGenerator 3 body (pseudoLetter tile) * root ^ pseudoGap tile

private def pseudoWord (tile : PseudoTile) : List (Option TagLetter) :=
  some (pseudoLetter tile) :: List.replicate (pseudoGap tile) none

private theorem poisonAtom_eq_semanticMatrix (body : List TagLetter) :
    pseudoReduced body poisonB =
      semanticMatrix (pseudoUpper poisonB) (pseudoLower body poisonB) := by
  rw [pseudoReduced, poisonB, pseudoLetter, pseudoGap, atom, dataFlank, bFlank,
    show 30 = 3 * 10 by norm_num, root_pow_three_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [semanticMatrix, poisonB, pseudoUpper, pseudoLower, tagCode, sparseCode,
      sparseDigit, Nat.ofDigits, ParabolicBlade.flank, ParabolicBlade.drift,
      ParabolicBlade.injection, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem pseudoTile_reduced_eq_semanticMatrix
    (body : List TagLetter) (tile : PseudoTile) :
    pseudoReduced body tile = semanticMatrix (pseudoUpper tile) (pseudoLower body tile) := by
  cases tile with
  | inl tile =>
      simpa [pseudoReduced, pseudoLetter, pseudoGap, pseudoUpper, pseudoLower, tileAtom] using
        tileAtom_eq_semanticMatrix 3 body tile
  | inr payload =>
      cases payload
      exact poisonAtom_eq_semanticMatrix body

private def pseudoReducedProduct (body : List TagLetter) (word : List PseudoTile) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  wordProduct (pseudoReduced body) word

private theorem pseudoReducedProduct_eq_semanticMatrix
    (body : List TagLetter) (word : List PseudoTile) :
    pseudoReducedProduct body word =
      semanticMatrix (spell pseudoUpper word) (spell (pseudoLower body) word) := by
  induction word with
  | nil => simp [pseudoReducedProduct, wordProduct, spell]
  | cons tile word induction =>
      rw [pseudoReducedProduct, wordProduct_cons, pseudoTile_reduced_eq_semanticMatrix]
      change semanticMatrix _ _ * wordProduct (pseudoReduced body) word = _
      rw [← pseudoReducedProduct, induction, ← semanticMatrix_append]
      rfl

/-- The admissible body on which the legal restricted tag system cycles forever. -/
def poisonBody : List TagLetter := [.b, .b, .c, .c]

private def poisonTiles : List PseudoTile :=
  [ordinary (.rule .c), ordinary (.erase .b), ordinary (.erase .b),
   ordinary (.rule .c), ordinary (.erase .c), ordinary (.erase .b),
   poisonB, ordinary (.erase .b), ordinary (.erase .c),
   ordinary (.rule .c), ordinary (.erase .b), ordinary (.erase .c),
   ordinary (.rule .c), ordinary (.erase .b), ordinary (.erase .b),
   ordinary (.rule .b), ordinary (.erase .c), ordinary (.erase .c),
   ordinary (.rule .b), ordinary (.erase .b), ordinary (.erase .b),
   ordinary (.rule .c), ordinary (.erase .c), ordinary (.erase .b),
   ordinary (.rule .b), ordinary (.erase .b), ordinary (.erase .b),
   ordinary (.rule .b), ordinary (.erase .c), ordinary (.erase .c),
   ordinary (.rule .b), ordinary (.erase .b), ordinary (.erase .b)]

private theorem poisonTiles_terminal :
    spell pseudoUpper poisonTiles ++ nearyMarker 3 =
      spell (pseudoLower poisonBody) poisonTiles := by
  decide

private def pseudoPhysicalProduct (body : List TagLetter) (word : List PseudoTile) :
    Matrix (Fin 4) (Fin 4) ℚ :=
  wordProduct (pseudoPhysical body) word

private theorem pseudoPhysicalProduct_mul_injection
    (body : List TagLetter) (word : List PseudoTile) :
    pseudoPhysicalProduct body word * ParabolicBlade.injection =
      ParabolicBlade.injection * pseudoReducedProduct body word := by
  induction word with
  | nil => simp [pseudoPhysicalProduct, pseudoReducedProduct, wordProduct]
  | cons tile word induction =>
      simp only [pseudoPhysicalProduct, pseudoReducedProduct, wordProduct_cons]
      change wordProduct (pseudoPhysical body) word * ParabolicBlade.injection =
        ParabolicBlade.injection * wordProduct (pseudoReduced body) word at induction
      rw [Matrix.mul_assoc, induction]
      simp only [pseudoPhysical, pseudoReduced, dataGenerator, atom, Matrix.mul_assoc]

private def pseudoMiddleWord (word : List PseudoTile) : List (Option TagLetter) :=
  word.bind pseudoWord

private theorem pseudoTile_word_product (body : List TagLetter) (tile : PseudoTile) :
    wordProduct (generator 3 body) (pseudoWord tile) = pseudoPhysical body tile := by
  simp [generator, pseudoWord, pseudoPhysical, wordProduct, separatedGenerator]

private theorem pseudoMiddleWord_product (body : List TagLetter) (word : List PseudoTile) :
    wordProduct (generator 3 body) (pseudoMiddleWord word) =
      pseudoPhysicalProduct body word := by
  induction word with
  | nil => simp [pseudoMiddleWord, pseudoPhysicalProduct, wordProduct]
  | cons tile word induction =>
      change wordProduct (generator 3 body) (word.bind pseudoWord) =
        pseudoPhysicalProduct body word at induction
      rw [pseudoMiddleWord, List.bind_cons, wordProduct_append, pseudoTile_word_product,
        pseudoPhysicalProduct, wordProduct_cons, induction]
      rfl

private def poisonContext : Matrix (Fin 4) (Fin 4) ℚ :=
  dataGenerator 3 poisonBody .b * root ^ 2 * pseudoPhysicalProduct poisonBody poisonTiles *
    dataGenerator 3 poisonBody .b * root ^ 2 * dataGenerator 3 poisonBody .b

/-- Literal malformed word over the three retuned generators. -/
def poisonContextWord : List (Option TagLetter) :=
  [some .b, none, none] ++ pseudoMiddleWord poisonTiles ++
    [some .b, none, none, some .b]

theorem poisonContextWord_length : poisonContextWord.length = 100 := by
  norm_num [poisonContextWord, pseudoMiddleWord, poisonTiles, pseudoWord, pseudoGap,
    ordinary, poisonB, tileGap]

private theorem poisonContextWord_product :
    wordProduct (generator 3 poisonBody) poisonContextWord = poisonContext := by
  rw [poisonContextWord, wordProduct_append, wordProduct_append,
    pseudoMiddleWord_product]
  simp [generator, poisonContext, separatedGenerator, wordProduct, pow_two,
    Matrix.mul_assoc]

private theorem poisonContext_factor :
    poisonContext =
      ParabolicBlade.injection * bladeOutput 3 *
        bridge 3 (pseudoReducedProduct poisonBody poisonTiles) * bladeInput * bFlank 3 := by
  have middle := pseudoPhysicalProduct_mul_injection poisonBody poisonTiles
  have blade :
      bFlank 3 * root ^ 2 * ParabolicBlade.injection = bladeOutput 3 * bladeInput := by
    simpa [atom, dataFlank] using exceptional_factor 3 poisonBody
  rw [poisonContext]
  simp only [dataGenerator, dataFlank]
  calc
    ParabolicBlade.injection * bFlank 3 * root ^ 2 *
          pseudoPhysicalProduct poisonBody poisonTiles *
          (ParabolicBlade.injection * bFlank 3) * root ^ 2 *
          (ParabolicBlade.injection * bFlank 3) =
        (ParabolicBlade.injection * bFlank 3 * root ^ 2) *
          (pseudoPhysicalProduct poisonBody poisonTiles * ParabolicBlade.injection) *
          (bFlank 3 * root ^ 2 * ParabolicBlade.injection) * bFlank 3 := by
      simp only [Matrix.mul_assoc]
    _ = (ParabolicBlade.injection * bFlank 3 * root ^ 2) *
          (ParabolicBlade.injection * pseudoReducedProduct poisonBody poisonTiles) *
          (bFlank 3 * root ^ 2 * ParabolicBlade.injection) * bFlank 3 := by
      rw [middle]
    _ = ParabolicBlade.injection * (bFlank 3 * root ^ 2 * ParabolicBlade.injection) *
          pseudoReducedProduct poisonBody poisonTiles *
          (bFlank 3 * root ^ 2 * ParabolicBlade.injection) * bFlank 3 := by
      simp only [Matrix.mul_assoc]
    _ = ParabolicBlade.injection * bladeOutput 3 *
          bridge 3 (pseudoReducedProduct poisonBody poisonTiles) * bladeInput * bFlank 3 := by
      rw [blade]
      simp only [bridge, Matrix.mul_assoc]

private theorem poisonContext_outer :
    ∃ column : Fin 4 → ℚ, column ≠ 0 ∧
      poisonContext = Matrix.vecMulVec column (terminalRow 3) := by
  let upper := spell pseudoUpper poisonTiles
  let middle := semanticMatrix upper (upper ++ nearyMarker 3)
  let core := ParabolicBlade.injection * bladeOutput 3 * bridge 3 middle
  let column : Fin 4 → ℚ := fun i => core i 1 / 2
  have bridge_columns (i : Fin 2) :
      bridge 3 middle i 0 = -(1 / 2 : ℚ) * bridge 3 middle i 1 := by
    exact bridge_semanticMatrix_terminal_columns 3 upper i
  have core_columns (i : Fin 4) : core i 0 = -(1 / 2 : ℚ) * core i 1 := by
    simp only [core, Matrix.mul_apply, Fin.sum_univ_two]
    rw [bridge_columns 0, bridge_columns 1]
    ring
  have outer : poisonContext = Matrix.vecMulVec column (terminalRow 3) := by
    rw [poisonContext_factor, pseudoReducedProduct_eq_semanticMatrix, ← poisonTiles_terminal]
    change core * bladeInput * bFlank 3 = Matrix.vecMulVec column (terminalRow 3)
    ext i j
    fin_cases j <;>
      norm_num [column, terminalRow, bladeInput, bFlank, ParabolicBlade.flank,
        Matrix.mul_apply, Matrix.vecMulVec, Fin.sum_univ_succ]
    all_goals try rw [core_columns i]
    all_goals ring
  refine ⟨column, ?_, outer⟩
  intro column_zero
  have entry_zero := congr_fun column_zero 1
  norm_num [column, core, middle, upper, bridge, semanticMatrix, bladeOutput, bladeInput,
    ParabolicBlade.injection, Matrix.mul_apply, Fin.sum_univ_succ] at entry_zero
  linarith

/-- The malformed context is a nonzero outer product with the lawful fixed terminal row. -/
theorem poisonContextWord_product_outer :
    ∃ column : Fin 4 → ℚ, column ≠ 0 ∧
      wordProduct (generator 3 poisonBody) poisonContextWord =
        Matrix.vecMulVec column (terminalRow 3) := by
  simpa [poisonContextWord_product] using poisonContext_outer

/-- Appending any physical word kills the malformed context exactly when it annihilates the
lawful terminal row. -/
theorem poisonContext_append_zero_iff (continuation : List (Option TagLetter)) :
    wordProduct (generator 3 poisonBody) (poisonContextWord ++ continuation) = 0 ↔
      terminalRow 3 ᵥ* wordProduct (generator 3 poisonBody) continuation = 0 := by
  obtain ⟨column, column_ne, outer⟩ := poisonContextWord_product_outer
  rw [wordProduct_append, outer, outer_mul]
  constructor
  · intro product_zero
    by_contra row_ne
    exact outer_ne_zero column_ne row_ne product_zero
  · intro row_zero
    rw [row_zero]
    ext i j
    simp [Matrix.vecMulVec]

private theorem poisonStep_initial :
    TagStep 3 (tagOutput poisonBody) [.c, .c, .b] [.b, .b, .c, .c, .b] := by
  refine ⟨{ head := .c, wake := [.c, .b], width := by decide }, [], rfl, ?_⟩
  decide

private theorem poisonStep_long :
    TagStep 3 (tagOutput poisonBody) [.b, .b, .c, .c, .b] [.c, .b, .b] := by
  refine ⟨{ head := .b, wake := [.b, .c], width := by decide }, [.c, .b], rfl, ?_⟩
  decide

private theorem poisonStep_short :
    TagStep 3 (tagOutput poisonBody) [.c, .b, .b] [.b, .b, .c, .c, .b] := by
  refine ⟨{ head := .c, wake := [.b, .b], width := by decide }, [], rfl, ?_⟩
  decide

private def PoisonOrbit (queue : List TagLetter) : Prop :=
  queue = [.c, .c, .b] ∨ queue = [.b, .b, .c, .c, .b] ∨ queue = [.c, .b, .b]

private theorem poisonOrbit_progress {queue : List TagLetter} (holds : PoisonOrbit queue) :
    ∃ next, PoisonOrbit next ∧
      Relation.TransGen (TagStep 3 (tagOutput poisonBody)) queue next := by
  rcases holds with rfl | rfl | rfl
  · exact ⟨[.b, .b, .c, .c, .b], Or.inr (Or.inl rfl), .single poisonStep_initial⟩
  · exact ⟨[.c, .b, .b], Or.inr (Or.inr rfl), .single poisonStep_long⟩
  · exact ⟨[.b, .b, .c, .c, .b], Or.inr (Or.inl rfl), .single poisonStep_short⟩

/-- The admissible legal source `(3,bbcc)` never halts. -/
theorem poison_not_tagHaltsFrom :
    ¬TagHaltsFrom 3 (tagOutput poisonBody) [.c, .c, .b] := by
  apply Undecidability.not_tagHaltsFrom_of_transGen_progress PoisonOrbit
    (fun holds => poisonOrbit_progress holds)
  exact Or.inl rfl

/-- The admissible legal source `(3,bbcc)` has no genuine Neary terminal word. -/
theorem poison_no_terminal_match :
    ¬∃ word : List NearyTile,
      spell (nearyUpper 3) word ++ nearyMarker 3 = spell (nearyLower 3 poisonBody) word := by
  intro terminal
  have halts :=
    (terminal_match_iff_tagHaltsFrom 3 poisonBody (by norm_num)
      (by norm_num [poisonBody]) (by norm_num [poisonBody])).mp terminal
  exact poison_not_tagHaltsFrom halts

/-- The fixed-terminal-row closure fails on one admissible no-instance: every lawful row
annihilator also completes the explicit malformed context to a zero word. -/
theorem poison_fixedTerminalRow_obstruction :
    (¬∃ word : List NearyTile,
      spell (nearyUpper 3) word ++ nearyMarker 3 =
        spell (nearyLower 3 poisonBody) word) ∧
      ∀ continuation : List (Option TagLetter),
        terminalRow 3 ᵥ* wordProduct (generator 3 poisonBody) continuation = 0 →
          wordProduct (generator 3 poisonBody) (poisonContextWord ++ continuation) = 0 := by
  refine ⟨poison_no_terminal_match, ?_⟩
  intro continuation annihilates
  exact (poisonContext_append_zero_iff continuation).mpr annihilates

end ParabolicRetuned

end MatrixMortality
