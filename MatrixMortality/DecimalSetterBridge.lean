import MatrixMortality.DecimalSetterFracture
import MatrixMortality.DecimalSetterInteger
import Mathlib.Tactic

/-!
# Triple-free bridge parser for the decimal setter

After fracture at delimiter cubes, every interior bridge contains no `S³`.  This module parses
such a bridge into blocks separated by `S²`: every block except the rightmost ends in an erasure,
while the rightmost block ends in a rule because the delimiter cube supplies the ordinary root
column.  Boundary delimiter runs are removed without changing the bridge coefficient.
-/

namespace MatrixMortality.DecimalSetterBridge

open scoped Matrix

open MatrixMortality.DecimalSetterFracture
open MatrixMortality.DecimalSetterMatrix

/-- A physical word contains no delimiter cube. -/
def IsCubeFree (word : List (Option TagLetter)) : Prop :=
  ¬∃ left right, word = left ++ none :: none :: none :: right

/-- Every letter of the word is a delimiter. -/
def AllDelimiters (word : List (Option TagLetter)) : Prop :=
  ∀ label ∈ word, label = none

/-- The first physical symbol is a data letter. -/
def StartsWithData (word : List (Option TagLetter)) : Prop :=
  ∃ letter tail, word = some letter :: tail

/-- The last physical symbol is a data letter. -/
def EndsWithData (word : List (Option TagLetter)) : Prop :=
  ∃ letter, word.getLast? = some (some letter)

/-- `core` is obtained by deleting only delimiter runs at the two boundaries of `word`. -/
def IsBoundaryCore (word core : List (Option TagLetter)) : Prop :=
  ∃ left right,
    word = List.replicate left none ++ core ++ List.replicate right none ∧
      StartsWithData core ∧ EndsWithData core

theorem IsCubeFree.suffix {front suffix : List (Option TagLetter)}
    (cube_free : IsCubeFree (front ++ suffix)) : IsCubeFree suffix := by
  rintro ⟨left, right, suffix_eq⟩
  apply cube_free
  refine ⟨front ++ left, right, ?_⟩
  rw [suffix_eq]
  simp [List.append_assoc]

theorem EndsWithData.suffix {front suffix : List (Option TagLetter)}
    (ends_in_data : EndsWithData (front ++ suffix)) (suffix_ne : suffix ≠ []) :
    EndsWithData suffix := by
  obtain ⟨letter, last_eq⟩ := ends_in_data
  refine ⟨letter, ?_⟩
  rw [List.getLast?_append_of_ne_nil front suffix_ne] at last_eq
  exact last_eq

/-- Every physical word is all delimiter or has a data-anchored boundary core. -/
theorem allDelimiters_or_exists_boundaryCore (word : List (Option TagLetter)) :
    AllDelimiters word ∨ ∃ core, IsBoundaryCore word core := by
  induction word using List.reverseRecOn with
  | nil =>
      exact Or.inl (by simp [AllDelimiters])
  | append_singleton word label induction =>
      cases label with
      | none =>
          rcases induction with all_delimiters | ⟨core, left, right, word_eq,
              core_starts, core_ends⟩
          · left
            intro label label_mem
            rw [List.mem_append, List.mem_singleton] at label_mem
            rcases label_mem with label_mem | rfl
            · exact all_delimiters label label_mem
            · rfl
          · right
            refine ⟨core, left, right + 1, ?_, core_starts, core_ends⟩
            rw [word_eq, List.replicate_succ', List.append_assoc]
      | some letter =>
          rcases induction with all_delimiters | ⟨core, left, right, word_eq,
              core_starts, core_ends⟩
          · have word_eq_replicate : word = List.replicate word.length none :=
              List.eq_replicate_length.mpr all_delimiters
            right
            refine ⟨[some letter], word.length, 0, ?_, ?_, ?_⟩
            · rw [word_eq_replicate]
              simp
            · exact ⟨letter, [], rfl⟩
            · exact ⟨letter, by simp⟩
          · let extended := core ++ List.replicate right none ++ [some letter]
            right
            refine ⟨extended, left, 0, ?_, ?_, ?_⟩
            · simp [extended, word_eq, List.append_assoc]
            · obtain ⟨first, tail, core_eq⟩ := core_starts
              exact ⟨first, tail ++ List.replicate right none ++ [some letter], by
                simp [extended, core_eq, List.append_assoc]⟩
            · exact ⟨letter, by simp [extended]⟩

theorem IsBoundaryCore.core_cubeFree {word core : List (Option TagLetter)}
    (boundary : IsBoundaryCore word core) (cube_free : IsCubeFree word) :
    IsCubeFree core := by
  obtain ⟨leftCount, rightCount, word_eq, _, _⟩ := boundary
  rintro ⟨left, right, core_eq⟩
  apply cube_free
  refine ⟨List.replicate leftCount none ++ left,
    right ++ List.replicate rightCount none, ?_⟩
  rw [word_eq, core_eq]
  simp [List.append_assoc]

/-! ## Boundary delimiter invariance -/

theorem terminalRow_vecMul_delimiter (β : Nat) :
    terminalRow ᵥ* delimiter β = terminalRow := by
  ext coordinate
  fin_cases coordinate <;>
    simp [terminalRow, delimiter, MatrixMortality.SetterShear.delimiter,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

theorem delimiter_mulVec_firstAxis (β : Nat) :
    delimiter β *ᵥ firstAxis = firstAxis := by
  ext coordinate
  fin_cases coordinate <;>
    simp [firstAxis, delimiter, MatrixMortality.SetterShear.delimiter,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem terminalRow_vecMul_delimiter_pow (β power : Nat) :
    terminalRow ᵥ* delimiter β ^ power = terminalRow := by
  induction power with
  | zero => simp
  | succ power induction =>
      rw [pow_succ, ← Matrix.vecMul_vecMul, induction, terminalRow_vecMul_delimiter]

theorem delimiter_pow_mulVec_firstAxis (β power : Nat) :
    delimiter β ^ power *ᵥ firstAxis = firstAxis := by
  induction power with
  | zero => simp
  | succ power induction =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, delimiter_mulVec_firstAxis, induction]

theorem wordProduct_replicate_delimiter (β : Nat) (body : List TagLetter)
    (power : Nat) :
    wordProduct (generator β body) (List.replicate power none) = delimiter β ^ power := by
  simp [wordProduct, generator, List.map_replicate]

/-- Removing boundary delimiter runs does not change a bridge scalar. -/
theorem IsBoundaryCore.bridgeScalar_eq {β : Nat} {body : List TagLetter}
    {word core : List (Option TagLetter)} (boundary : IsBoundaryCore word core) :
    DecimalSetterFracture.bridgeScalar β body word =
      DecimalSetterFracture.bridgeScalar β body core := by
  obtain ⟨left, right, word_eq, _, _⟩ := boundary
  rw [DecimalSetterFracture.bridgeScalar, word_eq, wordProduct_append, wordProduct_append,
    wordProduct_replicate_delimiter, wordProduct_replicate_delimiter]
  change terminalRow ⬝ᵥ
      ((delimiter β ^ left * wordProduct (generator β body) core) *
          delimiter β ^ right) *ᵥ firstAxis = _
  calc
    terminalRow ⬝ᵥ
          ((delimiter β ^ left * wordProduct (generator β body) core) *
            delimiter β ^ right) *ᵥ firstAxis =
        MatrixMortality.bridgeScalar
          (delimiter β ^ right *ᵥ firstAxis)
          (terminalRow ᵥ* delimiter β ^ left)
          (wordProduct (generator β body) core) := by
      exact (bridgeScalar_fold_boundaries terminalRow firstAxis
        (delimiter β ^ left) (wordProduct (generator β body) core)
        (delimiter β ^ right)).symm
    _ = MatrixMortality.bridgeScalar firstAxis terminalRow
          (wordProduct (generator β body) core) := by
      rw [delimiter_pow_mulVec_firstAxis, terminalRow_vecMul_delimiter_pow]
    _ = DecimalSetterFracture.bridgeScalar β body core := rfl

/-- A word consisting only of delimiters has bridge scalar one. -/
theorem bridgeScalar_eq_one_of_allDelimiters {β : Nat} {body : List TagLetter}
    {word : List (Option TagLetter)} (all_delimiters : AllDelimiters word) :
    DecimalSetterFracture.bridgeScalar β body word = 1 := by
  have word_eq : word = List.replicate word.length none :=
    List.eq_replicate_length.mpr all_delimiters
  rw [DecimalSetterFracture.bridgeScalar, word_eq, wordProduct_replicate_delimiter,
    delimiter_pow_mulVec_firstAxis]
  norm_num [terminalRow, firstAxis, dotProduct, Fin.sum_univ_succ]

/-! ## Anchored block grammar -/

/-- Exact block parsing of a data-anchored cube-free word. Blocks are listed left to right. -/
inductive CoreSpelling :
    List (Option TagLetter) → List (List NearyTile) → Prop
  | terminal (letter : TagLetter) :
      CoreSpelling [some letter] [[.rule letter]]
  | rule {physical : List (Option TagLetter)} {roles : List NearyTile}
      {blocks : List (List NearyTile)} (letter : TagLetter)
      (tail : CoreSpelling physical (roles :: blocks)) :
      CoreSpelling (some letter :: physical) ((.rule letter :: roles) :: blocks)
  | erase {physical : List (Option TagLetter)} {roles : List NearyTile}
      {blocks : List (List NearyTile)} (letter : TagLetter)
      (tail : CoreSpelling physical (roles :: blocks)) :
      CoreSpelling (some letter :: none :: physical) ((.erase letter :: roles) :: blocks)
  | square {physical : List (Option TagLetter)} {roles : List NearyTile}
      {blocks : List (List NearyTile)} (letter : TagLetter)
      (tail : CoreSpelling physical (roles :: blocks)) :
      CoreSpelling (some letter :: none :: none :: physical)
        ([.erase letter] :: roles :: blocks)

theorem CoreSpelling.blocks_ne_nil {physical : List (Option TagLetter)}
    {blocks : List (List NearyTile)} (spelling : CoreSpelling physical blocks) :
    blocks ≠ [] := by
  cases spelling <;> simp

private theorem exists_coreSpelling_go :
    ∀ word : List (Option TagLetter),
      IsCubeFree word → StartsWithData word → EndsWithData word →
        ∃ blocks, CoreSpelling word blocks := by
  intro word cube_free starts_in_data ends_in_data
  obtain ⟨letter, tail, rfl⟩ := starts_in_data
  cases tail with
  | nil =>
      exact ⟨[[.rule letter]], .terminal letter⟩
  | cons second rest =>
      cases second with
      | some next =>
          have suffix_cube_free : IsCubeFree (some next :: rest) :=
            cube_free.suffix (front := [some letter])
          have suffix_ends : EndsWithData (some next :: rest) :=
            ends_in_data.suffix (front := [some letter]) (by simp)
          obtain ⟨blocks, spelling⟩ := exists_coreSpelling_go
            (some next :: rest) suffix_cube_free ⟨next, rest, rfl⟩ suffix_ends
          obtain ⟨roles, blocks, blocks_eq⟩ :=
            List.exists_cons_of_ne_nil spelling.blocks_ne_nil
          subst blocks_eq
          exact ⟨(.rule letter :: roles) :: blocks, .rule letter spelling⟩
      | none =>
          cases rest with
          | nil =>
              obtain ⟨last, last_eq⟩ := ends_in_data
              simp at last_eq
          | cons third rest =>
              cases third with
              | some next =>
                  have suffix_cube_free : IsCubeFree (some next :: rest) :=
                    cube_free.suffix (front := [some letter, none])
                  have suffix_ends : EndsWithData (some next :: rest) :=
                    ends_in_data.suffix (front := [some letter, none]) (by simp)
                  obtain ⟨blocks, spelling⟩ := exists_coreSpelling_go
                    (some next :: rest) suffix_cube_free ⟨next, rest, rfl⟩ suffix_ends
                  obtain ⟨roles, blocks, blocks_eq⟩ :=
                    List.exists_cons_of_ne_nil spelling.blocks_ne_nil
                  subst blocks_eq
                  exact ⟨(.erase letter :: roles) :: blocks, .erase letter spelling⟩
              | none =>
                  cases rest with
                  | nil =>
                      obtain ⟨last, last_eq⟩ := ends_in_data
                      simp at last_eq
                  | cons fourth rest =>
                      cases fourth with
                      | none =>
                          exact False.elim (cube_free ⟨[some letter], rest, by simp⟩)
                      | some next =>
                          have suffix_cube_free : IsCubeFree (some next :: rest) :=
                            cube_free.suffix (front := [some letter, none, none])
                          have suffix_ends : EndsWithData (some next :: rest) :=
                            ends_in_data.suffix
                              (front := [some letter, none, none]) (by simp)
                          obtain ⟨blocks, spelling⟩ := exists_coreSpelling_go
                            (some next :: rest) suffix_cube_free
                            ⟨next, rest, rfl⟩ suffix_ends
                          obtain ⟨roles, blocks, blocks_eq⟩ :=
                            List.exists_cons_of_ne_nil spelling.blocks_ne_nil
                          subst blocks_eq
                          exact ⟨[.erase letter] :: roles :: blocks,
                            .square letter spelling⟩
termination_by word => word.length

/-- Every data-anchored cube-free word has an exact square-separated role-block spelling. -/
theorem exists_coreSpelling {word : List (Option TagLetter)}
    (cube_free : IsCubeFree word) (starts_in_data : StartsWithData word)
    (ends_in_data : EndsWithData word) :
    ∃ blocks, CoreSpelling word blocks :=
  exists_coreSpelling_go word cube_free starts_in_data ends_in_data

/-- Every cube-free zero bridge contracts to a data-anchored parsed zero core. -/
theorem exists_boundaryCoreSpelling_of_cubeFree_zero
    {β : Nat} {body : List TagLetter} {word : List (Option TagLetter)}
    (cube_free : IsCubeFree word)
    (bridge_zero : DecimalSetterFracture.bridgeScalar β body word = 0) :
    ∃ core blocks,
      IsBoundaryCore word core ∧ CoreSpelling core blocks ∧
        DecimalSetterFracture.bridgeScalar β body core = 0 := by
  rcases allDelimiters_or_exists_boundaryCore word with all_delimiters |
      ⟨core, boundary⟩
  · have bridge_one := bridgeScalar_eq_one_of_allDelimiters
      (β := β) (body := body) all_delimiters
    rw [bridge_zero] at bridge_one
    norm_num at bridge_one
  · obtain ⟨blocks, spelling⟩ := exists_coreSpelling
      (boundary.core_cubeFree cube_free)
      (by obtain ⟨_, _, _, starts, _⟩ := boundary; exact starts)
      (by obtain ⟨_, _, _, _, ends⟩ := boundary; exact ends)
    exact ⟨core, blocks, boundary, spelling,
      boundary.bridgeScalar_eq.symm.trans bridge_zero⟩

/-- A role block ends in an erasure. -/
def EndsInErase (roles : List NearyTile) : Prop :=
  ∃ front letter, roles = front ++ [.erase letter]

/-- A role block ends in a rule. -/
def EndsInRule (roles : List NearyTile) : Prop :=
  ∃ front letter, roles = front ++ [.rule letter]

/-- Every block except the rightmost ends in erasure; the rightmost ends in rule. -/
def BlocksLaw : List (List NearyTile) → Prop
  | [] => False
  | [last] => EndsInRule last
  | block :: next :: rest => EndsInErase block ∧ BlocksLaw (next :: rest)

private theorem EndsInErase.cons (role : NearyTile) {roles : List NearyTile}
    (ends_in_erase : EndsInErase roles) : EndsInErase (role :: roles) := by
  obtain ⟨front, letter, roles_eq⟩ := ends_in_erase
  exact ⟨role :: front, letter, by rw [roles_eq]; rfl⟩

private theorem EndsInRule.cons (role : NearyTile) {roles : List NearyTile}
    (ends_in_rule : EndsInRule roles) : EndsInRule (role :: roles) := by
  obtain ⟨front, letter, roles_eq⟩ := ends_in_rule
  exact ⟨role :: front, letter, by rw [roles_eq]; rfl⟩

private theorem BlocksLaw.cons_head (role : NearyTile)
    {roles : List NearyTile} {blocks : List (List NearyTile)}
    (law : BlocksLaw (roles :: blocks)) : BlocksLaw ((role :: roles) :: blocks) := by
  cases blocks with
  | nil => exact EndsInRule.cons role law
  | cons next rest => exact ⟨EndsInErase.cons role law.1, law.2⟩

/-- The parser's block list obeys the exact erasure/rule boundary law. -/
theorem CoreSpelling.blocksLaw {physical : List (Option TagLetter)}
    {blocks : List (List NearyTile)} (spelling : CoreSpelling physical blocks) :
    BlocksLaw blocks := by
  induction spelling with
  | terminal letter => exact ⟨[], letter, rfl⟩
  | rule letter tail induction | erase letter tail induction =>
      exact BlocksLaw.cons_head _ induction
  | square letter tail induction =>
      exact ⟨⟨[], letter, rfl⟩, induction⟩

/-! ## Exact bridge recurrence -/

/-- A regular erasure-ending spelling acts correctly on every marked side column. -/
theorem regularSpelling_mulVec_markedColumn {β : Nat} (β_pos : 0 < β)
    (body : List TagLetter) {physical : List (Option TagLetter)}
    {roles : List NearyTile} (spelling : RegularSpelling physical roles)
    (column : Fin 3 → ℚ) :
    wordProduct (generator β body) physical *ᵥ markedColumn column =
      rootColumn (roleProduct β body roles *ᵥ column) := by
  induction spelling with
  | terminal letter =>
      rw [show wordProduct (generator β body) [some letter] =
          data β body letter by simp [generator]]
      simpa [roleProduct] using data_mul_markedColumn β_pos body letter column
  | rule letter tail induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec, induction]
      change data β body letter *ᵥ
          rootColumn (roleProduct β body _ *ᵥ column) = _
      rw [data_mul_rootColumn]
      simp [roleProduct, ← Matrix.mulVec_mulVec]
  | erase letter tail induction =>
      rw [wordProduct_cons, wordProduct_cons, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, induction]
      change data β body letter *ᵥ delimiter β *ᵥ
          rootColumn (roleProduct β body _ *ᵥ column) = _
      rw [delimiter_mul_rootColumn, data_mul_markedColumn β_pos]
      simp [roleProduct, ← Matrix.mulVec_mulVec]

/-- Side state produced by a delimiter square from a cleared root column. -/
def squareReset (β : Nat) (column : Fin 3 → ℚ) : Fin 3 → ℚ :=
  ![column 0, separatorScale β * column 2, 0]

theorem delimiter_square_mul_rootColumn (β : Nat) (column : Fin 3 → ℚ) :
    delimiter β ^ 2 *ᵥ rootColumn column = markedColumn (squareReset β column) := by
  ext coordinate
  fin_cases coordinate <;>
    simp [delimiter, MatrixMortality.SetterShear.delimiter, rootColumn, markedColumn,
      squareReset, pow_succ, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem delimiter_twice_mul_rootColumn (β : Nat) (column : Fin 3 → ℚ) :
    delimiter β *ᵥ delimiter β *ᵥ rootColumn column =
      markedColumn (squareReset β column) := by
  rw [Matrix.mulVec_mulVec, ← pow_two, delimiter_square_mul_rootColumn]

/-- Three-coordinate state obtained by evaluating parsed blocks from right to left. -/
def bridgeState (β : Nat) (body : List TagLetter) :
    List (List NearyTile) → (Fin 3 → ℚ)
  | [] => 0
  | [roles] =>
      roleProduct β body roles *ᵥ (![1, 0, 0] : Fin 3 → ℚ)
  | roles :: next :: rest =>
      roleProduct β body roles *ᵥ squareReset β (bridgeState β body (next :: rest))

theorem bridgeState_consRole (β : Nat) (body : List TagLetter)
    (role : NearyTile) (roles : List NearyTile) (blocks : List (List NearyTile)) :
    bridgeState β body ((role :: roles) :: blocks) =
      conjugatedRole β body role *ᵥ bridgeState β body (roles :: blocks) := by
  cases blocks with
  | nil => simp [bridgeState, roleProduct, ← Matrix.mulVec_mulVec]
  | cons next rest => simp [bridgeState, roleProduct, ← Matrix.mulVec_mulVec]

/-- The parsed recurrence is the exact action of the physical core on the delimiter-cube root. -/
theorem CoreSpelling.mulVec_firstAxis {β : Nat} (β_pos : 0 < β)
    (body : List TagLetter) {physical : List (Option TagLetter)}
    {blocks : List (List NearyTile)} (spelling : CoreSpelling physical blocks) :
    wordProduct (generator β body) physical *ᵥ firstAxis =
      rootColumn (bridgeState β body blocks) := by
  induction spelling with
  | terminal letter =>
      rw [show firstAxis = rootColumn (![1, 0, 0] : Fin 3 → ℚ) by
        funext coordinate
        fin_cases coordinate <;> rfl,
        show wordProduct (generator β body) [some letter] =
          data β body letter by simp [generator]]
      rw [data_mul_rootColumn]
      simp [bridgeState, roleProduct]
  | rule letter tail induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec, induction]
      change data β body letter *ᵥ rootColumn (bridgeState β body _) = _
      rw [data_mul_rootColumn, bridgeState_consRole]
  | erase letter tail induction =>
      rw [wordProduct_cons, wordProduct_cons, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, induction]
      change data β body letter *ᵥ delimiter β *ᵥ
          rootColumn (bridgeState β body _) = _
      rw [delimiter_mul_rootColumn, data_mul_markedColumn β_pos,
        bridgeState_consRole]
  | square letter tail induction =>
      rw [wordProduct_cons, wordProduct_cons, wordProduct_cons,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        induction]
      change data β body letter *ᵥ delimiter β *ᵥ delimiter β *ᵥ
          rootColumn (bridgeState β body _) = _
      rw [delimiter_twice_mul_rootColumn, data_mul_markedColumn β_pos]
      simp [bridgeState, roleProduct]

/-- A parsed bridge scalar is the first coordinate of its exact three-state recurrence. -/
theorem CoreSpelling.bridgeScalar_eq {β : Nat} (β_pos : 0 < β)
    (body : List TagLetter) {physical : List (Option TagLetter)}
    {blocks : List (List NearyTile)} (spelling : CoreSpelling physical blocks) :
    DecimalSetterFracture.bridgeScalar β body physical =
      bridgeState β body blocks 0 := by
  rw [DecimalSetterFracture.bridgeScalar, spelling.mulVec_firstAxis β_pos body,
    terminalRow_dot_rootColumn]

/-! ## Zero frontier -/

/-- The unsquared rightmost block cannot itself vanish: its first coordinate is a positive
radix-ten prefix. -/
theorem bridgeState_single_pos {β : Nat} (β_pos : 0 < β)
    (body : List TagLetter) (roles : List NearyTile) :
    0 < bridgeState β body [roles] 0 := by
  have scale_pos : (0 : ℚ) < 10 ^ (β + 1) := pow_pos (by norm_num) _
  have ratio_pos : (0 : ℚ) < 10 ^ (β + 1) / marker β :=
    div_pos scale_pos (marker_pos β)
  have upper_nonneg :
      (0 : ℚ) ≤ DecimalSetterCarry.code (spell (nearyUpper β) roles) := Nat.cast_nonneg _
  rw [bridgeState, roleProduct_eq_conjugatedSide β_pos,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp [sideBasis, sideBasisInv, sideMatrix, ratio, markerScale,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  nlinarith [mul_nonneg upper_nonneg ratio_pos.le]

/-- A delimiter cube factors the surrounding bridge coefficient into its two subbridges. -/
theorem bridgeScalar_append_delimiter_cube (β : Nat) (body : List TagLetter)
    (left right : List (Option TagLetter)) :
    DecimalSetterFracture.bridgeScalar β body
        (left ++ none :: none :: none :: right) =
      DecimalSetterFracture.bridgeScalar β body left *
        DecimalSetterFracture.bridgeScalar β body right := by
  rw [DecimalSetterFracture.bridgeScalar, wordProduct_append]
  have triple_product :
      wordProduct (generator β body) (none :: none :: none :: right) =
        delimiter β ^ 3 * wordProduct (generator β body) right := by
    simp [generator, pow_succ, Matrix.mul_assoc]
  rw [triple_product]
  rw [delimiter_cube, ← Matrix.mul_assoc, mul_outer, outer_mul,
    Matrix.dotProduct_mulVec, vecMul_outer]
  simp [DecimalSetterFracture.bridgeScalar, terminalRow, firstAxis,
    Matrix.vecMul, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem exists_cubeFree_bridgeScalar_zero_go (β : Nat) (body : List TagLetter) :
    ∀ word : List (Option TagLetter),
      DecimalSetterFracture.bridgeScalar β body word = 0 →
        ∃ chunk, chunk <:+: word ∧ IsCubeFree chunk ∧
          DecimalSetterFracture.bridgeScalar β body chunk = 0 := by
  intro word bridge_zero
  by_cases cube_free : IsCubeFree word
  · exact ⟨word, ⟨[], [], by simp⟩, cube_free, bridge_zero⟩
  · simp only [IsCubeFree, not_not] at cube_free
    obtain ⟨left, right, word_eq⟩ := cube_free
    rw [word_eq, bridgeScalar_append_delimiter_cube] at bridge_zero
    rcases mul_eq_zero.mp bridge_zero with left_zero | right_zero
    · obtain ⟨chunk, chunk_in_left, chunk_cube_free, chunk_zero⟩ :=
        exists_cubeFree_bridgeScalar_zero_go β body left left_zero
      have left_in_word : left <:+: word := by
        refine ⟨[], none :: none :: none :: right, ?_⟩
        simpa using word_eq.symm
      exact ⟨chunk, chunk_in_left.trans left_in_word, chunk_cube_free, chunk_zero⟩
    · obtain ⟨chunk, chunk_in_right, chunk_cube_free, chunk_zero⟩ :=
        exists_cubeFree_bridgeScalar_zero_go β body right right_zero
      have right_in_word : right <:+: word := by
        refine ⟨left ++ [none, none, none], [], ?_⟩
        simpa [List.append_assoc] using word_eq.symm
      exact ⟨chunk, chunk_in_right.trans right_in_word, chunk_cube_free, chunk_zero⟩
termination_by word => word.length
decreasing_by
  · rw [word_eq]
    simp
  · rw [word_eq]
    simp
    omega

/-- Every scalar-zero word contains a cube-free scalar-zero descendant obtained by repeatedly
cutting at delimiter cubes. -/
theorem exists_cubeFree_bridgeScalar_zero_of_bridgeScalar_zero
    (β : Nat) (body : List TagLetter) {word : List (Option TagLetter)}
    (bridge_zero : DecimalSetterFracture.bridgeScalar β body word = 0) :
    ∃ chunk, chunk <:+: word ∧ IsCubeFree chunk ∧
      DecimalSetterFracture.bridgeScalar β body chunk = 0 :=
  exists_cubeFree_bridgeScalar_zero_go β body word bridge_zero

/-- A zero matrix word therefore supplies a cube-free zero bridge coefficient. -/
theorem exists_cubeFree_bridgeScalar_zero_of_wordProduct_eq_zero
    (β : Nat) (body : List TagLetter) {word : List (Option TagLetter)}
    (word_zero : wordProduct (generator β body) word = 0) :
    ∃ chunk, chunk <:+: word ∧ IsCubeFree chunk ∧
      DecimalSetterFracture.bridgeScalar β body chunk = 0 := by
  apply exists_cubeFree_bridgeScalar_zero_of_bridgeScalar_zero β body
  rw [DecimalSetterFracture.bridgeScalar, word_zero]
  simp

/-- Any zero bridge coefficient yields a literal zero word by surrounding it with delimiter
cubes. -/
theorem mortal_of_bridgeScalar_zero (β : Nat) (body : List TagLetter)
    {word : List (Option TagLetter)}
    (bridge_zero : DecimalSetterFracture.bridgeScalar β body word = 0) :
    IsMortal (generator β body) := by
  refine ⟨[none, none, none] ++ word ++ [none, none, none], by simp, ?_⟩
  rw [wordProduct_append, wordProduct_append]
  have triple_product :
      wordProduct (generator β body) [none, none, none] = delimiter β ^ 3 := by
    simp [generator, pow_succ, Matrix.mul_assoc]
  have folded_zero :
      terminalRow ᵥ* wordProduct (generator β body) word ⬝ᵥ firstAxis = 0 := by
    rw [← Matrix.dotProduct_mulVec]
    exact bridge_zero
  rw [triple_product, delimiter_cube, outer_mul, outer_mul_outer, folded_zero]
  simp

/-- A parsed target block hits the square-reset state generated by the blocks to its right. -/
def HitsSquarePole (β : Nat) (body : List TagLetter) (target : List NearyTile)
    (source : List (List NearyTile)) : Prop :=
  (roleProduct β body target *ᵥ squareReset β (bridgeState β body source)) 0 = 0

/-- Exact frontier of a parsed zero bridge. There is a leftmost erasure-ending target and at
least one block to its right. The target is either a singleton erasure, a non-singleton above one
ordinary rightmost block, or a non-singleton above a genuinely deeper block history. -/
theorem CoreSpelling.zero_frontier {β : Nat} (β_pos : 0 < β)
    (body : List TagLetter) {physical : List (Option TagLetter)}
    {blocks : List (List NearyTile)} (spelling : CoreSpelling physical blocks)
    (bridge_zero : DecimalSetterFracture.bridgeScalar β body physical = 0) :
    ∃ target next rest,
      blocks = target :: next :: rest ∧
        EndsInErase target ∧ BlocksLaw (next :: rest) ∧
          HitsSquarePole β body target (next :: rest) ∧
            ((∃ letter, target = [.erase letter]) ∨
              (2 ≤ target.length ∧ rest = []) ∨
                (2 ≤ target.length ∧ rest ≠ [])) := by
  have state_zero : bridgeState β body blocks 0 = 0 := by
    rw [← spelling.bridgeScalar_eq β_pos body]
    exact bridge_zero
  have law := spelling.blocksLaw
  cases blocks with
  | nil => exact False.elim law
  | cons target tail =>
      cases tail with
      | nil =>
          have state_pos := bridgeState_single_pos β_pos body target
          rw [state_zero] at state_pos
          norm_num at state_pos
      | cons next rest =>
          have target_ends : EndsInErase target := law.1
          refine ⟨target, next, rest, rfl, target_ends, law.2, ?_, ?_⟩
          · exact state_zero
          · by_cases target_single : target.length = 1
            · left
              obtain ⟨front, letter, target_eq⟩ := target_ends
              have front_length : front.length = 0 := by
                simpa [target_eq] using target_single
              have front_nil : front = [] := List.length_eq_zero_iff.mp front_length
              exact ⟨letter, by simpa [front_nil] using target_eq⟩
            · have target_positive : 0 < target.length := by
                obtain ⟨front, letter, target_eq⟩ := target_ends
                simp [target_eq]
              have target_large : 2 ≤ target.length := by omega
              right
              by_cases shallow : rest = []
              · exact Or.inl ⟨target_large, shallow⟩
              · exact Or.inr ⟨target_large, shallow⟩

/-- Every cube-free zero word contracts to the exact singleton/shallow/deep pole frontier. -/
theorem exists_boundaryZeroFrontier_of_cubeFree_zero
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    {word : List (Option TagLetter)} (cube_free : IsCubeFree word)
    (bridge_zero : DecimalSetterFracture.bridgeScalar β body word = 0) :
    ∃ core target next rest,
      IsBoundaryCore word core ∧
        CoreSpelling core (target :: next :: rest) ∧
          DecimalSetterFracture.bridgeScalar β body core = 0 ∧
            EndsInErase target ∧ BlocksLaw (next :: rest) ∧
              HitsSquarePole β body target (next :: rest) ∧
                ((∃ letter, target = [.erase letter]) ∨
                  (2 ≤ target.length ∧ rest = []) ∨
                    (2 ≤ target.length ∧ rest ≠ [])) := by
  obtain ⟨core, blocks, boundary, spelling, core_zero⟩ :=
    exists_boundaryCoreSpelling_of_cubeFree_zero cube_free bridge_zero
  obtain ⟨target, next, rest, blocks_eq, target_ends, suffix_law, pole, frontier⟩ :=
    spelling.zero_frontier β_pos body core_zero
  subst blocks
  exact ⟨core, target, next, rest, boundary, spelling, core_zero, target_ends,
    suffix_law, pole, frontier⟩

/-- Complete arbitrary-word reduction: every zero matrix word yields a cube-free zero chunk and
therefore one exact singleton/shallow/deep square-pole frontier. -/
theorem exists_zeroFrontier_of_wordProduct_eq_zero
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    {word : List (Option TagLetter)}
    (word_zero : wordProduct (generator β body) word = 0) :
    ∃ chunk core target next rest,
      chunk <:+: word ∧ IsCubeFree chunk ∧ IsBoundaryCore chunk core ∧
        CoreSpelling core (target :: next :: rest) ∧
          DecimalSetterFracture.bridgeScalar β body core = 0 ∧
            EndsInErase target ∧ BlocksLaw (next :: rest) ∧
              HitsSquarePole β body target (next :: rest) ∧
                ((∃ letter, target = [.erase letter]) ∨
                  (2 ≤ target.length ∧ rest = []) ∨
                    (2 ≤ target.length ∧ rest ≠ [])) := by
  obtain ⟨chunk, chunk_in_word, cube_free, chunk_zero⟩ :=
    exists_cubeFree_bridgeScalar_zero_of_wordProduct_eq_zero β body word_zero
  obtain ⟨core, target, next, rest, boundary, spelling, core_zero, target_ends,
      suffix_law, pole, frontier⟩ :=
    exists_boundaryZeroFrontier_of_cubeFree_zero β_pos body cube_free chunk_zero
  exact ⟨chunk, core, target, next, rest, chunk_in_word, cube_free, boundary, spelling,
    core_zero, target_ends, suffix_law, pole, frontier⟩

/-- Existence of one parsed singleton, shallow, or deep square-pole frontier. -/
def HasParsedZeroFrontier (β : Nat) (body : List TagLetter) : Prop :=
  ∃ core target next rest,
    CoreSpelling core (target :: next :: rest) ∧
      DecimalSetterFracture.bridgeScalar β body core = 0 ∧
        EndsInErase target ∧ BlocksLaw (next :: rest) ∧
          HitsSquarePole β body target (next :: rest) ∧
            ((∃ letter, target = [.erase letter]) ∨
              (2 ≤ target.length ∧ rest = []) ∨
                (2 ≤ target.length ∧ rest ≠ []))

/-- Mortality of the rational decimal setter is exactly existence of a parsed square-pole
frontier. This is the complete outer algebraic converse; excluding the displayed arithmetic
frontier remains a separate obligation. -/
theorem isMortal_iff_exists_parsedZeroFrontier {β : Nat} (β_pos : 0 < β)
    (body : List TagLetter) :
    IsMortal (generator β body) ↔ HasParsedZeroFrontier β body := by
  unfold HasParsedZeroFrontier
  constructor
  · intro mortal
    obtain ⟨word, word_zero⟩ :=
      (isMortal_iff_exists_wordProduct_eq_zero (generator β body)).mp mortal
    obtain ⟨chunk, core, target, next, rest, _, _, _, spelling, core_zero,
        target_ends, suffix_law, pole, frontier⟩ :=
      exists_zeroFrontier_of_wordProduct_eq_zero β_pos body word_zero
    exact ⟨core, target, next, rest, spelling, core_zero, target_ends,
      suffix_law, pole, frontier⟩
  · rintro ⟨core, target, next, rest, spelling, core_zero, target_ends,
      suffix_law, pole, frontier⟩
    exact mortal_of_bridgeScalar_zero β body core_zero

/-- The cleared three-generator integer `5 × 5` family has the same parsed pole frontier. -/
theorem mortalityProblem_mortal_iff_exists_parsedZeroFrontier
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter) :
    (DecimalSetterInteger.mortalityProblem β body).Mortal ↔
      HasParsedZeroFrontier β body := by
  rw [DecimalSetterInteger.mortalityProblem_mortal_iff,
    isMortal_iff_exists_parsedZeroFrontier β_pos]

end MatrixMortality.DecimalSetterBridge
