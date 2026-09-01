import MatrixMortality.DecimalSetterBridge
import MatrixMortality.DecimalSetterPositioned
import MatrixMortality.HistoryFracture
import MatrixMortality.Undecidability.NearyCompiler

/-!
# Minimum-body shallow decimal pole

At the minimum admissible body length, the decimal setter's generalized shallow pole is attained
exactly.  This is the lawful terminal word of an immediately halting tag instance, not a false
positive.  Compiler-emitted bodies lie strictly above this slice.
-/

namespace MatrixMortality.DecimalSetterMinimumBody

open MatrixMortality.DecimalSetterBridge
open MatrixMortality.DecimalSetterAncestry
open MatrixMortality.DecimalSetterMatrix
open MatrixMortality.Undecidability

/-- The one-role root immediately to the right of the shallow reset. -/
def minimumBodyRoot : List NearyTile := [.rule .c]

private theorem minimumBodyTarget_upper_spelling (β : Nat) (body : List TagLetter) :
    spell (nearyUpper β) (minimalBodyWord body) =
      [true] ++ tagEncode β body := by
  rw [spell_nearyUpper]
  have roles_letters :
      (minimalBodyWord body).map NearyTile.letter = .c :: body := by
    simp [minimalBodyWord, NearyTile.letter, Function.comp_def]
  rw [roles_letters, tagEncode_cons]
  rfl

private theorem minimumBodyTarget_lower_spelling (β : Nat) (body : List TagLetter) :
    spell (nearyLower β body) (minimalBodyWord body) =
      [true] ++ tagEncode β body ++ [true, false] ++
        List.replicate body.length false := by
  rw [show minimalBodyWord body = [.rule .c] ++ letterEraseBlock body by
        simp [minimalBodyWord, letterEraseBlock],
    spell_append, spell_letterEraseBlock_lower]
  simp [spell, nearyLower, List.append_assoc]

/-- At length `|body|=β−1`, the target's punctuated upper and complete lower words coincide
literally. -/
theorem minimumBodyTarget_word_identity {β : Nat} (β_pos : 0 < β)
    {body : List TagLetter} (body_length : body.length = β - 1) :
    spell (nearyUpper β) (minimalBodyWord body) ++ nearyMarker β =
      spell (nearyLower β body) (minimalBodyWord body) := by
  obtain ⟨offset, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt β_pos)
  have body_length_eq : body.length = offset := by omega
  rw [minimumBodyTarget_upper_spelling, minimumBodyTarget_lower_spelling]
  simp [nearyMarker, body_length_eq, List.replicate_succ', List.append_assoc]
  rw [← List.replicate_succ', List.replicate_succ]

/-- The minimum-body source queue is already shorter than the deletion width, so the pole below
belongs to a lawful immediately halting instance. -/
theorem minimumBody_initialQueue_halts {β : Nat} (β_large : 2 < β)
    {body : List TagLetter} (body_length : body.length = β - 1) :
    TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  apply TagHaltsFrom.stop
  simp [body_length]
  omega

/-- The pole target is the unique terminal role spelling on the minimum-body slice. -/
theorem minimumBodyTarget_unique {β : Nat} (β_large : 2 < β)
    {body : List TagLetter} (body_length : body.length = β - 1)
    {word : List NearyTile}
    (terminal_match :
      spell (nearyUpper β) word ++ nearyMarker β =
        spell (nearyLower β body) word) :
    word = minimalBodyWord body := by
  exact minimalBody_terminal_word_unique β body (by omega) body_length
    word terminal_match

/-- The target's upper and lower decimal codes are therefore equal on the minimum-body slice. -/
theorem minimumBodyTarget_boundaryCode_eq {β : Nat} (β_pos : 0 < β)
    {body : List TagLetter} (body_length : body.length = β - 1) :
    upperBoundaryCode β (minimalBodyWord body) =
      lowerBoundaryCode β body (minimalBodyWord body) := by
  unfold upperBoundaryCode lowerBoundaryCode
  rw [minimumBodyTarget_word_identity β_pos body_length]

/-- The punctuated upper code of the one-`R_c` root is one ninth of the physical lift. -/
theorem minimumBodyRoot_code_calibration (β : Nat) :
    9 * upperBoundaryCode β minimumBodyRoot =
      DecimalSetterCarry.lift ((10 : ℚ) ^ β) := by
  calc
    9 * upperBoundaryCode β minimumBodyRoot =
        45 * (10 : ℚ) ^ (β + 1) + 9 * marker β := by
      rw [upperBoundaryCode_eq]
      simp [minimumBodyRoot, spell, nearyUpper, tagCode, markerScale]
      ring
    _ = 502 * (10 : ℚ) ^ β - 7 := by
      rw [marker_relation, pow_succ]
      ring
    _ = DecimalSetterCarry.lift ((10 : ℚ) ^ β) := by
      simp [DecimalSetterCarry.lift]

/-- The exact-length complement of the one-`R_c` root is one ninth of the physical gap. -/
theorem minimumBodyRoot_complement_calibration (β : Nat) :
    9 * upperBoundaryComplement β minimumBodyRoot =
      DecimalSetterCarry.gap ((10 : ℚ) ^ β) := by
  calc
    9 * upperBoundaryComplement β minimumBodyRoot =
        10 * (9 * marker β) - 9 * upperBoundaryCode β minimumBodyRoot := by
      simp [upperBoundaryComplement, minimumBodyRoot, spell, nearyUpper, tagCode]
      ring
    _ = 10 * (52 * (10 : ℚ) ^ β - 7) -
        DecimalSetterCarry.lift ((10 : ℚ) ^ β) := by
      rw [marker_relation, minimumBodyRoot_code_calibration]
    _ = DecimalSetterCarry.gap ((10 : ℚ) ^ β) := by
      simp [DecimalSetterCarry.gap, DecimalSetterCarry.lift]
      ring

/-- The lawful minimum-body target hits the exact shallow square-reset pole over the one-`R_c`
root. -/
theorem minimumBodyTarget_hitsSquarePole {β : Nat} (β_pos : 0 < β)
    {body : List TagLetter} (body_length : body.length = β - 1) :
    HitsSquarePole β body (minimalBodyWord body) [minimumBodyRoot] := by
  rw [hitsSquarePole_single_iff_generalizedRawHead β_pos]
  rw [minimumBodyTarget_boundaryCode_eq β_pos body_length]
  calc
    DecimalSetterCarry.gap ((10 : ℚ) ^ β) *
          lowerBoundaryCode β body (minimalBodyWord body) *
          upperBoundaryCode β minimumBodyRoot =
        (9 * upperBoundaryComplement β minimumBodyRoot) *
          lowerBoundaryCode β body (minimalBodyWord body) *
          upperBoundaryCode β minimumBodyRoot := by
      rw [minimumBodyRoot_complement_calibration]
    _ = (9 * upperBoundaryCode β minimumBodyRoot) *
          lowerBoundaryCode β body (minimalBodyWord body) *
          upperBoundaryComplement β minimumBodyRoot := by ring
    _ = DecimalSetterCarry.lift ((10 : ℚ) ^ β) *
          lowerBoundaryCode β body (minimalBodyWord body) *
          upperBoundaryComplement β minimumBodyRoot := by
      rw [minimumBodyRoot_code_calibration]

private theorem exists_eraseTarget_coreSpelling (front : List TagLetter)
    (last : TagLetter) :
    ∃ core,
      CoreSpelling core
        (letterEraseBlock (front ++ [last]) :: [minimumBodyRoot]) := by
  induction front with
  | nil =>
      refine ⟨[some last, none, none, some .c], ?_⟩
      simpa [letterEraseBlock, minimumBodyRoot] using
        CoreSpelling.square last (CoreSpelling.terminal .c)
  | cons letter front induction =>
      obtain ⟨core, spelling⟩ := induction
      refine ⟨some letter :: none :: core, ?_⟩
      simpa [letterEraseBlock] using CoreSpelling.erase letter spelling

/-- Every nonempty minimum body has a literal cube-free core spelling for the shallow pole. -/
theorem exists_minimumBody_coreSpelling {body : List TagLetter} (body_ne : body ≠ []) :
    ∃ core,
      CoreSpelling core (minimalBodyWord body :: [minimumBodyRoot]) := by
  induction body using List.reverseRecOn with
  | nil => exact False.elim (body_ne rfl)
  | append_singleton front last =>
      obtain ⟨core, spelling⟩ := exists_eraseTarget_coreSpelling front last
      refine ⟨some .c :: core, ?_⟩
      simpa [minimalBodyWord, minimumBodyRoot, letterEraseBlock] using
        CoreSpelling.rule .c spelling

/-- Every minimum-length body occupies the shallow branch of the complete parsed zero frontier. -/
theorem hasParsedZeroFrontier_of_minimumBody {β : Nat} (β_large : 2 < β)
    {body : List TagLetter} (body_length : body.length = β - 1) :
    HasParsedZeroFrontier β body := by
  have body_ne : body ≠ [] := by
    intro body_eq
    rw [body_eq] at body_length
    simp at body_length
    omega
  obtain ⟨core, spelling⟩ := exists_minimumBody_coreSpelling body_ne
  have pole := minimumBodyTarget_hitsSquarePole (by omega) body_length
  have bridge_zero : DecimalSetterFracture.bridgeScalar β body core = 0 := by
    rw [spelling.bridgeScalar_eq (by omega) body]
    simpa [HitsSquarePole, bridgeState] using pole
  have blocks_law := spelling.blocksLaw
  have target_multi : 2 ≤ (minimalBodyWord body).length := by
    simp [minimalBodyWord, body_length]
    omega
  exact ⟨core, minimalBodyWord body, minimumBodyRoot, [], spelling, bridge_zero,
    blocks_law.1, blocks_law.2, pole, Or.inr (Or.inl ⟨target_multi, rfl⟩)⟩

/-- Every minimum-length body produces an actual mortal rational decimal setter. This witness is
the lawful terminal computation, not a malformed false positive. -/
theorem generator_isMortal_of_minimumBody {β : Nat} (β_large : 2 < β)
    {body : List TagLetter} (body_length : body.length = β - 1) :
    IsMortal (generator β body) := by
  exact (isMortal_iff_exists_parsedZeroFrontier (by omega) body).mpr
    (hasParsedZeroFrontier_of_minimumBody β_large body_length)

/-- Exact clearing transports the minimum-body witness to the integer three-generator
`5 × 5` family. -/
theorem mortalityProblem_mortal_of_minimumBody {β : Nat} (β_large : 2 < β)
    {body : List TagLetter} (body_length : body.length = β - 1) :
    (DecimalSetterInteger.mortalityProblem β body).Mortal := by
  rw [DecimalSetterInteger.mortalityProblem_mortal_iff]
  exact generator_isMortal_of_minimumBody β_large body_length

/-- Neary's primitive-recursive compiler emits bodies strictly longer than the minimum-body
slice, so the exact witness above does not by itself decide the intended universal family. -/
theorem compiler_body_length_gt_minimum {period : Nat} (system : CyclicTag period)
    (input : List Bool) (haltPhase : Fin period) (period_pos : 0 < period) :
    NearyCompiler.deletionWidth period - 1 <
      (NearyCompiler.body system input haltPhase period_pos).length := by
  rw [NearyCompiler.body_length]
  have β_large := NearyCompiler.deletionWidth_large period_pos
  have minimum_pos : 0 < NearyCompiler.deletionWidth period - 1 := by omega
  have factor_large :
      1 < NearyCompiler.safetyBound system input *
          NearyCompiler.deletionWidth period + 1 := by
    have safety_pos := NearyCompiler.safetyBound_pos system input
    have product_pos :
        0 < NearyCompiler.safetyBound system input *
          NearyCompiler.deletionWidth period :=
      Nat.mul_pos safety_pos (NearyCompiler.deletionWidth_pos period_pos)
    omega
  exact lt_mul_of_one_lt_left minimum_pos factor_large

end MatrixMortality.DecimalSetterMinimumBody
