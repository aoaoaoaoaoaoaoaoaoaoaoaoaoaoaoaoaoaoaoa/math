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

/-- The one-`R_c` root immediately to the right of a shallow reset. -/
def ruleCRoot : List NearyTile := [.rule .c]

/-- The other one-role parser root. -/
def ruleBRoot : List NearyTile := [.rule .b]

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
theorem ruleCRoot_code_calibration (β : Nat) :
    9 * upperBoundaryCode β ruleCRoot =
      DecimalSetterCarry.lift ((10 : ℚ) ^ β) := by
  calc
    9 * upperBoundaryCode β ruleCRoot =
        45 * (10 : ℚ) ^ (β + 1) + 9 * marker β := by
      rw [upperBoundaryCode_eq]
      simp [ruleCRoot, spell, nearyUpper, tagCode, markerScale]
      ring
    _ = 502 * (10 : ℚ) ^ β - 7 := by
      rw [marker_relation, pow_succ]
      ring
    _ = DecimalSetterCarry.lift ((10 : ℚ) ^ β) := by
      simp [DecimalSetterCarry.lift]

/-- The exact-length complement of the one-`R_c` root is one ninth of the physical gap. -/
theorem ruleCRoot_complement_calibration (β : Nat) :
    9 * upperBoundaryComplement β ruleCRoot =
      DecimalSetterCarry.gap ((10 : ℚ) ^ β) := by
  calc
    9 * upperBoundaryComplement β ruleCRoot =
        10 * (9 * marker β) - 9 * upperBoundaryCode β ruleCRoot := by
      simp [upperBoundaryComplement, ruleCRoot, spell, nearyUpper, tagCode]
      ring
    _ = 10 * (52 * (10 : ℚ) ^ β - 7) -
        DecimalSetterCarry.lift ((10 : ℚ) ^ β) := by
      rw [marker_relation, ruleCRoot_code_calibration]
    _ = DecimalSetterCarry.gap ((10 : ℚ) ^ β) := by
      simp [DecimalSetterCarry.gap, DecimalSetterCarry.lift]
      ring

/-- The exact-length complement of the one-`R_b` root is negative one ninth of the physical
lift. -/
theorem ruleBRoot_complement_calibration (β : Nat) :
    9 * upperBoundaryComplement β ruleBRoot =
      -DecimalSetterCarry.lift ((10 : ℚ) ^ β) := by
  have upper_spelling :
      spell (nearyUpper β) ruleBRoot = DecimalSetterChamber.bTag β := by
    simp [ruleBRoot, spell, nearyUpper, tagCode, DecimalSetterChamber.bTag,
      DecimalSetterChamber.markerWord]
  have upper_code :
      (DecimalSetterCarry.code (spell (nearyUpper β) ruleBRoot) : ℚ) =
        10 * marker β + 5 := by
    rw [upper_spelling, DecimalSetterChamber.bTag_code]
    simp [marker, DecimalSetterChamber.markerWord, nearyMarker]
  calc
    9 * upperBoundaryComplement β ruleBRoot =
        -(450 * (10 : ℚ) ^ β + 9 * marker β) := by
      rw [upperBoundaryComplement, upperBoundaryCode_eq, upper_code]
      simp [ruleBRoot, spell, nearyUpper, tagCode, markerScale]
      rw [show β + 2 = (β + 1) + 1 by omega, pow_succ, pow_succ]
      ring
    _ = -(502 * (10 : ℚ) ^ β - 7) := by
      rw [marker_relation]
      ring
    _ = -DecimalSetterCarry.lift ((10 : ℚ) ^ β) := by
      simp [DecimalSetterCarry.lift]

/-- Equality of a target's decimal boundary codes is equivalent to its literal Neary terminal
word equation. -/
theorem boundaryCode_eq_iff_terminalMatch (β : Nat) (body : List TagLetter)
    (target : List NearyTile) :
    upperBoundaryCode β target = lowerBoundaryCode β body target ↔
      spell (nearyUpper β) target ++ nearyMarker β =
        spell (nearyLower β body) target := by
  unfold upperBoundaryCode lowerBoundaryCode
  constructor
  · intro code_eq
    apply DecimalSetterCarry.code_injective
    exact_mod_cast code_eq
  · intro word_eq
    rw [word_eq]

/-- Over the one-`R_c` root, a shallow pole is exactly equality of the target's upper and lower
boundary codes. -/
theorem ruleCRoot_hitsSquarePole_iff_boundaryCode_eq
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter) (target : List NearyTile) :
    HitsSquarePole β body target [ruleCRoot] ↔
      upperBoundaryCode β target = lowerBoundaryCode β body target := by
  rw [hitsSquarePole_single_iff_generalizedRawHead β_pos]
  have root_ends : EndsInRule ruleCRoot := by
    exact ⟨[], .c, by simp [ruleCRoot]⟩
  obtain ⟨root_unit, complement_unit⟩ := sourceBoundary_decimalUnits β_pos root_ends
  have factor_ne :
      9 * upperBoundaryCode β ruleCRoot * upperBoundaryComplement β ruleCRoot ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) root_unit.1.1) complement_unit.1.1
  constructor
  · intro pole
    have scaled :
        (9 * upperBoundaryCode β ruleCRoot * upperBoundaryComplement β ruleCRoot) *
            upperBoundaryCode β target =
          (9 * upperBoundaryCode β ruleCRoot * upperBoundaryComplement β ruleCRoot) *
            lowerBoundaryCode β body target := by
      calc
        (9 * upperBoundaryCode β ruleCRoot * upperBoundaryComplement β ruleCRoot) *
              upperBoundaryCode β target =
            DecimalSetterCarry.gap ((10 : ℚ) ^ β) *
              upperBoundaryCode β target * upperBoundaryCode β ruleCRoot := by
          rw [← ruleCRoot_complement_calibration]
          ring
        _ = DecimalSetterCarry.lift ((10 : ℚ) ^ β) *
              lowerBoundaryCode β body target * upperBoundaryComplement β ruleCRoot := pole
        _ = (9 * upperBoundaryCode β ruleCRoot *
              upperBoundaryComplement β ruleCRoot) *
              lowerBoundaryCode β body target := by
          rw [← ruleCRoot_code_calibration]
          ring
    exact mul_left_cancel₀ factor_ne scaled
  · intro code_eq
    rw [code_eq]
    calc
      DecimalSetterCarry.gap ((10 : ℚ) ^ β) *
            lowerBoundaryCode β body target * upperBoundaryCode β ruleCRoot =
          (9 * upperBoundaryComplement β ruleCRoot) *
            lowerBoundaryCode β body target * upperBoundaryCode β ruleCRoot := by
        rw [ruleCRoot_complement_calibration]
      _ = (9 * upperBoundaryCode β ruleCRoot) *
            lowerBoundaryCode β body target * upperBoundaryComplement β ruleCRoot := by ring
      _ = DecimalSetterCarry.lift ((10 : ℚ) ^ β) *
            lowerBoundaryCode β body target * upperBoundaryComplement β ruleCRoot := by
        rw [ruleCRoot_code_calibration]

/-- Complete one-`R_c` shallow-root normalization: its pole language is exactly the literal
Neary terminal language, so this root admits no malformed shallow pole. -/
theorem ruleCRoot_hitsSquarePole_iff_terminalMatch
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter) (target : List NearyTile) :
    HitsSquarePole β body target [ruleCRoot] ↔
      spell (nearyUpper β) target ++ nearyMarker β =
        spell (nearyLower β body) target := by
  rw [ruleCRoot_hitsSquarePole_iff_boundaryCode_eq β_pos,
    boundaryCode_eq_iff_terminalMatch]

/-- The one-`R_b` root cannot hit any shallow square-reset pole: its exact-length complement has
the opposite sign from every physical target code. -/
theorem ruleBRoot_hitsSquarePole_impossible
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter) (target : List NearyTile) :
    ¬HitsSquarePole β body target [ruleBRoot] := by
  have rho_lower : (10 : ℚ) ≤ 10 ^ β := by
    obtain ⟨offset, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt β_pos)
    have power_one : (1 : ℚ) ≤ 10 ^ offset := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    nlinarith
  have gap_pos : 0 < DecimalSetterCarry.gap ((10 : ℚ) ^ β) := by
    simp [DecimalSetterCarry.gap]
    linarith
  have lift_pos : 0 < DecimalSetterCarry.lift ((10 : ℚ) ^ β) := by
    simp [DecimalSetterCarry.lift]
    linarith
  have target_upper_unit := upperBoundaryCode_decimalUnit β_pos target
  have target_upper_nonneg : 0 ≤ upperBoundaryCode β target := by
    unfold upperBoundaryCode
    positivity
  have target_upper_pos : 0 < upperBoundaryCode β target :=
    lt_of_le_of_ne target_upper_nonneg (Ne.symm target_upper_unit.1.1)
  have root_upper_unit := upperBoundaryCode_decimalUnit β_pos ruleBRoot
  have root_upper_nonneg : 0 ≤ upperBoundaryCode β ruleBRoot := by
    unfold upperBoundaryCode
    positivity
  have root_upper_pos : 0 < upperBoundaryCode β ruleBRoot :=
    lt_of_le_of_ne root_upper_nonneg (Ne.symm root_upper_unit.1.1)
  have target_lower_nonneg : 0 ≤ lowerBoundaryCode β body target := by
    unfold lowerBoundaryCode
    positivity
  have complement_neg : upperBoundaryComplement β ruleBRoot < 0 := by
    have calibration := ruleBRoot_complement_calibration β
    nlinarith
  intro pole
  have equation :=
    (hitsSquarePole_single_iff_generalizedRawHead β_pos body target ruleBRoot).mp pole
  have left_pos :
      0 < DecimalSetterCarry.gap ((10 : ℚ) ^ β) *
        upperBoundaryCode β target * upperBoundaryCode β ruleBRoot :=
    mul_pos (mul_pos gap_pos target_upper_pos) root_upper_pos
  have right_nonpos :
      DecimalSetterCarry.lift ((10 : ℚ) ^ β) *
          lowerBoundaryCode β body target * upperBoundaryComplement β ruleBRoot ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg lift_pos.le target_lower_nonneg) complement_neg.le
  rw [equation] at left_pos
  exact (not_lt_of_ge right_nonpos) left_pos

/-- Complete one-role shallow-source classification: only `R_c` can hit, and it hits exactly on
a literal terminal match. -/
theorem singletonRuleRoot_hitsSquarePole_iff_terminalMatch
    {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (target : List NearyTile) (letter : TagLetter) :
    HitsSquarePole β body target [[.rule letter]] ↔
      letter = .c ∧
        spell (nearyUpper β) target ++ nearyMarker β =
          spell (nearyLower β body) target := by
  cases letter with
  | b =>
      simpa [ruleBRoot] using ruleBRoot_hitsSquarePole_impossible β_pos body target
  | c =>
      simpa [ruleCRoot] using
        ruleCRoot_hitsSquarePole_iff_terminalMatch β_pos body target

/-- The lawful minimum-body target hits the exact shallow square-reset pole over the one-`R_c`
root. -/
theorem minimumBodyTarget_hitsSquarePole {β : Nat} (β_pos : 0 < β)
    {body : List TagLetter} (body_length : body.length = β - 1) :
    HitsSquarePole β body (minimalBodyWord body) [ruleCRoot] := by
  exact (ruleCRoot_hitsSquarePole_iff_terminalMatch β_pos body _).mpr
    (minimumBodyTarget_word_identity β_pos body_length)

private theorem exists_eraseTarget_coreSpelling (front : List TagLetter)
    (last : TagLetter) :
    ∃ core,
      CoreSpelling core
        (letterEraseBlock (front ++ [last]) :: [ruleCRoot]) := by
  induction front with
  | nil =>
      refine ⟨[some last, none, none, some .c], ?_⟩
      simpa [letterEraseBlock, ruleCRoot] using
        CoreSpelling.square last (CoreSpelling.terminal .c)
  | cons letter front induction =>
      obtain ⟨core, spelling⟩ := induction
      refine ⟨some letter :: none :: core, ?_⟩
      simpa [letterEraseBlock] using CoreSpelling.erase letter spelling

/-- Every nonempty minimum body has a literal cube-free core spelling for the shallow pole. -/
theorem exists_minimumBody_coreSpelling {body : List TagLetter} (body_ne : body ≠ []) :
    ∃ core,
      CoreSpelling core (minimalBodyWord body :: [ruleCRoot]) := by
  induction body using List.reverseRecOn with
  | nil => exact False.elim (body_ne rfl)
  | append_singleton front last =>
      obtain ⟨core, spelling⟩ := exists_eraseTarget_coreSpelling front last
      refine ⟨some .c :: core, ?_⟩
      simpa [minimalBodyWord, ruleCRoot, letterEraseBlock] using
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
  exact ⟨core, minimalBodyWord body, ruleCRoot, [], spelling, bridge_zero,
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
