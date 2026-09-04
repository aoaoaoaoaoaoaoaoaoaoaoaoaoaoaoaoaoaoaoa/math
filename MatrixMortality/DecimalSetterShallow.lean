import MatrixMortality.DecimalSetterMinimumBody

/-!
# Complete shallow decimal pole classification

A non-singleton erasure-ended target has upper and lower boundary codes ending in decimal digits
`77`, so its transfer trace lies in shell `(1,1)`. Rewriting a shallow pole against the source
complement then forces the source's complete upper spelling to have length one. Parser law reduces
the source to `R_c`, whose pole equation is exactly the literal Neary terminal equation.
-/

namespace MatrixMortality.DecimalSetterShallow

open MatrixMortality.DecimalSetterArithmetic
open MatrixMortality.DecimalSetterBridge
open MatrixMortality.DecimalSetterCarry
open MatrixMortality.DecimalSetterMatrix
open MatrixMortality.PadicValuation

private theorem code_append_false_false_mod_hundred (stem : List Bool) :
    (code (stem ++ [false, false]) : ℤ) ≡ 77 [ZMOD 100] := by
  rw [code_append]
  norm_num [code, digit, Nat.ofDigits]

private theorem ten_pow_mod_hundred {β : Nat} (β_large : 2 ≤ β) :
    (10 : ℤ) ^ β ≡ 0 [ZMOD 100] := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le β_large
  have square_mod : (10 : ℤ) ^ 2 ≡ 0 [ZMOD 100] := by norm_num
  simpa [pow_add, mul_comm] using
    square_mod.mul (Int.ModEq.refl ((10 : ℤ) ^ offset))

private theorem punctuatedUpper_ends_false_false {β : Nat} (β_large : 2 ≤ β)
    (roles : List NearyTile) :
    ∃ stem,
      spell (nearyUpper β) roles ++ nearyMarker β = stem ++ [false, false] := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le β_large
  refine ⟨spell (nearyUpper (2 + offset)) roles ++
      true :: List.replicate offset false, ?_⟩
  simp [nearyMarker, List.replicate_add, List.append_assoc, Nat.add_comm]

private theorem spellLower_ends_false
    (β : Nat) (body : List TagLetter) (roles : List NearyTile) (roles_ne : roles ≠ []) :
    ∃ stem, spell (nearyLower β body) roles = stem ++ [false] := by
  induction roles with
  | nil => exact False.elim (roles_ne rfl)
  | cons role tail induction =>
      by_cases tail_empty : tail = []
      · subst tail
        obtain ⟨_, lower, _, lower_eq⟩ := nearyTile_final_mismatch β body role
        exact ⟨lower, by simpa [spell] using lower_eq⟩
      · obtain ⟨stem, shape⟩ := induction tail_empty
        exact ⟨nearyLower β body role ++ stem, by
          change nearyLower β body role ++ spell (nearyLower β body) tail = _
          rw [shape, List.append_assoc]⟩

private theorem lower_ends_false_false_of_multi_endsInErase
    (β : Nat) (body : List TagLetter) {roles : List NearyTile}
    (roles_multi : 2 ≤ roles.length) (roles_ends : EndsInErase roles) :
    ∃ stem, spell (nearyLower β body) roles = stem ++ [false, false] := by
  obtain ⟨front, letter, roles_eq⟩ := roles_ends
  have front_ne : front ≠ [] := by
    intro front_eq
    rw [roles_eq, front_eq] at roles_multi
    simp at roles_multi
  have front_lower := spellLower_ends_false β body front front_ne
  obtain ⟨stem, front_eq⟩ := front_lower
  refine ⟨stem, ?_⟩
  rw [roles_eq, spell_append, front_eq]
  simp [spell, nearyLower, List.append_assoc]

/-- Every positive-width punctuated upper boundary ends in decimal digits `77`. -/
theorem upperBoundaryCode_mod_hundred {β : Nat} (β_large : 2 ≤ β)
    (roles : List NearyTile) :
    (code (spell (nearyUpper β) roles ++ nearyMarker β) : ℤ) ≡ 77 [ZMOD 100] := by
  obtain ⟨stem, word_eq⟩ := punctuatedUpper_ends_false_false β_large roles
  rw [word_eq]
  exact code_append_false_false_mod_hundred stem

/-- A non-singleton erasure-ended block's lower boundary ends in decimal digits `77`. -/
theorem lowerBoundaryCode_mod_hundred_of_multi_endsInErase
    (β : Nat) (body : List TagLetter) {roles : List NearyTile}
    (roles_multi : 2 ≤ roles.length) (roles_ends : EndsInErase roles) :
    (code (spell (nearyLower β body) roles) : ℤ) ≡ 77 [ZMOD 100] := by
  obtain ⟨stem, word_eq⟩ :=
    lower_ends_false_false_of_multi_endsInErase β body roles_multi roles_ends
  rw [word_eq]
  exact code_append_false_false_mod_hundred stem

/-- Every non-singleton erasure-ended target has transfer-trace shell `(1,1)`. -/
theorem multiRoleErasureEnded_boundaryTrace_hasDecimalShell
    {β : Nat} (β_large : 2 ≤ β) (body : List TagLetter)
    {target : List NearyTile} (target_multi : 2 ≤ target.length)
    (target_ends : EndsInErase target) :
    HasDecimalShell
      (gap ((10 : ℚ) ^ β) * upperBoundaryCode β target +
        lift ((10 : ℚ) ^ β) * lowerBoundaryCode β body target) 1 1 := by
  have trace_shell := multiErasure_trace_hasDecimalShell
    (ten_pow_mod_hundred β_large)
    (upperBoundaryCode_mod_hundred β_large target)
    (lowerBoundaryCode_mod_hundred_of_multi_endsInErase
      β body target_multi target_ends)
  simpa [transferTrace, decimalGap, decimalLift, gap, lift,
    upperBoundaryCode, lowerBoundaryCode] using trace_shell

private theorem one_hasDecimalShell : HasDecimalShell (1 : ℚ) 0 0 :=
  ⟨⟨one_ne_zero, padicValRat.one⟩, ⟨one_ne_zero, padicValRat.one⟩⟩

/-- Any shallow pole over a non-singleton erasure-ended target forces the source upper spelling
to contain exactly one digit. -/
theorem shallowSquarePole_sourceUpperLength_eq_one
    {β : Nat} (β_large : 2 ≤ β) (body : List TagLetter)
    {target source : List NearyTile} (target_multi : 2 ≤ target.length)
    (target_ends : EndsInErase target)
    (pole : HitsSquarePole β body target [source]) :
    (spell (nearyUpper β) source).length = 1 := by
  let m := (spell (nearyUpper β) source).length
  have β_pos : 0 < β := by omega
  have source_unit := upperBoundaryCode_decimalUnit β_pos source
  have trace_shell :=
    multiRoleErasureEnded_boundaryTrace_hasDecimalShell β_large body target_multi target_ends
  have marker_unit : HasDecimalShell (DecimalSetterMatrix.marker β) 0 0 := by
    simpa [upperBoundaryCode, DecimalSetterMatrix.marker, spell] using
      (upperBoundaryCode_decimalUnit β_pos ([] : List NearyTile))
  have nine_unit : HasDecimalShell (9 : ℚ) 0 0 :=
    ⟨intCast_isUnit_of_not_dvd (by norm_num),
      intCast_isUnit_of_not_dvd (by norm_num)⟩
  have lift_unit : HasDecimalShell (lift ((10 : ℚ) ^ β)) 0 0 := by
    have scaled := nine_unit.mul
      (upperBoundaryCode_decimalUnit β_pos DecimalSetterMinimumBody.ruleCRoot)
    rw [DecimalSetterMinimumBody.ruleCRoot_code_calibration] at scaled
    exact scaled
  have lower_unit : HasDecimalShell (lowerBoundaryCode β body target) 0 0 := by
    obtain ⟨stem, lower_eq⟩ :=
      lower_ends_false_false_of_multi_endsInErase β body target_multi target_ends
    unfold lowerBoundaryCode
    rw [lower_eq, show stem ++ [false, false] = (stem ++ [false]) ++ [false] by simp]
    exact code_append_false_hasDecimalShell (stem ++ [false])
  have pole_eq :=
    (hitsSquarePole_single_iff_generalizedRawHead β_pos body target source).mp pole
  have reset_equation :
      upperBoundaryCode β source *
          (gap ((10 : ℚ) ^ β) * upperBoundaryCode β target +
            lift ((10 : ℚ) ^ β) * lowerBoundaryCode β body target) =
        1 * lift ((10 : ℚ) ^ β) * DecimalSetterMatrix.marker β * 10 ^ m *
          lowerBoundaryCode β body target := by
    rw [upperBoundaryComplement] at pole_eq
    dsimp only [m]
    linear_combination pole_eq
  exact resetZero_multiTarget_length source_unit trace_shell one_hasDecimalShell
    lift_unit marker_unit lower_unit reset_equation

/-- No source containing at least two roles can underlie a shallow non-singleton target pole. -/
theorem shallowSquarePole_impossible_of_source_multi
    {β : Nat} (β_large : 2 ≤ β) (body : List TagLetter)
    {target source : List NearyTile} (target_multi : 2 ≤ target.length)
    (target_ends : EndsInErase target) (source_multi : 2 ≤ source.length) :
    ¬HitsSquarePole β body target [source] := by
  intro pole
  have upper_length_eq := shallowSquarePole_sourceUpperLength_eq_one
    β_large body target_multi target_ends pole
  have upper_length_lower :
      source.length ≤ (spell (nearyUpper β) source).length := by
    rw [spell_nearyUpper]
    simpa using
      (DecimalSetterChamber.length_le_tagEncode β (source.map NearyTile.letter))
  omega

/-- Complete parser-lawful shallow classification: a non-singleton erasure-ended target hits
exactly over the one-`R_c` root and exactly when it is a literal Neary terminal match. -/
theorem shallowSquarePole_iff_ruleCRoot_terminalMatch
    {β : Nat} (β_large : 2 ≤ β) (body : List TagLetter)
    {target source : List NearyTile} (target_multi : 2 ≤ target.length)
    (target_ends : EndsInErase target) (source_ends : EndsInRule source) :
    HitsSquarePole β body target [source] ↔
      source = DecimalSetterMinimumBody.ruleCRoot ∧
        spell (nearyUpper β) target ++ nearyMarker β =
          spell (nearyLower β body) target := by
  constructor
  · intro pole
    have upper_length_eq := shallowSquarePole_sourceUpperLength_eq_one
      β_large body target_multi target_ends pole
    have source_length_upper :
        source.length ≤ (spell (nearyUpper β) source).length := by
      rw [spell_nearyUpper]
      simpa using
        (DecimalSetterChamber.length_le_tagEncode β (source.map NearyTile.letter))
    obtain ⟨front, letter, source_eq⟩ := source_ends
    have source_length_le_one : source.length ≤ 1 := by
      rw [upper_length_eq] at source_length_upper
      exact source_length_upper
    have front_nil : front = [] := by
      have front_length_le : front.length + 1 ≤ 1 := by
        calc
          front.length + 1 = source.length := by simp [source_eq]
          _ ≤ 1 := source_length_le_one
      exact List.length_eq_zero_iff.mp (by omega)
    have source_singleton : source = [.rule letter] := by
      simpa [front_nil] using source_eq
    have classified :=
      (DecimalSetterMinimumBody.singletonRuleRoot_hitsSquarePole_iff_terminalMatch
        (β := β) (by omega) body target letter).mp
          (by simpa [source_singleton] using pole)
    have letter_c : letter = .c := classified.1
    subst letter
    exact ⟨by simp [source_singleton, DecimalSetterMinimumBody.ruleCRoot], classified.2⟩
  · rintro ⟨rfl, terminal_match⟩
    exact
      (DecimalSetterMinimumBody.ruleCRoot_hitsSquarePole_iff_terminalMatch
        (β := β) (by omega) body target).mpr terminal_match

/-- The shallow branch of an actual two-block parser spelling is exactly the lawful `R_c`
terminal branch. -/
theorem coreSpelling_shallowSquarePole_iff_ruleCRoot_terminalMatch
    {β : Nat} (β_large : 2 ≤ β) (body : List TagLetter)
    {core : List (Option TagLetter)} {target source : List NearyTile}
    (spelling : CoreSpelling core [target, source]) (target_multi : 2 ≤ target.length) :
    HitsSquarePole β body target [source] ↔
      source = DecimalSetterMinimumBody.ruleCRoot ∧
        spell (nearyUpper β) target ++ nearyMarker β =
          spell (nearyLower β body) target := by
  have law := spelling.blocksLaw
  exact shallowSquarePole_iff_ruleCRoot_terminalMatch
    β_large body target_multi law.1 law.2

end MatrixMortality.DecimalSetterShallow
