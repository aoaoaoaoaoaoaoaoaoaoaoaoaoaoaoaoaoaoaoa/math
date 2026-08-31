import MatrixMortality.ExpandingHistoryNoGo
import MatrixMortality.ForcedRuleCCompanion

/-!
# Sourcewise-existential probe blindness

Exact Hankel certificates do not survive weakening to sourcewise zero existence. A uniform guard
transform preserves whether a series has a zero while moving every zero beyond any prescribed
finite word horizon. Applied to the forced-rule derivative, it turns the complete MM-O18 probe
matrix into the constant-one matrix without changing terminal-match existence.

The complementary computability theorem rules out the opposite shortcut: a uniform universal
compiler cannot have a primitive-recursive finite probe set complete for its zero witnesses.
Thus a weak M₅(3) attack needs an arbitrary-word semantic invariant; no finite probe-rank
certificate follows from existential equivalence alone.
-/

namespace MatrixMortality

/-- Remove a prescribed run and separator from the beginning of a word. -/
def guardDecode {α : Type*} [DecidableEq α] (guard separator : α) :
    Nat → List α → Option (List α)
  | 0, head :: tail => if head = separator then some tail else none
  | 0, _ => none
  | n + 1, head :: tail => if head = guard then guardDecode guard separator n tail else none
  | _ + 1, _ => none

/-- Place one word behind a fixed guard run and separator. -/
def guardEncode {α : Type*} (guard separator : α)
    (guardLength : Nat) (word : List α) : List α :=
  List.replicate guardLength guard ++ separator :: word

@[simp] theorem guardDecode_guardEncode {α : Type*} [DecidableEq α]
    (guard separator : α) (guardLength : Nat) (word : List α) :
    guardDecode guard separator guardLength
      (guardEncode guard separator guardLength word) = some word := by
  induction guardLength with
  | zero => simp [guardDecode, guardEncode]
  | succ guardLength induction =>
      simp only [guardEncode, List.replicate_succ, List.cons_append, guardDecode]
      change guardDecode guard separator guardLength
        (guardEncode guard separator guardLength word) = some word
      exact induction

/-- Successful decoding certifies that the guarded word crosses the guard horizon. -/
theorem guardDecode_eq_some_length {α : Type*} [DecidableEq α]
    (guard separator : α) {guardLength : Nat} {word tail : List α}
    (decoded : guardDecode guard separator guardLength word = some tail) :
    guardLength + 1 ≤ word.length := by
  induction guardLength generalizing word with
  | zero =>
      cases word with
      | nil => simp [guardDecode] at decoded
      | cons head word => simp
  | succ guardLength induction =>
      cases word with
      | nil => simp [guardDecode] at decoded
      | cons head word =>
          simp only [guardDecode] at decoded
          split at decoded
          next head_guard =>
            have tail_length := induction decoded
            simp only [List.length_cons]
            omega
          next head_ne => simp at decoded

/-- Copy a series behind one guard and assign the nonzero value one to every other word. -/
def guardedSeries {α R : Type*} [DecidableEq α] [One R]
    (series : List α → R) (guard separator : α)
    (guardLength : Nat) (word : List α) : R :=
  match guardDecode guard separator guardLength word with
  | some tail => series tail
  | none => 1

@[simp] theorem guardedSeries_guardEncode {α R : Type*} [DecidableEq α] [One R]
    (series : List α → R) (guard separator : α)
    (guardLength : Nat) (word : List α) :
    guardedSeries series guard separator guardLength
      (guardEncode guard separator guardLength word) = series word := by
  simp [guardedSeries]

/-- Every word inside the chosen finite horizon receives coefficient one. -/
theorem guardedSeries_eq_one_of_length_le {α R : Type*} [DecidableEq α] [One R]
    (series : List α → R) (guard separator : α)
    (guardLength : Nat) (word : List α)
    (short : word.length ≤ guardLength) :
    guardedSeries series guard separator guardLength word = 1 := by
  unfold guardedSeries
  cases decoded : guardDecode guard separator guardLength word with
  | none => rfl
  | some tail =>
      have long := guardDecode_eq_some_length guard separator decoded
      omega

/-- Guarding preserves zero existence and makes every copied witness nonempty. -/
theorem guardedSeries_hasNonemptyZero_iff {α R : Type*} [DecidableEq α]
    [Semiring R] [Nontrivial R] (series : List α → R) (guard separator : α)
    (guardLength : Nat) :
    WordSeries.HasNonemptyZero (guardedSeries series guard separator guardLength) ↔
      WordSeries.HasZero series := by
  constructor
  · rintro ⟨word, _, series_zero⟩
    cases decoded : guardDecode guard separator guardLength word with
    | none => simp [guardedSeries, decoded] at series_zero
    | some tail =>
        refine ⟨tail, ?_⟩
        simpa [guardedSeries, decoded] using series_zero
  · rintro ⟨word, series_zero⟩
    refine ⟨guardEncode guard separator guardLength word, ?_, ?_⟩
    · simp [guardEncode]
    · simpa using series_zero

/-- Every finite Hankel section inside the guard horizon is the constant-one matrix. -/
theorem guardedSeries_finiteHankel_eq_one
    {α P S R : Type*} [DecidableEq α] [One R]
    (series : List α → R) (guard separator : α)
    (prefixes : P → List α) (suffixes : S → List α) (guardLength : Nat)
    (short : ∀ pidx sidx,
      (prefixes pidx ++ suffixes sidx).length ≤ guardLength) :
    finiteHankel (guardedSeries series guard separator guardLength) prefixes suffixes =
      fun _ _ => 1 := by
  ext pidx sidx
  exact guardedSeries_eq_one_of_length_le series guard separator guardLength _
    (short pidx sidx)

/-- Zero existence for the forced-rule derivative is exactly Neary terminal-match existence. -/
theorem forcedRuleC_hasZero_iff_terminal_match
    (β : Nat) (body : List TagLetter) (β_pos : 0 < β) :
    WordSeries.HasZero (forcedRuleCCoefficient ℚ β body) ↔
      ∃ word : List NearyTile,
        spell (nearyUpper β) word ++ nearyMarker β =
          spell (nearyLower β body) word := by
  constructor
  · rintro ⟨word, coefficient_zero⟩
    refine ⟨.rule .c :: decodePairedWord word, ?_⟩
    apply (sideCoefficient_eq_zero_iff_terminal_match_rat β body _).mp
    rw [← forcedRuleCCoefficient_eq_sideCoefficient]
    exact coefficient_zero
  · rintro ⟨word, terminal_match⟩
    obtain ⟨tail, word_eq⟩ :=
      terminalMatch_starts_rule_c β body β_pos word terminal_match
    subst word
    obtain ⟨controls, decoded⟩ := decodePairedWord_surjective tail
    refine ⟨controls, ?_⟩
    rw [forcedRuleCCoefficient_eq_sideCoefficient, decoded]
    exact (sideCoefficient_eq_zero_iff_terminal_match_rat β body _).mpr terminal_match

/-- An existence-equivalent changed series whose zeros begin beyond the MM-O18 probe horizon. -/
def existentialGuardedForcedRuleCCoefficient
    (β : Nat) (body : List TagLetter) : List PairedControl → ℚ :=
  guardedSeries (forcedRuleCCoefficient ℚ β body)
    .toggle (.data .b) 6

theorem existentialGuardedForcedRuleC_hasNonemptyZero_iff_terminal_match
    (β : Nat) (body : List TagLetter) (β_pos : 0 < β) :
    WordSeries.HasNonemptyZero (existentialGuardedForcedRuleCCoefficient β body) ↔
      ∃ word : List NearyTile,
        spell (nearyUpper β) word ++ nearyMarker β =
          spell (nearyLower β body) word := by
  rw [existentialGuardedForcedRuleCCoefficient,
    guardedSeries_hasNonemptyZero_iff,
    forcedRuleC_hasZero_iff_terminal_match β body β_pos]

/-- The complete inserted-toggle certificate from MM-O18 becomes the constant-one matrix after
the existence-preserving guard transform. -/
theorem existentialGuardedForcedRuleC_probeHankel_eq_one
    (β : Nat) (body : List TagLetter) :
    finiteHankel (existentialGuardedForcedRuleCCoefficient β body)
        forcedRuleCInsertedPrefixes forcedRuleCSuffixes =
      fun _ _ => 1 := by
  apply guardedSeries_finiteHankel_eq_one
  intro pidx sidx
  fin_cases pidx <;> fin_cases sidx <;>
    norm_num [forcedRuleCInsertedPrefixes, forcedRuleCPrefixes, forcedRuleCSuffixes]

/-- The guarded MM-O18 probe matrix is singular. -/
theorem existentialGuardedForcedRuleC_probeHankel_det
    (β : Nat) (body : List TagLetter) :
    (finiteHankel (existentialGuardedForcedRuleCCoefficient β body)
      forcedRuleCInsertedPrefixes forcedRuleCSuffixes).det = 0 := by
  rw [existentialGuardedForcedRuleC_probeHankel_eq_one]
  apply Matrix.det_zero_of_row_eq (i := 0) (j := 1) (by decide)
  rfl

namespace Undecidability.UniversalNeary

/-- A source is accepted when one probe below its source-computable cutoff succeeds. -/
def BoundedProbeZero (test : Nat.Partrec.Code → Nat → Prop)
    (bound : Nat.Partrec.Code → Nat) (index : Nat.Partrec.Code) : Prop :=
  ∃ probe < bound index, test index probe

/-- Primitive-recursive probes and cutoff make bounded probe acceptance computable. -/
theorem boundedProbeZero_computable
    (test : Nat.Partrec.Code → Nat → Prop)
    (bound : Nat.Partrec.Code → Nat)
    (test_primrec : PrimrecRel fun probe index => test index probe)
    (bound_primrec : Primrec bound) :
    ComputablePred (BoundedProbeZero test bound) := by
  have bounded_primrec : PrimrecPred fun index : Nat.Partrec.Code =>
      ∃ probe ∈ List.range (bound index), test index probe :=
    test_primrec.exists_mem_list.comp (Primrec.list_range.comp bound_primrec) Primrec.id
  exact (bounded_primrec.of_eq fun index => by
    simp [BoundedProbeZero]).computablePred

/-- No primitive-recursive finite probe search has the universal paired zero answers. -/
theorem no_boundedProbeZero_iff_universal
    (test : Nat.Partrec.Code → Nat → Prop)
    (bound : Nat.Partrec.Code → Nat)
    (test_primrec : PrimrecRel fun probe index => test index probe)
    (bound_primrec : Primrec bound)
    (same_zero : ∀ index,
      BoundedProbeZero test bound index ↔ universalPairedZero index) : False :=
  no_computable_sameZero_predicate (BoundedProbeZero test bound)
    (boundedProbeZero_computable test bound test_primrec bound_primrec) same_zero

end Undecidability.UniversalNeary

end MatrixMortality
