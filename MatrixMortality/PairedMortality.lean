import MatrixMortality.PairedCompression
import MatrixMortality.TerminalTile

/-!
# Mortality from paired-role scalar reachability

The compressed data matrices are singular, so the invertible-block converse used by the
three-dimensional mortality compiler does not apply.  Their common fixed column supplies the
needed exterior nonvanishing instead.  This file proves the arbitrary-product converse over
`ℚ`, then reflects it to the exact integer matrices.
-/

namespace MatrixMortality

open scoped Matrix

/-- The rank-one separator formed from the compressed boundary column and row. -/
def pairedSeparator (R : Type*) [CommRing R] (β : Nat) : Matrix (Fin 4) (Fin 4) R :=
  Matrix.vecMulVec (pairedColumn R β) (pairedRow R)

/-- Three compressed control matrices together with their rank-one separator. -/
def pairedMortalityFamily (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter) :
    Option PairedControl → Matrix (Fin 4) (Fin 4) R :=
  separatedGenerator (pairedSeparator R β) (pairedGenerator R β body)

theorem pairedRow_ne_zero (R : Type*) [CommRing R] [Nontrivial R] : pairedRow R ≠ 0 := by
  intro row_zero
  have entry := congr_fun row_zero 0
  simp [pairedRow] at entry

theorem pairedColumn_ne_zero (β : Nat) : pairedColumn ℚ β ≠ 0 := by
  intro column_zero
  have entry := congr_fun column_zero 0
  change phaseVector ℚ .rule (sideTerminalColumn ℚ (nearyMarker β)) 0 = 0 at entry
  rw [phaseHead] at entry
  have marker_zero : (ternaryCode (nearyMarker β) : ℚ) = 0 := by simpa using entry
  exact (ternaryCode_nearyMarker_ne_zero β) (by exact_mod_cast marker_zero)

/-- Every compressed control generator fixes the first standard column. -/
theorem pairedGenerator_mulVec_anchor (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (control : PairedControl) :
    pairedGenerator R β body control *ᵥ pairedAnchor R = pairedAnchor R := by
  cases control with
  | toggle =>
      have routed :=
        pairedToggleMatrix_mulVec_phaseVector R .rule (![1, 0, 0] : Fin 3 → R)
      rw [phaseVector_basis_zero, phaseVector_basis_zero] at routed
      simpa [pairedGenerator, pairedAnchor] using routed
  | data letter =>
      simpa [pairedGenerator, pairedDataMatrix, pairedAnchor, twoStateAnchor] using
        twoStateDataMatrix_mulVec_anchor R
          (fun symbol => nearyUpper β (.rule symbol))
          (fun phase symbol => nearyLower β body (phase.tile symbol))
          (fun _ _ => PairPhase.erase)
          letter

theorem pairedCoefficient_eq_bridgeScalar (R : Type*) [Field R] (β : Nat)
    (body : List TagLetter) (word : List PairedControl) :
    pairedCoefficient R β body word =
      bridgeScalar (pairedColumn R β) (pairedRow R)
        (wordProduct (pairedGenerator R β body) word) := by
  rw [pairedCoefficient, bridgeScalar]
  rfl

theorem pairedCoefficient_nil_ne_zero (β : Nat) (body : List TagLetter) :
    pairedCoefficient ℚ β body [] ≠ 0 := by
  rw [pairedCoefficient_nil]
  exact_mod_cast ternaryCode_nearyMarker_ne_zero β

theorem paired_zero_rat_iff_terminal_match (β : Nat) (body : List TagLetter) :
    WordSeries.HasNonemptyZero (pairedCoefficient ℚ β body) ↔
      ∃ word : List NearyTile,
        spell (nearyUpper β) word ++ nearyMarker β = spell (nearyLower β body) word := by
  constructor
  · rintro ⟨control, _, coefficient_zero⟩
    refine ⟨decodePairedWord control, ?_⟩
    exact (sideCoefficient_eq_zero_iff_terminal_match_rat β body _).mp
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
    exact (sideCoefficient_eq_zero_iff_terminal_match_rat β body word).mpr terminal_match

theorem pairedMortalityFamily_rat_mortal_iff_paired_zero (β : Nat)
    (body : List TagLetter) :
    IsMortal (pairedMortalityFamily ℚ β body) ↔
      WordSeries.HasNonemptyZero (pairedCoefficient ℚ β body) := by
  let X := pairedGenerator ℚ β body
  have fixed : ∀ control, X control *ᵥ pairedAnchor ℚ = pairedAnchor ℚ :=
    pairedGenerator_mulVec_anchor ℚ β body
  have anchor_pair : pairedRow ℚ ⬝ᵥ pairedAnchor ℚ ≠ 0 := by
    simp [pairedRow, pairedAnchor]
  rw [show pairedMortalityFamily ℚ β body =
      separatedGenerator
        (Matrix.vecMulVec (pairedColumn ℚ β) (pairedRow ℚ)) X by
        rfl]
  rw [fixedAnchor_mortal_adjoin_outer_iff X (pairedAnchor ℚ)
    (pairedColumn ℚ β) (pairedRow ℚ) fixed anchor_pair]
  constructor
  · rintro ⟨word, bridge_zero⟩
    have coefficient_zero : pairedCoefficient ℚ β body word = 0 := by
      simpa [pairedCoefficient_eq_bridgeScalar, X] using bridge_zero
    have word_nonempty : word ≠ [] := by
      intro word_empty
      subst word
      exact pairedCoefficient_nil_ne_zero β body coefficient_zero
    exact ⟨word, word_nonempty, coefficient_zero⟩
  · rintro ⟨word, _, coefficient_zero⟩
    exact ⟨word, by simpa [pairedCoefficient_eq_bridgeScalar, X] using coefficient_zero⟩

theorem pairedMortalityFamily_rat_mortal_iff_terminal_match (β : Nat)
    (body : List TagLetter) :
    IsMortal (pairedMortalityFamily ℚ β body) ↔
      ∃ word : List NearyTile,
        spell (nearyUpper β) word ++ nearyMarker β = spell (nearyLower β body) word := by
  rw [pairedMortalityFamily_rat_mortal_iff_paired_zero,
    paired_zero_rat_iff_terminal_match]

/-! ## Exact integer family -/

theorem pairedSeparator_map {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (β : Nat) :
    (pairedSeparator R β).map hom = pairedSeparator S β := by
  rw [pairedSeparator, vecMulVec_map, pairedColumn_map, pairedRow_map]
  rfl

theorem pairedMortalityFamily_map {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (β : Nat) (body : List TagLetter) (label : Option PairedControl) :
    (pairedMortalityFamily R β body label).map hom =
      pairedMortalityFamily S β body label := by
  cases label with
  | none => exact pairedSeparator_map hom β
  | some control => exact pairedGenerator_map hom β body control

theorem pairedMortalityFamily_int_mortal_iff_rat (β : Nat) (body : List TagLetter) :
    IsMortal (pairedMortalityFamily ℤ β body) ↔
      IsMortal (pairedMortalityFamily ℚ β body) := by
  have family_cast :
      castMatrix ∘ pairedMortalityFamily ℤ β body = pairedMortalityFamily ℚ β body := by
    funext label
    exact pairedMortalityFamily_map (Int.castRingHom ℚ) β body label
  rw [← family_cast]
  exact (isMortal_cast_iff (pairedMortalityFamily ℤ β body)).symm

theorem pairedMortalityFamily_int_mortal_iff_terminal_match (β : Nat)
    (body : List TagLetter) :
    IsMortal (pairedMortalityFamily ℤ β body) ↔
      ∃ word : List NearyTile,
        spell (nearyUpper β) word ++ nearyMarker β = spell (nearyLower β body) word := by
  rw [pairedMortalityFamily_int_mortal_iff_rat,
    pairedMortalityFamily_rat_mortal_iff_terminal_match]

theorem pairedMortalityFamily_int_mortal_iff_tagHaltsFrom (β : Nat)
    (body : List TagLetter) (β_large : 2 < β) (body_long : β - 1 ≤ body.length)
    (body_divisible : β - 1 ∣ body.length) :
    IsMortal (pairedMortalityFamily ℤ β body) ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  rw [pairedMortalityFamily_int_mortal_iff_terminal_match]
  exact terminal_match_iff_tagHaltsFrom β body β_large body_long body_divisible

theorem pairedColumn_int_ne_zero (β : Nat) : pairedColumn ℤ β ≠ 0 := by
  intro column_zero
  apply pairedColumn_ne_zero β
  rw [← pairedColumn_map (Int.castRingHom ℚ), column_zero]
  rfl

theorem pairedSeparator_int_ne_zero (β : Nat) : pairedSeparator ℤ β ≠ 0 := by
  have rational_nonzero : pairedSeparator ℚ β ≠ 0 := by
    unfold pairedSeparator
    exact outer_ne_zero (pairedColumn_ne_zero β) (pairedRow_ne_zero ℚ)
  intro separator_zero
  apply rational_nonzero
  rw [← pairedSeparator_map (Int.castRingHom ℚ), separator_zero]
  simp [castMatrix]

theorem castMatrix_pairedSeparator_rank_eq_one (β : Nat) :
    (castMatrix (pairedSeparator ℤ β)).toLin'.rank = 1 := by
  change (Matrix.toLin' ((pairedSeparator ℤ β).map (Int.castRingHom ℚ))).rank = 1
  rw [pairedSeparator_map (Int.castRingHom ℚ)]
  apply le_antisymm (Matrix.rank_vecMulVec _ _)
  rw [Cardinal.one_le_iff_ne_zero]
  intro rank_zero
  have range_bot : LinearMap.range (Matrix.toLin' (pairedSeparator ℚ β)) = ⊥ := by
    letI : Subsingleton (LinearMap.range (Matrix.toLin' (pairedSeparator ℚ β))) :=
      rank_zero_iff.mp rank_zero
    exact Submodule.eq_bot_of_subsingleton
  have linear_zero : Matrix.toLin' (pairedSeparator ℚ β) = 0 :=
    LinearMap.range_eq_bot.mp range_bot
  have separator_zero : pairedSeparator ℚ β = 0 := by
    apply Matrix.toLin'.injective
    simpa using linear_zero
  exact (by
    unfold pairedSeparator at separator_zero
    exact outer_ne_zero (pairedColumn_ne_zero β) (pairedRow_ne_zero ℚ) separator_zero)

/-- The compressed family has exactly four semantic labels. -/
theorem paired_mortality_generator_count : Fintype.card (Option PairedControl) = 4 := by decide

end MatrixMortality
