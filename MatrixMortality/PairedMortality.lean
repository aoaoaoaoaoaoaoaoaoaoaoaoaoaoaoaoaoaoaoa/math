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
  have entry := congr_fun column_zero 2
  simp [pairedColumn, phaseVector, sideTerminalColumn, sidePcpMatrix, sideTailBasis,
    nearyMarker, Matrix.vecHead, Matrix.vecTail, Matrix.mulVec, Matrix.dotProduct,
    Fin.sum_univ_succ] at entry

/-- Every compressed control generator fixes the first standard column. -/
theorem pairedGenerator_mulVec_anchor (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (control : PairedControl) :
    pairedGenerator R β body control *ᵥ pairedAnchor R = pairedAnchor R := by
  cases control with
  | toggle =>
      funext i
      fin_cases i <;>
        simp [pairedGenerator, pairedToggleMatrix, pairedAnchor, Matrix.vecHead, Matrix.vecTail,
          Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]
  | data letter =>
      funext i
      fin_cases i <;>
        simp [pairedGenerator, pairedDataMatrix, pairedAnchor, Matrix.vecHead, Matrix.vecTail,
          Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]

theorem pairedProduct_mulVec_anchor (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (word : List PairedControl) :
    pairedProduct R β body word *ᵥ pairedAnchor R = pairedAnchor R := by
  induction word with
  | nil => simp [pairedProduct]
  | cons control word ih =>
      simp only [pairedProduct, List.map_cons, List.prod_cons]
      rw [← Matrix.mulVec_mulVec]
      change pairedGenerator R β body control *ᵥ
        (pairedProduct R β body word *ᵥ pairedAnchor R) = _
      rw [ih, pairedGenerator_mulVec_anchor]

theorem pairedProduct_ne_zero (R : Type*) [CommRing R] [Nontrivial R] (β : Nat)
    (body : List TagLetter) (word : List PairedControl) : pairedProduct R β body word ≠ 0 := by
  intro product_zero
  have fixed := pairedProduct_mulVec_anchor R β body word
  rw [product_zero] at fixed
  have anchor_nonzero : pairedAnchor R ≠ 0 := by
    intro anchor_zero
    have entry := congr_fun anchor_zero 0
    simp [pairedAnchor] at entry
  exact anchor_nonzero (by simpa using fixed.symm)

theorem pairedProduct_zero_zero (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (word : List PairedControl) :
    pairedProduct R β body word 0 0 = 1 := by
  have fixed := congr_fun (pairedProduct_mulVec_anchor R β body word) 0
  simpa [pairedAnchor, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ] using fixed

theorem pairedRow_vecMul_pairedProduct_ne_zero (R : Type*) [CommRing R] [Nontrivial R]
    (β : Nat) (body : List TagLetter) (word : List PairedControl) :
    pairedRow R ᵥ* pairedProduct R β body word ≠ 0 := by
  intro row_zero
  have entry := congr_fun row_zero 0
  have diagonal := pairedProduct_zero_zero R β body word
  simp [pairedRow, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_succ, diagonal] at entry

theorem generatorProduct_mulVec_anchor_of_no_separator (β : Nat)
    (body : List TagLetter) (word : List (Option PairedControl)) (no_separator : none ∉ word) :
    generatorProduct (pairedSeparator ℚ β) (pairedGenerator ℚ β body) word *ᵥ pairedAnchor ℚ =
      pairedAnchor ℚ := by
  induction word with
  | nil => simp [generatorProduct]
  | cons control word ih =>
      cases control with
      | none => exact (no_separator (by simp)).elim
      | some control =>
          have tail_no_separator : none ∉ word := by
            intro member
            exact no_separator (by simp [member])
          simp only [generatorProduct, separatedGenerator, List.map_cons, List.prod_cons]
          rw [← Matrix.mulVec_mulVec]
          change pairedGenerator ℚ β body control *ᵥ
            (generatorProduct (pairedSeparator ℚ β) (pairedGenerator ℚ β body) word *ᵥ
              pairedAnchor ℚ) = _
          rw [ih tail_no_separator, pairedGenerator_mulVec_anchor]

theorem pairedCoefficient_eq_bridgeScalar (R : Type*) [Field R] (β : Nat)
    (body : List TagLetter) (word : List PairedControl) :
    pairedCoefficient R β body word =
      bridgeScalar (pairedColumn R β) (pairedRow R)
        (blockProduct (pairedGenerator R β body) word) := by
  rw [pairedCoefficient, bridgeScalar]
  rfl

theorem pairedCoefficient_nil_ne_zero (β : Nat) (body : List TagLetter) :
    pairedCoefficient ℚ β body [] ≠ 0 := by
  intro coefficient_zero
  rw [pairedCoefficient_nil] at coefficient_zero
  have code_zero : ternaryCode (nearyMarker β) = 0 := by
    exact_mod_cast coefficient_zero
  have marker_empty : nearyMarker β = [] := by
    apply ternaryCode_injective
    simpa using code_zero
  simp [nearyMarker] at marker_empty

/-- Rational nonempty scalar zero reachability for the compressed controls. -/
def HasPairedZeroRat (β : Nat) (body : List TagLetter) : Prop :=
  ∃ word : List PairedControl, word ≠ [] ∧ pairedCoefficient ℚ β body word = 0

theorem paired_zero_rat_iff_terminal_match (β : Nat) (body : List TagLetter) :
    HasPairedZeroRat β body ↔
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
    IsMortal (pairedMortalityFamily ℚ β body) ↔ HasPairedZeroRat β body := by
  let c := pairedColumn ℚ β
  let r := pairedRow ℚ
  let A := pairedSeparator ℚ β
  let X := pairedGenerator ℚ β body
  have column_nonzero : c ≠ 0 := pairedColumn_ne_zero β
  constructor
  · rintro ⟨raw, _, product_zero⟩
    have chain_zero : generatorProduct A X raw = 0 := by
      simpa [pairedMortalityFamily, generatorProduct, A, X] using product_zero
    have separator_mem : none ∈ raw := by
      by_contra no_separator
      have fixed := generatorProduct_mulVec_anchor_of_no_separator β body raw no_separator
      rw [show generatorProduct (pairedSeparator ℚ β) (pairedGenerator ℚ β body) raw = 0 by
        simpa [A, X] using chain_zero] at fixed
      have anchor_nonzero : pairedAnchor ℚ ≠ 0 := by
        intro anchor_zero
        have entry := congr_fun anchor_zero 0
        simp [pairedAnchor] at entry
      exact anchor_nonzero (by simpa using fixed.symm)
    rw [generatorProduct_eq_rankOneChain] at chain_zero
    have fracture_length := fracture_length_two_le_of_none_mem separator_mem
    have fracture_nonempty := fracture_ne_nil raw
    rcases List.exists_cons_of_ne_nil fracture_nonempty with ⟨first, rest, fracture_eq⟩
    have rest_nonempty : rest ≠ [] := by
      intro rest_empty
      rw [fracture_eq, rest_empty] at fracture_length
      simp at fracture_length
    let last := rest.getLast rest_nonempty
    let middle := rest.dropLast
    have fracture_decomposition : fracture raw = first :: middle ++ [last] := by
      rw [fracture_eq]
      congr 1
      exact (List.dropLast_append_getLast rest_nonempty).symm
    have mapped_decomposition : (fracture raw).map (blockProduct X) =
        blockProduct X first :: middle.map (blockProduct X) ++ [blockProduct X last] := by
      simp [fracture_decomposition]
    rw [mapped_decomposition] at chain_zero
    change rankOneChain (Matrix.vecMulVec c r)
      (blockProduct X first :: middle.map (blockProduct X) ++ [blockProduct X last]) = 0
      at chain_zero
    rw [rankOneChain_formula] at chain_zero
    by_cases first_column_zero : blockProduct X first *ᵥ c = 0
    · have first_nonempty : first ≠ [] := by
        intro first_empty
        subst first
        simp [blockProduct, column_nonzero] at first_column_zero
      refine ⟨first, first_nonempty, ?_⟩
      rw [pairedCoefficient_eq_bridgeScalar, bridgeScalar]
      simp [c, r, X, first_column_zero]
    · have last_row_nonzero : r ᵥ* blockProduct X last ≠ 0 := by
        simpa [r, X, blockProduct, pairedProduct] using
          pairedRow_vecMul_pairedProduct_ne_zero ℚ β body last
      have boundary_nonzero :
          Matrix.vecMulVec (blockProduct X first *ᵥ c) (r ᵥ* blockProduct X last) ≠ 0 :=
        outer_ne_zero first_column_zero last_row_nonzero
      have scalar_product_zero :
          ((middle.map (blockProduct X)).map (bridgeScalar c r)).prod = 0 := by
        exact (smul_eq_zero.mp chain_zero).resolve_right boundary_nonzero
      have zero_mem :
          0 ∈ (middle.map (blockProduct X)).map (bridgeScalar c r) :=
        List.prod_eq_zero_iff.mp scalar_product_zero
      obtain ⟨matrix, matrix_mem, bridge_zero⟩ := List.mem_map.mp zero_mem
      obtain ⟨word, _, word_matrix⟩ := List.mem_map.mp matrix_mem
      subst matrix
      have word_nonempty : word ≠ [] := by
        intro word_empty
        subst word
        exact pairedCoefficient_nil_ne_zero β body
          (by simpa [pairedCoefficient_eq_bridgeScalar, c, r, X])
      refine ⟨word, word_nonempty, ?_⟩
      simpa [pairedCoefficient_eq_bridgeScalar, c, r, X] using bridge_zero
  · rintro ⟨word, _, coefficient_zero⟩
    refine ⟨none :: word.map some ++ [none], by simp, ?_⟩
    have fracture_shape : fracture (none :: word.map some ++ [none]) = [[], word, []] := by
      simp [fracture, fracture_map_some_append_none]
    change generatorProduct A X (none :: word.map some ++ [none]) = 0
    rw [generatorProduct_eq_rankOneChain, fracture_shape]
    have bridge_zero : bridgeScalar c r (blockProduct X word) = 0 := by
      simpa [pairedCoefficient_eq_bridgeScalar, c, r, X] using coefficient_zero
    rw [show ([[], word, []] : List (List PairedControl)).map (blockProduct X) =
      [1, blockProduct X word, 1] by simp [blockProduct]]
    rw [show rankOneChain A [1, blockProduct X word, 1] =
      bridgeScalar c r (blockProduct X word) • Matrix.vecMulVec c r by
        simpa [A] using rankOneChain_formula c r 1 1 [blockProduct X word]]
    simp [bridge_zero]

theorem pairedMortalityFamily_rat_mortal_iff_terminal_match (β : Nat)
    (body : List TagLetter) :
    IsMortal (pairedMortalityFamily ℚ β body) ↔
      ∃ word : List NearyTile,
        spell (nearyUpper β) word ++ nearyMarker β = spell (nearyLower β body) word := by
  rw [pairedMortalityFamily_rat_mortal_iff_paired_zero,
    paired_zero_rat_iff_terminal_match]

/-! ## Exact integer family -/

/-- Entrywise inclusion of a `4 × 4` integer matrix into the rationals. -/
def castMatrix4 (matrix : Matrix (Fin 4) (Fin 4) ℤ) : Matrix (Fin 4) (Fin 4) ℚ :=
  matrix.map (Int.castRingHom ℚ)

/-- Entrywise inclusion of a four-dimensional integer vector into the rationals. -/
def castVector4 (vector : Fin 4 → ℤ) : Fin 4 → ℚ := fun i => vector i

theorem castMatrix4_mul (left right : Matrix (Fin 4) (Fin 4) ℤ) :
    castMatrix4 (left * right) = castMatrix4 left * castMatrix4 right := by
  ext i j
  simp [castMatrix4, Matrix.mul_apply]

theorem castMatrix4_eq_zero_iff (matrix : Matrix (Fin 4) (Fin 4) ℤ) :
    castMatrix4 matrix = 0 ↔ matrix = 0 := by
  constructor
  · intro cast_zero
    ext i j
    have entry := congr_fun (congr_fun cast_zero i) j
    simpa [castMatrix4] using entry
  · rintro rfl
    simp [castMatrix4]

theorem castVector4_pairedRow : castVector4 (pairedRow ℤ) = pairedRow ℚ := by
  funext i
  fin_cases i <;> simp [castVector4, pairedRow]

theorem castVector4_pairedColumn (β : Nat) :
    castVector4 (pairedColumn ℤ β) = pairedColumn ℚ β := by
  funext i
  fin_cases i <;>
    simp [castVector4, pairedColumn, phaseVector, sideTerminalColumn, sidePcpMatrix,
      sideTailBasis, nearyMarker, Matrix.vecHead, Matrix.vecTail, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_succ]

theorem castMatrix4_vecMulVec (column row : Fin 4 → ℤ) :
    castMatrix4 (Matrix.vecMulVec column row) =
      Matrix.vecMulVec (castVector4 column) (castVector4 row) := by
  ext i j
  simp [castMatrix4, castVector4, Matrix.vecMulVec]

theorem castMatrix4_pairedGenerator (β : Nat) (body : List TagLetter)
    (control : PairedControl) :
    castMatrix4 (pairedGenerator ℤ β body control) = pairedGenerator ℚ β body control := by
  cases control with
  | toggle =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [castMatrix4, pairedGenerator, pairedToggleMatrix, Matrix.vecHead, Matrix.vecTail]
  | data letter =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [castMatrix4, pairedGenerator, pairedDataMatrix, Matrix.vecHead, Matrix.vecTail]

theorem castMatrix4_pairedSeparator (β : Nat) :
    castMatrix4 (pairedSeparator ℤ β) = pairedSeparator ℚ β := by
  rw [pairedSeparator, castMatrix4_vecMulVec, castVector4_pairedColumn,
    castVector4_pairedRow]
  rfl

theorem castMatrix4_pairedMortalityFamily (β : Nat) (body : List TagLetter)
    (label : Option PairedControl) :
    castMatrix4 (pairedMortalityFamily ℤ β body label) =
      pairedMortalityFamily ℚ β body label := by
  cases label with
  | none => exact castMatrix4_pairedSeparator β
  | some control => exact castMatrix4_pairedGenerator β body control

theorem castMatrix4_pairedMortalityProduct (β : Nat) (body : List TagLetter)
    (word : List (Option PairedControl)) :
    castMatrix4 ((word.map (pairedMortalityFamily ℤ β body)).prod) =
      (word.map (pairedMortalityFamily ℚ β body)).prod := by
  induction word with
  | nil =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp [castMatrix4]
  | cons label word ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [castMatrix4_mul, castMatrix4_pairedMortalityFamily, ih]

theorem pairedMortalityFamily_int_mortal_iff_rat (β : Nat) (body : List TagLetter) :
    IsMortal (pairedMortalityFamily ℤ β body) ↔
      IsMortal (pairedMortalityFamily ℚ β body) := by
  constructor
  · rintro ⟨word, word_nonempty, product_zero⟩
    refine ⟨word, word_nonempty, ?_⟩
    rw [← castMatrix4_pairedMortalityProduct]
    exact (castMatrix4_eq_zero_iff _).mpr product_zero
  · rintro ⟨word, word_nonempty, product_zero⟩
    refine ⟨word, word_nonempty, ?_⟩
    apply (castMatrix4_eq_zero_iff _).mp
    rw [castMatrix4_pairedMortalityProduct]
    exact product_zero

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
  rw [← castVector4_pairedColumn, column_zero]
  rfl

theorem pairedSeparator_int_ne_zero (β : Nat) : pairedSeparator ℤ β ≠ 0 := by
  have rational_nonzero : pairedSeparator ℚ β ≠ 0 := by
    unfold pairedSeparator
    exact outer_ne_zero (pairedColumn_ne_zero β) (pairedRow_ne_zero ℚ)
  intro separator_zero
  apply rational_nonzero
  rw [← castMatrix4_pairedSeparator, separator_zero]
  simp [castMatrix4]

theorem castMatrix4_pairedSeparator_rank_eq_one (β : Nat) :
    (castMatrix4 (pairedSeparator ℤ β)).toLin'.rank = 1 := by
  rw [castMatrix4_pairedSeparator]
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
