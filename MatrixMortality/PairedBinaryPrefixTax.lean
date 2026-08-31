import MatrixMortality.PairedMortality

/-!
# Trailing-toggle boundary and variable-fibre prefix tax

Appending two paired toggles changes neither the control product nor its scalar coefficient.
One toggle may therefore be absorbed into the right boundary without changing existential zero
reachability.  In that boundary, the private rule coordinate vanishes, placing the separator
column in the same three-dimensional plane as both data images.

This saves one state in the exact paired-source binary comb, but cannot save two.  The rank of a
leaf product bounds every intermediate fibre on its prefix path.  A four-dimensional short leaf
and a rank-three leaf at depth three therefore cost at least `4 + 3 + 3 = 10` states.
-/

namespace MatrixMortality

open scoped Matrix

/-- The paired phase toggle is an involution. -/
theorem pairedToggleMatrix_mul_self (R : Type*) [CommRing R] :
    pairedToggleMatrix R * pairedToggleMatrix R = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [pairedToggleMatrix_eq_explicit, Matrix.mul_apply,
      Fin.sum_univ_succ]

/-- The paired phase toggle has full rank over the rationals. -/
theorem pairedToggleMatrix_rank_eq_four :
    (pairedToggleMatrix ℚ).rank = 4 := by
  have toggle_is_unit : IsUnit (pairedToggleMatrix ℚ) :=
    isUnit_iff_exists.mpr
      ⟨pairedToggleMatrix ℚ, pairedToggleMatrix_mul_self ℚ,
        pairedToggleMatrix_mul_self ℚ⟩
  simpa using Matrix.rank_of_isUnit (pairedToggleMatrix ℚ) toggle_is_unit

/-- Each paired data generator has rank three over the rationals. -/
theorem pairedDataMatrix_rank_eq_three (β : Nat) (body : List TagLetter)
    (letter : TagLetter) :
    (pairedDataMatrix ℚ β body letter).rank = 3 := by
  exact twoStateDataMatrix_rank_eq_three_of_eq
    (fun symbol => nearyUpper β (.rule symbol))
    (fun phase symbol => nearyLower β body (phase.tile symbol))
    (fun _ _ => .erase) letter rfl

/-- Every paired data image has zero private rule coordinate. -/
theorem pairedDataMatrix_mulVec_one (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (letter : TagLetter) (column : Fin 4 → R) :
    (pairedDataMatrix R β body letter *ᵥ column) 1 = 0 := by
  rw [pairedDataMatrix_eq_explicit]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The right boundary obtained by absorbing one trailing phase toggle. -/
def pairedTrailingToggleColumn (R : Type*) [CommRing R] (β : Nat) : Fin 4 → R :=
  pairedToggleMatrix R *ᵥ pairedColumn R β

/-- The absorbed boundary has no private rule coordinate. -/
theorem pairedTrailingToggleColumn_one (R : Type*) [CommRing R] (β : Nat) :
    pairedTrailingToggleColumn R β 1 = 0 := by
  simp [pairedTrailingToggleColumn, pairedToggleMatrix_eq_explicit, pairedColumn,
    phaseVector, controllerVector, pairControllerEquiv, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]

/-- Rank-one punctuation formed from the absorbed right boundary. -/
def pairedTrailingToggleSeparator (R : Type*) [CommRing R] (β : Nat) :
    Matrix (Fin 4) (Fin 4) R :=
  Matrix.vecMulVec (pairedTrailingToggleColumn R β) (pairedRow R)

/-- The absorbed separator image has zero private rule coordinate. -/
theorem pairedTrailingToggleSeparator_one (R : Type*) [CommRing R] (β : Nat)
    (column : Fin 4) :
    pairedTrailingToggleSeparator R β 1 column = 0 := by
  simp [pairedTrailingToggleSeparator, Matrix.vecMulVec,
    pairedTrailingToggleColumn_one]

/-- Scalar series obtained by moving one trailing toggle into the right boundary. -/
def pairedTrailingToggleCoefficient (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (word : List PairedControl) : R :=
  pairedRow R ⬝ᵥ
    pairedProduct R β body word *ᵥ pairedTrailingToggleColumn R β

/-- Boundary absorption is exactly right-appending one toggle to the control word. -/
theorem pairedTrailingToggleCoefficient_eq_append (R : Type*) [CommRing R]
    (β : Nat) (body : List TagLetter) (word : List PairedControl) :
    pairedTrailingToggleCoefficient R β body word =
      pairedCoefficient R β body (word ++ [.toggle]) := by
  rw [pairedTrailingToggleCoefficient, pairedTrailingToggleColumn,
    pairedCoefficient, pairedProduct, pairedProduct, wordProduct_append]
  simp only [wordProduct_cons, wordProduct_nil, mul_one, pairedGenerator]
  rw [Matrix.mulVec_mulVec]

/-- Appending two toggles leaves the complete paired control product unchanged. -/
theorem pairedProduct_append_toggle_toggle (R : Type*) [CommRing R]
    (β : Nat) (body : List TagLetter) (word : List PairedControl) :
    pairedProduct R β body (word ++ [.toggle, .toggle]) =
      pairedProduct R β body word := by
  simp only [pairedProduct, wordProduct_append]
  simp only [wordProduct_cons, wordProduct_nil, mul_one, pairedGenerator]
  rw [pairedToggleMatrix_mul_self, mul_one]

/-- Appending two toggles leaves the paired scalar coefficient unchanged. -/
theorem pairedCoefficient_append_toggle_toggle (R : Type*) [CommRing R]
    (β : Nat) (body : List TagLetter) (word : List PairedControl) :
    pairedCoefficient R β body (word ++ [.toggle, .toggle]) =
      pairedCoefficient R β body word := by
  simp only [pairedCoefficient]
  rw [pairedProduct_append_toggle_toggle]

/-- Absorbing a trailing toggle preserves existential nonempty zero reachability exactly. -/
theorem pairedTrailingToggle_hasNonemptyZero_iff (R : Type*) [CommRing R]
    (β : Nat) (body : List TagLetter) :
    WordSeries.HasNonemptyZero (pairedTrailingToggleCoefficient R β body) ↔
      WordSeries.HasNonemptyZero (pairedCoefficient R β body) := by
  constructor
  · rintro ⟨word, _, coefficient_zero⟩
    refine ⟨word ++ [.toggle], by simp, ?_⟩
    rw [← pairedTrailingToggleCoefficient_eq_append]
    exact coefficient_zero
  · rintro ⟨word, _, coefficient_zero⟩
    refine ⟨word ++ [.toggle], by simp, ?_⟩
    rw [pairedTrailingToggleCoefficient_eq_append]
    have concatenation : word ++ [.toggle] ++ [.toggle] =
        word ++ [.toggle, .toggle] := by
      simp
    rw [concatenation, pairedCoefficient_append_toggle_toggle]
    exact coefficient_zero

namespace VariablePrefixRankTax

/-- A leaf's matrix rank taxes every intermediate fibre on its factorization path. -/
theorem shortLeaf_add_two_mul_deepLeaf_le
    {Root Middle Deep : Type*}
    [Fintype Root] [Fintype Middle] [Fintype Deep]
    (shortLeaf : Matrix Root Root ℚ)
    (firstEdge : Matrix Root Middle ℚ)
    (secondEdge : Matrix Middle Deep ℚ)
    (lastEdge : Matrix Deep Root ℚ)
    (shortRank deepRank : Nat)
    (short_rank : shortLeaf.rank = shortRank)
    (deep_rank : (firstEdge * secondEdge * lastEdge).rank = deepRank) :
    shortRank + 2 * deepRank ≤
      Fintype.card Root + Fintype.card Middle + Fintype.card Deep := by
  have root_bound : shortRank ≤ Fintype.card Root := by
    calc
      shortRank = shortLeaf.rank := short_rank.symm
      _ ≤ Fintype.card Root := Matrix.rank_le_card_height shortLeaf
  have middle_bound : deepRank ≤ Fintype.card Middle := by
    calc
      deepRank = (firstEdge * secondEdge * lastEdge).rank := deep_rank.symm
      _ = (firstEdge * (secondEdge * lastEdge)).rank := by rw [Matrix.mul_assoc]
      _ ≤ firstEdge.rank := Matrix.rank_mul_le_left firstEdge (secondEdge * lastEdge)
      _ ≤ Fintype.card Middle := Matrix.rank_le_card_width firstEdge
  have deep_bound : deepRank ≤ Fintype.card Deep := by
    calc
      deepRank = (firstEdge * secondEdge * lastEdge).rank := deep_rank.symm
      _ = (firstEdge * (secondEdge * lastEdge)).rank := by rw [Matrix.mul_assoc]
      _ ≤ (secondEdge * lastEdge).rank :=
        Matrix.rank_mul_le_right firstEdge (secondEdge * lastEdge)
      _ ≤ secondEdge.rank := Matrix.rank_mul_le_left secondEdge lastEdge
      _ ≤ Fintype.card Deep := Matrix.rank_le_card_width secondEdge
  omega

/-- A full-rank four-state short leaf and a rank-three depth-three leaf need ten states. -/
theorem ten_le_of_rank_four_short_rank_three_deep
    {Root Middle Deep : Type*}
    [Fintype Root] [Fintype Middle] [Fintype Deep]
    (shortLeaf : Matrix Root Root ℚ)
    (firstEdge : Matrix Root Middle ℚ)
    (secondEdge : Matrix Middle Deep ℚ)
    (lastEdge : Matrix Deep Root ℚ)
    (short_rank : shortLeaf.rank = 4)
    (deep_rank : (firstEdge * secondEdge * lastEdge).rank = 3) :
    10 ≤ Fintype.card Root + Fintype.card Middle + Fintype.card Deep := by
  have tax := shortLeaf_add_two_mul_deepLeaf_le shortLeaf firstEdge secondEdge lastEdge
    4 3 short_rank deep_rank
  omega

/-- In a balanced tree, rank-four and rank-three leaves on opposite branches need eleven states. -/
theorem eleven_le_balanced_rank_four_rank_three
    {Root FullBranch ThreeBranch : Type*}
    [Fintype Root] [Fintype FullBranch] [Fintype ThreeBranch]
    (fullFirst : Matrix Root FullBranch ℚ)
    (fullLast : Matrix FullBranch Root ℚ)
    (threeFirst : Matrix Root ThreeBranch ℚ)
    (threeLast : Matrix ThreeBranch Root ℚ)
    (full_rank : (fullFirst * fullLast).rank = 4)
    (three_rank : (threeFirst * threeLast).rank = 3) :
    11 ≤ Fintype.card Root + Fintype.card FullBranch + Fintype.card ThreeBranch := by
  have root_bound : 4 ≤ Fintype.card Root := by
    calc
      4 = (fullFirst * fullLast).rank := full_rank.symm
      _ ≤ Fintype.card Root := Matrix.rank_le_card_height (fullFirst * fullLast)
  have full_bound : 4 ≤ Fintype.card FullBranch := by
    calc
      4 = (fullFirst * fullLast).rank := full_rank.symm
      _ ≤ fullFirst.rank := Matrix.rank_mul_le_left fullFirst fullLast
      _ ≤ Fintype.card FullBranch := Matrix.rank_le_card_width fullFirst
  have three_bound : 3 ≤ Fintype.card ThreeBranch := by
    calc
      3 = (threeFirst * threeLast).rank := three_rank.symm
      _ ≤ threeFirst.rank := Matrix.rank_mul_le_left threeFirst threeLast
      _ ≤ Fintype.card ThreeBranch := Matrix.rank_le_card_width threeFirst
  omega

end VariablePrefixRankTax

end MatrixMortality
