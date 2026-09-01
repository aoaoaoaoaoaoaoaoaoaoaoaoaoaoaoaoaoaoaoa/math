import MatrixMortality.DecimalSetterCarry
import MatrixMortality.MatrixSemigroup
import MatrixMortality.NearyEncoding
import MatrixMortality.RankOne
import MatrixMortality.SetterShear
import Mathlib.Tactic

/-!
# The explicit decimal five-state setter

This module reconstructs the three rational `5 × 5` matrices underlying the decimal setter.
The data matrices are the radix-ten side correspondence representation in a boundary-adapted
basis.  The delimiter records whether the data letter immediately to its left is read as a rule
or an erasure, stabilizes at a rank-one cube, and forms the internal separator
`S² A_c S³`.
-/

namespace MatrixMortality.DecimalSetterMatrix

open scoped Matrix

open MatrixMortality.DecimalSetterCarry

/-- Radix-ten side-normal matrix for one upper/lower word pair. -/
def sideMatrix (upper lower : List Bool) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, code lower, code upper;
     0, (10 : ℚ) ^ lower.length, 0;
     0, 0, (10 : ℚ) ^ upper.length]

@[simp] theorem sideMatrix_nil : sideMatrix [] [] = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;> simp [sideMatrix]

theorem sideMatrix_append (upper lower upper' lower' : List Bool) :
    sideMatrix (upper ++ upper') (lower ++ lower') =
      sideMatrix upper lower * sideMatrix upper' lower' := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [sideMatrix, Matrix.mul_apply, Fin.sum_univ_succ, code_append, pow_add]
  all_goals ring

/-- Decimal side matrix of one physical Neary role. -/
def roleMatrix (β : Nat) (body : List TagLetter) (role : NearyTile) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  sideMatrix (nearyUpper β role) (nearyLower β body role)

/-- Decimal value of the fixed right marker. -/
def marker (β : Nat) : ℚ := code (nearyMarker β)

/-- Decimal scale immediately beyond the fixed right marker. -/
def markerScale (β : Nat) : ℚ := (10 : ℚ) ^ (β + 1)

/-- Ratio aligning the distinguished basis vector with the fixed right boundary. -/
def ratio (β : Nat) : ℚ := markerScale β / marker β

/-- Gap between the radix and the distinguished upper digit in the setter basis. -/
def basisGap (β : Nat) : ℚ := 9 - 5 * ratio β

/-- First coordinate of the distinguished `c` image. -/
def alpha (β : Nat) : ℚ := 1 + 5 * ratio β

/-- Scalar in the internal rank-one separator. -/
def separatorScale (β : Nat) : ℚ := alpha β / marker β

/-- Boundary-adapted side basis with columns `f`, `p`, and `q`. -/
def sideBasis (β : Nat) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 0, 0;
     0, -1, 0;
     ratio β, 0, ratio β * basisGap β]

/-- Explicit inverse of `sideBasis`. -/
def sideBasisInv (β : Nat) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 0, 0;
     0, -1, 0;
     -(1 / basisGap β), 0, 1 / (ratio β * basisGap β)]

/-- A side role in the boundary-adapted basis. -/
def conjugatedRole (β : Nat) (body : List TagLetter) (role : NearyTile) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  sideBasisInv β * roleMatrix β body role * sideBasis β

/-- Rank-one rule/erasure difference before the side-basis change. -/
def roleDifference (β : Nat) (body : List TagLetter) (letter : TagLetter) : Fin 3 → ℚ :=
  ![(code (nearyLower β body (.rule letter)) : ℚ) - 7,
    (10 : ℚ) ^ (nearyLower β body (.rule letter)).length - 10,
    0]

/-- Rule/erasure difference in the boundary-adapted basis. -/
def conjugatedDifference (β : Nat) (body : List TagLetter) (letter : TagLetter) :
    Fin 3 → ℚ :=
  sideBasisInv β *ᵥ roleDifference β body letter

/-- A data letter. Its fourth column changes the role from rule to erasure. -/
def data (β : Nat) (body : List TagLetter) (letter : TagLetter) :
    Matrix (Fin 5) (Fin 5) ℚ :=
  let rule := conjugatedRole β body (.rule letter)
  let difference := conjugatedDifference β body letter
  !![rule 0 0, rule 0 1, rule 0 2, difference 0, 0;
     rule 1 0, rule 1 1, rule 1 2, difference 1, 0;
     rule 2 0, rule 2 1, rule 2 2, difference 2, 0;
     0, 0, 0, 0, 0;
     0, 0, 0, 0, 0]

/-- The third physical generator, recording one role-phase bit and cubing to rank one. -/
def delimiter (β : Nat) : Matrix (Fin 5) (Fin 5) ℚ :=
  SetterShear.delimiter 0 (separatorScale β)

/-- Embed a side-basis column with cleared phase markers. -/
def rootColumn (column : Fin 3 → ℚ) : Fin 5 → ℚ :=
  ![column 0, column 1, column 2, 0, 0]

/-- The phase-marked form produced by one delimiter. -/
def markedColumn (column : Fin 3 → ℚ) : Fin 5 → ℚ :=
  ![column 0, column 1, column 2, column 1, column 2]

/-- Fixed column representing the marked right boundary. -/
def terminalColumn (β : Nat) : Fin 5 → ℚ :=
  ![marker β, 1, 0, 1, 0]

/-- Fixed row extracted by every delimiter run of length at least three. -/
def terminalRow : Fin 5 → ℚ := ![1, 0, 0, 0, 0]

/-- First coordinate axis in the five-state space. -/
def firstAxis : Fin 5 → ℚ := ![1, 0, 0, 0, 0]

theorem marker_relation (β : Nat) :
    9 * marker β = 52 * (10 : ℚ) ^ β - 7 := by
  induction β with
  | zero => norm_num [marker, nearyMarker, code, digit]
  | succ β induction =>
      have marker_succ : nearyMarker (β + 1) = nearyMarker β ++ [false] := by
        simp [nearyMarker, List.replicate_succ']
      have induction' :
          9 * (code (nearyMarker β) : ℚ) = 52 * (10 : ℚ) ^ β - 7 := by
        simpa only [marker] using induction
      rw [marker, marker_succ, code_append]
      norm_num [digit] at induction' ⊢
      rw [pow_succ]
      linarith

theorem marker_pos (β : Nat) : 0 < marker β := by
  change (0 : ℚ) < (code (nearyMarker β) : ℚ)
  exact_mod_cast code_pos_of_ne_nil (by simp [nearyMarker] : nearyMarker β ≠ [])

theorem ratio_ne_zero (β : Nat) : ratio β ≠ 0 := by
  exact div_ne_zero (pow_ne_zero _ (by norm_num)) (ne_of_gt (marker_pos β))

theorem basisGap_pos {β : Nat} (β_pos : 0 < β) : 0 < basisGap β := by
  have rho_lower : (10 : ℚ) ≤ 10 ^ β := by
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt β_pos)
    have power_one : (1 : ℚ) ≤ 10 ^ offset := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    nlinarith
  have marker_formula := marker_relation β
  have marker_positive := marker_pos β
  unfold basisGap ratio markerScale
  rw [sub_pos, show 5 * (10 ^ (β + 1) / marker β) =
      (5 * 10 ^ (β + 1)) / marker β by ring,
    div_lt_iff₀ marker_positive]
  rw [pow_succ]
  nlinarith

theorem basisGap_ne_zero {β : Nat} (β_pos : 0 < β) : basisGap β ≠ 0 :=
  ne_of_gt (basisGap_pos β_pos)

theorem sideBasis_mul_sideBasisInv {β : Nat} (β_pos : 0 < β) :
    sideBasis β * sideBasisInv β = 1 := by
  have ratio_nonzero := ratio_ne_zero β
  have gap_nonzero := basisGap_ne_zero β_pos
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [sideBasis, sideBasisInv, Matrix.mul_apply, Fin.sum_univ_succ,
      gap_nonzero]
  all_goals field_simp [ratio_nonzero, gap_nonzero]

theorem sideBasisInv_mul_sideBasis {β : Nat} (β_pos : 0 < β) :
    sideBasisInv β * sideBasis β = 1 := by
  have ratio_nonzero := ratio_ne_zero β
  have gap_nonzero := basisGap_ne_zero β_pos
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [sideBasis, sideBasisInv, Matrix.mul_apply, Fin.sum_univ_succ,
      ratio_nonzero]
  all_goals field_simp [ratio_nonzero, gap_nonzero]

theorem role_rule_eq_erase_add_outer (β : Nat) (body : List TagLetter)
    (letter : TagLetter) :
    roleMatrix β body (.rule letter) =
      roleMatrix β body (.erase letter) +
        Matrix.vecMulVec (roleDifference β body letter) (![0, 1, 0] : Fin 3 → ℚ) := by
  ext row column
  cases letter <;> fin_cases row <;> fin_cases column <;>
    simp [roleMatrix, sideMatrix, roleDifference, nearyUpper, nearyLower]

theorem delimiter_mul_rootColumn (β : Nat) (column : Fin 3 → ℚ) :
    delimiter β *ᵥ rootColumn column = markedColumn column := by
  ext coordinate
  fin_cases coordinate <;>
    simp [delimiter, SetterShear.delimiter, rootColumn, markedColumn,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem data_mul_rootColumn (β : Nat) (body : List TagLetter) (letter : TagLetter)
    (column : Fin 3 → ℚ) :
    data β body letter *ᵥ rootColumn column =
      rootColumn (conjugatedRole β body (.rule letter) *ᵥ column) := by
  ext coordinate
  fin_cases coordinate <;>
    simp [data, rootColumn, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem data_mul_markedColumn {β : Nat} (β_pos : 0 < β) (body : List TagLetter)
    (letter : TagLetter) (column : Fin 3 → ℚ) :
    data β body letter *ᵥ markedColumn column =
      rootColumn (conjugatedRole β body (.erase letter) *ᵥ column) := by
  ext coordinate
  cases letter <;> fin_cases coordinate <;>
    simp [data, markedColumn, rootColumn, conjugatedDifference, conjugatedRole,
      roleDifference, roleMatrix, sideMatrix, sideBasis, sideBasisInv,
      nearyUpper, nearyLower, Matrix.mulVec, Matrix.mul_apply, dotProduct,
      Fin.sum_univ_succ]
  all_goals (field_simp [ratio_ne_zero β, basisGap_ne_zero β_pos]; ring)

theorem delimiter_cube (β : Nat) :
    delimiter β ^ 3 = Matrix.vecMulVec firstAxis terminalRow := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [delimiter, SetterShear.delimiter, firstAxis, terminalRow,
      Matrix.vecMulVec_apply, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem delimiter_stabilizes (β : Nat) (power : Nat) (power_large : 3 ≤ power) :
    delimiter β ^ power = delimiter β ^ 3 := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le power_large
  induction offset with
  | zero => rfl
  | succ offset induction =>
      rw [show 3 + (offset + 1) = (3 + offset) + 1 by omega, pow_succ,
        induction (by omega)]
      ext row column
      fin_cases row <;> fin_cases column <;>
        simp [delimiter, SetterShear.delimiter, pow_succ, Matrix.mul_apply,
          Fin.sum_univ_succ]

/-- The delimiter has the audited rank three. -/
theorem delimiter_rank_eq_three (β : Nat) : (delimiter β).rank = 3 := by
  let rangeInjection : Matrix (Fin 5) (Fin 3) ℚ :=
    !![1, 0, 0;
       0, 1, 0;
       0, 0, 1;
       0, 1, 0;
       0, 0, 1]
  let core : Matrix (Fin 3) (Fin 5) ℚ :=
    !![1, 0, 0, 0, 0;
       0, 1, 0, -1, separatorScale β;
       0, 0, 1, 0, -1]
  have factor : delimiter β = rangeInjection * core := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [delimiter, SetterShear.delimiter, rangeInjection, core, Matrix.mul_apply,
        Fin.sum_univ_succ]
  have rank_le : (delimiter β).rank ≤ 3 := by
    rw [factor]
    exact (Matrix.rank_mul_le_left rangeInjection core).trans
      (Matrix.rank_le_width rangeInjection)
  let firstProjection : Matrix (Fin 3) (Fin 5) ℚ :=
    !![1, 0, 0, 0, 0;
       0, 1, 0, 0, 0;
       0, 0, 1, 0, 0]
  let firstInjection : Matrix (Fin 5) (Fin 3) ℚ :=
    !![1, 0, 0;
       0, 1, 0;
       0, 0, 1;
       0, 0, 0;
       0, 0, 0]
  have sandwich : firstProjection * delimiter β * firstInjection = 1 := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [delimiter, SetterShear.delimiter, firstProjection, firstInjection,
        Matrix.mul_apply, Fin.sum_univ_succ]
  have rank_ge : 3 ≤ (delimiter β).rank := by
    calc
      3 = (1 : Matrix (Fin 3) (Fin 3) ℚ).rank := by
        simp
      _ = (firstProjection * delimiter β * firstInjection).rank := by rw [sandwich]
      _ ≤ (delimiter β * firstInjection).rank := by
        simpa [Matrix.mul_assoc] using
          Matrix.rank_mul_le_right firstProjection (delimiter β * firstInjection)
      _ ≤ (delimiter β).rank :=
        Matrix.rank_mul_le_left (delimiter β) firstInjection
  exact le_antisymm rank_le rank_ge

/-- The delimiter square has the audited rank two. -/
theorem delimiter_square_rank_eq_two (β : Nat) : (delimiter β ^ 2).rank = 2 := by
  have ratio_positive : 0 < ratio β :=
    div_pos (pow_pos (by norm_num) _) (marker_pos β)
  have alpha_positive : 0 < alpha β := by
    unfold alpha
    nlinarith
  have scale_ne : separatorScale β ≠ 0 :=
    div_ne_zero (ne_of_gt alpha_positive) (ne_of_gt (marker_pos β))
  let rangeInjection : Matrix (Fin 5) (Fin 2) ℚ :=
    !![1, 0;
       0, 1;
       0, 0;
       0, 1;
       0, 0]
  let core : Matrix (Fin 2) (Fin 5) ℚ :=
    !![1, 0, 0, 0, 0;
       0, 0, separatorScale β, 0, -separatorScale β]
  have factor : delimiter β ^ 2 = rangeInjection * core := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [delimiter, SetterShear.delimiter, rangeInjection, core, pow_succ,
        Matrix.mul_apply, Fin.sum_univ_succ]
  have rank_le : (delimiter β ^ 2).rank ≤ 2 := by
    rw [factor]
    exact (Matrix.rank_mul_le_left rangeInjection core).trans
      (Matrix.rank_le_width rangeInjection)
  let rangeProjection : Matrix (Fin 2) (Fin 5) ℚ :=
    !![1, 0, 0, 0, 0;
       0, 1, 0, 0, 0]
  let rangeSection : Matrix (Fin 5) (Fin 2) ℚ :=
    !![1, 0;
       0, 0;
       0, 1 / separatorScale β;
       0, 0;
       0, 0]
  have sandwich : rangeProjection * delimiter β ^ 2 * rangeSection = 1 := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [delimiter, SetterShear.delimiter, rangeProjection, rangeSection, pow_succ,
        Matrix.mul_apply, Fin.sum_univ_succ, scale_ne]
  have rank_ge : 2 ≤ (delimiter β ^ 2).rank := by
    calc
      2 = (1 : Matrix (Fin 2) (Fin 2) ℚ).rank := by
        simp
      _ = (rangeProjection * delimiter β ^ 2 * rangeSection).rank := by rw [sandwich]
      _ ≤ (delimiter β ^ 2 * rangeSection).rank := by
        simpa [Matrix.mul_assoc] using
          Matrix.rank_mul_le_right rangeProjection (delimiter β ^ 2 * rangeSection)
      _ ≤ (delimiter β ^ 2).rank :=
        Matrix.rank_mul_le_left (delimiter β ^ 2) rangeSection
  exact le_antisymm rank_le rank_ge

/-- The stabilized delimiter cube has the audited rank one. -/
theorem delimiter_cube_rank_eq_one (β : Nat) : (delimiter β ^ 3).rank = 1 := by
  let rangeInjection : Matrix (Fin 5) (Fin 1) ℚ :=
    !![1;
       0;
       0;
       0;
       0]
  let core : Matrix (Fin 1) (Fin 5) ℚ :=
    !![1, 0, 0, 0, 0]
  have factor : delimiter β ^ 3 = rangeInjection * core := by
    rw [delimiter_cube]
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [firstAxis, terminalRow, rangeInjection, core, Matrix.vecMulVec_apply,
        Matrix.mul_apply]
  have rank_le : (delimiter β ^ 3).rank ≤ 1 := by
    rw [factor]
    exact (Matrix.rank_mul_le_left rangeInjection core).trans
      (Matrix.rank_le_width rangeInjection)
  have sandwich : core * delimiter β ^ 3 * rangeInjection = 1 := by
    ext row column
    have row_eq : row = 0 := Subsingleton.elim row 0
    have column_eq : column = 0 := Subsingleton.elim column 0
    subst row
    subst column
    simp [delimiter, SetterShear.delimiter, rangeInjection, core, pow_succ,
      Matrix.mul_apply, Fin.sum_univ_succ]
  have rank_ge : 1 ≤ (delimiter β ^ 3).rank := by
    calc
      1 = (1 : Matrix (Fin 1) (Fin 1) ℚ).rank := by simp
      _ = (core * delimiter β ^ 3 * rangeInjection).rank := by rw [sandwich]
      _ ≤ (delimiter β ^ 3 * rangeInjection).rank := by
        simpa [Matrix.mul_assoc] using
          Matrix.rank_mul_le_right core (delimiter β ^ 3 * rangeInjection)
      _ ≤ (delimiter β ^ 3).rank :=
        Matrix.rank_mul_le_left (delimiter β ^ 3) rangeInjection
  exact le_antisymm rank_le rank_ge

theorem sideBasis_mul_boundary (β : Nat) :
    sideBasis β *ᵥ (![marker β, 1, 0] : Fin 3 → ℚ) =
      ![marker β, -1, markerScale β] := by
  ext coordinate
  fin_cases coordinate <;>
    simp [sideBasis, ratio, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      marker_pos β |>.ne']

theorem conjugatedRuleC_mul_first {β : Nat} (β_pos : 0 < β)
    (body : List TagLetter) :
    conjugatedRole β body (.rule .c) *ᵥ (![1, 0, 0] : Fin 3 → ℚ) =
      ![alpha β, 0, 1] := by
  ext coordinate
  fin_cases coordinate <;>
    simp [conjugatedRole, roleMatrix, sideMatrix, sideBasis, sideBasisInv,
      alpha, Matrix.mulVec, Matrix.mul_apply, dotProduct,
      Fin.sum_univ_succ, nearyUpper, nearyLower, tagCode, code, digit]
  all_goals
    field_simp [ratio_ne_zero β, basisGap_ne_zero β_pos]
    simp [basisGap]
    ring

theorem dataC_mul_firstAxis {β : Nat} (β_pos : 0 < β) (body : List TagLetter) :
    data β body .c *ᵥ firstAxis =
      SetterShear.distinguishedColumn (alpha β) := by
  rw [show firstAxis = rootColumn (![1, 0, 0] : Fin 3 → ℚ) by
    funext coordinate
    fin_cases coordinate <;> rfl, data_mul_rootColumn,
    conjugatedRuleC_mul_first β_pos]
  rfl

theorem separator_calibrated (β : Nat) :
    separatorScale β * marker β = 1 + ratio β * 5 := by
  unfold separatorScale alpha
  rw [div_mul_cancel₀ _ (ne_of_gt (marker_pos β))]
  ring

/-- The mixed word `S² A_c S³` is the exact internal rank-one separator. -/
theorem internalSeparator {β : Nat} (β_pos : 0 < β) (body : List TagLetter) :
    delimiter β ^ 2 * data β body .c * delimiter β ^ 3 =
      separatorScale β • Matrix.vecMulVec (terminalColumn β) terminalRow := by
  rw [delimiter_cube]
  rw [mul_outer, ← Matrix.mulVec_mulVec, dataC_mul_firstAxis β_pos]
  have square_image := SetterShear.delimiter_square_distinguishedColumn
    (ratio β) 5 (alpha β) (separatorScale β) (marker β)
    (separator_calibrated β)
  rw [show delimiter β = SetterShear.delimiter 0 (separatorScale β) by rfl]
  rw [show SetterShear.hook (ratio β) 5 (alpha β) = 0 by
    simp [SetterShear.hook, alpha]
    ring] at square_image
  rw [square_image]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [terminalColumn, terminalRow, SetterShear.separatorColumn,
      Matrix.vecMulVec_apply]

/-! ## Regular physical language -/

/-- The three physical setter generators: two data letters and the delimiter. -/
def generator (β : Nat) (body : List TagLetter) :
    Option TagLetter → Matrix (Fin 5) (Fin 5) ℚ
  | none => delimiter β
  | some letter => data β body letter

/-- A regular physical spelling and the role word it decodes. The final data letter is read as
an erasure by the marked terminal column; every earlier erasure carries one delimiter. -/
inductive RegularSpelling : List (Option TagLetter) → List NearyTile → Prop
  | terminal (letter : TagLetter) : RegularSpelling [some letter] [.erase letter]
  | rule {physical : List (Option TagLetter)} {roles : List NearyTile}
      (letter : TagLetter) (tail : RegularSpelling physical roles) :
      RegularSpelling (some letter :: physical) (.rule letter :: roles)
  | erase {physical : List (Option TagLetter)} {roles : List NearyTile}
      (letter : TagLetter) (tail : RegularSpelling physical roles) :
      RegularSpelling (some letter :: none :: physical) (.erase letter :: roles)

/-- Product of the decoded roles in the boundary-adapted three-state space. -/
def roleProduct (β : Nat) (body : List TagLetter) (roles : List NearyTile) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  wordProduct (conjugatedRole β body) roles

theorem terminalColumn_eq_marked (β : Nat) :
    terminalColumn β = markedColumn (![marker β, 1, 0] : Fin 3 → ℚ) := by
  funext coordinate
  fin_cases coordinate <;> rfl

/-- The physical regular spelling executes exactly its decoded role word. -/
theorem RegularSpelling.mulVec_terminalColumn {β : Nat} (β_pos : 0 < β)
    (body : List TagLetter) {physical : List (Option TagLetter)}
    {roles : List NearyTile} (spelling : RegularSpelling physical roles) :
    wordProduct (generator β body) physical *ᵥ terminalColumn β =
      rootColumn (roleProduct β body roles *ᵥ (![marker β, 1, 0] : Fin 3 → ℚ)) := by
  induction spelling with
  | terminal letter =>
      rw [terminalColumn_eq_marked, show wordProduct (generator β body) [some letter] =
          data β body letter by simp [generator], data_mul_markedColumn β_pos]
      simp [roleProduct]
  | rule letter tail induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec, induction]
      change data β body letter *ᵥ
          rootColumn (roleProduct β body _ *ᵥ _) = _
      rw [data_mul_rootColumn]
      simp [roleProduct, ← Matrix.mulVec_mulVec]
  | erase letter tail induction =>
      rw [wordProduct_cons, wordProduct_cons, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, induction]
      change data β body letter *ᵥ delimiter β *ᵥ
          rootColumn (roleProduct β body _ *ᵥ _) = _
      rw [delimiter_mul_rootColumn, data_mul_markedColumn β_pos]
      simp [roleProduct, ← Matrix.mulVec_mulVec]

theorem roleProduct_eq_conjugatedSide {β : Nat} (β_pos : 0 < β)
    (body : List TagLetter) (roles : List NearyTile) :
    roleProduct β body roles =
      sideBasisInv β *
        sideMatrix (spell (nearyUpper β) roles) (spell (nearyLower β body) roles) *
          sideBasis β := by
  induction roles with
  | nil =>
      change 1 = sideBasisInv β * sideMatrix [] [] * sideBasis β
      rw [sideMatrix_nil, Matrix.mul_one]
      exact (sideBasisInv_mul_sideBasis β_pos).symm
  | cons role roles induction =>
      rw [roleProduct, wordProduct_cons]
      change conjugatedRole β body role * roleProduct β body roles = _
      rw [induction, conjugatedRole]
      simp only [spell]
      calc
        (sideBasisInv β * roleMatrix β body role * sideBasis β) *
              (sideBasisInv β *
                sideMatrix (spell (nearyUpper β) roles)
                  (spell (nearyLower β body) roles) * sideBasis β) =
            sideBasisInv β * roleMatrix β body role *
              (sideBasis β * sideBasisInv β) *
                sideMatrix (spell (nearyUpper β) roles)
                  (spell (nearyLower β body) roles) * sideBasis β := by
          noncomm_ring
        _ = sideBasisInv β *
              (roleMatrix β body role *
                sideMatrix (spell (nearyUpper β) roles)
                  (spell (nearyLower β body) roles)) * sideBasis β := by
          rw [sideBasis_mul_sideBasisInv β_pos]
          simp [Matrix.mul_assoc]
        _ = sideBasisInv β *
              sideMatrix
                (nearyUpper β role ++ spell (nearyUpper β) roles)
                (nearyLower β body role ++ spell (nearyLower β body) roles) *
                sideBasis β := by
          rw [roleMatrix, sideMatrix_append]

theorem sideMatrix_boundaryCoefficient (β : Nat) (upper lower : List Bool) :
    (sideMatrix upper lower *ᵥ
        (![marker β, -1, markerScale β] : Fin 3 → ℚ)) 0 =
      (code (upper ++ nearyMarker β) : ℚ) - code lower := by
  rw [code_append]
  simp [sideMatrix, marker, markerScale, nearyMarker, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]
  ring

theorem roleProduct_boundaryCoefficient {β : Nat} (β_pos : 0 < β)
    (body : List TagLetter) (roles : List NearyTile) :
    (roleProduct β body roles *ᵥ (![marker β, 1, 0] : Fin 3 → ℚ)) 0 =
      (code (spell (nearyUpper β) roles ++ nearyMarker β) : ℚ) -
        code (spell (nearyLower β body) roles) := by
  rw [roleProduct_eq_conjugatedSide β_pos, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, sideBasis_mul_boundary]
  have coefficient := sideMatrix_boundaryCoefficient β
    (spell (nearyUpper β) roles) (spell (nearyLower β body) roles)
  simpa [sideBasisInv, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using coefficient

theorem terminalRow_dot_rootColumn (column : Fin 3 → ℚ) :
    terminalRow ⬝ᵥ rootColumn column = column 0 := by
  simp [terminalRow, rootColumn, dotProduct, Fin.sum_univ_succ]

/-- A regular physical scalar is exactly the radix-ten terminal discrepancy. -/
theorem RegularSpelling.coefficient_eq {β : Nat} (β_pos : 0 < β)
    (body : List TagLetter) {physical : List (Option TagLetter)}
    {roles : List NearyTile} (spelling : RegularSpelling physical roles) :
    terminalRow ⬝ᵥ wordProduct (generator β body) physical *ᵥ terminalColumn β =
      (code (spell (nearyUpper β) roles ++ nearyMarker β) : ℚ) -
        code (spell (nearyLower β body) roles) := by
  rw [spelling.mulVec_terminalColumn β_pos, terminalRow_dot_rootColumn,
    roleProduct_boundaryCoefficient β_pos]

/-- Regular physical zeros are precisely Neary terminal matches. -/
theorem RegularSpelling.coefficient_eq_zero_iff {β : Nat} (β_pos : 0 < β)
    (body : List TagLetter) {physical : List (Option TagLetter)}
    {roles : List NearyTile} (spelling : RegularSpelling physical roles) :
    terminalRow ⬝ᵥ wordProduct (generator β body) physical *ᵥ terminalColumn β = 0 ↔
      spell (nearyUpper β) roles ++ nearyMarker β =
        spell (nearyLower β body) roles := by
  rw [spelling.coefficient_eq β_pos, sub_eq_zero, Nat.cast_inj]
  exact code_injective.eq_iff

theorem exists_regularSpelling_append_erase (front : List NearyTile)
    (last : TagLetter) :
    ∃ physical, RegularSpelling physical (front ++ [.erase last]) := by
  induction front with
  | nil => exact ⟨[some last], .terminal last⟩
  | cons role front induction =>
      obtain ⟨physical, spelling⟩ := induction
      cases role with
      | rule letter => exact ⟨some letter :: physical, .rule letter spelling⟩
      | erase letter => exact ⟨some letter :: none :: physical, .erase letter spelling⟩

private theorem strokeTiles_eq_append_erase {β : Nat} (β_large : 1 < β)
    (stroke : Stroke TagLetter β) :
    ∃ front last, strokeTiles stroke = front ++ [.erase last] := by
  have wake_ne : stroke.wake ≠ [] := by
    intro wake_nil
    have width := stroke.width
    simp [wake_nil] at width
    omega
  let last := stroke.wake.getLast wake_ne
  let frontWake := stroke.wake.dropLast
  have wake_eq : stroke.wake = frontWake ++ [last] :=
    (List.dropLast_append_getLast wake_ne).symm
  refine ⟨.rule stroke.head :: frontWake.map .erase, last, ?_⟩
  rw [strokeTiles, wake_eq, List.map_append]
  rfl

theorem tileHistory_eq_append_erase {β : Nat} (β_large : 1 < β)
    (first : Stroke TagLetter β) (history : List (Stroke TagLetter β)) :
    ∃ front last, tileHistory (first :: history) = front ++ [.erase last] := by
  induction history generalizing first with
  | nil =>
      simpa [tileHistory_cons] using strokeTiles_eq_append_erase β_large first
  | cons next history induction =>
      obtain ⟨front, last, tail_eq⟩ := induction next
      refine ⟨strokeTiles first ++ front, last, ?_⟩
      change strokeTiles first ++ tileHistory (next :: history) =
        (strokeTiles first ++ front) ++ [.erase last]
      rw [tail_eq, List.append_assoc]

/-- Every terminal match has a regular physical spelling. -/
theorem terminalMatch_has_regularSpelling {β : Nat} (β_large : 1 < β)
    (body : List TagLetter) (roles : List NearyTile)
    (terminal_match :
      spell (nearyUpper β) roles ++ nearyMarker β =
        spell (nearyLower β body) roles) :
    ∃ physical, RegularSpelling physical roles := by
  obtain ⟨history, roles_eq⟩ :=
    tileHistory_of_terminal_match β body (by omega) roles terminal_match
  have history_ne : history ≠ [] := by
    intro history_nil
    subst history
    simp [roles_eq, spell, nearyMarker] at terminal_match
  obtain ⟨first, history, rfl⟩ := List.exists_cons_of_ne_nil history_ne
  rw [roles_eq]
  obtain ⟨front, last, role_shape⟩ :=
    tileHistory_eq_append_erase β_large first history
  rw [role_shape]
  exact exists_regularSpelling_append_erase front last

/-! ## Forward mortality compiler -/

/-- Physical spelling of the internal separator `S² A_c S³`. -/
def internalSeparatorWord : List (Option TagLetter) :=
  [none, none, some .c, none, none, none]

theorem wordProduct_internalSeparatorWord (β : Nat) (body : List TagLetter) :
    wordProduct (generator β body) internalSeparatorWord =
      delimiter β ^ 2 * data β body .c * delimiter β ^ 3 := by
  simp [internalSeparatorWord, generator, pow_succ, Matrix.mul_assoc]

private theorem internalSeparator_sandwich_eq_zero {β : Nat} (β_pos : 0 < β)
    (body : List TagLetter) (middle : Matrix (Fin 5) (Fin 5) ℚ)
    (coefficient_zero : terminalRow ⬝ᵥ middle *ᵥ terminalColumn β = 0) :
    (delimiter β ^ 2 * data β body .c * delimiter β ^ 3) * middle *
        (delimiter β ^ 2 * data β body .c * delimiter β ^ 3) = 0 := by
  rw [internalSeparator β_pos body]
  let outer := Matrix.vecMulVec (terminalColumn β) terminalRow
  calc
    (separatorScale β • outer) * middle * (separatorScale β • outer) =
        (separatorScale β * separatorScale β) • (outer * middle * outer) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    _ = (separatorScale β * separatorScale β) •
          ((terminalRow ⬝ᵥ middle *ᵥ terminalColumn β) • outer) := by
      simp only [outer]
      rw [outer_mul, outer_mul_outer, Matrix.dotProduct_mulVec]
    _ = 0 := by rw [coefficient_zero]; simp

/-- A terminal match supplies an explicit zero word over the three rational setter matrices. -/
theorem mortal_of_terminalMatch {β : Nat} (β_large : 1 < β)
    (body : List TagLetter) (roles : List NearyTile)
    (terminal_match :
      spell (nearyUpper β) roles ++ nearyMarker β =
        spell (nearyLower β body) roles) :
    IsMortal (generator β body) := by
  obtain ⟨physical, spelling⟩ :=
    terminalMatch_has_regularSpelling β_large body roles terminal_match
  have coefficient_zero :
      terminalRow ⬝ᵥ wordProduct (generator β body) physical *ᵥ terminalColumn β = 0 :=
    (spelling.coefficient_eq_zero_iff (by omega) body).mpr terminal_match
  refine ⟨internalSeparatorWord ++ physical ++ internalSeparatorWord,
    by simp [internalSeparatorWord], ?_⟩
  rw [wordProduct_append, wordProduct_append,
    wordProduct_internalSeparatorWord]
  exact internalSeparator_sandwich_eq_zero (by omega) body
    (wordProduct (generator β body) physical) coefficient_zero

/-- Halting of a restricted Neary source implies mortality of its rational decimal setter. -/
theorem mortal_of_tagHaltsFrom (β : Nat) (body : List TagLetter)
    (β_large : 2 < β) (body_long : β - 1 ≤ body.length)
    (body_divisible : β - 1 ∣ body.length)
    (halts : TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b])) :
    IsMortal (generator β body) := by
  obtain ⟨roles, terminal_match⟩ :=
    terminal_match_of_tagHaltsFrom β body β_large body_long body_divisible halts
  exact mortal_of_terminalMatch (by omega) body roles terminal_match

end MatrixMortality.DecimalSetterMatrix
