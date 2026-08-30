import MatrixMortality.ParabolicDefect

/-!
# Three-defect bad runs

The second protected-plane bad incidence consists of three consecutive residue-two atoms between
equal safe phases. At deletion width three, both all-`b` orientations have fixed nonzero bridge
sign. The two explicit cores below retain the exact characteristic-zero certificates.
-/

namespace MatrixMortality.ParabolicBlade

/-- Positive coefficient core of the residue pattern `0 | 2 | 2 | 2 | 0` at deletion width
three. -/
def tripleBDefectZeroCore (a b c y z : ℚ) : ℚ :=
  a * b * c *
      (34074371915440717824 * y * z + 3185627353139183616 * y +
        4259296489430089728 * z + 398203419142397952) +
    a * b *
      (1341445461427407863808 * y * z + 125412299934244319232 * y +
        103581321415333982208 * z + 9683861265996770304) +
    a * c *
      (1351742474715759525888 * y * z + 126374952378230802432 * y +
        168967809339469940736 * z + 15796869047278850304) +
    a *
      (52250299870671771503616 * y * z + 4884901732062751918464 * y +
        4006164069491545854720 * z + 374537904055429098528) +
    b * c *
      (1331251286533069160448 * y * z + 124312819656101548032 * y +
        166406410816633645056 * z + 15539102457012693504) +
    b *
      (52404345416407034059776 * y * z + 4893540087399053485824 * y +
        4046329849884117090048 * z + 377847995276287673280) +
    c *
      (51854812837108821017856 * y * z + 4842161079636904628544 * y +
        6481851604638602627232 * z + 605270134954613078568) +
    2004266957209355580973552 * y * z + 187156841535247848961148 * y +
    153668352923040370249412 * z + 14349427323320359186993

/-- Positive coefficient core of the residue pattern `1 | 2 | 2 | 2 | 1` at deletion width
three. -/
def tripleBDefectOneCore (a b c : ℚ) : ℚ :=
  820818011565195264 * a * b * c +
    32926106303550508032 * a * b +
    32550519970051863552 * a * c +
    1281941764421891891040 * a +
    29489532362083003392 * b * c +
    1182835770175838353536 * b +
    1148618523667458448800 * c +
    45233211842593927206431

theorem tripleBDefectZeroCore_pos
    (a b c y z : ℚ) (a_nonnegative : 0 ≤ a) (b_nonnegative : 0 ≤ b)
    (c_nonnegative : 0 ≤ c) (y_nonnegative : 0 ≤ y) (z_nonnegative : 0 ≤ z) :
    0 < tripleBDefectZeroCore a b c y z := by
  unfold tripleBDefectZeroCore
  positivity

theorem tripleBDefectOneCore_pos
    (a b c : ℚ) (a_nonnegative : 0 ≤ a) (b_nonnegative : 0 ≤ b)
    (c_nonnegative : 0 ≤ c) :
    0 < tripleBDefectOneCore a b c := by
  unfold tripleBDefectOneCore
  positivity

/-- Exact all-`b` bridge determinant for the shortest three-defect run between residue-zero safe
phases. -/
theorem bridge_bZero_bTwo_bTwo_bTwo_bZero_det (a b c y z : Nat) :
    (bridge 27
      (bAtom 27 (3 * z) * bAtom 27 (3 * a + 2) * bAtom 27 (3 * b + 2) *
        bAtom 27 (3 * c + 2) * bAtom 27 (3 * y))).det =
      6561 / 32 * tripleBDefectZeroCore a b c y z := by
  simp_rw [bAtom_three_mul_matrix, bAtom_three_mul_add_two_matrix]
  rw [Matrix.det_fin_two]
  norm_num [bridge, coreInput, coreOutput, Matrix.mul_apply, Fin.sum_univ_succ,
    tripleBDefectZeroCore]
  ring

/-- Exact all-`b` bridge determinant for the shortest three-defect run between residue-one safe
phases. -/
theorem bridge_bOne_bTwo_bTwo_bTwo_bOne_det (a b c y z : Nat) :
    (bridge 27
      (bAtom 27 (3 * z + 1) * bAtom 27 (3 * a + 2) * bAtom 27 (3 * b + 2) *
        bAtom 27 (3 * c + 2) * bAtom 27 (3 * y + 1))).det =
      -2187 * y * z / 4 * tripleBDefectOneCore a b c := by
  simp_rw [bAtom_three_mul_add_one_matrix, bAtom_three_mul_add_two_matrix]
  rw [Matrix.det_fin_two]
  norm_num [bridge, coreInput, coreOutput, Matrix.mul_apply, Fin.sum_univ_succ,
    tripleBDefectOneCore]
  ring

/-- No all-`b` three-defect run between residue-zero safe phases closes the bridge. -/
theorem bridge_bZero_bTwo_bTwo_bTwo_bZero_det_ne_zero (a b c y z : Nat) :
    (bridge 27
      (bAtom 27 (3 * z) * bAtom 27 (3 * a + 2) * bAtom 27 (3 * b + 2) *
        bAtom 27 (3 * c + 2) * bAtom 27 (3 * y))).det ≠ 0 := by
  rw [bridge_bZero_bTwo_bTwo_bTwo_bZero_det]
  have core_positive : 0 < tripleBDefectZeroCore (a : ℚ) b c y z :=
    tripleBDefectZeroCore_pos a b c y z (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity)
  positivity

/-- No regular all-`b` three-defect run between residue-one safe phases closes the bridge. -/
theorem bridge_bOne_bTwo_bTwo_bTwo_bOne_det_ne_zero
    (a b c y z : Nat) (y_positive : 0 < y) (z_positive : 0 < z) :
    (bridge 27
      (bAtom 27 (3 * z + 1) * bAtom 27 (3 * a + 2) * bAtom 27 (3 * b + 2) *
        bAtom 27 (3 * c + 2) * bAtom 27 (3 * y + 1))).det ≠ 0 := by
  rw [bridge_bOne_bTwo_bTwo_bTwo_bOne_det]
  have core_positive : 0 < tripleBDefectOneCore (a : ℚ) b c :=
    tripleBDefectOneCore_pos a b c (by positivity) (by positivity) (by positivity)
  positivity

end MatrixMortality.ParabolicBlade
