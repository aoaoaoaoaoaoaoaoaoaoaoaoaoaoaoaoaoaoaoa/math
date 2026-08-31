import MatrixMortality.ParabolicDefect

/-!
# Uniform all-`b` defect-run exclusion

At deletion width three, one rational cone is invariant under every residue-two `b` atom.
Both regular safe endpoint phases enter the cone, while their left bridge covectors have strict
sign. The resulting theorem excludes every all-`b` safe/defect/safe bridge, with no bound or
parity restriction on the defect run.
-/

namespace MatrixMortality.ParabolicBlade

open scoped Matrix

private def bConeSign : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 0, 0; 0, -1, 0; 0, 0, -1]

private theorem bConeSign_sq : bConeSign * bConeSign = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bConeSign, Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ]

private def bDefectConeAction (wait : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, 4617 + 5832 * wait, 745281 / 8;
     3029 / 2 - 24 * wait, 3865 + 4896 * wait, 312823 / 4;
     0, 8262 + 11664 * wait, 744309 / 4]

private def InBDefectCone (state : Fin 3 → ℚ) : Prop :=
  0 < state 0 ∧
    state 0 ≤ 2 * state 1 ∧
    7 * state 1 ≤ 6 * state 0 ∧
    state 0 ≤ state 2

private theorem inBDefectCone_coordinates {state : Fin 3 → ℚ}
    (inside : InBDefectCone state) :
    0 < state 0 ∧ 0 < state 1 ∧ 0 < state 2 := by
  rcases inside with ⟨first_positive, first_le_twice_second, _, first_le_third⟩
  constructor
  · exact first_positive
  constructor <;> nlinarith

private theorem bDefectConeAction_mulVec (wait : ℚ) (state : Fin 3 → ℚ) :
    bDefectConeAction wait *ᵥ state =
      ![(4617 + 5832 * wait) * state 1 + 745281 / 8 * state 2,
        (3029 / 2 - 24 * wait) * state 0 +
          (3865 + 4896 * wait) * state 1 + 312823 / 4 * state 2,
        (8262 + 11664 * wait) * state 1 + 744309 / 4 * state 2] := by
  funext i
  fin_cases i <;>
    norm_num [bDefectConeAction, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

private theorem bDefectConeAction_preserves
    (wait : ℚ) (wait_nonnegative : 0 ≤ wait) (state : Fin 3 → ℚ)
    (inside : InBDefectCone state) :
    InBDefectCone (bDefectConeAction wait *ᵥ state) := by
  rcases inside with ⟨x_positive, x_le_two_y, seven_y_le_six_x, x_le_z⟩
  obtain ⟨_, y_positive, z_positive⟩ :=
    inBDefectCone_coordinates ⟨x_positive, x_le_two_y, seven_y_le_six_x, x_le_z⟩
  rw [bDefectConeAction_mulVec]
  change
    0 < (4617 + 5832 * wait) * state 1 + 745281 / 8 * state 2 ∧
      (4617 + 5832 * wait) * state 1 + 745281 / 8 * state 2 ≤
        2 * ((3029 / 2 - 24 * wait) * state 0 +
          (3865 + 4896 * wait) * state 1 + 312823 / 4 * state 2) ∧
      7 * ((3029 / 2 - 24 * wait) * state 0 +
          (3865 + 4896 * wait) * state 1 + 312823 / 4 * state 2) ≤
        6 * ((4617 + 5832 * wait) * state 1 + 745281 / 8 * state 2) ∧
      (4617 + 5832 * wait) * state 1 + 745281 / 8 * state 2 ≤
        (8262 + 11664 * wait) * state 1 + 744309 / 4 * state 2
  have first_positive :
      0 < (4617 + 5832 * wait) * state 1 + 745281 / 8 * state 2 := by
    positivity
  have wait_guard : 0 ≤ wait * (165 * state 1 - 2 * state 0) := by
    apply mul_nonneg wait_nonnegative
    nlinarith
  have twice_second_sub_first_nonnegative :
      0 ≤
        2 * ((3029 / 2 - 24 * wait) * state 0 +
          (3865 + 4896 * wait) * state 1 + 312823 / 4 * state 2) -
        ((4617 + 5832 * wait) * state 1 + 745281 / 8 * state 2) := by
    nlinarith
  have six_first_sub_seven_second_nonnegative :
      0 ≤
        6 * ((4617 + 5832 * wait) * state 1 + 745281 / 8 * state 2) -
        7 * ((3029 / 2 - 24 * wait) * state 0 +
          (3865 + 4896 * wait) * state 1 + 312823 / 4 * state 2) := by
    have wait_term : 0 ≤ wait * (168 * state 0 + 720 * state 1) := by positivity
    nlinarith
  have third_sub_first_nonnegative :
      0 ≤
        ((8262 + 11664 * wait) * state 1 + 744309 / 4 * state 2) -
        ((4617 + 5832 * wait) * state 1 + 745281 / 8 * state 2) := by
    have wait_y_nonnegative : 0 ≤ wait * state 1 :=
      mul_nonneg wait_nonnegative (le_of_lt y_positive)
    nlinarith
  constructor
  · exact first_positive
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem signed_bDefect_mulVec (wait : Nat) (state : Fin 3 → ℚ) :
    bConeSign *ᵥ
        ((bAtom 27 (3 * wait + 2)).adjugateᵀ *ᵥ state) =
      -(bDefectConeAction wait *ᵥ (bConeSign *ᵥ state)) := by
  rw [bAtom_three_mul_add_two_matrix]
  funext i
  fin_cases i <;>
    norm_num [bConeSign, bDefectConeAction, Matrix.adjugate_fin_three,
      Matrix.transpose_apply, Matrix.mulVec, Matrix.vecMul, dotProduct,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_succ]
  all_goals ring

/-- The residue-zero or residue-one `b` atom selected by its protected-plane phase. -/
def bSafeAtom (phase : Bool) (wait : Nat) : Matrix (Fin 3) (Fin 3) ℚ :=
  if phase then bAtom 27 (3 * wait + 1) else bAtom 27 (3 * wait)

private theorem signed_bSafe_right (phase : Bool) (wait : Nat) :
    bConeSign *ᵥ ((bSafeAtom phase wait).adjugateᵀ *ᵥ exteriorSeed) =
      if phase then
        ![52488 * (wait : ℚ), 43320 * (wait : ℚ), 104976 * (wait : ℚ)]
      else
        ![16038 + 128304 * (wait : ℚ), 13491 + 107928 * (wait : ℚ),
          19440 + 256608 * (wait : ℚ)] := by
  cases phase
  · simp only [bSafeAtom, Bool.false_eq_true, ↓reduceIte]
    rw [bAtom_three_mul_matrix]
    funext i
    fin_cases i <;>
      norm_num [bConeSign, exteriorSeed, Matrix.adjugate_fin_three,
        Matrix.transpose_apply, Matrix.mulVec, Matrix.vecMul, dotProduct,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_succ]
    all_goals ring
  · simp only [bSafeAtom, ↓reduceIte]
    rw [bAtom_three_mul_add_one_matrix]
    funext i
    fin_cases i <;>
      norm_num [bConeSign, exteriorSeed, Matrix.adjugate_fin_three,
        Matrix.transpose_apply, Matrix.mulVec, Matrix.vecMul, dotProduct,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_succ]
    all_goals ring

private theorem signed_bSafe_right_mem
    (phase : Bool) (wait : Nat) (regular : RegularSafeLabel (.b, wait, phase)) :
    InBDefectCone
      (bConeSign *ᵥ ((bSafeAtom phase wait).adjugateᵀ *ᵥ exteriorSeed)) := by
  rw [signed_bSafe_right]
  cases phase
  · change
      0 < 16038 + 128304 * (wait : ℚ) ∧
        16038 + 128304 * (wait : ℚ) ≤ 2 * (13491 + 107928 * (wait : ℚ)) ∧
        7 * (13491 + 107928 * (wait : ℚ)) ≤ 6 * (16038 + 128304 * (wait : ℚ)) ∧
        16038 + 128304 * (wait : ℚ) ≤ 19440 + 256608 * (wait : ℚ)
    have wait_nonnegative : 0 ≤ (wait : ℚ) := by positivity
    constructor
    · positivity
    constructor
    · nlinarith
    constructor <;> nlinarith
  · simp only [RegularSafeLabel] at regular
    change
      0 < 52488 * (wait : ℚ) ∧
        52488 * (wait : ℚ) ≤ 2 * (43320 * (wait : ℚ)) ∧
        7 * (43320 * (wait : ℚ)) ≤ 6 * (52488 * (wait : ℚ)) ∧
        52488 * (wait : ℚ) ≤ 104976 * (wait : ℚ)
    constructor
    · positivity
    constructor
    · nlinarith
    constructor
    · nlinarith
    · nlinarith

private def bridgeExteriorRow : Fin 3 → ℚ := ![-1, -1, 1 / 4]

private def signed_bSafe_left (phase : Bool) (wait : Nat) : Fin 3 → ℚ :=
  (bridgeExteriorRow ᵥ* (bSafeAtom phase wait).adjugateᵀ) ᵥ* bConeSign

private theorem signed_bSafe_left_eq (phase : Bool) (wait : Nat) :
    signed_bSafe_left phase wait =
      if phase then ![3852 * (wait : ℚ), -3876 * (wait : ℚ), 0]
      else ![-483 / 2 - 3876 * (wait : ℚ), 3 + 24 * (wait : ℚ), -243 / 4] := by
  cases phase
  · simp only [signed_bSafe_left, bSafeAtom, Bool.false_eq_true, ↓reduceIte]
    rw [bAtom_three_mul_matrix]
    funext i
    fin_cases i <;>
      norm_num [bridgeExteriorRow, bConeSign, Matrix.adjugate_fin_three,
        Matrix.transpose_apply, Matrix.vecMul, dotProduct, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
        Fin.sum_univ_succ]
    all_goals ring
  · simp only [signed_bSafe_left, bSafeAtom, ↓reduceIte]
    rw [bAtom_three_mul_add_one_matrix]
    funext i
    fin_cases i <;>
      norm_num [bridgeExteriorRow, bConeSign, Matrix.adjugate_fin_three,
        Matrix.transpose_apply, Matrix.vecMul, dotProduct, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
        Fin.sum_univ_succ]
    all_goals ring

private theorem signed_bSafe_left_zero_neg
    (wait : Nat) (state : Fin 3 → ℚ) (inside : InBDefectCone state) :
    signed_bSafe_left false wait ⬝ᵥ state < 0 := by
  rw [signed_bSafe_left_eq]
  norm_num [dotProduct, Fin.sum_univ_succ]
  rcases inside with ⟨x_positive, _, seven_y_le_six_x, x_le_z⟩
  have wait_inner_nonpositive :
      -3876 * state 0 + 24 * state 1 ≤ 0 := by
    nlinarith
  have wait_term_nonpositive :
      (wait : ℚ) * (-3876 * state 0 + 24 * state 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) wait_inner_nonpositive
  nlinarith

private theorem signed_bSafe_left_one_pos
    (wait : Nat) (wait_positive : 0 < wait)
    (state : Fin 3 → ℚ) (inside : InBDefectCone state) :
    0 < signed_bSafe_left true wait ⬝ᵥ state := by
  rw [signed_bSafe_left_eq]
  norm_num [dotProduct, Fin.sum_univ_succ]
  rcases inside with ⟨x_positive, _, seven_y_le_six_x, _⟩
  have inner_positive : 0 < 3852 * state 0 - 3876 * state 1 := by
    nlinarith
  have product_positive :
      0 < (wait : ℚ) * (3852 * state 0 - 3876 * state 1) := by
    exact mul_pos (by exact_mod_cast wait_positive) inner_positive
  nlinarith

/-- Physical product of an arbitrary run of residue-two `b` atoms at deletion width three. -/
def bDefectRun (waits : List Nat) : Matrix (Fin 3) (Fin 3) ℚ :=
  wordProduct (fun wait => bAtom 27 (3 * wait + 2)) waits

private def bDefectConeRun : List Nat → (Fin 3 → ℚ) → Fin 3 → ℚ
  | [], state => state
  | wait :: waits, state =>
      bDefectConeAction wait *ᵥ bDefectConeRun waits state

private theorem bDefectConeRun_preserves
    (waits : List Nat) (state : Fin 3 → ℚ) (inside : InBDefectCone state) :
    InBDefectCone (bDefectConeRun waits state) := by
  induction waits with
  | nil => exact inside
  | cons wait waits induction =>
      exact bDefectConeAction_preserves wait (by positivity)
        (bDefectConeRun waits state) induction

private theorem signed_bDefectRun (waits : List Nat) (state : Fin 3 → ℚ) :
    bConeSign *ᵥ ((bDefectRun waits).adjugateᵀ *ᵥ state) =
      (-1 : ℚ) ^ waits.length • bDefectConeRun waits (bConeSign *ᵥ state) := by
  induction waits with
  | nil => simp [bDefectRun, bDefectConeRun]
  | cons wait waits induction =>
      rw [bDefectRun, wordProduct_cons, Matrix.adjugate_mul_distrib,
        Matrix.transpose_mul]
      rw [← Matrix.mulVec_mulVec, signed_bDefect_mulVec]
      change
        -(bDefectConeAction wait *ᵥ
          (bConeSign *ᵥ ((bDefectRun waits).adjugateᵀ *ᵥ state))) = _
      rw [induction]
      simp only [List.length_cons, bDefectConeRun, pow_succ]
      rw [Matrix.mulVec_smul]
      simp [mul_comm]

private theorem bridge_det_eq_bExteriorRow (middle : Matrix (Fin 3) (Fin 3) ℚ) :
    (bridge 27 middle).det =
      243 / 2 * (bridgeExteriorRow ⬝ᵥ (middle.adjugateᵀ *ᵥ exteriorSeed)) := by
  rw [bridge_det_eq_adjugate_first]
  norm_num [bridgeExteriorRow, exteriorSeed, dotProduct, Fin.sum_univ_succ]
  ring

private theorem bridgeExteriorRow_bSafe_signed
    (phase : Bool) (wait : Nat) (state : Fin 3 → ℚ) :
    bridgeExteriorRow ⬝ᵥ ((bSafeAtom phase wait).adjugateᵀ *ᵥ state) =
      signed_bSafe_left phase wait ⬝ᵥ (bConeSign *ᵥ state) := by
  rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
  simp only [signed_bSafe_left]
  rw [Matrix.vecMul_vecMul, bConeSign_sq, Matrix.vecMul_one]

private theorem bSafe_bDefectRun_bSafe_state
    (leftPhase rightPhase : Bool) (leftWait rightWait : Nat) (waits : List Nat) :
    ((bSafeAtom leftPhase leftWait * bDefectRun waits *
          bSafeAtom rightPhase rightWait).adjugateᵀ *ᵥ exteriorSeed) =
      (bSafeAtom leftPhase leftWait).adjugateᵀ *ᵥ
        ((bDefectRun waits).adjugateᵀ *ᵥ
          ((bSafeAtom rightPhase rightWait).adjugateᵀ *ᵥ exteriorSeed)) := by
  simp only [Matrix.adjugate_mul_distrib, Matrix.transpose_mul, Matrix.mulVec_mulVec]
  rw [Matrix.mul_assoc]

/-- Every regular all-`b` safe/defect/safe bridge at deletion width three has nonzero
determinant, for an arbitrary number of residue-two atoms and arbitrary waits. -/
theorem bridge_bSafe_bDefectRun_bSafe_det_ne_zero
    (leftPhase rightPhase : Bool) (leftWait rightWait : Nat) (waits : List Nat)
    (leftRegular : RegularSafeLabel (.b, leftWait, leftPhase))
    (rightRegular : RegularSafeLabel (.b, rightWait, rightPhase)) :
    (bridge 27
      (bSafeAtom leftPhase leftWait * bDefectRun waits *
        bSafeAtom rightPhase rightWait)).det ≠ 0 := by
  let rightState :=
    (bSafeAtom rightPhase rightWait).adjugateᵀ *ᵥ exteriorSeed
  let coneState := bDefectConeRun waits (bConeSign *ᵥ rightState)
  have right_inside : InBDefectCone (bConeSign *ᵥ rightState) := by
    exact signed_bSafe_right_mem rightPhase rightWait rightRegular
  have cone_inside : InBDefectCone coneState :=
    bDefectConeRun_preserves waits (bConeSign *ᵥ rightState) right_inside
  have run_signed :
      bConeSign *ᵥ ((bDefectRun waits).adjugateᵀ *ᵥ rightState) =
        (-1 : ℚ) ^ waits.length • coneState := by
    exact signed_bDefectRun waits rightState
  rw [bridge_det_eq_bExteriorRow, bSafe_bDefectRun_bSafe_state,
    bridgeExteriorRow_bSafe_signed, run_signed]
  rw [dotProduct_smul]
  have parity_nonzero : (-1 : ℚ) ^ waits.length ≠ 0 := by positivity
  cases leftPhase
  · have left_negative : signed_bSafe_left false leftWait ⬝ᵥ coneState < 0 :=
      signed_bSafe_left_zero_neg leftWait coneState cone_inside
    exact mul_ne_zero (by norm_num) (mul_ne_zero parity_nonzero (ne_of_lt left_negative))
  · simp only [RegularSafeLabel] at leftRegular
    have left_positive : 0 < signed_bSafe_left true leftWait ⬝ᵥ coneState :=
      signed_bSafe_left_one_pos leftWait leftRegular coneState cone_inside
    exact mul_ne_zero (by norm_num) (mul_ne_zero parity_nonzero (ne_of_gt left_positive))

end MatrixMortality.ParabolicBlade
