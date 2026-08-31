import MatrixMortality.TransverseSeparatedAtlas
import MatrixMortality.BranchingRecognizer
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Algebra.Field.ZMod

/-!
# The distinct-data infinite-carrier candidate cannot recognize `bcbc`

Three exact terminal forks force the candidate's terminal boundary row to vanish whenever the
source parameter is nonzero. The proof reduces the fork blocks to two-dimensional quotient
actions and certifies irreducibility from a commutator determinant whose two nonconstant factors
have no rational roots. At source zero, one explicit terminal/nonterminal word-product collision
supplies the missing contradiction. Hence no row and column give the candidate the `bcbc` paired
zero language at any rational parameter.
-/

namespace MatrixMortality
namespace TransverseSeparatedForkNoGo

open scoped Matrix Polynomial

open Polynomial

open BranchingHistory PeriodicHistory TransverseInfiniteAtlas TransverseSeparatedAtlas

/-- A state on the first two coordinates of the separated carrier. -/
abbrev PlaneState := Fin 2 → ℚ

/-- A rational endomorphism of the first-two-coordinate quotient. -/
abbrev PlaneMatrix := Matrix (Fin 2) (Fin 2) ℚ

/-- Project a three-state carrier onto its first two coordinates. -/
def planeHead (state : State) : PlaneState := fun coordinate => state coordinate.castSucc

/-- The fixed two-stroke prefix shared by the terminal fork controls. -/
def terminalPrefixControl : List PairedControl :=
  BranchingRecognizer.historyControl [strokeCBC, strokeBCB]

/-- The control obtained by appending a binary `bcbc` fork and its terminal toggle. -/
def terminalForkControl (bits : List Bool) : List PairedControl :=
  BranchingRecognizer.historyControl ([strokeCBC, strokeBCB] ++ bcbcFork bits) ++ [.toggle]

/-- The control spelling of one flat null fork block. -/
def flatForkControl : List PairedControl :=
  BranchingRecognizer.historyControl flatBlock

/-- The control spelling of one nested null fork block. -/
def nestedForkControl : List PairedControl :=
  BranchingRecognizer.historyControl nestedBlock

/-- The separated-generator product of the fixed terminal prefix. -/
def prefixMatrix (source : ℚ) : ControlMatrix :=
  wordProduct (TransverseSeparatedAtlas.generator source) terminalPrefixControl

/-- The separated-generator product of one flat fork block. -/
def flatForkMatrix (source : ℚ) : ControlMatrix :=
  wordProduct (TransverseSeparatedAtlas.generator source) flatForkControl

/-- The separated-generator product of one nested fork block. -/
def nestedForkMatrix (source : ℚ) : ControlMatrix :=
  wordProduct (TransverseSeparatedAtlas.generator source) nestedForkControl

/-- The first-two-coordinate action of the `bbb` stroke. -/
def bbbQuotient (source : ℚ) : PlaneMatrix :=
  !![1 - 3 * source, -source * (2 * source - 1);
     source - 1, -source]

/-- The first-two-coordinate action of the `bcb` stroke. -/
def bcbQuotient (source : ℚ) : PlaneMatrix :=
  !![2, 3 * source;
     2 * (source - 1), -3 * source]

/-- The first-two-coordinate action of the `cbb` stroke. -/
def cbbQuotient (source : ℚ) : PlaneMatrix :=
  !![1 - 7 * source, -source * (4 * source - 1);
     2, 2 * source]

/-- The first-two-coordinate action of the `cbc` stroke. -/
def cbcQuotient (source : ℚ) : PlaneMatrix :=
  !![-3 * (4 * source - 1), -8 * source ^ 2 - 5 * source + 1;
     6, 2 * (2 * source + 1)]

/-- The first-two-coordinate action of one flat fork block. -/
def flatQuotient (source : ℚ) : PlaneMatrix :=
  bbbQuotient source * cbcQuotient source * bbbQuotient source * cbcQuotient source

/-- The first-two-coordinate action of one nested fork block. -/
def nestedQuotient (source : ℚ) : PlaneMatrix :=
  bbbQuotient source * bcbQuotient source * cbbQuotient source * cbcQuotient source

private theorem planeHead_strokeBBB (source : ℚ) (state : State) :
    planeHead (wordProduct (TransverseSeparatedAtlas.generator source)
      (BranchingRecognizer.strokeControl strokeBBB) *ᵥ state) =
      bbbQuotient source *ᵥ planeHead state := by
  ext coordinate
  fin_cases coordinate <;>
    simp [planeHead, BranchingRecognizer.strokeControl, strokeBBB, stroke₃, wordProduct,
      TransverseSeparatedAtlas.generator, TransverseLineAtlas.generator, separatedData,
      toggle, data,
      dataInput, dataProjection, bbbQuotient, Matrix.mulVec, Matrix.mul_apply, dotProduct,
      Fin.sum_univ_succ] <;>
    ring

private theorem planeHead_strokeBCB (source : ℚ) (state : State) :
    planeHead (wordProduct (TransverseSeparatedAtlas.generator source)
      (BranchingRecognizer.strokeControl strokeBCB) *ᵥ state) =
      bcbQuotient source *ᵥ planeHead state := by
  ext coordinate
  fin_cases coordinate <;>
    simp [planeHead, BranchingRecognizer.strokeControl, strokeBCB, stroke₃, wordProduct,
      TransverseSeparatedAtlas.generator, TransverseLineAtlas.generator, separatedData, separator,
      toggle, data,
      dataInput, dataProjection, bcbQuotient, Matrix.mulVec, Matrix.mul_apply, dotProduct,
      Fin.sum_univ_succ] <;>
    ring

private theorem planeHead_strokeCBB (source : ℚ) (state : State) :
    planeHead (wordProduct (TransverseSeparatedAtlas.generator source)
      (BranchingRecognizer.strokeControl strokeCBB) *ᵥ state) =
      cbbQuotient source *ᵥ planeHead state := by
  ext coordinate
  fin_cases coordinate <;>
    simp [planeHead, BranchingRecognizer.strokeControl, strokeCBB, stroke₃, wordProduct,
      TransverseSeparatedAtlas.generator, TransverseLineAtlas.generator, separatedData, separator,
      toggle, data,
      dataInput, dataProjection, cbbQuotient, Matrix.mulVec, Matrix.mul_apply, dotProduct,
      Fin.sum_univ_succ] <;>
    ring

private theorem planeHead_strokeCBC (source : ℚ) (state : State) :
    planeHead (wordProduct (TransverseSeparatedAtlas.generator source)
      (BranchingRecognizer.strokeControl strokeCBC) *ᵥ state) =
      cbcQuotient source *ᵥ planeHead state := by
  ext coordinate
  fin_cases coordinate <;>
    simp [planeHead, BranchingRecognizer.strokeControl, strokeCBC, stroke₃, wordProduct,
      TransverseSeparatedAtlas.generator, TransverseLineAtlas.generator, separatedData, separator,
      toggle, data,
      dataInput, dataProjection, cbcQuotient, Matrix.mulVec, Matrix.mul_apply, dotProduct,
      Fin.sum_univ_succ] <;>
    ring

theorem planeHead_flatForkMatrix_mulVec (source : ℚ) (state : State) :
    planeHead (flatForkMatrix source *ᵥ state) =
      flatQuotient source *ᵥ planeHead state := by
  rw [flatForkMatrix]
  simp only [flatForkControl, flatBlock, BranchingRecognizer.historyControl,
    wordProduct_append, wordProduct_nil, Matrix.mul_one]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    planeHead_strokeBBB, planeHead_strokeCBC, planeHead_strokeBBB,
    planeHead_strokeCBC]
  simp only [flatQuotient, ← Matrix.mulVec_mulVec]

theorem planeHead_nestedForkMatrix_mulVec (source : ℚ) (state : State) :
    planeHead (nestedForkMatrix source *ᵥ state) =
      nestedQuotient source *ᵥ planeHead state := by
  rw [nestedForkMatrix]
  simp only [nestedForkControl, nestedBlock, BranchingRecognizer.historyControl,
    wordProduct_append, wordProduct_nil, Matrix.mul_one]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    planeHead_strokeBBB, planeHead_strokeBCB, planeHead_strokeCBB,
    planeHead_strokeCBC]
  simp only [nestedQuotient, ← Matrix.mulVec_mulVec]

theorem bbbQuotient_det (source : ℚ) :
    (bbbQuotient source).det = 2 * source ^ 3 := by
  rw [Matrix.det_fin_two]
  simp [bbbQuotient]
  ring

theorem bcbQuotient_det (source : ℚ) :
    (bcbQuotient source).det = -6 * source ^ 2 := by
  rw [Matrix.det_fin_two]
  simp [bcbQuotient]
  ring

theorem cbbQuotient_det (source : ℚ) :
    (cbbQuotient source).det = -6 * source ^ 2 := by
  rw [Matrix.det_fin_two]
  simp [cbbQuotient]
  ring

theorem cbcQuotient_det (source : ℚ) :
    (cbcQuotient source).det = 18 * source := by
  rw [Matrix.det_fin_two]
  simp [cbcQuotient]
  ring

theorem flatQuotient_det (source : ℚ) :
    (flatQuotient source).det = 1296 * source ^ 8 := by
  simp only [flatQuotient, Matrix.det_mul, bbbQuotient_det, cbcQuotient_det]
  ring

theorem nestedQuotient_det (source : ℚ) :
    (nestedQuotient source).det = 1296 * source ^ 8 := by
  simp only [nestedQuotient, Matrix.det_mul, bbbQuotient_det, bcbQuotient_det,
    cbbQuotient_det, cbcQuotient_det]
  ring

/-- The cubic rational-root-free factor in the fork-commutator determinant. -/
def cubicFactor (source : ℚ) : ℚ :=
  8 * source ^ 3 - 23 * source ^ 2 + 11 * source - 2

/-- The degree-nine rational-root-free factor in the fork-commutator determinant. -/
def nonicFactor (source : ℚ) : ℚ :=
  5120 * source ^ 9 + 2080 * source ^ 8 - 24796 * source ^ 7 +
    50600 * source ^ 6 - 52007 * source ^ 5 + 33053 * source ^ 4 -
      12661 * source ^ 3 + 2956 * source ^ 2 - 400 * source + 24

theorem forkQuotient_commutator_det (source : ℚ) :
    (flatQuotient source * nestedQuotient source -
        nestedQuotient source * flatQuotient source).det =
      -144 * source ^ 6 * cubicFactor source ^ 2 * nonicFactor source := by
  rw [Matrix.det_fin_two]
  simp [flatQuotient, nestedQuotient, bbbQuotient, bcbQuotient, cbbQuotient,
    cbcQuotient, cubicFactor, nonicFactor]
  ring

private theorem noRatRoot_of_mod_noRoot
    (modulus : Nat) [Fact modulus.Prime]
    (polynomial : ℤ[X])
    (leading_mod_ne : ((polynomial.leadingCoeff : ℤ) : ZMod modulus) ≠ 0)
    (mod_no_root : ∀ residue : ZMod modulus,
      (polynomial.map (Int.castRingHom (ZMod modulus))).eval residue ≠ 0)
    (source : ℚ) :
    aeval source polynomial ≠ 0 := by
  intro source_root
  let numerator : ℤ := IsFractionRing.num ℤ source
  let denominator : ℤ := IsFractionRing.den ℤ source
  have denominator_dvd := den_dvd_of_is_root source_root
  have denominator_mod_ne : (denominator : ZMod modulus) ≠ 0 := by
    intro denominator_mod_zero
    obtain ⟨quotient, leading_eq⟩ := denominator_dvd
    have leading_mod_zero : (polynomial.leadingCoeff : ZMod modulus) = 0 := by
      rw [leading_eq, Int.cast_mul]
      change (denominator : ZMod modulus) * (quotient : ZMod modulus) = 0
      rw [denominator_mod_zero, zero_mul]
    exact leading_mod_ne leading_mod_zero
  have scaled_root := num_isRoot_scaleRoots_of_aeval_eq_zero source_root
  have mapped_scaled_root :=
    Polynomial.IsRoot.map (f := Int.castRingHom (ZMod modulus)) scaled_root
  have mapped_leading_ne :
      (Int.castRingHom (ZMod modulus)) polynomial.leadingCoeff ≠ 0 :=
    leading_mod_ne
  rw [Polynomial.map_scaleRoots polynomial denominator _ mapped_leading_ne] at mapped_scaled_root
  let residue : ZMod modulus := (denominator : ZMod modulus)⁻¹ * numerator
  have denominator_mul_residue :
      (denominator : ZMod modulus) * residue = numerator := by
    dsimp [residue]
    rw [← mul_assoc, mul_inv_cancel₀ denominator_mod_ne, one_mul]
  have mapped_root_eq :
      ((polynomial.map (Int.castRingHom (ZMod modulus))).scaleRoots
          (denominator : ZMod modulus)).eval (numerator : ZMod modulus) = 0 := by
    simpa [numerator, denominator] using mapped_scaled_root.eq_zero
  have scaled_value := Polynomial.scaleRoots_eval_mul
    (polynomial.map (Int.castRingHom (ZMod modulus))) residue
      (denominator : ZMod modulus)
  rw [denominator_mul_residue, mapped_root_eq] at scaled_value
  have denominator_power_ne :
      (denominator : ZMod modulus) ^
        (polynomial.map (Int.castRingHom (ZMod modulus))).natDegree ≠ 0 :=
    pow_ne_zero _ denominator_mod_ne
  have residue_root :
      (polynomial.map (Int.castRingHom (ZMod modulus))).eval residue = 0 :=
    (mul_eq_zero.mp scaled_value.symm).resolve_left denominator_power_ne
  exact mod_no_root residue residue_root

private noncomputable def integerCubic : ℤ[X] :=
  8 * X ^ 3 - 23 * X ^ 2 + 11 * X - 2

private theorem integerCubic_leadingCoeff : integerCubic.leadingCoeff = 8 := by
  rw [Polynomial.leadingCoeff]
  have degree : integerCubic.natDegree = 3 := by
    unfold integerCubic
    compute_degree <;> norm_num
  rw [degree]
  simp [integerCubic, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X]

private theorem integerCubic_eval_mod7 (residue : ZMod 7) :
    (integerCubic.map (Int.castRingHom (ZMod 7))).eval residue =
      8 * residue ^ 3 - 23 * residue ^ 2 + 11 * residue - 2 := by
  simp [integerCubic]

private theorem integerCubic_mod7_no_root (residue : ZMod 7) :
    (integerCubic.map (Int.castRingHom (ZMod 7))).eval residue ≠ 0 := by
  rw [integerCubic_eval_mod7]
  fin_cases residue <;> decide

theorem cubicFactor_ne_zero (source : ℚ) : cubicFactor source ≠ 0 := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  have root_ne := noRatRoot_of_mod_noRoot 7 integerCubic
    (by rw [integerCubic_leadingCoeff]; decide) integerCubic_mod7_no_root source
  simpa [integerCubic, cubicFactor, aeval_def] using root_ne

private noncomputable def integerNonic : ℤ[X] :=
  5120 * X ^ 9 + 2080 * X ^ 8 - 24796 * X ^ 7 + 50600 * X ^ 6 -
    52007 * X ^ 5 + 33053 * X ^ 4 - 12661 * X ^ 3 + 2956 * X ^ 2 -
      400 * X + 24

private theorem integerNonic_leadingCoeff : integerNonic.leadingCoeff = 5120 := by
  rw [Polynomial.leadingCoeff]
  have degree : integerNonic.natDegree = 9 := by
    unfold integerNonic
    compute_degree <;> norm_num
  rw [degree]
  simp [integerNonic, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X]

private theorem integerNonic_eval_mod13 (residue : ZMod 13) :
    (integerNonic.map (Int.castRingHom (ZMod 13))).eval residue =
      5120 * residue ^ 9 + 2080 * residue ^ 8 - 24796 * residue ^ 7 +
        50600 * residue ^ 6 - 52007 * residue ^ 5 + 33053 * residue ^ 4 -
          12661 * residue ^ 3 + 2956 * residue ^ 2 - 400 * residue + 24 := by
  simp [integerNonic]

private theorem integerNonic_mod13_no_root (residue : ZMod 13) :
    (integerNonic.map (Int.castRingHom (ZMod 13))).eval residue ≠ 0 := by
  rw [integerNonic_eval_mod13]
  fin_cases residue <;> decide

theorem nonicFactor_ne_zero (source : ℚ) : nonicFactor source ≠ 0 := by
  let _ : Fact (Nat.Prime 13) := ⟨by decide⟩
  have root_ne := noRatRoot_of_mod_noRoot 13 integerNonic
    (by rw [integerNonic_leadingCoeff]; decide) integerNonic_mod13_no_root source
  simpa [integerNonic, nonicFactor, aeval_def] using root_ne

theorem forkQuotient_commutator_det_ne_zero {source : ℚ} (source_ne : source ≠ 0) :
    (flatQuotient source * nestedQuotient source -
        nestedQuotient source * flatQuotient source).det ≠ 0 := by
  rw [forkQuotient_commutator_det]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero _ source_ne))
      (pow_ne_zero _ (cubicFactor_ne_zero source)))
    (nonicFactor_ne_zero source)

theorem flatQuotient_det_ne_zero {source : ℚ} (source_ne : source ≠ 0) :
    (flatQuotient source).det ≠ 0 := by
  rw [flatQuotient_det]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ source_ne)

private theorem vector_eq_smul_of_common_annihilator
    (row column vector : PlaneState)
    (row_ne : row ≠ 0) (column_ne : column ≠ 0)
    (column_zero : row ⬝ᵥ column = 0)
    (vector_zero : row ⬝ᵥ vector = 0) :
    ∃ scalar : ℚ, vector = scalar • column := by
  have column_equation :
      row 0 * column 0 + row 1 * column 1 = 0 := by
    simpa [dotProduct, Fin.sum_univ_succ] using column_zero
  have vector_equation :
      row 0 * vector 0 + row 1 * vector 1 = 0 := by
    simpa [dotProduct, Fin.sum_univ_succ] using vector_zero
  by_cases row_first_zero : row 0 = 0
  · have row_second_ne : row 1 ≠ 0 := by
      intro row_second_zero
      apply row_ne
      funext coordinate
      fin_cases coordinate
      · exact row_first_zero
      · exact row_second_zero
    have column_second_zero : column 1 = 0 := by
      rw [row_first_zero, zero_mul, zero_add] at column_equation
      exact (mul_eq_zero.mp column_equation).resolve_left row_second_ne
    have vector_second_zero : vector 1 = 0 := by
      rw [row_first_zero, zero_mul, zero_add] at vector_equation
      exact (mul_eq_zero.mp vector_equation).resolve_left row_second_ne
    have column_first_ne : column 0 ≠ 0 := by
      intro column_first_zero
      apply column_ne
      funext coordinate
      fin_cases coordinate
      · exact column_first_zero
      · exact column_second_zero
    refine ⟨vector 0 / column 0, ?_⟩
    funext coordinate
    fin_cases coordinate
    · simp [column_first_ne]
    · simp [vector_second_zero, column_second_zero]
  · have column_second_ne : column 1 ≠ 0 := by
      intro column_second_zero
      have column_first_zero : column 0 = 0 := by
        rw [column_second_zero, mul_zero, add_zero] at column_equation
        exact (mul_eq_zero.mp column_equation).resolve_left row_first_zero
      apply column_ne
      funext coordinate
      fin_cases coordinate
      · exact column_first_zero
      · exact column_second_zero
    have cross : vector 0 * column 1 = vector 1 * column 0 := by
      apply mul_left_cancel₀ row_first_zero
      linear_combination column 1 * vector_equation - vector 1 * column_equation
    refine ⟨vector 1 / column 1, ?_⟩
    funext coordinate
    fin_cases coordinate
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div]
      change vector 0 = vector 1 * column 0 / column 1
      exact (eq_div_iff column_second_ne).mpr cross
    · simp [column_second_ne]

theorem planeRow_eq_zero_of_irreducible_pair
    (first second : PlaneMatrix) (row column : PlaneState)
    (commutator_ne : (first * second - second * first).det ≠ 0)
    (column_ne : column ≠ 0)
    (column_zero : row ⬝ᵥ column = 0)
    (first_zero : row ⬝ᵥ (first *ᵥ column) = 0)
    (second_zero : row ⬝ᵥ (second *ᵥ column) = 0) :
    row = 0 := by
  by_contra row_ne
  obtain ⟨firstScalar, first_eigen⟩ :=
    vector_eq_smul_of_common_annihilator row column (first *ᵥ column)
      row_ne column_ne column_zero first_zero
  obtain ⟨secondScalar, second_eigen⟩ :=
    vector_eq_smul_of_common_annihilator row column (second *ᵥ column)
      row_ne column_ne column_zero second_zero
  have commutator_zero : (first * second - second * first) *ᵥ column = 0 := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      second_eigen, first_eigen, Matrix.mulVec_smul, Matrix.mulVec_smul,
      first_eigen, second_eigen]
    simp [smul_smul, mul_comm]
  exact column_ne (Matrix.eq_zero_of_mulVec_eq_zero commutator_ne commutator_zero)

/-- Three annihilations under a pair with nonsingular commutator force one of the two boundary
vectors to vanish. -/
theorem planeRow_eq_zero_or_column_eq_zero_of_irreducible_pair
    (first second : PlaneMatrix) (row column : PlaneState)
    (commutator_ne : (first * second - second * first).det ≠ 0)
    (column_zero : row ⬝ᵥ column = 0)
    (first_zero : row ⬝ᵥ (first *ᵥ column) = 0)
    (second_zero : row ⬝ᵥ (second *ᵥ column) = 0) :
    row = 0 ∨ column = 0 := by
  by_cases column_ne : column = 0
  · exact Or.inr column_ne
  · exact Or.inl (planeRow_eq_zero_of_irreducible_pair first second row column
      commutator_ne column_ne column_zero first_zero second_zero)

theorem terminalForkControl_eq (bits : List Bool) :
    terminalForkControl bits = terminalPrefixControl ++
      BranchingRecognizer.historyControl (bcbcFork bits) ++ [.toggle] := by
  rw [terminalForkControl, BranchingRecognizer.historyControl_append]
  rfl

theorem terminalForkControl_decode (bits : List Bool) :
    decodePairedWord (terminalForkControl bits) = bcbcTerminalFork bits := by
  have decoded := BranchingRecognizer.suffixDecode_historyControl
    ([strokeCBC, strokeBCB] ++ bcbcFork bits)
  have decodedWord := congrArg Prod.snd decoded
  simpa [decodePairedWord, terminalForkControl, bcbcTerminalFork,
    bcbcForkRoles_eq_tileHistory, tileHistory, List.map_append] using decodedWord

theorem terminalForkControl_paired_zero (bits : List Bool) :
    pairedCoefficient ℚ 3 bcbcBody (terminalForkControl bits) = 0 := by
  rw [pairedCoefficient_eq_sideCoefficient, terminalForkControl_decode]
  exact (sideCoefficient_eq_zero_iff_terminal_match_rat 3 bcbcBody _).mpr
    (bcbcTerminalFork_match bits)

theorem terminalForkControl_false :
    terminalForkControl [false] =
      terminalPrefixControl ++ flatForkControl ++ [.toggle] := by
  simp [terminalForkControl_eq, flatForkControl, bcbcFork, forkBlock,
    List.append_assoc]

theorem terminalForkControl_false_false :
    terminalForkControl [false, false] =
      terminalPrefixControl ++ flatForkControl ++ flatForkControl ++ [.toggle] := by
  simp [terminalForkControl_eq, flatForkControl, bcbcFork, forkBlock,
    BranchingRecognizer.historyControl_append, List.append_assoc]

theorem terminalForkControl_false_true :
    terminalForkControl [false, true] =
      terminalPrefixControl ++ flatForkControl ++ nestedForkControl ++ [.toggle] := by
  simp [terminalForkControl_eq, flatForkControl, nestedForkControl, bcbcFork, forkBlock,
    BranchingRecognizer.historyControl_append, List.append_assoc]

theorem terminalPrefixControl_paired_ne_zero :
    pairedCoefficient ℚ 3 bcbcBody terminalPrefixControl ≠ 0 := by
  rw [pairedCoefficient_eq_sideCoefficient]
  intro source_zero
  have terminal_match :=
    (sideCoefficient_eq_zero_iff_terminal_match_rat 3 bcbcBody _).mp source_zero
  have not_terminal :
      spell (nearyUpper 3) (decodePairedWord terminalPrefixControl) ++ nearyMarker 3 ≠
        spell (nearyLower 3 bcbcBody) (decodePairedWord terminalPrefixControl) := by
    decide
  exact not_terminal terminal_match

/-- The one-letter data-`b` control used when the terminal quotient column vanishes. -/
def singleDataControl : List PairedControl := [.data .b]

theorem singleDataControl_paired_ne_zero :
    pairedCoefficient ℚ 3 bcbcBody singleDataControl ≠ 0 := by
  rw [pairedCoefficient_eq_sideCoefficient]
  intro source_zero
  have terminal_match :=
    (sideCoefficient_eq_zero_iff_terminal_match_rat 3 bcbcBody _).mp source_zero
  have not_terminal :
      spell (nearyUpper 3) (decodePairedWord singleDataControl) ++ nearyMarker 3 ≠
        spell (nearyLower 3 bcbcBody) (decodePairedWord singleDataControl) := by
    decide
  exact not_terminal terminal_match

/-- The nonterminal control whose source-zero product equals the canonical terminal product. -/
def zeroSourceCollisionControl : List PairedControl :=
  [.data .c, .toggle, .data .b, .data .c, .data .b,
    .data .c, .data .b, .data .b, .data .b]

theorem zeroSourceCollisionControl_paired_ne_zero :
    pairedCoefficient ℚ 3 bcbcBody zeroSourceCollisionControl ≠ 0 := by
  rw [pairedCoefficient_eq_sideCoefficient]
  intro source_zero
  have terminal_match :=
    (sideCoefficient_eq_zero_iff_terminal_match_rat 3 bcbcBody _).mp source_zero
  have not_terminal :
      spell (nearyUpper 3) (decodePairedWord zeroSourceCollisionControl) ++ nearyMarker 3 ≠
        spell (nearyLower 3 bcbcBody) (decodePairedWord zeroSourceCollisionControl) := by
    decide
  exact not_terminal terminal_match

theorem zeroSource_wordProduct_collision :
    wordProduct (TransverseSeparatedAtlas.generator 0) zeroSourceCollisionControl =
      wordProduct (TransverseSeparatedAtlas.generator 0) bcbcTerminalControl := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [zeroSourceCollisionControl, bcbcTerminalControl, wordProduct,
      TransverseSeparatedAtlas.generator, TransverseLineAtlas.generator, separatedData,
      separator, toggle, data, dataInput, dataProjection, Matrix.mul_apply,
      Fin.sum_univ_succ]

/-- Apply the terminal toggle to a right boundary column. -/
def terminalColumn (column : State) : State := toggle *ᵥ column

/-- Push a left boundary row through the fixed terminal prefix. -/
def prefixRow (source : ℚ) (row : State) : State := row ᵥ* prefixMatrix source

/-- Push the prefixed boundary row through one flat fork block. -/
def flatBoundaryRow (source : ℚ) (row : State) : State :=
  prefixRow source row ᵥ* flatForkMatrix source

/-- The first-two-coordinate projection of a toggled terminal column. -/
def planeTerminalColumn (column : State) : PlaneState := planeHead (terminalColumn column)

/-- The first-two-coordinate projection of a prefixed boundary row. -/
def planePrefixRow (source : ℚ) (row : State) : PlaneState :=
  planeHead (prefixRow source row)

/-- The first-two-coordinate projection of a flat-fork boundary row. -/
def planeFlatBoundaryRow (source : ℚ) (row : State) : PlaneState :=
  planeHead (flatBoundaryRow source row)

theorem prefixRow_third_zero (source : ℚ) (row : State) :
    prefixRow source row 2 = 0 := by
  simp [prefixRow, prefixMatrix, terminalPrefixControl, BranchingRecognizer.historyControl,
    BranchingRecognizer.strokeControl, strokeCBC, strokeBCB, stroke₃, wordProduct,
    TransverseSeparatedAtlas.generator, TransverseLineAtlas.generator, separatedData,
    separator, toggle, data, dataInput, dataProjection, Matrix.vecMul, dotProduct,
    Matrix.mul_apply, Fin.sum_univ_succ]

theorem flatBoundaryRow_third_zero (source : ℚ) (row : State) :
    flatBoundaryRow source row 2 = 0 := by
  simp [flatBoundaryRow, flatForkMatrix, flatForkControl, flatBlock,
    BranchingRecognizer.historyControl, BranchingRecognizer.strokeControl, strokeBBB,
    strokeCBC, stroke₃, wordProduct, TransverseSeparatedAtlas.generator,
    TransverseLineAtlas.generator, separatedData, separator, toggle, data, dataInput,
    dataProjection, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ]

theorem planeFlatBoundaryRow_eq (source : ℚ) (row : State) :
    planeFlatBoundaryRow source row =
      planePrefixRow source row ᵥ* flatQuotient source := by
  ext coordinate
  fin_cases coordinate <;>
    simp [planeFlatBoundaryRow, flatBoundaryRow, planePrefixRow, planeHead, prefixRow,
      prefixMatrix, terminalPrefixControl, flatForkMatrix, flatForkControl, flatBlock,
      BranchingRecognizer.historyControl, BranchingRecognizer.strokeControl, strokeBBB,
      strokeCBC, strokeBCB, stroke₃, wordProduct, TransverseSeparatedAtlas.generator,
      TransverseLineAtlas.generator, separatedData, separator, toggle, data, dataInput,
      dataProjection, flatQuotient, bbbQuotient, cbcQuotient, Matrix.vecMul, dotProduct,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

private theorem dotProduct_eq_planeHead
    (left right : State) (left_third_zero : left 2 = 0) :
    left ⬝ᵥ right = planeHead left ⬝ᵥ planeHead right := by
  simp [dotProduct, planeHead, Fin.sum_univ_succ, left_third_zero]

theorem wordProduct_terminalFork_false (source : ℚ) :
    wordProduct (TransverseSeparatedAtlas.generator source) (terminalForkControl [false]) =
      prefixMatrix source * flatForkMatrix source * toggle := by
  rw [terminalForkControl_false, wordProduct_append, wordProduct_append]
  simp [prefixMatrix, flatForkMatrix, wordProduct, TransverseSeparatedAtlas.generator,
    TransverseLineAtlas.generator]

theorem wordProduct_terminalFork_false_false (source : ℚ) :
    wordProduct (TransverseSeparatedAtlas.generator source)
        (terminalForkControl [false, false]) =
      prefixMatrix source * flatForkMatrix source * flatForkMatrix source * toggle := by
  rw [terminalForkControl_false_false, wordProduct_append, wordProduct_append,
    wordProduct_append]
  simp [prefixMatrix, flatForkMatrix, wordProduct, TransverseSeparatedAtlas.generator,
    TransverseLineAtlas.generator]

theorem wordProduct_terminalFork_false_true (source : ℚ) :
    wordProduct (TransverseSeparatedAtlas.generator source)
        (terminalForkControl [false, true]) =
      prefixMatrix source * flatForkMatrix source * nestedForkMatrix source * toggle := by
  rw [terminalForkControl_false_true, wordProduct_append, wordProduct_append,
    wordProduct_append]
  simp [prefixMatrix, flatForkMatrix, nestedForkMatrix, wordProduct,
    TransverseSeparatedAtlas.generator, TransverseLineAtlas.generator]

theorem terminalForkCoefficient_false (source : ℚ) (row column : State) :
    linearCoefficient (TransverseSeparatedAtlas.generator source) row column
        (terminalForkControl [false]) =
      planeFlatBoundaryRow source row ⬝ᵥ planeTerminalColumn column := by
  rw [linearCoefficient, wordProduct_terminalFork_false]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.dotProduct_mulVec]
  exact dotProduct_eq_planeHead _ _ (flatBoundaryRow_third_zero source row)

theorem terminalForkCoefficient_false_false (source : ℚ) (row column : State) :
    linearCoefficient (TransverseSeparatedAtlas.generator source) row column
        (terminalForkControl [false, false]) =
      planeFlatBoundaryRow source row ⬝ᵥ
        (flatQuotient source *ᵥ planeTerminalColumn column) := by
  rw [linearCoefficient, wordProduct_terminalFork_false_false]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
  change flatBoundaryRow source row ⬝ᵥ
    (flatForkMatrix source *ᵥ terminalColumn column) = _
  rw [dotProduct_eq_planeHead _ _ (flatBoundaryRow_third_zero source row),
    planeHead_flatForkMatrix_mulVec]
  rfl

theorem terminalForkCoefficient_false_true (source : ℚ) (row column : State) :
    linearCoefficient (TransverseSeparatedAtlas.generator source) row column
        (terminalForkControl [false, true]) =
      planeFlatBoundaryRow source row ⬝ᵥ
        (nestedQuotient source *ᵥ planeTerminalColumn column) := by
  rw [linearCoefficient, wordProduct_terminalFork_false_true]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
  change flatBoundaryRow source row ⬝ᵥ
    (nestedForkMatrix source *ᵥ terminalColumn column) = _
  rw [dotProduct_eq_planeHead _ _ (flatBoundaryRow_third_zero source row),
    planeHead_nestedForkMatrix_mulVec]
  rfl

theorem singleData_target_zero_of_planeTerminalColumn_eq_zero
    (source : ℚ) (row column : State)
    (terminalColumn_zero : planeTerminalColumn column = 0) :
    linearCoefficient (TransverseSeparatedAtlas.generator source) row column
      singleDataControl = 0 := by
  have column_first_zero := congrFun terminalColumn_zero 0
  have column_second_zero := congrFun terminalColumn_zero 1
  simp [planeTerminalColumn, planeHead, terminalColumn, toggle, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] at column_first_zero column_second_zero
  simp [linearCoefficient, singleDataControl, wordProduct,
    TransverseSeparatedAtlas.generator, TransverseLineAtlas.generator, separatedData, data,
    dataInput, dataProjection, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    column_first_zero, column_second_zero]

theorem terminalPrefix_target_zero_of_prefixRow_eq_zero
    (source : ℚ) (row column : State) (prefix_zero : prefixRow source row = 0) :
    linearCoefficient (TransverseSeparatedAtlas.generator source) row column
      terminalPrefixControl = 0 := by
  rw [linearCoefficient]
  change row ⬝ᵥ (prefixMatrix source *ᵥ column) = 0
  rw [Matrix.dotProduct_mulVec]
  change prefixRow source row ⬝ᵥ column = 0
  rw [prefix_zero]
  simp

theorem no_bcbc_sameZero_at_zero (row column : State) :
    ¬(∀ word,
      linearCoefficient (TransverseSeparatedAtlas.generator 0) row column word = 0 ↔
        pairedCoefficient ℚ 3 bcbcBody word = 0) := by
  intro same_zero
  have terminal_target_zero :
      linearCoefficient (TransverseSeparatedAtlas.generator 0) row column
        bcbcTerminalControl = 0 :=
    (same_zero bcbcTerminalControl).mpr bcbc_terminal_nearFork.1
  have collision_target_zero :
      linearCoefficient (TransverseSeparatedAtlas.generator 0) row column
        zeroSourceCollisionControl = 0 := by
    rw [linearCoefficient, zeroSource_wordProduct_collision]
    exact terminal_target_zero
  exact zeroSourceCollisionControl_paired_ne_zero
    ((same_zero zeroSourceCollisionControl).mp collision_target_zero)

theorem no_bcbc_sameZero_of_source_ne_zero
    {source : ℚ} (source_ne : source ≠ 0) (row column : State) :
    ¬(∀ word,
      linearCoefficient (TransverseSeparatedAtlas.generator source) row column word = 0 ↔
        pairedCoefficient ℚ 3 bcbcBody word = 0) := by
  intro same_zero
  have flat_zero :
      planeFlatBoundaryRow source row ⬝ᵥ planeTerminalColumn column = 0 := by
    rw [← terminalForkCoefficient_false]
    exact (same_zero (terminalForkControl [false])).mpr
      (terminalForkControl_paired_zero [false])
  have flat_flat_zero :
      planeFlatBoundaryRow source row ⬝ᵥ
        (flatQuotient source *ᵥ planeTerminalColumn column) = 0 := by
    rw [← terminalForkCoefficient_false_false]
    exact (same_zero (terminalForkControl [false, false])).mpr
      (terminalForkControl_paired_zero [false, false])
  have flat_nested_zero :
      planeFlatBoundaryRow source row ⬝ᵥ
        (nestedQuotient source *ᵥ planeTerminalColumn column) = 0 := by
    rw [← terminalForkCoefficient_false_true]
    exact (same_zero (terminalForkControl [false, true])).mpr
      (terminalForkControl_paired_zero [false, true])
  have boundary_zero_or_column_zero :
      planeFlatBoundaryRow source row = 0 ∨ planeTerminalColumn column = 0 :=
    planeRow_eq_zero_or_column_eq_zero_of_irreducible_pair
      (flatQuotient source) (nestedQuotient source)
      (planeFlatBoundaryRow source row) (planeTerminalColumn column)
      (forkQuotient_commutator_det_ne_zero source_ne) flat_zero flat_flat_zero flat_nested_zero
  rcases boundary_zero_or_column_zero with boundary_zero | terminal_plane_zero
  · have plane_prefix_times_flat :
      planePrefixRow source row ᵥ* flatQuotient source = 0 := by
      rw [← planeFlatBoundaryRow_eq, boundary_zero]
    have plane_prefix_zero : planePrefixRow source row = 0 :=
      Matrix.eq_zero_of_vecMul_eq_zero (flatQuotient_det_ne_zero source_ne)
        plane_prefix_times_flat
    have prefix_zero : prefixRow source row = 0 := by
      funext coordinate
      fin_cases coordinate
      · exact congrFun plane_prefix_zero 0
      · exact congrFun plane_prefix_zero 1
      · exact prefixRow_third_zero source row
    have target_zero := terminalPrefix_target_zero_of_prefixRow_eq_zero
      source row column prefix_zero
    exact terminalPrefixControl_paired_ne_zero
      ((same_zero terminalPrefixControl).mp target_zero)
  · have target_zero := singleData_target_zero_of_planeTerminalColumn_eq_zero
      source row column terminal_plane_zero
    exact singleDataControl_paired_ne_zero
      ((same_zero singleDataControl).mp target_zero)

/-- No row and column turn the separated-data infinite-carrier candidate into a same-zero
representation of the fixed `bcbc` paired source, at any rational source parameter. -/
theorem no_bcbc_sameZero (source : ℚ) (row column : State) :
    ¬(∀ word,
      linearCoefficient (TransverseSeparatedAtlas.generator source) row column word = 0 ↔
        pairedCoefficient ℚ 3 bcbcBody word = 0) := by
  by_cases source_zero : source = 0
  · subst source
    exact no_bcbc_sameZero_at_zero row column
  · exact no_bcbc_sameZero_of_source_ne_zero source_zero row column

end TransverseSeparatedForkNoGo
end MatrixMortality
