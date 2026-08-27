import MatrixMortality.ReturnFamily
import MatrixMortality.ReverseEdge

/-!
# Pure-cubic return collapse

When an ambient action satisfies `A³ = N I` with `N ≠ 0`, every return is a nonzero scalar
multiple of one of its first three returns.  The infinite return family therefore has exactly the
same zero products as a finite three-generator interface family.
-/

namespace MatrixMortality.CubicReturn

open scoped Matrix

variable {K Large Small : Type*} [Field K]
  [Fintype Large] [DecidableEq Large]
  [Fintype Small] [DecidableEq Small]

/-- Residue of a wait modulo the pure-cubic period. -/
def residue (wait : Nat) : Fin 3 :=
  ⟨wait % 3, Nat.mod_lt wait (by omega)⟩

/-- The three residue returns retained by a pure-cubic ambient action. -/
def residueReturn
    (ambient : Square Large K) (input : Matrix Large Small K)
    (output : Matrix Small Large K) (index : Fin 3) : Square Small K :=
  ReturnFamily.returnMatrix ambient input output index

/-- A pure-cubic ambient power is its residue power times the corresponding scalar power. -/
theorem pow_eq_smul_residue
    (ambient : Square Large K) (scalar : K)
    (cubic : ambient ^ 3 = scalar • 1) (wait : Nat) :
    ambient ^ wait = scalar ^ (wait / 3) • ambient ^ (wait % 3) := by
  conv_lhs => rw [← Nat.div_add_mod wait 3]
  rw [pow_add, show ambient ^ (3 * (wait / 3)) = (ambient ^ 3) ^ (wait / 3) by
    rw [pow_mul], cubic]
  simp [smul_pow]

omit [Fintype Small] [DecidableEq Small] in
/-- Every pure-cubic return is a nonzero scalar multiple of one of the first three returns. -/
theorem returnMatrix_eq_smul_residue
    (ambient : Square Large K) (input : Matrix Large Small K)
    (output : Matrix Small Large K) (scalar : K)
    (cubic : ambient ^ 3 = scalar • 1) (wait : Nat) :
    ReturnFamily.returnMatrix ambient input output wait =
      scalar ^ (wait / 3) • residueReturn ambient input output (residue wait) := by
  rw [ReturnFamily.returnMatrix, pow_eq_smul_residue ambient scalar cubic wait]
  simp [residueReturn, residue, ReturnFamily.returnMatrix,
    Matrix.mul_smul, Matrix.smul_mul]

/-- Arbitrary return products reduce exactly to their residue word and one common nonzero
scalar. -/
theorem returnProduct_eq_smul_residues
    (ambient : Square Large K) (input : Matrix Large Small K)
    (output : Matrix Small Large K) (scalar : K)
    (cubic : ambient ^ 3 = scalar • 1) (waits : List Nat) :
    ReturnFamily.returnProduct ambient input output waits =
      (waits.map fun wait => scalar ^ (wait / 3)).prod •
        wordProduct (residueReturn ambient input output) (waits.map residue) := by
  change wordProduct (ReturnFamily.returnMatrix ambient input output) waits = _
  have generators :
      ReturnFamily.returnMatrix ambient input output =
        fun wait => scalar ^ (wait / 3) •
          (residueReturn ambient input output ∘ residue) wait := by
    funext wait
    exact returnMatrix_eq_smul_residue ambient input output scalar cubic wait
  rw [generators, wordProduct_smulMatrix, wordProduct_comp]

/-- The infinite pure-cubic return family and its finite residue triple have identical zero
languages. -/
theorem exists_returnProduct_eq_zero_iff_residue
    (ambient : Square Large K) (input : Matrix Large Small K)
    (output : Matrix Small Large K) (scalar : K)
    (scalar_ne_zero : scalar ≠ 0) (cubic : ambient ^ 3 = scalar • 1) :
    (∃ waits, ReturnFamily.returnProduct ambient input output waits = 0) ↔
      ∃ word, wordProduct (residueReturn ambient input output) word = 0 := by
  constructor
  · rintro ⟨waits, product_zero⟩
    rw [returnProduct_eq_smul_residues ambient input output scalar cubic] at product_zero
    have scale_ne_zero :
        (waits.map fun wait => scalar ^ (wait / 3)).prod ≠ 0 := by
      apply List.prod_ne_zero
      intro zero_mem
      obtain ⟨wait, _, power_zero⟩ := List.mem_map.mp zero_mem
      exact (pow_ne_zero _ scalar_ne_zero) power_zero
    exact ⟨waits.map residue,
      (smul_eq_zero.mp product_zero).resolve_left scale_ne_zero⟩
  · rintro ⟨word, product_zero⟩
    let waits := word.map Fin.val
    refine ⟨waits, ?_⟩
    have residue_val (index : Fin 3) : residue index = index := by
      apply Fin.ext
      simp [residue, Nat.mod_eq_of_lt index.isLt]
    have residues_eq : waits.map residue = word := by
      simp [waits, List.map_map, Function.comp_def, residue_val]
    rw [returnProduct_eq_smul_residues ambient input output scalar cubic, residues_eq,
      product_zero, smul_zero]

/-- A split physical pair with pure-cubic ambient action is mortal exactly when the finite
three-return family is mortal. -/
theorem pairGenerator_isMortal_iff_residue
    [Nonempty Large]
    (ambient : Square Large K) (input : Matrix Large Small K)
    (output : Matrix Small Large K)
    (inputLeftInverse : Matrix Small Large K)
    (outputRightInverse : Matrix Large Small K)
    (ambient_unit : IsUnit ambient)
    (left_inverse : inputLeftInverse * input = 1)
    (right_inverse : output * outputRightInverse = 1)
    (scalar : K) (scalar_ne_zero : scalar ≠ 0)
    (cubic : ambient ^ 3 = scalar • 1) :
    IsMortal (ReturnFamily.pairGenerator ambient (input * output)) ↔
      ∃ word, wordProduct (residueReturn ambient input output) word = 0 := by
  rw [ReturnFamily.pairGenerator_isMortal_iff ambient input output
    inputLeftInverse outputRightInverse ambient_unit left_inverse right_inverse]
  exact exists_returnProduct_eq_zero_iff_residue ambient input output scalar
    scalar_ne_zero cubic

/-! ## The one-singular normal form -/

/-- Normalized projective involution in the pure one-singular cubic residue. -/
def pureInvolution (mu : ℚ) : Square (Fin 2) ℚ :=
  !![0, mu; 1, 0]

/-- In the pure one-singular normal form `(P R, P, P J_mu)`, both exceptional scalars of the
reverse-edge compiler are `mu⁻¹`. Thus every such instance with `mu ≠ 0` is already generic. -/
theorem pureOneSingular_reverseEdgeScalars
    (P : Square (Fin 2) ℚ) (P_unit : IsUnit P)
    (mu : ℚ) (mu_ne : mu ≠ 0) :
    let J := pureInvolution mu
    let row : Fin 2 → ℚ := ![1, 1]
    let source : Fin 2 → ℚ := ![1, 0]
    let column := P *ᵥ source
    ReverseEdge.alpha (P * J) row column = mu⁻¹ ∧
      ReverseEdge.beta P (P * J) row column = mu⁻¹ := by
  dsimp only
  let J := pureInvolution mu
  let first : Fin 2 → ℚ := ![1, 0]
  let second : Fin 2 → ℚ := ![0, 1]
  let row : Fin 2 → ℚ := ![1, 1]
  let column := P *ᵥ first
  have J_unit : IsUnit J := by
    rw [Matrix.isUnit_iff_isUnit_det]
    apply isUnit_iff_ne_zero.mpr
    simp [J, pureInvolution, Matrix.det_fin_two, mu_ne]
  have H_unit : IsUnit (P * J) := P_unit.mul J_unit
  have pulled_action :
      (P * J) *ᵥ (mu⁻¹ • second) = column := by
    have J_action : J *ᵥ (mu⁻¹ • second) = first := by
      ext i
      fin_cases i <;>
        simp [J, pureInvolution, first, second, Matrix.mulVec,
          dotProduct, Fin.sum_univ_succ, mu_ne]
    calc
      (P * J) *ᵥ (mu⁻¹ • second) = P *ᵥ (J *ᵥ (mu⁻¹ • second)) :=
        (Matrix.mulVec_mulVec (mu⁻¹ • second) P J).symm
      _ = P *ᵥ first := congrArg (fun vector => P *ᵥ vector) J_action
      _ = column := rfl
  have pulled_eq :
      ReverseEdge.pulledColumn (P * J) column = mu⁻¹ • second := by
    exact nonsingInv_mulVec_eq_of_mulVec_eq H_unit pulled_action
  have first_action :
      (P * J) *ᵥ (mu⁻¹ • first) = P *ᵥ (mu⁻¹ • second) := by
    have J_action : J *ᵥ (mu⁻¹ • first) = mu⁻¹ • second := by
      ext i
      fin_cases i <;>
        simp [J, pureInvolution, first, second, Matrix.mulVec,
          dotProduct, Fin.sum_univ_succ]
    calc
      (P * J) *ᵥ (mu⁻¹ • first) = P *ᵥ (J *ᵥ (mu⁻¹ • first)) :=
        (Matrix.mulVec_mulVec (mu⁻¹ • first) P J).symm
      _ = P *ᵥ (mu⁻¹ • second) :=
        congrArg (fun vector => P *ᵥ vector) J_action
  have first_eq :
      ReverseEdge.firstVector P (P * J) column = mu⁻¹ • first := by
    rw [ReverseEdge.firstVector, pulled_eq]
    exact nonsingInv_mulVec_eq_of_mulVec_eq H_unit first_action
  constructor
  · rw [ReverseEdge.alpha, pulled_eq]
    simp [second, dotProduct, Fin.sum_univ_succ]
  · rw [ReverseEdge.beta, first_eq]
    simp [first, dotProduct, Fin.sum_univ_succ]

end MatrixMortality.CubicReturn
