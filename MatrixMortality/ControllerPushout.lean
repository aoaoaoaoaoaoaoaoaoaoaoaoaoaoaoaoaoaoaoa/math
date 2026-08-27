import MatrixMortality.SideNormal

/-!
# Finite-controller pushouts

A side-normal correspondence representation has two shared upper coordinates and one private
lower coordinate.  This file glues one private coordinate for each controller state and routes
it through an arbitrary deterministic transition.  Column action gives suffix control; the
transpose gives prefix control.
-/

namespace MatrixMortality

open scoped Matrix

/-- Two shared coordinates and one private lower coordinate per controller state. -/
abbrev ControllerIndex (State : Type*) := Fin 2 ⊕ State

/-- A deterministic finite controller over an alphabet. -/
abbrev ControllerTransition (State Symbol : Type*) := State → Symbol → State

/-- One side-normal role selected by a controller state and physical symbol. -/
abbrev ControllerRole (State Symbol : Type*) := State × Symbol

/-- The side-normal payload selected by a controlled role. -/
def controllerRoleMatrix (R : Type*) [CommRing R] {State Symbol : Type*}
    (upper : Symbol → List Bool) (lower : State → Symbol → List Bool)
    (role : ControllerRole State Symbol) : Matrix (Fin 3) (Fin 3) R :=
  sidePcpMatrix R (upper role.2) (lower role.1 role.2)

/-- Every controlled side-normal role is nonsingular over the rationals. -/
theorem controllerRoleMatrix_det_rat {State Symbol : Type*}
    (upper : Symbol → List Bool) (lower : State → Symbol → List Bool)
    (role : ControllerRole State Symbol) :
    (controllerRoleMatrix ℚ upper lower role).det =
      (3 : ℚ) ^ (upper role.2).length * (3 : ℚ) ^ (lower role.1 role.2).length := by
  rw [Matrix.det_fin_three]
  norm_num [controllerRoleMatrix, sidePcpMatrix, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  ring_nf

theorem controllerRoleMatrix_rank_rat {State Symbol : Type*}
    (upper : Symbol → List Bool) (lower : State → Symbol → List Bool)
    (role : ControllerRole State Symbol) :
    (controllerRoleMatrix ℚ upper lower role).rank = 3 := by
  apply Matrix.rank_of_isUnit
  rw [Matrix.isUnit_iff_isUnit_det, controllerRoleMatrix_det_rat]
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (pow_ne_zero _ (by norm_num)))

/-- Embed one side-normal vector at a controller state. -/
def controllerVector (R : Type*) [CommRing R] {State : Type*}
    [DecidableEq State] (state : State) (vector : Fin 3 → R) :
    ControllerIndex State → R
  | .inl index => ![vector 0, vector 2] index
  | .inr candidate => if candidate = state then vector 1 else 0

/-- Route every private lower channel through one deterministic controller transition. -/
def controllerMatrix (R : Type*) [CommRing R] {State Symbol : Type*}
    [DecidableEq State] (upper : Symbol → List Bool)
    (lower : State → Symbol → List Bool) (δ : ControllerTransition State Symbol)
    (symbol : Symbol) : Matrix (ControllerIndex State) (ControllerIndex State) R
  | .inl target, .inl source =>
      !![(1 : R), ternaryCode (upper symbol);
         0, (3 : R) ^ (upper symbol).length] target source
  | .inl target, .inr source => ![ternaryCode (lower source symbol), 0] target
  | .inr _, .inl _ => 0
  | .inr target, .inr source =>
      if δ source symbol = target then (3 : R) ^ (lower source symbol).length else 0

/-- The finite-controller pushout performs the selected role and routes its private channel. -/
theorem controllerMatrix_mulVec_controllerVector
    (R : Type*) [CommRing R] {State Symbol : Type*}
    [Fintype State] [DecidableEq State]
    (upper : Symbol → List Bool) (lower : State → Symbol → List Bool)
    (δ : ControllerTransition State Symbol) (symbol : Symbol) (state : State)
    (vector : Fin 3 → R) :
    controllerMatrix R upper lower δ symbol *ᵥ controllerVector R state vector =
      controllerVector R (δ state symbol)
        (controllerRoleMatrix R upper lower (state, symbol) *ᵥ vector) := by
  funext target
  cases target with
  | inl target =>
      fin_cases target <;>
        simp [controllerMatrix, controllerVector, controllerRoleMatrix, sidePcpMatrix,
          Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fintype.sum_sum_type]
      all_goals ring
  | inr target =>
      simp only [controllerMatrix, controllerVector, controllerRoleMatrix, sidePcpMatrix,
        Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
      rw [Finset.sum_eq_single state]
      · by_cases destination : δ state symbol = target
        · subst target
          simp [Fin.sum_univ_succ]
        · simp [destination, Ne.symm destination]
      · intro other _ other_ne
        simp [other_ne]
      · simp

/-- Prefix control is the transpose of the suffix-controlled pushout. -/
theorem controllerVector_vecMul_controllerMatrix_transpose
    (R : Type*) [CommRing R] {State Symbol : Type*}
    [Fintype State] [DecidableEq State]
    (upper : Symbol → List Bool) (lower : State → Symbol → List Bool)
    (δ : ControllerTransition State Symbol) (state : State)
    (vector : Fin 3 → R) (symbol : Symbol) :
    controllerVector R state vector ᵥ* (controllerMatrix R upper lower δ symbol)ᵀ =
      controllerVector R (δ state symbol)
        (controllerRoleMatrix R upper lower (state, symbol) *ᵥ vector) := by
  rw [Matrix.vecMul_transpose, controllerMatrix_mulVec_controllerVector]

/-- A controller-only transition: shared coordinates are fixed and private coordinates move. -/
def controllerStateMatrix (R : Type*) [CommRing R] {State : Type*}
    [DecidableEq State] (next : State → State) :
    Matrix (ControllerIndex State) (ControllerIndex State) R :=
  controllerMatrix R (fun _ : Unit => []) (fun _ _ => []) (fun state _ => next state) ()

theorem controllerStateMatrix_mulVec_controllerVector
    (R : Type*) [CommRing R] {State : Type*}
    [Fintype State] [DecidableEq State] (next : State → State)
    (state : State) (vector : Fin 3 → R) :
    controllerStateMatrix R next *ᵥ controllerVector R state vector =
      controllerVector R (next state) vector := by
  simpa [controllerStateMatrix, controllerRoleMatrix] using
    controllerMatrix_mulVec_controllerVector R
      (fun _ : Unit => []) (fun _ _ => []) (fun source _ => next source) () state vector

theorem controllerVector_map {R S State : Type*} [CommRing R] [CommRing S]
    [DecidableEq State] (hom : R →+* S) (state : State) (vector : Fin 3 → R) :
    hom ∘ controllerVector R state vector =
      controllerVector S state (hom ∘ vector) := by
  funext index
  rcases index with index | candidate
  · fin_cases index <;> simp [controllerVector]
  · by_cases active : candidate = state <;> simp [controllerVector, active]

theorem controllerMatrix_map {R S State Symbol : Type*} [CommRing R] [CommRing S]
    [DecidableEq State] (hom : R →+* S)
    (upper : Symbol → List Bool) (lower : State → Symbol → List Bool)
    (δ : ControllerTransition State Symbol) (symbol : Symbol) :
    (controllerMatrix R upper lower δ symbol).map hom =
      controllerMatrix S upper lower δ symbol := by
  ext target source
  rcases target with target | target <;> rcases source with source | source
  · fin_cases target <;> fin_cases source <;>
      simp [controllerMatrix]
    all_goals
      congr 1
      exact map_ofNat hom 3
  · fin_cases target <;>
      simp [controllerMatrix]
  · simp [controllerMatrix]
  · by_cases routed : δ source symbol = target
    · simp [controllerMatrix, routed]
      congr 1
      exact map_ofNat hom 3
    · simp [controllerMatrix, routed]

theorem controllerStateMatrix_map {R S State : Type*} [CommRing R] [CommRing S]
    [DecidableEq State] (hom : R →+* S) (next : State → State) :
    (controllerStateMatrix R next).map hom = controllerStateMatrix S next := by
  simpa [controllerStateMatrix] using
    controllerMatrix_map hom
      (fun _ : Unit => []) (fun _ _ => []) (fun state _ => next state) ()

/-- Decode from the right boundary, retaining the state seen by a further symbol on the left. -/
def controllerSuffixDecode {State Symbol : Type*}
    (δ : ControllerTransition State Symbol) :
    State → List Symbol → State × List (ControllerRole State Symbol)
  | terminal, [] => (terminal, [])
  | terminal, symbol :: word =>
      let decoded := controllerSuffixDecode δ terminal word
      (δ decoded.1 symbol, (decoded.1, symbol) :: decoded.2)

/-- The role word assigned by suffix control. -/
def controllerSuffixRoles {State Symbol : Type*}
    (δ : ControllerTransition State Symbol) (terminal : State) (word : List Symbol) :
    List (ControllerRole State Symbol) :=
  (controllerSuffixDecode δ terminal word).2

/-- Product of finite-controller matrices. -/
def controllerProduct (R : Type*) [CommRing R] {State Symbol : Type*}
    [Fintype State] [DecidableEq State] (upper : Symbol → List Bool)
    (lower : State → Symbol → List Bool) (δ : ControllerTransition State Symbol)
    (word : List Symbol) : Matrix (ControllerIndex State) (ControllerIndex State) R :=
  wordProduct (controllerMatrix R upper lower δ) word

/-- Product of the decoded side-normal roles. -/
def controllerRoleProduct (R : Type*) [CommRing R] {State Symbol : Type*}
    (upper : Symbol → List Bool) (lower : State → Symbol → List Bool)
    (word : List (ControllerRole State Symbol)) : Matrix (Fin 3) (Fin 3) R :=
  wordProduct (controllerRoleMatrix R upper lower) word

/-- Every suffix-controlled physical word obeys its total decoder. -/
theorem controllerProduct_mulVec_controllerVector
    (R : Type*) [CommRing R] {State Symbol : Type*}
    [Fintype State] [DecidableEq State]
    (upper : Symbol → List Bool) (lower : State → Symbol → List Bool)
    (δ : ControllerTransition State Symbol) (terminal : State) (word : List Symbol)
    (vector : Fin 3 → R) :
    controllerProduct R upper lower δ word *ᵥ controllerVector R terminal vector =
      controllerVector R (controllerSuffixDecode δ terminal word).1
        (controllerRoleProduct R upper lower (controllerSuffixRoles δ terminal word) *ᵥ
          vector) := by
  induction word with
  | nil =>
      simp [controllerProduct, controllerSuffixDecode, controllerSuffixRoles,
        controllerRoleProduct]
  | cons symbol word induction =>
      simp only [controllerProduct, wordProduct_cons]
      rw [← Matrix.mulVec_mulVec]
      change controllerMatrix R upper lower δ symbol *ᵥ
        (controllerProduct R upper lower δ word *ᵥ controllerVector R terminal vector) = _
      rw [induction, controllerMatrix_mulVec_controllerVector]
      simp only [controllerSuffixDecode, controllerSuffixRoles, controllerRoleProduct,
        wordProduct_cons, Matrix.mulVec_mulVec]

/-- Residual state after consuming a prefix-controlled word. -/
def controllerResidualFrom {State Symbol : Type*}
    (δ : ControllerTransition State Symbol) : State → List Symbol → State
  | state, [] => state
  | state, symbol :: word => controllerResidualFrom δ (δ state symbol) word

/-- Prefix-controlled roles in chronological order. -/
def controllerRolesFrom {State Symbol : Type*}
    (δ : ControllerTransition State Symbol) :
    State → List Symbol → List (ControllerRole State Symbol)
  | _, [] => []
  | state, symbol :: word =>
      (state, symbol) :: controllerRolesFrom δ (δ state symbol) word

/-- Prefix-controlled roles in matrix-product order. -/
def controllerDecodeFrom {State Symbol : Type*}
    (δ : ControllerTransition State Symbol) :
    State → List Symbol → List (ControllerRole State Symbol)
  | _, [] => []
  | state, symbol :: word =>
      controllerDecodeFrom δ (δ state symbol) word ++ [(state, symbol)]

theorem controllerResidualFrom_append {State Symbol : Type*}
    (δ : ControllerTransition State Symbol) (state : State) (left right : List Symbol) :
    controllerResidualFrom δ state (left ++ right) =
      controllerResidualFrom δ (controllerResidualFrom δ state left) right := by
  induction left generalizing state with
  | nil => rfl
  | cons symbol left induction =>
      simpa only [List.cons_append, controllerResidualFrom] using
        induction (δ state symbol)

theorem controllerRolesFrom_append {State Symbol : Type*}
    (δ : ControllerTransition State Symbol) (state : State) (left right : List Symbol) :
    controllerRolesFrom δ state (left ++ right) =
      controllerRolesFrom δ state left ++
        controllerRolesFrom δ (controllerResidualFrom δ state left) right := by
  induction left generalizing state with
  | nil => rfl
  | cons symbol left induction =>
      simp only [List.cons_append, controllerRolesFrom, List.cons_append,
        controllerResidualFrom]
      exact congrArg ((state, symbol) :: ·) (induction (δ state symbol))

theorem controllerDecodeFrom_eq_reverse_roles {State Symbol : Type*}
    (δ : ControllerTransition State Symbol) (state : State) (word : List Symbol) :
    controllerDecodeFrom δ state word = (controllerRolesFrom δ state word).reverse := by
  induction word generalizing state with
  | nil => rfl
  | cons symbol word induction =>
      simp only [controllerDecodeFrom, controllerRolesFrom, List.reverse_cons]
      rw [induction]

/-- Prefix-controlled products are transposes of the same finite-controller matrices. -/
def controllerTransposeProduct (R : Type*) [CommRing R] {State Symbol : Type*}
    [Fintype State] [DecidableEq State] (upper : Symbol → List Bool)
    (lower : State → Symbol → List Bool) (δ : ControllerTransition State Symbol)
    (word : List Symbol) : Matrix (ControllerIndex State) (ControllerIndex State) R :=
  wordProduct (fun symbol => (controllerMatrix R upper lower δ symbol)ᵀ) word

/-- Every prefix-controlled physical word obeys its total decoder. -/
theorem controllerVector_vecMul_transposeProduct
    (R : Type*) [CommRing R] {State Symbol : Type*}
    [Fintype State] [DecidableEq State]
    (upper : Symbol → List Bool) (lower : State → Symbol → List Bool)
    (δ : ControllerTransition State Symbol) (state : State) (vector : Fin 3 → R)
    (word : List Symbol) :
    controllerVector R state vector ᵥ* controllerTransposeProduct R upper lower δ word =
      controllerVector R (controllerResidualFrom δ state word)
        (controllerRoleProduct R upper lower (controllerDecodeFrom δ state word) *ᵥ vector) := by
  induction word generalizing state vector with
  | nil =>
      simp [controllerResidualFrom, controllerDecodeFrom, controllerTransposeProduct,
        controllerRoleProduct]
  | cons symbol word induction =>
      simp only [controllerTransposeProduct, wordProduct_cons]
      rw [← Matrix.vecMul_vecMul, controllerVector_vecMul_controllerMatrix_transpose]
      change controllerVector R (δ state symbol)
          (controllerRoleMatrix R upper lower (state, symbol) *ᵥ vector) ᵥ*
        controllerTransposeProduct R upper lower δ word = _
      rw [induction]
      simp only [controllerResidualFrom, controllerDecodeFrom]
      simp [controllerRoleProduct, wordProduct_append, Matrix.mulVec_mulVec]

end MatrixMortality
