import MatrixMortality.LinearRepresentation

/-!
# The two-slot CHHN packing

Five three-state generators occupy one root slot and two ordered payload pairs.  The CHHN
generator trade exposes them through three six-state matrices.  This file owns the packing and
the linear-independence argument behind its finite Hankel certificates.
-/

namespace MatrixMortality

open scoped Matrix

/-- The five source slots of the two-slot CHHN packing. -/
inductive CHHNSlot where
  | root
  | leftLeading
  | leftTrailing
  | rightLeading
  | rightTrailing
  deriving DecidableEq, Fintype, Repr

/-- The four payload slots, excluding the distinguished root. -/
inductive CHHNPayloadSlot where
  | leftLeading
  | leftTrailing
  | rightLeading
  | rightTrailing
  deriving DecidableEq, Fintype, Repr

/-- Embed a payload slot into the five-slot packing. -/
def CHHNPayloadSlot.toSlot : CHHNPayloadSlot → CHHNSlot
  | .leftLeading => .leftLeading
  | .leftTrailing => .leftTrailing
  | .rightLeading => .rightLeading
  | .rightTrailing => .rightTrailing

/-- The three physical controls of the packed family. -/
inductive CHHNControl where
  | shift
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- The six-state carrier, retained as its two native three-state blocks. -/
abbrev CHHNPackedState := Sum (Fin 3) (Fin 3)

/-- Join two three-state vectors into one packed vector. -/
def chhnPairVector {R : Type*} (left right : Fin 3 → R) :
    CHHNPackedState → R :=
  Sum.elim left right

/-- The cyclic shift exposing the root matrix. -/
def chhnShift {R : Type*} [CommRing R] (root : Matrix (Fin 3) (Fin 3) R) :
    Matrix CHHNPackedState CHHNPackedState R :=
  Matrix.fromBlocks 0 root 1 0

/-- One payload block holding an ordered pair of source matrices. -/
def chhnPayload {R : Type*} [CommRing R]
    (leading trailing : Matrix (Fin 3) (Fin 3) R) :
    Matrix CHHNPackedState CHHNPackedState R :=
  Matrix.fromBlocks leading trailing 0 0

/-- The three packed generators emitted from one five-slot assignment. -/
def chhnPackedGenerator {R : Type*} [CommRing R]
    (source : CHHNSlot → Matrix (Fin 3) (Fin 3) R) :
    CHHNControl → Matrix CHHNPackedState CHHNPackedState R
  | .shift => chhnShift (source .root)
  | .left => chhnPayload (source .leftLeading) (source .leftTrailing)
  | .right => chhnPayload (source .rightLeading) (source .rightTrailing)

/-- Packed boundary row supported on the root block. -/
def chhnPackedRow {R : Type*} [Zero R] (row : Fin 3 → R) : CHHNPackedState → R :=
  chhnPairVector row 0

/-- Packed boundary column supported on the root block. -/
def chhnPackedColumn {R : Type*} [Zero R] (column : Fin 3 → R) :
    CHHNPackedState → R :=
  chhnPairVector column 0

theorem chhnPairVector_vecMul_shift {R : Type*} [CommRing R]
    (root : Matrix (Fin 3) (Fin 3) R) (left right : Fin 3 → R) :
    chhnPairVector left right ᵥ* chhnShift root =
      chhnPairVector right (left ᵥ* root) := by
  ext index
  cases index <;>
    simp [chhnPairVector, chhnShift, Matrix.vecMul, Matrix.dotProduct, Matrix.one_apply]

theorem chhnPairVector_vecMul_payload {R : Type*} [CommRing R]
    (leading trailing : Matrix (Fin 3) (Fin 3) R) (left right : Fin 3 → R) :
    chhnPairVector left right ᵥ* chhnPayload leading trailing =
      chhnPairVector (left ᵥ* leading) (left ᵥ* trailing) := by
  ext index
  cases index <;>
    simp [chhnPairVector, chhnPayload, Matrix.vecMul, Matrix.dotProduct]

theorem chhnPairVector_vecMul_payload_shift {R : Type*} [CommRing R]
    (root leading trailing : Matrix (Fin 3) (Fin 3) R) (left right : Fin 3 → R) :
    chhnPairVector left right ᵥ* (chhnPayload leading trailing * chhnShift root) =
      chhnPairVector (left ᵥ* trailing) ((left ᵥ* leading) ᵥ* root) := by
  rw [← Matrix.vecMul_vecMul, chhnPairVector_vecMul_payload,
    chhnPairVector_vecMul_shift]

theorem chhnPairVector_vecMul_shift_sq {R : Type*} [CommRing R]
    (root : Matrix (Fin 3) (Fin 3) R) (left right : Fin 3 → R) :
    chhnPairVector left right ᵥ* (chhnShift root * chhnShift root) =
      chhnPairVector (left ᵥ* root) (right ᵥ* root) := by
  rw [← Matrix.vecMul_vecMul, chhnPairVector_vecMul_shift,
    chhnPairVector_vecMul_shift]

theorem chhnPairVector_vecMul_payload_shift_sq {R : Type*} [CommRing R]
    (root leading trailing : Matrix (Fin 3) (Fin 3) R) (left right : Fin 3 → R) :
    chhnPairVector left right ᵥ*
        (chhnPayload leading trailing * (chhnShift root * chhnShift root)) =
      chhnPairVector ((left ᵥ* leading) ᵥ* root)
        ((left ᵥ* trailing) ᵥ* root) := by
  rw [← Matrix.vecMul_vecMul, chhnPairVector_vecMul_payload,
    chhnPairVector_vecMul_shift_sq]

theorem smul_vecMul {K : Type*} [Field K]
    (scalar : K) (vector : Fin 3 → K) (matrix : Matrix (Fin 3) (Fin 3) K) :
    (scalar • vector) ᵥ* matrix = scalar • (vector ᵥ* matrix) := by
  ext index
  simp only [Matrix.vecMul, Matrix.dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

theorem chhnShift_mulVec_pairVector {R : Type*} [CommRing R]
    (root : Matrix (Fin 3) (Fin 3) R) (left right : Fin 3 → R) :
    chhnShift root *ᵥ chhnPairVector left right =
      chhnPairVector (root *ᵥ right) left := by
  ext index
  cases index <;>
    simp [chhnPairVector, chhnShift, Matrix.mulVec, Matrix.dotProduct, Matrix.one_apply]

theorem chhnPayload_mulVec_pairVector {R : Type*} [CommRing R]
    (leading trailing : Matrix (Fin 3) (Fin 3) R) (left right : Fin 3 → R) :
    chhnPayload leading trailing *ᵥ chhnPairVector left right =
      chhnPairVector (leading *ᵥ left + trailing *ᵥ right) 0 := by
  ext index
  cases index <;>
    simp [chhnPairVector, chhnPayload, Matrix.mulVec, Matrix.dotProduct]

/-! ## Six-vector independence kernels -/

theorem chhn_root_rows_linearIndependent
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (e a₁ a₂ a₃ a₄ : V) (μ κ₁ κ₃ : K) (μ_ne_zero : μ ≠ 0)
    (basis : LinearIndependent K ![e, a₂, a₄]) :
    LinearIndependent K
      ![(e, 0), (0, μ • e), (a₁, a₂), (a₃, a₄),
        (a₂, κ₁ • e), (a₄, κ₃ • e)] := by
  rw [Fintype.linearIndependent_iff] at basis ⊢
  intro coefficients combination_zero index
  have first_zero := congrArg Prod.fst combination_zero
  have second_zero := congrArg Prod.snd combination_zero
  simp [Fin.sum_univ_succ] at first_zero second_zero
  change coefficients 0 • e +
    (coefficients 2 • a₁ + (coefficients 3 • a₃ +
      (coefficients 4 • a₂ + coefficients 5 • a₄))) = 0 at first_zero
  change coefficients 1 • μ • e +
    (coefficients 2 • a₂ + (coefficients 3 • a₄ +
      (coefficients 4 • κ₁ • e + coefficients 5 • κ₃ • e))) = 0 at second_zero
  have second_basis_zero :
      (coefficients 1 * μ + coefficients 4 * κ₁ + coefficients 5 * κ₃) • e +
        coefficients 2 • a₂ + coefficients 3 • a₄ = 0 := by
    calc
      _ = coefficients 1 • μ • e +
          (coefficients 2 • a₂ + (coefficients 3 • a₄ +
            (coefficients 4 • κ₁ • e + coefficients 5 • κ₃ • e))) := by
        module
      _ = 0 := second_zero
  have second_coefficients := basis
    ![coefficients 1 * μ + coefficients 4 * κ₁ + coefficients 5 * κ₃,
      coefficients 2, coefficients 3]
    (by simpa [Fin.sum_univ_succ, add_assoc] using second_basis_zero)
  have coefficient_two : coefficients 2 = 0 := second_coefficients 1
  have coefficient_three : coefficients 3 = 0 := second_coefficients 2
  have first_basis_zero :
      coefficients 0 • e + coefficients 4 • a₂ + coefficients 5 • a₄ = 0 := by
    simp [coefficient_two, coefficient_three] at first_zero
    calc
      _ = coefficients 0 • e +
          (coefficients 4 • a₂ + coefficients 5 • a₄) := by module
      _ = 0 := first_zero
  have first_coefficients := basis ![coefficients 0, coefficients 4, coefficients 5]
    (by simpa [Fin.sum_univ_succ, add_assoc] using first_basis_zero)
  have coefficient_zero : coefficients 0 = 0 := first_coefficients 0
  have coefficient_four : coefficients 4 = 0 := first_coefficients 1
  have coefficient_five : coefficients 5 = 0 := first_coefficients 2
  have coefficient_one : coefficients 1 = 0 := by
    have scalar_zero := second_coefficients 0
    simp [coefficient_four, coefficient_five, mul_eq_zero, μ_ne_zero] at scalar_zero
    exact scalar_zero
  fin_cases index <;> assumption

theorem chhn_leading_rows_linearIndependent
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (e a₀ a₂ a₃ a₄ : V) (μ : K)
    (left_basis : LinearIndependent K ![e, a₀, a₂])
    (right_basis : LinearIndependent K ![a₀, a₂, a₄]) :
    LinearIndependent K
      ![(e, 0), (0, a₀), (μ • e, a₂), (a₃, a₄),
        (a₀, 0), (a₂, μ • a₀)] := by
  rw [Fintype.linearIndependent_iff] at left_basis right_basis ⊢
  intro coefficients combination_zero index
  have first_zero := congrArg Prod.fst combination_zero
  have second_zero := congrArg Prod.snd combination_zero
  simp [Fin.sum_univ_succ] at first_zero second_zero
  change coefficients 0 • e +
    (coefficients 2 • μ • e + (coefficients 3 • a₃ +
      (coefficients 4 • a₀ + coefficients 5 • a₂))) = 0 at first_zero
  change coefficients 1 • a₀ +
    (coefficients 2 • a₂ +
      (coefficients 3 • a₄ + coefficients 5 • μ • a₀)) = 0 at second_zero
  have second_basis_zero :
      (coefficients 1 + coefficients 5 * μ) • a₀ +
        coefficients 2 • a₂ + coefficients 3 • a₄ = 0 := by
    calc
      _ = coefficients 1 • a₀ +
          (coefficients 2 • a₂ +
            (coefficients 3 • a₄ + coefficients 5 • μ • a₀)) := by
        module
      _ = 0 := second_zero
  have second_coefficients := right_basis
    ![coefficients 1 + coefficients 5 * μ, coefficients 2, coefficients 3]
    (by simpa [Fin.sum_univ_succ, add_assoc] using second_basis_zero)
  have coefficient_two : coefficients 2 = 0 := second_coefficients 1
  have coefficient_three : coefficients 3 = 0 := second_coefficients 2
  have first_basis_zero :
      coefficients 0 • e + coefficients 4 • a₀ + coefficients 5 • a₂ = 0 := by
    simp [coefficient_two, coefficient_three] at first_zero
    calc
      _ = coefficients 0 • e +
          (coefficients 4 • a₀ + coefficients 5 • a₂) := by module
      _ = 0 := first_zero
  have first_coefficients := left_basis ![coefficients 0, coefficients 4, coefficients 5]
    (by simpa [Fin.sum_univ_succ, add_assoc] using first_basis_zero)
  have coefficient_zero : coefficients 0 = 0 := first_coefficients 0
  have coefficient_four : coefficients 4 = 0 := first_coefficients 1
  have coefficient_five : coefficients 5 = 0 := first_coefficients 2
  have coefficient_one : coefficients 1 = 0 := by
    simpa [coefficient_five] using second_coefficients 0
  fin_cases index <;> assumption

theorem chhn_trailing_rows_linearIndependent
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (e a₀ a₁ a₁₀ : V) (μ : K) (μ_ne_zero : μ ≠ 0)
    (basis : LinearIndependent K ![e, a₀, a₁₀]) :
    LinearIndependent K
      ![(e, 0), (0, a₀), (a₀, 0), (a₁, μ • e),
        (μ • e, a₁₀), (a₁₀, μ • a₀)] := by
  rw [Fintype.linearIndependent_iff] at basis ⊢
  intro coefficients combination_zero index
  have first_zero := congrArg Prod.fst combination_zero
  have second_zero := congrArg Prod.snd combination_zero
  simp [Fin.sum_univ_succ] at first_zero second_zero
  change coefficients 0 • e +
    (coefficients 2 • a₀ + (coefficients 3 • a₁ +
      (coefficients 4 • μ • e + coefficients 5 • a₁₀))) = 0 at first_zero
  change coefficients 1 • a₀ +
    (coefficients 3 • μ • e +
      (coefficients 4 • a₁₀ + coefficients 5 • μ • a₀)) = 0 at second_zero
  have second_basis_zero :
      (coefficients 3 * μ) • e +
        (coefficients 1 + coefficients 5 * μ) • a₀ +
        coefficients 4 • a₁₀ = 0 := by
    calc
      _ = coefficients 1 • a₀ +
          (coefficients 3 • μ • e +
            (coefficients 4 • a₁₀ + coefficients 5 • μ • a₀)) := by
        module
      _ = 0 := second_zero
  have second_coefficients := basis
    ![coefficients 3 * μ, coefficients 1 + coefficients 5 * μ, coefficients 4]
    (by simpa [Fin.sum_univ_succ, add_assoc] using second_basis_zero)
  have coefficient_three : coefficients 3 = 0 :=
    (mul_eq_zero.mp (second_coefficients 0)).resolve_right μ_ne_zero
  have coefficient_four : coefficients 4 = 0 := second_coefficients 2
  have first_basis_zero :
      coefficients 0 • e + coefficients 2 • a₀ + coefficients 5 • a₁₀ = 0 := by
    simp [coefficient_three, coefficient_four] at first_zero
    calc
      _ = coefficients 0 • e +
          (coefficients 2 • a₀ + coefficients 5 • a₁₀) := by module
      _ = 0 := first_zero
  have first_coefficients := basis ![coefficients 0, coefficients 2, coefficients 5]
    (by simpa [Fin.sum_univ_succ, add_assoc] using first_basis_zero)
  have coefficient_zero : coefficients 0 = 0 := first_coefficients 0
  have coefficient_two : coefficients 2 = 0 := first_coefficients 1
  have coefficient_five : coefficients 5 = 0 := first_coefficients 2
  have coefficient_one : coefficients 1 = 0 := by
    simpa [coefficient_five] using second_coefficients 1
  fin_cases index <;> assumption

theorem chhn_split_columns_linearIndependent
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (c h k : V) (basis : LinearIndependent K ![c, h, k]) :
    LinearIndependent K
      ![(c, 0), (0, c), (h, 0), (k, 0), (0, h), (0, k)] := by
  rw [Fintype.linearIndependent_iff] at basis ⊢
  intro coefficients combination_zero index
  have first_zero := congrArg Prod.fst combination_zero
  have second_zero := congrArg Prod.snd combination_zero
  simp [Fin.sum_univ_succ] at first_zero second_zero
  change coefficients 0 • c +
    (coefficients 2 • h + coefficients 3 • k) = 0 at first_zero
  change coefficients 1 • c +
    (coefficients 4 • h + coefficients 5 • k) = 0 at second_zero
  have first_coefficients := basis ![coefficients 0, coefficients 2, coefficients 3]
    (by simpa [Fin.sum_univ_succ, add_assoc] using first_zero)
  have second_coefficients := basis ![coefficients 1, coefficients 4, coefficients 5]
    (by simpa [Fin.sum_univ_succ, add_assoc] using second_zero)
  fin_cases index
  · exact first_coefficients 0
  · exact second_coefficients 0
  · exact first_coefficients 1
  · exact first_coefficients 2
  · exact second_coefficients 1
  · exact second_coefficients 2

/-! ## Reindexed finite certificates -/

/-- Split a packed vector into its two native blocks. -/
def chhnSplitLinear (K : Type*) [Semiring K] :
    (CHHNPackedState → K) →ₗ[K] (Fin 3 → K) × (Fin 3 → K) where
  toFun vector := (vector ∘ Sum.inl, vector ∘ Sum.inr)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem chhnSplitLinear_pairVector
    (K : Type*) [Semiring K] (left right : Fin 3 → K) :
    chhnSplitLinear K (chhnPairVector left right) = (left, right) :=
  rfl

/-- Join two native blocks into one packed vector. -/
def chhnJoinLinear (K : Type*) [Semiring K] :
    ((Fin 3 → K) × (Fin 3 → K)) →ₗ[K] (CHHNPackedState → K) where
  toFun pair := chhnPairVector pair.1 pair.2
  map_add' left right := by
    ext index
    cases index <;> rfl
  map_smul' scalar pair := by
    ext index
    cases index <;> rfl

theorem chhnJoinLinear_injective
    (K : Type*) [Semiring K] : Function.Injective (chhnJoinLinear K) := by
  intro left right equal
  apply Prod.ext
  · funext index
    exact congrFun equal (Sum.inl index)
  · funext index
    exact congrFun equal (Sum.inr index)

/-- Six values indexed by the native two-block carrier. -/
def chhnSextet {α : Type*} (x₀ x₁ x₂ x₃ x₄ x₅ : α) : CHHNPackedState → α
  | .inl index => ![x₀, x₁, x₂] index
  | .inr index => ![x₃, x₄, x₅] index

/-- Join six native block pairs into six packed vectors. -/
def chhnJoinedSextet {K : Type*} [Semiring K]
    (x₀ x₁ x₂ x₃ x₄ x₅ : (Fin 3 → K) × (Fin 3 → K)) :
    CHHNPackedState → (CHHNPackedState → K) :=
  chhnJoinLinear K ∘ chhnSextet x₀ x₁ x₂ x₃ x₄ x₅

theorem chhn_pairVector_family_linearIndependent
    {K : Type*} [Field K]
    (x₀ x₁ x₂ x₃ x₄ x₅ : (Fin 3 → K) × (Fin 3 → K))
    (independent : LinearIndependent K ![x₀, x₁, x₂, x₃, x₄, x₅]) :
    LinearIndependent K (chhnJoinedSextet x₀ x₁ x₂ x₃ x₄ x₅) := by
  have reindexed :
      LinearIndependent K
        (chhnSextet x₀ x₁ x₂ x₃ x₄ x₅) := by
    let reindex : CHHNPackedState ≃ Fin 6 := finSumFinEquiv
    apply (linearIndependent_equiv' reindex ?_).2 independent
    funext index
    cases index with
    | inl localIndex => fin_cases localIndex <;> rfl
    | inr localIndex => fin_cases localIndex <;> rfl
  exact reindexed.map' (chhnJoinLinear K) <|
    LinearMap.ker_eq_bot.mpr (chhnJoinLinear_injective K)

/-- Root-separator prefix family. -/
def chhnRootPrefixes : CHHNPackedState → List CHHNControl :=
  chhnSextet [] [.shift] [.left] [.right] [.left, .shift] [.right, .shift]

/-- Prefix family when the leading matrix of the left payload is the separator. -/
def chhnLeftLeadingPrefixes : CHHNPackedState → List CHHNControl :=
  chhnSextet [] [.shift] [.left] [.right] [.shift, .shift] [.left, .shift]

/-- Prefix family when the trailing matrix of the left payload is the separator. -/
def chhnLeftTrailingPrefixes : CHHNPackedState → List CHHNControl :=
  chhnSextet [] [.shift] [.shift, .shift] [.left]
    [.left, .shift] [.left, .shift, .shift]

/-- Prefix family when the leading matrix of the right payload is the separator. -/
def chhnRightLeadingPrefixes : CHHNPackedState → List CHHNControl :=
  chhnSextet [] [.shift] [.right] [.left] [.shift, .shift] [.right, .shift]

/-- Prefix family when the trailing matrix of the right payload is the separator. -/
def chhnRightTrailingPrefixes : CHHNPackedState → List CHHNControl :=
  chhnSextet [] [.shift] [.shift, .shift] [.right]
    [.right, .shift] [.right, .shift, .shift]

/-- Physical word selecting one payload slot into the leading output block. -/
def chhnPayloadWord : CHHNPayloadSlot → List CHHNControl
  | .leftLeading => [.left]
  | .leftTrailing => [.left, .shift]
  | .rightLeading => [.right]
  | .rightTrailing => [.right, .shift]

/-- Reachable-column family selected by two ordinary payload slots. -/
def chhnReachableSuffixes (first second : CHHNPayloadSlot) :
    CHHNPackedState → List CHHNControl :=
  chhnSextet [] [.shift] (chhnPayloadWord first) (chhnPayloadWord second)
    ([.shift] ++ chhnPayloadWord first) ([.shift] ++ chhnPayloadWord second)

/-- The three-state row exposed by a source slot. -/
def chhnSlotRow {K : Type*} [Field K]
    (source : CHHNSlot → Matrix (Fin 3) (Fin 3) K)
    (row : Fin 3 → K) (slot : CHHNSlot) : Fin 3 → K :=
  row ᵥ* source slot

/-- The three-state column exposed by a source slot. -/
def chhnSlotColumn {K : Type*} [Field K]
    (source : CHHNSlot → Matrix (Fin 3) (Fin 3) K)
    (column : Fin 3 → K) (slot : CHHNSlot) : Fin 3 → K :=
  source slot *ᵥ column

theorem chhnPayloadWord_mulVec_packedColumn
    {K : Type*} [Field K]
    (source : CHHNSlot → Matrix (Fin 3) (Fin 3) K)
    (column : Fin 3 → K) (slot : CHHNPayloadSlot) :
    wordProduct (chhnPackedGenerator source) (chhnPayloadWord slot) *ᵥ
        chhnPairVector column 0 =
      chhnPairVector (chhnSlotColumn source column slot.toSlot) 0 := by
  cases slot <;>
    ext state <;>
    cases state <;>
    simp [chhnPayloadWord, chhnPackedGenerator, chhnPackedColumn,
      chhnSlotColumn, CHHNPayloadSlot.toSlot, wordProduct, ← Matrix.mulVec_mulVec,
      chhnShift_mulVec_pairVector, chhnPayload_mulVec_pairVector]

theorem chhnShiftPayloadWord_mulVec_packedColumn
    {K : Type*} [Field K]
    (source : CHHNSlot → Matrix (Fin 3) (Fin 3) K)
    (column : Fin 3 → K) (slot : CHHNPayloadSlot) :
    wordProduct (chhnPackedGenerator source)
        ([.shift] ++ chhnPayloadWord slot) *ᵥ chhnPairVector column 0 =
      chhnPairVector 0 (chhnSlotColumn source column slot.toSlot) := by
  rw [wordProduct_append, ← Matrix.mulVec_mulVec,
    chhnPayloadWord_mulVec_packedColumn]
  simpa using chhnShift_mulVec_pairVector (source .root)
    (chhnSlotColumn source column slot.toSlot) 0

theorem chhnShift_mul_payloadWord_mulVec_packedColumn
    {K : Type*} [Field K]
    (source : CHHNSlot → Matrix (Fin 3) (Fin 3) K)
    (column : Fin 3 → K) (slot : CHHNPayloadSlot) :
    (chhnShift (source .root) *
        wordProduct (chhnPackedGenerator source) (chhnPayloadWord slot)) *ᵥ
        chhnPairVector column 0 =
      chhnPairVector 0 (chhnSlotColumn source column slot.toSlot) := by
  rw [← Matrix.mulVec_mulVec, chhnPayloadWord_mulVec_packedColumn]
  simpa using chhnShift_mulVec_pairVector (source .root)
    (chhnSlotColumn source column slot.toSlot) 0

/-- A rank-one source slot sends the boundary row to its boundary pairing times that row. -/
theorem vecMul_vecMulVec_same {K : Type*} [Field K]
    (row column : Fin 3 → K) :
    row ᵥ* Matrix.vecMulVec column row = (row ⬝ᵥ column) • row := by
  ext index
  change (∑ coordinate : Fin 3, row coordinate * (column coordinate * row index)) =
    (∑ coordinate : Fin 3, row coordinate * column coordinate) * row index
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

/-- Any row entering a rank-one source slot exits along its boundary row. -/
theorem vecMul_vecMulVec {K : Type*} [Field K]
    (active row column : Fin 3 → K) :
    active ᵥ* Matrix.vecMulVec column row = (active ⬝ᵥ column) • row := by
  ext index
  change (∑ coordinate : Fin 3, active coordinate * (column coordinate * row index)) =
    (∑ coordinate : Fin 3, active coordinate * column coordinate) * row index
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

theorem vecMul_mul_vecMulVec {K : Type*} [Field K]
    (active row column : Fin 3 → K) (matrix : Matrix (Fin 3) (Fin 3) K) :
    active ᵥ* (matrix * Matrix.vecMulVec column row) =
      (active ᵥ* matrix ⬝ᵥ column) • row := by
  rw [← Matrix.vecMul_vecMul, vecMul_vecMulVec]

theorem chhnRootPrefixStates_linearIndependent
    {K : Type*} [Field K]
    (source : CHHNSlot → Matrix (Fin 3) (Fin 3) K)
    (row column : Fin 3 → K)
    (root_separator : source .root = Matrix.vecMulVec column row)
    (pairing_ne_zero : row ⬝ᵥ column ≠ 0)
    (basis : LinearIndependent K
      ![row, chhnSlotRow source row .leftTrailing,
        chhnSlotRow source row .rightTrailing]) :
    LinearIndependent K fun index =>
      finitePrefixStates (chhnPackedGenerator source) (chhnPackedRow row)
        chhnRootPrefixes index := by
  let μ := row ⬝ᵥ column
  let a₁ := chhnSlotRow source row .leftLeading
  let a₂ := chhnSlotRow source row .leftTrailing
  let a₃ := chhnSlotRow source row .rightLeading
  let a₄ := chhnSlotRow source row .rightTrailing
  let κ₁ := a₁ ⬝ᵥ column
  let κ₃ := a₃ ⬝ᵥ column
  have pair_independent :
      LinearIndependent K
        ![(row, 0), (0, μ • row), (a₁, a₂), (a₃, a₄),
          (a₂, κ₁ • row), (a₄, κ₃ • row)] :=
    chhn_root_rows_linearIndependent row a₁ a₂ a₃ a₄ μ κ₁ κ₃
      pairing_ne_zero basis
  let expected : CHHNPackedState → (CHHNPackedState → K) :=
    chhnJoinedSextet (row, 0) (0, μ • row) (a₁, a₂) (a₃, a₄)
      (a₂, κ₁ • row) (a₄, κ₃ • row)
  have expected_independent : LinearIndependent K expected := by
    exact chhn_pairVector_family_linearIndependent
      (row, 0) (0, μ • row) (a₁, a₂) (a₃, a₄)
      (a₂, κ₁ • row) (a₄, κ₃ • row) pair_independent
  have rows_eq :
      (fun index =>
        finitePrefixStates (chhnPackedGenerator source) (chhnPackedRow row)
          chhnRootPrefixes index) = expected := by
    funext index
    cases index with
    | inl blockIndex =>
        fin_cases blockIndex <;> ext state <;> cases state <;>
          simp [expected, chhnJoinedSextet, chhnJoinLinear, chhnSextet, chhnRootPrefixes,
            finitePrefixStates, chhnPackedRow,
            chhnPackedGenerator, wordProduct, chhnPairVector_vecMul_shift,
            chhnPairVector_vecMul_payload, chhnPairVector_vecMul_payload_shift, root_separator,
            vecMul_vecMulVec_same,
            vecMul_vecMulVec, vecMul_mul_vecMulVec, μ, a₁, a₂, a₃, a₄, κ₁, κ₃, chhnSlotRow,
            Matrix.vecMul_zero]
    | inr blockIndex =>
        fin_cases blockIndex <;> ext state <;> cases state <;>
          simp [expected, chhnJoinedSextet, chhnJoinLinear, chhnSextet, chhnRootPrefixes,
            finitePrefixStates, chhnPackedRow,
            chhnPackedGenerator, wordProduct, chhnPairVector_vecMul_shift,
            chhnPairVector_vecMul_payload, chhnPairVector_vecMul_payload_shift, root_separator,
            vecMul_vecMulVec_same,
            vecMul_vecMulVec, vecMul_mul_vecMulVec, μ, a₁, a₂, a₃, a₄, κ₁, κ₃, chhnSlotRow,
            Matrix.vecMul_zero]
  rw [rows_eq]
  exact expected_independent

theorem chhnLeftLeadingPrefixStates_linearIndependent
    {K : Type*} [Field K]
    (source : CHHNSlot → Matrix (Fin 3) (Fin 3) K)
    (row column : Fin 3 → K)
    (separator : source .leftLeading = Matrix.vecMulVec column row)
    (left_basis : LinearIndependent K
      ![row, chhnSlotRow source row .root,
        chhnSlotRow source row .leftTrailing])
    (right_basis : LinearIndependent K
      ![chhnSlotRow source row .root,
        chhnSlotRow source row .leftTrailing,
        chhnSlotRow source row .rightTrailing]) :
    LinearIndependent K fun index =>
      finitePrefixStates (chhnPackedGenerator source) (chhnPackedRow row)
        chhnLeftLeadingPrefixes index := by
  let μ := row ⬝ᵥ column
  let a₀ := chhnSlotRow source row .root
  let a₂ := chhnSlotRow source row .leftTrailing
  let a₃ := chhnSlotRow source row .rightLeading
  let a₄ := chhnSlotRow source row .rightTrailing
  have pair_independent :
      LinearIndependent K
        ![(row, 0), (0, a₀), (μ • row, a₂), (a₃, a₄),
          (a₀, 0), (a₂, μ • a₀)] :=
    chhn_leading_rows_linearIndependent row a₀ a₂ a₃ a₄ μ
      left_basis right_basis
  let expected : CHHNPackedState → (CHHNPackedState → K) :=
    chhnJoinedSextet (row, 0) (0, a₀) (μ • row, a₂) (a₃, a₄)
      (a₀, 0) (a₂, μ • a₀)
  have expected_independent : LinearIndependent K expected :=
    chhn_pairVector_family_linearIndependent
      (row, 0) (0, a₀) (μ • row, a₂) (a₃, a₄)
      (a₀, 0) (a₂, μ • a₀) pair_independent
  have rows_eq :
      (fun index =>
        finitePrefixStates (chhnPackedGenerator source) (chhnPackedRow row)
          chhnLeftLeadingPrefixes index) = expected := by
    funext index
    cases index with
    | inl blockIndex =>
        fin_cases blockIndex <;> ext state <;> cases state <;>
          simp [expected, chhnJoinedSextet, chhnJoinLinear, chhnSextet,
            chhnLeftLeadingPrefixes, finitePrefixStates, chhnPackedRow,
            chhnPackedGenerator, wordProduct, chhnPairVector_vecMul_shift,
            chhnPairVector_vecMul_payload, chhnPairVector_vecMul_payload_shift,
            chhnPairVector_vecMul_shift_sq, smul_vecMul,
            separator, vecMul_vecMulVec_same, vecMul_vecMulVec, μ, a₀, a₂, a₃, a₄,
            chhnSlotRow, Matrix.vecMul_zero]
    | inr blockIndex =>
        fin_cases blockIndex <;> ext state <;> cases state <;>
          simp [expected, chhnJoinedSextet, chhnJoinLinear, chhnSextet,
            chhnLeftLeadingPrefixes, finitePrefixStates, chhnPackedRow,
            chhnPackedGenerator, wordProduct, chhnPairVector_vecMul_shift,
            chhnPairVector_vecMul_payload, chhnPairVector_vecMul_payload_shift,
            chhnPairVector_vecMul_shift_sq, smul_vecMul,
            separator, vecMul_vecMulVec_same, vecMul_vecMulVec, μ, a₀, a₂, a₃, a₄,
            chhnSlotRow, Matrix.vecMul_zero]
  rw [rows_eq]
  exact expected_independent

theorem chhnRightLeadingPrefixStates_linearIndependent
    {K : Type*} [Field K]
    (source : CHHNSlot → Matrix (Fin 3) (Fin 3) K)
    (row column : Fin 3 → K)
    (separator : source .rightLeading = Matrix.vecMulVec column row)
    (left_basis : LinearIndependent K
      ![row, chhnSlotRow source row .root,
        chhnSlotRow source row .rightTrailing])
    (right_basis : LinearIndependent K
      ![chhnSlotRow source row .root,
        chhnSlotRow source row .rightTrailing,
        chhnSlotRow source row .leftTrailing]) :
    LinearIndependent K fun index =>
      finitePrefixStates (chhnPackedGenerator source) (chhnPackedRow row)
        chhnRightLeadingPrefixes index := by
  let μ := row ⬝ᵥ column
  let a₀ := chhnSlotRow source row .root
  let a₂ := chhnSlotRow source row .rightTrailing
  let a₃ := chhnSlotRow source row .leftLeading
  let a₄ := chhnSlotRow source row .leftTrailing
  have pair_independent :
      LinearIndependent K
        ![(row, 0), (0, a₀), (μ • row, a₂), (a₃, a₄),
          (a₀, 0), (a₂, μ • a₀)] :=
    chhn_leading_rows_linearIndependent row a₀ a₂ a₃ a₄ μ
      left_basis right_basis
  let expected : CHHNPackedState → (CHHNPackedState → K) :=
    chhnJoinedSextet (row, 0) (0, a₀) (μ • row, a₂) (a₃, a₄)
      (a₀, 0) (a₂, μ • a₀)
  have expected_independent : LinearIndependent K expected :=
    chhn_pairVector_family_linearIndependent
      (row, 0) (0, a₀) (μ • row, a₂) (a₃, a₄)
      (a₀, 0) (a₂, μ • a₀) pair_independent
  have rows_eq :
      (fun index =>
        finitePrefixStates (chhnPackedGenerator source) (chhnPackedRow row)
          chhnRightLeadingPrefixes index) = expected := by
    funext index
    cases index with
    | inl blockIndex =>
        fin_cases blockIndex <;> ext state <;> cases state <;>
          simp [expected, chhnJoinedSextet, chhnJoinLinear, chhnSextet,
            chhnRightLeadingPrefixes, finitePrefixStates, chhnPackedRow,
            chhnPackedGenerator, wordProduct, chhnPairVector_vecMul_shift,
            chhnPairVector_vecMul_payload, chhnPairVector_vecMul_payload_shift,
            chhnPairVector_vecMul_shift_sq, smul_vecMul,
            separator, vecMul_vecMulVec_same, vecMul_vecMulVec, μ, a₀, a₂, a₃, a₄,
            chhnSlotRow, Matrix.vecMul_zero]
    | inr blockIndex =>
        fin_cases blockIndex <;> ext state <;> cases state <;>
          simp [expected, chhnJoinedSextet, chhnJoinLinear, chhnSextet,
            chhnRightLeadingPrefixes, finitePrefixStates, chhnPackedRow,
            chhnPackedGenerator, wordProduct, chhnPairVector_vecMul_shift,
            chhnPairVector_vecMul_payload, chhnPairVector_vecMul_payload_shift,
            chhnPairVector_vecMul_shift_sq, smul_vecMul,
            separator, vecMul_vecMulVec_same, vecMul_vecMulVec, μ, a₀, a₂, a₃, a₄,
            chhnSlotRow, Matrix.vecMul_zero]
  rw [rows_eq]
  exact expected_independent

theorem chhnLeftTrailingPrefixStates_linearIndependent
    {K : Type*} [Field K]
    (source : CHHNSlot → Matrix (Fin 3) (Fin 3) K)
    (row column : Fin 3 → K)
    (separator : source .leftTrailing = Matrix.vecMulVec column row)
    (pairing_ne_zero : row ⬝ᵥ column ≠ 0)
    (basis : LinearIndependent K
      ![row, chhnSlotRow source row .root,
        row ᵥ* (source .leftLeading * source .root)]) :
    LinearIndependent K fun index =>
      finitePrefixStates (chhnPackedGenerator source) (chhnPackedRow row)
        chhnLeftTrailingPrefixes index := by
  let μ := row ⬝ᵥ column
  let a₀ := chhnSlotRow source row .root
  let a₁ := chhnSlotRow source row .leftLeading
  let a₁₀ := row ᵥ* (source .leftLeading * source .root)
  have pair_independent :
      LinearIndependent K
        ![(row, 0), (0, a₀), (a₀, 0), (a₁, μ • row),
          (μ • row, a₁₀), (a₁₀, μ • a₀)] :=
    chhn_trailing_rows_linearIndependent row a₀ a₁ a₁₀ μ
      pairing_ne_zero basis
  let expected : CHHNPackedState → (CHHNPackedState → K) :=
    chhnJoinedSextet (row, 0) (0, a₀) (a₀, 0) (a₁, μ • row)
      (μ • row, a₁₀) (a₁₀, μ • a₀)
  have expected_independent : LinearIndependent K expected :=
    chhn_pairVector_family_linearIndependent
      (row, 0) (0, a₀) (a₀, 0) (a₁, μ • row)
      (μ • row, a₁₀) (a₁₀, μ • a₀) pair_independent
  have rows_eq :
      (fun index =>
        finitePrefixStates (chhnPackedGenerator source) (chhnPackedRow row)
          chhnLeftTrailingPrefixes index) = expected := by
    funext index
    cases index with
    | inl blockIndex =>
        fin_cases blockIndex <;> ext state <;> cases state <;>
          simp [expected, chhnJoinedSextet, chhnJoinLinear, chhnSextet,
            chhnLeftTrailingPrefixes, finitePrefixStates, chhnPackedRow,
            chhnPackedGenerator, wordProduct, chhnPairVector_vecMul_shift,
            chhnPairVector_vecMul_payload, chhnPairVector_vecMul_payload_shift,
            chhnPairVector_vecMul_shift_sq, chhnPairVector_vecMul_payload_shift_sq,
            smul_vecMul,
            separator, vecMul_vecMulVec_same, vecMul_vecMulVec,
            vecMul_mul_vecMulVec, μ, a₀, a₁, a₁₀, chhnSlotRow, Matrix.vecMul_zero]
    | inr blockIndex =>
        fin_cases blockIndex <;> ext state <;> cases state <;>
          simp [expected, chhnJoinedSextet, chhnJoinLinear, chhnSextet,
            chhnLeftTrailingPrefixes, finitePrefixStates, chhnPackedRow,
            chhnPackedGenerator, wordProduct, chhnPairVector_vecMul_shift,
            chhnPairVector_vecMul_payload, chhnPairVector_vecMul_payload_shift,
            chhnPairVector_vecMul_shift_sq, chhnPairVector_vecMul_payload_shift_sq,
            smul_vecMul,
            separator, vecMul_vecMulVec_same, vecMul_vecMulVec,
            vecMul_mul_vecMulVec, μ, a₀, a₁, a₁₀, chhnSlotRow, Matrix.vecMul_zero]
  rw [rows_eq]
  exact expected_independent

theorem chhnRightTrailingPrefixStates_linearIndependent
    {K : Type*} [Field K]
    (source : CHHNSlot → Matrix (Fin 3) (Fin 3) K)
    (row column : Fin 3 → K)
    (separator : source .rightTrailing = Matrix.vecMulVec column row)
    (pairing_ne_zero : row ⬝ᵥ column ≠ 0)
    (basis : LinearIndependent K
      ![row, chhnSlotRow source row .root,
        row ᵥ* (source .rightLeading * source .root)]) :
    LinearIndependent K fun index =>
      finitePrefixStates (chhnPackedGenerator source) (chhnPackedRow row)
        chhnRightTrailingPrefixes index := by
  let μ := row ⬝ᵥ column
  let a₀ := chhnSlotRow source row .root
  let a₁ := chhnSlotRow source row .rightLeading
  let a₁₀ := row ᵥ* (source .rightLeading * source .root)
  have pair_independent :
      LinearIndependent K
        ![(row, 0), (0, a₀), (a₀, 0), (a₁, μ • row),
          (μ • row, a₁₀), (a₁₀, μ • a₀)] :=
    chhn_trailing_rows_linearIndependent row a₀ a₁ a₁₀ μ
      pairing_ne_zero basis
  let expected : CHHNPackedState → (CHHNPackedState → K) :=
    chhnJoinedSextet (row, 0) (0, a₀) (a₀, 0) (a₁, μ • row)
      (μ • row, a₁₀) (a₁₀, μ • a₀)
  have expected_independent : LinearIndependent K expected :=
    chhn_pairVector_family_linearIndependent
      (row, 0) (0, a₀) (a₀, 0) (a₁, μ • row)
      (μ • row, a₁₀) (a₁₀, μ • a₀) pair_independent
  have rows_eq :
      (fun index =>
        finitePrefixStates (chhnPackedGenerator source) (chhnPackedRow row)
          chhnRightTrailingPrefixes index) = expected := by
    funext index
    cases index with
    | inl blockIndex =>
        fin_cases blockIndex <;> ext state <;> cases state <;>
          simp [expected, chhnJoinedSextet, chhnJoinLinear, chhnSextet,
            chhnRightTrailingPrefixes, finitePrefixStates, chhnPackedRow,
            chhnPackedGenerator, wordProduct, chhnPairVector_vecMul_shift,
            chhnPairVector_vecMul_payload, chhnPairVector_vecMul_payload_shift,
            chhnPairVector_vecMul_shift_sq, chhnPairVector_vecMul_payload_shift_sq,
            smul_vecMul,
            separator, vecMul_vecMulVec_same, vecMul_vecMulVec,
            vecMul_mul_vecMulVec, μ, a₀, a₁, a₁₀, chhnSlotRow, Matrix.vecMul_zero]
    | inr blockIndex =>
        fin_cases blockIndex <;> ext state <;> cases state <;>
          simp [expected, chhnJoinedSextet, chhnJoinLinear, chhnSextet,
            chhnRightTrailingPrefixes, finitePrefixStates, chhnPackedRow,
            chhnPackedGenerator, wordProduct, chhnPairVector_vecMul_shift,
            chhnPairVector_vecMul_payload, chhnPairVector_vecMul_payload_shift,
            chhnPairVector_vecMul_shift_sq, chhnPairVector_vecMul_payload_shift_sq,
            smul_vecMul,
            separator, vecMul_vecMulVec_same, vecMul_vecMulVec,
            vecMul_mul_vecMulVec, μ, a₀, a₁, a₁₀, chhnSlotRow, Matrix.vecMul_zero]
  rw [rows_eq]
  exact expected_independent

theorem chhnReachableSuffixStates_linearIndependent
    {K : Type*} [Field K]
    (source : CHHNSlot → Matrix (Fin 3) (Fin 3) K)
    (column : Fin 3 → K) (first second : CHHNPayloadSlot)
    (basis : LinearIndependent K
      ![column, chhnSlotColumn source column first.toSlot,
        chhnSlotColumn source column second.toSlot]) :
    LinearIndependent K fun index state =>
      finiteSuffixStates (chhnPackedGenerator source) (chhnPackedColumn column)
        (chhnReachableSuffixes first second) state index := by
  let h := chhnSlotColumn source column first.toSlot
  let k := chhnSlotColumn source column second.toSlot
  have pair_independent :
      LinearIndependent K
        ![(column, 0), (0, column), (h, 0), (k, 0), (0, h), (0, k)] :=
    chhn_split_columns_linearIndependent column h k basis
  let expected : CHHNPackedState → (CHHNPackedState → K) :=
    chhnJoinedSextet (column, 0) (0, column) (h, 0) (k, 0) (0, h) (0, k)
  have expected_independent : LinearIndependent K expected :=
    chhn_pairVector_family_linearIndependent
      (column, 0) (0, column) (h, 0) (k, 0) (0, h) (0, k) pair_independent
  have columns_eq :
      (fun index state =>
        finiteSuffixStates (chhnPackedGenerator source) (chhnPackedColumn column)
          (chhnReachableSuffixes first second) state index) = expected := by
    funext index state
    cases index with
    | inl blockIndex =>
        fin_cases blockIndex <;> cases state <;>
          simp [expected, chhnJoinedSextet, chhnJoinLinear, chhnSextet,
            chhnReachableSuffixes, finiteSuffixStates, chhnPackedColumn,
            chhnPackedGenerator, chhnShift_mulVec_pairVector,
            chhnPayloadWord_mulVec_packedColumn,
            chhnShiftPayloadWord_mulVec_packedColumn,
            chhnShift_mul_payloadWord_mulVec_packedColumn, h, k]
    | inr blockIndex =>
        fin_cases blockIndex <;> cases state <;>
          simp [expected, chhnJoinedSextet, chhnJoinLinear, chhnSextet,
            chhnReachableSuffixes, finiteSuffixStates, chhnPackedColumn,
            chhnPackedGenerator, chhnShift_mulVec_pairVector,
            chhnPayloadWord_mulVec_packedColumn,
            chhnShiftPayloadWord_mulVec_packedColumn,
            chhnShift_mul_payloadWord_mulVec_packedColumn, h, k]
  rw [columns_eq]
  exact expected_independent

/-- Independent rows and columns make a square matrix product nonsingular. -/
theorem det_mul_ne_zero_of_linearIndependent_rows_cols
    {K ν : Type*} [Field K] [Fintype ν] [DecidableEq ν]
    (left right : Matrix ν ν K)
    (left_independent : LinearIndependent K fun index => left index)
    (right_independent : LinearIndependent K fun index => rightᵀ index) :
    (left * right).det ≠ 0 := by
  have left_unit : IsUnit left :=
    Matrix.linearIndependent_rows_iff_isUnit.mp left_independent
  have right_unit : IsUnit right :=
    Matrix.linearIndependent_cols_iff_isUnit.mp right_independent
  exact ((left * right).isUnit_iff_isUnit_det.mp (left_unit.mul right_unit)).ne_zero

/-- Independent reachable rows and observable columns make the selected packed Hankel section
nonsingular. -/
theorem chhnFiniteHankel_det_ne_zero
    {K : Type*} [Field K]
    (source : CHHNSlot → Matrix (Fin 3) (Fin 3) K)
    (row column : Fin 3 → K)
    (prefixes suffixes : CHHNPackedState → List CHHNControl)
    (prefix_independent :
      LinearIndependent K fun index =>
        finitePrefixStates (chhnPackedGenerator source) (chhnPackedRow row)
          prefixes index)
    (suffix_independent :
      LinearIndependent K fun index state =>
        finiteSuffixStates (chhnPackedGenerator source) (chhnPackedColumn column)
          suffixes state index) :
    (finiteHankel
      (linearCoefficient (chhnPackedGenerator source)
        (chhnPackedRow row) (chhnPackedColumn column))
      prefixes suffixes).det ≠ 0 := by
  have exact :
      RepresentsSeries
        (linearCoefficient (chhnPackedGenerator source)
          (chhnPackedRow row) (chhnPackedColumn column))
        (chhnPackedGenerator source) (chhnPackedRow row) (chhnPackedColumn column) :=
    fun _ => rfl
  rw [finiteHankel_factor _ _ _ _ _ _ exact]
  apply det_mul_ne_zero_of_linearIndependent_rows_cols
  · exact prefix_independent
  · simpa [Matrix.transpose_apply] using suffix_independent

/-- A nonsingular packed certificate forces six states in every exact scalar realization. -/
theorem chhnExactRepresentation_six_le_card
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (source : CHHNSlot → Matrix (Fin 3) (Fin 3) K)
    (row column : Fin 3 → K)
    (prefixes suffixes : CHHNPackedState → List CHHNControl)
    (prefix_independent :
      LinearIndependent K fun index =>
        finitePrefixStates (chhnPackedGenerator source) (chhnPackedRow row)
          prefixes index)
    (suffix_independent :
      LinearIndependent K fun index state =>
        finiteSuffixStates (chhnPackedGenerator source) (chhnPackedColumn column)
          suffixes state index)
    (generators : CHHNControl → Matrix ι ι K) (left right : ι → K)
    (exact : RepresentsSeries
      (linearCoefficient (chhnPackedGenerator source)
        (chhnPackedRow row) (chhnPackedColumn column))
      generators left right) :
    6 ≤ Fintype.card ι := by
  have card_bound :=
    finiteHankel_card_le
      (linearCoefficient (chhnPackedGenerator source)
        (chhnPackedRow row) (chhnPackedColumn column))
      prefixes suffixes generators left right exact
      (chhnFiniteHankel_det_ne_zero source row column prefixes suffixes
        prefix_independent suffix_independent)
  norm_num at card_bound ⊢
  exact card_bound

end MatrixMortality
