import Mathlib.GroupTheory.FreeGroup.Basic
import MatrixMortality.ExpandingHistoryNoGo

/-!
# Cancellative projective obstruction

Every finite prefix-suffix zero table of the paired compiler admits a rational conic
realization in three dimensions. A lower bound must therefore use the common shifts. The exact
free-group role fractions and the odd-dimensional scalar-commutator law isolate the algebraic
spine of the obstruction to extending both word sides to independent inverse dynamics.
-/

namespace MatrixMortality

open scoped Matrix

/-! ## Prefix-suffix decoding -/

namespace PairedResidual

/-- Decode a control block with a prescribed phase entering from its right. -/
def decodeFrom : PairPhase → List PairedControl → PairPhase × List NearyTile
  | phase, [] => (phase, [])
  | phase, .toggle :: word =>
      let decoded := decodeFrom phase word
      (decoded.1.flip, decoded.2)
  | phase, .data letter :: word =>
      let decoded := decodeFrom phase word
      (.erase, decoded.1.tile letter :: decoded.2)

/-- The checked suffix decoder starts with rule phase at the right boundary. -/
theorem decodeFrom_rule (word : List PairedControl) :
    decodeFrom .rule word = suffixDecode word := by
  induction word with
  | nil => rfl
  | cons control word induction =>
      cases control <;> simp [decodeFrom, suffixDecode, induction]

/-- Decoding a concatenation first decodes the suffix, then feeds its phase into the prefix. -/
theorem decodeFrom_append (phase : PairPhase) (left right : List PairedControl) :
    decodeFrom phase (left ++ right) =
      let rightDecoded := decodeFrom phase right
      let leftDecoded := decodeFrom rightDecoded.1 left
      (leftDecoded.1, leftDecoded.2 ++ rightDecoded.2) := by
  induction left with
  | nil => simp [decodeFrom]
  | cons control left induction =>
      cases rightDecoded_eq : decodeFrom phase right with
      | mk rightPhase rightWord =>
          cases leftDecoded_eq : decodeFrom rightPhase left with
          | mk leftPhase leftWord =>
              cases control <;>
                simp [decodeFrom, induction, rightDecoded_eq, leftDecoded_eq]

/-- Exact phase-aware prefix decomposition of the repository decoder. -/
theorem suffixDecode_append (left right : List PairedControl) :
    suffixDecode (left ++ right) =
      let rightDecoded := suffixDecode right
      let leftDecoded := decodeFrom rightDecoded.1 left
      (leftDecoded.1, leftDecoded.2 ++ rightDecoded.2) := by
  rw [← decodeFrom_rule, decodeFrom_append, decodeFrom_rule]

end PairedResidual

/-! ## Finite support tables -/

/-- Two residual targets for each prefix and one phase-tagged residual for each suffix. -/
structure TwoPhaseResidualSystem (Prefix Suffix Residual : Type*) where
  /-- Residual selected by a prefix and an entering suffix phase. -/
  prefixResidual : Prefix → PairPhase → Residual
  /-- Phase entering a suffix from its left. -/
  suffixPhase : Suffix → PairPhase
  /-- Residual carried by a suffix. -/
  suffixResidual : Suffix → Residual
  /-- Rational separation of every phase-tagged residual under consideration. -/
  code : PairPhase × Residual ↪ ℚ

namespace TwoPhaseResidualSystem

variable {Prefix Suffix Residual : Type*}

/-- Rational conic point assigned to a suffix residual. -/
def point (system : TwoPhaseResidualSystem Prefix Suffix Residual) (suffix : Suffix) :
    Fin 3 → ℚ :=
  let t := system.code (system.suffixPhase suffix, system.suffixResidual suffix)
  ![1, t, t ^ 2]

/-- Secant through the two phase targets assigned to a prefix. -/
def line (system : TwoPhaseResidualSystem Prefix Suffix Residual) (context : Prefix) :
    Fin 3 → ℚ :=
  let a := system.code (.rule, system.prefixResidual context .rule)
  let b := system.code (.erase, system.prefixResidual context .erase)
  ![a * b, -(a + b), 1]

/-- Scalar incidence coefficient of one prefix and suffix. -/
def coefficient (system : TwoPhaseResidualSystem Prefix Suffix Residual)
    (context : Prefix) (suffix : Suffix) : ℚ :=
  system.line context ⬝ᵥ system.point suffix

/-- Matrix of all selected prefix-suffix incidences. -/
def incidenceMatrix (system : TwoPhaseResidualSystem Prefix Suffix Residual) :
    Matrix Prefix Suffix ℚ :=
  fun context suffix => system.coefficient context suffix

/-- Matrix of prefix secants. -/
def lineMatrix (system : TwoPhaseResidualSystem Prefix Suffix Residual) :
    Matrix Prefix (Fin 3) ℚ :=
  fun context coordinate => system.line context coordinate

/-- Matrix of suffix conic points. -/
def pointMatrix (system : TwoPhaseResidualSystem Prefix Suffix Residual) :
    Matrix (Fin 3) Suffix ℚ :=
  fun coordinate suffix => system.point suffix coordinate

/-- The finite support matrix factors through three rational coordinates. -/
theorem incidenceMatrix_eq_mul (system : TwoPhaseResidualSystem Prefix Suffix Residual) :
    system.incidenceMatrix = system.lineMatrix * system.pointMatrix := by
  ext context suffix
  rfl

/-- Every finite two-phase residual table has support rank at most three. -/
theorem incidenceMatrix_rank_le_three [Fintype Suffix]
    (system : TwoPhaseResidualSystem Prefix Suffix Residual) :
    system.incidenceMatrix.rank ≤ 3 := by
  rw [system.incidenceMatrix_eq_mul]
  exact (Matrix.rank_mul_le_left system.lineMatrix system.pointMatrix).trans <| by
    simpa using Matrix.rank_le_card_width system.lineMatrix

/-- The conic-secant coefficient factors through the two phase-tagged residual targets. -/
theorem coefficient_eq (system : TwoPhaseResidualSystem Prefix Suffix Residual)
    (context : Prefix) (suffix : Suffix) :
    system.coefficient context suffix =
      (system.code (system.suffixPhase suffix, system.suffixResidual suffix) -
          system.code (.rule, system.prefixResidual context .rule)) *
        (system.code (system.suffixPhase suffix, system.suffixResidual suffix) -
          system.code (.erase, system.prefixResidual context .erase)) := by
  simp [coefficient, line, point, dotProduct, Fin.sum_univ_succ]
  ring

/-- Conic incidence is exactly equality with the residual selected by the suffix phase. -/
theorem coefficient_eq_zero_iff
    (system : TwoPhaseResidualSystem Prefix Suffix Residual)
    (context : Prefix) (suffix : Suffix) :
    system.coefficient context suffix = 0 ↔
      system.suffixResidual suffix =
        system.prefixResidual context (system.suffixPhase suffix) := by
  rw [system.coefficient_eq, mul_eq_zero]
  cases phase_eq : system.suffixPhase suffix with
  | rule =>
      constructor
      · rintro (rule_zero | erase_zero)
        · have tagged_eq := system.code.injective (sub_eq_zero.mp rule_zero)
          simpa [phase_eq] using congrArg Prod.snd tagged_eq
        · have tagged_eq := system.code.injective (sub_eq_zero.mp erase_zero)
          simp at tagged_eq
      · intro residual_eq
        left
        apply sub_eq_zero.mpr
        simp [residual_eq]
  | erase =>
      constructor
      · rintro (rule_zero | erase_zero)
        · have tagged_eq := system.code.injective (sub_eq_zero.mp rule_zero)
          simp at tagged_eq
        · have tagged_eq := system.code.injective (sub_eq_zero.mp erase_zero)
          simpa [phase_eq] using congrArg Prod.snd tagged_eq
      · intro residual_eq
        right
        apply sub_eq_zero.mpr
        simp [residual_eq]

end TwoPhaseResidualSystem

/-! ## Exact role fractions -/

namespace CancellativeRoleFraction

/-- Free group on the two encoded bit symbols. -/
abbrev BitGroup := FreeGroup Bool

/-- Positive binary words embedded in the free group. -/
def positiveWord (word : List Bool) : BitGroup :=
  FreeGroup.mk (word.map fun bit => (bit, true))

@[simp] theorem positiveWord_append (left right : List Bool) :
    positiveWord (left ++ right) = positiveWord left * positiveWord right := by
  simp [positiveWord, FreeGroup.mul_mk]

private theorem reduce_positiveWord (word : List Bool) :
    FreeGroup.reduce (word.map fun bit => (bit, true)) =
      word.map fun bit => (bit, true) := by
  induction word with
  | nil => rfl
  | cons bit word induction =>
      simp only [List.map_cons]
      rw [FreeGroup.reduce.cons, induction]
      cases word <;> simp

/-- The positive binary monoid embeds in its free-group completion. -/
theorem positiveWord_injective : Function.Injective positiveWord := by
  intro left right equality
  have reduced := FreeGroup.reduce.sound equality
  rw [reduce_positiveWord, reduce_positiveWord] at reduced
  exact (List.map_injective_iff.mpr fun _ _ pair_eq => congrArg Prod.fst pair_eq) reduced

/-- A terminal concatenation is equivalent to equality of its left and right free-group
residuals. -/
theorem terminal_eq_iff_residual_eq (upperContext upperSuffix marker lowerContext lowerSuffix :
    List Bool) :
    upperContext ++ upperSuffix ++ marker = lowerContext ++ lowerSuffix ↔
      (positiveWord upperContext)⁻¹ * positiveWord lowerContext =
        positiveWord upperSuffix * positiveWord marker * (positiveWord lowerSuffix)⁻¹ := by
  constructor
  · intro terminal
    have embedded := congrArg positiveWord terminal
    simp only [positiveWord_append] at embedded
    calc
      (positiveWord upperContext)⁻¹ * positiveWord lowerContext =
          (positiveWord upperContext)⁻¹ *
            (positiveWord lowerContext * positiveWord lowerSuffix) *
              (positiveWord lowerSuffix)⁻¹ := by group
      _ = (positiveWord upperContext)⁻¹ *
            (positiveWord upperContext * positiveWord upperSuffix * positiveWord marker) *
              (positiveWord lowerSuffix)⁻¹ := by rw [embedded]
      _ = positiveWord upperSuffix * positiveWord marker *
            (positiveWord lowerSuffix)⁻¹ := by group
  · intro residual
    apply positiveWord_injective
    simp only [positiveWord_append]
    calc
      positiveWord upperContext * positiveWord upperSuffix * positiveWord marker =
          positiveWord upperContext *
            (positiveWord upperSuffix * positiveWord marker *
              (positiveWord lowerSuffix)⁻¹) * positiveWord lowerSuffix := by group
      _ = positiveWord upperContext *
            ((positiveWord upperContext)⁻¹ * positiveWord lowerContext) *
              positiveWord lowerSuffix := by rw [residual]
      _ = positiveWord lowerContext * positiveWord lowerSuffix := by group

/-- Boolean code of the two paired phases. -/
def phaseBit : PairPhase → Bool
  | .rule => true
  | .erase => false

theorem phaseBit_injective : Function.Injective phaseBit := by
  intro left right equality
  cases left <;> cases right <;> simp_all [phaseBit]

/-- Rational code of every phase-tagged binary free-group residual. -/
noncomputable def residualCode : PairPhase × BitGroup ↪ ℚ where
  toFun residual :=
    (Encodable.encode (phaseBit residual.1, residual.2.toWord) : ℚ)
  inj' := by
    intro left right equality
    have encoded :
        Encodable.encode (phaseBit left.1, left.2.toWord) =
          Encodable.encode (phaseBit right.1, right.2.toWord) := by
      exact Nat.cast_injective equality
    have tagged := Encodable.encode_injective encoded
    apply Prod.ext
    · exact phaseBit_injective (congrArg Prod.fst tagged)
    · apply FreeGroup.toWord_injective
      exact congrArg Prod.snd tagged

/-- Free-group residual selected by a control context and its entering phase. -/
def prefixResidual (β : Nat) (body : List TagLetter) (context : List PairedControl)
    (phase : PairPhase) : BitGroup :=
  let roles := (PairedResidual.decodeFrom phase context).2
  (positiveWord (spell (nearyUpper β) roles))⁻¹ *
    positiveWord (spell (nearyLower β body) roles)

/-- Terminal free-group residual carried by a control suffix. -/
def suffixResidual (β : Nat) (body : List TagLetter) (suffix : List PairedControl) :
    BitGroup :=
  let roles := decodePairedWord suffix
  positiveWord (spell (nearyUpper β) roles) * positiveWord (nearyMarker β) *
    (positiveWord (spell (nearyLower β body) roles))⁻¹

/-- Static conic incidence system of all paired prefix-suffix residuals. -/
noncomputable def pairedSystem (β : Nat) (body : List TagLetter) :
    TwoPhaseResidualSystem (List PairedControl) (List PairedControl) BitGroup where
  prefixResidual := prefixResidual β body
  suffixPhase suffix := (suffixDecode suffix).1
  suffixResidual := suffixResidual β body
  code := residualCode

/-- The complete paired terminal table is equality of one phase-selected prefix residual and one
suffix residual. -/
theorem terminal_match_append_iff_residual_eq (β : Nat) (body : List TagLetter)
    (context suffix : List PairedControl) :
    spell (nearyUpper β) (decodePairedWord (context ++ suffix)) ++ nearyMarker β =
        spell (nearyLower β body) (decodePairedWord (context ++ suffix)) ↔
      suffixResidual β body suffix =
        prefixResidual β body context (suffixDecode suffix).1 := by
  cases suffix_eq : suffixDecode suffix with
  | mk suffixPhase suffixRoles =>
      cases context_eq : PairedResidual.decodeFrom suffixPhase context with
      | mk contextPhase contextRoles =>
          have decoded_eq :
              decodePairedWord (context ++ suffix) = contextRoles ++ suffixRoles := by
            simp [decodePairedWord, PairedResidual.suffixDecode_append, suffix_eq, context_eq]
          rw [decoded_eq, spell_append, spell_append]
          rw [terminal_eq_iff_residual_eq]
          simp [suffixResidual, prefixResidual, decodePairedWord, suffix_eq, context_eq, eq_comm]

/-- A rational conic realizes every paired prefix-suffix zero exactly; it carries no common shift
maps. -/
theorem conicCoefficient_zero_iff_pairedCoefficient_zero (β : Nat) (body : List TagLetter)
    (context suffix : List PairedControl) :
    (pairedSystem β body).coefficient context suffix = 0 ↔
      pairedCoefficient ℚ β body (context ++ suffix) = 0 := by
  rw [(pairedSystem β body).coefficient_eq_zero_iff]
  rw [pairedCoefficient_eq_sideCoefficient,
    sideCoefficient_eq_zero_iff_terminal_match_rat]
  exact (terminal_match_append_iff_residual_eq β body context suffix).symm

/-- Pull the global paired residual system back to selected prefix and suffix indices. -/
noncomputable def sampledPairedSystem {ContextIndex SuffixIndex : Type*}
    (β : Nat) (body : List TagLetter) (contexts : ContextIndex → List PairedControl)
    (suffixes : SuffixIndex → List PairedControl) :
    TwoPhaseResidualSystem ContextIndex SuffixIndex BitGroup where
  prefixResidual context phase := prefixResidual β body (contexts context) phase
  suffixPhase suffix := (suffixDecode (suffixes suffix)).1
  suffixResidual suffix := suffixResidual β body (suffixes suffix)
  code := residualCode

/-- Every finite paired prefix-suffix zero table has a rational matrix of rank at most three with
exactly the same zero support. -/
theorem exists_supportMatrix_rank_le_three {ContextIndex SuffixIndex : Type*}
    [Fintype SuffixIndex]
    (β : Nat) (body : List TagLetter) (contexts : ContextIndex → List PairedControl)
    (suffixes : SuffixIndex → List PairedControl) :
    ∃ support : Matrix ContextIndex SuffixIndex ℚ,
      support.rank ≤ 3 ∧
        ∀ context suffix,
          support context suffix = 0 ↔
            pairedCoefficient ℚ β body (contexts context ++ suffixes suffix) = 0 := by
  let system := sampledPairedSystem β body contexts suffixes
  refine ⟨system.incidenceMatrix, system.incidenceMatrix_rank_le_three, ?_⟩
  intro context suffix
  exact conicCoefficient_zero_iff_pairedCoefficient_zero β body
    (contexts context) (suffixes suffix)

/-- Encoded zero bit. -/
def x : BitGroup := FreeGroup.of false

/-- Encoded one bit. -/
def z : BitGroup := FreeGroup.of true

/-- Upper word of the Neary `b` tile. -/
def block (β : Nat) : BitGroup := z * x ^ β * z

/-- Erase-`b` word pair. -/
def eraseB (β : Nat) : BitGroup × BitGroup := (block β, x)

/-- Erase-`c` word pair. -/
def eraseC : BitGroup × BitGroup := (z, x)

/-- Rule-`b` word pair. -/
def ruleB (β : Nat) : BitGroup × BitGroup := (block β, z ^ 2 * x)

/-- Left-only fraction obtained by cancelling the two erasing roles. -/
def leftSeed (β : Nat) : BitGroup × BitGroup := eraseB β * eraseC⁻¹

/-- A conjugate left-only fraction. -/
def leftConjugate (β : Nat) : BitGroup × BitGroup :=
  eraseC * leftSeed β * eraseC⁻¹

/-- Right-only fraction obtained by cancelling the common upper word. -/
def rightSeed (β : Nat) : BitGroup × BitGroup := ruleB β * (eraseB β)⁻¹

/-- A conjugate right-only fraction. -/
def rightConjugate (β : Nat) : BitGroup × BitGroup :=
  eraseB β * rightSeed β * (eraseB β)⁻¹

theorem leftSeed_eq (β : Nat) : leftSeed β = (z * x ^ β, 1) := by
  simp [leftSeed, eraseB, eraseC, block, mul_assoc]

theorem leftConjugate_eq (β : Nat) :
    leftConjugate β = (z * (z * x ^ β) * z⁻¹, 1) := by
  simp [leftConjugate, leftSeed_eq, eraseC, mul_assoc]

theorem rightSeed_eq (β : Nat) : rightSeed β = (1, z ^ 2) := by
  simp [rightSeed, ruleB, eraseB, block, mul_assoc]

theorem rightConjugate_eq (β : Nat) :
    rightConjugate β = (1, x * z ^ 2 * x⁻¹) := by
  simp [rightConjugate, rightSeed_eq, eraseB, block, mul_assoc]

end CancellativeRoleFraction

/-! ## Odd-dimensional projective rigidity -/

namespace CancellativeProjectiveRigidity

/-- A rational scalar whose cube is one is one. -/
theorem eq_one_of_cube_eq_one {μ : ℚ} (cube : μ ^ 3 = 1) : μ = 1 := by
  have factor : (μ - 1) * (μ ^ 2 + μ + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp factor with linear | quadratic
  · linarith
  · nlinarith [sq_nonneg (μ + 1 / 2)]

/-- Projectively commuting invertible rational `3 × 3` matrices commute linearly. -/
theorem scalar_commutator_eq_one (A B : Matrix (Fin 3) (Fin 3) ℚ) (μ : ℚ)
    (detA : A.det ≠ 0) (detB : B.det ≠ 0)
    (projective_commute : A * B = μ • (B * A)) : μ = 1 := by
  have determinant_eq := congrArg Matrix.det projective_commute
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul] at determinant_eq
  simp only [Fintype.card_fin] at determinant_eq
  apply eq_one_of_cube_eq_one
  apply mul_left_cancel₀ (mul_ne_zero detA detB)
  calc
    A.det * B.det * μ ^ 3 = μ ^ 3 * (B.det * A.det) := by ring
    _ = A.det * B.det := by simpa [mul_comm, mul_left_comm] using determinant_eq.symm
    _ = A.det * B.det * 1 := by ring

end CancellativeProjectiveRigidity

end MatrixMortality
