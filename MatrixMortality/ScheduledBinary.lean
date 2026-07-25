import MatrixMortality.MatrixSemigroup
import MatrixMortality.PairedCompression

/-!
# Scheduled binary compression

A fixed-width tag stroke contains one rule role followed by `β - 1` erasure roles. After word
reversal, its phase pattern is therefore fixed: `β - 1` erasures followed by one rule. These
matrices spend one lower-channel coordinate on each clock phase and let the binary input choose
only the tag letter.

The decoder is total on the binary free monoid. Its exact coefficient identity, together with
the existing terminal-match normal form, proves that unfinished clock cycles cannot create a
zero.
-/

namespace MatrixMortality

open scoped Matrix

/-- Two common affine/upper coordinates, followed by one lower coordinate per clock phase. -/
abbrev ScheduledIndex (β : Nat) := Fin 2 ⊕ Fin β

/-- The first clock phase. -/
def scheduledInitialPhase {β : Nat} (β_pos : 0 < β) : Fin β := ⟨0, β_pos⟩

/-- Advance the cyclic clock by one phase. -/
def scheduledNextPhase {β : Nat} (β_pos : 0 < β) (phase : Fin β) : Fin β :=
  if next_lt : phase.val + 1 < β then
    ⟨phase.val + 1, next_lt⟩
  else
    scheduledInitialPhase β_pos

/-- All nonfinal phases emit erasures; the final phase emits a rule. -/
def scheduledPhase {β : Nat} (phase : Fin β) : PairPhase :=
  if phase.val + 1 = β then .rule else .erase

/-- Interpret a bit as a tag letter. -/
def scheduledLetter : Bool → TagLetter
  | false => .b
  | true => .c

/-- Binary code inverse to `scheduledLetter`. -/
def scheduledBit : TagLetter → Bool
  | .b => false
  | .c => true

@[simp] theorem scheduledLetter_scheduledBit (letter : TagLetter) :
    scheduledLetter (scheduledBit letter) = letter := by
  cases letter <;> rfl

/-- Interpret a bit as one role at the current clock phase. -/
def scheduledTile {β : Nat} (phase : Fin β) (bit : Bool) : NearyTile :=
  (scheduledPhase phase).tile (scheduledLetter bit)

@[simp] theorem nearyUpper_scheduledTile (β : Nat) (phase : Fin β) (bit : Bool) :
    nearyUpper β (scheduledTile phase bit) = tagCode β (scheduledLetter bit) := by
  unfold scheduledTile
  cases scheduledPhase phase <;> rfl

/-- One of the two scheduled generators. -/
def scheduledGenerator (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter)
    (β_pos : 0 < β) (bit : Bool) :
    Matrix (ScheduledIndex β) (ScheduledIndex β) R
  | .inl source, .inl target =>
      !![(1 : R), 0;
         ternaryCode (tagCode β (scheduledLetter bit)),
           (3 : R) ^ (tagCode β (scheduledLetter bit)).length] source target
  | .inl _, .inr _ => 0
  | .inr phase, .inl target =>
      ![ternaryCode (nearyLower β body (scheduledTile phase bit)), 0] target
  | .inr phase, .inr target =>
      if target = scheduledNextPhase β_pos phase then
        (3 : R) ^ (nearyLower β body (scheduledTile phase bit)).length
      else
        0

/-- Embed a side-normal payload row at one active lower-channel phase. -/
def scheduledRow (R : Type*) [CommRing R] {β : Nat} (phase : Fin β)
    (vector : Fin 3 → R) : ScheduledIndex β → R
  | .inl index => ![vector 0, vector 2] index
  | .inr index => if index = phase then vector 1 else 0

theorem scheduledNextPhase_eq_zero_iff {β : Nat} (β_pos : 0 < β) (phase : Fin β) :
    scheduledNextPhase β_pos phase = scheduledInitialPhase β_pos ↔ phase.val + 1 = β := by
  rw [scheduledNextPhase]
  split_ifs with next_lt
  · constructor
    · intro next_eq
      have values := congrArg Fin.val next_eq
      simp [scheduledInitialPhase] at values
    · omega
  · constructor
    · intro
      omega
    · intro
      rfl

theorem scheduledRow_mul_generator (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (β_pos : 0 < β) (phase : Fin β)
    (vector : Fin 3 → R) (bit : Bool) :
    scheduledRow R phase vector ᵥ* scheduledGenerator R β body β_pos bit =
      scheduledRow R (scheduledNextPhase β_pos phase)
        (sidePcpMatrix R (nearyUpper β (scheduledTile phase bit))
          (nearyLower β body (scheduledTile phase bit)) *ᵥ vector) := by
  funext target
  cases target with
  | inl target =>
      fin_cases target <;>
        simp only [nearyUpper_scheduledTile] <;>
        simp [scheduledRow, scheduledGenerator, sidePcpMatrix, Matrix.vecMul,
          Matrix.dotProduct, Matrix.mulVec, Fin.sum_univ_succ, Fintype.sum_sum_type]
      all_goals ring
  | inr target =>
      simp only [scheduledRow, scheduledGenerator, Matrix.vecMul, Matrix.dotProduct,
        Fintype.sum_sum_type]
      rw [Finset.sum_eq_single phase]
      · by_cases target_next : target = scheduledNextPhase β_pos phase
        · subst target
          simp [sidePcpMatrix, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]
          ring
        · simp [target_next]
      · intro other _ other_ne
        simp [other_ne]
      · simp

/-- Decode a suffix while carrying its starting clock phase. Roles are returned in the matrix
product order, hence in reverse input order. -/
def decodeScheduledFrom {β : Nat} (β_pos : 0 < β) :
    Fin β → List Bool → List NearyTile
  | _, [] => []
  | phase, bit :: rest =>
      decodeScheduledFrom β_pos (scheduledNextPhase β_pos phase) rest ++
        [scheduledTile phase bit]

/-- The phase retained after consuming a binary word. -/
def scheduledResidualFrom {β : Nat} (β_pos : 0 < β) : Fin β → List Bool → Fin β
  | phase, [] => phase
  | phase, _ :: rest => scheduledResidualFrom β_pos (scheduledNextPhase β_pos phase) rest

/-- The chronological role stream emitted by a scheduled word. -/
def scheduledRolesFrom {β : Nat} (β_pos : 0 < β) : Fin β → List Bool → List NearyTile
  | _, [] => []
  | phase, bit :: rest =>
      scheduledTile phase bit :: scheduledRolesFrom β_pos (scheduledNextPhase β_pos phase) rest

/-- Total scheduled decoder from the initial phase. -/
def decodeScheduled {β : Nat} (β_pos : 0 < β) (word : List Bool) : List NearyTile :=
  decodeScheduledFrom β_pos (scheduledInitialPhase β_pos) word

theorem decodeScheduledFrom_eq_reverse_roles {β : Nat} (β_pos : 0 < β)
    (phase : Fin β) (word : List Bool) :
    decodeScheduledFrom β_pos phase word = (scheduledRolesFrom β_pos phase word).reverse := by
  induction word generalizing phase with
  | nil => rfl
  | cons bit rest induction =>
      simp only [decodeScheduledFrom, scheduledRolesFrom, List.reverse_cons]
      rw [induction]

theorem scheduledResidualFrom_append {β : Nat} (β_pos : 0 < β) (phase : Fin β)
    (left right : List Bool) :
    scheduledResidualFrom β_pos phase (left ++ right) =
      scheduledResidualFrom β_pos (scheduledResidualFrom β_pos phase left) right := by
  induction left generalizing phase with
  | nil => rfl
  | cons bit left induction =>
      simp only [List.cons_append, scheduledResidualFrom]
      exact induction (scheduledNextPhase β_pos phase)

theorem scheduledRolesFrom_append {β : Nat} (β_pos : 0 < β) (phase : Fin β)
    (left right : List Bool) :
    scheduledRolesFrom β_pos phase (left ++ right) =
      scheduledRolesFrom β_pos phase left ++
        scheduledRolesFrom β_pos (scheduledResidualFrom β_pos phase left) right := by
  induction left generalizing phase with
  | nil => rfl
  | cons bit left induction =>
      simp only [List.cons_append, scheduledRolesFrom, List.cons_append,
        scheduledResidualFrom]
      exact congrArg (scheduledTile phase bit :: ·)
        (induction (scheduledNextPhase β_pos phase))

theorem scheduledEraseRun {β : Nat} (β_pos : 0 < β) (phase : Fin β)
    (letters : List TagLetter) (within_clock : phase.val + letters.length < β) :
    scheduledRolesFrom β_pos phase (letters.map scheduledBit) =
        letters.map NearyTile.erase ∧
      scheduledResidualFrom β_pos phase (letters.map scheduledBit) =
        ⟨phase.val + letters.length, within_clock⟩ := by
  induction letters generalizing phase with
  | nil =>
      constructor
      · rfl
      · apply Fin.ext
        simp [scheduledResidualFrom]
  | cons letter letters induction =>
      have within_clock' : phase.val + (letters.length + 1) < β := by
        simpa using within_clock
      have next_lt : phase.val + 1 < β := by
        omega
      have next_eq :
          scheduledNextPhase β_pos phase = ⟨phase.val + 1, next_lt⟩ := by
        simp [scheduledNextPhase, next_lt]
      have tail_within : phase.val + 1 + letters.length < β := by
        change phase.val + 1 + letters.length < β
        omega
      obtain ⟨roles, residual⟩ :=
        induction (phase := ⟨phase.val + 1, next_lt⟩) tail_within
      constructor
      · simp only [List.map_cons, scheduledRolesFrom, scheduledTile, scheduledPhase,
          scheduledLetter_scheduledBit, next_eq]
        rw [if_neg (by omega)]
        exact congrArg (NearyTile.erase letter :: ·) roles
      · simp only [List.map_cons, scheduledResidualFrom, next_eq]
        rw [residual]
        apply Fin.ext
        simp
        omega

/-- Reverse-bit code for one fixed-width stroke. -/
def scheduledStrokeCode {β : Nat} (stroke : Stroke TagLetter β) : List Bool :=
  stroke.wake.reverse.map scheduledBit ++ [scheduledBit stroke.head]

/-- Histories are encoded in reverse stroke order because matrices act on the terminal column
from the right. -/
def scheduledHistoryCode {β : Nat} : List (Stroke TagLetter β) → List Bool
  | [] => []
  | stroke :: history => scheduledHistoryCode history ++ scheduledStrokeCode stroke

theorem scheduledStrokeCode_roles {β : Nat} (β_pos : 0 < β)
    (stroke : Stroke TagLetter β) :
    scheduledRolesFrom β_pos (scheduledInitialPhase β_pos) (scheduledStrokeCode stroke) =
      (strokeTiles stroke).reverse := by
  have wake_length : stroke.wake.length = β - 1 := by
    have width := stroke.width
    omega
  have prefix_within :
      (scheduledInitialPhase β_pos).val + stroke.wake.reverse.length < β := by
    simp [scheduledInitialPhase, wake_length]
    omega
  obtain ⟨prefix_roles, prefix_residual⟩ :=
    scheduledEraseRun β_pos (scheduledInitialPhase β_pos) stroke.wake.reverse prefix_within
  rw [scheduledStrokeCode, scheduledRolesFrom_append, prefix_roles, prefix_residual]
  have final_phase :
      (⟨(scheduledInitialPhase β_pos).val + stroke.wake.reverse.length,
          prefix_within⟩ : Fin β).val + 1 = β := by
    simp [scheduledInitialPhase, wake_length]
    omega
  have final_phase' :
      (scheduledInitialPhase β_pos).val + stroke.wake.length + 1 = β := by
    simp [scheduledInitialPhase, wake_length]
    omega
  simp [scheduledRolesFrom, scheduledTile, scheduledPhase, final_phase, strokeTiles,
    final_phase', PairPhase.tile, List.map_reverse]

theorem scheduledStrokeCode_residual {β : Nat} (β_pos : 0 < β)
    (stroke : Stroke TagLetter β) :
    scheduledResidualFrom β_pos (scheduledInitialPhase β_pos) (scheduledStrokeCode stroke) =
      scheduledInitialPhase β_pos := by
  have wake_length : stroke.wake.length = β - 1 := by
    have width := stroke.width
    omega
  have prefix_within :
      (scheduledInitialPhase β_pos).val + stroke.wake.reverse.length < β := by
    simp [scheduledInitialPhase, wake_length]
    omega
  obtain ⟨_, prefix_residual⟩ :=
    scheduledEraseRun β_pos (scheduledInitialPhase β_pos) stroke.wake.reverse prefix_within
  rw [scheduledStrokeCode, scheduledResidualFrom_append, prefix_residual]
  have final_phase :
      (⟨(scheduledInitialPhase β_pos).val + stroke.wake.reverse.length,
          prefix_within⟩ : Fin β).val + 1 = β := by
    simp [scheduledInitialPhase, wake_length]
    omega
  simp only [scheduledResidualFrom]
  exact (scheduledNextPhase_eq_zero_iff β_pos _).mpr final_phase

theorem scheduledHistoryCode_residual {β : Nat} (β_pos : 0 < β)
    (history : List (Stroke TagLetter β)) :
    scheduledResidualFrom β_pos (scheduledInitialPhase β_pos)
        (scheduledHistoryCode history) =
      scheduledInitialPhase β_pos := by
  induction history with
  | nil => rfl
  | cons stroke history induction =>
      rw [scheduledHistoryCode, scheduledResidualFrom_append, induction,
        scheduledStrokeCode_residual]

theorem scheduledHistoryCode_roles {β : Nat} (β_pos : 0 < β)
    (history : List (Stroke TagLetter β)) :
    scheduledRolesFrom β_pos (scheduledInitialPhase β_pos) (scheduledHistoryCode history) =
      (tileHistory history).reverse := by
  induction history with
  | nil => rfl
  | cons stroke history induction =>
      rw [scheduledHistoryCode, scheduledRolesFrom_append, induction]
      rw [scheduledHistoryCode_residual, scheduledStrokeCode_roles, tileHistory_cons,
        List.reverse_append]

/-- Every lawful tile history lies in the total decoder's image. -/
theorem decodeScheduled_historyCode {β : Nat} (β_pos : 0 < β)
    (history : List (Stroke TagLetter β)) :
    decodeScheduled β_pos (scheduledHistoryCode history) = tileHistory history := by
  rw [decodeScheduled, decodeScheduledFrom_eq_reverse_roles, scheduledHistoryCode_roles,
    List.reverse_reverse]

theorem scheduledRow_wordProduct (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (β_pos : 0 < β) (phase : Fin β)
    (vector : Fin 3 → R) (word : List Bool) :
    scheduledRow R phase vector ᵥ*
        wordProduct (scheduledGenerator R β body β_pos) word =
      scheduledRow R (scheduledResidualFrom β_pos phase word)
        (sideTileProduct R β body (decodeScheduledFrom β_pos phase word) *ᵥ vector) := by
  induction word generalizing phase vector with
  | nil =>
      simp [scheduledResidualFrom, decodeScheduledFrom, sideTileProduct]
  | cons bit rest induction =>
      simp only [wordProduct_cons]
      rw [← Matrix.vecMul_vecMul, scheduledRow_mul_generator, induction]
      simp only [scheduledResidualFrom, decodeScheduledFrom]
      rw [sideTileProduct_append]
      simp only [sideTileProduct, wordProduct_cons, wordProduct_nil, mul_one,
        Matrix.mulVec_mulVec]

/-- The fixed left boundary in scheduled coordinates. -/
def scheduledBoundaryRow (R : Type*) [CommRing R] (β : Nat) (β_pos : 0 < β) :
    ScheduledIndex β → R :=
  scheduledRow R (scheduledInitialPhase β_pos)
    (sideTerminalColumn R (nearyMarker β))

/-- The common affine coordinate extracts the coefficient in every residual clock phase. -/
def scheduledBoundaryColumn (R : Type*) [CommRing R] (β : Nat) : ScheduledIndex β → R
  | .inl index => if index = 0 then 1 else 0
  | .inr _ => 0

theorem scheduledRow_dot_boundaryColumn (R : Type*) [CommRing R] {β : Nat}
    (phase : Fin β) (vector : Fin 3 → R) :
    scheduledRow R phase vector ⬝ᵥ scheduledBoundaryColumn R β = vector 0 := by
  simp [scheduledRow, scheduledBoundaryColumn, Matrix.dotProduct, Fintype.sum_sum_type,
    Fin.sum_univ_succ]

/-- Scalar series represented by the scheduled binary compiler. -/
def scheduledCoefficient (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter)
    (β_pos : 0 < β) (word : List Bool) : R :=
  scheduledBoundaryRow R β β_pos ⬝ᵥ
    wordProduct (scheduledGenerator R β body β_pos) word *ᵥ
      scheduledBoundaryColumn R β

theorem scheduledCoefficient_eq_sideCoefficient (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (β_pos : 0 < β) (word : List Bool) :
    scheduledCoefficient R β body β_pos word =
      sideCoefficient R β body (decodeScheduled β_pos word) := by
  rw [scheduledCoefficient, Matrix.dotProduct_mulVec, scheduledBoundaryRow,
    scheduledRow_wordProduct, scheduledRow_dot_boundaryColumn]
  rfl

@[simp] theorem scheduledCoefficient_nil (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (β_pos : 0 < β) :
    scheduledCoefficient R β body β_pos [] = (ternaryCode (nearyMarker β) : R) := by
  rw [scheduledCoefficient_eq_sideCoefficient]
  simp [decodeScheduled, decodeScheduledFrom, sideCoefficient, sideTileProduct,
    sideTerminalColumn, sidePcpMatrix, sideTailBasis, Matrix.vecHead, Matrix.vecTail,
    Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ]

theorem scheduledCoefficient_nil_ne_zero (β : Nat) (body : List TagLetter)
    (β_pos : 0 < β) : scheduledCoefficient ℤ β body β_pos [] ≠ 0 := by
  rw [scheduledCoefficient_nil]
  exact_mod_cast ternaryCode_nearyMarker_ne_zero β

theorem scheduledGenerator_transpose_fixes_boundaryColumn
    (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter)
    (β_pos : 0 < β) (bit : Bool) :
    (scheduledGenerator R β body β_pos bit)ᵀ *ᵥ scheduledBoundaryColumn R β =
      scheduledBoundaryColumn R β := by
  funext index
  cases index with
  | inl index =>
      fin_cases index <;>
        simp [scheduledGenerator, scheduledBoundaryColumn, Matrix.mulVec, Matrix.dotProduct,
          Fintype.sum_sum_type, Fin.sum_univ_succ]
  | inr phase =>
      simp [scheduledGenerator, scheduledBoundaryColumn, Matrix.mulVec, Matrix.dotProduct,
        Fintype.sum_sum_type]

theorem decodeScheduledFrom_length {β : Nat} (β_pos : 0 < β)
    (phase : Fin β) (word : List Bool) :
    (decodeScheduledFrom β_pos phase word).length = word.length := by
  induction word generalizing phase with
  | nil => rfl
  | cons bit word induction =>
      simp [decodeScheduledFrom, induction]

theorem decodeScheduled_length {β : Nat} (β_pos : 0 < β) (word : List Bool) :
    (decodeScheduled β_pos word).length = word.length :=
  decodeScheduledFrom_length β_pos (scheduledInitialPhase β_pos) word

@[simp] theorem strokeTiles_length {β : Nat} (stroke : Stroke TagLetter β) :
    (strokeTiles stroke).length = β := by
  simpa [strokeTiles, Nat.add_comm] using stroke.width

theorem tileHistory_length {β : Nat} (history : List (Stroke TagLetter β)) :
    (tileHistory history).length = history.length * β := by
  induction history with
  | nil => simp [tileHistory]
  | cons stroke history induction =>
      simp [tileHistory_cons, induction, Nat.succ_mul, Nat.add_comm]

/-- A zero coefficient forces the total decoder into the existing exact stroke normal form. -/
theorem decodeScheduled_is_tileHistory_of_coefficient_zero (β : Nat)
    (body : List TagLetter) (β_pos : 0 < β) (word : List Bool)
    (coefficient_zero : scheduledCoefficient ℤ β body β_pos word = 0) :
    ∃ history : List (Stroke TagLetter β),
      decodeScheduled β_pos word = tileHistory history := by
  have side_zero : sideCoefficient ℤ β body (decodeScheduled β_pos word) = 0 := by
    simpa [scheduledCoefficient_eq_sideCoefficient] using coefficient_zero
  have terminal_match :=
    (sideCoefficient_eq_zero_iff_terminal_match β body (decodeScheduled β_pos word)).mp
      side_zero
  exact tileHistory_of_terminal_match β body β_pos (decodeScheduled β_pos word) terminal_match

/-- Incomplete clock cycles are harmless: every zero word has length divisible by `β`. -/
theorem scheduledCoefficient_zero_length_dvd (β : Nat) (body : List TagLetter)
    (β_pos : 0 < β) (word : List Bool)
    (coefficient_zero : scheduledCoefficient ℤ β body β_pos word = 0) :
    β ∣ word.length := by
  obtain ⟨history, decoded⟩ :=
    decodeScheduled_is_tileHistory_of_coefficient_zero β body β_pos word coefficient_zero
  refine ⟨history.length, ?_⟩
  rw [← decodeScheduled_length β_pos word, decoded, tileHistory_length, Nat.mul_comm]

/-- Nonempty scalar zero reachability for the scheduled binary compiler. -/
def HasScheduledBinaryZero (β : Nat) (body : List TagLetter) (β_pos : 0 < β) : Prop :=
  ∃ word : List Bool, word ≠ [] ∧ scheduledCoefficient ℤ β body β_pos word = 0

theorem scheduledBinary_zero_iff_terminal_match (β : Nat) (body : List TagLetter)
    (β_pos : 0 < β) :
    HasScheduledBinaryZero β body β_pos ↔
      ∃ word : List NearyTile,
        spell (nearyUpper β) word ++ nearyMarker β =
          spell (nearyLower β body) word := by
  constructor
  · rintro ⟨bits, _, coefficient_zero⟩
    refine ⟨decodeScheduled β_pos bits, ?_⟩
    exact (sideCoefficient_eq_zero_iff_terminal_match β body _).mp
      (by simpa [scheduledCoefficient_eq_sideCoefficient] using coefficient_zero)
  · rintro ⟨word, terminal_match⟩
    obtain ⟨history, word_eq⟩ :=
      tileHistory_of_terminal_match β body β_pos word terminal_match
    let bits := scheduledHistoryCode history
    have decoded : decodeScheduled β_pos bits = word := by
      change decodeScheduled β_pos (scheduledHistoryCode history) = word
      rw [decodeScheduled_historyCode, ← word_eq]
    have word_nonempty : word ≠ [] := by
      intro word_empty
      have marker_empty : nearyMarker β = [] := by
        simpa [word_empty, spell] using terminal_match
      simp [nearyMarker] at marker_empty
    have bits_nonempty : bits ≠ [] := by
      intro bits_empty
      apply word_nonempty
      calc
        word = decodeScheduled β_pos bits := decoded.symm
        _ = decodeScheduled β_pos [] := by rw [bits_empty]
        _ = [] := rfl
    refine ⟨bits, bits_nonempty, ?_⟩
    rw [scheduledCoefficient_eq_sideCoefficient, decoded]
    exact (sideCoefficient_eq_zero_iff_terminal_match β body word).mpr terminal_match

theorem scheduledBinary_zero_iff_tagHaltsFrom (β : Nat) (body : List TagLetter)
    (β_large : 2 < β) (body_long : β - 1 ≤ body.length)
    (body_divisible : β - 1 ∣ body.length) :
    HasScheduledBinaryZero β body (by omega) ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  rw [scheduledBinary_zero_iff_terminal_match]
  exact terminal_match_iff_tagHaltsFrom β body β_large body_long body_divisible

end MatrixMortality
