import MatrixMortality.ControllerPushout
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
abbrev ScheduledIndex (β : Nat) := ControllerIndex (Fin β)

/-- The first clock phase. -/
def scheduledInitialPhase {β : Nat} (β_pos : 0 < β) : Fin β := ⟨0, β_pos⟩

/-- Advance the cyclic clock by one phase. -/
def scheduledNextPhase {β : Nat} (β_pos : 0 < β) (phase : Fin β) : Fin β :=
  if next_lt : phase.val + 1 < β then
    ⟨phase.val + 1, next_lt⟩
  else
    scheduledInitialPhase β_pos

/-- The clock transition ignores the physical bit. -/
def scheduledTransition {β : Nat} (β_pos : 0 < β) :
    ControllerTransition (Fin β) Bool :=
  fun phase _ => scheduledNextPhase β_pos phase

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
    Matrix (ScheduledIndex β) (ScheduledIndex β) R :=
  (controllerMatrix R
    (fun symbol => tagCode β (scheduledLetter symbol))
    (fun phase symbol => nearyLower β body (scheduledTile phase symbol))
    (scheduledTransition β_pos)
    bit)ᵀ

/-- Embed a side-normal payload row at one active lower-channel phase. -/
def scheduledRow (R : Type*) [CommRing R] {β : Nat} (phase : Fin β)
    (vector : Fin 3 → R) : ScheduledIndex β → R :=
  controllerVector R phase vector

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

/-- Decode from a starting clock phase. Roles are returned in matrix-product order, hence in
reverse input order. -/
def decodeScheduledFrom {β : Nat} (β_pos : 0 < β) :
    Fin β → List Bool → List NearyTile :=
  fun phase word =>
    (controllerDecodeFrom (scheduledTransition β_pos) phase word).map
      fun role => scheduledTile role.1 role.2

@[simp] theorem decodeScheduledFrom_nil {β : Nat} (β_pos : 0 < β) (phase : Fin β) :
    decodeScheduledFrom β_pos phase [] = [] := rfl

@[simp] theorem decodeScheduledFrom_cons {β : Nat} (β_pos : 0 < β)
    (phase : Fin β) (bit : Bool) (word : List Bool) :
    decodeScheduledFrom β_pos phase (bit :: word) =
      decodeScheduledFrom β_pos (scheduledNextPhase β_pos phase) word ++
        [scheduledTile phase bit] := by
  simp [decodeScheduledFrom, controllerDecodeFrom, scheduledTransition, List.map_append]

/-- The phase retained after consuming a binary word. -/
def scheduledResidualFrom {β : Nat} (β_pos : 0 < β) : Fin β → List Bool → Fin β :=
  controllerResidualFrom (scheduledTransition β_pos)

/-- The chronological role stream emitted by a scheduled word. -/
def scheduledRolesFrom {β : Nat} (β_pos : 0 < β) :
    Fin β → List Bool → List NearyTile :=
  fun phase word =>
    (controllerRolesFrom (scheduledTransition β_pos) phase word).map
      fun role => scheduledTile role.1 role.2

/-- Total scheduled decoder from the initial phase. -/
def decodeScheduled {β : Nat} (β_pos : 0 < β) (word : List Bool) : List NearyTile :=
  decodeScheduledFrom β_pos (scheduledInitialPhase β_pos) word

theorem decodeScheduledFrom_eq_reverse_roles {β : Nat} (β_pos : 0 < β)
    (phase : Fin β) (word : List Bool) :
    decodeScheduledFrom β_pos phase word = (scheduledRolesFrom β_pos phase word).reverse := by
  rw [decodeScheduledFrom, controllerDecodeFrom_eq_reverse_roles, scheduledRolesFrom,
    List.map_reverse]

theorem scheduledResidualFrom_append {β : Nat} (β_pos : 0 < β) (phase : Fin β)
    (left right : List Bool) :
    scheduledResidualFrom β_pos phase (left ++ right) =
      scheduledResidualFrom β_pos (scheduledResidualFrom β_pos phase left) right := by
  exact controllerResidualFrom_append (scheduledTransition β_pos) phase left right

theorem scheduledRolesFrom_append {β : Nat} (β_pos : 0 < β) (phase : Fin β)
    (left right : List Bool) :
    scheduledRolesFrom β_pos phase (left ++ right) =
      scheduledRolesFrom β_pos phase left ++
        scheduledRolesFrom β_pos (scheduledResidualFrom β_pos phase left) right := by
  rw [scheduledRolesFrom, controllerRolesFrom_append, List.map_append,
    scheduledRolesFrom, scheduledRolesFrom, scheduledResidualFrom]

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
        simp [scheduledResidualFrom, controllerResidualFrom]
  | cons letter letters induction =>
      have within_clock' : phase.val + (letters.length + 1) < β := by
        simpa using within_clock
      have next_lt : phase.val + 1 < β := by
        omega
      have next_eq :
          scheduledNextPhase β_pos phase = ⟨phase.val + 1, next_lt⟩ := by
        simp [scheduledNextPhase, next_lt]
      have tail_within : phase.val + 1 + letters.length < β := by
        omega
      obtain ⟨roles, residual⟩ :=
        induction (phase := ⟨phase.val + 1, next_lt⟩) tail_within
      constructor
      · simp only [List.map_cons, scheduledRolesFrom, controllerRolesFrom,
          scheduledTransition, scheduledTile, scheduledPhase, scheduledLetter_scheduledBit,
          next_eq]
        rw [if_neg (by omega)]
        exact congrArg (NearyTile.erase letter :: ·) roles
      · simp only [List.map_cons, scheduledResidualFrom, controllerResidualFrom,
          scheduledTransition, next_eq]
        change scheduledResidualFrom β_pos ⟨phase.val + 1, next_lt⟩
            (letters.map scheduledBit) =
          _
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
  have final_phase' :
      (scheduledInitialPhase β_pos).val + stroke.wake.length + 1 = β := by
    simp [scheduledInitialPhase, wake_length]
    omega
  simp [scheduledRolesFrom, controllerRolesFrom, scheduledTile, scheduledPhase,
    strokeTiles, final_phase', PairPhase.tile, List.map_reverse]

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

theorem controllerRoleProduct_eq_scheduledTileProduct
    (R : Type*) [CommRing R] (β : Nat) (body : List TagLetter)
    (roles : List (ControllerRole (Fin β) Bool)) :
    controllerRoleProduct R
        (fun symbol => tagCode β (scheduledLetter symbol))
        (fun state symbol => nearyLower β body (scheduledTile state symbol))
        roles =
      sideTileProduct R β body (roles.map fun role => scheduledTile role.1 role.2) := by
  induction roles with
  | nil => simp [controllerRoleProduct, sideTileProduct]
  | cons role roles induction =>
      simp only [controllerRoleProduct, sideTileProduct, wordProduct_cons, List.map_cons]
      change
        wordProduct
            (controllerRoleMatrix R
              (fun symbol => tagCode β (scheduledLetter symbol))
              (fun state symbol => nearyLower β body (scheduledTile state symbol)))
            roles =
          wordProduct
            (fun tile =>
              sidePcpMatrix R (nearyUpper β tile) (nearyLower β body tile))
            (roles.map fun item => scheduledTile item.1 item.2) at induction
      rw [induction]
      congr 1
      simp [controllerRoleMatrix, nearyUpper_scheduledTile]

theorem scheduledRow_wordProduct (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (β_pos : 0 < β) (phase : Fin β)
    (vector : Fin 3 → R) (word : List Bool) :
    scheduledRow R phase vector ᵥ*
        wordProduct (scheduledGenerator R β body β_pos) word =
      scheduledRow R (scheduledResidualFrom β_pos phase word)
        (sideTileProduct R β body (decodeScheduledFrom β_pos phase word) *ᵥ vector) := by
  change controllerVector R phase vector ᵥ*
      controllerTransposeProduct R
        (fun symbol => tagCode β (scheduledLetter symbol))
        (fun state symbol => nearyLower β body (scheduledTile state symbol))
        (scheduledTransition β_pos) word = _
  rw [controllerVector_vecMul_transposeProduct]
  rw [controllerRoleProduct_eq_scheduledTileProduct]
  rfl

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
  simp [scheduledRow, controllerVector, scheduledBoundaryColumn, dotProduct,
    Fintype.sum_sum_type]

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

theorem scheduledCoefficient_map {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (β : Nat) (body : List TagLetter)
    (β_pos : 0 < β) (word : List Bool) :
    hom (scheduledCoefficient R β body β_pos word) =
      scheduledCoefficient S β body β_pos word := by
  rw [scheduledCoefficient_eq_sideCoefficient, scheduledCoefficient_eq_sideCoefficient]
  exact sideCoefficient_map hom β body (decodeScheduled β_pos word)

@[simp] theorem scheduledCoefficient_nil (R : Type*) [CommRing R] (β : Nat)
    (body : List TagLetter) (β_pos : 0 < β) :
    scheduledCoefficient R β body β_pos [] = (ternaryCode (nearyMarker β) : R) := by
  rw [scheduledCoefficient_eq_sideCoefficient]
  simp [decodeScheduled, decodeScheduledFrom, controllerDecodeFrom]

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
        simp [scheduledGenerator, controllerMatrix, scheduledBoundaryColumn, Matrix.mulVec,
          dotProduct, Fintype.sum_sum_type]
  | inr phase =>
      simp [scheduledGenerator, controllerMatrix, scheduledBoundaryColumn, Matrix.mulVec,
        dotProduct, Fintype.sum_sum_type]

theorem decodeScheduledFrom_length {β : Nat} (β_pos : 0 < β)
    (phase : Fin β) (word : List Bool) :
    (decodeScheduledFrom β_pos phase word).length = word.length := by
  induction word generalizing phase with
  | nil => rfl
  | cons bit word induction =>
      simp only [decodeScheduledFrom, controllerDecodeFrom, scheduledTransition,
        List.map_append, List.length_map, List.length_append, List.length_cons]
      rw [show
        (controllerDecodeFrom (scheduledTransition β_pos)
            (scheduledNextPhase β_pos phase) word).length = word.length by
          simpa [decodeScheduledFrom] using induction (scheduledNextPhase β_pos phase)]
      simp

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

theorem scheduledBinary_zero_iff_terminal_match (β : Nat) (body : List TagLetter)
    (β_pos : 0 < β) :
    WordSeries.HasNonemptyZero (scheduledCoefficient ℤ β body β_pos) ↔
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
    WordSeries.HasNonemptyZero (scheduledCoefficient ℤ β body (by omega)) ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  rw [scheduledBinary_zero_iff_terminal_match]
  exact terminal_match_iff_tagHaltsFrom β body β_large body_long body_divisible

end MatrixMortality
