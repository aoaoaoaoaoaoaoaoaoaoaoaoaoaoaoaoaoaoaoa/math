import MatrixMortality.PairedCompression
import MatrixMortality.WeightedTransducer

/-!
# Binary prefix compiler for five-matrix mortality

The normalized transposed `M₃(5)` family is emitted by a complete binary prefix transducer with
four control states. A two-letter synchronizer aligns every block row, making mortality of the
twelve-state binary realization equivalent to mortality of the source family.
-/

namespace MatrixMortality

open scoped Matrix

/-- Simultaneously side-normalize and transpose the five-matrix Neary family. -/
def normalizedNearyFamily (β : Nat) (body : List TagLetter) :
    Option NearyTile → Square (Fin 3) ℤ :=
  fun label =>
    (sideChangeInv ℤ * nearyMortalityFamilyInt β body label * sideChange ℤ)ᵀ

theorem normalizedNearyFamily_some (β : Nat) (body : List TagLetter)
    (tile : NearyTile) :
    normalizedNearyFamily β body (some tile) =
      (sidePcpMatrix ℤ (nearyUpper β tile) (nearyLower β body tile))ᵀ := by
  rw [normalizedNearyFamily, nearyMortalityFamilyInt, absorbedFamily,
    separatedGenerator, sidePcpMatrix_eq_conjugate]

theorem normalizedNearyFamily_mortal_iff (β : Nat) (body : List TagLetter) :
    IsMortal (normalizedNearyFamily β body) ↔
      IsMortal (nearyMortalityFamilyInt β body) := by
  let conjugated : Option NearyTile → Square (Fin 3) ℤ :=
    fun label => sideChangeInv ℤ * nearyMortalityFamilyInt β body label * sideChange ℤ
  have transpose_form :
      normalizedNearyFamily β body = Matrix.transpose ∘ conjugated := by
    rfl
  rw [transpose_form, isMortal_transpose_iff]
  exact isMortal_conjugate_iff (nearyMortalityFamilyInt β body)
    (sideChange ℤ) (sideChangeInv ℤ)
    (sideChange_mul_sideChangeInv ℤ) (sideChangeInv_mul_sideChange ℤ)

theorem normalizedNearyFamily_mortal_iff_tagHaltsFrom (β : Nat)
    (body : List TagLetter) (β_large : 2 < β) (body_long : β - 1 ≤ body.length)
    (body_divisible : β - 1 ∣ body.length) :
    IsMortal (normalizedNearyFamily β body) ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  rw [normalizedNearyFamily_mortal_iff]
  exact nearyMortalityFamilyInt_mortal_iff_tagHaltsFrom β body β_large body_long
    body_divisible

/-- Proper-prefix states of the complete code `0, 100, 101, 110, 111`. -/
inductive PrefixState where
  | root
  | one
  | ten
  | eleven
  deriving DecidableEq, Repr

instance : Fintype PrefixState :=
  Fintype.ofList [.root, .one, .ten, .eleven] fun state => by cases state <;> simp

/-- Deterministic prefix-state transition. -/
def prefixNext : PrefixState → Bool → PrefixState
  | .root, false => .root
  | .root, true => .one
  | .one, false => .ten
  | .one, true => .eleven
  | .ten, _ => .root
  | .eleven, _ => .root

/-- A completed codeword emits a source label; proper prefixes emit nothing. -/
def prefixEmission : PrefixState → Bool → Option (Option NearyTile)
  | .root, false => some none
  | .root, true => none
  | .one, _ => none
  | .ten, false => some (some (.rule .c))
  | .ten, true => some (some (.rule .b))
  | .eleven, false => some (some (.erase .c))
  | .eleven, true => some (some (.erase .b))

/-- Matrix emitted by one prefix transition. -/
def prefixOutput (β : Nat) (body : List TagLetter) (state : PrefixState)
    (bit : Bool) : Square (Fin 3) ℤ :=
  match prefixEmission state bit with
  | none => 1
  | some label => normalizedNearyFamily β body label

/-- The four-state matrix transducer underlying the twelve-state binary compiler. -/
def prefixMachine (β : Nat) (body : List TagLetter) :
    WeightedTransducer PrefixState Bool (Fin 3) ℤ where
  next := prefixNext
  output := prefixOutput β body

/-- Final state and emitted source word of a prefix-decoder run. -/
def prefixDecode : PrefixState → List Bool → PrefixState × List (Option NearyTile)
  | state, [] => (state, [])
  | state, bit :: word =>
      let tail := prefixDecode (prefixNext state bit) word
      match prefixEmission state bit with
      | none => tail
      | some label => (tail.1, label :: tail.2)

theorem prefixMachine_run (β : Nat) (body : List TagLetter) (state : PrefixState)
    (word : List Bool) :
    (prefixMachine β body).run state word =
      let decoded := prefixDecode state word
      (decoded.1, wordProduct (normalizedNearyFamily β body) decoded.2) := by
  induction word generalizing state with
  | nil => simp [prefixDecode, WeightedTransducer.run]
  | cons bit word induction =>
      rw [WeightedTransducer.run, induction]
      cases state <;>
        cases bit <;>
        simp [prefixMachine, prefixNext, prefixOutput, prefixEmission, prefixDecode,
          wordProduct_cons]

/-- Complete prefix code for the five normalized source matrices. -/
def prefixCode : Option NearyTile → List Bool
  | none => [false]
  | some (.rule .c) => [true, false, false]
  | some (.rule .b) => [true, false, true]
  | some (.erase .c) => [true, true, false]
  | some (.erase .b) => [true, true, true]

/-- Encode a source word by concatenating its complete prefix codewords. -/
def prefixEncode : List (Option NearyTile) → List Bool
  | [] => []
  | label :: word => prefixCode label ++ prefixEncode word

theorem prefixDecode_code_append (label : Option NearyTile) (bits : List Bool) :
    prefixDecode .root (prefixCode label ++ bits) =
      let tail := prefixDecode .root bits
      (tail.1, label :: tail.2) := by
  cases label with
  | none => rfl
  | some tile =>
      cases tile with
      | rule letter | erase letter => cases letter <;> rfl

theorem prefixDecode_encode (word : List (Option NearyTile)) :
    prefixDecode .root (prefixEncode word) = (.root, word) := by
  induction word with
  | nil => rfl
  | cons label word induction =>
      rw [prefixEncode, prefixDecode_code_append, induction]

theorem prefixDecode_append (state : PrefixState) (left right : List Bool) :
    prefixDecode state (left ++ right) =
      let first := prefixDecode state left
      let second := prefixDecode first.1 right
      (second.1, first.2 ++ second.2) := by
  induction left generalizing state with
  | nil => simp [prefixDecode]
  | cons bit left induction =>
      cases state <;>
        cases bit <;>
        simp [prefixNext, prefixEmission, prefixDecode, induction]

/-- The word `00` returns every prefix state to the root. -/
theorem prefixDecode_sync_state (state : PrefixState) :
    (prefixDecode state [false, false]).1 = .root := by
  cases state <;> rfl

theorem prefixMachine_sync_encode_output_zero (β : Nat) (body : List TagLetter)
    (sourceWord : List (Option NearyTile))
    (source_zero : wordProduct (normalizedNearyFamily β body) sourceWord = 0)
    (state : PrefixState) :
    ((prefixMachine β body).run state ([false, false] ++ prefixEncode sourceWord)).2 = 0 := by
  rw [prefixMachine_run, prefixDecode_append]
  dsimp only
  rw [show (prefixDecode state [false, false]).1 = .root from prefixDecode_sync_state state]
  rw [prefixDecode_encode]
  simp only [wordProduct_append, source_zero, mul_zero]

theorem prefixMachine_mortal_iff_normalized (β : Nat) (body : List TagLetter) :
    IsMortal (prefixMachine β body).generator ↔
      IsMortal (normalizedNearyFamily β body) := by
  constructor
  · rintro ⟨bits, _, packed_zero⟩
    let decoded := prefixDecode .root bits
    have output_zero : ((prefixMachine β body).run .root bits).2 = 0 := by
      ext row column
      have entry_zero := congr_fun (congr_fun packed_zero (.root, row))
        (((prefixMachine β body).run .root bits).1, column)
      rw [(prefixMachine β body).wordProduct_apply bits .root
        ((prefixMachine β body).run .root bits).1 row column, if_pos rfl] at entry_zero
      simpa using entry_zero
    have source_zero :
        wordProduct (normalizedNearyFamily β body) decoded.2 = 0 := by
      rw [prefixMachine_run] at output_zero
      exact output_zero
    have decoded_nonempty : decoded.2 ≠ [] := by
      intro decoded_empty
      rw [decoded_empty, wordProduct_nil] at source_zero
      exact one_ne_zero source_zero
    exact ⟨decoded.2, decoded_nonempty, source_zero⟩
  · rintro ⟨sourceWord, _, source_zero⟩
    let bits := [false, false] ++ prefixEncode sourceWord
    refine ⟨bits, by simp [bits], ?_⟩
    ext ⟨start, row⟩ ⟨finish, column⟩
    rw [(prefixMachine β body).wordProduct_apply bits start finish row column]
    by_cases final_eq : ((prefixMachine β body).run start bits).1 = finish
    · rw [if_pos final_eq]
      rw [prefixMachine_sync_encode_output_zero β body sourceWord source_zero start]
      rfl
    · rw [if_neg final_eq]
      simp

theorem prefixMachine_mortal_iff_tagHaltsFrom (β : Nat) (body : List TagLetter)
    (β_large : 2 < β) (body_long : β - 1 ≤ body.length)
    (body_divisible : β - 1 ∣ body.length) :
    IsMortal (prefixMachine β body).generator ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  rw [prefixMachine_mortal_iff_normalized]
  exact normalizedNearyFamily_mortal_iff_tagHaltsFrom β body β_large body_long
    body_divisible

/-! ## Ten-dimensional common image -/

theorem normalizedNearyFamily_rule_erase_row_zero (β : Nat)
    (body : List TagLetter) (letter : TagLetter) (column : Fin 3) :
    normalizedNearyFamily β body (some (.rule letter)) 0 column =
      normalizedNearyFamily β body (some (.erase letter)) 0 column := by
  rw [normalizedNearyFamily_some, normalizedNearyFamily_some]
  fin_cases column <;>
    simp [sidePcpMatrix, nearyUpper]

theorem normalizedNearyFamily_rule_erase_row_two (β : Nat)
    (body : List TagLetter) (letter : TagLetter) (column : Fin 3) :
    normalizedNearyFamily β body (some (.rule letter)) 2 column =
      normalizedNearyFamily β body (some (.erase letter)) 2 column := by
  rw [normalizedNearyFamily_some, normalizedNearyFamily_some]
  fin_cases column <;>
    simp [sidePcpMatrix, nearyUpper]

/-- Small coordinate represented by each coordinate of the four three-state prefix blocks. -/
def prefixCoordinate : PrefixState → Fin 3 → Fin 10
  | .root, ⟨0, _⟩ => 0
  | .root, ⟨1, _⟩ => 1
  | .root, ⟨2, _⟩ => 2
  | .one, ⟨0, _⟩ => 3
  | .one, ⟨1, _⟩ => 4
  | .one, ⟨2, _⟩ => 5
  | .ten, ⟨0, _⟩ => 6
  | .ten, ⟨1, _⟩ => 7
  | .ten, ⟨2, _⟩ => 8
  | .eleven, ⟨0, _⟩ => 6
  | .eleven, ⟨1, _⟩ => 9
  | .eleven, ⟨2, _⟩ => 8

/-- Chosen large representative of each ten-state coordinate. -/
def prefixRepresentative : Fin 10 → PrefixState × Fin 3
  | ⟨0, _⟩ => (.root, 0)
  | ⟨1, _⟩ => (.root, 1)
  | ⟨2, _⟩ => (.root, 2)
  | ⟨3, _⟩ => (.one, 0)
  | ⟨4, _⟩ => (.one, 1)
  | ⟨5, _⟩ => (.one, 2)
  | ⟨6, _⟩ => (.ten, 0)
  | ⟨7, _⟩ => (.ten, 1)
  | ⟨8, _⟩ => (.ten, 2)
  | ⟨9, _⟩ => (.eleven, 1)

theorem prefixCoordinate_representative (coordinate : Fin 10) :
    prefixCoordinate (prefixRepresentative coordinate).1
      (prefixRepresentative coordinate).2 = coordinate := by
  fin_cases coordinate <;> rfl

theorem prefixCoordinate_injective (state : PrefixState) :
    Function.Injective (prefixCoordinate state) := by
  intro left right equal
  cases state <;> fin_cases left <;> fin_cases right <;> simp_all [prefixCoordinate]

/-- Integral embedding of the shared ten-coordinate carrier into the four prefix blocks. -/
def prefixEmbed : Matrix (PrefixState × Fin 3) (Fin 10) ℤ :=
  fun large small =>
    if prefixCoordinate large.1 large.2 = small then 1 else 0

/-- Coordinate retraction choosing the `ten` copy of the two shared coordinates. -/
def prefixRetract : Matrix (Fin 10) (PrefixState × Fin 3) ℤ :=
  fun small large =>
    if prefixRepresentative small = large then 1 else 0

theorem prefixRetract_mul_prefixEmbed : prefixRetract * prefixEmbed = 1 := by
  ext row column
  rw [Matrix.mul_apply, Finset.sum_eq_single (prefixRepresentative row)]
  · simp [prefixRetract, prefixEmbed, prefixCoordinate_representative, Matrix.one_apply]
  · intro large _ large_ne
    simp [prefixRetract, Ne.symm large_ne]
  · intro representative_absent
    exact (representative_absent (Finset.mem_univ _)).elim

theorem prefixEmbed_mul_prefixRetract_mul_apply
    (matrix : Matrix (PrefixState × Fin 3) (PrefixState × Fin 3) ℤ)
    (row column : PrefixState × Fin 3) :
    (prefixEmbed * prefixRetract * matrix) row column =
      matrix (prefixRepresentative (prefixCoordinate row.1 row.2)) column := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  rw [Finset.sum_eq_single (prefixCoordinate row.1 row.2)]
  · simp only [prefixEmbed, if_pos, one_mul]
    rw [Matrix.mul_apply, Finset.sum_eq_single
      (prefixRepresentative (prefixCoordinate row.1 row.2))]
    · simp [prefixRetract]
    · intro large _ large_ne
      simp [prefixRetract, Ne.symm large_ne]
    · intro representative_absent
      exact (representative_absent (Finset.mem_univ _)).elim
  · intro small _ small_ne
    simp [prefixEmbed, Ne.symm small_ne]
  · intro coordinate_absent
    exact (coordinate_absent (Finset.mem_univ _)).elim

/-- The two rows duplicated between prefix states `10` and `11`. -/
def SharesPrefixRows
    (matrix : Matrix (PrefixState × Fin 3) (PrefixState × Fin 3) ℤ) : Prop :=
  (∀ column, matrix (.ten, 0) column = matrix (.eleven, 0) column) ∧
    ∀ column, matrix (.ten, 2) column = matrix (.eleven, 2) column

theorem prefixGenerator_sharesRows (β : Nat) (body : List TagLetter) (bit : Bool) :
    SharesPrefixRows ((prefixMachine β body).generator bit) := by
  cases bit <;>
    constructor <;>
    rintro ⟨finish, column⟩ <;>
    cases finish <;>
    fin_cases column <;>
    simp [prefixMachine, WeightedTransducer.generator, prefixNext,
      prefixOutput, prefixEmission, normalizedNearyFamily_rule_erase_row_zero,
      normalizedNearyFamily_rule_erase_row_two]

theorem prefixProjection_generator (β : Nat) (body : List TagLetter) (bit : Bool) :
    prefixEmbed * prefixRetract * (prefixMachine β body).generator bit =
      (prefixMachine β body).generator bit := by
  have shared := prefixGenerator_sharesRows β body bit
  ext ⟨state, row⟩ column
  rw [prefixEmbed_mul_prefixRetract_mul_apply]
  cases state with
  | root => fin_cases row <;> rfl
  | one => fin_cases row <;> rfl
  | ten => fin_cases row <;> rfl
  | eleven =>
      fin_cases row
      · simpa [prefixCoordinate, prefixRepresentative] using shared.1 column
      · rfl
      · simpa [prefixCoordinate, prefixRepresentative] using shared.2 column

/-- The explicit pair of ten-state restricted generators. -/
def restrictedPrefixGenerator (β : Nat) (body : List TagLetter) (bit : Bool) :
    Square (Fin 10) ℤ :=
  prefixRetract * (prefixMachine β body).generator bit * prefixEmbed

/-- Entry formula after eliminating the one-hot restriction and deterministic prefix
transition. -/
theorem restrictedPrefixGenerator_apply (β : Nat) (body : List TagLetter)
    (bit : Bool) (row column : Fin 10) :
    restrictedPrefixGenerator β body bit row column =
      ∑ payloadColumn : Fin 3,
        if prefixCoordinate
            (prefixNext (prefixRepresentative row).1 bit) payloadColumn = column
        then prefixOutput β body (prefixRepresentative row).1 bit
          (prefixRepresentative row).2 payloadColumn
        else 0 := by
  rw [restrictedPrefixGenerator, Matrix.mul_assoc, Matrix.mul_apply]
  rw [Finset.sum_eq_single (prefixRepresentative row)]
  · simp only [prefixRetract, if_pos, one_mul]
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single
      (prefixNext (prefixRepresentative row).1 bit)]
    · apply Finset.sum_congr rfl
      intro payloadColumn _
      simp [prefixMachine, WeightedTransducer.generator, prefixEmbed]
    · intro state _ state_ne
      apply Finset.sum_eq_zero
      intro payloadColumn _
      simp [prefixMachine, WeightedTransducer.generator, Ne.symm state_ne]
    · intro state_absent
      exact (state_absent (Finset.mem_univ _)).elim
  · intro large _ large_ne
    simp [prefixRetract, Ne.symm large_ne]
  · intro representative_absent
    exact (representative_absent (Finset.mem_univ _)).elim

/-- Sparse coordinate form: one prefix transition routes each payload column to a distinct
restricted coordinate. -/
theorem restrictedPrefixGenerator_apply_sparse (β : Nat) (body : List TagLetter)
    (bit : Bool) (row column : Fin 10) :
    restrictedPrefixGenerator β body bit row column =
      let state := prefixNext (prefixRepresentative row).1 bit
      let output := prefixOutput β body (prefixRepresentative row).1 bit
      if prefixCoordinate state 0 = column then output (prefixRepresentative row).2 0
      else if prefixCoordinate state 1 = column then output (prefixRepresentative row).2 1
      else if prefixCoordinate state 2 = column then output (prefixRepresentative row).2 2
      else 0 := by
  rw [restrictedPrefixGenerator_apply]
  simp only [Fin.sum_univ_succ]
  by_cases zero : prefixCoordinate
      (prefixNext (prefixRepresentative row).1 bit) 0 = column
  · have one_ne : prefixCoordinate
        (prefixNext (prefixRepresentative row).1 bit) 1 ≠ column := by
      intro one
      exact Fin.zero_ne_one <|
        prefixCoordinate_injective _ (zero.trans one.symm)
    have two_ne : prefixCoordinate
        (prefixNext (prefixRepresentative row).1 bit) 2 ≠ column := by
      intro two
      exact (by decide : (0 : Fin 3) ≠ 2) <|
        prefixCoordinate_injective _ (zero.trans two.symm)
    simp [zero, one_ne, two_ne]
  · by_cases one : prefixCoordinate
        (prefixNext (prefixRepresentative row).1 bit) 1 = column
    · have two_ne : prefixCoordinate
          (prefixNext (prefixRepresentative row).1 bit) 2 ≠ column := by
        intro two
        exact (by decide : (1 : Fin 3) ≠ 2) <|
          prefixCoordinate_injective _ (one.trans two.symm)
      simp [zero, one, two_ne]
    · by_cases two : prefixCoordinate
          (prefixNext (prefixRepresentative row).1 bit) 2 = column
      · simp [zero, one, two]
      · simp [zero, one, two]

theorem prefixGenerator_intertwine (β : Nat) (body : List TagLetter) (bit : Bool) :
    (prefixMachine β body).generator bit * prefixEmbed =
      prefixEmbed * restrictedPrefixGenerator β body bit := by
  rw [restrictedPrefixGenerator]
  calc
    (prefixMachine β body).generator bit * prefixEmbed =
        (prefixEmbed * prefixRetract * (prefixMachine β body).generator bit) *
          prefixEmbed := by rw [prefixProjection_generator]
    _ = prefixEmbed *
        (prefixRetract * (prefixMachine β body).generator bit * prefixEmbed) := by
      simp only [Matrix.mul_assoc]

theorem prefixGenerator_zero_factors (β : Nat) (body : List TagLetter) :
    (prefixMachine β body).generator false =
      prefixEmbed * (prefixRetract * (prefixMachine β body).generator false) := by
  calc
    (prefixMachine β body).generator false =
        prefixEmbed * prefixRetract * (prefixMachine β body).generator false :=
      (prefixProjection_generator β body false).symm
    _ = prefixEmbed * (prefixRetract * (prefixMachine β body).generator false) := by
      rw [Matrix.mul_assoc]

theorem restrictedPrefixGenerator_mortal_iff_prefixMachine (β : Nat)
    (body : List TagLetter) :
    IsMortal (restrictedPrefixGenerator β body) ↔
      IsMortal (prefixMachine β body).generator := by
  exact isMortal_commonImage_iff (prefixMachine β body).generator
    (restrictedPrefixGenerator β body) prefixEmbed prefixRetract
    prefixRetract_mul_prefixEmbed (prefixGenerator_intertwine β body) false
    (prefixRetract * (prefixMachine β body).generator false)
    (prefixGenerator_zero_factors β body)

theorem restrictedPrefixGenerator_mortal_iff_tagHaltsFrom (β : Nat)
    (body : List TagLetter) (β_large : 2 < β) (body_long : β - 1 ≤ body.length)
    (body_divisible : β - 1 ∣ body.length) :
    IsMortal (restrictedPrefixGenerator β body) ↔
      TagHaltsFrom β (tagOutput body) (body.drop (β - 1) ++ [.b]) := by
  rw [restrictedPrefixGenerator_mortal_iff_prefixMachine]
  exact prefixMachine_mortal_iff_tagHaltsFrom β body β_large body_long body_divisible

end MatrixMortality
