import MatrixMortality.PairedMortality
import MatrixMortality.LinearRepresentation

/-!
# History-sensitive fracture of paired compression

The global terminal equation need not determine one tag history: a lawful execution may be
followed by a nonexecuted history whose net queue contribution is null.  Minimal Neary bodies
exclude that defect.  On this infinite subclass the terminal word is unique, and an injective
base-five role code gives an exact three-state representation of the paired zero language.
-/

namespace MatrixMortality

open scoped Matrix

/-! ## Injective coding of Neary roles -/

/-- The four Neary roles as the nonzero base-five digits `1,2,3,4`. -/
def historyDigit : NearyTile → Nat
  | .rule .b => 1
  | .rule .c => 2
  | .erase .b => 3
  | .erase .c => 4

@[simp] theorem historyDigit_lt_five (tile : NearyTile) : historyDigit tile < 5 := by
  cases tile with
  | rule letter => cases letter <;> decide
  | erase letter => cases letter <;> decide

@[simp] theorem historyDigit_ne_zero (tile : NearyTile) : historyDigit tile ≠ 0 := by
  cases tile with
  | rule letter => cases letter <;> decide
  | erase letter => cases letter <;> decide

theorem historyDigit_injective : Function.Injective historyDigit := by
  intro x y equality
  cases x with
  | rule xletter =>
      cases y with
      | rule yletter => cases xletter <;> cases yletter <;> simp_all [historyDigit]
      | erase yletter => cases xletter <;> cases yletter <;> simp_all [historyDigit]
  | erase xletter =>
      cases y with
      | rule yletter => cases xletter <;> cases yletter <;> simp_all [historyDigit]
      | erase yletter => cases xletter <;> cases yletter <;> simp_all [historyDigit]

/-- Least-significant-digit-first base-five code of a Neary role word. -/
def historyCode (word : List NearyTile) : Nat :=
  Nat.ofDigits 5 (word.map historyDigit)

theorem digits_historyCode (word : List NearyTile) :
    Nat.digits 5 (historyCode word) = word.map historyDigit := by
  apply Nat.digits_ofDigits 5 (by decide)
  · intro digit member
    obtain ⟨tile, _, rfl⟩ := List.mem_map.mp member
    exact historyDigit_lt_five tile
  · intro nonempty
    have last_mem := List.getLast_mem nonempty
    obtain ⟨tile, _, last_eq⟩ := List.mem_map.mp last_mem
    rw [← last_eq]
    exact historyDigit_ne_zero tile

theorem historyCode_injective : Function.Injective historyCode := by
  intro x y code_eq
  have digits_eq := congrArg (Nat.digits 5) code_eq
  rw [digits_historyCode, digits_historyCode] at digits_eq
  exact (List.map_injective_iff.mpr historyDigit_injective) digits_eq

/-! ## Three-state history encoder -/

/-- Sign coordinate distinguishing the two suffix phases. -/
def historyPhaseSign (R : Type*) [CommRing R] : PairPhase → R
  | .rule => 1
  | .erase => -1

/-- A data control prefixes the role digit selected by the suffix phase. -/
def historyDataMatrix (R : Type*) [CommRing R] : TagLetter → Matrix (Fin 3) (Fin 3) R
  | .b =>
      !![(5 : R), -1, 2;
         0, 0, -1;
         0, 0, 1]
  | .c =>
      !![(5 : R), -1, 3;
         0, 0, -1;
         0, 0, 1]

/-- Each data control is singular: it consumes the entering phase after encoding it in the new
role digit. -/
@[simp] theorem historyDataMatrix_det (R : Type*) [CommRing R] (letter : TagLetter) :
    (historyDataMatrix R letter).det = 0 := by
  cases letter <;>
    simp [historyDataMatrix, Matrix.det_fin_three, Matrix.vecHead, Matrix.vecTail]

/-- The toggle flips the phase sign without changing the role code. -/
def historyToggleMatrix (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![(1 : R), 0, 0;
     0, -1, 0;
     0, 0, 1]

/-- The three matrices encoding every paired control word. -/
def historyGenerator (R : Type*) [CommRing R] :
    PairedControl → Matrix (Fin 3) (Fin 3) R
  | .data letter => historyDataMatrix R letter
  | .toggle => historyToggleMatrix R

/-- Homogeneous initial state `(0,1,1)`. -/
def historyColumn (R : Type*) [CommRing R] : Fin 3 → R := ![0, 1, 1]

/-- Row testing equality with one prescribed role code. -/
def historyRow (R : Type*) [CommRing R] (target : Nat) : Fin 3 → R :=
  ![1, 0, -(target : R)]

/-- Decoded code, suffix-phase sign, and homogeneous unit. -/
def historyState (R : Type*) [CommRing R] (decoded : PairPhase × List NearyTile) :
    Fin 3 → R :=
  ![(historyCode decoded.2 : R), historyPhaseSign R decoded.1, 1]

theorem historyProduct_mulVec_column (R : Type*) [CommRing R]
    (word : List PairedControl) :
    wordProduct (historyGenerator R) word *ᵥ historyColumn R =
      historyState R (suffixDecode word) := by
  induction word with
  | nil =>
      ext coordinate
      fin_cases coordinate <;>
        simp [wordProduct, historyColumn, historyState, suffixDecode, historyCode,
          historyPhaseSign]
  | cons control word induction =>
      rw [wordProduct_cons, ← Matrix.mulVec_mulVec, induction]
      cases decoded_eq : suffixDecode word with
      | mk phase decoded =>
          cases control with
          | toggle =>
              cases phase <;>
                ext coordinate <;>
                fin_cases coordinate <;>
                simp [historyGenerator, historyToggleMatrix, historyState, suffixDecode,
                  decoded_eq, PairPhase.flip, historyPhaseSign, Matrix.mulVec,
                  Matrix.dotProduct, Fin.sum_univ_succ]
          | data letter =>
              cases phase <;> cases letter <;>
                ext coordinate <;>
                fin_cases coordinate <;>
                simp [historyGenerator, historyDataMatrix, historyState, suffixDecode,
                  decoded_eq, PairPhase.tile, historyPhaseSign, historyCode, historyDigit,
                  Nat.ofDigits, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_succ] <;>
                ring

/-- Scalar emitted by the history encoder for one prescribed role word. -/
def historyCoefficient (R : Type*) [CommRing R] (target : Nat)
    (word : List PairedControl) : R :=
  linearCoefficient (historyGenerator R) (historyRow R target) (historyColumn R) word

theorem historyCoefficient_eq_code_sub (R : Type*) [CommRing R] (target : Nat)
    (word : List PairedControl) :
    historyCoefficient R target word =
      (historyCode (decodePairedWord word) : R) - target := by
  rw [historyCoefficient, linearCoefficient, historyProduct_mulVec_column]
  cases decoded_eq : suffixDecode word with
  | mk phase decoded =>
      cases phase <;>
        simp [historyRow, historyState, decodePairedWord, decoded_eq, Matrix.dotProduct,
          Fin.sum_univ_succ, sub_eq_add_neg]

theorem historyCoefficient_zero_iff_decode_eq (target : List NearyTile)
    (word : List PairedControl) :
    historyCoefficient ℚ (historyCode target) word = 0 ↔
      decodePairedWord word = target := by
  rw [historyCoefficient_eq_code_sub, sub_eq_zero]
  constructor
  · intro code_eq
    apply historyCode_injective
    exact_mod_cast code_eq
  · intro decoded_eq
    rw [decoded_eq]

/-! ## Rank-one mortality lift -/

/-- Rank-one separator formed from the history encoder boundaries. -/
def historySeparator (R : Type*) [CommRing R] (target : Nat) :
    Matrix (Fin 3) (Fin 3) R :=
  Matrix.vecMulVec (historyColumn R) (historyRow R target)

/-- Four physical generators: the separator and the three history controls. -/
def historyMortalityFamily (R : Type*) [CommRing R] (target : Nat) :
    Option PairedControl → Matrix (Fin 3) (Fin 3) R :=
  separatedGenerator (historySeparator R target) (historyGenerator R)

theorem historyMortalityFamily_rat_mortal_iff_zero (target : Nat) :
    IsMortal (historyMortalityFamily ℚ target) ↔
      ∃ word : List PairedControl, historyCoefficient ℚ target word = 0 := by
  simpa [historyMortalityFamily, historySeparator, historyCoefficient, linearCoefficient,
    bridgeScalar] using
    mortal_adjoin_outer_iff (historyGenerator ℚ)
      (historyColumn ℚ) (historyRow ℚ target)

theorem historyGenerator_map {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (control : PairedControl) :
    (historyGenerator R control).map hom = historyGenerator S control := by
  cases control with
  | data letter =>
      cases letter <;>
        ext i j <;>
        fin_cases i <;> fin_cases j <;>
        simp [historyGenerator, historyDataMatrix, Matrix.vecHead, Matrix.vecTail]
      all_goals
        first
        | exact map_ofNat hom 5
        | exact map_ofNat hom 3
        | exact map_ofNat hom 2
  | toggle =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [historyGenerator, historyToggleMatrix, Matrix.vecHead, Matrix.vecTail]

theorem historyColumn_map {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) : hom ∘ historyColumn R = historyColumn S := by
  funext coordinate
  fin_cases coordinate <;> simp [historyColumn]

theorem historyRow_map {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (target : Nat) : hom ∘ historyRow R target = historyRow S target := by
  funext coordinate
  fin_cases coordinate <;> simp [historyRow]

theorem historyMortalityFamily_map {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (target : Nat) (label : Option PairedControl) :
    (historyMortalityFamily R target label).map hom =
      historyMortalityFamily S target label := by
  cases label with
  | none =>
      rw [historyMortalityFamily, separatedGenerator, historySeparator, vecMulVec_map,
        historyColumn_map, historyRow_map]
      rfl
  | some control => exact historyGenerator_map hom control

theorem historyMortalityFamily_int_mortal_iff_zero (target : Nat) :
    IsMortal (historyMortalityFamily ℤ target) ↔
      ∃ word : List PairedControl, historyCoefficient ℚ target word = 0 := by
  have family_cast :
      castMatrix ∘ historyMortalityFamily ℤ target = historyMortalityFamily ℚ target := by
    funext label
    exact historyMortalityFamily_map (Int.castRingHom ℚ) target label
  rw [← historyMortalityFamily_rat_mortal_iff_zero, ← family_cast]
  exact (isMortal_cast_iff (historyMortalityFamily ℤ target)).symm

/-- The physical history family has exactly four generators. -/
theorem history_mortality_generator_count :
    Fintype.card (Option PairedControl) = 4 := by decide

/-! ## The minimal-body terminal language -/

/-- The sole terminal role word when the Neary body has its minimum admissible length. -/
def minimalBodyWord (body : List TagLetter) : List NearyTile :=
  .rule .c :: body.map .erase

private theorem consumed_length {β : Nat} (history : List (Stroke TagLetter β)) :
    (consumed history).length = history.length * β := by
  induction history with
  | nil => simp
  | cons stroke history induction =>
      simp [consumed_cons, induction, Nat.succ_mul, Nat.add_comm]

private theorem tagOutput_length_le (β : Nat) (body : List TagLetter)
    (β_pos : 0 < β) (body_length : body.length = β - 1) (letter : TagLetter) :
    (tagOutput body letter).length ≤ β := by
  cases letter <;> simp [tagOutput, nearyBody, body_length] <;> omega

private theorem produced_length_le (β : Nat) (body : List TagLetter)
    (β_pos : 0 < β) (body_length : body.length = β - 1)
    (history : List (Stroke TagLetter β)) :
    (produced (tagOutput body) history).length ≤ history.length * β := by
  induction history with
  | nil => simp
  | cons stroke history induction =>
      rw [produced_cons, List.length_append]
      have head_bound := tagOutput_length_le β body β_pos body_length stroke.head
      calc
        (tagOutput body stroke.head).length +
            (produced (tagOutput body) history).length ≤
            β + history.length * β := Nat.add_le_add head_bound induction
        _ = (history.length + 1) * β := by
          rw [Nat.add_mul, one_mul, Nat.add_comm]

/-- At minimum body length, every terminal match is the initialization stroke and nothing more.

The proof excludes nonexecuted null histories rather than appealing to deterministic execution.
-/
theorem minimalBody_terminal_word_unique (β : Nat) (body : List TagLetter)
    (β_large : 1 < β) (body_length : body.length = β - 1)
    (word : List NearyTile)
    (terminal_match : spell (nearyUpper β) word ++ nearyMarker β =
      spell (nearyLower β body) word) :
    word = minimalBodyWord body := by
  obtain ⟨raw_history, rfl⟩ :=
    tileHistory_of_terminal_match β body (by omega) word terminal_match
  have history_nonempty : raw_history ≠ [] := by
    intro history_empty
    subst raw_history
    simp [spell, nearyMarker] at terminal_match
  obtain ⟨first, history, rfl⟩ := List.exists_cons_of_ne_nil history_nonempty
  have bits_eq := congrArg (fun bits => bits ++ [true]) terminal_match
  change (spell (nearyUpper β) (tileHistory (first :: history)) ++ nearyMarker β) ++
      [true] = spell (nearyLower β body) (tileHistory (first :: history)) ++ [true] at bits_eq
  rw [spell_nearyUpper_tileHistory,
    spell_nearyLower_tileHistory_append_true] at bits_eq
  have encoded_eq : tagEncode β (consumed (first :: history) ++ [.b]) =
      tagEncode β
        (.c :: nearyBody body first.head ++ [.b] ++ produced (tagOutput body) history) := by
    simpa [tagEncode_append, marker_append_true, List.append_assoc] using bits_eq
  have semantic_eq := tagEncode_injective β (by omega) encoded_eq
  have first_head : first.head = .c := by
    have heads_eq := congrArg List.head? semantic_eq
    simpa [consumed_cons, Stroke.letters] using heads_eq
  rw [consumed_cons, Stroke.letters, first_head, nearyBody] at semantic_eq
  have tail_eq : first.wake ++ consumed history ++ [.b] =
      body ++ [.b] ++ produced (tagOutput body) history :=
    (List.cons.inj semantic_eq).2
  have wake_length : first.wake.length = β - 1 := by
    have width := first.width
    omega
  have wake_prefix_common : first.wake <+:
      body ++ [.b] ++ produced (tagOutput body) history := by
    rw [← tail_eq]
    simp [List.append_assoc]
  have body_prefix_common : body <+:
      body ++ [.b] ++ produced (tagOutput body) history := by
    simp [List.append_assoc]
  have wake_prefix : first.wake <+: body :=
    common_prefix_of_length_le wake_prefix_common body_prefix_common <| by
      omega
  have wake_eq : first.wake = body :=
    wake_prefix.eq_of_length <| by omega
  have history_eq : consumed history ++ [.b] =
      [.b] ++ produced (tagOutput body) history := by
    have normalized : first.wake ++ (consumed history ++ [.b]) =
        first.wake ++ ([.b] ++ produced (tagOutput body) history) := by
      simpa [wake_eq, List.append_assoc] using tail_eq
    exact List.append_cancel_left normalized
  have history_empty : history = [] := by
    by_contra history_nonempty
    obtain ⟨stroke, later, rfl⟩ := List.exists_cons_of_ne_nil history_nonempty
    have stroke_head : stroke.head = .b := by
      have heads_eq := congrArg List.head? history_eq
      simpa [consumed_cons, Stroke.letters] using heads_eq
    have lengths_eq := congrArg List.length history_eq
    have later_bound := produced_length_le β body (by omega) body_length later
    rw [consumed_cons, produced_cons, stroke_head] at lengths_eq
    simp only [List.length_append, List.length_singleton, Stroke.length_letters] at lengths_eq
    rw [consumed_length] at lengths_eq
    simp [tagOutput, nearyBody] at lengths_eq
    omega
  subst history
  simp [minimalBodyWord, strokeTiles, first_head, wake_eq]

/-- The canonical minimal-body word satisfies the terminal equation. -/
theorem minimalBody_terminal_match (β : Nat) (body : List TagLetter)
    (β_large : 2 < β) (body_length : body.length = β - 1) :
    spell (nearyUpper β) (minimalBodyWord body) ++ nearyMarker β =
      spell (nearyLower β body) (minimalBodyWord body) := by
  have body_long : β - 1 ≤ body.length := by omega
  have body_divisible : β - 1 ∣ body.length := by
    rw [body_length]
  have initial_short : (body.drop (β - 1) ++ [TagLetter.b]).length < β := by
    simp [body_length]
    omega
  obtain ⟨word, terminal_match⟩ := terminal_match_of_tagHaltsFrom β body β_large body_long
    body_divisible (.stop initial_short)
  rw [minimalBody_terminal_word_unique β body (by omega) body_length word terminal_match]
    at terminal_match
  exact terminal_match

/-- On every minimum-length body, the history encoder and paired compiler have exactly the same
zeros on the complete control free monoid. -/
theorem minimalBody_history_zero_iff_paired_zero (β : Nat) (body : List TagLetter)
    (β_large : 2 < β) (body_length : body.length = β - 1)
    (word : List PairedControl) :
    historyCoefficient ℚ (historyCode (minimalBodyWord body)) word = 0 ↔
      pairedCoefficient ℚ β body word = 0 := by
  rw [historyCoefficient_zero_iff_decode_eq, pairedCoefficient_eq_sideCoefficient,
    sideCoefficient_eq_zero_iff_terminal_match_rat]
  constructor
  · intro decoded_eq
    rw [decoded_eq]
    exact minimalBody_terminal_match β body β_large body_length
  · intro terminal_match
    exact minimalBody_terminal_word_unique β body (by omega) body_length
      (decodePairedWord word) terminal_match

/-- The four integral history matrices are mortal exactly when their three-state coefficient has
a zero, and on the minimum-body subclass this is exactly the paired zero language. -/
theorem minimalBody_historyMortality_iff_paired_zero (β : Nat) (body : List TagLetter)
    (β_large : 2 < β) (body_length : body.length = β - 1) :
    IsMortal (historyMortalityFamily ℤ (historyCode (minimalBodyWord body))) ↔
      ∃ word : List PairedControl, pairedCoefficient ℚ β body word = 0 := by
  rw [historyMortalityFamily_int_mortal_iff_zero]
  exact exists_congr fun word =>
    minimalBody_history_zero_iff_paired_zero β body β_large body_length word

/-! ## Exact rejection of global terminal-word uniqueness -/

namespace NullHistoryCounterexample

/-- A width-three body admitting both a lawful terminal history and its null extension. -/
def body : List TagLetter := [.b, .c, .b, .b]

/-- The terminal word ending with the canonical execution. -/
def shortWord : List NearyTile :=
  [.rule .c, .erase .b, .erase .c,
   .rule .b, .erase .b, .erase .b]

/-- The same terminal word extended by two nonexecuted strokes of net zero queue effect. -/
def longWord : List NearyTile :=
  [.rule .c, .erase .b, .erase .c,
   .rule .b, .erase .b, .erase .b,
   .rule .b, .erase .b, .erase .b,
   .rule .c, .erase .b, .erase .b]

/-- The global terminal equation has distinct witnesses even though tag execution is
deterministic. -/
theorem terminal_word_not_unique :
    spell (nearyUpper 3) shortWord ++ nearyMarker 3 =
        spell (nearyLower 3 body) shortWord ∧
      spell (nearyUpper 3) longWord ++ nearyMarker 3 =
        spell (nearyLower 3 body) longWord ∧
      shortWord ≠ longWord := by
  decide

end NullHistoryCounterexample

/-! ## Concrete minimum-body witness -/

namespace MinimalBodyExample

/-- The smallest admissible width-three body. -/
def body : List TagLetter := [.b, .b]

/-- A control word decoding to the unique terminal role word. -/
def witness : List PairedControl :=
  [.data .c, .toggle, .data .b, .data .b, .toggle]

theorem body_length : body.length = 3 - 1 := by decide

theorem terminal_code : historyCode (minimalBodyWord body) = 92 := by decide

theorem witness_decode : decodePairedWord witness = minimalBodyWord body := by decide

theorem history_witness_zero : historyCoefficient ℚ 92 witness = 0 := by
  rw [← terminal_code, historyCoefficient_zero_iff_decode_eq, witness_decode]

theorem paired_witness_zero : pairedCoefficient ℚ 3 body witness = 0 :=
  (minimalBody_history_zero_iff_paired_zero 3 body (by decide) body_length witness).mp <| by
    simpa [terminal_code] using history_witness_zero

/-- The concrete matrices with separator parameter `92` form a mortal four-generator integral
family. -/
theorem mortality : IsMortal (historyMortalityFamily ℤ 92) :=
  (historyMortalityFamily_int_mortal_iff_zero 92).mpr ⟨witness, history_witness_zero⟩

end MinimalBodyExample

end MatrixMortality
