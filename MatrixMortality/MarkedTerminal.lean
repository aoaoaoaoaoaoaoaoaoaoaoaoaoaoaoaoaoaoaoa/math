import MatrixMortality.TerminalSource

/-!
# A synchronizing terminal tile

A fresh marker turns the forced terminal tile into a delimiter rather than a long unary guard.
The first marker tile compatible with a PCP solution closes the current residual immediately.
Consequently any primitive solution contains it exactly once, at the end, as soon as ordinary
tiles alone cannot solve the instance.
-/

namespace MatrixMortality

/-- Append a fresh marker to a word, representing ordinary letters by `some`. -/
def suture {α : Type*} (word : List α) : List (Option α) := word.map some ++ [none]

@[simp] theorem suture_nil {α : Type*} : suture ([] : List α) = [none] := rfl

@[simp] theorem suture_cons {α : Type*} (a : α) (word : List α) :
    suture (a :: word) = some a :: suture word := by
  simp [suture]

theorem suture_prefix_iff {α : Type*} (x y : List α) : suture x <+: suture y ↔ x = y := by
  induction x generalizing y with
  | nil => cases y <;> simp
  | cons a x ih =>
      cases y with
      | nil => simp
      | cons b y => simp [ih]

/-- Two words are prefix-comparable. -/
def PrefixComparable {α : Type*} (x y : List α) : Prop := x <+: y ∨ y <+: x

theorem suture_prefixComparable_iff {α : Type*} (x y : List α) :
    PrefixComparable (suture x) (suture y) ↔ x = y := by
  simp [PrefixComparable, suture_prefix_iff, eq_comm]

theorem spell_append {ι α : Type*} (side : ι → List α) (x y : List ι) :
    spell side (x ++ y) = spell side x ++ spell side y := by
  simp [spell, List.map_append]

theorem spell_map {ι α β : Type*} (f : α → β) (side : ι → List α) (word : List ι) :
    spell (fun i => (side i).map f) word = (spell side word).map f := by
  induction word with
  | nil => simp [spell]
  | cons i word ih => simp [spell, Function.comp_def, ih]

/-- Lift ordinary PCP words into the marked alphabet and use `suture terminal` for the
distinguished tile. -/
def markedSide {ι α : Type*} (side : ι → List α) (terminal : List α) :
    Option ι → List (Option α) :=
  fullSide (fun i => (side i).map some) (suture terminal)

theorem spell_marked_terminal {ι α : Type*} (side : ι → List α)
    (terminal : List α) (word : List ι) :
    spell (markedSide side terminal) (word.map some ++ [none]) =
      suture (spell side word ++ terminal) := by
  simp [markedSide, spell_map_some_append_none, spell_map, suture]

theorem exists_first_none {ι : Type*} {word : List (Option ι)} (h : none ∈ word) :
    ∃ interior : List ι, ∃ suffix : List (Option ι),
      word = interior.map some ++ none :: suffix := by
  induction word with
  | nil => simp at h
  | cons head word ih =>
      cases head with
      | none => exact ⟨[], word, rfl⟩
      | some i =>
          have htail : none ∈ word := by simpa using h
          obtain ⟨interior, suffix, rfl⟩ := ih htail
          exact ⟨i :: interior, suffix, by simp⟩

theorem exists_eq_map_some_of_none_not_mem {ι : Type*} {word : List (Option ι)}
    (h : none ∉ word) : ∃ interior : List ι, word = interior.map some := by
  induction word with
  | nil => exact ⟨[], rfl⟩
  | cons head word ih =>
      cases head with
      | none => simp at h
      | some i =>
          have htail : none ∉ word := by simpa using h
          obtain ⟨interior, rfl⟩ := ih htail
          exact ⟨i :: interior, by simp⟩

theorem spell_marked_ordinary {ι α : Type*} (side : ι → List α)
    (terminal : List α) (word : List ι) :
    spell (markedSide side terminal) (word.map some) = (spell side word).map some := by
  simpa only [spell, markedSide, fullSide, List.map_map, Function.comp_apply] using
    (spell_map (fun a : α => some a) side word)

/-- If the ordinary tiles have no solution, every solution of the marked instance uses the
terminal tile. -/
theorem marked_solution_uses_terminal {ι α : Type*} (u v : ι → List α)
    (terminal : List α) (hordinary : ¬ ∃ word, IsPCPSolution u v word) :
    ∀ word : List (Option ι),
      IsPCPSolution (markedSide u terminal) (markedSide v []) word → none ∈ word := by
  intro word hword
  by_contra hnone
  obtain ⟨interior, rfl⟩ := exists_eq_map_some_of_none_not_mem hnone
  apply hordinary
  refine ⟨interior, ?_, ?_⟩
  · simpa using hword.1
  · have hlifted := hword.2
    rw [spell_marked_ordinary, spell_marked_ordinary] at hlifted
    exact (List.map_injective_iff.mpr fun _ _ h => Option.some.inj h) hlifted

/-- Distinct final symbols on every ordinary tile rule out an ordinary PCP solution. -/
theorem no_ordinary_solution_of_final_mismatch {ι α : Type*} (u v : ι → List α)
    (upper lower : α) (hne : upper ≠ lower)
    (hfinal : ∀ i, ∃ u₀ v₀, u i = u₀ ++ [upper] ∧ v i = v₀ ++ [lower]) :
    ¬ ∃ word, IsPCPSolution u v word := by
  rintro ⟨word, hword, hspell⟩
  let i := word.getLast hword
  let front := word.dropLast
  have hdecompose : word = front ++ [i] := by
    simpa [i, front] using (List.dropLast_append_getLast hword).symm
  obtain ⟨u₀, v₀, hu, hv⟩ := hfinal i
  have hlast := congrArg List.getLast? hspell
  rw [hdecompose, spell_append, spell_append] at hlast
  simp [spell, hu, hv] at hlast
  exact hne hlast

theorem spelled_prefixes_comparable {ι α : Type*} {u v : ι → List α}
    {front tail : List ι} (hsolution : spell u (front ++ tail) = spell v (front ++ tail)) :
    PrefixComparable (spell u front) (spell v front) := by
  have hu : spell u front <+: spell u (front ++ tail) := by
    rw [spell_append]
    exact List.prefix_append _ _
  have hv : spell v front <+: spell u (front ++ tail) := by
    rw [hsolution, spell_append]
    exact List.prefix_append _ _
  exact List.prefix_or_prefix_of_prefix hu hv

/-- A fresh terminal marker discharges the primitive-terminal source hypothesis. The sole
instance-specific premise is that every solution uses the distinguished tile at least once. -/
theorem marked_primitive_terminal {ι α : Type*} (u v : ι → List α) (terminal : List α)
    (huses : ∀ word : List (Option ι),
      IsPCPSolution (markedSide u terminal) (markedSide v []) word → none ∈ word) :
    ∀ word : List (Option ι),
      IsPrimitivePCPSolution (markedSide u terminal) (markedSide v []) word →
        ∃ interior : List ι, word = interior.map some ++ [none] := by
  intro word hprimitive
  obtain ⟨interior, suffix, hword⟩ := exists_first_none (huses word hprimitive.1)
  let front : List (Option ι) := interior.map some ++ [none]
  have hdecompose : word = front ++ suffix := by
    simpa [front] using hword
  have hcomparable : PrefixComparable
      (spell (markedSide u terminal) front) (spell (markedSide v []) front) := by
    apply spelled_prefixes_comparable
    simpa [hdecompose] using hprimitive.1.2
  have hinterior : spell u interior ++ terminal = spell v interior := by
    apply (suture_prefixComparable_iff _ _).mp
    simpa [front, spell_marked_terminal] using hcomparable
  have hfront : IsPCPSolution (markedSide u terminal) (markedSide v []) front := by
    constructor
    · simp [front]
    · simpa [front, spell_marked_terminal] using congrArg suture hinterior
  by_cases hsuffix : suffix = []
  · subst suffix
    exact ⟨interior, by simpa [front] using hdecompose⟩
  · exfalso
    apply hprimitive.2
    refine ⟨front, suffix, by simp [front], hsuffix, hdecompose, hfront, ?_⟩
    constructor
    · exact hsuffix
    · have htotal :
          spell (markedSide u terminal) front ++ spell (markedSide u terminal) suffix =
            spell (markedSide v []) front ++ spell (markedSide v []) suffix := by
        rw [← spell_append, ← spell_append, ← hdecompose]
        exact hprimitive.1.2
      rw [hfront.2] at htotal
      exact List.append_cancel_left htotal

theorem marked_primitive_terminal_of_final_mismatch {ι α : Type*} (u v : ι → List α)
    (terminal : List α) (upper lower : α) (hne : upper ≠ lower)
    (hfinal : ∀ i, ∃ u₀ v₀, u i = u₀ ++ [upper] ∧ v i = v₀ ++ [lower]) :
    ∀ word : List (Option ι),
      IsPrimitivePCPSolution (markedSide u terminal) (markedSide v []) word →
        ∃ interior : List ι, word = interior.map some ++ [none] :=
  marked_primitive_terminal u v terminal <|
    marked_solution_uses_terminal u v terminal <|
      no_ordinary_solution_of_final_mismatch u v upper lower hne hfinal

/-- Solvability of the synchronously marked PCP instance is exactly the right-bounded
ordinary word equation. -/
theorem marked_solvable_iff_terminal_match_of_final_mismatch {ι α : Type*}
    (u v : ι → List α) (terminal : List α) (upper lower : α) (hne : upper ≠ lower)
    (hfinal : ∀ i, ∃ u₀ v₀, u i = u₀ ++ [upper] ∧ v i = v₀ ++ [lower]) :
    (∃ word, IsPCPSolution (markedSide u terminal) (markedSide v []) word) ↔
      ∃ interior, spell u interior ++ terminal = spell v interior := by
  let u' : ι → List (Option α) := fun i => (u i).map some
  let v' : ι → List (Option α) := fun i => (v i).map some
  have hprimitive : ∀ word : List (Option ι),
      IsPrimitivePCPSolution (fullSide u' (suture terminal))
          (fullSide v' (suture [])) word →
        ∃ interior : List ι, word = interior.map some ++ [none] := by
    simpa [u', v', markedSide] using
      (marked_primitive_terminal_of_final_mismatch u v terminal upper lower hne hfinal)
  change (∃ word, IsPCPSolution (fullSide u' (suture terminal))
      (fullSide v' (suture [])) word) ↔ _
  rw [pcp_solvable_iff_terminal_match_of_primitive_terminal
    u' v' (suture terminal) (suture []) hprimitive]
  apply exists_congr
  intro interior
  have hu : spell u' interior = (spell u interior).map some := by
    exact spell_map some u interior
  have hv : spell v' interior = (spell v interior).map some := by
    exact spell_map some v interior
  rw [hu, hv]
  constructor
  · intro hmatch
    have hsuture : suture (spell u interior ++ terminal) = suture (spell v interior) := by
      simpa [suture, List.map_append, List.append_assoc] using hmatch
    exact (suture_prefix_iff _ _).mp (by simp [hsuture])
  · intro hmatch
    simpa [suture, List.map_append, List.append_assoc] using congrArg suture hmatch

/-! ## Fixed-length recoding into the binary alphabet -/

def markedBitCode : Option Bool → List Bool
  | some bit => [false, bit]
  | none => [true, true]

def encodeMarkedBits (word : List (Option Bool)) : List Bool := spell markedBitCode word

def decodeMarkedBits : List Bool → List (Option Bool)
  | false :: bit :: tail => some bit :: decodeMarkedBits tail
  | true :: _ :: tail => none :: decodeMarkedBits tail
  | _ => []

@[simp] theorem decode_encodeMarkedBits (word : List (Option Bool)) :
    decodeMarkedBits (encodeMarkedBits word) = word := by
  induction word with
  | nil => rfl
  | cons symbol word ih =>
      change decodeMarkedBits (markedBitCode symbol ++ encodeMarkedBits word) = symbol :: word
      cases symbol with
      | none => simp [markedBitCode, decodeMarkedBits, ih]
      | some bit =>
          cases bit <;> simp [markedBitCode, decodeMarkedBits, ih]

theorem encodeMarkedBits_injective : Function.Injective encodeMarkedBits :=
  (Function.leftInverse_iff_comp.mpr funext_decode_encodeMarkedBits).injective
where
  funext_decode_encodeMarkedBits : decodeMarkedBits ∘ encodeMarkedBits = id := by
    funext word
    exact decode_encodeMarkedBits word

theorem encodeMarkedBits_append (x y : List (Option Bool)) :
    encodeMarkedBits (x ++ y) = encodeMarkedBits x ++ encodeMarkedBits y := by
  exact spell_append markedBitCode x y

def binaryMarkedSide {ι : Type*} (side : ι → List Bool) (terminal : List Bool) :
    Option ι → List Bool := fun i => encodeMarkedBits (markedSide side terminal i)

def binaryMarkedOrdinary {ι : Type*} (side : ι → List Bool) (i : ι) : List Bool :=
  encodeMarkedBits ((side i).map some)

def binaryMarkedTerminal (terminal : List Bool) : List Bool :=
  encodeMarkedBits (suture terminal)

theorem binaryMarkedSide_eq_fullSide {ι : Type*} (side : ι → List Bool)
    (terminal : List Bool) :
    binaryMarkedSide side terminal =
      fullSide (binaryMarkedOrdinary side) (binaryMarkedTerminal terminal) := by
  funext i
  cases i <;> rfl

theorem spell_binaryMarkedSide {ι : Type*} (side : ι → List Bool)
    (terminal : List Bool) (word : List (Option ι)) :
    spell (binaryMarkedSide side terminal) word =
      encodeMarkedBits (spell (markedSide side terminal) word) := by
  induction word with
  | nil => rfl
  | cons i word ih =>
      change encodeMarkedBits (markedSide side terminal i) ++
          spell (binaryMarkedSide side terminal) word =
        encodeMarkedBits (markedSide side terminal i ++ spell (markedSide side terminal) word)
      rw [ih, ← encodeMarkedBits_append]

theorem binaryMarked_solution_iff {ι : Type*} (u v : ι → List Bool)
    (terminal : List Bool) (word : List (Option ι)) :
    IsPCPSolution (binaryMarkedSide u terminal) (binaryMarkedSide v []) word ↔
      IsPCPSolution (markedSide u terminal) (markedSide v []) word := by
  simp only [IsPCPSolution, spell_binaryMarkedSide]
  exact and_congr_right fun _ => encodeMarkedBits_injective.eq_iff

theorem binaryMarked_primitive_iff {ι : Type*} (u v : ι → List Bool)
    (terminal : List Bool) (word : List (Option ι)) :
    IsPrimitivePCPSolution (binaryMarkedSide u terminal) (binaryMarkedSide v []) word ↔
      IsPrimitivePCPSolution (markedSide u terminal) (markedSide v []) word := by
  simp only [IsPrimitivePCPSolution, binaryMarked_solution_iff]

theorem binaryMarked_primitive_terminal_of_final_mismatch {ι : Type*}
    (u v : ι → List Bool) (terminal : List Bool) (upper lower : Bool) (hne : upper ≠ lower)
    (hfinal : ∀ i, ∃ u₀ v₀, u i = u₀ ++ [upper] ∧ v i = v₀ ++ [lower]) :
    ∀ word : List (Option ι),
      IsPrimitivePCPSolution (binaryMarkedSide u terminal) (binaryMarkedSide v []) word →
        ∃ interior : List ι, word = interior.map some ++ [none] := by
  intro word hword
  apply marked_primitive_terminal_of_final_mismatch u v terminal upper lower hne hfinal word
  exact (binaryMarked_primitive_iff u v terminal word).mp hword

/-- The fixed two-bit code neither creates nor destroys marked PCP solutions. -/
theorem binaryMarked_solvable_iff_terminal_match_of_final_mismatch {ι : Type*}
    (u v : ι → List Bool) (terminal : List Bool) (upper lower : Bool) (hne : upper ≠ lower)
    (hfinal : ∀ i, ∃ u₀ v₀, u i = u₀ ++ [upper] ∧ v i = v₀ ++ [lower]) :
    (∃ word, IsPCPSolution (binaryMarkedSide u terminal) (binaryMarkedSide v []) word) ↔
      ∃ interior, spell u interior ++ terminal = spell v interior := by
  rw [show (∃ word, IsPCPSolution (binaryMarkedSide u terminal)
      (binaryMarkedSide v []) word) ↔
      ∃ word, IsPCPSolution (markedSide u terminal) (markedSide v []) word by
    exact exists_congr fun word => binaryMarked_solution_iff u v terminal word]
  exact marked_solvable_iff_terminal_match_of_final_mismatch
    u v terminal upper lower hne hfinal

theorem spell_binaryMarkedOrdinary {ι : Type*} (side : ι → List Bool) (word : List ι) :
    spell (binaryMarkedOrdinary side) word =
      encodeMarkedBits ((spell side word).map some) := by
  induction word with
  | nil => rfl
  | cons i word ih =>
      simp only [spell, List.map_cons, List.join_cons, List.map_append, binaryMarkedOrdinary]
      change encodeMarkedBits ((side i).map some) ++ spell (binaryMarkedOrdinary side) word =
        encodeMarkedBits ((side i).map some ++ (spell side word).map some)
      rw [ih, ← encodeMarkedBits_append]

/-- The exact integer family obtained after binary marker recoding. -/
def synchronizedFamilyInt {ι : Type*} (u v : ι → List Bool) (terminal : List Bool) :
    Option ι → Matrix (Fin 3) (Fin 3) Int :=
  absorbedFamilyInt (binaryMarkedOrdinary u) (binaryMarkedOrdinary v)
    (binaryMarkedTerminal terminal) (binaryMarkedTerminal [])

/-- Fresh-marker synchronization and fixed-length binary recoding preserve the terminal word
equation all the way through the exact five-matrix compiler. -/
theorem synchronizedFamilyInt_mortal_iff_terminal_match {ι : Type*}
    (u v : ι → List Bool) (terminal : List Bool) :
    IsMortal (synchronizedFamilyInt u v terminal) ↔
      ∃ word, spell u word ++ terminal = spell v word := by
  rw [synchronizedFamilyInt, absorbedFamilyInt_mortal_iff_terminal_match]
  apply exists_congr
  intro word
  rw [spell_binaryMarkedOrdinary, spell_binaryMarkedOrdinary]
  constructor
  · intro hmatch
    have hencoded : encodeMarkedBits (suture (spell u word ++ terminal)) =
        encodeMarkedBits (suture (spell v word)) := by
      simpa [binaryMarkedTerminal, suture, encodeMarkedBits_append, List.map_append,
        List.append_assoc] using hmatch
    exact (suture_prefix_iff _ _).mp <| by
      simp [encodeMarkedBits_injective hencoded]
  · intro hmatch
    have hencoded := congrArg encodeMarkedBits (congrArg suture hmatch)
    simpa [binaryMarkedTerminal, suture, encodeMarkedBits_append, List.map_append,
      List.append_assoc] using hencoded

end MatrixMortality
