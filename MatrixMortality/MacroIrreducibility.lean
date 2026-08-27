import MatrixMortality.NearyEncoding

/-!
# Exact Neary macro factorizations

An exact macro factorization replaces each of Neary's four source roles by an arbitrary word
over a new alphabet, then spells both binary sides through nonerasing morphisms.  Such a
factorization still requires at least four new letters.
-/

namespace MatrixMortality

/-- An exact rolewise factorization of Neary's four binary word pairs through fixed macros. -/
structure ExactNearyMacroFactorization
    (β : Nat) (body : List TagLetter) (C : Type*) where
  /-- Macro word assigned to each Neary role. -/
  code : NearyTile → List C
  /-- Upper binary image of each new source letter. -/
  upper : C → List Bool
  /-- Lower binary image of each new source letter. -/
  lower : C → List Bool
  upper_nonerasing : ∀ letter, upper letter ≠ []
  lower_nonerasing : ∀ letter, lower letter ≠ []
  upper_exact : ∀ tile, spell upper (code tile) = nearyUpper β tile
  lower_exact : ∀ tile, spell lower (code tile) = nearyLower β body tile

private theorem word_length_le_spell_length {α δ : Type*} (side : α → List δ)
    (nonerasing : ∀ letter, side letter ≠ []) (word : List α) :
    word.length ≤ (spell side word).length := by
  induction word with
  | nil => simp [spell]
  | cons letter word ih =>
      have letter_length : 0 < (side letter).length :=
        List.length_pos_of_ne_nil (nonerasing letter)
      change (letter :: word).length ≤ (side letter ++ spell side word).length
      simp only [List.length_cons, List.length_append]
      omega

private theorem exists_eq_singleton_of_spell_eq_singleton {α δ : Type*}
    (side : α → List δ) (nonerasing : ∀ letter, side letter ≠ []) (word : List α)
    (symbol : δ) (exact : spell side word = [symbol]) :
    ∃ letter, word = [letter] := by
  have length_le : word.length ≤ 1 := by
    simpa [exact] using word_length_le_spell_length side nonerasing word
  have word_ne_nil : word ≠ [] := by
    intro word_nil
    simp [word_nil, spell] at exact
  have length_pos : 0 < word.length := List.length_pos_of_ne_nil word_ne_nil
  have length_eq : word.length = 1 := by omega
  exact List.length_eq_one_iff.mp length_eq

private theorem image_length_le_spell_length_of_mem {α δ : Type*}
    (side : α → List δ) {letter : α} {word : List α} (member : letter ∈ word) :
    (side letter).length ≤ (spell side word).length := by
  induction word with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      change (side letter).length ≤ (side head ++ spell side tail).length
      rw [List.length_append]
      rcases member with rfl | member
      · exact Nat.le_add_right _ _
      · exact (ih member).trans (Nat.le_add_left _ _)

private theorem eq_singleton_of_mem_of_spell_eq_image {α δ : Type*}
    (side : α → List δ) (nonerasing : ∀ letter, side letter ≠ [])
    {letter : α} {word : List α} (member : letter ∈ word)
    (exact : spell side word = side letter) :
    word = [letter] := by
  cases word with
  | nil => simp at member
  | cons head tail =>
      simp only [List.mem_cons] at member
      change side head ++ spell side tail = side letter at exact
      rcases member with rfl | member
      · have tail_spell_nil : spell side tail = [] := by
          have cancelled :
              side letter ++ spell side tail = side letter ++ [] := by
            simpa using exact
          exact List.append_cancel_left cancelled
        have tail_nil : tail = [] := by
          by_contra tail_ne_nil
          have positive : 0 < (spell side tail).length := by
            have : 0 < tail.length := List.length_pos_of_ne_nil tail_ne_nil
            exact this.trans_le (word_length_le_spell_length side nonerasing tail)
          simp [tail_spell_nil] at positive
        simp [tail_nil]
      · have head_length_pos : 0 < (side head).length :=
          List.length_pos_of_ne_nil (nonerasing head)
        have image_le : (side letter).length ≤ (spell side tail).length :=
          image_length_le_spell_length_of_mem side member
        have length_exact :
            (side head).length + (spell side tail).length = (side letter).length := by
          simpa only [List.length_append] using congrArg List.length exact
        omega

/-- Exact nonerasing role macros for the four Neary pairs require at least four letters.

The macros may have arbitrary unequal lengths, need not form a code, and may coincide a priori.
The theorem assumes only exact rolewise spelling and nonerasure on both new morphisms.
-/
theorem ExactNearyMacroFactorization.four_le_card {C : Type*} [Fintype C]
    {β : Nat} {body : List TagLetter}
    (factorization : ExactNearyMacroFactorization β body C) (β_pos : 0 < β) :
    4 ≤ Fintype.card C := by
  classical
  obtain ⟨x, code_rule_c⟩ :=
    exists_eq_singleton_of_spell_eq_singleton factorization.upper
      factorization.upper_nonerasing (factorization.code (.rule .c)) true <| by
        simpa [nearyUpper, tagCode] using factorization.upper_exact (.rule .c)
  obtain ⟨y, code_erase_c⟩ :=
    exists_eq_singleton_of_spell_eq_singleton factorization.upper
      factorization.upper_nonerasing (factorization.code (.erase .c)) true <| by
        simpa [nearyUpper, tagCode] using factorization.upper_exact (.erase .c)
  obtain ⟨z, code_erase_b⟩ :=
    exists_eq_singleton_of_spell_eq_singleton factorization.lower
      factorization.lower_nonerasing (factorization.code (.erase .b)) false <| by
        simpa [nearyLower] using factorization.lower_exact (.erase .b)

  have upper_x : factorization.upper x = [true] := by
    simpa [code_rule_c, spell, nearyUpper, tagCode] using
      factorization.upper_exact (.rule .c)
  have upper_y : factorization.upper y = [true] := by
    simpa [code_erase_c, spell, nearyUpper, tagCode] using
      factorization.upper_exact (.erase .c)
  have upper_z : factorization.upper z = tagCode β .b := by
    simpa [code_erase_b, spell, nearyUpper] using factorization.upper_exact (.erase .b)
  have lower_z : factorization.lower z = [false] := by
    simpa [code_erase_b, spell, nearyLower] using factorization.lower_exact (.erase .b)

  have x_ne_y : x ≠ y := by
    intro x_eq_y
    have rule_lower := factorization.lower_exact (.rule .c)
    have erase_lower := factorization.lower_exact (.erase .c)
    simp [code_rule_c, code_erase_c, x_eq_y, spell, nearyLower] at rule_lower erase_lower
    have impossible := rule_lower.symm.trans erase_lower
    simp at impossible
  have false_mem_upper_z : false ∈ factorization.upper z := by
    rw [upper_z]
    simp [tagCode, β_pos.ne']
  have z_ne_x : z ≠ x := by
    intro z_eq_x
    rw [z_eq_x, upper_x] at false_mem_upper_z
    simp at false_mem_upper_z
  have z_ne_y : z ≠ y := by
    intro z_eq_y
    rw [z_eq_y, upper_y] at false_mem_upper_z
    simp at false_mem_upper_z

  have false_mem_rule_b :
      false ∈ spell factorization.upper (factorization.code (.rule .b)) := by
    rw [factorization.upper_exact]
    simp [nearyUpper, tagCode, β_pos.ne']
  obtain ⟨image, image_mem, false_mem_image⟩ := List.mem_flatten.mp false_mem_rule_b
  obtain ⟨w, w_mem, image_eq⟩ := List.mem_map.mp image_mem
  subst image
  have w_ne_x : w ≠ x := by
    intro w_eq_x
    rw [w_eq_x, upper_x] at false_mem_image
    simp at false_mem_image
  have w_ne_y : w ≠ y := by
    intro w_eq_y
    rw [w_eq_y, upper_y] at false_mem_image
    simp at false_mem_image
  have w_ne_z : w ≠ z := by
    intro w_eq_z
    subst w
    have code_rule_b :
        factorization.code (.rule .b) = [z] :=
      eq_singleton_of_mem_of_spell_eq_image factorization.upper
        factorization.upper_nonerasing w_mem <| by
          rw [factorization.upper_exact, upper_z]
          rfl
    have rule_lower := factorization.lower_exact (.rule .b)
    simp [code_rule_b, spell, nearyLower, lower_z] at rule_lower

  let injection : Fin 4 → C
    | 0 => x
    | 1 => y
    | 2 => z
    | 3 => w
  have injection_injective : Function.Injective injection := by
    intro i j equal
    fin_cases i <;> fin_cases j <;>
      simp [injection, x_ne_y, x_ne_y.symm, z_ne_x, z_ne_x.symm, z_ne_y, z_ne_y.symm,
        w_ne_x, w_ne_x.symm, w_ne_y, w_ne_y.symm, w_ne_z, w_ne_z.symm] at equal ⊢
  simpa using Fintype.card_le_of_injective injection injection_injective

end MatrixMortality
