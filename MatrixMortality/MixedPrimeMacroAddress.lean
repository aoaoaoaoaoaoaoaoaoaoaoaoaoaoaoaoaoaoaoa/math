import MatrixMortality.MixedPrimeNormalization

/-!
# A free binary address stack inside the mixed-prime affine monoid

The length-two macros `DT` and `TD` have one common multiplier but distinct offsets. Their
equal-length products encode binary addresses simultaneously from the left modulo two and from
the right modulo five. Thus these two macros generate a free fixed-length affine submonoid even
though the underlying `D,T` generators satisfy long relations.
-/

set_option autoImplicit false

namespace MatrixMortality.MixedPrimeMacroAddress

open MixedPrimeKernel

/-- The radix digit carried by one length-two macro. -/
def addressDigit : Bool → ℕ
  | false => 2
  | true => 3

/-- The two macro generators, `false ↦ DT` and `true ↦ TD`. -/
def addressMacro : Bool → List Letter
  | false => [.dilate, .translate]
  | true => [.translate, .dilate]

/-- Expand a binary macro address to a raw mixed-prime word. -/
def expandAddress : List Bool → List Letter
  | [] => []
  | bit :: tail => addressMacro bit ++ expandAddress tail

/-- Integer numerator of the mixed `2/5` radix expansion. -/
def addressCode : List Bool → ℕ
  | [] => 0
  | bit :: tail => addressDigit bit * 5 ^ tail.length + 2 * addressCode tail

/-- Rational offset of the affine action encoded by a macro address. -/
def addressOffset : List Bool → ℚ
  | [] => 0
  | bit :: tail => addressDigit bit / 3 + 2 / 5 * addressOffset tail

@[simp]
theorem addressMacro_length (bit : Bool) : (addressMacro bit).length = 2 := by
  cases bit <;> rfl

@[simp]
theorem expandAddress_length (address : List Bool) :
    (expandAddress address).length = 2 * address.length := by
  induction address with
  | nil => rfl
  | cons bit tail induction =>
      simp only [expandAddress, List.length_append, addressMacro_length,
        List.length_cons, induction]
      omega

/-- Both macros act with multiplier `2/5`; their offsets are the digits `2/3` and `3/3`. -/
theorem wordAction_addressMacro (bit : Bool) (state : ℚ) :
    wordAction (addressMacro bit) state =
      2 / 5 * state + addressDigit bit / 3 := by
  cases bit <;> norm_num [addressMacro, addressDigit, wordAction, action] <;> ring

/-- A macro address acts by its common multiplier power and its radix offset. -/
theorem wordAction_expandAddress (address : List Bool) (state : ℚ) :
    wordAction (expandAddress address) state =
      (2 / 5 : ℚ) ^ address.length * state + addressOffset address := by
  induction address with
  | nil => simp [expandAddress, wordAction, addressOffset]
  | cons bit tail induction =>
      rw [expandAddress, wordAction_append, wordAction_addressMacro, induction]
      simp only [List.length_cons, addressOffset, pow_succ']
      ring

/-- The rational offset has exact integer numerator `addressCode` over
`3·5^(length-1)`, expressed without a truncated predecessor. -/
theorem addressOffset_scaled (address : List Bool) :
    3 * 5 ^ address.length * addressOffset address = 5 * addressCode address := by
  induction address with
  | nil => norm_num [addressOffset, addressCode]
  | cons bit tail induction =>
      simp only [List.length_cons, addressOffset, addressCode, pow_succ]
      push_cast
      norm_num at induction ⊢
      linarith

/-- The leftmost macro digit is the parity of the address code. -/
theorem addressCode_cons_mod_two (bit : Bool) (tail : List Bool) :
    addressCode (bit :: tail) % 2 = addressDigit bit % 2 := by
  simp [addressCode, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]

/-- Equal codes of equal-length nonempty addresses have the same first macro. -/
theorem head_eq_of_addressCode_eq
    (leftHead rightHead : Bool) (leftTail rightTail : List Bool)
    (codes_eq : addressCode (leftHead :: leftTail) =
      addressCode (rightHead :: rightTail)) :
    leftHead = rightHead := by
  have residues_eq := congrArg (fun value : ℕ => value % 2) codes_eq
  rw [addressCode_cons_mod_two, addressCode_cons_mod_two] at residues_eq
  cases leftHead <;> cases rightHead
  <;> norm_num [addressDigit] at residues_eq
  <;> rfl

/-- Appending one macro exposes the reverse radix recurrence. -/
theorem addressCode_append (stem : List Bool) (last : Bool) :
    addressCode (stem ++ [last]) =
      5 * addressCode stem + addressDigit last * 2 ^ stem.length := by
  induction stem with
  | nil => simp [addressCode]
  | cons bit stem induction =>
      simp only [List.cons_append, List.length_cons, List.length_append,
        List.length_nil, addressCode, induction, pow_succ]
      ring

/-- The rightmost macro digit is exposed modulo five, up to the invertible power of two. -/
theorem addressCode_append_cast_zmod_five (stem : List Bool) (last : Bool) :
    (addressCode (stem ++ [last]) : ZMod 5) =
      addressDigit last * (2 : ZMod 5) ^ stem.length := by
  rw [addressCode_append]
  push_cast
  have five_eq_zero : (5 : ZMod 5) = 0 := by decide
  rw [five_eq_zero]
  simp

/-- The two macro digits remain distinct after reduction modulo five. -/
theorem addressDigit_cast_zmod_five_injective :
    Function.Injective (fun bit => (addressDigit bit : ZMod 5)) := by
  decide

/-- Equal codes with equally long prefixes have the same last macro. -/
theorem last_eq_of_addressCode_append_eq
    (leftPrefix rightPrefix : List Bool) (leftLast rightLast : Bool)
    (length_eq : leftPrefix.length = rightPrefix.length)
    (codes_eq : addressCode (leftPrefix ++ [leftLast]) =
      addressCode (rightPrefix ++ [rightLast])) :
    leftLast = rightLast := by
  have cast_eq := congrArg (fun value : ℕ => (value : ZMod 5)) codes_eq
  rw [addressCode_append_cast_zmod_five,
    addressCode_append_cast_zmod_five, length_eq] at cast_eq
  have two_unit : IsUnit (2 : ZMod 5) := by decide
  have power_unit : IsUnit ((2 : ZMod 5) ^ rightPrefix.length) :=
    two_unit.pow rightPrefix.length
  have digits_eq : (addressDigit leftLast : ZMod 5) = addressDigit rightLast := by
    exact power_unit.mul_right_cancel cast_eq
  exact addressDigit_cast_zmod_five_injective digits_eq

/-- Equal-length binary addresses have distinct integer radix codes. -/
theorem addressCode_injective_of_length_eq
    (left right : List Bool) (length_eq : left.length = right.length)
    (codes_eq : addressCode left = addressCode right) :
    left = right := by
  induction left generalizing right with
  | nil => simpa using length_eq.symm
  | cons leftHead leftTail induction =>
      cases right with
      | nil => simp at length_eq
      | cons rightHead rightTail =>
          have tails_length_eq : leftTail.length = rightTail.length := by
            exact Nat.succ.inj length_eq
          have heads_eq :=
            head_eq_of_addressCode_eq leftHead rightHead leftTail rightTail codes_eq
          subst heads_eq
          simp only [addressCode] at codes_eq
          rw [tails_length_eq] at codes_eq
          have tails_code_eq : addressCode leftTail = addressCode rightTail := by
            omega
          rw [induction rightTail tails_length_eq tails_code_eq]

/-- At fixed macro length, equality of affine actions forces equality of binary addresses. -/
theorem expandAddress_wordAction_injective_of_length_eq
    (left right : List Bool) (length_eq : left.length = right.length)
    (actions_eq : ∀ state : ℚ,
      wordAction (expandAddress left) state = wordAction (expandAddress right) state) :
    left = right := by
  have at_zero := actions_eq 0
  rw [wordAction_expandAddress, wordAction_expandAddress] at at_zero
  norm_num at at_zero
  have scaled_left := addressOffset_scaled left
  have scaled_right := addressOffset_scaled right
  rw [length_eq] at scaled_left
  rw [at_zero] at scaled_left
  have scaled_codes_eq : (5 : ℚ) * addressCode left = 5 * addressCode right :=
    scaled_left.symm.trans scaled_right
  have codes_cast_eq : (addressCode left : ℚ) = addressCode right := by
    linarith [scaled_codes_eq]
  have codes_eq : addressCode left = addressCode right := by
    exact_mod_cast codes_cast_eq
  exact addressCode_injective_of_length_eq left right length_eq codes_eq

/-- The two length-two macros generate a free affine monoid: equality of actions also recovers
the macro length from the common multiplier. -/
theorem expandAddress_wordAction_injective
    (left right : List Bool)
    (actions_eq : ∀ state : ℚ,
      wordAction (expandAddress left) state = wordAction (expandAddress right) state) :
    left = right := by
  have at_zero := actions_eq 0
  have at_one := actions_eq 1
  rw [wordAction_expandAddress, wordAction_expandAddress] at at_zero at_one
  norm_num at at_zero at_one
  have powers_eq : (2 / 5 : ℚ) ^ left.length = (2 / 5 : ℚ) ^ right.length := by
    linarith
  have length_eq : left.length = right.length := by
    exact pow_right_injective₀ (by norm_num) (by norm_num) powers_eq
  exact expandAddress_wordAction_injective_of_length_eq left right length_eq actions_eq

/-- At fixed length, selecting the offset of one constant address selects that address itself. -/
theorem eq_replicate_of_addressOffset_eq
    (address : List Bool) (bit : Bool)
    (offset_eq : addressOffset address =
      addressOffset (List.replicate address.length bit)) :
    address = List.replicate address.length bit := by
  apply expandAddress_wordAction_injective_of_length_eq
  · simp
  · intro state
    rw [wordAction_expandAddress, wordAction_expandAddress]
    simp only [List.length_replicate, offset_eq]

end MatrixMortality.MixedPrimeMacroAddress
