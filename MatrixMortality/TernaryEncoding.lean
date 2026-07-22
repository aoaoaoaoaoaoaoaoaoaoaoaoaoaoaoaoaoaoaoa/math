import Mathlib

/-!
# The nonzero ternary word encoding

This file verifies the base-3 coding facts used by the PCP matrix morphism.  Binary letters are
encoded as the nonzero ternary digits `1` and `2`, so no leading-zero ambiguity is possible.
-/

namespace MatrixMortality

/-- Encode binary digits as the nonzero ternary digits `1` and `2`. -/
def ternaryDigit : Bool → ℕ
  | false => 1
  | true => 2

@[simp] theorem ternaryDigit_lt_three (b : Bool) : ternaryDigit b < 3 := by
  cases b <;> decide

@[simp] theorem ternaryDigit_ne_zero (b : Bool) : ternaryDigit b ≠ 0 := by
  cases b <;> decide

theorem ternaryDigit_injective : Function.Injective ternaryDigit := by
  intro a b h
  cases a <;> cases b <;> simp_all [ternaryDigit]

/-- The usual left-to-right base-3 value of a binary word after replacing its letters by `1,2`. -/
def ternaryCode (word : List Bool) : ℕ :=
  Nat.ofDigits 3 (word.reverse.map ternaryDigit)

@[simp] theorem ternaryCode_nil : ternaryCode [] = 0 := by
  simp [ternaryCode]

theorem ternaryCode_append (x y : List Bool) :
    ternaryCode (x ++ y) = 3 ^ y.length * ternaryCode x + ternaryCode y := by
  simp [ternaryCode, List.reverse_append, Nat.ofDigits_append, add_comm, mul_comm]

theorem digits_ternaryCode (word : List Bool) :
    Nat.digits 3 (ternaryCode word) = word.reverse.map ternaryDigit := by
  apply Nat.digits_ofDigits 3 (by decide)
  · intro digit hdigit
    rcases List.mem_map.mp hdigit with ⟨b, _, rfl⟩
    exact ternaryDigit_lt_three b
  · intro hne
    have hmem := List.getLast_mem hne
    rcases List.mem_map.mp hmem with ⟨b, _, hb⟩
    rw [← hb]
    exact ternaryDigit_ne_zero b

theorem ternaryCode_injective : Function.Injective ternaryCode := by
  intro x y hcode
  have hdigits := congrArg (Nat.digits 3) hcode
  rw [digits_ternaryCode, digits_ternaryCode] at hdigits
  have hreverse : x.reverse = y.reverse :=
    (List.map_injective_iff.mpr ternaryDigit_injective) hdigits
  exact List.reverse_injective hreverse

end MatrixMortality
