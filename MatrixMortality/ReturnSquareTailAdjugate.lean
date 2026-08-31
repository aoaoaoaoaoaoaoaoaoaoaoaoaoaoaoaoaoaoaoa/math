import MatrixMortality.ReturnSquareGeometricResidue

/-!
# Adjugate tail certificates for ReturnSquare

The reverse fraction pullback admits an explicit adjugate action.  Separating the head wait from
a bridge word turns mortality into one homogeneous power-ray incidence after a fixed weighted
tail, without affine division or an unbounded head search.
-/

namespace MatrixMortality.ReturnSquare

open scoped Matrix

/-- Explicit adjugate of the fraction pullback. -/
def fractionPullbackAdjugate {R : Type*} [CommRing R] (A B t : R) :
    Square (Fin 2) R :=
  !![B * t, -(A * B);
     t, (B - A) * t ^ 2 - B]

/-- Alternating form detecting equality of two projective rays. -/
def fractionRayCross {R : Type*} [CommRing R]
    (left right : Fin 2 → R) : R :=
  left 0 * right 1 - left 1 * right 0

/-- The terminal-ray incidence is one alternating-form zero. -/
theorem fractionRayCross_terminal_eq_zero_iff
    {R : Type*} [CommRing R] (B : R) (state : Fin 2 → R) :
    fractionRayCross state ![B, 1] = 0 ↔ state 0 = B * state 1 := by
  simp [fractionRayCross]
  constructor <;> intro equality
  · linear_combination equality
  · linear_combination equality

/-- A geometric source ray is one alternating-form zero. -/
theorem fractionRayCross_source_eq_zero_iff
    {R : Type*} [CommRing R] (source : R) (state : Fin 2 → R) :
    fractionRayCross ![source, 1] state = 0 ↔
      state 0 = source * state 1 := by
  simp [fractionRayCross]
  constructor <;> intro equality
  · linear_combination -equality
  · linear_combination -equality

/-- One pullback moves across the alternating form by its explicit adjugate. -/
theorem fractionRayCross_pullback_mulVec
    {R : Type*} [CommRing R] (A B t : R) (left right : Fin 2 → R) :
    fractionRayCross (fractionPullback A B t *ᵥ left) right =
      fractionRayCross left (fractionPullbackAdjugate A B t *ᵥ right) := by
  simp [fractionRayCross, fractionPullback, fractionPullbackAdjugate,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- A reversed pullback word moves across the alternating form as the forward adjugate word. -/
theorem fractionRayCross_pullbackWord
    {R : Type*} [CommRing R] (A B : R) (scales : List R)
    (left right : Fin 2 → R) :
    fractionRayCross
        (wordProduct (fractionPullback A B) scales.reverse *ᵥ left) right =
      fractionRayCross left
        (wordProduct (fractionPullbackAdjugate A B) scales *ᵥ right) := by
  induction scales generalizing left right with
  | nil => simp [fractionRayCross]
  | cons scale scales induction =>
      rw [List.reverse_cons, wordProduct_append, wordProduct_cons,
        wordProduct_nil, Matrix.mul_one, ← Matrix.mulVec_mulVec]
      calc
        fractionRayCross
            (wordProduct (fractionPullback A B) scales.reverse *ᵥ
              (fractionPullback A B scale *ᵥ left)) right =
          fractionRayCross (fractionPullback A B scale *ᵥ left)
            (wordProduct (fractionPullbackAdjugate A B) scales *ᵥ right) :=
          induction _ _
        _ = fractionRayCross left
            (fractionPullbackAdjugate A B scale *ᵥ
              (wordProduct (fractionPullbackAdjugate A B) scales *ᵥ right)) :=
          fractionRayCross_pullback_mulVec A B scale left _
        _ = fractionRayCross left
            (wordProduct (fractionPullbackAdjugate A B) (scale :: scales) *ᵥ
              right) := by
          rw [wordProduct_cons, ← Matrix.mulVec_mulVec]

/-- Homogeneous predecessor of the terminal ray through a positive-wait tail. -/
def fractionTailPredecessorState
    (q A B : ℚ) (tail : List Nat) : Fin 2 → ℚ :=
  wordProduct
      (fun wait => fractionPullbackAdjugate A B (q ^ (wait + 1))) tail *ᵥ
    ![B, 1]

/-- Pulling the reset ray through a separated head exposes `Aq^(head+1)` before the tail. -/
theorem fractionWaitState_cons
    (q A B : ℚ) (head : Nat) (tail : List Nat) :
    fractionWaitState q A B (head :: tail) =
      ((B - A) * q ^ (head + 1)) •
        (wordProduct
          (fun wait => fractionPullback A B (q ^ (wait + 1))) tail.reverse *ᵥ
            ![A * q ^ (head + 1), 1]) := by
  rw [fractionWaitState, List.reverse_cons, wordProduct_append,
    wordProduct_cons, wordProduct_nil, Matrix.mul_one, ← Matrix.mulVec_mulVec,
    fractionPullback_mulVec_reset, Matrix.mulVec_smul]

/-- Exact head-separated bridge certificate.  Once the tail is fixed, the unbounded head wait
appears only as membership in the geometric ray `Aqⁿ`. -/
theorem positiveBridge_fraction_cons_zero_iff_tailAdjugate
    (q A B : ℚ) (head : Nat) (tail : List Nat)
    (B_ne : B ≠ 0) (B_sub_A_ne : B - A ≠ 0) (q_ne : q ≠ 0) :
    positiveBridge q (-(A / B)) (head :: tail) = 0 ↔
      fractionTailPredecessorState q A B tail 0 =
        A * q ^ (head + 1) * fractionTailPredecessorState q A B tail 1 := by
  rw [positiveBridge_fraction_zero_iff q A B B_ne]
  have scale_ne : q ^ (head + 1) ≠ 0 := pow_ne_zero _ q_ne
  have reset_weight_ne : (B - A) * q ^ (head + 1) ≠ 0 :=
    mul_ne_zero B_sub_A_ne scale_ne
  rw [fractionWaitState_cons]
  change
    ((B - A) * q ^ (head + 1)) *
          (wordProduct
              (fun wait => fractionPullback A B (q ^ (wait + 1))) tail.reverse *ᵥ
            ![A * q ^ (head + 1), 1]) 0 =
        B * (((B - A) * q ^ (head + 1)) *
          (wordProduct
              (fun wait => fractionPullback A B (q ^ (wait + 1))) tail.reverse *ᵥ
            ![A * q ^ (head + 1), 1]) 1) ↔ _
  have cancel_reset
      (left right : ℚ) :
      ((B - A) * q ^ (head + 1)) * left =
          B * (((B - A) * q ^ (head + 1)) * right) ↔
        left = B * right := by
    constructor
    · intro scaled
      apply mul_left_cancel₀ reset_weight_ne
      calc
        ((B - A) * q ^ (head + 1)) * left =
            B * (((B - A) * q ^ (head + 1)) * right) := scaled
        _ = ((B - A) * q ^ (head + 1)) * (B * right) := by ring
    · intro unscaled
      rw [unscaled]
      ring
  rw [cancel_reset]
  have cross_identity :=
    fractionRayCross_pullbackWord A B
      (tail.map fun wait => q ^ (wait + 1))
      ![A * q ^ (head + 1), 1] ![B, 1]
  rw [← List.map_reverse, ← wordProduct_comp, ← wordProduct_comp] at cross_identity
  change
    fractionRayCross
        (wordProduct
            (fun wait => fractionPullback A B (q ^ (wait + 1))) tail.reverse *ᵥ
          ![A * q ^ (head + 1), 1]) ![B, 1] =
      fractionRayCross ![A * q ^ (head + 1), 1]
        (fractionTailPredecessorState q A B tail) at cross_identity
  rw [← fractionRayCross_terminal_eq_zero_iff,
    ← fractionRayCross_source_eq_zero_iff, cross_identity]

/-- A positive base-prime valuation fixes the complete tail weight.  Mortality in this stratum
therefore reduces to finitely many weighted tails, followed by one geometric-ray membership
test for the separated head. -/
theorem positiveBridge_fraction_zero_positive_valuation_tail_certificate
    (q : ℤ) (q_ne : q ≠ 0) (prime : Nat) (prime_spec : prime.Prime)
    (prime_dvd : (prime : ℤ) ∣ q)
    (A B : ℚ) (B_ne : B ≠ 0) (B_sub_A_ne : B - A ≠ 0)
    (fraction_ne_one : A / B ≠ 1)
    (head weight : Nat) (tail : List Nat)
    (bridge_zero :
      positiveBridge (q : ℚ) (-(A / B)) (head :: tail) = 0)
    (valuation_positive : 0 < padicValRat prime (A / B))
    (base_valuation_positive : 0 < (padicValInt prime q : ℤ))
    (valuation_shape :
      padicValRat prime (A / B) =
        (weight : ℤ) * (padicValInt prime q : ℤ)) :
    tail ≠ [] ∧ waitExponent tail = weight ∧
      fractionTailPredecessorState (q : ℚ) A B tail 0 =
        A * (q : ℚ) ^ (head + 1) *
          fractionTailPredecessorState (q : ℚ) A B tail 1 := by
  obtain ⟨tail_ne, tail_valuation⟩ :=
    positiveBridge_zero_positive_valuation_eq_tail
      q q_ne prime prime_spec prime_dvd (A / B) fraction_ne_one head tail
        bridge_zero valuation_positive
  have weight_eq_int : (waitExponent tail : ℤ) = weight := by
    nlinarith [tail_valuation, valuation_shape, base_valuation_positive]
  have weight_eq : waitExponent tail = weight := by
    exact_mod_cast weight_eq_int
  have q_ne_rat : (q : ℚ) ≠ 0 := by exact_mod_cast q_ne
  have incidence :=
    (positiveBridge_fraction_cons_zero_iff_tailAdjugate
      (q : ℚ) A B head tail B_ne B_sub_A_ne q_ne_rat).mp bridge_zero
  exact ⟨tail_ne, weight_eq, incidence⟩

end MatrixMortality.ReturnSquare
