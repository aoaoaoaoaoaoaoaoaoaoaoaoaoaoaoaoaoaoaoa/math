import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.CoprodI
import MatrixMortality.ProjectiveLine

/-!
# A free rational orbit invisible to every congruence quotient

The upper and lower shears of step three generate a free subgroup of `GL₂(ℚ)`, and the rational
projective point one has trivial stabilizer.  The point `10 / 13` lies outside its orbit, but its
reduction lies in the orbit modulo every positive integer.  Thus no congruence quotient separates
this rational no-instance.
-/

namespace MatrixMortality.CongruenceBlindOrbit

open scoped Matrix Pointwise

/-- Two-by-two square matrices. -/
abbrev Square₂ (R : Type*) := Matrix (Fin 2) (Fin 2) R

/-! ## Shear algebra -/

/-- Upper unipotent shear. -/
def upperShear {R : Type*} [Zero R] [One R] (shift : R) : Square₂ R :=
  !![1, shift; 0, 1]

/-- Lower unipotent shear. -/
def lowerShear {R : Type*} [Zero R] [One R] (shift : R) : Square₂ R :=
  !![1, 0; shift, 1]

/-- The homogeneous source ray `[1:1]`. -/
def sourceRay (R : Type*) [One R] : Fin 2 → R := ![1, 1]

/-- The homogeneous target ray `[10:13]`. -/
def targetRay (R : Type*) [OfNat R 10] [OfNat R 13] : Fin 2 → R := ![10, 13]

/-- A homogeneous pair whose coordinates generate the unit ideal. -/
def IsUnimodularRay {R : Type*} [CommRing R] (ray : Fin 2 → R) : Prop :=
  ∃ first second : R, first * ray 0 + second * ray 1 = 1

/-- The integral target pair `[10:13]` remains unimodular over every commutative ring. -/
theorem targetRay_isUnimodular (R : Type*) [CommRing R] :
    IsUnimodularRay (targetRay R) := by
  refine ⟨4, -3, ?_⟩
  norm_num [IsUnimodularRay, targetRay]

@[simp]
theorem upperShear_mul (R : Type*) [CommRing R] (left right : R) :
    upperShear left * upperShear right = upperShear (left + right) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperShear, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

@[simp]
theorem lowerShear_mul (R : Type*) [CommRing R] (left right : R) :
    lowerShear left * lowerShear right = lowerShear (left + right) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerShear, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Five shear blocks comprising the congruence witness.  When `x = 3rd`, these blocks are the
integer powers `B^(rd) A^(3rd) B^(2rd) A^(-3rdn) A^n`. -/
def bridgeMatrix {R : Type*} [CommRing R] (x n : R) : Square₂ R :=
  lowerShear x * upperShear (3 * x) * lowerShear (2 * x) *
    upperShear (-3 * x * n) * upperShear (3 * n)

/-- If the simulated inverse makes `x = 1`, the five-block bridge sends `[1:1]` exactly to
`[10:13]`. -/
theorem bridgeMatrix_one_mulVec_source
    {R : Type*} [CommRing R] (n : R) :
    bridgeMatrix 1 n *ᵥ sourceRay R = targetRay R := by
  ext i
  fin_cases i
  · simp [bridgeMatrix, upperShear, lowerShear, sourceRay, targetRay,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · simp [bridgeMatrix, upperShear, lowerShear, sourceRay, targetRay,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring

/-- If `x = 0`, the four correction blocks vanish and only the terminal upper shear remains. -/
theorem bridgeMatrix_zero_mulVec_source
    {R : Type*} [CommRing R] (n : R) :
    bridgeMatrix 0 n *ᵥ sourceRay R = ![1 + 3 * n, 1] := by
  ext i
  fin_cases i <;>
    simp [bridgeMatrix, upperShear, lowerShear, sourceRay,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- On an idempotent CRT selector, the bridge interpolates its exact `x=1` and `x=0`
actions. -/
theorem bridgeMatrix_idempotent_mulVec_source
    {R : Type*} [CommRing R] (x n : R) (x_idempotent : x * x = x) :
    bridgeMatrix x n *ᵥ sourceRay R =
      ![x * 10 + (1 - x) * (1 + 3 * n), x * 13 + (1 - x)] := by
  ext i
  fin_cases i
  · simp [bridgeMatrix, upperShear, lowerShear, sourceRay,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    linear_combination 6 * (1 - 3 * n * x) * x_idempotent
  · simp [bridgeMatrix, upperShear, lowerShear, sourceRay,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    linear_combination (9 - 9 * n + 6 * x - 18 * n * x ^ 2) * x_idempotent

/-- CRT-local projective data turn the interpolated bridge into one scalar copy of the target
ray. -/
theorem bridgeMatrix_idempotent_projective_target
    {R : Type*} [CommRing R] (x n unit : R)
    (x_idempotent : x * x = x)
    (unit_on_left : x * unit = x)
    (unit_on_right : (1 - x) * (13 * unit) = 1 - x)
    (source_on_right :
      (1 - x) * (1 + 3 * n) = (1 - x) * (10 * unit)) :
    bridgeMatrix x n *ᵥ sourceRay R = unit • targetRay R := by
  rw [bridgeMatrix_idempotent_mulVec_source x n x_idempotent]
  ext i
  fin_cases i
  · simp [targetRay]
    calc
      x * 10 + (1 - x) * (1 + 3 * n) =
          x * 10 + (1 - x) * (10 * unit) := by rw [source_on_right]
      _ = 10 * (x + (1 - x) * unit) := by ring
      _ = 10 * (x * unit + (1 - x) * unit) := by rw [unit_on_left]
      _ = unit * 10 := by ring
  · simp [targetRay]
    calc
      x * 13 + (1 - x) = x * 13 + (1 - x) * (13 * unit) := by
        rw [unit_on_right]
      _ = 13 * (x + (1 - x) * unit) := by ring
      _ = 13 * (x * unit + (1 - x) * unit) := by rw [unit_on_left]
      _ = unit * 13 := by ring

/-! ## End-to-end congruence closure -/

/-- The bridge over a product ring is the coordinatewise pair of the two bridges. -/
theorem bridgeMatrix_prod_mulVec_source
    {R S : Type*} [CommRing R] [CommRing S] (x₁ n₁ : R) (x₂ n₂ : S) :
    bridgeMatrix (x₁, x₂) (n₁, n₂) *ᵥ sourceRay (R × S) =
      fun index => ((bridgeMatrix x₁ n₁ *ᵥ sourceRay R) index,
        (bridgeMatrix x₂ n₂ *ᵥ sourceRay S) index) := by
  ext i <;> fin_cases i <;>
    simp [bridgeMatrix, upperShear, lowerShear, sourceRay,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Integer powers of the step-three upper and lower shears over a target ring. -/
def modularShearPower {R : Type*} [CommRing R]
    (syllable : Bool × ℤ) : Square₂ R :=
  if syllable.1 then lowerShear (3 * syllable.2) else upperShear (3 * syllable.2)

/-- The two positive step-three shear generators. -/
def modularShearGenerator {R : Type*} [CommRing R] (letter : Bool) : Square₂ R :=
  if letter then lowerShear 3 else upperShear 3

/-- Replace one signed shear power by its nonnegative residue modulo the target characteristic. -/
def positiveModularSyllable (modulus : ℕ) (syllable : Bool × ℤ) : List Bool :=
  List.replicate (syllable.2 : ZMod modulus).val syllable.1

private theorem upperShear_pow
    {R : Type*} [CommRing R] (shift : R) (exponent : ℕ) :
    upperShear shift ^ exponent = upperShear (exponent * shift) := by
  induction exponent with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp [upperShear]
  | succ exponent induction =>
      rw [pow_succ, induction, upperShear_mul]
      congr 1
      push_cast
      ring

private theorem lowerShear_pow
    {R : Type*} [CommRing R] (shift : R) (exponent : ℕ) :
    lowerShear shift ^ exponent = lowerShear (exponent * shift) := by
  induction exponent with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp [lowerShear]
  | succ exponent induction =>
      rw [pow_succ, induction, lowerShear_mul]
      congr 1
      push_cast
      ring

/-- A signed shear syllable and its positive modular expansion have the same matrix value. -/
theorem positiveModularSyllable_product
    (modulus : ℕ) [NeZero modulus] (syllable : Bool × ℤ) :
    wordProduct (modularShearGenerator (R := ZMod modulus))
        (positiveModularSyllable modulus syllable) =
      modularShearPower syllable := by
  cases syllable with
  | mk letter exponent =>
      cases letter <;>
        simp [positiveModularSyllable, modularShearGenerator, modularShearPower,
          wordProduct, List.prod_replicate, upperShear_pow, lowerShear_pow,
          mul_comm]

/-- Expanding every signed syllable gives the same modular matrix product. -/
theorem positiveModularWord_product
    (modulus : ℕ) [NeZero modulus] (word : List (Bool × ℤ)) :
    wordProduct (modularShearGenerator (R := ZMod modulus))
        (word.flatMap (positiveModularSyllable modulus)) =
      wordProduct (modularShearPower (R := ZMod modulus)) word := by
  induction word with
  | nil => rfl
  | cons syllable word induction =>
      rw [List.flatMap_cons, wordProduct_append, wordProduct_cons,
        positiveModularSyllable_product, induction]

/-- The literal five-factor bridge spelling, retained over an arbitrary target ring. -/
def modularBridgeWord (r d n : ℤ) : List (Bool × ℤ) :=
  [(true, r * d), (false, 3 * r * d), (true, 2 * r * d),
    (false, -3 * r * d * n), (false, n)]

/-- Evaluation of the modular spelling is the polynomial bridge with `x = 3rd`. -/
theorem modularBridgeWord_product
    {R : Type*} [CommRing R] (r d n : ℤ) :
    wordProduct (modularShearPower (R := R)) (modularBridgeWord r d n) =
      bridgeMatrix (3 * (r : R) * (d : R)) (n : R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modularBridgeWord, modularShearPower, bridgeMatrix, upperShear, lowerShear,
      wordProduct, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

/-- Two unimodular homogeneous vectors represent the same projective point when a unit rescales
the first to the second.  This definition remains valid over composite residue rings. -/
def SameProjectiveRay {R : Type*} [CommRing R] (left right : Fin 2 → R) : Prop :=
  IsUnimodularRay left ∧ IsUnimodularRay right ∧ ∃ scale : Rˣ, scale.1 • left = right

private theorem isUnimodularRay_of_unit_smul_eq
    {R : Type*} [CommRing R] {left right : Fin 2 → R}
    (scale : Rˣ) (scale_eq : scale.1 • left = right)
    (right_unimodular : IsUnimodularRay right) :
    IsUnimodularRay left := by
  obtain ⟨first, second, combination⟩ := right_unimodular
  refine ⟨first * scale.1, second * scale.1, ?_⟩
  have coordinate_zero := congrFun scale_eq 0
  have coordinate_one := congrFun scale_eq 1
  change scale.1 * left 0 = right 0 at coordinate_zero
  change scale.1 * left 1 = right 1 at coordinate_one
  rw [← coordinate_zero, ← coordinate_one] at combination
  simpa only [mul_assoc] using combination

/-- Ring maps commute with the bridge action on the fixed integral source ray. -/
theorem map_bridgeMatrix_mulVec_source
    {R S : Type*} [CommRing R] [CommRing S] (map : R →+* S) (x n : R) :
    (fun index => map ((bridgeMatrix x n *ᵥ sourceRay R) index)) =
      bridgeMatrix (map x) (map n) *ᵥ sourceRay S := by
  ext i
  fin_cases i <;>
    simp [bridgeMatrix, upperShear, lowerShear, sourceRay,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals simp only [map_ofNat]

private def crtScalePair (power coprimePart : ℕ)
    (thirteen_coprime : Nat.Coprime 13 power) :
    (ZMod power × ZMod coprimePart)ˣ where
  val := (ZMod.unitOfCoprime 13 thirteen_coprime, 1)
  inv := ((ZMod.unitOfCoprime 13 thirteen_coprime)⁻¹, 1)
  val_inv := by
    apply Prod.ext
    · exact congrArg Units.val (mul_inv_cancel (ZMod.unitOfCoprime 13 thirteen_coprime))
    · simp
  inv_val := by
    apply Prod.ext
    · exact congrArg Units.val (inv_mul_cancel (ZMod.unitOfCoprime 13 thirteen_coprime))
    · simp

private def crtScale (power coprimePart : ℕ)
    (moduli_coprime : Nat.Coprime power coprimePart)
    (thirteen_coprime : Nat.Coprime 13 power) :
    (ZMod (power * coprimePart))ˣ :=
  Units.map (ZMod.chineseRemainder moduli_coprime).symm.toRingHom
    (crtScalePair power coprimePart thirteen_coprime)

private theorem crtScale_image (power coprimePart : ℕ)
    (moduli_coprime : Nat.Coprime power coprimePart)
    (thirteen_coprime : Nat.Coprime 13 power) :
    ZMod.chineseRemainder moduli_coprime
        (crtScale power coprimePart moduli_coprime thirteen_coprime).1 =
      ((13 : ZMod power), (1 : ZMod coprimePart)) := by
  change ZMod.chineseRemainder moduli_coprime
      ((ZMod.chineseRemainder moduli_coprime).symm
        (crtScalePair power coprimePart thirteen_coprime).1) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

/-- CRT core: if the bridge parameter is `(0,1)` and its terminal exponent satisfies the one
remaining power-of-three equation, the bridge hits `[10:13]` projectively. -/
theorem bridgeMatrix_projectively_hits_of_crt
    (power coprimePart : ℕ)
    (moduli_coprime : Nat.Coprime power coprimePart)
    (thirteen_coprime : Nat.Coprime 13 power)
    (x n : ZMod (power * coprimePart))
    (x_image : ZMod.chineseRemainder moduli_coprime x = (0, 1))
    (n_relation : (13 : ZMod power) *
      (1 + 3 * (ZMod.chineseRemainder moduli_coprime n).1) = 10) :
    SameProjectiveRay (bridgeMatrix x n *ᵥ sourceRay _) (targetRay _) := by
  let scale := crtScale power coprimePart moduli_coprime thirteen_coprime
  have scale_eq : scale.1 • (bridgeMatrix x n *ᵥ sourceRay _) = targetRay _ := by
    ext index
    apply (ZMod.chineseRemainder moduli_coprime).injective
    have bridge_map := congrFun
      (map_bridgeMatrix_mulVec_source
        (ZMod.chineseRemainder moduli_coprime).toRingHom x n) index
    change ZMod.chineseRemainder moduli_coprime
        ((bridgeMatrix x n *ᵥ sourceRay _) index) =
      (bridgeMatrix (ZMod.chineseRemainder moduli_coprime x)
        (ZMod.chineseRemainder moduli_coprime n) *ᵥ sourceRay _) index at bridge_map
    rw [x_image] at bridge_map
    have scale_image : ZMod.chineseRemainder moduli_coprime scale.1 =
        ((13 : ZMod power), (1 : ZMod coprimePart)) := by
      simpa [scale] using
        crtScale_image power coprimePart moduli_coprime thirteen_coprime
    have pair_bridge := bridgeMatrix_prod_mulVec_source
      (0 : ZMod power) (ZMod.chineseRemainder moduli_coprime n).1
      (1 : ZMod coprimePart) (ZMod.chineseRemainder moduli_coprime n).2
    have crt_ten : ZMod.chineseRemainder moduli_coprime
        (10 : ZMod (power * coprimePart)) =
        ((10 : ZMod power), (10 : ZMod coprimePart)) := by
      rw [map_ofNat]
      rfl
    have crt_thirteen : ZMod.chineseRemainder moduli_coprime
        (13 : ZMod (power * coprimePart)) =
        ((13 : ZMod power), (13 : ZMod coprimePart)) := by
      rw [map_ofNat]
      rfl
    change ZMod.chineseRemainder moduli_coprime
        (scale.1 * (bridgeMatrix x n *ᵥ sourceRay _) index) =
      ZMod.chineseRemainder moduli_coprime (targetRay _ index)
    rw [map_mul, scale_image, bridge_map]
    rw [pair_bridge, bridgeMatrix_zero_mulVec_source, bridgeMatrix_one_mulVec_source]
    fin_cases index
    · apply Prod.ext
      · simpa [targetRay, crt_ten] using n_relation
      · simp [targetRay, crt_ten]
    · simp [targetRay, crt_thirteen]
  have target_unimodular : IsUnimodularRay (targetRay (ZMod (power * coprimePart))) :=
    targetRay_isUnimodular _
  exact ⟨isUnimodularRay_of_unit_smul_eq scale scale_eq target_unimodular,
    target_unimodular, scale, scale_eq⟩

/-- The correction radius is one below the three-adic exponent, truncated at zero. -/
def congruenceRadius (power : ℕ) : ℕ := 3 ^ (power - 1)

/-- The available shear step: `3` at three-adic depth zero and `3^k` at positive depth. -/
def congruenceStride (power : ℕ) : ℕ := 3 * congruenceRadius power

/-- An integral representative of the inverse correction modulo the prime-to-three part. -/
def congruenceInverse (power coprimePart : ℕ) : ℤ :=
  (((congruenceStride power : ZMod coprimePart)⁻¹).val : ℤ)

/-- A terminal upper-shear exponent solving the power-of-three endpoint equation. -/
def congruenceTerminalExponent (power : ℕ) : ℤ :=
  -((((13 : ZMod (3 ^ (power - 1)))⁻¹).val : ℤ))

private theorem congruenceStride_coprime (power coprimePart : ℕ)
    (three_coprime : Nat.Coprime 3 coprimePart) :
    Nat.Coprime (congruenceStride power) coprimePart := by
  exact three_coprime.mul_left (three_coprime.pow_left (power - 1))

private theorem congruenceStride_mul_inverse (power coprimePart : ℕ)
    (three_coprime : Nat.Coprime 3 coprimePart) :
    (congruenceStride power : ZMod coprimePart) * congruenceInverse power coprimePart = 1 := by
  simpa [congruenceInverse] using
    ZMod.mul_val_inv (congruenceStride_coprime power coprimePart three_coprime)

/-- The terminal exponent satisfies `13(1+3n)=10` modulo `3^k`, including the zero-depth
`ZMod 1` case. -/
theorem congruenceTerminalExponent_relation (power : ℕ) :
    (13 : ZMod (3 ^ power)) * (1 + 3 * congruenceTerminalExponent power) = 10 := by
  cases power with
  | zero =>
      change (13 : ZMod 1) * (1 + 3 * congruenceTerminalExponent 0) = 10
      exact (ZMod.subsingleton_iff.mpr rfl).allEq _ _
  | succ depth =>
      let inverse : ℕ := ((13 : ZMod (3 ^ depth))⁻¹).val
      have thirteen_coprime : Nat.Coprime 13 (3 ^ depth) :=
        (by norm_num : Nat.Coprime 13 3).pow_right depth
      have inverse_eq :
          (13 : ZMod (3 ^ depth)) * (inverse : ZMod (3 ^ depth)) = 1 := by
        simpa [inverse] using ZMod.mul_val_inv thirteen_coprime
      have inverse_cast :
          ((13 * (inverse : ℤ) : ℤ) : ZMod (3 ^ depth)) = (1 : ℤ) := by
        norm_num only [Int.cast_mul, Int.cast_ofNat, Int.cast_one, Int.cast_natCast]
        exact inverse_eq
      have inverse_mod : Int.ModEq (3 ^ depth) (13 * (inverse : ℤ)) 1 :=
        (ZMod.intCast_eq_intCast_iff _ _ _).mp inverse_cast
      have centered : Int.ModEq (3 ^ depth) (1 - 13 * (inverse : ℤ)) 0 := by
        convert Int.ModEq.rfl.sub inverse_mod using 1
        norm_num
      have lifted : Int.ModEq (3 * (3 ^ depth))
          (3 * (1 - 13 * (inverse : ℤ))) 0 := centered.mul_left' (c := 3)
      have translated : Int.ModEq (3 * (3 ^ depth))
          (3 * (1 - 13 * (inverse : ℤ)) + 10) 10 :=
        lifted.add Int.ModEq.rfl
      have desired : Int.ModEq (3 ^ depth.succ)
          (13 * (1 + 3 * (-(inverse : ℤ)))) 10 := by
        convert translated using 1 <;> simp <;> ring
      have desired_eq :
          ((13 * (1 + 3 * (-(inverse : ℤ))) : ℤ) : ZMod (3 ^ depth.succ)) =
            (10 : ℤ) :=
        (ZMod.intCast_eq_intCast_iff _ _ _).2 desired
      simpa [congruenceTerminalExponent, inverse] using desired_eq

private theorem congruenceParameter_image (power coprimePart : ℕ)
    (three_coprime : Nat.Coprime 3 coprimePart) :
    ZMod.chineseRemainder (three_coprime.pow_left power)
        (3 * (congruenceRadius power : ZMod ((3 ^ power) * coprimePart)) *
          congruenceInverse power coprimePart) =
      ((0 : ZMod (3 ^ power)), (1 : ZMod coprimePart)) := by
  rw [map_mul, map_mul, map_ofNat, map_natCast, map_intCast]
  apply Prod.ext
  · change (3 : ZMod (3 ^ power)) * congruenceRadius power *
        congruenceInverse power coprimePart = 0
    cases power with
    | zero => exact (ZMod.subsingleton_iff.mpr rfl).allEq _ _
    | succ depth =>
        simp only [congruenceRadius, Nat.add_sub_cancel]
        have stride_zero :
            (3 : ZMod (3 ^ depth.succ)) *
                ((3 ^ depth : ℕ) : ZMod (3 ^ depth.succ)) = 0 := by
          calc
            _ = ((3 : ℕ) : ZMod (3 ^ depth.succ)) *
                ((3 ^ depth : ℕ) : ZMod (3 ^ depth.succ)) := by rw [Nat.cast_ofNat]
            _ = ((3 * 3 ^ depth : ℕ) : ZMod (3 ^ depth.succ)) := by rw [Nat.cast_mul]
            _ = ((3 ^ depth.succ : ℕ) : ZMod (3 ^ depth.succ)) := by
              rw [show 3 * 3 ^ depth = 3 ^ depth.succ by simp [Nat.pow_succ, mul_comm]]
            _ = 0 := ZMod.natCast_self (3 ^ depth.succ)
        rw [stride_zero, zero_mul]
  · change (3 : ZMod coprimePart) * congruenceRadius power *
      congruenceInverse power coprimePart = 1
    simpa [congruenceStride, congruenceRadius, mul_assoc] using
      congruenceStride_mul_inverse power coprimePart three_coprime

/-- Every positive modulus admits an explicit word in the step-three shears which sends
`[1:1]` to `[10:13]` projectively over the composite residue ring. -/
theorem exists_bridgeWord_modular_hit (modulus : ℕ) (modulus_pos : 0 < modulus) :
    ∃ word : List (Bool × ℤ),
      SameProjectiveRay
        (wordProduct (modularShearPower (R := ZMod modulus)) word *ᵥ sourceRay _)
        (targetRay _) := by
  obtain ⟨power, coprimePart, three_not_dvd, modulus_eq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd modulus_pos.ne' 3 (by norm_num)
  subst modulus
  have three_coprime : Nat.Coprime 3 coprimePart :=
    Nat.prime_three.coprime_iff_not_dvd.mpr three_not_dvd
  let radius : ℤ := congruenceRadius power
  let inverse : ℤ := congruenceInverse power coprimePart
  let terminal : ℤ := congruenceTerminalExponent power
  refine ⟨modularBridgeWord radius inverse terminal, ?_⟩
  rw [modularBridgeWord_product]
  have moduli_coprime : Nat.Coprime (3 ^ power) coprimePart :=
    three_coprime.pow_left power
  have thirteen_coprime : Nat.Coprime 13 (3 ^ power) :=
    (by norm_num : Nat.Coprime 13 3).pow_right power
  have terminal_image :
      (ZMod.chineseRemainder moduli_coprime
        (terminal : ZMod ((3 ^ power) * coprimePart))).1 =
        (terminal : ZMod (3 ^ power)) := by
    rw [show (terminal : ZMod ((3 ^ power) * coprimePart)) =
        ((terminal : ℤ) : ZMod ((3 ^ power) * coprimePart)) by rfl]
    rw [map_intCast]
    rfl
  have terminal_relation :
      (13 : ZMod (3 ^ power)) *
        (1 + 3 * (ZMod.chineseRemainder moduli_coprime
          (terminal : ZMod ((3 ^ power) * coprimePart))).1) = 10 := by
    rw [terminal_image]
    exact congruenceTerminalExponent_relation power
  simpa [radius, inverse, terminal] using
    bridgeMatrix_projectively_hits_of_crt
      (3 ^ power) coprimePart moduli_coprime thirteen_coprime
      (3 * (congruenceRadius power : ZMod ((3 ^ power) * coprimePart)) *
        congruenceInverse power coprimePart)
      (congruenceTerminalExponent power)
      (congruenceParameter_image power coprimePart three_coprime)
      terminal_relation

/-- Every positive modulus admits a positive word in the two step-three shear generators which
sends `[1:1]` to `[10:13]` projectively. -/
theorem exists_positiveBridgeWord_modular_hit (modulus : ℕ) (modulus_pos : 0 < modulus) :
    ∃ word : List Bool,
      SameProjectiveRay
        (wordProduct (modularShearGenerator (R := ZMod modulus)) word *ᵥ sourceRay _)
        (targetRay _) := by
  let _ : NeZero modulus := ⟨modulus_pos.ne'⟩
  obtain ⟨signedWord, signed_hit⟩ := exists_bridgeWord_modular_hit modulus modulus_pos
  refine ⟨signedWord.flatMap (positiveModularSyllable modulus), ?_⟩
  rw [positiveModularWord_product]
  exact signed_hit

/-! ## Rational ping-pong -/

/-- The rational projective line. -/
abbrev RationalPoint := ProjectiveLine.Point ℚ

/-- Projective points outside the closed unit interval, together with infinity. -/
def UpperChamber : Set RationalPoint
  | some value => 1 < |value|
  | none => True

/-- Projective points in the open interval of radius `2/3`. -/
def LowerChamber : Set RationalPoint
  | some value => |value| < 2 / 3
  | none => False

/-- The rational source point. -/
def sourcePoint : RationalPoint := some 1

/-- The rational target point. -/
def targetPoint : RationalPoint := some (10 / 13)

/-- Integral upper shears as rational invertible matrices. -/
def upperUnit (exponent : ℤ) : Matrix.GeneralLinearGroup (Fin 2) ℚ where
  val := upperShear (3 * exponent)
  inv := upperShear (-3 * exponent)
  val_inv := by
    rw [upperShear_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperShear]
  inv_val := by
    rw [upperShear_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperShear]

/-- Integral lower shears as rational invertible matrices. -/
def lowerUnit (exponent : ℤ) : Matrix.GeneralLinearGroup (Fin 2) ℚ where
  val := lowerShear (3 * exponent)
  inv := lowerShear (-3 * exponent)
  val_inv := by
    rw [lowerShear_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerShear]
  inv_val := by
    rw [lowerShear_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerShear]

/-- Upper powers form a homomorphism from the infinite cyclic group. -/
def upperFactor : Multiplicative ℤ →* Matrix.GeneralLinearGroup (Fin 2) ℚ where
  toFun exponent := upperUnit (Multiplicative.toAdd exponent)
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperUnit, upperShear]
  map_mul' left right := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperUnit, upperShear, Matrix.mul_apply, Fin.sum_univ_succ]
    ring

/-- Lower powers form a homomorphism from the infinite cyclic group. -/
def lowerFactor : Multiplicative ℤ →* Matrix.GeneralLinearGroup (Fin 2) ℚ where
  toFun exponent := lowerUnit (Multiplicative.toAdd exponent)
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerUnit, lowerShear]
  map_mul' left right := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lowerUnit, lowerShear, Matrix.mul_apply, Fin.sum_univ_succ]
    ring

@[simp]
theorem upperFactor_apply (exponent : ℤ) :
    upperFactor (Multiplicative.ofAdd exponent) = upperUnit exponent := rfl

@[simp]
theorem lowerFactor_apply (exponent : ℤ) :
    lowerFactor (Multiplicative.ofAdd exponent) = lowerUnit exponent := rfl

/-- The two cyclic shear factors. -/
def factor : (index : Bool) → Multiplicative ℤ →*
    Matrix.GeneralLinearGroup (Fin 2) ℚ
  | false => upperFactor
  | true => lowerFactor

/-- The canonical rational projective action of invertible matrices. -/
noncomputable local instance :
    MulAction (Matrix.GeneralLinearGroup (Fin 2) ℚ) RationalPoint where
  smul matrix point := ProjectiveLine.act matrix point
  one_smul point := ProjectiveLine.act_one point
  mul_smul left right point := by
    exact ProjectiveLine.act_mul left right right.isUnit point

@[simp]
theorem upperUnit_smul_some (exponent : ℤ) (value : ℚ) :
    upperUnit exponent • (some value : RationalPoint) = some (value + 3 * exponent) := by
  change ProjectiveLine.act (upperUnit exponent).1 (some value) = _
  simp [upperUnit, upperShear, ProjectiveLine.act, ProjectiveLine.numerator,
    ProjectiveLine.denominator]

theorem lowerUnit_smul_some (exponent : ℤ) (value : ℚ)
    (denominator_ne : 3 * exponent * value + 1 ≠ 0) :
    lowerUnit exponent • (some value : RationalPoint) =
      some (value / (3 * exponent * value + 1)) := by
  change ProjectiveLine.act (lowerUnit exponent).1 (some value) = _
  simp [lowerUnit, lowerShear, ProjectiveLine.act, ProjectiveLine.numerator,
    ProjectiveLine.denominator, denominator_ne]

@[simp]
theorem lowerUnit_smul_none (exponent : ℤ) (exponent_ne : exponent ≠ 0) :
    lowerUnit exponent • (none : RationalPoint) =
      some ((1 : ℚ) / (3 * (exponent : ℚ))) := by
  have lower_left_ne : (3 : ℚ) * exponent ≠ 0 := by
    exact_mod_cast mul_ne_zero (by norm_num) exponent_ne
  change ProjectiveLine.act (lowerUnit exponent).1 none = _
  simp [lowerUnit, lowerShear, ProjectiveLine.act, lower_left_ne]

private theorem upper_maps_lower
    (exponent : ℤ) (exponent_ne : exponent ≠ 0)
    (point : RationalPoint) (point_mem : point ∈ LowerChamber) :
    upperUnit exponent • point ∈ UpperChamber := by
  cases point with
  | none => exact point_mem.elim
  | some value =>
    change |value| < 2 / 3 at point_mem
    rw [upperUnit_smul_some]
    change 1 < |value + 3 * exponent|
    have exponent_abs : (1 : ℚ) ≤ |(exponent : ℚ)| := by
      exact_mod_cast Int.one_le_abs exponent_ne
    calc
      1 < 3 * |(exponent : ℚ)| - |value| := by linarith
      _ = |3 * (exponent : ℚ)| - |value| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 3)]
      _ ≤ |value + 3 * exponent| := by
        simpa [add_comm] using
          abs_sub_abs_le_abs_sub (3 * (exponent : ℚ)) (-value)

private theorem lower_maps_upper
    (exponent : ℤ) (exponent_ne : exponent ≠ 0)
    (point : RationalPoint) (point_mem : point ∈ UpperChamber) :
    lowerUnit exponent • point ∈ LowerChamber := by
  cases point with
  | some value =>
    change 1 < |value| at point_mem
    have exponent_abs : (1 : ℚ) ≤ |(exponent : ℚ)| := by
      exact_mod_cast Int.one_le_abs exponent_ne
    have reverse_bound :
        3 * |(exponent : ℚ)| * |value| - 1 ≤
          |3 * exponent * value + 1| := by
      calc
        3 * |(exponent : ℚ)| * |value| - 1 =
            |3 * (exponent : ℚ) * value| - |(1 : ℚ)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 3), abs_one]
        _ ≤ |3 * exponent * value + 1| := by
          simpa only [abs_neg, sub_neg_eq_add] using
            abs_sub_abs_le_abs_sub (3 * exponent * value) (-1)
    have coefficient_pos : 0 < 3 * |(exponent : ℚ)| := by positivity
    have scaled_value :
        3 * |(exponent : ℚ)| <
          3 * |(exponent : ℚ)| * |value| := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left point_mem coefficient_pos
    have product_gt_three :
        3 < 3 * |(exponent : ℚ)| * |value| := by
      have coefficient_lower : (3 : ℚ) ≤ 3 * |(exponent : ℚ)| := by nlinarith
      exact coefficient_lower.trans_lt scaled_value
    have denominator_abs : 2 < |3 * exponent * value + 1| := by linarith
    have denominator_ne : 3 * (exponent : ℚ) * value + 1 ≠ 0 := by
      intro denominator_zero
      rw [denominator_zero, abs_zero] at denominator_abs
      linarith
    rw [lowerUnit_smul_some exponent value denominator_ne]
    change |value / (3 * exponent * value + 1)| < 2 / 3
    rw [abs_div]
    have denominator_pos : 0 < |3 * (exponent : ℚ) * value + 1| := by linarith
    apply (div_lt_iff₀ denominator_pos).mpr
    have value_nonneg : 0 ≤ |value| := abs_nonneg value
    have scaled_exponent :
        |value| ≤ |(exponent : ℚ)| * |value| :=
      by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right exponent_abs value_nonneg
    nlinarith [reverse_bound, scaled_exponent]
  | none =>
    rw [lowerUnit_smul_none exponent exponent_ne]
    change |1 / (3 * (exponent : ℚ))| < 2 / 3
    rw [abs_div, abs_one, abs_mul, abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 3)]
    have exponent_abs : (1 : ℚ) ≤ |(exponent : ℚ)| := by
      exact_mod_cast Int.one_le_abs exponent_ne
    have denominator_pos : 0 < 3 * |(exponent : ℚ)| := by positivity
    apply (div_lt_iff₀ denominator_pos).mpr
    norm_num
    nlinarith [exponent_abs]

private theorem factor_maps_other_chamber :
    Pairwise fun left right => ∀ power : Multiplicative ℤ, power ≠ 1 →
      factor left power • (if right then LowerChamber else UpperChamber) ⊆
        if left then LowerChamber else UpperChamber := by
  intro left right distinct power power_ne
  cases left <;> cases right
  · exact (distinct rfl).elim
  · rintro point ⟨origin, origin_mem, rfl⟩
    exact upper_maps_lower (Multiplicative.toAdd power) (by simpa using power_ne)
      origin origin_mem
  · rintro point ⟨origin, origin_mem, rfl⟩
    exact lower_maps_upper (Multiplicative.toAdd power) (by simpa using power_ne)
      origin origin_mem
  · exact (distinct rfl).elim

private theorem factor_maps_source
    (index : Bool) (power : Multiplicative ℤ) (power_ne : power ≠ 1) :
    factor index power • sourcePoint ∈ if index then LowerChamber else UpperChamber := by
  cases index
  · change upperUnit (Multiplicative.toAdd power) • sourcePoint ∈ UpperChamber
    rw [show sourcePoint = some 1 by rfl]
    rw [upperUnit_smul_some]
    change 1 < |(1 : ℚ) + 3 * Multiplicative.toAdd power|
    have exponent_ne : Multiplicative.toAdd power ≠ 0 := by simpa using power_ne
    by_cases exponent_pos : 0 < Multiplicative.toAdd power
    · have expression_pos :
          0 < (1 : ℚ) + 3 * Multiplicative.toAdd power := by
        exact_mod_cast show
          (0 : ℤ) < 1 + 3 * Multiplicative.toAdd power by omega
      rw [abs_of_pos expression_pos]
      exact_mod_cast show
        (1 : ℤ) < 1 + 3 * Multiplicative.toAdd power by omega
    · have exponent_neg : Multiplicative.toAdd power < 0 := by omega
      have expression_nonpos :
          (1 : ℚ) + 3 * Multiplicative.toAdd power ≤ 0 := by
        exact_mod_cast show
          (1 : ℤ) + 3 * Multiplicative.toAdd power ≤ 0 by omega
      rw [abs_of_nonpos expression_nonpos]
      exact_mod_cast show
        (1 : ℤ) < -(1 + 3 * Multiplicative.toAdd power) by omega
  · let exponent := Multiplicative.toAdd power
    have exponent_ne : exponent ≠ 0 := by simpa [exponent] using power_ne
    have denominator_ne : (3 : ℚ) * exponent + 1 ≠ 0 := by
      exact_mod_cast show (3 : ℤ) * exponent + 1 ≠ 0 by omega
    change lowerUnit exponent • sourcePoint ∈ LowerChamber
    rw [show sourcePoint = some 1 by rfl]
    rw [lowerUnit_smul_some exponent 1 (by simpa using denominator_ne)]
    change |1 / ((3 : ℚ) * exponent * 1 + 1)| < 2 / 3
    simp only [mul_one]
    rw [abs_div, abs_one]
    have denominator_abs_int : (2 : ℤ) ≤ |3 * exponent + 1| := by
      by_cases exponent_pos : 0 < exponent
      · rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ 3 * exponent + 1)]
        omega
      · have exponent_neg : exponent < 0 := by omega
        rw [abs_of_nonpos (by omega : (3 : ℤ) * exponent + 1 ≤ 0)]
        omega
    have denominator_abs : (2 : ℚ) ≤ |(3 : ℚ) * exponent + 1| := by
      exact_mod_cast denominator_abs_int
    have denominator_pos : 0 < |(3 : ℚ) * exponent + 1| := by linarith
    apply (div_lt_iff₀ denominator_pos).mpr
    nlinarith

/-! ## Free orbit -/

/-- The ping-pong chamber owned by one cyclic shear factor. -/
def chamber (index : Bool) : Set RationalPoint :=
  if index then LowerChamber else UpperChamber

/-- Free product of the two infinite cyclic shear factors. -/
abbrev ShearFreeProduct :=
  Monoid.CoprodI fun _ : Bool => Multiplicative ℤ

/-- Canonical representation of the two-factor free product by rational shears. -/
def shearRepresentation :
    ShearFreeProduct →* Matrix.GeneralLinearGroup (Fin 2) ℚ :=
  Monoid.CoprodI.lift factor

theorem shearRepresentation_upper (exponent : ℤ) :
    shearRepresentation
        (Monoid.CoprodI.of (i := false) (Multiplicative.ofAdd exponent)) =
      upperUnit exponent := by
  rw [shearRepresentation, Monoid.CoprodI.lift_of]
  rfl

theorem shearRepresentation_lower (exponent : ℤ) :
    shearRepresentation
        (Monoid.CoprodI.of (i := true) (Multiplicative.ofAdd exponent)) =
      lowerUnit exponent := by
  rw [shearRepresentation, Monoid.CoprodI.lift_of]
  rfl

/-- Five-factor free-product spelling of the congruence bridge. -/
def bridgeWord (exponent correction : ℤ) : ShearFreeProduct :=
  Monoid.CoprodI.of (i := true) (Multiplicative.ofAdd exponent) *
    Monoid.CoprodI.of (i := false) (Multiplicative.ofAdd (3 * exponent)) *
    Monoid.CoprodI.of (i := true) (Multiplicative.ofAdd (2 * exponent)) *
    Monoid.CoprodI.of (i := false)
      (Multiplicative.ofAdd (-3 * exponent * correction)) *
    Monoid.CoprodI.of (i := false) (Multiplicative.ofAdd correction)

/-- The abstract five-factor word is represented by the literal integral bridge matrix. -/
theorem shearRepresentation_bridgeWord (exponent correction : ℤ) :
    (shearRepresentation (bridgeWord exponent correction) : Square₂ ℚ) =
      bridgeMatrix (3 * (exponent : ℚ)) (correction : ℚ) := by
  simp only [bridgeWord, map_mul, shearRepresentation_upper,
    shearRepresentation_lower]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [upperUnit, lowerUnit, bridgeMatrix, upperShear, lowerShear,
      Matrix.mul_apply, Fin.sum_univ_succ]
    ring_nf
    simp
  · simp [upperUnit, lowerUnit, bridgeMatrix, upperShear, lowerShear,
      Matrix.mul_apply, Fin.sum_univ_succ]
    ring
  · simp [upperUnit, lowerUnit, bridgeMatrix, upperShear, lowerShear,
      Matrix.mul_apply, Fin.sum_univ_succ]
    ring_nf
    simp
  · simp [upperUnit, lowerUnit, bridgeMatrix, upperShear, lowerShear,
      Matrix.mul_apply, Fin.sum_univ_succ]
    ring

private theorem reducedWord_maps_source
    {first last : Bool}
    (word : Monoid.CoprodI.NeWord (fun _ : Bool => Multiplicative ℤ) first last) :
    shearRepresentation word.prod • sourcePoint ∈ chamber first := by
  induction word with
  | @singleton index power power_ne =>
      simpa [shearRepresentation, chamber] using
        factor_maps_source index power power_ne
  | @append first middle next last left distinct right left_induction right_induction =>
      have mapped_chamber :
          shearRepresentation left.prod • chamber next ⊆ chamber first := by
        simpa [shearRepresentation, chamber] using
          Monoid.CoprodI.lift_word_ping_pong factor chamber
            (by simpa [chamber] using factor_maps_other_chamber) left distinct
      rw [Monoid.CoprodI.NeWord.append_prod, map_mul, mul_smul]
      apply mapped_chamber
      exact ⟨shearRepresentation right.prod • sourcePoint, right_induction, rfl⟩

/-- The source and target rays both lie in the gap between the ping-pong chambers. -/
theorem source_target_outside_chambers (index : Bool) :
    sourcePoint ∉ chamber index ∧ targetPoint ∉ chamber index := by
  cases index
  · constructor
    · change ¬1 < |(1 : ℚ)|
      norm_num
    · change ¬1 < |(10 / 13 : ℚ)|
      norm_num [abs_of_nonneg]
  · constructor
    · change ¬|(1 : ℚ)| < 2 / 3
      norm_num
    · change ¬|(10 / 13 : ℚ)| < 2 / 3
      norm_num [abs_of_nonneg]

/-- Every nonidentity free-product word moves the source into the chamber of its first factor. -/
theorem nontrivial_maps_source_into_chamber
    {word : ShearFreeProduct} (word_ne : word ≠ 1) :
    ∃ index, shearRepresentation word • sourcePoint ∈ chamber index := by
  let reduced := Monoid.CoprodI.Word.equiv word
  have reduced_ne : reduced ≠ Monoid.CoprodI.Word.empty := by
    intro reduced_empty
    apply word_ne
    have restored := congrArg Monoid.CoprodI.Word.equiv.symm reduced_empty
    calc
      word = Monoid.CoprodI.Word.equiv.symm Monoid.CoprodI.Word.empty := by
        simpa [reduced] using restored
      _ = 1 := by rfl
  obtain ⟨first, last, normal, normal_eq⟩ :=
    Monoid.CoprodI.NeWord.of_word reduced reduced_ne
  have normal_prod : normal.prod = word := by
    change normal.toWord.prod = word
    rw [normal_eq]
    exact Monoid.CoprodI.Word.equiv.symm_apply_apply word
  refine ⟨first, ?_⟩
  simpa [normal_prod] using reducedWord_maps_source normal

/-- No word in the two rational shears sends `[1:1]` to `[10:13]`. -/
theorem targetPoint_not_reachable (word : ShearFreeProduct) :
    shearRepresentation word • sourcePoint ≠ targetPoint := by
  by_cases word_one : word = 1
  · subst word
    norm_num [sourcePoint, targetPoint]
  · obtain ⟨index, moved_mem⟩ := nontrivial_maps_source_into_chamber word_one
    intro target_eq
    rw [target_eq] at moved_mem
    exact (source_target_outside_chambers index).2 moved_mem

/-- The source ray has trivial stabilizer in the abstract shear free product. -/
theorem sourcePoint_stabilizer_trivial
    {word : ShearFreeProduct}
    (fixed : shearRepresentation word • sourcePoint = sourcePoint) :
    word = 1 := by
  by_contra word_ne
  obtain ⟨index, moved_mem⟩ := nontrivial_maps_source_into_chamber word_ne
  rw [fixed] at moved_mem
  exact (source_target_outside_chambers index).1 moved_mem

/-- Ping-pong makes the rational shear representation faithful. -/
theorem shearRepresentation_injective : Function.Injective shearRepresentation := by
  apply (injective_iff_map_eq_one shearRepresentation).mpr
  intro word mapped_one
  apply sourcePoint_stabilizer_trivial
  rw [mapped_one, one_smul]

end MatrixMortality.CongruenceBlindOrbit
