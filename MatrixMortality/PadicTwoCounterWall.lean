import MatrixMortality.AlternatingReaderPoison
import MatrixMortality.InterfaceCompression
import MatrixMortality.TwoPlaceReader
import MatrixMortality.TwoRegisterPlaneNoGo
import MatrixMortality.TwoVertexPlaneNoGo

/-!
# The low-dimensional two-counter wall

This file joins the three checked obstructions reached after interface compression. It does not
claim that every two-counter simulation has one of these forms: `WallEnvelope` is the exact
remaining classification hypothesis.
-/

namespace MatrixMortality

open PadicValuation
open scoped Matrix

/-- A rational Möbius reader with a specified genuine finite pole. -/
structure PoleReader where
  leading : ℚ
  offset : ℚ
  lower : ℚ
  denominator : ℚ
  pole : ℚ
  lower_ne_zero : lower ≠ 0
  pole_denominator : lower * pole + denominator = 0

namespace PoleReader

/-- The affine-chart action of a Möbius reader. -/
def action (reader : PoleReader) (state : ℚ) : ℚ :=
  (reader.leading * state + reader.offset) /
    (reader.lower * state + reader.denominator)

/-- The integral unit-determinant condition for a projective isometry at `prime`. -/
structure IsIntegralIsometryAt (reader : PoleReader) (prime : Nat) : Prop where
  leading_integral : TwoPlaceReader.PoisonIntegral prime reader.leading
  offset_integral : TwoPlaceReader.PoisonIntegral prime reader.offset
  lower_integral : TwoPlaceReader.PoisonIntegral prime reader.lower
  denominator_integral : TwoPlaceReader.PoisonIntegral prime reader.denominator
  determinant_unit : PadicValuation.IsUnit prime
    (reader.leading * reader.denominator - reader.offset * reader.lower)

/-- Every state in the negative poison chamber remains there after the read. -/
def TrapForwardAt (reader : PoleReader) (prime : Nat) : Prop :=
  ∀ state, IsNegative prime state → IsNegative prime (reader.action state)

/-- The C2 affine isometry supplies the `trap_forward` law when the lower coefficient vanishes. -/
theorem affine_trapForward
    (reader : PoleReader) (prime : Nat) [Fact prime.Prime]
    (lower_zero : reader.lower = 0)
    (leading_unit : PadicValuation.IsUnit prime reader.leading)
    (offset_integral : reader.offset = 0 ∨ 0 ≤ padicValRat prime reader.offset)
    (denominator_unit : PadicValuation.IsUnit prime reader.denominator) :
    reader.TrapForwardAt prime := by
  intro state state_negative
  have forward := AlternatingReaderPoison.integralAffine_negative_forward
    leading_unit offset_integral denominator_unit state_negative
  simpa [action, lower_zero] using forward

end PoleReader

/-- The other one of two valuation coordinates. -/
def otherCoordinate (coordinate : Fin 2) : Fin 2 :=
  ⟨1 - coordinate, by omega⟩

/-- The one-cut projective-plane envelope killed by the shared empty-return obstruction. -/
def HasMirroredOneCut (readers : Fin 2 → PoleReader) : Prop :=
  ∃ xSpectator ySpectator xScale yScale : ℚ,
    xScale ≠ 0 ∧
    (readers 0).pole = 1 ∧
    xScale • TwoRegisterPlaneNoGo.xReader
        (readers 0).leading (readers 0).offset
        (readers 0).lower (readers 0).denominator xSpectator =
      yScale • TwoRegisterPlaneNoGo.yReader
        (readers 1).leading (readers 1).offset
        (readers 1).lower (readers 1).denominator ySpectator

/-- A pole reader which is integral and unit-determinant at the poison prime. -/
def HasPoisonIntegralPole
    (poisonPrime : Nat) (readers : Fin 2 → PoleReader) : Prop :=
  ∃ coordinate,
    (readers coordinate).IsIntegralIsometryAt poisonPrime ∧
      TwoPlaceReader.PoisonIntegral poisonPrime (readers coordinate).pole

/-- The normalized two-vertex mode dichotomy. One constant mode would factor the constant
coefficient through one outer product; otherwise the four independent nonconstant modes and
two constant modes embed `Fin 6` into the ambient mode type. -/
def HasTwoVertexModeAllocation (Mode : Type*) [Fintype Mode]
    [DecidableEq Mode] : Prop :=
  (∃ center : ℚ, ∃ column row : Fin 3 → ℚ,
    TwoVertexPlaneNoGo.xReaderConstant center = Matrix.vecMulVec column row) ∨
  Nonempty (Fin 6 ↪ Mode)

/-- The three return/bridge normal forms covered by the checked obstruction reports. -/
def WallEnvelope (Mode : Type*) [Fintype Mode] [DecidableEq Mode]
    (poisonPrime : Nat) (readers : Fin 2 → PoleReader) : Prop :=
  HasMirroredOneCut readers ∨
    HasPoisonIntegralPole poisonPrime readers ∨
      HasTwoVertexModeAllocation Mode

/-- A poison-guarded pair of independent valuation readers inside the checked low-dimensional
return/bridge envelope. `Mode` is the ambient diagonal-mode index after interface compression. -/
structure PadicTwoCounterReader (Mode : Type*) [Fintype Mode] [DecidableEq Mode] where
  registerPrime : Fin 2 → Nat
  registerPrime_isPrime : ∀ coordinate, (registerPrime coordinate).Prime
  registerPrime_injective : Function.Injective registerPrime
  reader : Fin 2 → PoleReader
  read_isometry_on_other : ∀ coordinate,
    (reader coordinate).IsIntegralIsometryAt
      (registerPrime (otherCoordinate coordinate))
  pole_integral_on_other : ∀ coordinate,
    TwoPlaceReader.PoisonIntegral
      (registerPrime (otherCoordinate coordinate)) (reader coordinate).pole
  poisonPrime : Nat
  poisonPrime_isPrime : poisonPrime.Prime
  poisonPrime_ne_register : ∀ coordinate, poisonPrime ≠ registerPrime coordinate
  trap_forward : ∀ coordinate, (reader coordinate).TrapForwardAt poisonPrime
  wall_envelope : WallEnvelope Mode poisonPrime reader

namespace PadicTwoCounterReader

/-- Every reader in the checked wall envelope consumes at least six ambient modes. -/
theorem six_le_dimension
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (system : PadicTwoCounterReader Mode) :
    6 ≤ Fintype.card Mode := by
  rcases system.wall_envelope with mirrored | poison_integral | two_vertex
  · rcases mirrored with
      ⟨xSpectator, ySpectator, xScale, yScale, xScale_ne_zero, pole_eq_one, common⟩
    have pole_at_one :
        TwoRegisterPlaneNoGo.DenominatorHasPoleAtOne
          (system.reader 0).lower (system.reader 0).denominator := by
      refine ⟨(system.reader 0).lower_ne_zero, ?_⟩
      have pole_denominator := (system.reader 0).pole_denominator
      simpa [pole_eq_one] using pole_denominator
    have distinct :=
      TwoRegisterPlaneNoGo.no_common_scaled_xReader_yReader_of_xPoleAtOne
        (system.reader 0).leading (system.reader 0).offset
        (system.reader 0).lower (system.reader 0).denominator xSpectator
        (system.reader 1).leading (system.reader 1).offset
        (system.reader 1).lower (system.reader 1).denominator ySpectator
        xScale yScale xScale_ne_zero pole_at_one
    exact (distinct common).elim
  · rcases poison_integral with ⟨coordinate, isometry, pole_integral⟩
    let primeFact : Fact system.poisonPrime.Prime := ⟨system.poisonPrime_isPrime⟩
    obtain ⟨state, state_negative, escapes⟩ :=
      @TwoPlaceReader.integralFinitePole_breaks_negative
        system.poisonPrime primeFact
        (system.reader coordinate).leading (system.reader coordinate).offset
        (system.reader coordinate).lower (system.reader coordinate).denominator
        (system.reader coordinate).pole
        isometry.leading_integral isometry.offset_integral
        isometry.lower_integral isometry.denominator_integral pole_integral
        (system.reader coordinate).pole_denominator isometry.determinant_unit
    exact (escapes (system.trap_forward coordinate state state_negative)).elim
  · rcases two_vertex with one_constant_mode | six_modes
    · rcases one_constant_mode with ⟨center, column, row, constant_eq⟩
      exact
        (TwoVertexPlaneNoGo.xReaderConstant_ne_vecMulVec center column row constant_eq).elim
    · simpa using Fintype.card_le_of_injective six_modes.some six_modes.some.injective

/-- In particular, no checked-envelope two-counter reader exists in dimension at most five. -/
theorem no_reader_of_dimension_le_five
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (dimension_le : Fintype.card Mode ≤ 5) :
    ¬Nonempty (PadicTwoCounterReader Mode) := by
  rintro ⟨system⟩
  have dimension_ge := system.six_le_dimension
  omega

end PadicTwoCounterReader

end MatrixMortality
