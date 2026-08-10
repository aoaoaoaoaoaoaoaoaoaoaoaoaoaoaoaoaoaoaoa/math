import Frankl.IntervalEntropy
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Lipschitz

namespace Frankl

open Asymptotics Filter Real Set Topology

/-- The compact expression language accepted by the reflected Frankl certificate checker. -/
inductive EntropyExpr where
  | constant (value : ℚ)
  | horizontal
  | vertical
  | add (left right : EntropyExpr)
  | neg (body : EntropyExpr)
  | mul (left right : EntropyExpr)
  | inv (body : EntropyExpr)
  | entropy (body : EntropyExpr)
  | cappedEntropy (body : EntropyExpr)
  | selfUnion (body : EntropyExpr)
deriving DecidableEq, Repr

namespace EntropyExpr

/-- Coordinate selected for a signed derivative. -/
inductive Coordinate where
  | horizontal
  | vertical
deriving DecidableEq, Repr

/-- Real semantics of the certificate expression language. -/
noncomputable def eval : EntropyExpr → ℝ → ℝ → ℝ
  | constant value, _, _ => value
  | horizontal, x, _ => x
  | vertical, _, y => y
  | add left right, x, y => left.eval x y + right.eval x y
  | neg body, x, y => -body.eval x y
  | mul left right, x, y => left.eval x y * right.eval x y
  | inv body, x, y => (body.eval x y)⁻¹
  | entropy body, x, y => binEntropy (body.eval x y)
  | cappedEntropy body, x, y => binEntropy (min (2 * body.eval x y) (1 / 2))
  | selfUnion body, x, y => Frankl.join (body.eval x y) (body.eval x y)

/-- Formal signed coordinate derivative used by the first-order box certificate. -/
noncomputable def slope (coordinate : Coordinate) : EntropyExpr → ℝ → ℝ → ℝ
  | constant _, _, _ => 0
  | horizontal, _, _ => if coordinate = .horizontal then 1 else 0
  | vertical, _, _ => if coordinate = .vertical then 1 else 0
  | add left right, x, y => left.slope coordinate x y + right.slope coordinate x y
  | neg body, x, y => -body.slope coordinate x y
  | mul left right, x, y =>
      left.slope coordinate x y * right.eval x y
        + left.eval x y * right.slope coordinate x y
  | inv body, x, y =>
      -body.slope coordinate x y * (body.eval x y * body.eval x y)⁻¹
  | entropy body, x, y =>
      (log (1 - body.eval x y) - log (body.eval x y)) * body.slope coordinate x y
  | cappedEntropy body, x, y =>
      if body.eval x y < 1 / 4 then
        (2 * (log (1 - 2 * body.eval x y) - log (2 * body.eval x y)))
          * body.slope coordinate x y
      else
        0
  | selfUnion body, x, y =>
      (2 * (1 - body.eval x y)) * body.slope coordinate x y

/-- Domain obligations for every analytic primitive in an expression. -/
def DomainAt : EntropyExpr → ℝ → ℝ → Prop
  | constant _, _, _ | horizontal, _, _ | vertical, _, _ => True
  | add left right, x, y | mul left right, x, y =>
      left.DomainAt x y ∧ right.DomainAt x y
  | neg body, x, y => body.DomainAt x y
  | inv body, x, y => body.DomainAt x y ∧ 0 < body.eval x y
  | entropy body, x, y => body.DomainAt x y ∧ body.eval x y ∈ Icc 0 1
  | cappedEntropy body, x, y => body.DomainAt x y ∧ body.eval x y ∈ Icc 0 (1 / 2)
  | selfUnion body, x, y => body.DomainAt x y ∧ body.eval x y ∈ Icc 0 1

/-- Local smoothness obligations beyond the semantic domain. The capped primitive may be
locally constant above its cap even when its discarded body is not differentiable. -/
def SmoothAt : EntropyExpr → ℝ → ℝ → Prop
  | constant _, _, _ | horizontal, _, _ | vertical, _, _ => True
  | add left right, x, y | mul left right, x, y =>
      left.SmoothAt x y ∧ right.SmoothAt x y
  | neg body, x, y | inv body, x, y => body.SmoothAt x y
  | entropy body, x, y =>
      body.SmoothAt x y ∧ body.eval x y ≠ 0 ∧ body.eval x y ≠ 1
  | cappedEntropy body, x, y =>
      body.SmoothAt x y ∧ body.eval x y ≠ 0
  | selfUnion body, x, y => body.SmoothAt x y

/-- Restriction of a bivariate expression to one coordinate line. -/
noncomputable def along (expression : EntropyExpr) (coordinate : Coordinate)
    (x y z : ℝ) : ℝ :=
  match coordinate with
  | .horizontal => expression.eval z y
  | .vertical => expression.eval x z

/-- Base point of a coordinate line. -/
def lineBase (coordinate : Coordinate) (x y : ℝ) : ℝ :=
  match coordinate with
  | .horizontal => x
  | .vertical => y

theorem hasDerivAt_cappedEntropy_at_quarter :
    HasDerivAt (fun z : ℝ => binEntropy (min (2 * z) (1 / 2))) 0 (1 / 4) := by
  let cap := fun z : ℝ => min (2 * z) (1 / 2)
  have houter : HasDerivAt binEntropy 0 (1 / 2) := by
    convert hasDerivAt_binEntropy (by norm_num : (1 / 2 : ℝ) ≠ 0)
      (by norm_num : (1 / 2 : ℝ) ≠ 1) using 1
    all_goals norm_num
  have houterLittle :
      (fun z : ℝ => binEntropy z - binEntropy (1 / 2)) =o[𝓝 (1 / 2)]
        fun z => z - 1 / 2 := by
    simpa using hasDerivAt_iff_isLittleO.mp houter
  have hcapTendsto : Tendsto cap (𝓝 (1 / 4)) (𝓝 (1 / 2)) := by
    have hdouble : ContinuousAt (fun z : ℝ => 2 * z) (1 / 4) :=
      continuousAt_const.mul continuousAt_id
    have hmin := hdouble.min (continuousAt_const :
      ContinuousAt (fun _ : ℝ => (1 : ℝ) / 2) (1 / 4))
    convert hmin using 1
    all_goals norm_num [cap]
  have hcapBig :
      (fun z : ℝ => cap z - 1 / 2) =O[𝓝 (1 / 4)]
        fun z => z - 1 / 4 := by
    apply IsBigO.of_bound 2
    filter_upwards
    intro z
    simp only [Real.norm_eq_abs, norm_eq_abs]
    by_cases hz : 2 * z ≤ (1 : ℝ) / 2
    · have hz' : 2 * z ≤ (2 : ℝ)⁻¹ := by
        norm_num at hz ⊢
        exact hz
      rw [show cap z = 2 * z by simp [cap, min_eq_left hz']]
      rw [show 2 * z - (1 : ℝ) / 2 = 2 * (z - 1 / 4) by ring, abs_mul]
      norm_num
    · have hz' : (2 : ℝ)⁻¹ ≤ 2 * z := by
        norm_num at hz ⊢
        exact hz.le
      rw [show cap z = (1 : ℝ) / 2 by simp [cap, min_eq_right hz']]
      simp
  rw [hasDerivAt_iff_isLittleO]
  have hcomposed := (houterLittle.comp_tendsto hcapTendsto).trans_isBigO hcapBig
  rw [show min (2 * (1 / 4 : ℝ)) (1 / 2) = (1 : ℝ) / 2 by norm_num]
  simpa only [Function.comp_apply, sub_zero, smul_zero] using hcomposed

theorem along_at_base (expression : EntropyExpr) (coordinate : Coordinate) (x y : ℝ) :
    expression.along coordinate x y (lineBase coordinate x y) = expression.eval x y := by
  cases coordinate <;> rfl

/-- Every expression is continuous along either coordinate throughout its semantic domain. -/
theorem continuousAt_along {expression : EntropyExpr} {coordinate : Coordinate} {x y : ℝ}
    (hdomain : expression.DomainAt x y) :
    ContinuousAt (expression.along coordinate x y) (lineBase coordinate x y) := by
  induction expression with
  | constant value =>
    cases coordinate <;> simpa [along, lineBase, eval] using continuousAt_const
  | horizontal =>
    cases coordinate
    · change ContinuousAt (fun z : ℝ => z) x
      exact continuousAt_id
    · change ContinuousAt (fun _ : ℝ => x) y
      exact continuousAt_const
  | vertical =>
    cases coordinate
    · change ContinuousAt (fun _ : ℝ => y) x
      exact continuousAt_const
    · change ContinuousAt (fun z : ℝ => z) y
      exact continuousAt_id
  | add left right hleft hright =>
    rcases hdomain with ⟨hleftDomain, hrightDomain⟩
    cases coordinate <;>
      simpa only [along, lineBase, eval] using (hleft hleftDomain).add (hright hrightDomain)
  | neg body hbody =>
    cases coordinate <;> simpa only [along, lineBase, eval] using (hbody hdomain).neg
  | mul left right hleft hright =>
    rcases hdomain with ⟨hleftDomain, hrightDomain⟩
    cases coordinate <;>
      simpa only [along, lineBase, eval] using (hleft hleftDomain).mul (hright hrightDomain)
  | inv body hbody =>
    rcases hdomain with ⟨hbodyDomain, hpositive⟩
    have hcontinuous := hbody hbodyDomain
    have hnonzero : body.along coordinate x y (lineBase coordinate x y) ≠ 0 := by
      rw [along_at_base]
      exact hpositive.ne'
    cases coordinate <;> simpa only [along, lineBase, eval] using hcontinuous.inv₀ hnonzero
  | entropy body hbody =>
    rcases hdomain with ⟨hbodyDomain, _hvalue⟩
    have hcontinuous := binEntropy_continuous.continuousAt.comp (hbody hbodyDomain)
    cases coordinate <;> simpa only [along, lineBase, eval] using hcontinuous
  | cappedEntropy body hbody =>
    rcases hdomain with ⟨hbodyDomain, _hvalue⟩
    have hbodyContinuous := hbody hbodyDomain
    have hdouble : ContinuousAt
        (fun z => 2 * body.along coordinate x y z) (lineBase coordinate x y) :=
      continuousAt_const.mul hbodyContinuous
    have hhalf : ContinuousAt (fun _ : ℝ => (1 : ℝ) / 2) (lineBase coordinate x y) :=
      continuousAt_const
    have hmin := hdouble.min hhalf
    have hcontinuous := binEntropy_continuous.continuousAt.comp hmin
    cases coordinate <;> simpa only [along, lineBase, eval] using hcontinuous
  | selfUnion body hbody =>
    rcases hdomain with ⟨hbodyDomain, _hvalue⟩
    have hcontinuous := hbody hbodyDomain
    cases coordinate <;>
      simpa only [along, lineBase, eval, Frankl.join] using
        hcontinuous.add hcontinuous |>.sub (hcontinuous.mul hcontinuous)

/-- The formal signed slope is the actual derivative on every smooth coordinate line. -/
theorem hasDerivAt_along {expression : EntropyExpr} {coordinate : Coordinate} {x y : ℝ}
    (hdomain : expression.DomainAt x y) (hsmooth : expression.SmoothAt x y) :
    HasDerivAt (expression.along coordinate x y) (expression.slope coordinate x y)
      (lineBase coordinate x y) := by
  induction expression with
  | constant value =>
    cases coordinate
    · change HasDerivAt (fun _ : ℝ => (value : ℝ)) 0 x
      exact hasDerivAt_const x (value : ℝ)
    · change HasDerivAt (fun _ : ℝ => (value : ℝ)) 0 y
      exact hasDerivAt_const y (value : ℝ)
  | horizontal =>
    cases coordinate
    · change HasDerivAt (fun z : ℝ => z) 1 x
      exact hasDerivAt_id x
    · change HasDerivAt (fun _ : ℝ => x) 0 y
      exact hasDerivAt_const y x
  | vertical =>
    cases coordinate
    · change HasDerivAt (fun _ : ℝ => y) 0 x
      exact hasDerivAt_const x y
    · change HasDerivAt (fun z : ℝ => z) 1 y
      exact hasDerivAt_id y
  | add left right hleft hright =>
    rcases hdomain with ⟨hleftDomain, hrightDomain⟩
    rcases hsmooth with ⟨hleftSmooth, hrightSmooth⟩
    cases coordinate <;> simpa only [along, lineBase, slope] using
      (hleft hleftDomain hleftSmooth).add (hright hrightDomain hrightSmooth)
  | neg body hbody =>
    cases coordinate <;> simpa only [along, lineBase, slope] using
      (hbody hdomain hsmooth).neg
  | mul left right hleft hright =>
    rcases hdomain with ⟨hleftDomain, hrightDomain⟩
    rcases hsmooth with ⟨hleftSmooth, hrightSmooth⟩
    cases coordinate <;> simpa only [along, lineBase, eval, slope] using
      (hleft hleftDomain hleftSmooth).mul (hright hrightDomain hrightSmooth)
  | inv body hbody =>
    rcases hdomain with ⟨hbodyDomain, hpositive⟩
    have hderiv := (hbody hbodyDomain hsmooth).inv (by
      rw [along_at_base]
      exact hpositive.ne')
    cases coordinate <;>
      simpa only [along, lineBase, eval, slope, div_eq_mul_inv, pow_two] using hderiv
  | entropy body hbody =>
    rcases hdomain with ⟨hbodyDomain, _hvalue⟩
    rcases hsmooth with ⟨hbodySmooth, hzero, hone⟩
    have houter : HasDerivAt binEntropy
        (log (1 - body.eval x y) - log (body.eval x y))
        (body.along coordinate x y (lineBase coordinate x y)) := by
      simpa only [along_at_base] using hasDerivAt_binEntropy hzero hone
    have hderiv := houter.comp (lineBase coordinate x y) (hbody hbodyDomain hbodySmooth)
    cases coordinate <;> simpa only [along, lineBase, eval, slope] using hderiv
  | cappedEntropy body hbody =>
    rcases hdomain with ⟨hbodyDomain, _hvalue⟩
    rcases hsmooth with ⟨hbodySmooth, hzero⟩
    have hbodyDeriv := hbody hbodyDomain hbodySmooth
    by_cases hbelow : body.eval x y < (1 : ℝ) / 4
    · have hdouble := (hasDerivAt_const (lineBase coordinate x y) (2 : ℝ)).mul hbodyDeriv
      have hdoubleZero : 2 * body.eval x y ≠ 0 := mul_ne_zero (by norm_num) hzero
      have hdoubleOne : 2 * body.eval x y ≠ 1 := by linarith
      have houter : HasDerivAt binEntropy
          (log (1 - 2 * body.eval x y) - log (2 * body.eval x y))
          (2 * body.along coordinate x y (lineBase coordinate x y)) := by
        simpa only [along_at_base] using hasDerivAt_binEntropy hdoubleZero hdoubleOne
      have hentropy := houter.comp (lineBase coordinate x y) hdouble
      have hbelowBase : body.along coordinate x y (lineBase coordinate x y) < (1 : ℝ) / 4 := by
        simpa only [along_at_base] using hbelow
      have hlocal := (continuousAt_along (coordinate := coordinate) hbodyDomain).eventually_lt
        continuousAt_const hbelowBase
      have heq :
          (EntropyExpr.cappedEntropy body).along coordinate x y =ᶠ[nhds (lineBase coordinate x y)]
            fun z => binEntropy (2 * body.along coordinate x y z) := by
        filter_upwards [hlocal] with z hz
        cases coordinate
        · change body.eval z y < (1 : ℝ) / 4 at hz
          change binEntropy (min (2 * body.eval z y) (1 / 2)) = binEntropy (2 * body.eval z y)
          rw [min_eq_left (by linarith)]
        · change body.eval x z < (1 : ℝ) / 4 at hz
          change binEntropy (min (2 * body.eval x z) (1 / 2)) = binEntropy (2 * body.eval x z)
          rw [min_eq_left (by linarith)]
      have hactual := HasDerivAt.congr_of_eventuallyEq hentropy heq
      cases coordinate <;> convert hactual using 1 <;>
        simp only [along, lineBase, eval, slope, hbelow, if_true, zero_mul, zero_add] <;>
        ring
    · by_cases hequal : body.eval x y = (1 : ℝ) / 4
      · have houter : HasDerivAt
            (fun z : ℝ => binEntropy (min (2 * z) (1 / 2))) 0
            (body.along coordinate x y (lineBase coordinate x y)) := by
          simpa only [along_at_base, hequal] using hasDerivAt_cappedEntropy_at_quarter
        have hactual := houter.comp (lineBase coordinate x y) hbodyDeriv
        cases coordinate <;>
          simpa only [Function.comp_apply, along, lineBase, eval, slope, hbelow, if_false,
            zero_mul] using hactual
      · have habove : (1 : ℝ) / 4 < body.eval x y :=
          lt_of_le_of_ne (le_of_not_gt hbelow) (Ne.symm hequal)
        have haboveBase : (1 : ℝ) / 4 <
            body.along coordinate x y (lineBase coordinate x y) := by
          simpa only [along_at_base] using habove
        have hlocal := continuousAt_const.eventually_lt
          (continuousAt_along (coordinate := coordinate) hbodyDomain) haboveBase
        have heq :
            (EntropyExpr.cappedEntropy body).along coordinate x y =ᶠ[
              nhds (lineBase coordinate x y)] fun _ => binEntropy ((1 : ℝ) / 2) := by
          filter_upwards [hlocal] with z hz
          cases coordinate
          · change (1 : ℝ) / 4 < body.eval z y at hz
            change binEntropy (min (2 * body.eval z y) (1 / 2)) = binEntropy (1 / 2)
            rw [min_eq_right (by linarith)]
          · change (1 : ℝ) / 4 < body.eval x z at hz
            change binEntropy (min (2 * body.eval x z) (1 / 2)) = binEntropy (1 / 2)
            rw [min_eq_right (by linarith)]
        have hconstant := hasDerivAt_const (lineBase coordinate x y)
          (binEntropy ((1 : ℝ) / 2))
        have hactual := HasDerivAt.congr_of_eventuallyEq hconstant heq
        cases coordinate <;>
          simpa only [along, lineBase, slope, hbelow, if_false] using hactual
  | selfUnion body hbody =>
    rcases hdomain with ⟨hbodyDomain, _hvalue⟩
    have hderiv := hbody hbodyDomain hsmooth
    have hsum := hderiv.add hderiv
    have hproduct := hderiv.mul hderiv
    cases coordinate <;>
      convert hsum.sub hproduct using 1 <;>
      simp only [along, lineBase, eval, slope, Frankl.join] <;>
      ring

/-- Subtraction in the certificate expression language. -/
def sub (left right : EntropyExpr) : EntropyExpr := .add left (.neg right)

/-- Division in the certificate expression language. -/
def div (left right : EntropyExpr) : EntropyExpr := .mul left (.inv right)

/-- The independent-OR parameter `1-(1-p)(1-q)`. -/
def join (left right : EntropyExpr) : EntropyExpr :=
  sub (.constant 1) (.mul (sub (.constant 1) left) (sub (.constant 1) right))

/-- The self-OR parameter `1-(1-p)²`, evaluated by its sharp monotone primitive. -/
def selfJoin (body : EntropyExpr) : EntropyExpr := .selfUnion body

end EntropyExpr

/-- Rational rectangle supplied to the reflected evaluator. -/
structure RatRectangle where
  /-- Enclosure of the horizontal coordinate. -/
  horizontal : RatBall
  /-- Enclosure of the vertical coordinate. -/
  vertical : RatBall
deriving DecidableEq, Repr

namespace RatRectangle

/-- Point rectangle at the midpoint of a rational rectangle. -/
def center (rectangle : RatRectangle) : RatRectangle :=
  ⟨RatBall.point rectangle.horizontal.center, RatBall.point rectangle.vertical.center⟩

end RatRectangle

/-- A value enclosure together with optional signed coordinate-derivative enclosures. -/
structure DualBall where
  /-- Enclosure of the expression value. -/
  value : RatBall
  /-- Horizontal and vertical derivative enclosures, when smoothness is certified. -/
  gradient : Option (RatBall × RatBall)
deriving DecidableEq, Repr

namespace DualBall

theorem cast_lt_quarter {x : ℚ} (hx : x < 1 / 4) :
    (x : ℝ) < (1 : ℝ) / 4 := by
  rw [← show (((1 / 4 : ℚ) : ℝ)) = (1 : ℝ) / 4 by norm_num]
  exact_mod_cast hx

theorem quarter_lt_cast {x : ℚ} (hx : 1 / 4 < x) :
    (1 : ℝ) / 4 < (x : ℝ) := by
  rw [← show (((1 / 4 : ℚ) : ℝ)) = (1 : ℝ) / 4 by norm_num]
  exact_mod_cast hx

theorem cast_le_quarter {x : ℚ} (hx : x ≤ 1 / 4) :
    (x : ℝ) ≤ (1 : ℝ) / 4 := by
  rw [← show (((1 / 4 : ℚ) : ℝ)) = (1 : ℝ) / 4 by norm_num]
  exact_mod_cast hx

theorem quarter_le_cast {x : ℚ} (hx : 1 / 4 ≤ x) :
    (1 : ℝ) / 4 ≤ (x : ℝ) := by
  rw [← show (((1 / 4 : ℚ) : ℝ)) = (1 : ℝ) / 4 by norm_num]
  exact_mod_cast hx

/-- Semantic contract of a rounded dual enclosure at one point. -/
def Encloses (dual : DualBall) (value horizontalSlope verticalSlope : ℝ) : Prop :=
  dual.value.Contains value ∧
    ∀ gradient, dual.gradient = some gradient →
      gradient.1.Contains horizontalSlope ∧ gradient.2.Contains verticalSlope

/-- Exact rational constant dual. -/
def constant (value : ℚ) : DualBall :=
  ⟨RatBall.point value, some (RatBall.point 0, RatBall.point 0)⟩

/-- Horizontal coordinate dual. -/
def horizontal (rectangle : RatRectangle) : DualBall :=
  ⟨rectangle.horizontal, some (RatBall.point 1, RatBall.point 0)⟩

/-- Vertical coordinate dual. -/
def vertical (rectangle : RatRectangle) : DualBall :=
  ⟨rectangle.vertical, some (RatBall.point 0, RatBall.point 1)⟩

/-- Rounded dual addition. -/
def add (bits : ℕ) (left right : DualBall) : DualBall :=
  let gradient := match left.gradient, right.gradient with
    | some leftGradient, some rightGradient => some
        (RatBall.roundedAdd bits leftGradient.1 rightGradient.1,
          RatBall.roundedAdd bits leftGradient.2 rightGradient.2)
    | _, _ => none
  ⟨RatBall.roundedAdd bits left.value right.value, gradient⟩

/-- Dual negation. -/
def neg (source : DualBall) : DualBall :=
  ⟨source.value.neg, source.gradient.map fun gradient => (gradient.1.neg, gradient.2.neg)⟩

/-- Rounded dual multiplication. -/
def mul (bits : ℕ) (left right : DualBall) : DualBall :=
  let gradient := match left.gradient, right.gradient with
    | some leftGradient, some rightGradient => some
        (RatBall.roundedAdd bits
          (RatBall.roundedMul bits leftGradient.1 right.value)
          (RatBall.roundedMul bits left.value rightGradient.1),
        RatBall.roundedAdd bits
          (RatBall.roundedMul bits leftGradient.2 right.value)
          (RatBall.roundedMul bits left.value rightGradient.2))
    | _, _ => none
  ⟨RatBall.roundedMul bits left.value right.value, gradient⟩

/-- Rounded positive reciprocal and its signed derivative enclosure. -/
def inv? (bits : ℕ) (source : DualBall) : Option DualBall := do
  let inverse ← RatBall.roundedInv? bits source.value
  let gradient := match source.gradient with
    | none => none
    | some sourceGradient => do
      let square := RatBall.roundedMul bits source.value source.value
      let inverseSquare ← RatBall.roundedInv? bits square
      some
        ((RatBall.roundedMul bits sourceGradient.1 inverseSquare).neg,
          (RatBall.roundedMul bits sourceGradient.2 inverseSquare).neg)
  some ⟨inverse, gradient⟩

/-- Rounded binary entropy and, away from its endpoints, exact-slope derivative enclosures. -/
def entropy? (terms fuel bits : ℕ) (source : DualBall) : Option DualBall := do
  let value ← RatBall.entropyRangeBall terms fuel bits source.value
  let gradient := if 0 < source.value.lower ∧ source.value.upper < 1 then
    match source.gradient with
    | none => none
    | some sourceGradient => do
      let complement := RatBall.roundedSub bits (RatBall.point 1) source.value
      let complementLog ← RatBall.roundedIntervalLogBall terms fuel bits complement
      let sourceLog ← RatBall.roundedIntervalLogBall terms fuel bits source.value
      let slope := RatBall.roundedSub bits complementLog sourceLog
      some
        (RatBall.roundedMul bits slope sourceGradient.1,
          RatBall.roundedMul bits slope sourceGradient.2)
  else none
  some ⟨value, gradient⟩

/-- Rounded capped entropy. Boxes touching the cap or its singular endpoint deliberately lose
their derivative enclosure and are discharged directly or subdivided. -/
def cappedEntropy? (terms fuel bits : ℕ) (source : DualBall) : Option DualBall :=
  if 1 / 4 ≤ source.value.lower then
    entropy? terms fuel bits (constant (1 / 2))
  else
    entropy? terms fuel bits (mul bits (constant 2) source)

/-- Sharp rounded dual enclosure of the self-OR map `p ↦ 2p-p²` on `[0,1]`. -/
def selfUnion (bits : ℕ) (source : DualBall) : DualBall :=
  let lower := max source.value.lower 0
  let upper := min source.value.upper 1
  let value := RatBall.ofBounds (2 * lower - lower * lower)
    (2 * upper - upper * upper) |>.round bits
  let complement := RatBall.roundedSub bits (RatBall.point 1) source.value
  let factor := RatBall.roundedMul bits (RatBall.point 2) complement
  let gradient := source.gradient.map fun sourceGradient =>
    (RatBall.roundedMul bits factor sourceGradient.1,
      RatBall.roundedMul bits factor sourceGradient.2)
  ⟨value, gradient⟩

theorem selfUnion_encloses {bits : ℕ} {source : DualBall}
    {value horizontalSlope verticalSlope : ℝ}
    (hsource : source.Encloses value horizontalSlope verticalSlope)
    (hvalue : value ∈ Icc (0 : ℝ) 1) :
    (source.selfUnion bits).Encloses (Frankl.join value value)
      ((2 * (1 - value)) * horizontalSlope)
      ((2 * (1 - value)) * verticalSlope) := by
  let lower := max source.value.lower 0
  let upper := min source.value.upper 1
  have hbounds := RatBall.contains_iff_bounds.mp hsource.1
  have hlowerValue : (lower : ℝ) ≤ value := by
    dsimp [lower]
    push_cast
    exact max_le hbounds.1 hvalue.1
  have hvalueUpper : value ≤ (upper : ℝ) := by
    dsimp [upper]
    push_cast
    exact le_min hbounds.2 hvalue.2
  have hupper₁ : (upper : ℝ) ≤ 1 := by
    exact_mod_cast min_le_right source.value.upper 1
  have hlowerJoin :
      (2 * (lower : ℝ) - lower * lower) ≤ Frankl.join value value := by
    rw [Frankl.join]
    nlinarith [mul_nonneg (sub_nonneg.2 hlowerValue)
      (by linarith : 0 ≤ 2 - (lower : ℝ) - value)]
  have hupperJoin :
      Frankl.join value value ≤ 2 * (upper : ℝ) - upper * upper := by
    rw [Frankl.join]
    nlinarith [mul_nonneg (sub_nonneg.2 hvalueUpper)
      (by linarith : 0 ≤ 2 - value - (upper : ℝ))]
  constructor
  · apply RatBall.round_contains
    apply RatBall.ofBounds_contains
    · push_cast
      simpa [lower] using hlowerJoin
    · push_cast
      simpa [upper] using hupperJoin
  · intro gradient hgradient
    unfold selfUnion at hgradient
    dsimp only at hgradient
    cases hsourceGradient : source.gradient with
    | none => simp [hsourceGradient] at hgradient
    | some sourceGradient =>
      simp [hsourceGradient] at hgradient
      subst gradient
      have hslopes := hsource.2 sourceGradient hsourceGradient
      have hone : (RatBall.point 1).Contains (1 : ℝ) := by
        simpa using RatBall.point_contains 1
      have htwo : (RatBall.point 2).Contains (2 : ℝ) := by
        simpa using RatBall.point_contains 2
      have hcomplement := RatBall.roundedSub_contains (bits := bits) hone hsource.1
      have hfactor := RatBall.roundedMul_contains (bits := bits) htwo hcomplement
      exact ⟨RatBall.roundedMul_contains hfactor hslopes.1,
        RatBall.roundedMul_contains hfactor hslopes.2⟩

theorem constant_encloses (value : ℚ) :
    (constant value).Encloses value 0 0 := by
  constructor
  · exact RatBall.point_contains value
  · intro gradient hgradient
    simp only [constant, Option.some.injEq] at hgradient
    subst gradient
    constructor <;> simpa using RatBall.point_contains 0

theorem horizontal_encloses {rectangle : RatRectangle} {x : ℝ}
    (hx : rectangle.horizontal.Contains x) :
    (horizontal rectangle).Encloses x 1 0 := by
  constructor
  · exact hx
  · intro gradient hgradient
    simp only [horizontal, Option.some.injEq] at hgradient
    subst gradient
    constructor
    · simpa using RatBall.point_contains 1
    · simpa using RatBall.point_contains 0

theorem vertical_encloses {rectangle : RatRectangle} {y : ℝ}
    (hy : rectangle.vertical.Contains y) :
    (vertical rectangle).Encloses y 0 1 := by
  constructor
  · exact hy
  · intro gradient hgradient
    simp only [vertical, Option.some.injEq] at hgradient
    subst gradient
    constructor
    · simpa using RatBall.point_contains 0
    · simpa using RatBall.point_contains 1

theorem add_encloses {bits : ℕ} {left right : DualBall}
    {leftValue rightValue leftHorizontal rightHorizontal leftVertical rightVertical : ℝ}
    (hleft : left.Encloses leftValue leftHorizontal leftVertical)
    (hright : right.Encloses rightValue rightHorizontal rightVertical) :
    (add bits left right).Encloses (leftValue + rightValue)
      (leftHorizontal + rightHorizontal) (leftVertical + rightVertical) := by
  constructor
  · exact RatBall.roundedAdd_contains hleft.1 hright.1
  · intro gradient hgradient
    simp only [add] at hgradient
    cases hleftGradient : left.gradient with
    | none => simp [hleftGradient] at hgradient
    | some leftGradient =>
      cases hrightGradient : right.gradient with
      | none => simp [hleftGradient, hrightGradient] at hgradient
      | some rightGradient =>
        simp [hleftGradient, hrightGradient] at hgradient
        subst gradient
        have hleftSlopes := hleft.2 leftGradient hleftGradient
        have hrightSlopes := hright.2 rightGradient hrightGradient
        exact ⟨RatBall.roundedAdd_contains hleftSlopes.1 hrightSlopes.1,
          RatBall.roundedAdd_contains hleftSlopes.2 hrightSlopes.2⟩

theorem neg_encloses {source : DualBall} {value horizontalSlope verticalSlope : ℝ}
    (hsource : source.Encloses value horizontalSlope verticalSlope) :
    source.neg.Encloses (-value) (-horizontalSlope) (-verticalSlope) := by
  constructor
  · exact RatBall.neg_contains hsource.1
  · intro gradient hgradient
    simp only [neg] at hgradient
    cases hsourceGradient : source.gradient with
    | none => simp [hsourceGradient] at hgradient
    | some sourceGradient =>
      simp [hsourceGradient] at hgradient
      subst gradient
      have hslopes := hsource.2 sourceGradient hsourceGradient
      exact ⟨RatBall.neg_contains hslopes.1, RatBall.neg_contains hslopes.2⟩

theorem mul_encloses {bits : ℕ} {left right : DualBall}
    {leftValue rightValue leftHorizontal rightHorizontal leftVertical rightVertical : ℝ}
    (hleft : left.Encloses leftValue leftHorizontal leftVertical)
    (hright : right.Encloses rightValue rightHorizontal rightVertical) :
    (mul bits left right).Encloses (leftValue * rightValue)
      (leftHorizontal * rightValue + leftValue * rightHorizontal)
      (leftVertical * rightValue + leftValue * rightVertical) := by
  constructor
  · exact RatBall.roundedMul_contains hleft.1 hright.1
  · intro gradient hgradient
    simp only [mul] at hgradient
    cases hleftGradient : left.gradient with
    | none => simp [hleftGradient] at hgradient
    | some leftGradient =>
      cases hrightGradient : right.gradient with
      | none => simp [hleftGradient, hrightGradient] at hgradient
      | some rightGradient =>
        simp [hleftGradient, hrightGradient] at hgradient
        subst gradient
        have hleftSlopes := hleft.2 leftGradient hleftGradient
        have hrightSlopes := hright.2 rightGradient hrightGradient
        exact ⟨RatBall.roundedAdd_contains
            (RatBall.roundedMul_contains hleftSlopes.1 hright.1)
            (RatBall.roundedMul_contains hleft.1 hrightSlopes.1),
          RatBall.roundedAdd_contains
            (RatBall.roundedMul_contains hleftSlopes.2 hright.1)
            (RatBall.roundedMul_contains hleft.1 hrightSlopes.2)⟩

theorem inv_encloses {bits : ℕ} {source inverse : DualBall}
    {value horizontalSlope verticalSlope : ℝ}
    (hsource : source.Encloses value horizontalSlope verticalSlope)
    (hinverse : source.inv? bits = some inverse) :
    inverse.Encloses value⁻¹
      (-horizontalSlope * (value * value)⁻¹)
      (-verticalSlope * (value * value)⁻¹) := by
  unfold inv? at hinverse
  cases hinverseValue : RatBall.roundedInv? bits source.value with
  | none => simp [hinverseValue] at hinverse
  | some inverseValue =>
    simp only [hinverseValue] at hinverse
    have hvalue := RatBall.roundedInv_contains hsource.1 hinverseValue
    constructor
    · have hvalueEq : inverse.value = inverseValue := by
        simpa [hinverseValue] using
          congrArg (Option.map DualBall.value) hinverse.symm
      rw [hvalueEq]
      exact hvalue
    · intro gradient hgradient
      cases hsourceGradient : source.gradient with
      | none =>
        simp [hsourceGradient] at hinverse
        subst inverse
        simp [hsourceGradient] at hgradient
      | some sourceGradient =>
        simp only [hsourceGradient] at hinverse
        let square := RatBall.roundedMul bits source.value source.value
        cases hinverseSquare : RatBall.roundedInv? bits square with
        | none =>
          simp [square, hinverseSquare] at hinverse
          subst inverse
          simp [hsourceGradient, square, hinverseSquare] at hgradient
        | some inverseSquare =>
          simp [square, hinverseSquare] at hinverse
          subst inverse
          simp [hsourceGradient, square, hinverseSquare] at hgradient
          subst gradient
          have hslopes := hsource.2 sourceGradient hsourceGradient
          have hsquare := RatBall.roundedMul_contains (bits := bits) hsource.1 hsource.1
          have hinverseSquareContains := RatBall.roundedInv_contains hsquare hinverseSquare
          constructor
          · simpa only [neg_mul] using RatBall.neg_contains
              (RatBall.roundedMul_contains hslopes.1 hinverseSquareContains)
          · simpa only [neg_mul] using RatBall.neg_contains
              (RatBall.roundedMul_contains hslopes.2 hinverseSquareContains)

theorem entropy_encloses {terms fuel bits : ℕ} {source result : DualBall}
    {value horizontalSlope verticalSlope : ℝ}
    (hsource : source.Encloses value horizontalSlope verticalSlope)
    (hvalue : value ∈ Icc (0 : ℝ) 1)
    (hresult : source.entropy? terms fuel bits = some result) :
    result.Encloses (binEntropy value)
      ((log (1 - value) - log value) * horizontalSlope)
      ((log (1 - value) - log value) * verticalSlope) := by
  unfold entropy? at hresult
  cases hvalueResult : RatBall.entropyRangeBall terms fuel bits source.value with
  | none => simp [hvalueResult] at hresult
  | some valueBall =>
    have hvalueContains := RatBall.entropyRangeBall_contains hsource.1 hvalue.1 hvalue.2
      hvalueResult
    constructor
    · have hvalueEq : result.value = valueBall := by
        simpa [hvalueResult] using congrArg (Option.map DualBall.value) hresult.symm
      rw [hvalueEq]
      exact hvalueContains
    · intro gradient hgradient
      simp only [hvalueResult] at hresult
      split at hresult <;> rename_i hinterior
      · cases hsourceGradient : source.gradient with
        | none =>
          simp [hsourceGradient] at hresult
          subst result
          simp [hsourceGradient] at hgradient
        | some sourceGradient =>
          simp only [hsourceGradient] at hresult
          let complement := RatBall.roundedSub bits (RatBall.point 1) source.value
          cases hcomplementLog :
              RatBall.roundedIntervalLogBall terms fuel bits complement with
          | none =>
            simp [complement, hcomplementLog] at hresult
            subst result
            simp [hsourceGradient, complement, hcomplementLog] at hgradient
          | some complementLog =>
            cases hsourceLog :
                RatBall.roundedIntervalLogBall terms fuel bits source.value with
            | none =>
              simp [complement, hcomplementLog, hsourceLog] at hresult
              subst result
              simp [hsourceGradient, complement, hcomplementLog, hsourceLog] at hgradient
            | some sourceLog =>
              simp [complement, hcomplementLog, hsourceLog] at hresult
              subst result
              simp [hsourceGradient, complement, hcomplementLog, hsourceLog] at hgradient
              subst gradient
              have hslopes := hsource.2 sourceGradient hsourceGradient
              have hcomplement : complement.Contains (1 - value) := by
                have hone : (RatBall.point 1).Contains (1 : ℝ) := by
                  simpa using RatBall.point_contains 1
                exact RatBall.roundedSub_contains hone hsource.1
              have hcomplementLogContains :=
                RatBall.roundedIntervalLogBall_contains hcomplement hcomplementLog
              have hsourceLogContains :=
                RatBall.roundedIntervalLogBall_contains hsource.1 hsourceLog
              have hslope := RatBall.roundedSub_contains (bits := bits)
                hcomplementLogContains hsourceLogContains
              exact ⟨RatBall.roundedMul_contains hslope hslopes.1,
                RatBall.roundedMul_contains hslope hslopes.2⟩
      · simp [hinterior] at hresult
        subst result
        simp [hinterior] at hgradient

theorem entropy_encloses_half_zero {terms fuel bits : ℕ} {source result : DualBall}
    {value horizontalSlope verticalSlope : ℝ}
    (hsource : source.Encloses value horizontalSlope verticalSlope)
    (hhalf : source.value.Contains ((1 : ℝ) / 2))
    (hresult : source.entropy? terms fuel bits = some result) :
    result.Encloses (binEntropy ((1 : ℝ) / 2)) 0 0 := by
  unfold entropy? at hresult
  cases hvalueResult : RatBall.entropyRangeBall terms fuel bits source.value with
  | none => simp [hvalueResult] at hresult
  | some valueBall =>
    have hvalueContains := RatBall.entropyRangeBall_contains hhalf
      (by norm_num) (by norm_num) hvalueResult
    constructor
    · have hvalueEq : result.value = valueBall := by
        simpa [hvalueResult] using congrArg (Option.map DualBall.value) hresult.symm
      rw [hvalueEq]
      exact hvalueContains
    · intro gradient hgradient
      simp only [hvalueResult] at hresult
      split at hresult <;> rename_i hinterior
      · cases hsourceGradient : source.gradient with
        | none =>
          simp [hsourceGradient] at hresult
          subst result
          simp [hsourceGradient] at hgradient
        | some sourceGradient =>
          simp only [hsourceGradient] at hresult
          let complement := RatBall.roundedSub bits (RatBall.point 1) source.value
          cases hcomplementLog :
              RatBall.roundedIntervalLogBall terms fuel bits complement with
          | none =>
            simp [complement, hcomplementLog] at hresult
            subst result
            simp [hsourceGradient, complement, hcomplementLog] at hgradient
          | some complementLog =>
            cases hsourceLog :
                RatBall.roundedIntervalLogBall terms fuel bits source.value with
            | none =>
              simp [complement, hcomplementLog, hsourceLog] at hresult
              subst result
              simp [hsourceGradient, complement, hcomplementLog, hsourceLog] at hgradient
            | some sourceLog =>
              simp [complement, hcomplementLog, hsourceLog] at hresult
              subst result
              simp [hsourceGradient, complement, hcomplementLog, hsourceLog] at hgradient
              subst gradient
              have hslopes := hsource.2 sourceGradient hsourceGradient
              have hone : (RatBall.point 1).Contains (1 : ℝ) := by
                simpa using RatBall.point_contains 1
              have hcomplementHalf : complement.Contains ((1 : ℝ) / 2) := by
                have hcontains := RatBall.roundedSub_contains (bits := bits) hone hhalf
                norm_num at hcontains ⊢
                exact hcontains
              have hcomplementLogContains :=
                RatBall.roundedIntervalLogBall_contains hcomplementHalf hcomplementLog
              have hsourceLogContains :=
                RatBall.roundedIntervalLogBall_contains hhalf hsourceLog
              have hslope := RatBall.roundedSub_contains (bits := bits)
                hcomplementLogContains hsourceLogContains
              have hzeroSlope : (RatBall.roundedSub bits complementLog sourceLog).Contains
                  (0 : ℝ) := by
                convert hslope using 1
                ring
              exact ⟨by
                  simpa using RatBall.roundedMul_contains hzeroSlope hslopes.1,
                by
                  simpa using RatBall.roundedMul_contains hzeroSlope hslopes.2⟩
      · simp [hinterior] at hresult
        subst result
        simp [hinterior] at hgradient

theorem cappedEntropy_encloses {terms fuel bits : ℕ} {source result : DualBall}
    {value horizontalSlope verticalSlope : ℝ}
    (hsource : source.Encloses value horizontalSlope verticalSlope)
    (hvalue : value ∈ Icc (0 : ℝ) (1 / 2))
    (hresult : source.cappedEntropy? terms fuel bits = some result) :
    result.Encloses (binEntropy (min (2 * value) (1 / 2)))
      (if value < 1 / 4 then
        (2 * (log (1 - 2 * value) - log (2 * value))) * horizontalSlope
      else 0)
      (if value < 1 / 4 then
        (2 * (log (1 - 2 * value) - log (2 * value))) * verticalSlope
      else 0) := by
  unfold cappedEntropy? at hresult
  split at hresult <;> rename_i habove
  · have hbounds := RatBall.contains_iff_bounds.mp hsource.1
    have hvalueAbove : (1 : ℝ) / 4 ≤ value :=
      (quarter_le_cast habove).trans hbounds.1
    have hhalf := constant_encloses (1 / 2)
    have hhalfMem : ((1 / 2 : ℚ) : ℝ) ∈ Icc (0 : ℝ) 1 := by
      norm_num
    have hentropy := entropy_encloses hhalf hhalfMem hresult
    convert hentropy using 1 <;>
      simp only [not_lt_of_ge hvalueAbove, if_false,
        min_eq_right (by linarith : (1 : ℝ) / 2 ≤ 2 * value),
        Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, zero_mul, add_zero] <;>
      norm_num
  · have hdoubled := mul_encloses (bits := bits) (constant_encloses 2) hsource
    by_cases hvalueBelow : value < (1 : ℝ) / 4
    · have hdoubledMem : 2 * value ∈ Icc (0 : ℝ) 1 := by
        constructor <;> nlinarith [hvalue.1, hvalue.2]
      have hentropy := entropy_encloses hdoubled hdoubledMem hresult
      convert hentropy using 1 <;>
        simp only [hvalueBelow, if_true,
          min_eq_left (by linarith : 2 * value ≤ (1 : ℝ) / 2),
          neg_mul, zero_mul, zero_add] <;>
        ring
    · have hsourceQuarter : source.value.Contains ((1 : ℝ) / 4) := by
        have hbounds := RatBall.contains_iff_bounds.mp hsource.1
        rw [RatBall.contains_iff_bounds]
        constructor
        · exact cast_le_quarter (le_of_not_ge habove)
        · exact (le_of_not_gt hvalueBelow).trans hbounds.2
      have htwo : (RatBall.point 2).Contains (2 : ℝ) := by
        simpa using RatBall.point_contains 2
      have hdoubledHalf :
          (mul bits (constant 2) source).value.Contains ((1 : ℝ) / 2) := by
        have hproduct := RatBall.roundedMul_contains (bits := bits) htwo hsourceQuarter
        convert hproduct using 1
        norm_num [mul, constant]
      have hentropy := entropy_encloses_half_zero hdoubled hdoubledHalf hresult
      convert hentropy using 1 <;>
        simp only [hvalueBelow, if_false,
          min_eq_right (by linarith : (1 : ℝ) / 2 ≤ 2 * value)]

end DualBall

end Frankl
