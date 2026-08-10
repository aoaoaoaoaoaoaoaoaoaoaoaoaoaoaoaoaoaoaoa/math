import Frankl.CertificateEval

namespace Frankl

open Real Set

/-- Terminal proof mode of a reflected subdivision leaf. -/
inductive CertificateLeaf where
  | interval
  | zeroCorner
  | oneCorner
deriving DecidableEq, Repr

/-- Binary rectangle subdivision tree. -/
inductive Subdivision where
  | leaf (mode : CertificateLeaf)
  | horizontal (cut : ℚ) (lower upper : Subdivision)
  | vertical (cut : ℚ) (lower upper : Subdivision)
deriving DecidableEq, Repr

/-- Rectangle below a horizontal cut. -/
def RatRectangle.lowerHorizontal (rectangle : RatRectangle) (cut : ℚ) : RatRectangle :=
  ⟨rectangle.horizontal.lowerAt cut, rectangle.vertical⟩

/-- Rectangle above a horizontal cut. -/
def RatRectangle.upperHorizontal (rectangle : RatRectangle) (cut : ℚ) : RatRectangle :=
  ⟨rectangle.horizontal.upperAt cut, rectangle.vertical⟩

/-- Rectangle below a vertical cut. -/
def RatRectangle.lowerVertical (rectangle : RatRectangle) (cut : ℚ) : RatRectangle :=
  ⟨rectangle.horizontal, rectangle.vertical.lowerAt cut⟩

/-- Rectangle above a vertical cut. -/
def RatRectangle.upperVertical (rectangle : RatRectangle) (cut : ℚ) : RatRectangle :=
  ⟨rectangle.horizontal, rectangle.vertical.upperAt cut⟩

/-- Side length of the two analytically discharged entropy-zero corners. -/
def cornerWidth : ℚ := 1 / 1000

/-- Executable adjudication of one terminal leaf. -/
def certifyLeaf (terms fuel bits : ℕ) (mode : CertificateLeaf)
    (rectangle : RatRectangle) (expression : EntropyExpr) : Option Unit :=
  match mode with
  | .zeroCorner =>
      if 0 ≤ rectangle.horizontal.lower ∧ rectangle.horizontal.upper ≤ cornerWidth ∧
          0 ≤ rectangle.vertical.lower ∧ rectangle.vertical.upper ≤ cornerWidth then
        some ()
      else none
  | .oneCorner =>
      if 0 ≤ rectangle.horizontal.lower ∧ rectangle.horizontal.upper ≤ cornerWidth ∧
          1 - cornerWidth ≤ rectangle.vertical.lower ∧ rectangle.vertical.upper ≤ 1 then
        some ()
      else none
  | .interval => do
      let dual ← evaluateDual terms fuel bits rectangle expression
      if 0 ≤ dual.value.lower then
        some ()
      else do
        let _ ← certifySmooth terms fuel bits rectangle expression
        let gradient ← dual.gradient
        let centerDual ← evaluateDual terms fuel bits rectangle.center expression
        let lower := centerDual.value.lower
          - gradient.1.absUpper * rectangle.horizontal.radius
          - gradient.2.absUpper * rectangle.vertical.radius
        if 0 ≤ lower then some () else none

/-- Executable verification of an entire subdivision tree. -/
def certifySubdivision (terms fuel bits : ℕ) (rectangle : RatRectangle)
    (expression : EntropyExpr) : Subdivision → Option Unit
  | .leaf mode => certifyLeaf terms fuel bits mode rectangle expression
  | .horizontal cut lower upper =>
      if rectangle.horizontal.lower ≤ cut ∧ cut ≤ rectangle.horizontal.upper then do
        let _ ← certifySubdivision terms fuel bits (rectangle.lowerHorizontal cut) expression lower
        certifySubdivision terms fuel bits (rectangle.upperHorizontal cut) expression upper
      else none
  | .vertical cut lower upper =>
      if rectangle.vertical.lower ≤ cut ∧ cut ≤ rectangle.vertical.upper then do
        let _ ← certifySubdivision terms fuel bits (rectangle.lowerVertical cut) expression lower
        certifySubdivision terms fuel bits (rectangle.upperVertical cut) expression upper
      else none

theorem certifyLeaf_sound {terms fuel bits : ℕ} {mode : CertificateLeaf}
    {rectangle : RatRectangle} {expression : EntropyExpr} {x y : ℝ}
    (hhorizontalRadius : 0 ≤ rectangle.horizontal.radius)
    (hverticalRadius : 0 ≤ rectangle.vertical.radius)
    (hx : rectangle.horizontal.Contains x) (hy : rectangle.vertical.Contains y)
    (hdomain : ∀ u v, rectangle.horizontal.Contains u → rectangle.vertical.Contains v →
      expression.DomainAt u v)
    (hzeroCorner : ∀ u v : ℝ, 0 ≤ u → u ≤ cornerWidth →
      0 ≤ v → v ≤ cornerWidth → 0 ≤ expression.eval u v)
    (honeCorner : ∀ u v : ℝ, 0 ≤ u → u ≤ cornerWidth →
      1 - cornerWidth ≤ v → v ≤ 1 → 0 ≤ expression.eval u v)
    (hcertified : certifyLeaf terms fuel bits mode rectangle expression = some ()) :
    0 ≤ expression.eval x y := by
  cases mode with
  | zeroCorner =>
    simp only [certifyLeaf] at hcertified
    split at hcertified <;> rename_i hcorner
    · have hxbounds := RatBall.contains_iff_bounds.mp hx
      have hybounds := RatBall.contains_iff_bounds.mp hy
      have hhorizontalLower : (0 : ℝ) ≤ rectangle.horizontal.lower := by
        exact_mod_cast hcorner.1
      have hhorizontalUpper : (rectangle.horizontal.upper : ℝ) ≤ cornerWidth := by
        exact_mod_cast hcorner.2.1
      have hverticalLower : (0 : ℝ) ≤ rectangle.vertical.lower := by
        exact_mod_cast hcorner.2.2.1
      have hverticalUpper : (rectangle.vertical.upper : ℝ) ≤ cornerWidth := by
        exact_mod_cast hcorner.2.2.2
      exact hzeroCorner x y
        (hhorizontalLower.trans hxbounds.1)
        (hxbounds.2.trans hhorizontalUpper)
        (hverticalLower.trans hybounds.1)
        (hybounds.2.trans hverticalUpper)
    · contradiction
  | oneCorner =>
    simp only [certifyLeaf] at hcertified
    split at hcertified <;> rename_i hcorner
    · have hxbounds := RatBall.contains_iff_bounds.mp hx
      have hybounds := RatBall.contains_iff_bounds.mp hy
      have hhorizontalLower : (0 : ℝ) ≤ rectangle.horizontal.lower := by
        exact_mod_cast hcorner.1
      have hhorizontalUpper : (rectangle.horizontal.upper : ℝ) ≤ cornerWidth := by
        exact_mod_cast hcorner.2.1
      have hverticalLower : (1 : ℝ) - cornerWidth ≤ rectangle.vertical.lower := by
        exact_mod_cast hcorner.2.2.1
      have hverticalUpper : (rectangle.vertical.upper : ℝ) ≤ 1 := by
        exact_mod_cast hcorner.2.2.2
      exact honeCorner x y
        (hhorizontalLower.trans hxbounds.1)
        (hxbounds.2.trans hhorizontalUpper)
        (hverticalLower.trans hybounds.1)
        (hybounds.2.trans hverticalUpper)
    · contradiction
  | interval =>
    simp only [certifyLeaf] at hcertified
    cases hdualResult : evaluateDual terms fuel bits rectangle expression with
    | none => simp [hdualResult] at hcertified
    | some dual =>
      simp [hdualResult] at hcertified
      by_cases hdirect : 0 ≤ dual.value.lower
      · have hencloses := evaluateDual_encloses hx hy (hdomain x y hx hy) hdualResult
        have hlower := (RatBall.contains_iff_bounds.mp hencloses.1).1
        have hdirectReal : (0 : ℝ) ≤ dual.value.lower := by exact_mod_cast hdirect
        exact hdirectReal.trans hlower
      · have hnegative : dual.value.lower < 0 := lt_of_not_ge hdirect
        have hcertified := hcertified hnegative
        cases hsmoothResult : certifySmooth terms fuel bits rectangle expression with
        | none => simp [hsmoothResult] at hcertified
        | some smoothWitness =>
          cases smoothWitness
          cases hgradient : dual.gradient with
          | none => simp [hsmoothResult, hgradient] at hcertified
          | some gradient =>
            cases hcenterResult :
                evaluateDual terms fuel bits rectangle.center expression with
            | none => simp [hsmoothResult, hgradient, hcenterResult] at hcertified
            | some centerDual =>
              simp [hsmoothResult, hgradient, hcenterResult] at hcertified
              have hbound := eval_ge_center_sub_gradient_error
                hhorizontalRadius hverticalRadius hx hy hdomain hsmoothResult
                hdualResult hgradient hcenterResult
              have hlowerRational : (0 : ℚ) ≤ centerDual.value.lower
                  - gradient.1.absUpper * rectangle.horizontal.radius
                  - gradient.2.absUpper * rectangle.vertical.radius := by
                linarith
              have hlowerReal : (0 : ℝ) ≤ centerDual.value.lower
                  - gradient.1.absUpper * rectangle.horizontal.radius
                  - gradient.2.absUpper * rectangle.vertical.radius := by
                exact_mod_cast hlowerRational
              exact hlowerReal.trans hbound

theorem certifySubdivision_sound {terms fuel bits : ℕ} {rectangle : RatRectangle}
    {expression : EntropyExpr} {tree : Subdivision} {x y : ℝ}
    (hhorizontalRadius : 0 ≤ rectangle.horizontal.radius)
    (hverticalRadius : 0 ≤ rectangle.vertical.radius)
    (hx : rectangle.horizontal.Contains x) (hy : rectangle.vertical.Contains y)
    (hdomain : ∀ u v, rectangle.horizontal.Contains u → rectangle.vertical.Contains v →
      expression.DomainAt u v)
    (hzeroCorner : ∀ u v : ℝ, 0 ≤ u → u ≤ cornerWidth →
      0 ≤ v → v ≤ cornerWidth → 0 ≤ expression.eval u v)
    (honeCorner : ∀ u v : ℝ, 0 ≤ u → u ≤ cornerWidth →
      1 - cornerWidth ≤ v → v ≤ 1 → 0 ≤ expression.eval u v)
    (hcertified : certifySubdivision terms fuel bits rectangle expression tree = some ()) :
    0 ≤ expression.eval x y := by
  revert rectangle x y
  induction tree with
  | leaf mode =>
    intro rectangle x y hhorizontalRadius hverticalRadius hx hy hdomain hcertified
    exact certifyLeaf_sound hhorizontalRadius hverticalRadius hx hy hdomain
      hzeroCorner honeCorner hcertified
  | horizontal cut lower upper hlower hupper =>
    intro rectangle x y _hhorizontalRadius hverticalRadius hx hy hdomain hcertified
    unfold certifySubdivision at hcertified
    split at hcertified <;> rename_i hcut
    · cases hlowerCertified : certifySubdivision terms fuel bits
          (rectangle.lowerHorizontal cut) expression lower with
      | none => simp [hlowerCertified] at hcertified
      | some lowerWitness =>
        cases lowerWitness
        simp [hlowerCertified] at hcertified
        by_cases hxCut : x ≤ (cut : ℝ)
        · have hxLower := RatBall.lowerAt_contains hx hxCut
          have hlowerDomain : ∀ u v,
              (rectangle.lowerHorizontal cut).horizontal.Contains u →
              (rectangle.lowerHorizontal cut).vertical.Contains v →
              expression.DomainAt u v := by
            intro u v hu hv
            exact hdomain u v (RatBall.lowerAt_contains_parent hu hcut.2) hv
          exact hlower (rectangle := rectangle.lowerHorizontal cut) (x := x) (y := y)
            (RatBall.lowerAt_radius_nonnegative hcut.1) hverticalRadius
            hxLower hy hlowerDomain hlowerCertified
        · have hxUpper := RatBall.upperAt_contains hx (le_of_not_ge hxCut)
          have hupperDomain : ∀ u v,
              (rectangle.upperHorizontal cut).horizontal.Contains u →
              (rectangle.upperHorizontal cut).vertical.Contains v →
              expression.DomainAt u v := by
            intro u v hu hv
            exact hdomain u v (RatBall.upperAt_contains_parent hu hcut.1) hv
          exact hupper (rectangle := rectangle.upperHorizontal cut) (x := x) (y := y)
            (RatBall.upperAt_radius_nonnegative hcut.2) hverticalRadius
            hxUpper hy hupperDomain hcertified
    · contradiction
  | vertical cut lower upper hlower hupper =>
    intro rectangle x y hhorizontalRadius _hverticalRadius hx hy hdomain hcertified
    unfold certifySubdivision at hcertified
    split at hcertified <;> rename_i hcut
    · cases hlowerCertified : certifySubdivision terms fuel bits
          (rectangle.lowerVertical cut) expression lower with
      | none => simp [hlowerCertified] at hcertified
      | some lowerWitness =>
        cases lowerWitness
        simp [hlowerCertified] at hcertified
        by_cases hyCut : y ≤ (cut : ℝ)
        · have hyLower := RatBall.lowerAt_contains hy hyCut
          have hlowerDomain : ∀ u v,
              (rectangle.lowerVertical cut).horizontal.Contains u →
              (rectangle.lowerVertical cut).vertical.Contains v →
              expression.DomainAt u v := by
            intro u v hu hv
            exact hdomain u v hu (RatBall.lowerAt_contains_parent hv hcut.2)
          exact hlower (rectangle := rectangle.lowerVertical cut) (x := x) (y := y)
            hhorizontalRadius (RatBall.lowerAt_radius_nonnegative hcut.1)
            hx hyLower hlowerDomain hlowerCertified
        · have hyUpper := RatBall.upperAt_contains hy (le_of_not_ge hyCut)
          have hupperDomain : ∀ u v,
              (rectangle.upperVertical cut).horizontal.Contains u →
              (rectangle.upperVertical cut).vertical.Contains v →
              expression.DomainAt u v := by
            intro u v hu hv
            exact hdomain u v hu (RatBall.upperAt_contains_parent hv hcut.1)
          exact hupper (rectangle := rectangle.upperVertical cut) (x := x) (y := y)
            hhorizontalRadius (RatBall.upperAt_radius_nonnegative hcut.2)
            hx hyUpper hupperDomain hcertified
    · contradiction

end Frankl
