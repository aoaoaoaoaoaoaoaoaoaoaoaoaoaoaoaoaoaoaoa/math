import Frankl.Entropy

namespace Frankl

open Real Set

/-- The numerator controlling concavity in the low-orbit self-pair estimate. -/
def curvaturePolynomial (x y : ℝ) : ℝ :=
  2 * x ^ 4 * y ^ 2 - x ^ 4 - x ^ 3 * y ^ 2 - x ^ 3 * y - x ^ 3
    - 3 * x ^ 2 * y ^ 2 + 5 * x ^ 2 * y + x ^ 2 - 2 * x * y ^ 2
    + 3 * x * y - 2 * x + y - 1

/-- The curvature polynomial is nonpositive on `1/2 ≤ y ≤ x ≤ 1`.

The proof is the exact degree-six Bernstein expansion in barycentric coordinates
`u=2(1-x)`, `v=2(x-y)`, and `z=2y-1`. -/
theorem curvaturePolynomial_nonpos {x y : ℝ} (hy : 1 / 2 ≤ y) (hyx : y ≤ x)
    (hx : x ≤ 1) : curvaturePolynomial x y ≤ 0 := by
  let u := 2 * (1 - x)
  let v := 2 * (x - y)
  let z := 2 * y - 1
  have hu : 0 ≤ u := by
    dsimp [u]
    nlinarith
  have hv : 0 ≤ v := by
    dsimp [v]
    nlinarith
  have hz : 0 ≤ z := by
    dsimp [z]
    linarith
  have hidentity :
      -curvaturePolynomial x y =
        v ^ 2 * z ^ 4
          + 4 * v ^ 3 * z ^ 3
          + 6 * v ^ 4 * z ^ 2
          + 4 * v ^ 5 * z
          + v ^ 6
          + u * v * z ^ 4
          + (61 / 8 : ℝ) * u * v ^ 2 * z ^ 3
          + (135 / 8 : ℝ) * u * v ^ 3 * z ^ 2
          + (119 / 8 : ℝ) * u * v ^ 4 * z
          + (37 / 8 : ℝ) * u * v ^ 5
          + 5 * u ^ 2 * v * z ^ 3
          + (39 / 2 : ℝ) * u ^ 2 * v ^ 2 * z ^ 2
          + 24 * u ^ 2 * v ^ 3 * z
          + (19 / 2 : ℝ) * u ^ 2 * v ^ 4
          + (3 / 2 : ℝ) * u ^ 3 * z ^ 3
          + (191 / 16 : ℝ) * u ^ 3 * v * z ^ 2
          + (695 / 32 : ℝ) * u ^ 3 * v ^ 2 * z
          + (361 / 32 : ℝ) * u ^ 3 * v ^ 3
          + (13 / 4 : ℝ) * u ^ 4 * z ^ 2
          + (175 / 16 : ℝ) * u ^ 4 * v * z
          + (65 / 8 : ℝ) * u ^ 4 * v ^ 2
          + (75 / 32 : ℝ) * u ^ 5 * z
          + (105 / 32 : ℝ) * u ^ 5 * v
          + (9 / 16 : ℝ) * u ^ 6 := by
    dsimp [curvaturePolynomial, u, v, z]
    ring
  have hnonneg : 0 ≤ -curvaturePolynomial x y := by
    rw [hidentity]
    positivity
  linarith

/-- The Jensen deficit of a symmetric two-point law about its mean. -/
noncomputable def orbitDeficit (f : ℝ → ℝ) (a d : ℝ) : ℝ :=
  f a - (f (a - d) + f (a + d)) / 2

/-- Binary entropy has nonnegative Jensen deficit on every symmetric low orbit. -/
theorem orbitDeficit_nonneg {a d : ℝ}
    (hlower : 0 ≤ a - d) (hupper : a + d ≤ 1) (hd : 0 ≤ d) :
    0 ≤ orbitDeficit binEntropy a d := by
  have hleft : a - d ∈ Icc (0 : ℝ) 1 := ⟨hlower, by linarith⟩
  have hright : a + d ∈ Icc (0 : ℝ) 1 := ⟨by linarith, hupper⟩
  have hmid := strictConcave_binEntropy.concaveOn.2 hleft hright
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  dsimp only [smul_eq_mul] at hmid
  have hpoint : (1 / 2 : ℝ) * (a - d) + 1 / 2 * (a + d) = a := by ring
  rw [hpoint] at hmid
  dsimp [orbitDeficit]
  linarith

/-- Curvature-comparison remainder between scaled marginal entropy and join entropy. -/
noncomputable def joinEntropyDifference (q coefficient x : ℝ) : ℝ :=
  coefficient * binEntropy x - binEntropy (join x q)

private noncomputable def joinEntropyDifferenceDeriv (q coefficient x : ℝ) : ℝ :=
  coefficient * (log (1 - x) - log x)
    - (1 - q) * (log (1 - join x q) - log (join x q))

private noncomputable def joinEntropyDifferenceDeriv2 (q coefficient x : ℝ) : ℝ :=
  coefficient * (-1 / (1 - x) - 1 / x)
    - (1 - q) * (-(1 - q) / (1 - join x q) - (1 - q) / join x q)

private theorem hasDerivAt_join (q x : ℝ) :
    HasDerivAt (fun y ↦ join y q) (1 - q) x := by
  have h : HasDerivAt (fun y : ℝ ↦ q + y * (1 - q)) (1 - q) x := by
    simpa only [id_eq, one_mul] using ((hasDerivAt_id x).mul_const (1 - q)).const_add q
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [join]
  ring

private theorem hasDerivAt_joinEntropyDifference {q coefficient x : ℝ}
    (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) (hjoin₀ : join x q ≠ 0) (hjoin₁ : join x q ≠ 1) :
    HasDerivAt (joinEntropyDifference q coefficient)
      (joinEntropyDifferenceDeriv q coefficient x) x := by
  have houter := hasDerivAt_binEntropy hjoin₀ hjoin₁
  have hcomp := houter.comp x (hasDerivAt_join q x)
  convert ((hasDerivAt_binEntropy hx₀ hx₁).const_mul coefficient).sub hcomp using 1
  all_goals
    first
    | simp only [joinEntropyDifferenceDeriv]
      ring
    | rfl

private theorem hasDerivAt_joinEntropyDifferenceDeriv {q coefficient x : ℝ}
    (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) (hjoin₀ : join x q ≠ 0) (hjoin₁ : join x q ≠ 1) :
    HasDerivAt (joinEntropyDifferenceDeriv q coefficient)
      (joinEntropyDifferenceDeriv2 q coefficient x) x := by
  have hxlog : HasDerivAt (fun y : ℝ ↦ log y) x⁻¹ x :=
    by simpa only [id_eq, one_div] using (hasDerivAt_id x).log hx₀
  have hxcomplog : HasDerivAt (fun y : ℝ ↦ log (1 - y)) (-1 / (1 - x)) x := by
    simpa only [id_eq] using
      ((hasDerivAt_id x).const_sub 1).log (sub_ne_zero.mpr hx₁.symm)
  have hj := hasDerivAt_join q x
  have hjlog : HasDerivAt (fun y : ℝ ↦ log (join y q)) ((1 - q) / join x q) x := by
    simpa only [one_div] using hj.log hjoin₀
  have hjcomplog : HasDerivAt (fun y : ℝ ↦ log (1 - join y q))
      (-(1 - q) / (1 - join x q)) x := by
    simpa only [one_div] using
      (hj.const_sub 1 |>.log (sub_ne_zero.mpr hjoin₁.symm))
  unfold joinEntropyDifferenceDeriv joinEntropyDifferenceDeriv2
  apply HasDerivAt.sub
  · apply HasDerivAt.const_mul
    apply HasDerivAt.sub
    · exact hxcomplog
    · simpa only [one_div] using hxlog
  · apply HasDerivAt.const_mul
    apply HasDerivAt.sub
    · exact hjcomplog
    · exact hjlog

/-- The join-curvature remainder is concave on every interval where its curvature ratio is
bounded. -/
theorem joinEntropyDifference_concaveOn {q coefficient upper : ℝ}
    (hupper₁ : upper < 1)
    (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (hcoefficient : ∀ x ∈ Ioo (0 : ℝ) upper,
      x * (1 - q) / join x q ≤ coefficient) :
    ConcaveOn ℝ (Icc (0 : ℝ) upper) (joinEntropyDifference q coefficient) := by
  refine concaveOn_of_hasDerivWithinAt2_nonpos (f' := joinEntropyDifferenceDeriv q coefficient)
    (f'' := joinEntropyDifferenceDeriv2 q coefficient) (convex_Icc 0 upper)
    (by
      apply Continuous.continuousOn
      change Continuous (fun x ↦ coefficient * binEntropy x - binEntropy (x + q - x * q))
      fun_prop)
    ?_ ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx
    change 0 < x ∧ x < upper at hx
    have hx₀ : x ≠ 0 := ne_of_gt hx.1
    have hx₁ : x ≠ 1 := by linarith
    have hjoin_pos : 0 < join x q := join_pos_of_pos_left hx.1 hq₀ hq₁.le
    have hjoin_lt : join x q < 1 := join_lt_one_of_lt_left (by linarith) hq₁
    exact (hasDerivAt_joinEntropyDifference hx₀ hx₁ hjoin_pos.ne' hjoin_lt.ne).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    change 0 < x ∧ x < upper at hx
    have hx₀ : x ≠ 0 := ne_of_gt hx.1
    have hx₁ : x ≠ 1 := by linarith
    have hjoin_pos : 0 < join x q := join_pos_of_pos_left hx.1 hq₀ hq₁.le
    have hjoin_lt : join x q < 1 := join_lt_one_of_lt_left (by linarith) hq₁
    exact (hasDerivAt_joinEntropyDifferenceDeriv hx₀ hx₁ hjoin_pos.ne' hjoin_lt.ne).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    change 0 < x ∧ x < upper at hx
    have hx₁ : x < 1 := by linarith
    have hjoin_pos : 0 < join x q := join_pos_of_pos_left hx.1 hq₀ hq₁.le
    have hjoin_lt : join x q < 1 := join_lt_one_of_lt_left hx₁ hq₁
    have hratio := hcoefficient x hx
    have hidentity :
        joinEntropyDifferenceDeriv2 q coefficient x =
          (x * (1 - q) / join x q - coefficient) / (x * (1 - x)) := by
      dsimp [joinEntropyDifferenceDeriv2]
      field_simp [hx.1.ne', (sub_pos.2 hx₁).ne', hjoin_pos.ne',
        (sub_pos.2 hjoin_lt).ne']
      rw [one_sub_join]
      simp only [join]
      ring
    rw [hidentity]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hratio)
      (mul_nonneg hx.1.le (sub_nonneg.2 hx₁.le))

theorem orbitDeficit_joinEntropy_le {a d q coefficient : ℝ}
    (ha₀ : 0 ≤ a - d) (ha₁ : a + d ≤ 1 / 2) (hd : 0 ≤ d)
    (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (hcoefficient : ∀ x ∈ Ioo (0 : ℝ) (1 / 2),
      x * (1 - q) / join x q ≤ coefficient) :
    orbitDeficit (fun x ↦ binEntropy (join x q)) a d ≤
      coefficient * orbitDeficit binEntropy a d := by
  have hleft : a - d ∈ Icc (0 : ℝ) (1 / 2) := ⟨ha₀, by linarith⟩
  have hright : a + d ∈ Icc (0 : ℝ) (1 / 2) := ⟨by linarith, ha₁⟩
  have hmid := (joinEntropyDifference_concaveOn (upper := (1 : ℝ) / 2)
    (by norm_num) hq₀ hq₁ hcoefficient).2
    hleft hright (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  dsimp [joinEntropyDifference] at hmid
  dsimp [orbitDeficit]
  have hmid' :
      ((coefficient * binEntropy (a - d) - binEntropy (join (a - d) q))
          + (coefficient * binEntropy (a + d) - binEntropy (join (a + d) q))) / 2 ≤
        coefficient * binEntropy a - binEntropy (join a q) := by
    convert hmid using 1 <;> first | rfl | ring_nf
  linarith

/-- The sharp elementary curvature coefficient for a low external parameter. -/
theorem orbitDeficit_joinEntropy_le_ratio {a d q : ℝ}
    (ha₀ : 0 ≤ a - d) (ha₁ : a + d ≤ 1 / 2) (hd : 0 ≤ d)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1 / 2) :
    orbitDeficit (fun x ↦ binEntropy (join x q)) a d ≤
      (1 - q) / (1 + q) * orbitDeficit binEntropy a d := by
  refine orbitDeficit_joinEntropy_le ha₀ ha₁ hd hq₀ (by linarith) ?_
  intro x hx
  exact join_curvature_ratio_le hx.1 hx.2.le hq₀ hq₁

/-- The affine curvature coefficient used in the ordered two-orbit contraction. -/
theorem orbitDeficit_joinEntropy_le_affine {a d q : ℝ}
    (ha₀ : 0 ≤ a - d) (ha₁ : a + d ≤ 1 / 2) (hd : 0 ≤ d)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1 / 2) :
    orbitDeficit (fun x ↦ binEntropy (join x q)) a d ≤
      (1 - 4 * q / 3) * orbitDeficit binEntropy a d := by
  refine orbitDeficit_joinEntropy_le ha₀ ha₁ hd hq₀ (by linarith) ?_
  intro x hx
  exact join_curvature_ratio_le_affine hx.1 hx.2.le hq₀ hq₁

/-- The endpoint curvature coefficient, valid for every external parameter. -/
theorem orbitDeficit_joinEntropy_le_endpoint {a d q : ℝ}
    (ha₀ : 0 ≤ a - d) (ha₁ : a + d ≤ 1 / 2) (hd : 0 ≤ d)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    orbitDeficit (fun x ↦ binEntropy (join x q)) a d ≤
      (1 - q) * orbitDeficit binEntropy a d := by
  rcases hq₁.eq_or_lt with rfl | hq₁
  · simp [orbitDeficit]
  · refine orbitDeficit_joinEntropy_le ha₀ ha₁ hd hq₀ hq₁ ?_
    intro x hx
    have hjoin : 0 < join x q := join_pos_of_pos_left hx.1 hq₀ hq₁.le
    rw [div_le_iff₀ hjoin]
    have hx₁ : x ≤ 1 := hx.2.le.trans (by norm_num)
    have hpjoin : x ≤ join x q := by
      dsimp [join]
      nlinarith [mul_nonneg hq₀ (sub_nonneg.2 hx₁)]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hpjoin (sub_nonneg.2 hq₁.le)

end Frankl
