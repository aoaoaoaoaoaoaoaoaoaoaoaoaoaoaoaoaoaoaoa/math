import Frankl.EndpointCertificate

namespace Frankl

private def lowRow13Cell6RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 16) ((13 : ℚ) / 64),
    RatBall.ofBounds ((5 : ℚ) / 32) ((3 : ℚ) / 16)⟩

private def lowRow13Cell6RootTree : Subdivision :=
.horizontal ((25 : ℚ) / 128)
  (.vertical ((11 : ℚ) / 64)
  (.horizontal ((49 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((49 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((11 : ℚ) / 64)
  (.horizontal ((51 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((51 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow13Cell6RootTree_certified :
    certifySubdivision 12 64 32 lowRow13Cell6RootRectangle
      CertificateObjective.endpointExpression lowRow13Cell6RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow13Cell6Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow13Cell6RootRectangle) (tree := lowRow13Cell6RootTree)
  · norm_num [lowRow13Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell6RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow13Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell6RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow13Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell6RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow13Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow13Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow13Cell6RootTree_certified

private def lowRow13Cell7RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 16) ((13 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 16) ((7 : ℚ) / 32)⟩

private def lowRow13Cell7RootTree : Subdivision :=
.horizontal ((25 : ℚ) / 128)
  (.vertical ((13 : ℚ) / 64)
  (.horizontal ((49 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((49 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((13 : ℚ) / 64)
  (.horizontal ((51 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((51 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow13Cell7RootTree_certified :
    certifySubdivision 12 64 32 lowRow13Cell7RootRectangle
      CertificateObjective.endpointExpression lowRow13Cell7RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow13Cell7Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow13Cell7RootRectangle) (tree := lowRow13Cell7RootTree)
  · norm_num [lowRow13Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell7RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow13Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell7RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow13Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell7RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow13Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow13Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow13Cell7RootTree_certified

private def lowRow13Cell8RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 16) ((13 : ℚ) / 64),
    RatBall.ofBounds ((7 : ℚ) / 32) ((1 : ℚ) / 4)⟩

private def lowRow13Cell8RootTree : Subdivision :=
.horizontal ((25 : ℚ) / 128)
  (.vertical ((15 : ℚ) / 64)
  (.horizontal ((49 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((49 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((15 : ℚ) / 64)
  (.horizontal ((51 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((51 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow13Cell8RootTree_certified :
    certifySubdivision 12 64 32 lowRow13Cell8RootRectangle
      CertificateObjective.endpointExpression lowRow13Cell8RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow13Cell8Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow13Cell8RootRectangle) (tree := lowRow13Cell8RootTree)
  · norm_num [lowRow13Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell8RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow13Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell8RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow13Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell8RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow13Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow13Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow13Cell8RootTree_certified

end Frankl
