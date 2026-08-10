import Frankl.EndpointCertificate

namespace Frankl

private def lowRow10Cell16RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((9 : ℚ) / 64) ((5 : ℚ) / 32),
    RatBall.ofBounds ((15 : ℚ) / 32) ((1 : ℚ) / 2)⟩

private def lowRow10Cell16RootTree : Subdivision :=
.leaf .interval

private theorem lowRow10Cell16RootTree_certified :
    certifySubdivision 12 64 32 lowRow10Cell16RootRectangle
      CertificateObjective.endpointExpression lowRow10Cell16RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow10Cell16Root_nonneg {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow10Cell16RootRectangle) (tree := lowRow10Cell16RootTree)
  · norm_num [lowRow10Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell16RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow10Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell16RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow10Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell16RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow10Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow10Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow10Cell16RootTree_certified

end Frankl
