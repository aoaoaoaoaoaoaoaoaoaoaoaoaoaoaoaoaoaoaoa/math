import Frankl.EndpointCertificate

namespace Frankl

private def lowRow13Cell16RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 16) ((13 : ℚ) / 64),
    RatBall.ofBounds ((15 : ℚ) / 32) ((1 : ℚ) / 2)⟩

private def lowRow13Cell16RootTree : Subdivision :=
.horizontal ((25 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow13Cell16RootTree_certified :
    certifySubdivision 12 64 32 lowRow13Cell16RootRectangle
      CertificateObjective.endpointExpression lowRow13Cell16RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow13Cell16Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow13Cell16RootRectangle) (tree := lowRow13Cell16RootTree)
  · norm_num [lowRow13Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell16RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow13Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell16RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow13Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell16RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow13Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow13Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow13Cell16RootTree_certified

end Frankl
