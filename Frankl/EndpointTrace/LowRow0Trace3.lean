import Frankl.EndpointCertificate

namespace Frankl

private def lowRow0Cell1RootLLUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((427 : ℚ) / 64000) ((137 : ℚ) / 16000)⟩

private def lowRow0Cell1RootLLUUTree : Subdivision :=
.vertical ((39 : ℚ) / 5120)
  (.horizontal ((1 : ℚ) / 2000)
  (.vertical ((1829 : ℚ) / 256000)
  (.horizontal ((1 : ℚ) / 4000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((1 : ℚ) / 4000)
  (.leaf .interval)
  (.leaf .interval)))
  (.leaf .interval))
  (.horizontal ((1 : ℚ) / 2000)
  (.vertical ((2071 : ℚ) / 256000)
  (.horizontal ((1 : ℚ) / 4000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((1 : ℚ) / 4000)
  (.leaf .interval)
  (.leaf .interval)))
  (.leaf .interval))

private theorem lowRow0Cell1RootLLUUTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell1RootLLUURectangle
      CertificateObjective.endpointExpression lowRow0Cell1RootLLUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell1RootLLUU_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((427 : ℝ) / 64000) ≤ q)
    (hqUpper : q ≤ ((137 : ℝ) / 16000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell1RootLLUURectangle) (tree := lowRow0Cell1RootLLUUTree)
  · norm_num [lowRow0Cell1RootLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLUURectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell1RootLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell1RootLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell1RootLLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell1RootLLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell1RootLLUUTree_certified

private def lowRow0Cell1RootLULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((137 : ℚ) / 16000) ((79 : ℚ) / 6400)⟩

private def lowRow0Cell1RootLULTree : Subdivision :=
.vertical ((669 : ℚ) / 64000)
  (.vertical ((1217 : ℚ) / 128000)
  (.horizontal ((1 : ℚ) / 2000)
  (.vertical ((2313 : ℚ) / 256000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.horizontal ((1 : ℚ) / 2000)
  (.vertical ((511 : ℚ) / 51200)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval)))
  (.vertical ((1459 : ℚ) / 128000)
  (.horizontal ((1 : ℚ) / 2000)
  (.vertical ((2797 : ℚ) / 256000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.horizontal ((1 : ℚ) / 2000)
  (.vertical ((3039 : ℚ) / 256000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval)))

private theorem lowRow0Cell1RootLULTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell1RootLULRectangle
      CertificateObjective.endpointExpression lowRow0Cell1RootLULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell1RootLUL_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((137 : ℝ) / 16000) ≤ q)
    (hqUpper : q ≤ ((79 : ℝ) / 6400)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell1RootLULRectangle) (tree := lowRow0Cell1RootLULTree)
  · norm_num [lowRow0Cell1RootLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLULRectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell1RootLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell1RootLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell1RootLULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell1RootLULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell1RootLULTree_certified

end Frankl
