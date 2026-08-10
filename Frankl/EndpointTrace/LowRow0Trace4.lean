import Frankl.EndpointCertificate

namespace Frankl

private def lowRow0Cell1RootLUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((79 : ℚ) / 6400) ((129 : ℚ) / 8000)⟩

private def lowRow0Cell1RootLUUTree : Subdivision :=
.vertical ((911 : ℚ) / 64000)
  (.vertical ((1701 : ℚ) / 128000)
  (.horizontal ((1 : ℚ) / 2000)
  (.vertical ((3281 : ℚ) / 256000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.horizontal ((1 : ℚ) / 2000)
  (.vertical ((3523 : ℚ) / 256000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval)))
  (.vertical ((1943 : ℚ) / 128000)
  (.horizontal ((1 : ℚ) / 2000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((1 : ℚ) / 2000)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow0Cell1RootLUUTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell1RootLUURectangle
      CertificateObjective.endpointExpression lowRow0Cell1RootLUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell1RootLUU_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((79 : ℝ) / 6400) ≤ q)
    (hqUpper : q ≤ ((129 : ℝ) / 8000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell1RootLUURectangle) (tree := lowRow0Cell1RootLUUTree)
  · norm_num [lowRow0Cell1RootLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLUURectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell1RootLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell1RootLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell1RootLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell1RootLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell1RootLUUTree_certified

private def lowRow0Cell1RootULLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((129 : ℚ) / 8000) ((637 : ℚ) / 32000)⟩

private def lowRow0Cell1RootULLTree : Subdivision :=
.vertical ((1153 : ℚ) / 64000)
  (.vertical ((437 : ℚ) / 25600)
  (.horizontal ((1 : ℚ) / 2000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((1 : ℚ) / 2000)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((2427 : ℚ) / 128000)
  (.horizontal ((1 : ℚ) / 2000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((1 : ℚ) / 2000)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow0Cell1RootULLTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell1RootULLRectangle
      CertificateObjective.endpointExpression lowRow0Cell1RootULLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell1RootULL_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((129 : ℝ) / 8000) ≤ q)
    (hqUpper : q ≤ ((637 : ℝ) / 32000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell1RootULLRectangle) (tree := lowRow0Cell1RootULLTree)
  · norm_num [lowRow0Cell1RootULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootULLRectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell1RootULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootULLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell1RootULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootULLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell1RootULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell1RootULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell1RootULLTree_certified

private def lowRow0Cell1RootULURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((637 : ℚ) / 32000) ((379 : ℚ) / 16000)⟩

private def lowRow0Cell1RootULUTree : Subdivision :=
.vertical ((279 : ℚ) / 12800)
  (.vertical ((2669 : ℚ) / 128000)
  (.horizontal ((1 : ℚ) / 2000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((1 : ℚ) / 2000)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((2911 : ℚ) / 128000)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow0Cell1RootULUTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell1RootULURectangle
      CertificateObjective.endpointExpression lowRow0Cell1RootULUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell1RootULU_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((637 : ℝ) / 32000) ≤ q)
    (hqUpper : q ≤ ((379 : ℝ) / 16000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell1RootULURectangle) (tree := lowRow0Cell1RootULUTree)
  · norm_num [lowRow0Cell1RootULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootULURectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell1RootULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootULURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell1RootULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootULURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell1RootULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell1RootULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell1RootULUTree_certified

end Frankl
