import Frankl.EndpointCertificate

namespace Frankl

private def lowRow0Cell1RootLLLUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((491 : ℚ) / 128000) ((153 : ℚ) / 32000)⟩

private def lowRow0Cell1RootLLLUUTree : Subdivision :=
.horizontal ((1 : ℚ) / 2000)
  (.vertical ((1103 : ℚ) / 256000)
  (.horizontal ((1 : ℚ) / 4000)
  (.vertical ((417 : ℚ) / 102400)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.horizontal ((1 : ℚ) / 4000)
  (.vertical ((2327 : ℚ) / 512000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval)))
  (.leaf .interval)

private theorem lowRow0Cell1RootLLLUUTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell1RootLLLUURectangle
      CertificateObjective.endpointExpression lowRow0Cell1RootLLLUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell1RootLLLUU_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((491 : ℝ) / 128000) ≤ q)
    (hqUpper : q ≤ ((153 : ℝ) / 32000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell1RootLLLUURectangle) (tree := lowRow0Cell1RootLLLUUTree)
  · norm_num [lowRow0Cell1RootLLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLUURectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell1RootLLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell1RootLLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell1RootLLLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell1RootLLLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell1RootLLLUUTree_certified

private def lowRow0Cell1RootLLULLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((153 : ℚ) / 32000) ((733 : ℚ) / 128000)⟩

private def lowRow0Cell1RootLLULLTree : Subdivision :=
.horizontal ((1 : ℚ) / 2000)
  (.vertical ((269 : ℚ) / 51200)
  (.horizontal ((1 : ℚ) / 4000)
  (.vertical ((2569 : ℚ) / 512000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.horizontal ((1 : ℚ) / 4000)
  (.vertical ((2811 : ℚ) / 512000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval)))
  (.leaf .interval)

private theorem lowRow0Cell1RootLLULLTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell1RootLLULLRectangle
      CertificateObjective.endpointExpression lowRow0Cell1RootLLULLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell1RootLLULL_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((153 : ℝ) / 32000) ≤ q)
    (hqUpper : q ≤ ((733 : ℝ) / 128000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell1RootLLULLRectangle) (tree := lowRow0Cell1RootLLULLTree)
  · norm_num [lowRow0Cell1RootLLULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLULLRectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell1RootLLULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLULLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell1RootLLULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLULLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell1RootLLULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell1RootLLULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell1RootLLULLTree_certified

private def lowRow0Cell1RootLLULURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((733 : ℚ) / 128000) ((427 : ℚ) / 64000)⟩

private def lowRow0Cell1RootLLULUTree : Subdivision :=
.horizontal ((1 : ℚ) / 2000)
  (.vertical ((1587 : ℚ) / 256000)
  (.horizontal ((1 : ℚ) / 4000)
  (.vertical ((3053 : ℚ) / 512000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.horizontal ((1 : ℚ) / 4000)
  (.leaf .interval)
  (.leaf .interval)))
  (.leaf .interval)

private theorem lowRow0Cell1RootLLULUTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell1RootLLULURectangle
      CertificateObjective.endpointExpression lowRow0Cell1RootLLULUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell1RootLLULU_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((733 : ℝ) / 128000) ≤ q)
    (hqUpper : q ≤ ((427 : ℝ) / 64000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell1RootLLULURectangle) (tree := lowRow0Cell1RootLLULUTree)
  · norm_num [lowRow0Cell1RootLLULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLULURectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell1RootLLULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLULURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell1RootLLULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLULURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell1RootLLULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell1RootLLULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell1RootLLULUTree_certified

end Frankl
