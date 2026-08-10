import Frankl.EndpointCertificate

namespace Frankl

private def lowRow1Cell0RootLLLULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((49 : ℚ) / 25600) ((181 : ℚ) / 64000),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 2000)⟩

private def lowRow1Cell0RootLLLULTree : Subdivision :=
.horizontal ((607 : ℚ) / 256000)
  (.vertical ((1 : ℚ) / 4000)
  (.horizontal ((1097 : ℚ) / 512000)
  (.vertical ((1 : ℚ) / 8000)
  (.horizontal ((2077 : ℚ) / 1024000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 8000)
  (.horizontal ((2311 : ℚ) / 1024000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval)))
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 4000)
  (.horizontal ((1331 : ℚ) / 512000)
  (.vertical ((1 : ℚ) / 8000)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 8000)
  (.leaf .interval)
  (.leaf .interval)))
  (.leaf .interval))

private theorem lowRow1Cell0RootLLLULTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell0RootLLLULRectangle
      CertificateObjective.endpointExpression lowRow1Cell0RootLLLULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell0RootLLLUL_nonneg {a q : ℝ}
    (haLower : ((49 : ℝ) / 25600) ≤ a)
    (haUpper : a ≤ ((181 : ℝ) / 64000))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell0RootLLLULRectangle) (tree := lowRow1Cell0RootLLLULTree)
  · norm_num [lowRow1Cell0RootLLLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLLLULRectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell0RootLLLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLLLULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell0RootLLLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLLLULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell0RootLLLULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell0RootLLLULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell0RootLLLULTree_certified

private def lowRow1Cell0RootLLLUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((49 : ℚ) / 25600) ((181 : ℚ) / 64000),
    RatBall.ofBounds ((1 : ℚ) / 2000) ((1 : ℚ) / 1000)⟩

private def lowRow1Cell0RootLLLUUTree : Subdivision :=
.leaf .interval

private theorem lowRow1Cell0RootLLLUUTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell0RootLLLUURectangle
      CertificateObjective.endpointExpression lowRow1Cell0RootLLLUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell0RootLLLUU_nonneg {a q : ℝ}
    (haLower : ((49 : ℝ) / 25600) ≤ a)
    (haUpper : a ≤ ((181 : ℝ) / 64000))
    (hqLower : ((1 : ℝ) / 2000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell0RootLLLUURectangle) (tree := lowRow1Cell0RootLLLUUTree)
  · norm_num [lowRow1Cell0RootLLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLLLUURectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell0RootLLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLLLUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell0RootLLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLLLUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell0RootLLLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell0RootLLLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell0RootLLLUUTree_certified

private def lowRow1Cell0RootLLULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((181 : ℚ) / 64000) ((479 : ℚ) / 128000),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow1Cell0RootLLULTree : Subdivision :=
.vertical ((1 : ℚ) / 2000)
  (.horizontal ((841 : ℚ) / 256000)
  (.vertical ((1 : ℚ) / 4000)
  (.horizontal ((313 : ℚ) / 102400)
  (.vertical ((1 : ℚ) / 8000)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 8000)
  (.leaf .interval)
  (.leaf .interval)))
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 4000)
  (.horizontal ((1799 : ℚ) / 512000)
  (.vertical ((1 : ℚ) / 8000)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 8000)
  (.leaf .interval)
  (.leaf .interval)))
  (.leaf .interval)))
  (.leaf .interval)

private theorem lowRow1Cell0RootLLULTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell0RootLLULRectangle
      CertificateObjective.endpointExpression lowRow1Cell0RootLLULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell0RootLLUL_nonneg {a q : ℝ}
    (haLower : ((181 : ℝ) / 64000) ≤ a)
    (haUpper : a ≤ ((479 : ℝ) / 128000))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell0RootLLULRectangle) (tree := lowRow1Cell0RootLLULTree)
  · norm_num [lowRow1Cell0RootLLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLLULRectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell0RootLLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLLULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell0RootLLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLLULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell0RootLLULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell0RootLLULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell0RootLLULTree_certified

end Frankl
