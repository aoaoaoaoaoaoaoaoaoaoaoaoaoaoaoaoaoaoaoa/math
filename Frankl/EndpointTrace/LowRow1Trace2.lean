import Frankl.EndpointCertificate

namespace Frankl

private def lowRow1Cell0RootLLUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((479 : ℚ) / 128000) ((149 : ℚ) / 32000),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow1Cell0RootLLUUTree : Subdivision :=
.vertical ((1 : ℚ) / 2000)
  (.horizontal ((43 : ℚ) / 10240)
  (.vertical ((1 : ℚ) / 4000)
  (.horizontal ((2033 : ℚ) / 512000)
  (.vertical ((1 : ℚ) / 8000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 4000)
  (.horizontal ((2267 : ℚ) / 512000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval)))
  (.leaf .interval)

private theorem lowRow1Cell0RootLLUUTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell0RootLLUURectangle
      CertificateObjective.endpointExpression lowRow1Cell0RootLLUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell0RootLLUU_nonneg {a q : ℝ}
    (haLower : ((479 : ℝ) / 128000) ≤ a)
    (haUpper : a ≤ ((149 : ℝ) / 32000))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell0RootLLUURectangle) (tree := lowRow1Cell0RootLLUUTree)
  · norm_num [lowRow1Cell0RootLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLLUURectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell0RootLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLLUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell0RootLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLLUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell0RootLLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell0RootLLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell0RootLLUUTree_certified

private def lowRow1Cell0RootLULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((149 : ℚ) / 32000) ((83 : ℚ) / 12800),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow1Cell0RootLULTree : Subdivision :=
.horizontal ((713 : ℚ) / 128000)
  (.vertical ((1 : ℚ) / 2000)
  (.horizontal ((1309 : ℚ) / 256000)
  (.vertical ((1 : ℚ) / 4000)
  (.horizontal ((2501 : ℚ) / 512000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 4000)
  (.leaf .interval)
  (.leaf .interval)))
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 2000)
  (.horizontal ((1543 : ℚ) / 256000)
  (.vertical ((1 : ℚ) / 4000)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 4000)
  (.leaf .interval)
  (.leaf .interval)))
  (.leaf .interval))

private theorem lowRow1Cell0RootLULTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell0RootLULRectangle
      CertificateObjective.endpointExpression lowRow1Cell0RootLULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell0RootLUL_nonneg {a q : ℝ}
    (haLower : ((149 : ℝ) / 32000) ≤ a)
    (haUpper : a ≤ ((83 : ℝ) / 12800))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell0RootLULRectangle) (tree := lowRow1Cell0RootLULTree)
  · norm_num [lowRow1Cell0RootLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLULRectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell0RootLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell0RootLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell0RootLULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell0RootLULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell0RootLULTree_certified

end Frankl
