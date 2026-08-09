import Frankl.EndpointCertificate

namespace Frankl

private def lowRow1Cell0RootLUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((83 : ℚ) / 12800) ((133 : ℚ) / 16000),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow1Cell0RootLUUTree : Subdivision :=
.horizontal ((947 : ℚ) / 128000)
  (.vertical ((1 : ℚ) / 2000)
  (.horizontal ((1777 : ℚ) / 256000)
  (.vertical ((1 : ℚ) / 4000)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 4000)
  (.leaf .interval)
  (.leaf .interval)))
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 2000)
  (.horizontal ((2011 : ℚ) / 256000)
  (.vertical ((1 : ℚ) / 4000)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 4000)
  (.leaf .interval)
  (.leaf .interval)))
  (.leaf .interval))

private theorem lowRow1Cell0RootLUUTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell0RootLUURectangle
      CertificateObjective.endpointExpression lowRow1Cell0RootLUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell0RootLUU_nonneg {a q : ℝ}
    (haLower : ((83 : ℝ) / 12800) ≤ a)
    (haUpper : a ≤ ((133 : ℝ) / 16000))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell0RootLUURectangle) (tree := lowRow1Cell0RootLUUTree)
  · norm_num [lowRow1Cell0RootLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLUURectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell0RootLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell0RootLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell0RootLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell0RootLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell0RootLUUTree_certified

private def lowRow1Cell0RootULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((133 : ℚ) / 16000) ((383 : ℚ) / 32000),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow1Cell0RootULTree : Subdivision :=
.horizontal ((649 : ℚ) / 64000)
  (.horizontal ((1181 : ℚ) / 128000)
  (.vertical ((1 : ℚ) / 2000)
  (.horizontal ((449 : ℚ) / 51200)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 2000)
  (.horizontal ((2479 : ℚ) / 256000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval)))
  (.horizontal ((283 : ℚ) / 25600)
  (.vertical ((1 : ℚ) / 2000)
  (.horizontal ((2713 : ℚ) / 256000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 2000)
  (.horizontal ((2947 : ℚ) / 256000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval)))

private theorem lowRow1Cell0RootULTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell0RootULRectangle
      CertificateObjective.endpointExpression lowRow1Cell0RootULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell0RootUL_nonneg {a q : ℝ}
    (haLower : ((133 : ℝ) / 16000) ≤ a)
    (haUpper : a ≤ ((383 : ℝ) / 32000))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell0RootULRectangle) (tree := lowRow1Cell0RootULTree)
  · norm_num [lowRow1Cell0RootULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootULRectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell0RootULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell0RootULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell0RootULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell0RootULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell0RootULTree_certified

end Frankl
