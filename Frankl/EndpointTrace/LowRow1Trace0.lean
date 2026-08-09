import Frankl.EndpointCertificate

namespace Frankl

private def lowRow1Cell0RootLLLLLLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 1000) ((373 : ℚ) / 256000),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 2000)⟩

private def lowRow1Cell0RootLLLLLLTree : Subdivision :=
.vertical ((1 : ℚ) / 4000)
  (.horizontal ((629 : ℚ) / 512000)
  (.vertical ((1 : ℚ) / 8000)
  (.horizontal ((1141 : ℚ) / 1024000)
  (.vertical ((1 : ℚ) / 16000)
  (.horizontal ((433 : ℚ) / 409600)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval)))
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 8000)
  (.horizontal ((11 : ℚ) / 8192)
  (.vertical ((1 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval)))
  (.leaf .interval)))
  (.leaf .interval)

private theorem lowRow1Cell0RootLLLLLLTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell0RootLLLLLLRectangle
      CertificateObjective.endpointExpression lowRow1Cell0RootLLLLLLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell0RootLLLLLL_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((373 : ℝ) / 256000))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell0RootLLLLLLRectangle) (tree := lowRow1Cell0RootLLLLLLTree)
  · norm_num [lowRow1Cell0RootLLLLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLLLLLLRectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell0RootLLLLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLLLLLLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell0RootLLLLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLLLLLLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell0RootLLLLLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell0RootLLLLLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell0RootLLLLLLTree_certified

private def lowRow1Cell0RootLLLLLURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((373 : ℚ) / 256000) ((49 : ℚ) / 25600),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 2000)⟩

private def lowRow1Cell0RootLLLLLUTree : Subdivision :=
.vertical ((1 : ℚ) / 4000)
  (.horizontal ((863 : ℚ) / 512000)
  (.vertical ((1 : ℚ) / 8000)
  (.horizontal ((1609 : ℚ) / 1024000)
  (.vertical ((1 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval)))
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 8000)
  (.horizontal ((1843 : ℚ) / 1024000)
  (.vertical ((1 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.leaf .interval)))
  (.leaf .interval)

private theorem lowRow1Cell0RootLLLLLUTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell0RootLLLLLURectangle
      CertificateObjective.endpointExpression lowRow1Cell0RootLLLLLUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell0RootLLLLLU_nonneg {a q : ℝ}
    (haLower : ((373 : ℝ) / 256000) ≤ a)
    (haUpper : a ≤ ((49 : ℝ) / 25600))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell0RootLLLLLURectangle) (tree := lowRow1Cell0RootLLLLLUTree)
  · norm_num [lowRow1Cell0RootLLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLLLLLURectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell0RootLLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLLLLLURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell0RootLLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLLLLLURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell0RootLLLLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell0RootLLLLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell0RootLLLLLUTree_certified

private def lowRow1Cell0RootLLLLURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 1000) ((49 : ℚ) / 25600),
    RatBall.ofBounds ((1 : ℚ) / 2000) ((1 : ℚ) / 1000)⟩

private def lowRow1Cell0RootLLLLUTree : Subdivision :=
.leaf .interval

private theorem lowRow1Cell0RootLLLLUTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell0RootLLLLURectangle
      CertificateObjective.endpointExpression lowRow1Cell0RootLLLLUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell0RootLLLLU_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((49 : ℝ) / 25600))
    (hqLower : ((1 : ℝ) / 2000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell0RootLLLLURectangle) (tree := lowRow1Cell0RootLLLLUTree)
  · norm_num [lowRow1Cell0RootLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLLLLURectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell0RootLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLLLLURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell0RootLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell0RootLLLLURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell0RootLLLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell0RootLLLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell0RootLLLLUTree_certified

end Frankl
