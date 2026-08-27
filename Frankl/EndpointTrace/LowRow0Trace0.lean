import Frankl.EndpointCertificate

namespace Frankl

private def lowRow0Cell0RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow0Cell0RootTree : Subdivision :=
.leaf .zeroCorner

private theorem lowRow0Cell0RootTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell0RootRectangle
      CertificateObjective.endpointExpression lowRow0Cell0RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell0Root_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell0RootRectangle) (tree := lowRow0Cell0RootTree)
  · norm_num [lowRow0Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell0RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell0RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell0RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell0RootTree_certified

private def lowRow0Cell1RootLLLLLLLLLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 4000),
    RatBall.ofBounds ((1 : ℚ) / 1000) ((633 : ℚ) / 512000)⟩

private def lowRow0Cell1RootLLLLLLLLLTree : Subdivision :=
.horizontal ((1 : ℚ) / 8000)
  (.vertical ((229 : ℚ) / 204800)
  (.horizontal ((1 : ℚ) / 16000)
  (.vertical ((2169 : ℚ) / 2048000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.horizontal ((1 : ℚ) / 16000)
  (.vertical ((2411 : ℚ) / 2048000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval)))
  (.leaf .interval)

private theorem lowRow0Cell1RootLLLLLLLLLTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell1RootLLLLLLLLLRectangle
      CertificateObjective.endpointExpression lowRow0Cell1RootLLLLLLLLLTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell1RootLLLLLLLLL_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 4000))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((633 : ℝ) / 512000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell1RootLLLLLLLLLRectangle) (tree := lowRow0Cell1RootLLLLLLLLLTree)
  · norm_num [lowRow0Cell1RootLLLLLLLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLLLLLLRectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell1RootLLLLLLLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLLLLLLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell1RootLLLLLLLLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLLLLLLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell1RootLLLLLLLLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell1RootLLLLLLLLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell1RootLLLLLLLLLTree_certified

private def lowRow0Cell1RootLLLLLLLLURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 4000),
    RatBall.ofBounds ((633 : ℚ) / 512000) ((377 : ℚ) / 256000)⟩

private def lowRow0Cell1RootLLLLLLLLUTree : Subdivision :=
.horizontal ((1 : ℚ) / 8000)
  (.vertical ((1387 : ℚ) / 1024000)
  (.horizontal ((1 : ℚ) / 16000)
  (.vertical ((2653 : ℚ) / 2048000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.horizontal ((1 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval)))
  (.leaf .interval)

private theorem lowRow0Cell1RootLLLLLLLLUTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell1RootLLLLLLLLURectangle
      CertificateObjective.endpointExpression lowRow0Cell1RootLLLLLLLLUTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell1RootLLLLLLLLU_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 4000))
    (hqLower : ((633 : ℝ) / 512000) ≤ q)
    (hqUpper : q ≤ ((377 : ℝ) / 256000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell1RootLLLLLLLLURectangle) (tree := lowRow0Cell1RootLLLLLLLLUTree)
  · norm_num [lowRow0Cell1RootLLLLLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLLLLLURectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell1RootLLLLLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLLLLLURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell1RootLLLLLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLLLLLURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell1RootLLLLLLLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell1RootLLLLLLLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell1RootLLLLLLLLUTree_certified

private def lowRow0Cell1RootLLLLLLLURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 4000) ((1 : ℚ) / 2000),
    RatBall.ofBounds ((1 : ℚ) / 1000) ((377 : ℚ) / 256000)⟩

private def lowRow0Cell1RootLLLLLLLUTree : Subdivision :=
.leaf .interval

private theorem lowRow0Cell1RootLLLLLLLUTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell1RootLLLLLLLURectangle
      CertificateObjective.endpointExpression lowRow0Cell1RootLLLLLLLUTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell1RootLLLLLLLU_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 4000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 2000))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((377 : ℝ) / 256000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell1RootLLLLLLLURectangle) (tree := lowRow0Cell1RootLLLLLLLUTree)
  · norm_num [lowRow0Cell1RootLLLLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLLLLURectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell1RootLLLLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLLLLURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell1RootLLLLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLLLLURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell1RootLLLLLLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell1RootLLLLLLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell1RootLLLLLLLUTree_certified

private def lowRow0Cell1RootLLLLLLURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 2000),
    RatBall.ofBounds ((377 : ℚ) / 256000) ((249 : ℚ) / 128000)⟩

private def lowRow0Cell1RootLLLLLLUTree : Subdivision :=
.horizontal ((1 : ℚ) / 4000)
  (.vertical ((7 : ℚ) / 4096)
  (.horizontal ((1 : ℚ) / 8000)
  (.vertical ((1629 : ℚ) / 1024000)
  (.horizontal ((1 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((1 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval)))
  (.leaf .interval))
  (.horizontal ((1 : ℚ) / 8000)
  (.vertical ((1871 : ℚ) / 1024000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval)))
  (.leaf .interval)

private theorem lowRow0Cell1RootLLLLLLUTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell1RootLLLLLLURectangle
      CertificateObjective.endpointExpression lowRow0Cell1RootLLLLLLUTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell1RootLLLLLLU_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 2000))
    (hqLower : ((377 : ℝ) / 256000) ≤ q)
    (hqUpper : q ≤ ((249 : ℝ) / 128000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell1RootLLLLLLURectangle) (tree := lowRow0Cell1RootLLLLLLUTree)
  · norm_num [lowRow0Cell1RootLLLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLLLURectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell1RootLLLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLLLURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell1RootLLLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLLLURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell1RootLLLLLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell1RootLLLLLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell1RootLLLLLLUTree_certified

private def lowRow0Cell1RootLLLLLURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 2000) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((1 : ℚ) / 1000) ((249 : ℚ) / 128000)⟩

private def lowRow0Cell1RootLLLLLUTree : Subdivision :=
.leaf .interval

private theorem lowRow0Cell1RootLLLLLUTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell1RootLLLLLURectangle
      CertificateObjective.endpointExpression lowRow0Cell1RootLLLLLUTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell1RootLLLLLU_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 2000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((249 : ℝ) / 128000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell1RootLLLLLURectangle) (tree := lowRow0Cell1RootLLLLLUTree)
  · norm_num [lowRow0Cell1RootLLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLLURectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell1RootLLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLLURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell1RootLLLLLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLLURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell1RootLLLLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell1RootLLLLLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell1RootLLLLLUTree_certified

end Frankl
