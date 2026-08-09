import Frankl.EndpointCertificate

namespace Frankl

private def lowRow0Cell1RootLLLLULLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 2000),
    RatBall.ofBounds ((249 : ℚ) / 128000) ((619 : ℚ) / 256000)⟩

private def lowRow0Cell1RootLLLLULLTree : Subdivision :=
.horizontal ((1 : ℚ) / 4000)
  (.vertical ((1117 : ℚ) / 512000)
  (.horizontal ((1 : ℚ) / 8000)
  (.vertical ((2113 : ℚ) / 1024000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.horizontal ((1 : ℚ) / 8000)
  (.vertical ((471 : ℚ) / 204800)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval)))
  (.leaf .interval)

private theorem lowRow0Cell1RootLLLLULLTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell1RootLLLLULLRectangle
      CertificateObjective.endpointExpression lowRow0Cell1RootLLLLULLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell1RootLLLLULL_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 2000))
    (hqLower : ((249 : ℝ) / 128000) ≤ q)
    (hqUpper : q ≤ ((619 : ℝ) / 256000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell1RootLLLLULLRectangle) (tree := lowRow0Cell1RootLLLLULLTree)
  · norm_num [lowRow0Cell1RootLLLLULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLULLRectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell1RootLLLLULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLULLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell1RootLLLLULLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLULLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell1RootLLLLULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell1RootLLLLULLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell1RootLLLLULLTree_certified

private def lowRow0Cell1RootLLLLULURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 2000),
    RatBall.ofBounds ((619 : ℚ) / 256000) ((37 : ℚ) / 12800)⟩

private def lowRow0Cell1RootLLLLULUTree : Subdivision :=
.horizontal ((1 : ℚ) / 4000)
  (.vertical ((1359 : ℚ) / 512000)
  (.horizontal ((1 : ℚ) / 8000)
  (.vertical ((2597 : ℚ) / 1024000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.horizontal ((1 : ℚ) / 8000)
  (.leaf .interval)
  (.leaf .interval)))
  (.leaf .interval)

private theorem lowRow0Cell1RootLLLLULUTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell1RootLLLLULURectangle
      CertificateObjective.endpointExpression lowRow0Cell1RootLLLLULUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell1RootLLLLULU_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 2000))
    (hqLower : ((619 : ℝ) / 256000) ≤ q)
    (hqUpper : q ≤ ((37 : ℝ) / 12800)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell1RootLLLLULURectangle) (tree := lowRow0Cell1RootLLLLULUTree)
  · norm_num [lowRow0Cell1RootLLLLULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLULURectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell1RootLLLLULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLULURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell1RootLLLLULURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLULURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell1RootLLLLULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell1RootLLLLULURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell1RootLLLLULUTree_certified

private def lowRow0Cell1RootLLLLUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 2000) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((249 : ℚ) / 128000) ((37 : ℚ) / 12800)⟩

private def lowRow0Cell1RootLLLLUUTree : Subdivision :=
.leaf .interval

private theorem lowRow0Cell1RootLLLLUUTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell1RootLLLLUURectangle
      CertificateObjective.endpointExpression lowRow0Cell1RootLLLLUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell1RootLLLLUU_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 2000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((249 : ℝ) / 128000) ≤ q)
    (hqUpper : q ≤ ((37 : ℝ) / 12800)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell1RootLLLLUURectangle) (tree := lowRow0Cell1RootLLLLUUTree)
  · norm_num [lowRow0Cell1RootLLLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLUURectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell1RootLLLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell1RootLLLLUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLLUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell1RootLLLLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell1RootLLLLUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell1RootLLLLUUTree_certified

private def lowRow0Cell1RootLLLULRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((37 : ℚ) / 12800) ((491 : ℚ) / 128000)⟩

private def lowRow0Cell1RootLLLULTree : Subdivision :=
.horizontal ((1 : ℚ) / 2000)
  (.vertical ((861 : ℚ) / 256000)
  (.horizontal ((1 : ℚ) / 4000)
  (.vertical ((1601 : ℚ) / 512000)
  (.horizontal ((1 : ℚ) / 8000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((1 : ℚ) / 8000)
  (.leaf .interval)
  (.leaf .interval)))
  (.leaf .interval))
  (.horizontal ((1 : ℚ) / 4000)
  (.vertical ((1843 : ℚ) / 512000)
  (.horizontal ((1 : ℚ) / 8000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((1 : ℚ) / 8000)
  (.leaf .interval)
  (.leaf .interval)))
  (.leaf .interval)))
  (.leaf .interval)

private theorem lowRow0Cell1RootLLLULTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell1RootLLLULRectangle
      CertificateObjective.endpointExpression lowRow0Cell1RootLLLULTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell1RootLLLUL_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((37 : ℝ) / 12800) ≤ q)
    (hqUpper : q ≤ ((491 : ℝ) / 128000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell1RootLLLULRectangle) (tree := lowRow0Cell1RootLLLULTree)
  · norm_num [lowRow0Cell1RootLLLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLULRectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell1RootLLLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLULRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell1RootLLLULRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootLLLULRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell1RootLLLULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell1RootLLLULRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell1RootLLLULTree_certified

end Frankl
