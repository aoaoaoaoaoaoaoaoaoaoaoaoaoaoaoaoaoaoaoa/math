import Frankl.EndpointCertificate

namespace Frankl

private def lowRow2Cell0RootLLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 64) ((5 : ℚ) / 256),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow2Cell0RootLLTree : Subdivision :=
.horizontal ((9 : ℚ) / 512)
  (.horizontal ((17 : ℚ) / 1024)
  (.vertical ((1 : ℚ) / 2000)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 2000)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((19 : ℚ) / 1024)
  (.vertical ((1 : ℚ) / 2000)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((1 : ℚ) / 2000)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow2Cell0RootLLTree_certified :
    certifySubdivision 12 64 32 lowRow2Cell0RootLLRectangle
      CertificateObjective.endpointExpression lowRow2Cell0RootLLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow2Cell0RootLL_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 256))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow2Cell0RootLLRectangle) (tree := lowRow2Cell0RootLLTree)
  · norm_num [lowRow2Cell0RootLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell0RootLLRectangle, RatBall.ofBounds]
  · norm_num [lowRow2Cell0RootLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell0RootLLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow2Cell0RootLLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell0RootLLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow2Cell0RootLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow2Cell0RootLLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow2Cell0RootLLTree_certified

private def lowRow2Cell0RootLURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 256) ((3 : ℚ) / 128),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow2Cell0RootLUTree : Subdivision :=
.horizontal ((11 : ℚ) / 512)
  (.horizontal ((21 : ℚ) / 1024)
  (.vertical ((1 : ℚ) / 2000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.horizontal ((23 : ℚ) / 1024)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow2Cell0RootLUTree_certified :
    certifySubdivision 12 64 32 lowRow2Cell0RootLURectangle
      CertificateObjective.endpointExpression lowRow2Cell0RootLUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow2Cell0RootLU_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 256) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 128))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow2Cell0RootLURectangle) (tree := lowRow2Cell0RootLUTree)
  · norm_num [lowRow2Cell0RootLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell0RootLURectangle, RatBall.ofBounds]
  · norm_num [lowRow2Cell0RootLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell0RootLURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow2Cell0RootLURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell0RootLURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow2Cell0RootLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow2Cell0RootLURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow2Cell0RootLUTree_certified

private def lowRow2Cell0RootURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 128) ((1 : ℚ) / 32),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow2Cell0RootUTree : Subdivision :=
.horizontal ((7 : ℚ) / 256)
  (.horizontal ((13 : ℚ) / 512)
  (.horizontal ((25 : ℚ) / 1024)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((27 : ℚ) / 1024)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((15 : ℚ) / 512)
  (.horizontal ((29 : ℚ) / 1024)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((31 : ℚ) / 1024)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow2Cell0RootUTree_certified :
    certifySubdivision 12 64 32 lowRow2Cell0RootURectangle
      CertificateObjective.endpointExpression lowRow2Cell0RootUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow2Cell0RootU_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 128) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow2Cell0RootURectangle) (tree := lowRow2Cell0RootUTree)
  · norm_num [lowRow2Cell0RootURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell0RootURectangle, RatBall.ofBounds]
  · norm_num [lowRow2Cell0RootURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell0RootURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow2Cell0RootURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell0RootURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow2Cell0RootURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow2Cell0RootURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow2Cell0RootUTree_certified

end Frankl
