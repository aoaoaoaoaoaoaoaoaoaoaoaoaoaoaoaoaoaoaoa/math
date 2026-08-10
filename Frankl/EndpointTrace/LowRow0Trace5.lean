import Frankl.EndpointCertificate

namespace Frankl

private def lowRow0Cell1RootUURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((379 : ℚ) / 16000) ((1 : ℚ) / 32)⟩

private def lowRow0Cell1RootUUTree : Subdivision :=
.vertical ((879 : ℚ) / 32000)
  (.vertical ((1637 : ℚ) / 64000)
  (.vertical ((3153 : ℚ) / 128000)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((679 : ℚ) / 25600)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((1879 : ℚ) / 64000)
  (.vertical ((3637 : ℚ) / 128000)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((3879 : ℚ) / 128000)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow0Cell1RootUUTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell1RootUURectangle
      CertificateObjective.endpointExpression lowRow0Cell1RootUUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell1RootUU_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((379 : ℝ) / 16000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell1RootUURectangle) (tree := lowRow0Cell1RootUUTree)
  · norm_num [lowRow0Cell1RootUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootUURectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell1RootUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootUURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell1RootUURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell1RootUURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell1RootUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell1RootUURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell1RootUUTree_certified

private def lowRow0Cell2RootLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((1 : ℚ) / 32) ((3 : ℚ) / 64)⟩

private def lowRow0Cell2RootLTree : Subdivision :=
.vertical ((5 : ℚ) / 128)
  (.vertical ((9 : ℚ) / 256)
  (.vertical ((17 : ℚ) / 512)
  (.vertical ((33 : ℚ) / 1024)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((35 : ℚ) / 1024)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((19 : ℚ) / 512)
  (.vertical ((37 : ℚ) / 1024)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval)))
  (.vertical ((11 : ℚ) / 256)
  (.vertical ((21 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((23 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow0Cell2RootLTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell2RootLRectangle
      CertificateObjective.endpointExpression lowRow0Cell2RootLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell2RootL_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 64)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell2RootLRectangle) (tree := lowRow0Cell2RootLTree)
  · norm_num [lowRow0Cell2RootLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell2RootLRectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell2RootLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell2RootLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell2RootLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell2RootLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell2RootLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell2RootLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell2RootLTree_certified

private def lowRow0Cell2RootURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((3 : ℚ) / 64) ((1 : ℚ) / 16)⟩

private def lowRow0Cell2RootUTree : Subdivision :=
.vertical ((7 : ℚ) / 128)
  (.vertical ((13 : ℚ) / 256)
  (.vertical ((25 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((27 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((15 : ℚ) / 256)
  (.vertical ((29 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((31 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow0Cell2RootUTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell2RootURectangle
      CertificateObjective.endpointExpression lowRow0Cell2RootUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell2RootU_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((3 : ℝ) / 64) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell2RootURectangle) (tree := lowRow0Cell2RootUTree)
  · norm_num [lowRow0Cell2RootURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell2RootURectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell2RootURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell2RootURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell2RootURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell2RootURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell2RootURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell2RootURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell2RootUTree_certified

end Frankl
