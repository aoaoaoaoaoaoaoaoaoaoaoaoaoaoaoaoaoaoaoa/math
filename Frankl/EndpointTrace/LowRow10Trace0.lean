import Frankl.EndpointCertificate

namespace Frankl

private def lowRow10Cell0RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((9 : ℚ) / 64) ((5 : ℚ) / 32),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow10Cell0RootTree : Subdivision :=
.horizontal ((19 : ℚ) / 128)
  (.horizontal ((37 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((39 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow10Cell0RootTree_certified :
    certifySubdivision 12 64 32 lowRow10Cell0RootRectangle
      CertificateObjective.endpointExpression lowRow10Cell0RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow10Cell0Root_nonneg {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow10Cell0RootRectangle) (tree := lowRow10Cell0RootTree)
  · norm_num [lowRow10Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell0RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow10Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell0RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow10Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell0RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow10Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow10Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow10Cell0RootTree_certified

private def lowRow10Cell1RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((9 : ℚ) / 64) ((5 : ℚ) / 32),
    RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 32)⟩

private def lowRow10Cell1RootTree : Subdivision :=
.vertical ((129 : ℚ) / 8000)
  (.vertical ((137 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((19 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow10Cell1RootTree_certified :
    certifySubdivision 12 64 32 lowRow10Cell1RootRectangle
      CertificateObjective.endpointExpression lowRow10Cell1RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow10Cell1Root_nonneg {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow10Cell1RootRectangle) (tree := lowRow10Cell1RootTree)
  · norm_num [lowRow10Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell1RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow10Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell1RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow10Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell1RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow10Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow10Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow10Cell1RootTree_certified

private def lowRow10Cell2RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((9 : ℚ) / 64) ((5 : ℚ) / 32),
    RatBall.ofBounds ((1 : ℚ) / 32) ((1 : ℚ) / 16)⟩

private def lowRow10Cell2RootTree : Subdivision :=
.vertical ((3 : ℚ) / 64)
  (.horizontal ((19 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((19 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow10Cell2RootTree_certified :
    certifySubdivision 12 64 32 lowRow10Cell2RootRectangle
      CertificateObjective.endpointExpression lowRow10Cell2RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow10Cell2Root_nonneg {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow10Cell2RootRectangle) (tree := lowRow10Cell2RootTree)
  · norm_num [lowRow10Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell2RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow10Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell2RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow10Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell2RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow10Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow10Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow10Cell2RootTree_certified

private def lowRow10Cell3RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((9 : ℚ) / 64) ((5 : ℚ) / 32),
    RatBall.ofBounds ((1 : ℚ) / 16) ((3 : ℚ) / 32)⟩

private def lowRow10Cell3RootTree : Subdivision :=
.vertical ((5 : ℚ) / 64)
  (.horizontal ((19 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((19 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow10Cell3RootTree_certified :
    certifySubdivision 12 64 32 lowRow10Cell3RootRectangle
      CertificateObjective.endpointExpression lowRow10Cell3RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow10Cell3Root_nonneg {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow10Cell3RootRectangle) (tree := lowRow10Cell3RootTree)
  · norm_num [lowRow10Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell3RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow10Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell3RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow10Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell3RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow10Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow10Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow10Cell3RootTree_certified

private def lowRow10Cell4RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((9 : ℚ) / 64) ((5 : ℚ) / 32),
    RatBall.ofBounds ((3 : ℚ) / 32) ((1 : ℚ) / 8)⟩

private def lowRow10Cell4RootTree : Subdivision :=
.vertical ((7 : ℚ) / 64)
  (.horizontal ((19 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((19 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow10Cell4RootTree_certified :
    certifySubdivision 12 64 32 lowRow10Cell4RootRectangle
      CertificateObjective.endpointExpression lowRow10Cell4RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow10Cell4Root_nonneg {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow10Cell4RootRectangle) (tree := lowRow10Cell4RootTree)
  · norm_num [lowRow10Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell4RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow10Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell4RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow10Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell4RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow10Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow10Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow10Cell4RootTree_certified

private def lowRow10Cell5RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((9 : ℚ) / 64) ((5 : ℚ) / 32),
    RatBall.ofBounds ((1 : ℚ) / 8) ((5 : ℚ) / 32)⟩

private def lowRow10Cell5RootTree : Subdivision :=
.vertical ((9 : ℚ) / 64)
  (.horizontal ((19 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((19 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow10Cell5RootTree_certified :
    certifySubdivision 12 64 32 lowRow10Cell5RootRectangle
      CertificateObjective.endpointExpression lowRow10Cell5RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow10Cell5Root_nonneg {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow10Cell5RootRectangle) (tree := lowRow10Cell5RootTree)
  · norm_num [lowRow10Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell5RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow10Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell5RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow10Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell5RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow10Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow10Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow10Cell5RootTree_certified

end Frankl
