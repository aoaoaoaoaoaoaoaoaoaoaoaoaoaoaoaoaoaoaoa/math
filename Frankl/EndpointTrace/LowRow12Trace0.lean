import Frankl.EndpointCertificate

namespace Frankl

private def lowRow12Cell0RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((11 : ℚ) / 64) ((3 : ℚ) / 16),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow12Cell0RootTree : Subdivision :=
.horizontal ((23 : ℚ) / 128)
  (.horizontal ((45 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((47 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow12Cell0RootTree_certified :
    certifySubdivision 12 64 32 lowRow12Cell0RootRectangle
      CertificateObjective.endpointExpression lowRow12Cell0RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow12Cell0Root_nonneg {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow12Cell0RootRectangle) (tree := lowRow12Cell0RootTree)
  · norm_num [lowRow12Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell0RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow12Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell0RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow12Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell0RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow12Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow12Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow12Cell0RootTree_certified

private def lowRow12Cell1RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((11 : ℚ) / 64) ((3 : ℚ) / 16),
    RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 32)⟩

private def lowRow12Cell1RootTree : Subdivision :=
.vertical ((129 : ℚ) / 8000)
  (.vertical ((137 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((23 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow12Cell1RootTree_certified :
    certifySubdivision 12 64 32 lowRow12Cell1RootRectangle
      CertificateObjective.endpointExpression lowRow12Cell1RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow12Cell1Root_nonneg {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow12Cell1RootRectangle) (tree := lowRow12Cell1RootTree)
  · norm_num [lowRow12Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell1RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow12Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell1RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow12Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell1RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow12Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow12Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow12Cell1RootTree_certified

private def lowRow12Cell2RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((11 : ℚ) / 64) ((3 : ℚ) / 16),
    RatBall.ofBounds ((1 : ℚ) / 32) ((1 : ℚ) / 16)⟩

private def lowRow12Cell2RootTree : Subdivision :=
.vertical ((3 : ℚ) / 64)
  (.horizontal ((23 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((23 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow12Cell2RootTree_certified :
    certifySubdivision 12 64 32 lowRow12Cell2RootRectangle
      CertificateObjective.endpointExpression lowRow12Cell2RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow12Cell2Root_nonneg {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow12Cell2RootRectangle) (tree := lowRow12Cell2RootTree)
  · norm_num [lowRow12Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell2RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow12Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell2RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow12Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell2RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow12Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow12Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow12Cell2RootTree_certified

private def lowRow12Cell3RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((11 : ℚ) / 64) ((3 : ℚ) / 16),
    RatBall.ofBounds ((1 : ℚ) / 16) ((3 : ℚ) / 32)⟩

private def lowRow12Cell3RootTree : Subdivision :=
.vertical ((5 : ℚ) / 64)
  (.horizontal ((23 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((23 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow12Cell3RootTree_certified :
    certifySubdivision 12 64 32 lowRow12Cell3RootRectangle
      CertificateObjective.endpointExpression lowRow12Cell3RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow12Cell3Root_nonneg {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow12Cell3RootRectangle) (tree := lowRow12Cell3RootTree)
  · norm_num [lowRow12Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell3RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow12Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell3RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow12Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell3RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow12Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow12Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow12Cell3RootTree_certified

private def lowRow12Cell4RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((11 : ℚ) / 64) ((3 : ℚ) / 16),
    RatBall.ofBounds ((3 : ℚ) / 32) ((1 : ℚ) / 8)⟩

private def lowRow12Cell4RootTree : Subdivision :=
.vertical ((7 : ℚ) / 64)
  (.horizontal ((23 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((23 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow12Cell4RootTree_certified :
    certifySubdivision 12 64 32 lowRow12Cell4RootRectangle
      CertificateObjective.endpointExpression lowRow12Cell4RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow12Cell4Root_nonneg {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow12Cell4RootRectangle) (tree := lowRow12Cell4RootTree)
  · norm_num [lowRow12Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell4RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow12Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell4RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow12Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell4RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow12Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow12Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow12Cell4RootTree_certified

private def lowRow12Cell5RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((11 : ℚ) / 64) ((3 : ℚ) / 16),
    RatBall.ofBounds ((1 : ℚ) / 8) ((5 : ℚ) / 32)⟩

private def lowRow12Cell5RootTree : Subdivision :=
.horizontal ((23 : ℚ) / 128)
  (.vertical ((9 : ℚ) / 64)
  (.leaf .interval)
  (.vertical ((19 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((9 : ℚ) / 64)
  (.vertical ((17 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((47 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

set_option maxHeartbeats 1000000 in
-- Kernel normalization of this reflected subdivision exceeds Lean's default heartbeat budget.
private theorem lowRow12Cell5RootTree_certified :
    certifySubdivision 12 64 32 lowRow12Cell5RootRectangle
      CertificateObjective.endpointExpression lowRow12Cell5RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow12Cell5Root_nonneg {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow12Cell5RootRectangle) (tree := lowRow12Cell5RootTree)
  · norm_num [lowRow12Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell5RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow12Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell5RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow12Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell5RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow12Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow12Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow12Cell5RootTree_certified

end Frankl
