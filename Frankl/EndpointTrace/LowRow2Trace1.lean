import Frankl.EndpointCertificate

namespace Frankl

private def lowRow2Cell1RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 64) ((1 : ℚ) / 32),
    RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 32)⟩

private def lowRow2Cell1RootTree : Subdivision :=
.vertical ((129 : ℚ) / 8000)
  (.vertical ((137 : ℚ) / 16000)
  (.horizontal ((3 : ℚ) / 128)
  (.vertical ((153 : ℚ) / 32000)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((153 : ℚ) / 32000)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((3 : ℚ) / 128)
  (.horizontal ((5 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval)))
  (.horizontal ((3 : ℚ) / 128)
  (.vertical ((379 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((379 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval)))

set_option maxHeartbeats 1000000 in
-- Kernel normalization of this reflected subdivision exceeds Lean's default heartbeat budget.
private theorem lowRow2Cell1RootTree_certified :
    certifySubdivision 12 64 32 lowRow2Cell1RootRectangle
      CertificateObjective.endpointExpression lowRow2Cell1RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow2Cell1Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow2Cell1RootRectangle) (tree := lowRow2Cell1RootTree)
  · norm_num [lowRow2Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell1RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow2Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell1RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow2Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell1RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow2Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow2Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow2Cell1RootTree_certified

private def lowRow2Cell2RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 64) ((1 : ℚ) / 32),
    RatBall.ofBounds ((1 : ℚ) / 32) ((1 : ℚ) / 16)⟩

private def lowRow2Cell2RootTree : Subdivision :=
.vertical ((3 : ℚ) / 64)
  (.horizontal ((3 : ℚ) / 128)
  (.vertical ((5 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((5 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((3 : ℚ) / 128)
  (.vertical ((7 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))

set_option maxHeartbeats 1000000 in
-- Kernel normalization of this reflected subdivision exceeds Lean's default heartbeat budget.
private theorem lowRow2Cell2RootTree_certified :
    certifySubdivision 12 64 32 lowRow2Cell2RootRectangle
      CertificateObjective.endpointExpression lowRow2Cell2RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow2Cell2Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow2Cell2RootRectangle) (tree := lowRow2Cell2RootTree)
  · norm_num [lowRow2Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell2RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow2Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell2RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow2Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell2RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow2Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow2Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow2Cell2RootTree_certified

private def lowRow2Cell3RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 64) ((1 : ℚ) / 32),
    RatBall.ofBounds ((1 : ℚ) / 16) ((3 : ℚ) / 32)⟩

private def lowRow2Cell3RootTree : Subdivision :=
.vertical ((5 : ℚ) / 64)
  (.horizontal ((3 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((3 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow2Cell3RootTree_certified :
    certifySubdivision 12 64 32 lowRow2Cell3RootRectangle
      CertificateObjective.endpointExpression lowRow2Cell3RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow2Cell3Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow2Cell3RootRectangle) (tree := lowRow2Cell3RootTree)
  · norm_num [lowRow2Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell3RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow2Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell3RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow2Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell3RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow2Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow2Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow2Cell3RootTree_certified

private def lowRow2Cell4RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 64) ((1 : ℚ) / 32),
    RatBall.ofBounds ((3 : ℚ) / 32) ((1 : ℚ) / 8)⟩

private def lowRow2Cell4RootTree : Subdivision :=
.horizontal ((3 : ℚ) / 128)
  (.vertical ((7 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((7 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow2Cell4RootTree_certified :
    certifySubdivision 12 64 32 lowRow2Cell4RootRectangle
      CertificateObjective.endpointExpression lowRow2Cell4RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow2Cell4Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow2Cell4RootRectangle) (tree := lowRow2Cell4RootTree)
  · norm_num [lowRow2Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell4RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow2Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell4RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow2Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell4RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow2Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow2Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow2Cell4RootTree_certified

private def lowRow2Cell5RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 64) ((1 : ℚ) / 32),
    RatBall.ofBounds ((1 : ℚ) / 8) ((5 : ℚ) / 32)⟩

private def lowRow2Cell5RootTree : Subdivision :=
.horizontal ((3 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow2Cell5RootTree_certified :
    certifySubdivision 12 64 32 lowRow2Cell5RootRectangle
      CertificateObjective.endpointExpression lowRow2Cell5RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow2Cell5Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow2Cell5RootRectangle) (tree := lowRow2Cell5RootTree)
  · norm_num [lowRow2Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell5RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow2Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell5RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow2Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell5RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow2Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow2Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow2Cell5RootTree_certified

end Frankl
