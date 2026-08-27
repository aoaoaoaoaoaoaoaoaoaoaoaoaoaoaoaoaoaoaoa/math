import Frankl.EndpointCertificate

namespace Frankl

private def lowRow13Cell0RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 16) ((13 : ℚ) / 64),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow13Cell0RootTree : Subdivision :=
.horizontal ((25 : ℚ) / 128)
  (.horizontal ((49 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((51 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow13Cell0RootTree_certified :
    certifySubdivision 12 64 32 lowRow13Cell0RootRectangle
      CertificateObjective.endpointExpression lowRow13Cell0RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow13Cell0Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow13Cell0RootRectangle) (tree := lowRow13Cell0RootTree)
  · norm_num [lowRow13Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell0RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow13Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell0RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow13Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell0RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow13Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow13Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow13Cell0RootTree_certified

private def lowRow13Cell1RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 16) ((13 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 32)⟩

private def lowRow13Cell1RootTree : Subdivision :=
.vertical ((129 : ℚ) / 8000)
  (.vertical ((137 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((25 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow13Cell1RootTree_certified :
    certifySubdivision 12 64 32 lowRow13Cell1RootRectangle
      CertificateObjective.endpointExpression lowRow13Cell1RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow13Cell1Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow13Cell1RootRectangle) (tree := lowRow13Cell1RootTree)
  · norm_num [lowRow13Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell1RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow13Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell1RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow13Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell1RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow13Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow13Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow13Cell1RootTree_certified

private def lowRow13Cell2RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 16) ((13 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 32) ((1 : ℚ) / 16)⟩

private def lowRow13Cell2RootTree : Subdivision :=
.vertical ((3 : ℚ) / 64)
  (.horizontal ((25 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((25 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow13Cell2RootTree_certified :
    certifySubdivision 12 64 32 lowRow13Cell2RootRectangle
      CertificateObjective.endpointExpression lowRow13Cell2RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow13Cell2Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow13Cell2RootRectangle) (tree := lowRow13Cell2RootTree)
  · norm_num [lowRow13Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell2RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow13Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell2RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow13Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell2RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow13Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow13Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow13Cell2RootTree_certified

private def lowRow13Cell3RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 16) ((13 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 16) ((3 : ℚ) / 32)⟩

private def lowRow13Cell3RootTree : Subdivision :=
.vertical ((5 : ℚ) / 64)
  (.horizontal ((25 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((25 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow13Cell3RootTree_certified :
    certifySubdivision 12 64 32 lowRow13Cell3RootRectangle
      CertificateObjective.endpointExpression lowRow13Cell3RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow13Cell3Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow13Cell3RootRectangle) (tree := lowRow13Cell3RootTree)
  · norm_num [lowRow13Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell3RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow13Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell3RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow13Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell3RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow13Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow13Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow13Cell3RootTree_certified

private def lowRow13Cell4RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 16) ((13 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 32) ((1 : ℚ) / 8)⟩

private def lowRow13Cell4RootTree : Subdivision :=
.vertical ((7 : ℚ) / 64)
  (.horizontal ((25 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((25 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow13Cell4RootTree_certified :
    certifySubdivision 12 64 32 lowRow13Cell4RootRectangle
      CertificateObjective.endpointExpression lowRow13Cell4RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow13Cell4Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow13Cell4RootRectangle) (tree := lowRow13Cell4RootTree)
  · norm_num [lowRow13Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell4RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow13Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell4RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow13Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell4RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow13Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow13Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow13Cell4RootTree_certified

private def lowRow13Cell5RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 16) ((13 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 8) ((5 : ℚ) / 32)⟩

private def lowRow13Cell5RootTree : Subdivision :=
.horizontal ((25 : ℚ) / 128)
  (.vertical ((9 : ℚ) / 64)
  (.vertical ((17 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((49 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((9 : ℚ) / 64)
  (.vertical ((17 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((51 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

set_option maxHeartbeats 1000000 in
-- Kernel normalization of this reflected subdivision exceeds Lean's default heartbeat budget.
private theorem lowRow13Cell5RootTree_certified :
    certifySubdivision 12 64 32 lowRow13Cell5RootRectangle
      CertificateObjective.endpointExpression lowRow13Cell5RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow13Cell5Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow13Cell5RootRectangle) (tree := lowRow13Cell5RootTree)
  · norm_num [lowRow13Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell5RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow13Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell5RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow13Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell5RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow13Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow13Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow13Cell5RootTree_certified

end Frankl
