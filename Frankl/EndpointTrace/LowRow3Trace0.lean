import Frankl.EndpointCertificate

namespace Frankl

private def lowRow3Cell0RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 32) ((3 : ℚ) / 64),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow3Cell0RootTree : Subdivision :=
.horizontal ((5 : ℚ) / 128)
  (.horizontal ((9 : ℚ) / 256)
  (.horizontal ((17 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((19 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((11 : ℚ) / 256)
  (.horizontal ((21 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((23 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow3Cell0RootTree_certified :
    certifySubdivision 12 64 32 lowRow3Cell0RootRectangle
      CertificateObjective.endpointExpression lowRow3Cell0RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow3Cell0Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow3Cell0RootRectangle) (tree := lowRow3Cell0RootTree)
  · norm_num [lowRow3Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell0RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow3Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell0RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow3Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell0RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow3Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow3Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow3Cell0RootTree_certified

private def lowRow3Cell1RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 32) ((3 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 32)⟩

private def lowRow3Cell1RootTree : Subdivision :=
.vertical ((129 : ℚ) / 8000)
  (.vertical ((137 : ℚ) / 16000)
  (.horizontal ((5 : ℚ) / 128)
  (.vertical ((153 : ℚ) / 32000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.horizontal ((5 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((5 : ℚ) / 128)
  (.vertical ((379 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((379 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval)))

set_option maxHeartbeats 1000000 in
-- Kernel normalization of this reflected subdivision exceeds Lean's default heartbeat budget.
private theorem lowRow3Cell1RootTree_certified :
    certifySubdivision 12 64 32 lowRow3Cell1RootRectangle
      CertificateObjective.endpointExpression lowRow3Cell1RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow3Cell1Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow3Cell1RootRectangle) (tree := lowRow3Cell1RootTree)
  · norm_num [lowRow3Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell1RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow3Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell1RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow3Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell1RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow3Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow3Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow3Cell1RootTree_certified

private def lowRow3Cell2RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 32) ((3 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 32) ((1 : ℚ) / 16)⟩

private def lowRow3Cell2RootTree : Subdivision :=
.vertical ((3 : ℚ) / 64)
  (.horizontal ((5 : ℚ) / 128)
  (.vertical ((5 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((5 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((5 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow3Cell2RootTree_certified :
    certifySubdivision 12 64 32 lowRow3Cell2RootRectangle
      CertificateObjective.endpointExpression lowRow3Cell2RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow3Cell2Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow3Cell2RootRectangle) (tree := lowRow3Cell2RootTree)
  · norm_num [lowRow3Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell2RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow3Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell2RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow3Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell2RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow3Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow3Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow3Cell2RootTree_certified

private def lowRow3Cell3RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 32) ((3 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 16) ((3 : ℚ) / 32)⟩

private def lowRow3Cell3RootTree : Subdivision :=
.vertical ((5 : ℚ) / 64)
  (.horizontal ((5 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((5 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow3Cell3RootTree_certified :
    certifySubdivision 12 64 32 lowRow3Cell3RootRectangle
      CertificateObjective.endpointExpression lowRow3Cell3RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow3Cell3Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow3Cell3RootRectangle) (tree := lowRow3Cell3RootTree)
  · norm_num [lowRow3Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell3RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow3Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell3RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow3Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell3RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow3Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow3Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow3Cell3RootTree_certified

end Frankl
