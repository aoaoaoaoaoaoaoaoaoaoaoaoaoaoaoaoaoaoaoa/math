import Frankl.EndpointCertificate

namespace Frankl

private def lowRow14Cell9RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((13 : ℚ) / 64) ((7 : ℚ) / 32),
    RatBall.ofBounds ((1 : ℚ) / 4) ((9 : ℚ) / 32)⟩

private def lowRow14Cell9RootTree : Subdivision :=
.horizontal ((27 : ℚ) / 128)
  (.vertical ((17 : ℚ) / 64)
  (.horizontal ((53 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((53 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((17 : ℚ) / 64)
  (.horizontal ((55 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((55 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

set_option maxHeartbeats 1000000 in
-- Kernel normalization of this reflected subdivision exceeds Lean's default heartbeat budget.
private theorem lowRow14Cell9RootTree_certified :
    certifySubdivision 12 64 32 lowRow14Cell9RootRectangle
      CertificateObjective.endpointExpression lowRow14Cell9RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow14Cell9Root_nonneg {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow14Cell9RootRectangle) (tree := lowRow14Cell9RootTree)
  · norm_num [lowRow14Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell9RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow14Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell9RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow14Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell9RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow14Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow14Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow14Cell9RootTree_certified

private def lowRow14Cell10RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((13 : ℚ) / 64) ((7 : ℚ) / 32),
    RatBall.ofBounds ((9 : ℚ) / 32) ((5 : ℚ) / 16)⟩

private def lowRow14Cell10RootTree : Subdivision :=
.horizontal ((27 : ℚ) / 128)
  (.vertical ((19 : ℚ) / 64)
  (.horizontal ((53 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((53 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((19 : ℚ) / 64)
  (.horizontal ((55 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((55 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

set_option maxHeartbeats 1000000 in
-- Kernel normalization of this reflected subdivision exceeds Lean's default heartbeat budget.
private theorem lowRow14Cell10RootTree_certified :
    certifySubdivision 12 64 32 lowRow14Cell10RootRectangle
      CertificateObjective.endpointExpression lowRow14Cell10RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow14Cell10Root_nonneg {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow14Cell10RootRectangle) (tree := lowRow14Cell10RootTree)
  · norm_num [lowRow14Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell10RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow14Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell10RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow14Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell10RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow14Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow14Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow14Cell10RootTree_certified

private def lowRow14Cell11RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((13 : ℚ) / 64) ((7 : ℚ) / 32),
    RatBall.ofBounds ((5 : ℚ) / 16) ((11 : ℚ) / 32)⟩

private def lowRow14Cell11RootTree : Subdivision :=
.horizontal ((27 : ℚ) / 128)
  (.vertical ((21 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((21 : ℚ) / 64)
  (.horizontal ((55 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))

private theorem lowRow14Cell11RootTree_certified :
    certifySubdivision 12 64 32 lowRow14Cell11RootRectangle
      CertificateObjective.endpointExpression lowRow14Cell11RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow14Cell11Root_nonneg {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow14Cell11RootRectangle) (tree := lowRow14Cell11RootTree)
  · norm_num [lowRow14Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell11RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow14Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell11RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow14Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell11RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow14Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow14Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow14Cell11RootTree_certified

private def lowRow14Cell12RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((13 : ℚ) / 64) ((7 : ℚ) / 32),
    RatBall.ofBounds ((11 : ℚ) / 32) ((3 : ℚ) / 8)⟩

private def lowRow14Cell12RootTree : Subdivision :=
.horizontal ((27 : ℚ) / 128)
  (.vertical ((23 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((23 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow14Cell12RootTree_certified :
    certifySubdivision 12 64 32 lowRow14Cell12RootRectangle
      CertificateObjective.endpointExpression lowRow14Cell12RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow14Cell12Root_nonneg {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow14Cell12RootRectangle) (tree := lowRow14Cell12RootTree)
  · norm_num [lowRow14Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell12RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow14Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell12RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow14Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell12RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow14Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow14Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow14Cell12RootTree_certified

end Frankl
