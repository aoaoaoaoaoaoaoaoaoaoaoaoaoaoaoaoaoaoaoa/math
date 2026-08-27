import Frankl.EndpointCertificate

namespace Frankl

private def lowRow15Cell9RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 32) ((15 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 4) ((9 : ℚ) / 32)⟩

private def lowRow15Cell9RootTree : Subdivision :=
.horizontal ((29 : ℚ) / 128)
  (.vertical ((17 : ℚ) / 64)
  (.horizontal ((57 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((57 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((17 : ℚ) / 64)
  (.horizontal ((59 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((59 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

set_option maxHeartbeats 1000000 in
-- Kernel normalization of this reflected subdivision exceeds Lean's default heartbeat budget.
private theorem lowRow15Cell9RootTree_certified :
    certifySubdivision 12 64 32 lowRow15Cell9RootRectangle
      CertificateObjective.endpointExpression lowRow15Cell9RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow15Cell9Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow15Cell9RootRectangle) (tree := lowRow15Cell9RootTree)
  · norm_num [lowRow15Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell9RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow15Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell9RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow15Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell9RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow15Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow15Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow15Cell9RootTree_certified

private def lowRow15Cell10RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 32) ((15 : ℚ) / 64),
    RatBall.ofBounds ((9 : ℚ) / 32) ((5 : ℚ) / 16)⟩

private def lowRow15Cell10RootTree : Subdivision :=
.horizontal ((29 : ℚ) / 128)
  (.vertical ((19 : ℚ) / 64)
  (.horizontal ((57 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((57 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((19 : ℚ) / 64)
  (.horizontal ((59 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((59 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

set_option maxHeartbeats 1000000 in
-- Kernel normalization of this reflected subdivision exceeds Lean's default heartbeat budget.
private theorem lowRow15Cell10RootTree_certified :
    certifySubdivision 12 64 32 lowRow15Cell10RootRectangle
      CertificateObjective.endpointExpression lowRow15Cell10RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow15Cell10Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow15Cell10RootRectangle) (tree := lowRow15Cell10RootTree)
  · norm_num [lowRow15Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell10RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow15Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell10RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow15Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell10RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow15Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow15Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow15Cell10RootTree_certified

private def lowRow15Cell11RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 32) ((15 : ℚ) / 64),
    RatBall.ofBounds ((5 : ℚ) / 16) ((11 : ℚ) / 32)⟩

private def lowRow15Cell11RootTree : Subdivision :=
.horizontal ((29 : ℚ) / 128)
  (.vertical ((21 : ℚ) / 64)
  (.horizontal ((57 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((57 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((21 : ℚ) / 64)
  (.horizontal ((59 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((59 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

set_option maxHeartbeats 1000000 in
-- Kernel normalization of this reflected subdivision exceeds Lean's default heartbeat budget.
private theorem lowRow15Cell11RootTree_certified :
    certifySubdivision 12 64 32 lowRow15Cell11RootRectangle
      CertificateObjective.endpointExpression lowRow15Cell11RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow15Cell11Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow15Cell11RootRectangle) (tree := lowRow15Cell11RootTree)
  · norm_num [lowRow15Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell11RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow15Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell11RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow15Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell11RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow15Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow15Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow15Cell11RootTree_certified

end Frankl
