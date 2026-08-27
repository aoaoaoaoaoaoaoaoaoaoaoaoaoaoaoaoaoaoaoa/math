import Frankl.EndpointCertificate

namespace Frankl

private def lowRow14Cell6RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((13 : ℚ) / 64) ((7 : ℚ) / 32),
    RatBall.ofBounds ((5 : ℚ) / 32) ((3 : ℚ) / 16)⟩

private def lowRow14Cell6RootTree : Subdivision :=
.horizontal ((27 : ℚ) / 128)
  (.vertical ((11 : ℚ) / 64)
  (.horizontal ((53 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((53 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((11 : ℚ) / 64)
  (.horizontal ((55 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((55 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

set_option maxHeartbeats 1000000 in
-- Kernel normalization of this reflected subdivision exceeds Lean's default heartbeat budget.
private theorem lowRow14Cell6RootTree_certified :
    certifySubdivision 12 64 32 lowRow14Cell6RootRectangle
      CertificateObjective.endpointExpression lowRow14Cell6RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow14Cell6Root_nonneg {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow14Cell6RootRectangle) (tree := lowRow14Cell6RootTree)
  · norm_num [lowRow14Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell6RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow14Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell6RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow14Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell6RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow14Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow14Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow14Cell6RootTree_certified

private def lowRow14Cell7RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((13 : ℚ) / 64) ((7 : ℚ) / 32),
    RatBall.ofBounds ((3 : ℚ) / 16) ((7 : ℚ) / 32)⟩

private def lowRow14Cell7RootTree : Subdivision :=
.horizontal ((27 : ℚ) / 128)
  (.vertical ((13 : ℚ) / 64)
  (.horizontal ((53 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((53 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((13 : ℚ) / 64)
  (.horizontal ((55 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((55 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

set_option maxHeartbeats 1000000 in
-- Kernel normalization of this reflected subdivision exceeds Lean's default heartbeat budget.
private theorem lowRow14Cell7RootTree_certified :
    certifySubdivision 12 64 32 lowRow14Cell7RootRectangle
      CertificateObjective.endpointExpression lowRow14Cell7RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow14Cell7Root_nonneg {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow14Cell7RootRectangle) (tree := lowRow14Cell7RootTree)
  · norm_num [lowRow14Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell7RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow14Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell7RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow14Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell7RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow14Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow14Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow14Cell7RootTree_certified

private def lowRow14Cell8RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((13 : ℚ) / 64) ((7 : ℚ) / 32),
    RatBall.ofBounds ((7 : ℚ) / 32) ((1 : ℚ) / 4)⟩

private def lowRow14Cell8RootTree : Subdivision :=
.horizontal ((27 : ℚ) / 128)
  (.vertical ((15 : ℚ) / 64)
  (.horizontal ((53 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((53 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((15 : ℚ) / 64)
  (.horizontal ((55 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((55 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

set_option maxHeartbeats 1000000 in
-- Kernel normalization of this reflected subdivision exceeds Lean's default heartbeat budget.
private theorem lowRow14Cell8RootTree_certified :
    certifySubdivision 12 64 32 lowRow14Cell8RootRectangle
      CertificateObjective.endpointExpression lowRow14Cell8RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow14Cell8Root_nonneg {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow14Cell8RootRectangle) (tree := lowRow14Cell8RootTree)
  · norm_num [lowRow14Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell8RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow14Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell8RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow14Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell8RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow14Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow14Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow14Cell8RootTree_certified

end Frankl
