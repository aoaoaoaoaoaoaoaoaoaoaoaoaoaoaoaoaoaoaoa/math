import Frankl.EndpointCertificate

namespace Frankl

private def lowRow12Cell6RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((11 : ℚ) / 64) ((3 : ℚ) / 16),
    RatBall.ofBounds ((5 : ℚ) / 32) ((3 : ℚ) / 16)⟩

private def lowRow12Cell6RootTree : Subdivision :=
.horizontal ((23 : ℚ) / 128)
  (.vertical ((11 : ℚ) / 64)
  (.horizontal ((45 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((45 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((11 : ℚ) / 64)
  (.horizontal ((47 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((47 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow12Cell6RootTree_certified :
    certifySubdivision 12 64 32 lowRow12Cell6RootRectangle
      CertificateObjective.endpointExpression lowRow12Cell6RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow12Cell6Root_nonneg {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow12Cell6RootRectangle) (tree := lowRow12Cell6RootTree)
  · norm_num [lowRow12Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell6RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow12Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell6RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow12Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell6RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow12Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow12Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow12Cell6RootTree_certified

private def lowRow12Cell7RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((11 : ℚ) / 64) ((3 : ℚ) / 16),
    RatBall.ofBounds ((3 : ℚ) / 16) ((7 : ℚ) / 32)⟩

private def lowRow12Cell7RootTree : Subdivision :=
.horizontal ((23 : ℚ) / 128)
  (.vertical ((13 : ℚ) / 64)
  (.horizontal ((45 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((45 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((13 : ℚ) / 64)
  (.horizontal ((47 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((47 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow12Cell7RootTree_certified :
    certifySubdivision 12 64 32 lowRow12Cell7RootRectangle
      CertificateObjective.endpointExpression lowRow12Cell7RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow12Cell7Root_nonneg {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow12Cell7RootRectangle) (tree := lowRow12Cell7RootTree)
  · norm_num [lowRow12Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell7RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow12Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell7RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow12Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell7RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow12Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow12Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow12Cell7RootTree_certified

private def lowRow12Cell8RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((11 : ℚ) / 64) ((3 : ℚ) / 16),
    RatBall.ofBounds ((7 : ℚ) / 32) ((1 : ℚ) / 4)⟩

private def lowRow12Cell8RootTree : Subdivision :=
.horizontal ((23 : ℚ) / 128)
  (.vertical ((15 : ℚ) / 64)
  (.horizontal ((45 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((45 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((15 : ℚ) / 64)
  (.horizontal ((47 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((47 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow12Cell8RootTree_certified :
    certifySubdivision 12 64 32 lowRow12Cell8RootRectangle
      CertificateObjective.endpointExpression lowRow12Cell8RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow12Cell8Root_nonneg {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow12Cell8RootRectangle) (tree := lowRow12Cell8RootTree)
  · norm_num [lowRow12Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell8RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow12Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell8RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow12Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell8RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow12Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow12Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow12Cell8RootTree_certified

end Frankl
