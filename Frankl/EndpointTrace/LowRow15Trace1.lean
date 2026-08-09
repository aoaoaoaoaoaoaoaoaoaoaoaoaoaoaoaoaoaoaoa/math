import Frankl.EndpointCertificate

namespace Frankl

private def lowRow15Cell6RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 32) ((15 : ℚ) / 64),
    RatBall.ofBounds ((5 : ℚ) / 32) ((3 : ℚ) / 16)⟩

private def lowRow15Cell6RootTree : Subdivision :=
.horizontal ((29 : ℚ) / 128)
  (.vertical ((11 : ℚ) / 64)
  (.horizontal ((57 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((57 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((11 : ℚ) / 64)
  (.horizontal ((59 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((59 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow15Cell6RootTree_certified :
    certifySubdivision 12 64 32 lowRow15Cell6RootRectangle
      CertificateObjective.endpointExpression lowRow15Cell6RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow15Cell6Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow15Cell6RootRectangle) (tree := lowRow15Cell6RootTree)
  · norm_num [lowRow15Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell6RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow15Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell6RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow15Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell6RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow15Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow15Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow15Cell6RootTree_certified

private def lowRow15Cell7RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 32) ((15 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 16) ((7 : ℚ) / 32)⟩

private def lowRow15Cell7RootTree : Subdivision :=
.horizontal ((29 : ℚ) / 128)
  (.vertical ((13 : ℚ) / 64)
  (.horizontal ((57 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((57 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((13 : ℚ) / 64)
  (.horizontal ((59 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((59 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow15Cell7RootTree_certified :
    certifySubdivision 12 64 32 lowRow15Cell7RootRectangle
      CertificateObjective.endpointExpression lowRow15Cell7RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow15Cell7Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow15Cell7RootRectangle) (tree := lowRow15Cell7RootTree)
  · norm_num [lowRow15Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell7RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow15Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell7RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow15Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell7RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow15Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow15Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow15Cell7RootTree_certified

private def lowRow15Cell8RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 32) ((15 : ℚ) / 64),
    RatBall.ofBounds ((7 : ℚ) / 32) ((1 : ℚ) / 4)⟩

private def lowRow15Cell8RootTree : Subdivision :=
.horizontal ((29 : ℚ) / 128)
  (.vertical ((15 : ℚ) / 64)
  (.horizontal ((57 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((57 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((15 : ℚ) / 64)
  (.horizontal ((59 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((59 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow15Cell8RootTree_certified :
    certifySubdivision 12 64 32 lowRow15Cell8RootRectangle
      CertificateObjective.endpointExpression lowRow15Cell8RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow15Cell8Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow15Cell8RootRectangle) (tree := lowRow15Cell8RootTree)
  · norm_num [lowRow15Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell8RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow15Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell8RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow15Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell8RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow15Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow15Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow15Cell8RootTree_certified

end Frankl
