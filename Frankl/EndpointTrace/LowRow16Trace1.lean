import Frankl.EndpointCertificate

namespace Frankl

private def lowRow16Cell6RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((15 : ℚ) / 64) ((1 : ℚ) / 4),
    RatBall.ofBounds ((5 : ℚ) / 32) ((3 : ℚ) / 16)⟩

private def lowRow16Cell6RootTree : Subdivision :=
.horizontal ((31 : ℚ) / 128)
  (.vertical ((11 : ℚ) / 64)
  (.horizontal ((61 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((61 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((11 : ℚ) / 64)
  (.horizontal ((63 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((63 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow16Cell6RootTree_certified :
    certifySubdivision 12 64 32 lowRow16Cell6RootRectangle
      CertificateObjective.endpointExpression lowRow16Cell6RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow16Cell6Root_nonneg {a q : ℝ}
    (haLower : ((15 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 4))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow16Cell6RootRectangle) (tree := lowRow16Cell6RootTree)
  · norm_num [lowRow16Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell6RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow16Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell6RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow16Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell6RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow16Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow16Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow16Cell6RootTree_certified

private def lowRow16Cell7RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((15 : ℚ) / 64) ((1 : ℚ) / 4),
    RatBall.ofBounds ((3 : ℚ) / 16) ((7 : ℚ) / 32)⟩

private def lowRow16Cell7RootTree : Subdivision :=
.horizontal ((31 : ℚ) / 128)
  (.vertical ((13 : ℚ) / 64)
  (.horizontal ((61 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((61 : ℚ) / 256)
  (.leaf .interval)
  (.vertical ((27 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))))
  (.vertical ((13 : ℚ) / 64)
  (.horizontal ((63 : ℚ) / 256)
  (.leaf .interval)
  (.vertical ((25 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((63 : ℚ) / 256)
  (.vertical ((27 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((27 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))))

private theorem lowRow16Cell7RootTree_certified :
    certifySubdivision 12 64 32 lowRow16Cell7RootRectangle
      CertificateObjective.endpointExpression lowRow16Cell7RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow16Cell7Root_nonneg {a q : ℝ}
    (haLower : ((15 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 4))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow16Cell7RootRectangle) (tree := lowRow16Cell7RootTree)
  · norm_num [lowRow16Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell7RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow16Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell7RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow16Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell7RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow16Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow16Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow16Cell7RootTree_certified

private def lowRow16Cell8RootLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((15 : ℚ) / 64) ((31 : ℚ) / 128),
    RatBall.ofBounds ((7 : ℚ) / 32) ((1 : ℚ) / 4)⟩

private def lowRow16Cell8RootLTree : Subdivision :=
.vertical ((15 : ℚ) / 64)
  (.horizontal ((61 : ℚ) / 256)
  (.vertical ((29 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((29 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((61 : ℚ) / 256)
  (.vertical ((31 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((31 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow16Cell8RootLTree_certified :
    certifySubdivision 12 64 32 lowRow16Cell8RootLRectangle
      CertificateObjective.endpointExpression lowRow16Cell8RootLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow16Cell8RootL_nonneg {a q : ℝ}
    (haLower : ((15 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((31 : ℝ) / 128))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow16Cell8RootLRectangle) (tree := lowRow16Cell8RootLTree)
  · norm_num [lowRow16Cell8RootLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell8RootLRectangle, RatBall.ofBounds]
  · norm_num [lowRow16Cell8RootLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell8RootLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow16Cell8RootLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell8RootLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow16Cell8RootLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow16Cell8RootLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow16Cell8RootLTree_certified

end Frankl
