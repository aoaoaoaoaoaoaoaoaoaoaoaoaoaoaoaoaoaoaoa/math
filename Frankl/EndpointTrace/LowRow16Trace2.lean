import Frankl.EndpointCertificate

namespace Frankl

private def lowRow16Cell8RootURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((31 : ℚ) / 128) ((1 : ℚ) / 4),
    RatBall.ofBounds ((7 : ℚ) / 32) ((1 : ℚ) / 4)⟩

private def lowRow16Cell8RootUTree : Subdivision :=
.vertical ((15 : ℚ) / 64)
  (.horizontal ((63 : ℚ) / 256)
  (.vertical ((29 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((29 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((63 : ℚ) / 256)
  (.vertical ((31 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((31 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow16Cell8RootUTree_certified :
    certifySubdivision 12 64 32 lowRow16Cell8RootURectangle
      CertificateObjective.endpointExpression lowRow16Cell8RootUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow16Cell8RootU_nonneg {a q : ℝ}
    (haLower : ((31 : ℝ) / 128) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 4))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow16Cell8RootURectangle) (tree := lowRow16Cell8RootUTree)
  · norm_num [lowRow16Cell8RootURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell8RootURectangle, RatBall.ofBounds]
  · norm_num [lowRow16Cell8RootURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell8RootURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow16Cell8RootURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell8RootURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow16Cell8RootURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow16Cell8RootURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow16Cell8RootUTree_certified

private def lowRow16Cell9RootLRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((15 : ℚ) / 64) ((31 : ℚ) / 128),
    RatBall.ofBounds ((1 : ℚ) / 4) ((9 : ℚ) / 32)⟩

private def lowRow16Cell9RootLTree : Subdivision :=
.vertical ((17 : ℚ) / 64)
  (.horizontal ((61 : ℚ) / 256)
  (.vertical ((33 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((33 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((61 : ℚ) / 256)
  (.leaf .interval)
  (.vertical ((35 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow16Cell9RootLTree_certified :
    certifySubdivision 12 64 32 lowRow16Cell9RootLRectangle
      CertificateObjective.endpointExpression lowRow16Cell9RootLTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow16Cell9RootL_nonneg {a q : ℝ}
    (haLower : ((15 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((31 : ℝ) / 128))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow16Cell9RootLRectangle) (tree := lowRow16Cell9RootLTree)
  · norm_num [lowRow16Cell9RootLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell9RootLRectangle, RatBall.ofBounds]
  · norm_num [lowRow16Cell9RootLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell9RootLRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow16Cell9RootLRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell9RootLRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow16Cell9RootLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow16Cell9RootLRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow16Cell9RootLTree_certified

private def lowRow16Cell9RootURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((31 : ℚ) / 128) ((1 : ℚ) / 4),
    RatBall.ofBounds ((1 : ℚ) / 4) ((9 : ℚ) / 32)⟩

private def lowRow16Cell9RootUTree : Subdivision :=
.vertical ((17 : ℚ) / 64)
  (.horizontal ((63 : ℚ) / 256)
  (.vertical ((33 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((33 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((63 : ℚ) / 256)
  (.vertical ((35 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((35 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow16Cell9RootUTree_certified :
    certifySubdivision 12 64 32 lowRow16Cell9RootURectangle
      CertificateObjective.endpointExpression lowRow16Cell9RootUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow16Cell9RootU_nonneg {a q : ℝ}
    (haLower : ((31 : ℝ) / 128) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 4))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow16Cell9RootURectangle) (tree := lowRow16Cell9RootUTree)
  · norm_num [lowRow16Cell9RootURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell9RootURectangle, RatBall.ofBounds]
  · norm_num [lowRow16Cell9RootURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell9RootURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow16Cell9RootURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell9RootURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow16Cell9RootURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow16Cell9RootURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow16Cell9RootUTree_certified

end Frankl
