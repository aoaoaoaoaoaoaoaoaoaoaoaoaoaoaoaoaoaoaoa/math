import Frankl.EndpointCertificate

namespace Frankl

private def lowRow16Cell9RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((15 : ℚ) / 64) ((1 : ℚ) / 4),
    RatBall.ofBounds ((1 : ℚ) / 4) ((9 : ℚ) / 32)⟩

private def lowRow16Cell9RootTree : Subdivision :=
.horizontal ((31 : ℚ) / 128)
  (.vertical ((17 : ℚ) / 64)
  (.horizontal ((61 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((61 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((17 : ℚ) / 64)
  (.horizontal ((63 : ℚ) / 256)
  (.leaf .interval)
  (.vertical ((33 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((63 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow16Cell9RootTree_certified :
    certifySubdivision 12 64 32 lowRow16Cell9RootRectangle
      CertificateObjective.endpointExpression lowRow16Cell9RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow16Cell9Root_nonneg {a q : ℝ}
    (haLower : ((15 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 4))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow16Cell9RootRectangle) (tree := lowRow16Cell9RootTree)
  · norm_num [lowRow16Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell9RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow16Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell9RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow16Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell9RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow16Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow16Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow16Cell9RootTree_certified

private def lowRow16Cell10RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((15 : ℚ) / 64) ((1 : ℚ) / 4),
    RatBall.ofBounds ((9 : ℚ) / 32) ((5 : ℚ) / 16)⟩

private def lowRow16Cell10RootTree : Subdivision :=
.horizontal ((31 : ℚ) / 128)
  (.vertical ((19 : ℚ) / 64)
  (.horizontal ((61 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((61 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((19 : ℚ) / 64)
  (.horizontal ((63 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((63 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow16Cell10RootTree_certified :
    certifySubdivision 12 64 32 lowRow16Cell10RootRectangle
      CertificateObjective.endpointExpression lowRow16Cell10RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow16Cell10Root_nonneg {a q : ℝ}
    (haLower : ((15 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 4))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow16Cell10RootRectangle) (tree := lowRow16Cell10RootTree)
  · norm_num [lowRow16Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell10RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow16Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell10RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow16Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell10RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow16Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow16Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow16Cell10RootTree_certified

private def lowRow16Cell11RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((15 : ℚ) / 64) ((1 : ℚ) / 4),
    RatBall.ofBounds ((5 : ℚ) / 16) ((11 : ℚ) / 32)⟩

private def lowRow16Cell11RootTree : Subdivision :=
.horizontal ((31 : ℚ) / 128)
  (.vertical ((21 : ℚ) / 64)
  (.horizontal ((61 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((61 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((21 : ℚ) / 64)
  (.horizontal ((63 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((63 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow16Cell11RootTree_certified :
    certifySubdivision 12 64 32 lowRow16Cell11RootRectangle
      CertificateObjective.endpointExpression lowRow16Cell11RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow16Cell11Root_nonneg {a q : ℝ}
    (haLower : ((15 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 4))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow16Cell11RootRectangle) (tree := lowRow16Cell11RootTree)
  · norm_num [lowRow16Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell11RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow16Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell11RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow16Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell11RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow16Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow16Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow16Cell11RootTree_certified

end Frankl
