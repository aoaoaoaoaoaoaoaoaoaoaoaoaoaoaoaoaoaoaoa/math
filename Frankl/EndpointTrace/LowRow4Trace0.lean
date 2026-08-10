import Frankl.EndpointCertificate

namespace Frankl

private def lowRow4Cell0RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 64) ((1 : ℚ) / 16),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow4Cell0RootTree : Subdivision :=
.horizontal ((7 : ℚ) / 128)
  (.horizontal ((13 : ℚ) / 256)
  (.horizontal ((25 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((27 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((15 : ℚ) / 256)
  (.horizontal ((29 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((31 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow4Cell0RootTree_certified :
    certifySubdivision 12 64 32 lowRow4Cell0RootRectangle
      CertificateObjective.endpointExpression lowRow4Cell0RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow4Cell0Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow4Cell0RootRectangle) (tree := lowRow4Cell0RootTree)
  · norm_num [lowRow4Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell0RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow4Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell0RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow4Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell0RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow4Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow4Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow4Cell0RootTree_certified

private def lowRow4Cell1RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 64) ((1 : ℚ) / 16),
    RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 32)⟩

private def lowRow4Cell1RootTree : Subdivision :=
.vertical ((129 : ℚ) / 8000)
  (.vertical ((137 : ℚ) / 16000)
  (.vertical ((153 : ℚ) / 32000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((7 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((7 : ℚ) / 128)
  (.vertical ((379 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))

private theorem lowRow4Cell1RootTree_certified :
    certifySubdivision 12 64 32 lowRow4Cell1RootRectangle
      CertificateObjective.endpointExpression lowRow4Cell1RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow4Cell1Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow4Cell1RootRectangle) (tree := lowRow4Cell1RootTree)
  · norm_num [lowRow4Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell1RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow4Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell1RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow4Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell1RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow4Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow4Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow4Cell1RootTree_certified

private def lowRow4Cell2RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 64) ((1 : ℚ) / 16),
    RatBall.ofBounds ((1 : ℚ) / 32) ((1 : ℚ) / 16)⟩

private def lowRow4Cell2RootTree : Subdivision :=
.vertical ((3 : ℚ) / 64)
  (.horizontal ((7 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((7 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow4Cell2RootTree_certified :
    certifySubdivision 12 64 32 lowRow4Cell2RootRectangle
      CertificateObjective.endpointExpression lowRow4Cell2RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow4Cell2Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow4Cell2RootRectangle) (tree := lowRow4Cell2RootTree)
  · norm_num [lowRow4Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell2RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow4Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell2RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow4Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell2RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow4Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow4Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow4Cell2RootTree_certified

private def lowRow4Cell3RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 64) ((1 : ℚ) / 16),
    RatBall.ofBounds ((1 : ℚ) / 16) ((3 : ℚ) / 32)⟩

private def lowRow4Cell3RootTree : Subdivision :=
.vertical ((5 : ℚ) / 64)
  (.horizontal ((7 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((7 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow4Cell3RootTree_certified :
    certifySubdivision 12 64 32 lowRow4Cell3RootRectangle
      CertificateObjective.endpointExpression lowRow4Cell3RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow4Cell3Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow4Cell3RootRectangle) (tree := lowRow4Cell3RootTree)
  · norm_num [lowRow4Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell3RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow4Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell3RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow4Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell3RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow4Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow4Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow4Cell3RootTree_certified

private def lowRow4Cell4RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 64) ((1 : ℚ) / 16),
    RatBall.ofBounds ((3 : ℚ) / 32) ((1 : ℚ) / 8)⟩

private def lowRow4Cell4RootTree : Subdivision :=
.vertical ((7 : ℚ) / 64)
  (.horizontal ((7 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((7 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow4Cell4RootTree_certified :
    certifySubdivision 12 64 32 lowRow4Cell4RootRectangle
      CertificateObjective.endpointExpression lowRow4Cell4RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow4Cell4Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow4Cell4RootRectangle) (tree := lowRow4Cell4RootTree)
  · norm_num [lowRow4Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell4RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow4Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell4RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow4Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell4RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow4Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow4Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow4Cell4RootTree_certified

end Frankl
