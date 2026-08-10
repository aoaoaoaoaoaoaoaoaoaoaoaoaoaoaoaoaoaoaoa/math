import Frankl.EndpointCertificate

namespace Frankl

private def lowRow16Cell0RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((15 : ℚ) / 64) ((1 : ℚ) / 4),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow16Cell0RootTree : Subdivision :=
.horizontal ((31 : ℚ) / 128)
  (.horizontal ((61 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((63 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow16Cell0RootTree_certified :
    certifySubdivision 12 64 32 lowRow16Cell0RootRectangle
      CertificateObjective.endpointExpression lowRow16Cell0RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow16Cell0Root_nonneg {a q : ℝ}
    (haLower : ((15 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 4))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow16Cell0RootRectangle) (tree := lowRow16Cell0RootTree)
  · norm_num [lowRow16Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell0RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow16Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell0RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow16Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell0RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow16Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow16Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow16Cell0RootTree_certified

private def lowRow16Cell1RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((15 : ℚ) / 64) ((1 : ℚ) / 4),
    RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 32)⟩

private def lowRow16Cell1RootTree : Subdivision :=
.vertical ((129 : ℚ) / 8000)
  (.vertical ((137 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((31 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow16Cell1RootTree_certified :
    certifySubdivision 12 64 32 lowRow16Cell1RootRectangle
      CertificateObjective.endpointExpression lowRow16Cell1RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow16Cell1Root_nonneg {a q : ℝ}
    (haLower : ((15 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 4))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow16Cell1RootRectangle) (tree := lowRow16Cell1RootTree)
  · norm_num [lowRow16Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell1RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow16Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell1RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow16Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell1RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow16Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow16Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow16Cell1RootTree_certified

private def lowRow16Cell2RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((15 : ℚ) / 64) ((1 : ℚ) / 4),
    RatBall.ofBounds ((1 : ℚ) / 32) ((1 : ℚ) / 16)⟩

private def lowRow16Cell2RootTree : Subdivision :=
.vertical ((3 : ℚ) / 64)
  (.horizontal ((31 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((31 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow16Cell2RootTree_certified :
    certifySubdivision 12 64 32 lowRow16Cell2RootRectangle
      CertificateObjective.endpointExpression lowRow16Cell2RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow16Cell2Root_nonneg {a q : ℝ}
    (haLower : ((15 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 4))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow16Cell2RootRectangle) (tree := lowRow16Cell2RootTree)
  · norm_num [lowRow16Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell2RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow16Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell2RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow16Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell2RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow16Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow16Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow16Cell2RootTree_certified

private def lowRow16Cell3RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((15 : ℚ) / 64) ((1 : ℚ) / 4),
    RatBall.ofBounds ((1 : ℚ) / 16) ((3 : ℚ) / 32)⟩

private def lowRow16Cell3RootTree : Subdivision :=
.vertical ((5 : ℚ) / 64)
  (.horizontal ((31 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((31 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow16Cell3RootTree_certified :
    certifySubdivision 12 64 32 lowRow16Cell3RootRectangle
      CertificateObjective.endpointExpression lowRow16Cell3RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow16Cell3Root_nonneg {a q : ℝ}
    (haLower : ((15 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 4))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow16Cell3RootRectangle) (tree := lowRow16Cell3RootTree)
  · norm_num [lowRow16Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell3RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow16Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell3RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow16Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell3RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow16Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow16Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow16Cell3RootTree_certified

private def lowRow16Cell4RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((15 : ℚ) / 64) ((1 : ℚ) / 4),
    RatBall.ofBounds ((3 : ℚ) / 32) ((1 : ℚ) / 8)⟩

private def lowRow16Cell4RootTree : Subdivision :=
.horizontal ((31 : ℚ) / 128)
  (.vertical ((7 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((7 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow16Cell4RootTree_certified :
    certifySubdivision 12 64 32 lowRow16Cell4RootRectangle
      CertificateObjective.endpointExpression lowRow16Cell4RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow16Cell4Root_nonneg {a q : ℝ}
    (haLower : ((15 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 4))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow16Cell4RootRectangle) (tree := lowRow16Cell4RootTree)
  · norm_num [lowRow16Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell4RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow16Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell4RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow16Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell4RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow16Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow16Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow16Cell4RootTree_certified

private def lowRow16Cell5RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((15 : ℚ) / 64) ((1 : ℚ) / 4),
    RatBall.ofBounds ((1 : ℚ) / 8) ((5 : ℚ) / 32)⟩

private def lowRow16Cell5RootTree : Subdivision :=
.horizontal ((31 : ℚ) / 128)
  (.vertical ((9 : ℚ) / 64)
  (.horizontal ((61 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((61 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((9 : ℚ) / 64)
  (.horizontal ((63 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((63 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow16Cell5RootTree_certified :
    certifySubdivision 12 64 32 lowRow16Cell5RootRectangle
      CertificateObjective.endpointExpression lowRow16Cell5RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow16Cell5Root_nonneg {a q : ℝ}
    (haLower : ((15 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 4))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow16Cell5RootRectangle) (tree := lowRow16Cell5RootTree)
  · norm_num [lowRow16Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell5RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow16Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell5RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow16Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell5RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow16Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow16Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow16Cell5RootTree_certified

end Frankl
