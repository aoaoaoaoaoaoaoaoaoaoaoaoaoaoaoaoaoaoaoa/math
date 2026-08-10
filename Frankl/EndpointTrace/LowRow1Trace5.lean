import Frankl.EndpointCertificate

namespace Frankl

private def lowRow1Cell1RootURectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 64),
    RatBall.ofBounds ((129 : ℚ) / 8000) ((1 : ℚ) / 32)⟩

private def lowRow1Cell1RootUTree : Subdivision :=
.horizontal ((133 : ℚ) / 16000)
  (.vertical ((379 : ℚ) / 16000)
  (.horizontal ((149 : ℚ) / 32000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((149 : ℚ) / 32000)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((379 : ℚ) / 16000)
  (.horizontal ((383 : ℚ) / 32000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))

private theorem lowRow1Cell1RootUTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell1RootURectangle
      CertificateObjective.endpointExpression lowRow1Cell1RootUTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell1RootU_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((129 : ℝ) / 8000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell1RootURectangle) (tree := lowRow1Cell1RootUTree)
  · norm_num [lowRow1Cell1RootURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell1RootURectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell1RootURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell1RootURectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell1RootURectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell1RootURectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell1RootURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell1RootURectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell1RootUTree_certified

private def lowRow1Cell2RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 32) ((1 : ℚ) / 16)⟩

private def lowRow1Cell2RootTree : Subdivision :=
.vertical ((3 : ℚ) / 64)
  (.horizontal ((133 : ℚ) / 16000)
  (.horizontal ((149 : ℚ) / 32000)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((5 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((133 : ℚ) / 16000)
  (.horizontal ((149 : ℚ) / 32000)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((7 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow1Cell2RootTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell2RootRectangle
      CertificateObjective.endpointExpression lowRow1Cell2RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell2Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell2RootRectangle) (tree := lowRow1Cell2RootTree)
  · norm_num [lowRow1Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell2RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell2RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell2RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell2RootTree_certified

private def lowRow1Cell3RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 16) ((3 : ℚ) / 32)⟩

private def lowRow1Cell3RootTree : Subdivision :=
.horizontal ((133 : ℚ) / 16000)
  (.vertical ((5 : ℚ) / 64)
  (.horizontal ((149 : ℚ) / 32000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.vertical ((5 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow1Cell3RootTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell3RootRectangle
      CertificateObjective.endpointExpression lowRow1Cell3RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell3Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell3RootRectangle) (tree := lowRow1Cell3RootTree)
  · norm_num [lowRow1Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell3RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell3RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell3RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell3RootTree_certified

private def lowRow1Cell4RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 32) ((1 : ℚ) / 8)⟩

private def lowRow1Cell4RootTree : Subdivision :=
.horizontal ((133 : ℚ) / 16000)
  (.vertical ((7 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((7 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow1Cell4RootTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell4RootRectangle
      CertificateObjective.endpointExpression lowRow1Cell4RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell4Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell4RootRectangle) (tree := lowRow1Cell4RootTree)
  · norm_num [lowRow1Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell4RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell4RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell4RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell4RootTree_certified

private def lowRow1Cell5RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 8) ((5 : ℚ) / 32)⟩

private def lowRow1Cell5RootTree : Subdivision :=
.horizontal ((133 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow1Cell5RootTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell5RootRectangle
      CertificateObjective.endpointExpression lowRow1Cell5RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell5Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell5RootRectangle) (tree := lowRow1Cell5RootTree)
  · norm_num [lowRow1Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell5RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell5RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell5RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell5RootTree_certified

private def lowRow1Cell6RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 64),
    RatBall.ofBounds ((5 : ℚ) / 32) ((3 : ℚ) / 16)⟩

private def lowRow1Cell6RootTree : Subdivision :=
.horizontal ((133 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow1Cell6RootTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell6RootRectangle
      CertificateObjective.endpointExpression lowRow1Cell6RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell6Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell6RootRectangle) (tree := lowRow1Cell6RootTree)
  · norm_num [lowRow1Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell6RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell6RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell6RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell6RootTree_certified

end Frankl
