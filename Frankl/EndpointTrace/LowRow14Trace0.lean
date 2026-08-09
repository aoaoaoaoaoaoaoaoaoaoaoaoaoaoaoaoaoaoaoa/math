import Frankl.EndpointCertificate

namespace Frankl

private def lowRow14Cell0RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((13 : ℚ) / 64) ((7 : ℚ) / 32),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow14Cell0RootTree : Subdivision :=
.horizontal ((27 : ℚ) / 128)
  (.horizontal ((53 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((55 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow14Cell0RootTree_certified :
    certifySubdivision 12 64 32 lowRow14Cell0RootRectangle
      CertificateObjective.endpointExpression lowRow14Cell0RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow14Cell0Root_nonneg {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow14Cell0RootRectangle) (tree := lowRow14Cell0RootTree)
  · norm_num [lowRow14Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell0RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow14Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell0RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow14Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell0RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow14Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow14Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow14Cell0RootTree_certified

private def lowRow14Cell1RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((13 : ℚ) / 64) ((7 : ℚ) / 32),
    RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 32)⟩

private def lowRow14Cell1RootTree : Subdivision :=
.vertical ((129 : ℚ) / 8000)
  (.vertical ((137 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((27 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow14Cell1RootTree_certified :
    certifySubdivision 12 64 32 lowRow14Cell1RootRectangle
      CertificateObjective.endpointExpression lowRow14Cell1RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow14Cell1Root_nonneg {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow14Cell1RootRectangle) (tree := lowRow14Cell1RootTree)
  · norm_num [lowRow14Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell1RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow14Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell1RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow14Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell1RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow14Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow14Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow14Cell1RootTree_certified

private def lowRow14Cell2RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((13 : ℚ) / 64) ((7 : ℚ) / 32),
    RatBall.ofBounds ((1 : ℚ) / 32) ((1 : ℚ) / 16)⟩

private def lowRow14Cell2RootTree : Subdivision :=
.vertical ((3 : ℚ) / 64)
  (.horizontal ((27 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((27 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow14Cell2RootTree_certified :
    certifySubdivision 12 64 32 lowRow14Cell2RootRectangle
      CertificateObjective.endpointExpression lowRow14Cell2RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow14Cell2Root_nonneg {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow14Cell2RootRectangle) (tree := lowRow14Cell2RootTree)
  · norm_num [lowRow14Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell2RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow14Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell2RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow14Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell2RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow14Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow14Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow14Cell2RootTree_certified

private def lowRow14Cell3RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((13 : ℚ) / 64) ((7 : ℚ) / 32),
    RatBall.ofBounds ((1 : ℚ) / 16) ((3 : ℚ) / 32)⟩

private def lowRow14Cell3RootTree : Subdivision :=
.vertical ((5 : ℚ) / 64)
  (.horizontal ((27 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((27 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow14Cell3RootTree_certified :
    certifySubdivision 12 64 32 lowRow14Cell3RootRectangle
      CertificateObjective.endpointExpression lowRow14Cell3RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow14Cell3Root_nonneg {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow14Cell3RootRectangle) (tree := lowRow14Cell3RootTree)
  · norm_num [lowRow14Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell3RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow14Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell3RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow14Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell3RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow14Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow14Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow14Cell3RootTree_certified

private def lowRow14Cell4RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((13 : ℚ) / 64) ((7 : ℚ) / 32),
    RatBall.ofBounds ((3 : ℚ) / 32) ((1 : ℚ) / 8)⟩

private def lowRow14Cell4RootTree : Subdivision :=
.vertical ((7 : ℚ) / 64)
  (.horizontal ((27 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((27 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow14Cell4RootTree_certified :
    certifySubdivision 12 64 32 lowRow14Cell4RootRectangle
      CertificateObjective.endpointExpression lowRow14Cell4RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow14Cell4Root_nonneg {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow14Cell4RootRectangle) (tree := lowRow14Cell4RootTree)
  · norm_num [lowRow14Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell4RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow14Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell4RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow14Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell4RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow14Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow14Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow14Cell4RootTree_certified

private def lowRow14Cell5RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((13 : ℚ) / 64) ((7 : ℚ) / 32),
    RatBall.ofBounds ((1 : ℚ) / 8) ((5 : ℚ) / 32)⟩

private def lowRow14Cell5RootTree : Subdivision :=
.horizontal ((27 : ℚ) / 128)
  (.vertical ((9 : ℚ) / 64)
  (.leaf .interval)
  (.horizontal ((53 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((9 : ℚ) / 64)
  (.leaf .interval)
  (.horizontal ((55 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow14Cell5RootTree_certified :
    certifySubdivision 12 64 32 lowRow14Cell5RootRectangle
      CertificateObjective.endpointExpression lowRow14Cell5RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow14Cell5Root_nonneg {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow14Cell5RootRectangle) (tree := lowRow14Cell5RootTree)
  · norm_num [lowRow14Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell5RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow14Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell5RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow14Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell5RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow14Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow14Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow14Cell5RootTree_certified

end Frankl
