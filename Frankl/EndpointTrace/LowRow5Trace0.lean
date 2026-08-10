import Frankl.EndpointCertificate

namespace Frankl

private def lowRow5Cell0RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 16) ((5 : ℚ) / 64),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow5Cell0RootTree : Subdivision :=
.horizontal ((9 : ℚ) / 128)
  (.horizontal ((17 : ℚ) / 256)
  (.horizontal ((33 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((35 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval)))
  (.horizontal ((19 : ℚ) / 256)
  (.horizontal ((37 : ℚ) / 512)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))

private theorem lowRow5Cell0RootTree_certified :
    certifySubdivision 12 64 32 lowRow5Cell0RootRectangle
      CertificateObjective.endpointExpression lowRow5Cell0RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow5Cell0Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow5Cell0RootRectangle) (tree := lowRow5Cell0RootTree)
  · norm_num [lowRow5Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell0RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow5Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell0RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow5Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell0RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow5Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow5Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow5Cell0RootTree_certified

private def lowRow5Cell1RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 16) ((5 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 32)⟩

private def lowRow5Cell1RootTree : Subdivision :=
.vertical ((129 : ℚ) / 8000)
  (.vertical ((137 : ℚ) / 16000)
  (.vertical ((153 : ℚ) / 32000)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))
  (.vertical ((379 : ℚ) / 16000)
  (.leaf .interval)
  (.horizontal ((9 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow5Cell1RootTree_certified :
    certifySubdivision 12 64 32 lowRow5Cell1RootRectangle
      CertificateObjective.endpointExpression lowRow5Cell1RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow5Cell1Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow5Cell1RootRectangle) (tree := lowRow5Cell1RootTree)
  · norm_num [lowRow5Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell1RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow5Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell1RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow5Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell1RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow5Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow5Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow5Cell1RootTree_certified

private def lowRow5Cell2RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 16) ((5 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 32) ((1 : ℚ) / 16)⟩

private def lowRow5Cell2RootTree : Subdivision :=
.vertical ((3 : ℚ) / 64)
  (.horizontal ((9 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((9 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow5Cell2RootTree_certified :
    certifySubdivision 12 64 32 lowRow5Cell2RootRectangle
      CertificateObjective.endpointExpression lowRow5Cell2RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow5Cell2Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow5Cell2RootRectangle) (tree := lowRow5Cell2RootTree)
  · norm_num [lowRow5Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell2RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow5Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell2RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow5Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell2RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow5Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow5Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow5Cell2RootTree_certified

private def lowRow5Cell3RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 16) ((5 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 16) ((3 : ℚ) / 32)⟩

private def lowRow5Cell3RootTree : Subdivision :=
.vertical ((5 : ℚ) / 64)
  (.horizontal ((9 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((9 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow5Cell3RootTree_certified :
    certifySubdivision 12 64 32 lowRow5Cell3RootRectangle
      CertificateObjective.endpointExpression lowRow5Cell3RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow5Cell3Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow5Cell3RootRectangle) (tree := lowRow5Cell3RootTree)
  · norm_num [lowRow5Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell3RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow5Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell3RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow5Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell3RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow5Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow5Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow5Cell3RootTree_certified

private def lowRow5Cell4RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 16) ((5 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 32) ((1 : ℚ) / 8)⟩

private def lowRow5Cell4RootTree : Subdivision :=
.vertical ((7 : ℚ) / 64)
  (.horizontal ((9 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((9 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow5Cell4RootTree_certified :
    certifySubdivision 12 64 32 lowRow5Cell4RootRectangle
      CertificateObjective.endpointExpression lowRow5Cell4RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow5Cell4Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow5Cell4RootRectangle) (tree := lowRow5Cell4RootTree)
  · norm_num [lowRow5Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell4RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow5Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell4RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow5Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell4RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow5Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow5Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow5Cell4RootTree_certified

end Frankl
