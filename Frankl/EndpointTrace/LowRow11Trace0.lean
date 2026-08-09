import Frankl.EndpointCertificate

namespace Frankl

private def lowRow11Cell0RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 32) ((11 : ℚ) / 64),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow11Cell0RootTree : Subdivision :=
.horizontal ((21 : ℚ) / 128)
  (.horizontal ((41 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((43 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow11Cell0RootTree_certified :
    certifySubdivision 12 64 32 lowRow11Cell0RootRectangle
      CertificateObjective.endpointExpression lowRow11Cell0RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow11Cell0Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow11Cell0RootRectangle) (tree := lowRow11Cell0RootTree)
  · norm_num [lowRow11Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell0RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow11Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell0RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow11Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell0RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow11Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow11Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow11Cell0RootTree_certified

private def lowRow11Cell1RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 32) ((11 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 32)⟩

private def lowRow11Cell1RootTree : Subdivision :=
.vertical ((129 : ℚ) / 8000)
  (.vertical ((137 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((21 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow11Cell1RootTree_certified :
    certifySubdivision 12 64 32 lowRow11Cell1RootRectangle
      CertificateObjective.endpointExpression lowRow11Cell1RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow11Cell1Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow11Cell1RootRectangle) (tree := lowRow11Cell1RootTree)
  · norm_num [lowRow11Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell1RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow11Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell1RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow11Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell1RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow11Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow11Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow11Cell1RootTree_certified

private def lowRow11Cell2RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 32) ((11 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 32) ((1 : ℚ) / 16)⟩

private def lowRow11Cell2RootTree : Subdivision :=
.vertical ((3 : ℚ) / 64)
  (.horizontal ((21 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((21 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow11Cell2RootTree_certified :
    certifySubdivision 12 64 32 lowRow11Cell2RootRectangle
      CertificateObjective.endpointExpression lowRow11Cell2RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow11Cell2Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow11Cell2RootRectangle) (tree := lowRow11Cell2RootTree)
  · norm_num [lowRow11Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell2RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow11Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell2RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow11Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell2RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow11Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow11Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow11Cell2RootTree_certified

private def lowRow11Cell3RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 32) ((11 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 16) ((3 : ℚ) / 32)⟩

private def lowRow11Cell3RootTree : Subdivision :=
.vertical ((5 : ℚ) / 64)
  (.horizontal ((21 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((21 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow11Cell3RootTree_certified :
    certifySubdivision 12 64 32 lowRow11Cell3RootRectangle
      CertificateObjective.endpointExpression lowRow11Cell3RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow11Cell3Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow11Cell3RootRectangle) (tree := lowRow11Cell3RootTree)
  · norm_num [lowRow11Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell3RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow11Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell3RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow11Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell3RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow11Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow11Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow11Cell3RootTree_certified

private def lowRow11Cell4RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 32) ((11 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 32) ((1 : ℚ) / 8)⟩

private def lowRow11Cell4RootTree : Subdivision :=
.vertical ((7 : ℚ) / 64)
  (.horizontal ((21 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((21 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow11Cell4RootTree_certified :
    certifySubdivision 12 64 32 lowRow11Cell4RootRectangle
      CertificateObjective.endpointExpression lowRow11Cell4RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow11Cell4Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow11Cell4RootRectangle) (tree := lowRow11Cell4RootTree)
  · norm_num [lowRow11Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell4RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow11Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell4RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow11Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell4RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow11Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow11Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow11Cell4RootTree_certified

private def lowRow11Cell5RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 32) ((11 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 8) ((5 : ℚ) / 32)⟩

private def lowRow11Cell5RootTree : Subdivision :=
.horizontal ((21 : ℚ) / 128)
  (.vertical ((9 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((9 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow11Cell5RootTree_certified :
    certifySubdivision 12 64 32 lowRow11Cell5RootRectangle
      CertificateObjective.endpointExpression lowRow11Cell5RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow11Cell5Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow11Cell5RootRectangle) (tree := lowRow11Cell5RootTree)
  · norm_num [lowRow11Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell5RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow11Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell5RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow11Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell5RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow11Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow11Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow11Cell5RootTree_certified

end Frankl
