import Frankl.EndpointCertificate

namespace Frankl

private def lowRow6Cell0RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 64) ((3 : ℚ) / 32),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow6Cell0RootTree : Subdivision :=
.horizontal ((11 : ℚ) / 128)
  (.horizontal ((21 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((23 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow6Cell0RootTree_certified :
    certifySubdivision 12 64 32 lowRow6Cell0RootRectangle
      CertificateObjective.endpointExpression lowRow6Cell0RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow6Cell0Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow6Cell0RootRectangle) (tree := lowRow6Cell0RootTree)
  · norm_num [lowRow6Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell0RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow6Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell0RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow6Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell0RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow6Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow6Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow6Cell0RootTree_certified

private def lowRow6Cell1RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 64) ((3 : ℚ) / 32),
    RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 32)⟩

private def lowRow6Cell1RootTree : Subdivision :=
.vertical ((129 : ℚ) / 8000)
  (.vertical ((137 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((379 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow6Cell1RootTree_certified :
    certifySubdivision 12 64 32 lowRow6Cell1RootRectangle
      CertificateObjective.endpointExpression lowRow6Cell1RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow6Cell1Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow6Cell1RootRectangle) (tree := lowRow6Cell1RootTree)
  · norm_num [lowRow6Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell1RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow6Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell1RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow6Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell1RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow6Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow6Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow6Cell1RootTree_certified

private def lowRow6Cell2RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 64) ((3 : ℚ) / 32),
    RatBall.ofBounds ((1 : ℚ) / 32) ((1 : ℚ) / 16)⟩

private def lowRow6Cell2RootTree : Subdivision :=
.vertical ((3 : ℚ) / 64)
  (.horizontal ((11 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((11 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow6Cell2RootTree_certified :
    certifySubdivision 12 64 32 lowRow6Cell2RootRectangle
      CertificateObjective.endpointExpression lowRow6Cell2RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow6Cell2Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow6Cell2RootRectangle) (tree := lowRow6Cell2RootTree)
  · norm_num [lowRow6Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell2RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow6Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell2RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow6Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell2RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow6Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow6Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow6Cell2RootTree_certified

private def lowRow6Cell3RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 64) ((3 : ℚ) / 32),
    RatBall.ofBounds ((1 : ℚ) / 16) ((3 : ℚ) / 32)⟩

private def lowRow6Cell3RootTree : Subdivision :=
.vertical ((5 : ℚ) / 64)
  (.horizontal ((11 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((11 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow6Cell3RootTree_certified :
    certifySubdivision 12 64 32 lowRow6Cell3RootRectangle
      CertificateObjective.endpointExpression lowRow6Cell3RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow6Cell3Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow6Cell3RootRectangle) (tree := lowRow6Cell3RootTree)
  · norm_num [lowRow6Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell3RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow6Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell3RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow6Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell3RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow6Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow6Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow6Cell3RootTree_certified

private def lowRow6Cell4RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 64) ((3 : ℚ) / 32),
    RatBall.ofBounds ((3 : ℚ) / 32) ((1 : ℚ) / 8)⟩

private def lowRow6Cell4RootTree : Subdivision :=
.vertical ((7 : ℚ) / 64)
  (.horizontal ((11 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((11 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow6Cell4RootTree_certified :
    certifySubdivision 12 64 32 lowRow6Cell4RootRectangle
      CertificateObjective.endpointExpression lowRow6Cell4RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow6Cell4Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow6Cell4RootRectangle) (tree := lowRow6Cell4RootTree)
  · norm_num [lowRow6Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell4RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow6Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell4RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow6Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell4RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow6Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow6Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow6Cell4RootTree_certified

private def lowRow6Cell5RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 64) ((3 : ℚ) / 32),
    RatBall.ofBounds ((1 : ℚ) / 8) ((5 : ℚ) / 32)⟩

private def lowRow6Cell5RootTree : Subdivision :=
.vertical ((9 : ℚ) / 64)
  (.horizontal ((11 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((11 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow6Cell5RootTree_certified :
    certifySubdivision 12 64 32 lowRow6Cell5RootRectangle
      CertificateObjective.endpointExpression lowRow6Cell5RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow6Cell5Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow6Cell5RootRectangle) (tree := lowRow6Cell5RootTree)
  · norm_num [lowRow6Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell5RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow6Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell5RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow6Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell5RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow6Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow6Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow6Cell5RootTree_certified

private def lowRow6Cell6RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 64) ((3 : ℚ) / 32),
    RatBall.ofBounds ((5 : ℚ) / 32) ((3 : ℚ) / 16)⟩

private def lowRow6Cell6RootTree : Subdivision :=
.horizontal ((11 : ℚ) / 128)
  (.vertical ((11 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((11 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow6Cell6RootTree_certified :
    certifySubdivision 12 64 32 lowRow6Cell6RootRectangle
      CertificateObjective.endpointExpression lowRow6Cell6RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow6Cell6Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow6Cell6RootRectangle) (tree := lowRow6Cell6RootTree)
  · norm_num [lowRow6Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell6RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow6Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell6RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow6Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell6RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow6Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow6Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow6Cell6RootTree_certified

end Frankl
