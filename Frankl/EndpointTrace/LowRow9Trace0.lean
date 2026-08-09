import Frankl.EndpointCertificate

namespace Frankl

private def lowRow9Cell0RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 8) ((9 : ℚ) / 64),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow9Cell0RootTree : Subdivision :=
.horizontal ((17 : ℚ) / 128)
  (.horizontal ((33 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((35 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow9Cell0RootTree_certified :
    certifySubdivision 12 64 32 lowRow9Cell0RootRectangle
      CertificateObjective.endpointExpression lowRow9Cell0RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow9Cell0Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 8) ≤ a)
    (haUpper : a ≤ ((9 : ℝ) / 64))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow9Cell0RootRectangle) (tree := lowRow9Cell0RootTree)
  · norm_num [lowRow9Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell0RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow9Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell0RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow9Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell0RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow9Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow9Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow9Cell0RootTree_certified

private def lowRow9Cell1RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 8) ((9 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 32)⟩

private def lowRow9Cell1RootTree : Subdivision :=
.vertical ((129 : ℚ) / 8000)
  (.vertical ((137 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((379 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow9Cell1RootTree_certified :
    certifySubdivision 12 64 32 lowRow9Cell1RootRectangle
      CertificateObjective.endpointExpression lowRow9Cell1RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow9Cell1Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 8) ≤ a)
    (haUpper : a ≤ ((9 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow9Cell1RootRectangle) (tree := lowRow9Cell1RootTree)
  · norm_num [lowRow9Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell1RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow9Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell1RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow9Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell1RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow9Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow9Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow9Cell1RootTree_certified

private def lowRow9Cell2RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 8) ((9 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 32) ((1 : ℚ) / 16)⟩

private def lowRow9Cell2RootTree : Subdivision :=
.vertical ((3 : ℚ) / 64)
  (.horizontal ((17 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((17 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow9Cell2RootTree_certified :
    certifySubdivision 12 64 32 lowRow9Cell2RootRectangle
      CertificateObjective.endpointExpression lowRow9Cell2RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow9Cell2Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 8) ≤ a)
    (haUpper : a ≤ ((9 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow9Cell2RootRectangle) (tree := lowRow9Cell2RootTree)
  · norm_num [lowRow9Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell2RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow9Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell2RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow9Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell2RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow9Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow9Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow9Cell2RootTree_certified

private def lowRow9Cell3RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 8) ((9 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 16) ((3 : ℚ) / 32)⟩

private def lowRow9Cell3RootTree : Subdivision :=
.vertical ((5 : ℚ) / 64)
  (.horizontal ((17 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((17 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow9Cell3RootTree_certified :
    certifySubdivision 12 64 32 lowRow9Cell3RootRectangle
      CertificateObjective.endpointExpression lowRow9Cell3RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow9Cell3Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 8) ≤ a)
    (haUpper : a ≤ ((9 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow9Cell3RootRectangle) (tree := lowRow9Cell3RootTree)
  · norm_num [lowRow9Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell3RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow9Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell3RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow9Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell3RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow9Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow9Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow9Cell3RootTree_certified

private def lowRow9Cell4RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 8) ((9 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 32) ((1 : ℚ) / 8)⟩

private def lowRow9Cell4RootTree : Subdivision :=
.vertical ((7 : ℚ) / 64)
  (.horizontal ((17 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((17 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow9Cell4RootTree_certified :
    certifySubdivision 12 64 32 lowRow9Cell4RootRectangle
      CertificateObjective.endpointExpression lowRow9Cell4RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow9Cell4Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 8) ≤ a)
    (haUpper : a ≤ ((9 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow9Cell4RootRectangle) (tree := lowRow9Cell4RootTree)
  · norm_num [lowRow9Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell4RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow9Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell4RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow9Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell4RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow9Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow9Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow9Cell4RootTree_certified

private def lowRow9Cell5RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 8) ((9 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 8) ((5 : ℚ) / 32)⟩

private def lowRow9Cell5RootTree : Subdivision :=
.vertical ((9 : ℚ) / 64)
  (.horizontal ((17 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((17 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow9Cell5RootTree_certified :
    certifySubdivision 12 64 32 lowRow9Cell5RootRectangle
      CertificateObjective.endpointExpression lowRow9Cell5RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow9Cell5Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 8) ≤ a)
    (haUpper : a ≤ ((9 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow9Cell5RootRectangle) (tree := lowRow9Cell5RootTree)
  · norm_num [lowRow9Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell5RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow9Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell5RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow9Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell5RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow9Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow9Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow9Cell5RootTree_certified

private def lowRow9Cell6RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 8) ((9 : ℚ) / 64),
    RatBall.ofBounds ((5 : ℚ) / 32) ((3 : ℚ) / 16)⟩

private def lowRow9Cell6RootTree : Subdivision :=
.horizontal ((17 : ℚ) / 128)
  (.vertical ((11 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((11 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow9Cell6RootTree_certified :
    certifySubdivision 12 64 32 lowRow9Cell6RootRectangle
      CertificateObjective.endpointExpression lowRow9Cell6RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow9Cell6Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 8) ≤ a)
    (haUpper : a ≤ ((9 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow9Cell6RootRectangle) (tree := lowRow9Cell6RootTree)
  · norm_num [lowRow9Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell6RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow9Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell6RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow9Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell6RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow9Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow9Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow9Cell6RootTree_certified

end Frankl
