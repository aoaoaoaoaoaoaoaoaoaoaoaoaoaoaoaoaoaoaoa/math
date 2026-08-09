import Frankl.EndpointCertificate

namespace Frankl

private def lowRow8Cell0RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 64) ((1 : ℚ) / 8),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow8Cell0RootTree : Subdivision :=
.horizontal ((15 : ℚ) / 128)
  (.horizontal ((29 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((31 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow8Cell0RootTree_certified :
    certifySubdivision 12 64 32 lowRow8Cell0RootRectangle
      CertificateObjective.endpointExpression lowRow8Cell0RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow8Cell0Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow8Cell0RootRectangle) (tree := lowRow8Cell0RootTree)
  · norm_num [lowRow8Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell0RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow8Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell0RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow8Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell0RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow8Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow8Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow8Cell0RootTree_certified

private def lowRow8Cell1RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 64) ((1 : ℚ) / 8),
    RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 32)⟩

private def lowRow8Cell1RootTree : Subdivision :=
.vertical ((129 : ℚ) / 8000)
  (.vertical ((137 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((379 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow8Cell1RootTree_certified :
    certifySubdivision 12 64 32 lowRow8Cell1RootRectangle
      CertificateObjective.endpointExpression lowRow8Cell1RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow8Cell1Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow8Cell1RootRectangle) (tree := lowRow8Cell1RootTree)
  · norm_num [lowRow8Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell1RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow8Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell1RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow8Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell1RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow8Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow8Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow8Cell1RootTree_certified

private def lowRow8Cell2RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 64) ((1 : ℚ) / 8),
    RatBall.ofBounds ((1 : ℚ) / 32) ((1 : ℚ) / 16)⟩

private def lowRow8Cell2RootTree : Subdivision :=
.vertical ((3 : ℚ) / 64)
  (.horizontal ((15 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((15 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow8Cell2RootTree_certified :
    certifySubdivision 12 64 32 lowRow8Cell2RootRectangle
      CertificateObjective.endpointExpression lowRow8Cell2RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow8Cell2Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow8Cell2RootRectangle) (tree := lowRow8Cell2RootTree)
  · norm_num [lowRow8Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell2RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow8Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell2RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow8Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell2RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow8Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow8Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow8Cell2RootTree_certified

private def lowRow8Cell3RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 64) ((1 : ℚ) / 8),
    RatBall.ofBounds ((1 : ℚ) / 16) ((3 : ℚ) / 32)⟩

private def lowRow8Cell3RootTree : Subdivision :=
.vertical ((5 : ℚ) / 64)
  (.horizontal ((15 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((15 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow8Cell3RootTree_certified :
    certifySubdivision 12 64 32 lowRow8Cell3RootRectangle
      CertificateObjective.endpointExpression lowRow8Cell3RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow8Cell3Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow8Cell3RootRectangle) (tree := lowRow8Cell3RootTree)
  · norm_num [lowRow8Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell3RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow8Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell3RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow8Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell3RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow8Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow8Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow8Cell3RootTree_certified

private def lowRow8Cell4RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 64) ((1 : ℚ) / 8),
    RatBall.ofBounds ((3 : ℚ) / 32) ((1 : ℚ) / 8)⟩

private def lowRow8Cell4RootTree : Subdivision :=
.vertical ((7 : ℚ) / 64)
  (.horizontal ((15 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((15 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow8Cell4RootTree_certified :
    certifySubdivision 12 64 32 lowRow8Cell4RootRectangle
      CertificateObjective.endpointExpression lowRow8Cell4RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow8Cell4Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow8Cell4RootRectangle) (tree := lowRow8Cell4RootTree)
  · norm_num [lowRow8Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell4RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow8Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell4RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow8Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell4RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow8Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow8Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow8Cell4RootTree_certified

private def lowRow8Cell5RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 64) ((1 : ℚ) / 8),
    RatBall.ofBounds ((1 : ℚ) / 8) ((5 : ℚ) / 32)⟩

private def lowRow8Cell5RootTree : Subdivision :=
.vertical ((9 : ℚ) / 64)
  (.horizontal ((15 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((15 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow8Cell5RootTree_certified :
    certifySubdivision 12 64 32 lowRow8Cell5RootRectangle
      CertificateObjective.endpointExpression lowRow8Cell5RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow8Cell5Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow8Cell5RootRectangle) (tree := lowRow8Cell5RootTree)
  · norm_num [lowRow8Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell5RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow8Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell5RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow8Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell5RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow8Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow8Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow8Cell5RootTree_certified

private def lowRow8Cell6RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 64) ((1 : ℚ) / 8),
    RatBall.ofBounds ((5 : ℚ) / 32) ((3 : ℚ) / 16)⟩

private def lowRow8Cell6RootTree : Subdivision :=
.horizontal ((15 : ℚ) / 128)
  (.vertical ((11 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((11 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow8Cell6RootTree_certified :
    certifySubdivision 12 64 32 lowRow8Cell6RootRectangle
      CertificateObjective.endpointExpression lowRow8Cell6RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow8Cell6Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow8Cell6RootRectangle) (tree := lowRow8Cell6RootTree)
  · norm_num [lowRow8Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell6RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow8Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell6RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow8Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell6RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow8Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow8Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow8Cell6RootTree_certified

end Frankl
