import Frankl.EndpointCertificate

namespace Frankl

private def lowRow15Cell0RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 32) ((15 : ℚ) / 64),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow15Cell0RootTree : Subdivision :=
.horizontal ((29 : ℚ) / 128)
  (.horizontal ((57 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((59 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow15Cell0RootTree_certified :
    certifySubdivision 12 64 32 lowRow15Cell0RootRectangle
      CertificateObjective.endpointExpression lowRow15Cell0RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow15Cell0Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow15Cell0RootRectangle) (tree := lowRow15Cell0RootTree)
  · norm_num [lowRow15Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell0RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow15Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell0RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow15Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell0RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow15Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow15Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow15Cell0RootTree_certified

private def lowRow15Cell1RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 32) ((15 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 32)⟩

private def lowRow15Cell1RootTree : Subdivision :=
.vertical ((129 : ℚ) / 8000)
  (.vertical ((137 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((29 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow15Cell1RootTree_certified :
    certifySubdivision 12 64 32 lowRow15Cell1RootRectangle
      CertificateObjective.endpointExpression lowRow15Cell1RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow15Cell1Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow15Cell1RootRectangle) (tree := lowRow15Cell1RootTree)
  · norm_num [lowRow15Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell1RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow15Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell1RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow15Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell1RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow15Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow15Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow15Cell1RootTree_certified

private def lowRow15Cell2RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 32) ((15 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 32) ((1 : ℚ) / 16)⟩

private def lowRow15Cell2RootTree : Subdivision :=
.vertical ((3 : ℚ) / 64)
  (.horizontal ((29 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((29 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow15Cell2RootTree_certified :
    certifySubdivision 12 64 32 lowRow15Cell2RootRectangle
      CertificateObjective.endpointExpression lowRow15Cell2RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow15Cell2Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow15Cell2RootRectangle) (tree := lowRow15Cell2RootTree)
  · norm_num [lowRow15Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell2RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow15Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell2RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow15Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell2RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow15Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow15Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow15Cell2RootTree_certified

private def lowRow15Cell3RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 32) ((15 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 16) ((3 : ℚ) / 32)⟩

private def lowRow15Cell3RootTree : Subdivision :=
.vertical ((5 : ℚ) / 64)
  (.horizontal ((29 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((29 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow15Cell3RootTree_certified :
    certifySubdivision 12 64 32 lowRow15Cell3RootRectangle
      CertificateObjective.endpointExpression lowRow15Cell3RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow15Cell3Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow15Cell3RootRectangle) (tree := lowRow15Cell3RootTree)
  · norm_num [lowRow15Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell3RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow15Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell3RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow15Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell3RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow15Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow15Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow15Cell3RootTree_certified

private def lowRow15Cell4RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 32) ((15 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 32) ((1 : ℚ) / 8)⟩

private def lowRow15Cell4RootTree : Subdivision :=
.horizontal ((29 : ℚ) / 128)
  (.vertical ((7 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((7 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow15Cell4RootTree_certified :
    certifySubdivision 12 64 32 lowRow15Cell4RootRectangle
      CertificateObjective.endpointExpression lowRow15Cell4RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow15Cell4Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow15Cell4RootRectangle) (tree := lowRow15Cell4RootTree)
  · norm_num [lowRow15Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell4RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow15Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell4RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow15Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell4RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow15Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow15Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow15Cell4RootTree_certified

private def lowRow15Cell5RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 32) ((15 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 8) ((5 : ℚ) / 32)⟩

private def lowRow15Cell5RootTree : Subdivision :=
.horizontal ((29 : ℚ) / 128)
  (.vertical ((9 : ℚ) / 64)
  (.horizontal ((57 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((57 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((9 : ℚ) / 64)
  (.horizontal ((59 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((59 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow15Cell5RootTree_certified :
    certifySubdivision 12 64 32 lowRow15Cell5RootRectangle
      CertificateObjective.endpointExpression lowRow15Cell5RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow15Cell5Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow15Cell5RootRectangle) (tree := lowRow15Cell5RootTree)
  · norm_num [lowRow15Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell5RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow15Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell5RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow15Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell5RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow15Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow15Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow15Cell5RootTree_certified

end Frankl
