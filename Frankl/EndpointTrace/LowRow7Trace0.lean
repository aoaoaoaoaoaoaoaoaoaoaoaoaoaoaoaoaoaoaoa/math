import Frankl.EndpointCertificate

namespace Frankl

private def lowRow7Cell0RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 32) ((7 : ℚ) / 64),
    RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000)⟩

private def lowRow7Cell0RootTree : Subdivision :=
.horizontal ((13 : ℚ) / 128)
  (.horizontal ((25 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((27 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow7Cell0RootTree_certified :
    certifySubdivision 12 64 32 lowRow7Cell0RootRectangle
      CertificateObjective.endpointExpression lowRow7Cell0RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow7Cell0Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((0 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1000)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow7Cell0RootRectangle) (tree := lowRow7Cell0RootTree)
  · norm_num [lowRow7Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell0RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow7Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell0RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow7Cell0RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell0RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow7Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow7Cell0RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow7Cell0RootTree_certified

private def lowRow7Cell1RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 32) ((7 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 32)⟩

private def lowRow7Cell1RootTree : Subdivision :=
.vertical ((129 : ℚ) / 8000)
  (.vertical ((137 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((379 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow7Cell1RootTree_certified :
    certifySubdivision 12 64 32 lowRow7Cell1RootRectangle
      CertificateObjective.endpointExpression lowRow7Cell1RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow7Cell1Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 1000) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow7Cell1RootRectangle) (tree := lowRow7Cell1RootTree)
  · norm_num [lowRow7Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell1RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow7Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell1RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow7Cell1RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell1RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow7Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow7Cell1RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow7Cell1RootTree_certified

private def lowRow7Cell2RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 32) ((7 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 32) ((1 : ℚ) / 16)⟩

private def lowRow7Cell2RootTree : Subdivision :=
.vertical ((3 : ℚ) / 64)
  (.horizontal ((13 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((13 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow7Cell2RootTree_certified :
    certifySubdivision 12 64 32 lowRow7Cell2RootRectangle
      CertificateObjective.endpointExpression lowRow7Cell2RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow7Cell2Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow7Cell2RootRectangle) (tree := lowRow7Cell2RootTree)
  · norm_num [lowRow7Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell2RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow7Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell2RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow7Cell2RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell2RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow7Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow7Cell2RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow7Cell2RootTree_certified

private def lowRow7Cell3RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 32) ((7 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 16) ((3 : ℚ) / 32)⟩

private def lowRow7Cell3RootTree : Subdivision :=
.vertical ((5 : ℚ) / 64)
  (.horizontal ((13 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((13 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow7Cell3RootTree_certified :
    certifySubdivision 12 64 32 lowRow7Cell3RootRectangle
      CertificateObjective.endpointExpression lowRow7Cell3RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow7Cell3Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow7Cell3RootRectangle) (tree := lowRow7Cell3RootTree)
  · norm_num [lowRow7Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell3RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow7Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell3RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow7Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell3RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow7Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow7Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow7Cell3RootTree_certified

private def lowRow7Cell4RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 32) ((7 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 32) ((1 : ℚ) / 8)⟩

private def lowRow7Cell4RootTree : Subdivision :=
.vertical ((7 : ℚ) / 64)
  (.horizontal ((13 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((13 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow7Cell4RootTree_certified :
    certifySubdivision 12 64 32 lowRow7Cell4RootRectangle
      CertificateObjective.endpointExpression lowRow7Cell4RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow7Cell4Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow7Cell4RootRectangle) (tree := lowRow7Cell4RootTree)
  · norm_num [lowRow7Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell4RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow7Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell4RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow7Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell4RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow7Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow7Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow7Cell4RootTree_certified

private def lowRow7Cell5RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 32) ((7 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 8) ((5 : ℚ) / 32)⟩

private def lowRow7Cell5RootTree : Subdivision :=
.vertical ((9 : ℚ) / 64)
  (.horizontal ((13 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((13 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow7Cell5RootTree_certified :
    certifySubdivision 12 64 32 lowRow7Cell5RootRectangle
      CertificateObjective.endpointExpression lowRow7Cell5RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow7Cell5Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow7Cell5RootRectangle) (tree := lowRow7Cell5RootTree)
  · norm_num [lowRow7Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell5RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow7Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell5RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow7Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell5RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow7Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow7Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow7Cell5RootTree_certified

private def lowRow7Cell6RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 32) ((7 : ℚ) / 64),
    RatBall.ofBounds ((5 : ℚ) / 32) ((3 : ℚ) / 16)⟩

private def lowRow7Cell6RootTree : Subdivision :=
.horizontal ((13 : ℚ) / 128)
  (.vertical ((11 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((11 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow7Cell6RootTree_certified :
    certifySubdivision 12 64 32 lowRow7Cell6RootRectangle
      CertificateObjective.endpointExpression lowRow7Cell6RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow7Cell6Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow7Cell6RootRectangle) (tree := lowRow7Cell6RootTree)
  · norm_num [lowRow7Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell6RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow7Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell6RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow7Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell6RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow7Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow7Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow7Cell6RootTree_certified

end Frankl
