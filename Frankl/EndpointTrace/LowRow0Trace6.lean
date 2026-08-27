import Frankl.EndpointCertificate

namespace Frankl

private def lowRow0Cell3RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((1 : ℚ) / 16) ((3 : ℚ) / 32)⟩

private def lowRow0Cell3RootTree : Subdivision :=
.vertical ((5 : ℚ) / 64)
  (.vertical ((9 : ℚ) / 128)
  (.vertical ((17 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((19 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((11 : ℚ) / 128)
  (.vertical ((21 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((23 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow0Cell3RootTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell3RootRectangle
      CertificateObjective.endpointExpression lowRow0Cell3RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell3Root_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((1 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell3RootRectangle) (tree := lowRow0Cell3RootTree)
  · norm_num [lowRow0Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell3RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell3RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell3RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell3RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell3RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell3RootTree_certified

private def lowRow0Cell4RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((3 : ℚ) / 32) ((1 : ℚ) / 8)⟩

private def lowRow0Cell4RootTree : Subdivision :=
.vertical ((7 : ℚ) / 64)
  (.vertical ((13 : ℚ) / 128)
  (.vertical ((25 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((27 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((15 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow0Cell4RootTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell4RootRectangle
      CertificateObjective.endpointExpression lowRow0Cell4RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell4Root_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell4RootRectangle) (tree := lowRow0Cell4RootTree)
  · norm_num [lowRow0Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell4RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell4RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell4RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell4RootTree_certified

private def lowRow0Cell5RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((1 : ℚ) / 8) ((5 : ℚ) / 32)⟩

private def lowRow0Cell5RootTree : Subdivision :=
.vertical ((9 : ℚ) / 64)
  (.vertical ((17 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((19 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow0Cell5RootTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell5RootRectangle
      CertificateObjective.endpointExpression lowRow0Cell5RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell5Root_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell5RootRectangle) (tree := lowRow0Cell5RootTree)
  · norm_num [lowRow0Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell5RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell5RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell5RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell5RootTree_certified

private def lowRow0Cell6RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((5 : ℚ) / 32) ((3 : ℚ) / 16)⟩

private def lowRow0Cell6RootTree : Subdivision :=
.vertical ((11 : ℚ) / 64)
  (.vertical ((21 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((23 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow0Cell6RootTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell6RootRectangle
      CertificateObjective.endpointExpression lowRow0Cell6RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell6Root_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell6RootRectangle) (tree := lowRow0Cell6RootTree)
  · norm_num [lowRow0Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell6RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell6RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell6RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell6RootTree_certified

private def lowRow0Cell7RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((3 : ℚ) / 16) ((7 : ℚ) / 32)⟩

private def lowRow0Cell7RootTree : Subdivision :=
.vertical ((13 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow0Cell7RootTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell7RootRectangle
      CertificateObjective.endpointExpression lowRow0Cell7RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell7Root_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell7RootRectangle) (tree := lowRow0Cell7RootTree)
  · norm_num [lowRow0Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell7RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell7RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell7RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell7RootTree_certified

private def lowRow0Cell8RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((7 : ℚ) / 32) ((1 : ℚ) / 4)⟩

private def lowRow0Cell8RootTree : Subdivision :=
.vertical ((15 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow0Cell8RootTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell8RootRectangle
      CertificateObjective.endpointExpression lowRow0Cell8RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell8Root_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell8RootRectangle) (tree := lowRow0Cell8RootTree)
  · norm_num [lowRow0Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell8RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell8RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell8RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell8RootTree_certified

private def lowRow0Cell9RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((1 : ℚ) / 4) ((9 : ℚ) / 32)⟩

private def lowRow0Cell9RootTree : Subdivision :=
.vertical ((17 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow0Cell9RootTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell9RootRectangle
      CertificateObjective.endpointExpression lowRow0Cell9RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell9Root_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell9RootRectangle) (tree := lowRow0Cell9RootTree)
  · norm_num [lowRow0Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell9RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell9RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell9RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell9RootTree_certified

end Frankl
