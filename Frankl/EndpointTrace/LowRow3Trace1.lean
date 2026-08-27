import Frankl.EndpointCertificate

namespace Frankl

private def lowRow3Cell4RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 32) ((3 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 32) ((1 : ℚ) / 8)⟩

private def lowRow3Cell4RootTree : Subdivision :=
.vertical ((7 : ℚ) / 64)
  (.horizontal ((5 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((5 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow3Cell4RootTree_certified :
    certifySubdivision 12 64 32 lowRow3Cell4RootRectangle
      CertificateObjective.endpointExpression lowRow3Cell4RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow3Cell4Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow3Cell4RootRectangle) (tree := lowRow3Cell4RootTree)
  · norm_num [lowRow3Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell4RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow3Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell4RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow3Cell4RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell4RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow3Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow3Cell4RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow3Cell4RootTree_certified

private def lowRow3Cell5RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 32) ((3 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 8) ((5 : ℚ) / 32)⟩

private def lowRow3Cell5RootTree : Subdivision :=
.horizontal ((5 : ℚ) / 128)
  (.vertical ((9 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((9 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow3Cell5RootTree_certified :
    certifySubdivision 12 64 32 lowRow3Cell5RootRectangle
      CertificateObjective.endpointExpression lowRow3Cell5RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow3Cell5Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow3Cell5RootRectangle) (tree := lowRow3Cell5RootTree)
  · norm_num [lowRow3Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell5RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow3Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell5RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow3Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell5RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow3Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow3Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow3Cell5RootTree_certified

private def lowRow3Cell6RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 32) ((3 : ℚ) / 64),
    RatBall.ofBounds ((5 : ℚ) / 32) ((3 : ℚ) / 16)⟩

private def lowRow3Cell6RootTree : Subdivision :=
.horizontal ((5 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow3Cell6RootTree_certified :
    certifySubdivision 12 64 32 lowRow3Cell6RootRectangle
      CertificateObjective.endpointExpression lowRow3Cell6RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow3Cell6Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow3Cell6RootRectangle) (tree := lowRow3Cell6RootTree)
  · norm_num [lowRow3Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell6RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow3Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell6RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow3Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell6RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow3Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow3Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow3Cell6RootTree_certified

private def lowRow3Cell7RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 32) ((3 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 16) ((7 : ℚ) / 32)⟩

private def lowRow3Cell7RootTree : Subdivision :=
.horizontal ((5 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow3Cell7RootTree_certified :
    certifySubdivision 12 64 32 lowRow3Cell7RootRectangle
      CertificateObjective.endpointExpression lowRow3Cell7RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow3Cell7Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow3Cell7RootRectangle) (tree := lowRow3Cell7RootTree)
  · norm_num [lowRow3Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell7RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow3Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell7RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow3Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell7RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow3Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow3Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow3Cell7RootTree_certified

private def lowRow3Cell8RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 32) ((3 : ℚ) / 64),
    RatBall.ofBounds ((7 : ℚ) / 32) ((1 : ℚ) / 4)⟩

private def lowRow3Cell8RootTree : Subdivision :=
.horizontal ((5 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow3Cell8RootTree_certified :
    certifySubdivision 12 64 32 lowRow3Cell8RootRectangle
      CertificateObjective.endpointExpression lowRow3Cell8RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow3Cell8Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow3Cell8RootRectangle) (tree := lowRow3Cell8RootTree)
  · norm_num [lowRow3Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell8RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow3Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell8RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow3Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell8RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow3Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow3Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow3Cell8RootTree_certified

private def lowRow3Cell9RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 32) ((3 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 4) ((9 : ℚ) / 32)⟩

private def lowRow3Cell9RootTree : Subdivision :=
.leaf .interval

private theorem lowRow3Cell9RootTree_certified :
    certifySubdivision 12 64 32 lowRow3Cell9RootRectangle
      CertificateObjective.endpointExpression lowRow3Cell9RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow3Cell9Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow3Cell9RootRectangle) (tree := lowRow3Cell9RootTree)
  · norm_num [lowRow3Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell9RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow3Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell9RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow3Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell9RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow3Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow3Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow3Cell9RootTree_certified

private def lowRow3Cell10RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 32) ((3 : ℚ) / 64),
    RatBall.ofBounds ((9 : ℚ) / 32) ((5 : ℚ) / 16)⟩

private def lowRow3Cell10RootTree : Subdivision :=
.leaf .interval

private theorem lowRow3Cell10RootTree_certified :
    certifySubdivision 12 64 32 lowRow3Cell10RootRectangle
      CertificateObjective.endpointExpression lowRow3Cell10RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow3Cell10Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow3Cell10RootRectangle) (tree := lowRow3Cell10RootTree)
  · norm_num [lowRow3Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell10RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow3Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell10RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow3Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell10RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow3Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow3Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow3Cell10RootTree_certified

private def lowRow3Cell11RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 32) ((3 : ℚ) / 64),
    RatBall.ofBounds ((5 : ℚ) / 16) ((11 : ℚ) / 32)⟩

private def lowRow3Cell11RootTree : Subdivision :=
.leaf .interval

private theorem lowRow3Cell11RootTree_certified :
    certifySubdivision 12 64 32 lowRow3Cell11RootRectangle
      CertificateObjective.endpointExpression lowRow3Cell11RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow3Cell11Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow3Cell11RootRectangle) (tree := lowRow3Cell11RootTree)
  · norm_num [lowRow3Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell11RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow3Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell11RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow3Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell11RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow3Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow3Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow3Cell11RootTree_certified

private def lowRow3Cell12RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 32) ((3 : ℚ) / 64),
    RatBall.ofBounds ((11 : ℚ) / 32) ((3 : ℚ) / 8)⟩

private def lowRow3Cell12RootTree : Subdivision :=
.leaf .interval

private theorem lowRow3Cell12RootTree_certified :
    certifySubdivision 12 64 32 lowRow3Cell12RootRectangle
      CertificateObjective.endpointExpression lowRow3Cell12RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow3Cell12Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow3Cell12RootRectangle) (tree := lowRow3Cell12RootTree)
  · norm_num [lowRow3Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell12RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow3Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell12RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow3Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell12RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow3Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow3Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow3Cell12RootTree_certified

private def lowRow3Cell13RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 32) ((3 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 8) ((13 : ℚ) / 32)⟩

private def lowRow3Cell13RootTree : Subdivision :=
.leaf .interval

private theorem lowRow3Cell13RootTree_certified :
    certifySubdivision 12 64 32 lowRow3Cell13RootRectangle
      CertificateObjective.endpointExpression lowRow3Cell13RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow3Cell13Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow3Cell13RootRectangle) (tree := lowRow3Cell13RootTree)
  · norm_num [lowRow3Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell13RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow3Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell13RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow3Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell13RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow3Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow3Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow3Cell13RootTree_certified

private def lowRow3Cell14RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 32) ((3 : ℚ) / 64),
    RatBall.ofBounds ((13 : ℚ) / 32) ((7 : ℚ) / 16)⟩

private def lowRow3Cell14RootTree : Subdivision :=
.leaf .interval

private theorem lowRow3Cell14RootTree_certified :
    certifySubdivision 12 64 32 lowRow3Cell14RootRectangle
      CertificateObjective.endpointExpression lowRow3Cell14RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow3Cell14Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow3Cell14RootRectangle) (tree := lowRow3Cell14RootTree)
  · norm_num [lowRow3Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell14RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow3Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell14RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow3Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell14RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow3Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow3Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow3Cell14RootTree_certified

private def lowRow3Cell15RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 32) ((3 : ℚ) / 64),
    RatBall.ofBounds ((7 : ℚ) / 16) ((15 : ℚ) / 32)⟩

private def lowRow3Cell15RootTree : Subdivision :=
.leaf .interval

private theorem lowRow3Cell15RootTree_certified :
    certifySubdivision 12 64 32 lowRow3Cell15RootRectangle
      CertificateObjective.endpointExpression lowRow3Cell15RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow3Cell15Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow3Cell15RootRectangle) (tree := lowRow3Cell15RootTree)
  · norm_num [lowRow3Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell15RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow3Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell15RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow3Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell15RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow3Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow3Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow3Cell15RootTree_certified

private def lowRow3Cell16RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 32) ((3 : ℚ) / 64),
    RatBall.ofBounds ((15 : ℚ) / 32) ((1 : ℚ) / 2)⟩

private def lowRow3Cell16RootTree : Subdivision :=
.leaf .interval

private theorem lowRow3Cell16RootTree_certified :
    certifySubdivision 12 64 32 lowRow3Cell16RootRectangle
      CertificateObjective.endpointExpression lowRow3Cell16RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow3Cell16Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 64))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow3Cell16RootRectangle) (tree := lowRow3Cell16RootTree)
  · norm_num [lowRow3Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell16RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow3Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell16RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow3Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow3Cell16RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow3Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow3Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow3Cell16RootTree_certified

end Frankl
