import Frankl.EndpointCertificate

namespace Frankl

private def lowRow4Cell5RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 64) ((1 : ℚ) / 16),
    RatBall.ofBounds ((1 : ℚ) / 8) ((5 : ℚ) / 32)⟩

private def lowRow4Cell5RootTree : Subdivision :=
.vertical ((9 : ℚ) / 64)
  (.horizontal ((7 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((7 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow4Cell5RootTree_certified :
    certifySubdivision 12 64 32 lowRow4Cell5RootRectangle
      CertificateObjective.endpointExpression lowRow4Cell5RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow4Cell5Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow4Cell5RootRectangle) (tree := lowRow4Cell5RootTree)
  · norm_num [lowRow4Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell5RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow4Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell5RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow4Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell5RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow4Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow4Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow4Cell5RootTree_certified

private def lowRow4Cell6RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 64) ((1 : ℚ) / 16),
    RatBall.ofBounds ((5 : ℚ) / 32) ((3 : ℚ) / 16)⟩

private def lowRow4Cell6RootTree : Subdivision :=
.horizontal ((7 : ℚ) / 128)
  (.leaf .interval)
  (.vertical ((11 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow4Cell6RootTree_certified :
    certifySubdivision 12 64 32 lowRow4Cell6RootRectangle
      CertificateObjective.endpointExpression lowRow4Cell6RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow4Cell6Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow4Cell6RootRectangle) (tree := lowRow4Cell6RootTree)
  · norm_num [lowRow4Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell6RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow4Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell6RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow4Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell6RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow4Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow4Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow4Cell6RootTree_certified

private def lowRow4Cell7RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 64) ((1 : ℚ) / 16),
    RatBall.ofBounds ((3 : ℚ) / 16) ((7 : ℚ) / 32)⟩

private def lowRow4Cell7RootTree : Subdivision :=
.horizontal ((7 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow4Cell7RootTree_certified :
    certifySubdivision 12 64 32 lowRow4Cell7RootRectangle
      CertificateObjective.endpointExpression lowRow4Cell7RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow4Cell7Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow4Cell7RootRectangle) (tree := lowRow4Cell7RootTree)
  · norm_num [lowRow4Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell7RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow4Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell7RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow4Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell7RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow4Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow4Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow4Cell7RootTree_certified

private def lowRow4Cell8RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 64) ((1 : ℚ) / 16),
    RatBall.ofBounds ((7 : ℚ) / 32) ((1 : ℚ) / 4)⟩

private def lowRow4Cell8RootTree : Subdivision :=
.horizontal ((7 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow4Cell8RootTree_certified :
    certifySubdivision 12 64 32 lowRow4Cell8RootRectangle
      CertificateObjective.endpointExpression lowRow4Cell8RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow4Cell8Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow4Cell8RootRectangle) (tree := lowRow4Cell8RootTree)
  · norm_num [lowRow4Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell8RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow4Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell8RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow4Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell8RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow4Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow4Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow4Cell8RootTree_certified

private def lowRow4Cell9RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 64) ((1 : ℚ) / 16),
    RatBall.ofBounds ((1 : ℚ) / 4) ((9 : ℚ) / 32)⟩

private def lowRow4Cell9RootTree : Subdivision :=
.horizontal ((7 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow4Cell9RootTree_certified :
    certifySubdivision 12 64 32 lowRow4Cell9RootRectangle
      CertificateObjective.endpointExpression lowRow4Cell9RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow4Cell9Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow4Cell9RootRectangle) (tree := lowRow4Cell9RootTree)
  · norm_num [lowRow4Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell9RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow4Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell9RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow4Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell9RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow4Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow4Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow4Cell9RootTree_certified

private def lowRow4Cell10RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 64) ((1 : ℚ) / 16),
    RatBall.ofBounds ((9 : ℚ) / 32) ((5 : ℚ) / 16)⟩

private def lowRow4Cell10RootTree : Subdivision :=
.leaf .interval

private theorem lowRow4Cell10RootTree_certified :
    certifySubdivision 12 64 32 lowRow4Cell10RootRectangle
      CertificateObjective.endpointExpression lowRow4Cell10RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow4Cell10Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow4Cell10RootRectangle) (tree := lowRow4Cell10RootTree)
  · norm_num [lowRow4Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell10RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow4Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell10RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow4Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell10RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow4Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow4Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow4Cell10RootTree_certified

private def lowRow4Cell11RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 64) ((1 : ℚ) / 16),
    RatBall.ofBounds ((5 : ℚ) / 16) ((11 : ℚ) / 32)⟩

private def lowRow4Cell11RootTree : Subdivision :=
.leaf .interval

private theorem lowRow4Cell11RootTree_certified :
    certifySubdivision 12 64 32 lowRow4Cell11RootRectangle
      CertificateObjective.endpointExpression lowRow4Cell11RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow4Cell11Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow4Cell11RootRectangle) (tree := lowRow4Cell11RootTree)
  · norm_num [lowRow4Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell11RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow4Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell11RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow4Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell11RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow4Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow4Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow4Cell11RootTree_certified

private def lowRow4Cell12RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 64) ((1 : ℚ) / 16),
    RatBall.ofBounds ((11 : ℚ) / 32) ((3 : ℚ) / 8)⟩

private def lowRow4Cell12RootTree : Subdivision :=
.leaf .interval

private theorem lowRow4Cell12RootTree_certified :
    certifySubdivision 12 64 32 lowRow4Cell12RootRectangle
      CertificateObjective.endpointExpression lowRow4Cell12RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow4Cell12Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow4Cell12RootRectangle) (tree := lowRow4Cell12RootTree)
  · norm_num [lowRow4Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell12RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow4Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell12RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow4Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell12RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow4Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow4Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow4Cell12RootTree_certified

private def lowRow4Cell13RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 64) ((1 : ℚ) / 16),
    RatBall.ofBounds ((3 : ℚ) / 8) ((13 : ℚ) / 32)⟩

private def lowRow4Cell13RootTree : Subdivision :=
.leaf .interval

private theorem lowRow4Cell13RootTree_certified :
    certifySubdivision 12 64 32 lowRow4Cell13RootRectangle
      CertificateObjective.endpointExpression lowRow4Cell13RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow4Cell13Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow4Cell13RootRectangle) (tree := lowRow4Cell13RootTree)
  · norm_num [lowRow4Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell13RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow4Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell13RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow4Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell13RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow4Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow4Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow4Cell13RootTree_certified

private def lowRow4Cell14RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 64) ((1 : ℚ) / 16),
    RatBall.ofBounds ((13 : ℚ) / 32) ((7 : ℚ) / 16)⟩

private def lowRow4Cell14RootTree : Subdivision :=
.leaf .interval

private theorem lowRow4Cell14RootTree_certified :
    certifySubdivision 12 64 32 lowRow4Cell14RootRectangle
      CertificateObjective.endpointExpression lowRow4Cell14RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow4Cell14Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow4Cell14RootRectangle) (tree := lowRow4Cell14RootTree)
  · norm_num [lowRow4Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell14RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow4Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell14RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow4Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell14RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow4Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow4Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow4Cell14RootTree_certified

private def lowRow4Cell15RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 64) ((1 : ℚ) / 16),
    RatBall.ofBounds ((7 : ℚ) / 16) ((15 : ℚ) / 32)⟩

private def lowRow4Cell15RootTree : Subdivision :=
.leaf .interval

private theorem lowRow4Cell15RootTree_certified :
    certifySubdivision 12 64 32 lowRow4Cell15RootRectangle
      CertificateObjective.endpointExpression lowRow4Cell15RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow4Cell15Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow4Cell15RootRectangle) (tree := lowRow4Cell15RootTree)
  · norm_num [lowRow4Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell15RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow4Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell15RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow4Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell15RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow4Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow4Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow4Cell15RootTree_certified

private def lowRow4Cell16RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 64) ((1 : ℚ) / 16),
    RatBall.ofBounds ((15 : ℚ) / 32) ((1 : ℚ) / 2)⟩

private def lowRow4Cell16RootTree : Subdivision :=
.leaf .interval

private theorem lowRow4Cell16RootTree_certified :
    certifySubdivision 12 64 32 lowRow4Cell16RootRectangle
      CertificateObjective.endpointExpression lowRow4Cell16RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow4Cell16Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 16))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow4Cell16RootRectangle) (tree := lowRow4Cell16RootTree)
  · norm_num [lowRow4Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell16RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow4Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell16RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow4Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow4Cell16RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow4Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow4Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow4Cell16RootTree_certified

end Frankl
