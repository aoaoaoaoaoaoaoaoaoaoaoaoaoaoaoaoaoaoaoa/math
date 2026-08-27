import Frankl.EndpointCertificate

namespace Frankl

private def lowRow5Cell5RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 16) ((5 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 8) ((5 : ℚ) / 32)⟩

private def lowRow5Cell5RootTree : Subdivision :=
.vertical ((9 : ℚ) / 64)
  (.horizontal ((9 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((9 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow5Cell5RootTree_certified :
    certifySubdivision 12 64 32 lowRow5Cell5RootRectangle
      CertificateObjective.endpointExpression lowRow5Cell5RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow5Cell5Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow5Cell5RootRectangle) (tree := lowRow5Cell5RootTree)
  · norm_num [lowRow5Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell5RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow5Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell5RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow5Cell5RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell5RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow5Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow5Cell5RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow5Cell5RootTree_certified

private def lowRow5Cell6RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 16) ((5 : ℚ) / 64),
    RatBall.ofBounds ((5 : ℚ) / 32) ((3 : ℚ) / 16)⟩

private def lowRow5Cell6RootTree : Subdivision :=
.horizontal ((9 : ℚ) / 128)
  (.vertical ((11 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((11 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow5Cell6RootTree_certified :
    certifySubdivision 12 64 32 lowRow5Cell6RootRectangle
      CertificateObjective.endpointExpression lowRow5Cell6RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow5Cell6Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow5Cell6RootRectangle) (tree := lowRow5Cell6RootTree)
  · norm_num [lowRow5Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell6RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow5Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell6RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow5Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell6RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow5Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow5Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow5Cell6RootTree_certified

private def lowRow5Cell7RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 16) ((5 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 16) ((7 : ℚ) / 32)⟩

private def lowRow5Cell7RootTree : Subdivision :=
.horizontal ((9 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow5Cell7RootTree_certified :
    certifySubdivision 12 64 32 lowRow5Cell7RootRectangle
      CertificateObjective.endpointExpression lowRow5Cell7RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow5Cell7Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow5Cell7RootRectangle) (tree := lowRow5Cell7RootTree)
  · norm_num [lowRow5Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell7RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow5Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell7RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow5Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell7RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow5Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow5Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow5Cell7RootTree_certified

private def lowRow5Cell8RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 16) ((5 : ℚ) / 64),
    RatBall.ofBounds ((7 : ℚ) / 32) ((1 : ℚ) / 4)⟩

private def lowRow5Cell8RootTree : Subdivision :=
.horizontal ((9 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow5Cell8RootTree_certified :
    certifySubdivision 12 64 32 lowRow5Cell8RootRectangle
      CertificateObjective.endpointExpression lowRow5Cell8RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow5Cell8Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow5Cell8RootRectangle) (tree := lowRow5Cell8RootTree)
  · norm_num [lowRow5Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell8RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow5Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell8RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow5Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell8RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow5Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow5Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow5Cell8RootTree_certified

private def lowRow5Cell9RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 16) ((5 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 4) ((9 : ℚ) / 32)⟩

private def lowRow5Cell9RootTree : Subdivision :=
.horizontal ((9 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow5Cell9RootTree_certified :
    certifySubdivision 12 64 32 lowRow5Cell9RootRectangle
      CertificateObjective.endpointExpression lowRow5Cell9RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow5Cell9Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow5Cell9RootRectangle) (tree := lowRow5Cell9RootTree)
  · norm_num [lowRow5Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell9RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow5Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell9RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow5Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell9RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow5Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow5Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow5Cell9RootTree_certified

private def lowRow5Cell10RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 16) ((5 : ℚ) / 64),
    RatBall.ofBounds ((9 : ℚ) / 32) ((5 : ℚ) / 16)⟩

private def lowRow5Cell10RootTree : Subdivision :=
.leaf .interval

private theorem lowRow5Cell10RootTree_certified :
    certifySubdivision 12 64 32 lowRow5Cell10RootRectangle
      CertificateObjective.endpointExpression lowRow5Cell10RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow5Cell10Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow5Cell10RootRectangle) (tree := lowRow5Cell10RootTree)
  · norm_num [lowRow5Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell10RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow5Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell10RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow5Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell10RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow5Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow5Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow5Cell10RootTree_certified

private def lowRow5Cell11RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 16) ((5 : ℚ) / 64),
    RatBall.ofBounds ((5 : ℚ) / 16) ((11 : ℚ) / 32)⟩

private def lowRow5Cell11RootTree : Subdivision :=
.leaf .interval

private theorem lowRow5Cell11RootTree_certified :
    certifySubdivision 12 64 32 lowRow5Cell11RootRectangle
      CertificateObjective.endpointExpression lowRow5Cell11RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow5Cell11Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow5Cell11RootRectangle) (tree := lowRow5Cell11RootTree)
  · norm_num [lowRow5Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell11RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow5Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell11RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow5Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell11RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow5Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow5Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow5Cell11RootTree_certified

private def lowRow5Cell12RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 16) ((5 : ℚ) / 64),
    RatBall.ofBounds ((11 : ℚ) / 32) ((3 : ℚ) / 8)⟩

private def lowRow5Cell12RootTree : Subdivision :=
.leaf .interval

private theorem lowRow5Cell12RootTree_certified :
    certifySubdivision 12 64 32 lowRow5Cell12RootRectangle
      CertificateObjective.endpointExpression lowRow5Cell12RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow5Cell12Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow5Cell12RootRectangle) (tree := lowRow5Cell12RootTree)
  · norm_num [lowRow5Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell12RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow5Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell12RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow5Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell12RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow5Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow5Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow5Cell12RootTree_certified

private def lowRow5Cell13RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 16) ((5 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 8) ((13 : ℚ) / 32)⟩

private def lowRow5Cell13RootTree : Subdivision :=
.leaf .interval

private theorem lowRow5Cell13RootTree_certified :
    certifySubdivision 12 64 32 lowRow5Cell13RootRectangle
      CertificateObjective.endpointExpression lowRow5Cell13RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow5Cell13Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow5Cell13RootRectangle) (tree := lowRow5Cell13RootTree)
  · norm_num [lowRow5Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell13RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow5Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell13RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow5Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell13RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow5Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow5Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow5Cell13RootTree_certified

private def lowRow5Cell14RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 16) ((5 : ℚ) / 64),
    RatBall.ofBounds ((13 : ℚ) / 32) ((7 : ℚ) / 16)⟩

private def lowRow5Cell14RootTree : Subdivision :=
.leaf .interval

private theorem lowRow5Cell14RootTree_certified :
    certifySubdivision 12 64 32 lowRow5Cell14RootRectangle
      CertificateObjective.endpointExpression lowRow5Cell14RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow5Cell14Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow5Cell14RootRectangle) (tree := lowRow5Cell14RootTree)
  · norm_num [lowRow5Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell14RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow5Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell14RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow5Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell14RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow5Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow5Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow5Cell14RootTree_certified

private def lowRow5Cell15RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 16) ((5 : ℚ) / 64),
    RatBall.ofBounds ((7 : ℚ) / 16) ((15 : ℚ) / 32)⟩

private def lowRow5Cell15RootTree : Subdivision :=
.leaf .interval

private theorem lowRow5Cell15RootTree_certified :
    certifySubdivision 12 64 32 lowRow5Cell15RootRectangle
      CertificateObjective.endpointExpression lowRow5Cell15RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow5Cell15Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow5Cell15RootRectangle) (tree := lowRow5Cell15RootTree)
  · norm_num [lowRow5Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell15RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow5Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell15RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow5Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell15RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow5Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow5Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow5Cell15RootTree_certified

private def lowRow5Cell16RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 16) ((5 : ℚ) / 64),
    RatBall.ofBounds ((15 : ℚ) / 32) ((1 : ℚ) / 2)⟩

private def lowRow5Cell16RootTree : Subdivision :=
.leaf .interval

private theorem lowRow5Cell16RootTree_certified :
    certifySubdivision 12 64 32 lowRow5Cell16RootRectangle
      CertificateObjective.endpointExpression lowRow5Cell16RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow5Cell16Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 64))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow5Cell16RootRectangle) (tree := lowRow5Cell16RootTree)
  · norm_num [lowRow5Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell16RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow5Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell16RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow5Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow5Cell16RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow5Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow5Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow5Cell16RootTree_certified

end Frankl
