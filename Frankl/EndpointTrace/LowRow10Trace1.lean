import Frankl.EndpointCertificate

namespace Frankl

private def lowRow10Cell6RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((9 : ℚ) / 64) ((5 : ℚ) / 32),
    RatBall.ofBounds ((5 : ℚ) / 32) ((3 : ℚ) / 16)⟩

private def lowRow10Cell6RootTree : Subdivision :=
.horizontal ((19 : ℚ) / 128)
  (.vertical ((11 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((11 : ℚ) / 64)
  (.horizontal ((39 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))

private theorem lowRow10Cell6RootTree_certified :
    certifySubdivision 12 64 32 lowRow10Cell6RootRectangle
      CertificateObjective.endpointExpression lowRow10Cell6RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow10Cell6Root_nonneg {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow10Cell6RootRectangle) (tree := lowRow10Cell6RootTree)
  · norm_num [lowRow10Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell6RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow10Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell6RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow10Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell6RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow10Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow10Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow10Cell6RootTree_certified

private def lowRow10Cell7RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((9 : ℚ) / 64) ((5 : ℚ) / 32),
    RatBall.ofBounds ((3 : ℚ) / 16) ((7 : ℚ) / 32)⟩

private def lowRow10Cell7RootTree : Subdivision :=
.horizontal ((19 : ℚ) / 128)
  (.vertical ((13 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((13 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow10Cell7RootTree_certified :
    certifySubdivision 12 64 32 lowRow10Cell7RootRectangle
      CertificateObjective.endpointExpression lowRow10Cell7RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow10Cell7Root_nonneg {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow10Cell7RootRectangle) (tree := lowRow10Cell7RootTree)
  · norm_num [lowRow10Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell7RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow10Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell7RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow10Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell7RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow10Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow10Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow10Cell7RootTree_certified

private def lowRow10Cell8RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((9 : ℚ) / 64) ((5 : ℚ) / 32),
    RatBall.ofBounds ((7 : ℚ) / 32) ((1 : ℚ) / 4)⟩

private def lowRow10Cell8RootTree : Subdivision :=
.horizontal ((19 : ℚ) / 128)
  (.vertical ((15 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((15 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow10Cell8RootTree_certified :
    certifySubdivision 12 64 32 lowRow10Cell8RootRectangle
      CertificateObjective.endpointExpression lowRow10Cell8RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow10Cell8Root_nonneg {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow10Cell8RootRectangle) (tree := lowRow10Cell8RootTree)
  · norm_num [lowRow10Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell8RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow10Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell8RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow10Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell8RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow10Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow10Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow10Cell8RootTree_certified

private def lowRow10Cell9RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((9 : ℚ) / 64) ((5 : ℚ) / 32),
    RatBall.ofBounds ((1 : ℚ) / 4) ((9 : ℚ) / 32)⟩

private def lowRow10Cell9RootTree : Subdivision :=
.horizontal ((19 : ℚ) / 128)
  (.vertical ((17 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((17 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow10Cell9RootTree_certified :
    certifySubdivision 12 64 32 lowRow10Cell9RootRectangle
      CertificateObjective.endpointExpression lowRow10Cell9RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow10Cell9Root_nonneg {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow10Cell9RootRectangle) (tree := lowRow10Cell9RootTree)
  · norm_num [lowRow10Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell9RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow10Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell9RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow10Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell9RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow10Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow10Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow10Cell9RootTree_certified

private def lowRow10Cell10RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((9 : ℚ) / 64) ((5 : ℚ) / 32),
    RatBall.ofBounds ((9 : ℚ) / 32) ((5 : ℚ) / 16)⟩

private def lowRow10Cell10RootTree : Subdivision :=
.horizontal ((19 : ℚ) / 128)
  (.leaf .interval)
  (.vertical ((19 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow10Cell10RootTree_certified :
    certifySubdivision 12 64 32 lowRow10Cell10RootRectangle
      CertificateObjective.endpointExpression lowRow10Cell10RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow10Cell10Root_nonneg {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow10Cell10RootRectangle) (tree := lowRow10Cell10RootTree)
  · norm_num [lowRow10Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell10RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow10Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell10RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow10Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell10RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow10Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow10Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow10Cell10RootTree_certified

private def lowRow10Cell11RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((9 : ℚ) / 64) ((5 : ℚ) / 32),
    RatBall.ofBounds ((5 : ℚ) / 16) ((11 : ℚ) / 32)⟩

private def lowRow10Cell11RootTree : Subdivision :=
.horizontal ((19 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow10Cell11RootTree_certified :
    certifySubdivision 12 64 32 lowRow10Cell11RootRectangle
      CertificateObjective.endpointExpression lowRow10Cell11RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow10Cell11Root_nonneg {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow10Cell11RootRectangle) (tree := lowRow10Cell11RootTree)
  · norm_num [lowRow10Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell11RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow10Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell11RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow10Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell11RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow10Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow10Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow10Cell11RootTree_certified

private def lowRow10Cell12RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((9 : ℚ) / 64) ((5 : ℚ) / 32),
    RatBall.ofBounds ((11 : ℚ) / 32) ((3 : ℚ) / 8)⟩

private def lowRow10Cell12RootTree : Subdivision :=
.horizontal ((19 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow10Cell12RootTree_certified :
    certifySubdivision 12 64 32 lowRow10Cell12RootRectangle
      CertificateObjective.endpointExpression lowRow10Cell12RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow10Cell12Root_nonneg {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow10Cell12RootRectangle) (tree := lowRow10Cell12RootTree)
  · norm_num [lowRow10Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell12RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow10Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell12RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow10Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell12RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow10Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow10Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow10Cell12RootTree_certified

private def lowRow10Cell13RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((9 : ℚ) / 64) ((5 : ℚ) / 32),
    RatBall.ofBounds ((3 : ℚ) / 8) ((13 : ℚ) / 32)⟩

private def lowRow10Cell13RootTree : Subdivision :=
.horizontal ((19 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow10Cell13RootTree_certified :
    certifySubdivision 12 64 32 lowRow10Cell13RootRectangle
      CertificateObjective.endpointExpression lowRow10Cell13RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow10Cell13Root_nonneg {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow10Cell13RootRectangle) (tree := lowRow10Cell13RootTree)
  · norm_num [lowRow10Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell13RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow10Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell13RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow10Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell13RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow10Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow10Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow10Cell13RootTree_certified

private def lowRow10Cell14RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((9 : ℚ) / 64) ((5 : ℚ) / 32),
    RatBall.ofBounds ((13 : ℚ) / 32) ((7 : ℚ) / 16)⟩

private def lowRow10Cell14RootTree : Subdivision :=
.leaf .interval

private theorem lowRow10Cell14RootTree_certified :
    certifySubdivision 12 64 32 lowRow10Cell14RootRectangle
      CertificateObjective.endpointExpression lowRow10Cell14RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow10Cell14Root_nonneg {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow10Cell14RootRectangle) (tree := lowRow10Cell14RootTree)
  · norm_num [lowRow10Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell14RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow10Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell14RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow10Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell14RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow10Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow10Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow10Cell14RootTree_certified

private def lowRow10Cell15RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((9 : ℚ) / 64) ((5 : ℚ) / 32),
    RatBall.ofBounds ((7 : ℚ) / 16) ((15 : ℚ) / 32)⟩

private def lowRow10Cell15RootTree : Subdivision :=
.leaf .interval

private theorem lowRow10Cell15RootTree_certified :
    certifySubdivision 12 64 32 lowRow10Cell15RootRectangle
      CertificateObjective.endpointExpression lowRow10Cell15RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow10Cell15Root_nonneg {a q : ℝ}
    (haLower : ((9 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((5 : ℝ) / 32))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow10Cell15RootRectangle) (tree := lowRow10Cell15RootTree)
  · norm_num [lowRow10Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell15RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow10Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell15RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow10Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow10Cell15RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow10Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow10Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow10Cell15RootTree_certified

end Frankl
