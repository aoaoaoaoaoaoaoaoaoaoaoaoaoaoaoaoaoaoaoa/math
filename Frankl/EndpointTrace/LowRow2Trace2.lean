import Frankl.EndpointCertificate

namespace Frankl

private def lowRow2Cell6RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 64) ((1 : ℚ) / 32),
    RatBall.ofBounds ((5 : ℚ) / 32) ((3 : ℚ) / 16)⟩

private def lowRow2Cell6RootTree : Subdivision :=
.horizontal ((3 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow2Cell6RootTree_certified :
    certifySubdivision 12 64 32 lowRow2Cell6RootRectangle
      CertificateObjective.endpointExpression lowRow2Cell6RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow2Cell6Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow2Cell6RootRectangle) (tree := lowRow2Cell6RootTree)
  · norm_num [lowRow2Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell6RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow2Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell6RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow2Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell6RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow2Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow2Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow2Cell6RootTree_certified

private def lowRow2Cell7RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 64) ((1 : ℚ) / 32),
    RatBall.ofBounds ((3 : ℚ) / 16) ((7 : ℚ) / 32)⟩

private def lowRow2Cell7RootTree : Subdivision :=
.horizontal ((3 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow2Cell7RootTree_certified :
    certifySubdivision 12 64 32 lowRow2Cell7RootRectangle
      CertificateObjective.endpointExpression lowRow2Cell7RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow2Cell7Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow2Cell7RootRectangle) (tree := lowRow2Cell7RootTree)
  · norm_num [lowRow2Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell7RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow2Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell7RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow2Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell7RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow2Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow2Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow2Cell7RootTree_certified

private def lowRow2Cell8RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 64) ((1 : ℚ) / 32),
    RatBall.ofBounds ((7 : ℚ) / 32) ((1 : ℚ) / 4)⟩

private def lowRow2Cell8RootTree : Subdivision :=
.horizontal ((3 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow2Cell8RootTree_certified :
    certifySubdivision 12 64 32 lowRow2Cell8RootRectangle
      CertificateObjective.endpointExpression lowRow2Cell8RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow2Cell8Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow2Cell8RootRectangle) (tree := lowRow2Cell8RootTree)
  · norm_num [lowRow2Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell8RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow2Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell8RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow2Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell8RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow2Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow2Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow2Cell8RootTree_certified

private def lowRow2Cell9RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 64) ((1 : ℚ) / 32),
    RatBall.ofBounds ((1 : ℚ) / 4) ((9 : ℚ) / 32)⟩

private def lowRow2Cell9RootTree : Subdivision :=
.leaf .interval

private theorem lowRow2Cell9RootTree_certified :
    certifySubdivision 12 64 32 lowRow2Cell9RootRectangle
      CertificateObjective.endpointExpression lowRow2Cell9RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow2Cell9Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow2Cell9RootRectangle) (tree := lowRow2Cell9RootTree)
  · norm_num [lowRow2Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell9RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow2Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell9RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow2Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell9RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow2Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow2Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow2Cell9RootTree_certified

private def lowRow2Cell10RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 64) ((1 : ℚ) / 32),
    RatBall.ofBounds ((9 : ℚ) / 32) ((5 : ℚ) / 16)⟩

private def lowRow2Cell10RootTree : Subdivision :=
.leaf .interval

private theorem lowRow2Cell10RootTree_certified :
    certifySubdivision 12 64 32 lowRow2Cell10RootRectangle
      CertificateObjective.endpointExpression lowRow2Cell10RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow2Cell10Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow2Cell10RootRectangle) (tree := lowRow2Cell10RootTree)
  · norm_num [lowRow2Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell10RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow2Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell10RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow2Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell10RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow2Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow2Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow2Cell10RootTree_certified

private def lowRow2Cell11RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 64) ((1 : ℚ) / 32),
    RatBall.ofBounds ((5 : ℚ) / 16) ((11 : ℚ) / 32)⟩

private def lowRow2Cell11RootTree : Subdivision :=
.leaf .interval

private theorem lowRow2Cell11RootTree_certified :
    certifySubdivision 12 64 32 lowRow2Cell11RootRectangle
      CertificateObjective.endpointExpression lowRow2Cell11RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow2Cell11Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow2Cell11RootRectangle) (tree := lowRow2Cell11RootTree)
  · norm_num [lowRow2Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell11RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow2Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell11RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow2Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell11RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow2Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow2Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow2Cell11RootTree_certified

private def lowRow2Cell12RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 64) ((1 : ℚ) / 32),
    RatBall.ofBounds ((11 : ℚ) / 32) ((3 : ℚ) / 8)⟩

private def lowRow2Cell12RootTree : Subdivision :=
.leaf .interval

private theorem lowRow2Cell12RootTree_certified :
    certifySubdivision 12 64 32 lowRow2Cell12RootRectangle
      CertificateObjective.endpointExpression lowRow2Cell12RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow2Cell12Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow2Cell12RootRectangle) (tree := lowRow2Cell12RootTree)
  · norm_num [lowRow2Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell12RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow2Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell12RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow2Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell12RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow2Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow2Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow2Cell12RootTree_certified

private def lowRow2Cell13RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 64) ((1 : ℚ) / 32),
    RatBall.ofBounds ((3 : ℚ) / 8) ((13 : ℚ) / 32)⟩

private def lowRow2Cell13RootTree : Subdivision :=
.leaf .interval

private theorem lowRow2Cell13RootTree_certified :
    certifySubdivision 12 64 32 lowRow2Cell13RootRectangle
      CertificateObjective.endpointExpression lowRow2Cell13RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow2Cell13Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow2Cell13RootRectangle) (tree := lowRow2Cell13RootTree)
  · norm_num [lowRow2Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell13RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow2Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell13RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow2Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell13RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow2Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow2Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow2Cell13RootTree_certified

private def lowRow2Cell14RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 64) ((1 : ℚ) / 32),
    RatBall.ofBounds ((13 : ℚ) / 32) ((7 : ℚ) / 16)⟩

private def lowRow2Cell14RootTree : Subdivision :=
.leaf .interval

private theorem lowRow2Cell14RootTree_certified :
    certifySubdivision 12 64 32 lowRow2Cell14RootRectangle
      CertificateObjective.endpointExpression lowRow2Cell14RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow2Cell14Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow2Cell14RootRectangle) (tree := lowRow2Cell14RootTree)
  · norm_num [lowRow2Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell14RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow2Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell14RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow2Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell14RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow2Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow2Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow2Cell14RootTree_certified

private def lowRow2Cell15RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 64) ((1 : ℚ) / 32),
    RatBall.ofBounds ((7 : ℚ) / 16) ((15 : ℚ) / 32)⟩

private def lowRow2Cell15RootTree : Subdivision :=
.leaf .interval

private theorem lowRow2Cell15RootTree_certified :
    certifySubdivision 12 64 32 lowRow2Cell15RootRectangle
      CertificateObjective.endpointExpression lowRow2Cell15RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow2Cell15Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow2Cell15RootRectangle) (tree := lowRow2Cell15RootTree)
  · norm_num [lowRow2Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell15RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow2Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell15RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow2Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell15RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow2Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow2Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow2Cell15RootTree_certified

private def lowRow2Cell16RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 64) ((1 : ℚ) / 32),
    RatBall.ofBounds ((15 : ℚ) / 32) ((1 : ℚ) / 2)⟩

private def lowRow2Cell16RootTree : Subdivision :=
.leaf .interval

private theorem lowRow2Cell16RootTree_certified :
    certifySubdivision 12 64 32 lowRow2Cell16RootRectangle
      CertificateObjective.endpointExpression lowRow2Cell16RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow2Cell16Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 32))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow2Cell16RootRectangle) (tree := lowRow2Cell16RootTree)
  · norm_num [lowRow2Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell16RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow2Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell16RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow2Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow2Cell16RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow2Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow2Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow2Cell16RootTree_certified

end Frankl
