import Frankl.EndpointCertificate

namespace Frankl

private def lowRow0Cell10RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((9 : ℚ) / 32) ((5 : ℚ) / 16)⟩

private def lowRow0Cell10RootTree : Subdivision :=
.leaf .interval

private theorem lowRow0Cell10RootTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell10RootRectangle
      CertificateObjective.endpointExpression lowRow0Cell10RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell10Root_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell10RootRectangle) (tree := lowRow0Cell10RootTree)
  · norm_num [lowRow0Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell10RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell10RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell10RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell10RootTree_certified

private def lowRow0Cell11RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((5 : ℚ) / 16) ((11 : ℚ) / 32)⟩

private def lowRow0Cell11RootTree : Subdivision :=
.leaf .interval

private theorem lowRow0Cell11RootTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell11RootRectangle
      CertificateObjective.endpointExpression lowRow0Cell11RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell11Root_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell11RootRectangle) (tree := lowRow0Cell11RootTree)
  · norm_num [lowRow0Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell11RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell11RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell11RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell11RootTree_certified

private def lowRow0Cell12RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((11 : ℚ) / 32) ((3 : ℚ) / 8)⟩

private def lowRow0Cell12RootTree : Subdivision :=
.leaf .interval

private theorem lowRow0Cell12RootTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell12RootRectangle
      CertificateObjective.endpointExpression lowRow0Cell12RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell12Root_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell12RootRectangle) (tree := lowRow0Cell12RootTree)
  · norm_num [lowRow0Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell12RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell12RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell12RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell12RootTree_certified

private def lowRow0Cell13RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((3 : ℚ) / 8) ((13 : ℚ) / 32)⟩

private def lowRow0Cell13RootTree : Subdivision :=
.leaf .interval

private theorem lowRow0Cell13RootTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell13RootRectangle
      CertificateObjective.endpointExpression lowRow0Cell13RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell13Root_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell13RootRectangle) (tree := lowRow0Cell13RootTree)
  · norm_num [lowRow0Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell13RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell13RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell13RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell13RootTree_certified

private def lowRow0Cell14RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((13 : ℚ) / 32) ((7 : ℚ) / 16)⟩

private def lowRow0Cell14RootTree : Subdivision :=
.leaf .interval

private theorem lowRow0Cell14RootTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell14RootRectangle
      CertificateObjective.endpointExpression lowRow0Cell14RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell14Root_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell14RootRectangle) (tree := lowRow0Cell14RootTree)
  · norm_num [lowRow0Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell14RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell14RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell14RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell14RootTree_certified

private def lowRow0Cell15RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((7 : ℚ) / 16) ((15 : ℚ) / 32)⟩

private def lowRow0Cell15RootTree : Subdivision :=
.leaf .interval

private theorem lowRow0Cell15RootTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell15RootRectangle
      CertificateObjective.endpointExpression lowRow0Cell15RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell15Root_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell15RootRectangle) (tree := lowRow0Cell15RootTree)
  · norm_num [lowRow0Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell15RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell15RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell15RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell15RootTree_certified

private def lowRow0Cell16RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((0 : ℚ) / 1) ((1 : ℚ) / 1000),
    RatBall.ofBounds ((15 : ℚ) / 32) ((1 : ℚ) / 2)⟩

private def lowRow0Cell16RootTree : Subdivision :=
.leaf .interval

private theorem lowRow0Cell16RootTree_certified :
    certifySubdivision 12 64 32 lowRow0Cell16RootRectangle
      CertificateObjective.endpointExpression lowRow0Cell16RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow0Cell16Root_nonneg {a q : ℝ}
    (haLower : ((0 : ℝ) / 1) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 1000))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow0Cell16RootRectangle) (tree := lowRow0Cell16RootTree)
  · norm_num [lowRow0Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell16RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow0Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell16RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow0Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow0Cell16RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow0Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow0Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow0Cell16RootTree_certified

end Frankl
