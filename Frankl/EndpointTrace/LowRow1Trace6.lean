import Frankl.EndpointCertificate

namespace Frankl

private def lowRow1Cell7RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 16) ((7 : ℚ) / 32)⟩

private def lowRow1Cell7RootTree : Subdivision :=
.horizontal ((133 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow1Cell7RootTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell7RootRectangle
      CertificateObjective.endpointExpression lowRow1Cell7RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell7Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell7RootRectangle) (tree := lowRow1Cell7RootTree)
  · norm_num [lowRow1Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell7RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell7RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell7RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell7RootTree_certified

private def lowRow1Cell8RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 64),
    RatBall.ofBounds ((7 : ℚ) / 32) ((1 : ℚ) / 4)⟩

private def lowRow1Cell8RootTree : Subdivision :=
.horizontal ((133 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow1Cell8RootTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell8RootRectangle
      CertificateObjective.endpointExpression lowRow1Cell8RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell8Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell8RootRectangle) (tree := lowRow1Cell8RootTree)
  · norm_num [lowRow1Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell8RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell8RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell8RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell8RootTree_certified

private def lowRow1Cell9RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 4) ((9 : ℚ) / 32)⟩

private def lowRow1Cell9RootTree : Subdivision :=
.horizontal ((133 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow1Cell9RootTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell9RootRectangle
      CertificateObjective.endpointExpression lowRow1Cell9RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell9Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell9RootRectangle) (tree := lowRow1Cell9RootTree)
  · norm_num [lowRow1Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell9RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell9RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell9RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell9RootTree_certified

private def lowRow1Cell10RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 64),
    RatBall.ofBounds ((9 : ℚ) / 32) ((5 : ℚ) / 16)⟩

private def lowRow1Cell10RootTree : Subdivision :=
.horizontal ((133 : ℚ) / 16000)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow1Cell10RootTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell10RootRectangle
      CertificateObjective.endpointExpression lowRow1Cell10RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell10Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell10RootRectangle) (tree := lowRow1Cell10RootTree)
  · norm_num [lowRow1Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell10RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell10RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell10RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell10RootTree_certified

private def lowRow1Cell11RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 64),
    RatBall.ofBounds ((5 : ℚ) / 16) ((11 : ℚ) / 32)⟩

private def lowRow1Cell11RootTree : Subdivision :=
.leaf .interval

private theorem lowRow1Cell11RootTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell11RootRectangle
      CertificateObjective.endpointExpression lowRow1Cell11RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell11Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell11RootRectangle) (tree := lowRow1Cell11RootTree)
  · norm_num [lowRow1Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell11RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell11RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell11RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell11RootTree_certified

private def lowRow1Cell12RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 64),
    RatBall.ofBounds ((11 : ℚ) / 32) ((3 : ℚ) / 8)⟩

private def lowRow1Cell12RootTree : Subdivision :=
.leaf .interval

private theorem lowRow1Cell12RootTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell12RootRectangle
      CertificateObjective.endpointExpression lowRow1Cell12RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell12Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell12RootRectangle) (tree := lowRow1Cell12RootTree)
  · norm_num [lowRow1Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell12RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell12RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell12RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell12RootTree_certified

private def lowRow1Cell13RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 8) ((13 : ℚ) / 32)⟩

private def lowRow1Cell13RootTree : Subdivision :=
.leaf .interval

private theorem lowRow1Cell13RootTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell13RootRectangle
      CertificateObjective.endpointExpression lowRow1Cell13RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell13Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell13RootRectangle) (tree := lowRow1Cell13RootTree)
  · norm_num [lowRow1Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell13RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell13RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell13RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell13RootTree_certified

private def lowRow1Cell14RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 64),
    RatBall.ofBounds ((13 : ℚ) / 32) ((7 : ℚ) / 16)⟩

private def lowRow1Cell14RootTree : Subdivision :=
.leaf .interval

private theorem lowRow1Cell14RootTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell14RootRectangle
      CertificateObjective.endpointExpression lowRow1Cell14RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell14Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell14RootRectangle) (tree := lowRow1Cell14RootTree)
  · norm_num [lowRow1Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell14RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell14RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell14RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell14RootTree_certified

private def lowRow1Cell15RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 64),
    RatBall.ofBounds ((7 : ℚ) / 16) ((15 : ℚ) / 32)⟩

private def lowRow1Cell15RootTree : Subdivision :=
.leaf .interval

private theorem lowRow1Cell15RootTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell15RootRectangle
      CertificateObjective.endpointExpression lowRow1Cell15RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell15Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell15RootRectangle) (tree := lowRow1Cell15RootTree)
  · norm_num [lowRow1Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell15RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell15RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell15RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell15RootTree_certified

private def lowRow1Cell16RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 1000) ((1 : ℚ) / 64),
    RatBall.ofBounds ((15 : ℚ) / 32) ((1 : ℚ) / 2)⟩

private def lowRow1Cell16RootTree : Subdivision :=
.leaf .interval

private theorem lowRow1Cell16RootTree_certified :
    certifySubdivision 12 64 32 lowRow1Cell16RootRectangle
      CertificateObjective.endpointExpression lowRow1Cell16RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow1Cell16Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 1000) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 64))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow1Cell16RootRectangle) (tree := lowRow1Cell16RootTree)
  · norm_num [lowRow1Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell16RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow1Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell16RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow1Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow1Cell16RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow1Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow1Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow1Cell16RootTree_certified

end Frankl
