import Frankl.EndpointCertificate

namespace Frankl

private def lowRow7Cell7RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 32) ((7 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 16) ((7 : ℚ) / 32)⟩

private def lowRow7Cell7RootTree : Subdivision :=
.horizontal ((13 : ℚ) / 128)
  (.vertical ((13 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((13 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow7Cell7RootTree_certified :
    certifySubdivision 12 64 32 lowRow7Cell7RootRectangle
      CertificateObjective.endpointExpression lowRow7Cell7RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow7Cell7Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow7Cell7RootRectangle) (tree := lowRow7Cell7RootTree)
  · norm_num [lowRow7Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell7RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow7Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell7RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow7Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell7RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow7Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow7Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow7Cell7RootTree_certified

private def lowRow7Cell8RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 32) ((7 : ℚ) / 64),
    RatBall.ofBounds ((7 : ℚ) / 32) ((1 : ℚ) / 4)⟩

private def lowRow7Cell8RootTree : Subdivision :=
.horizontal ((13 : ℚ) / 128)
  (.leaf .interval)
  (.vertical ((15 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow7Cell8RootTree_certified :
    certifySubdivision 12 64 32 lowRow7Cell8RootRectangle
      CertificateObjective.endpointExpression lowRow7Cell8RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow7Cell8Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow7Cell8RootRectangle) (tree := lowRow7Cell8RootTree)
  · norm_num [lowRow7Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell8RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow7Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell8RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow7Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell8RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow7Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow7Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow7Cell8RootTree_certified

private def lowRow7Cell9RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 32) ((7 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 4) ((9 : ℚ) / 32)⟩

private def lowRow7Cell9RootTree : Subdivision :=
.horizontal ((13 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow7Cell9RootTree_certified :
    certifySubdivision 12 64 32 lowRow7Cell9RootRectangle
      CertificateObjective.endpointExpression lowRow7Cell9RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow7Cell9Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow7Cell9RootRectangle) (tree := lowRow7Cell9RootTree)
  · norm_num [lowRow7Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell9RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow7Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell9RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow7Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell9RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow7Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow7Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow7Cell9RootTree_certified

private def lowRow7Cell10RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 32) ((7 : ℚ) / 64),
    RatBall.ofBounds ((9 : ℚ) / 32) ((5 : ℚ) / 16)⟩

private def lowRow7Cell10RootTree : Subdivision :=
.horizontal ((13 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow7Cell10RootTree_certified :
    certifySubdivision 12 64 32 lowRow7Cell10RootRectangle
      CertificateObjective.endpointExpression lowRow7Cell10RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow7Cell10Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow7Cell10RootRectangle) (tree := lowRow7Cell10RootTree)
  · norm_num [lowRow7Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell10RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow7Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell10RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow7Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell10RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow7Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow7Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow7Cell10RootTree_certified

private def lowRow7Cell11RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 32) ((7 : ℚ) / 64),
    RatBall.ofBounds ((5 : ℚ) / 16) ((11 : ℚ) / 32)⟩

private def lowRow7Cell11RootTree : Subdivision :=
.horizontal ((13 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow7Cell11RootTree_certified :
    certifySubdivision 12 64 32 lowRow7Cell11RootRectangle
      CertificateObjective.endpointExpression lowRow7Cell11RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow7Cell11Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow7Cell11RootRectangle) (tree := lowRow7Cell11RootTree)
  · norm_num [lowRow7Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell11RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow7Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell11RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow7Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell11RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow7Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow7Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow7Cell11RootTree_certified

private def lowRow7Cell12RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 32) ((7 : ℚ) / 64),
    RatBall.ofBounds ((11 : ℚ) / 32) ((3 : ℚ) / 8)⟩

private def lowRow7Cell12RootTree : Subdivision :=
.leaf .interval

private theorem lowRow7Cell12RootTree_certified :
    certifySubdivision 12 64 32 lowRow7Cell12RootRectangle
      CertificateObjective.endpointExpression lowRow7Cell12RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow7Cell12Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow7Cell12RootRectangle) (tree := lowRow7Cell12RootTree)
  · norm_num [lowRow7Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell12RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow7Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell12RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow7Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell12RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow7Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow7Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow7Cell12RootTree_certified

private def lowRow7Cell13RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 32) ((7 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 8) ((13 : ℚ) / 32)⟩

private def lowRow7Cell13RootTree : Subdivision :=
.leaf .interval

private theorem lowRow7Cell13RootTree_certified :
    certifySubdivision 12 64 32 lowRow7Cell13RootRectangle
      CertificateObjective.endpointExpression lowRow7Cell13RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow7Cell13Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow7Cell13RootRectangle) (tree := lowRow7Cell13RootTree)
  · norm_num [lowRow7Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell13RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow7Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell13RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow7Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell13RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow7Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow7Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow7Cell13RootTree_certified

private def lowRow7Cell14RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 32) ((7 : ℚ) / 64),
    RatBall.ofBounds ((13 : ℚ) / 32) ((7 : ℚ) / 16)⟩

private def lowRow7Cell14RootTree : Subdivision :=
.leaf .interval

private theorem lowRow7Cell14RootTree_certified :
    certifySubdivision 12 64 32 lowRow7Cell14RootRectangle
      CertificateObjective.endpointExpression lowRow7Cell14RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow7Cell14Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow7Cell14RootRectangle) (tree := lowRow7Cell14RootTree)
  · norm_num [lowRow7Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell14RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow7Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell14RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow7Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell14RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow7Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow7Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow7Cell14RootTree_certified

private def lowRow7Cell15RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 32) ((7 : ℚ) / 64),
    RatBall.ofBounds ((7 : ℚ) / 16) ((15 : ℚ) / 32)⟩

private def lowRow7Cell15RootTree : Subdivision :=
.leaf .interval

private theorem lowRow7Cell15RootTree_certified :
    certifySubdivision 12 64 32 lowRow7Cell15RootRectangle
      CertificateObjective.endpointExpression lowRow7Cell15RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow7Cell15Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow7Cell15RootRectangle) (tree := lowRow7Cell15RootTree)
  · norm_num [lowRow7Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell15RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow7Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell15RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow7Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell15RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow7Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow7Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow7Cell15RootTree_certified

private def lowRow7Cell16RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 32) ((7 : ℚ) / 64),
    RatBall.ofBounds ((15 : ℚ) / 32) ((1 : ℚ) / 2)⟩

private def lowRow7Cell16RootTree : Subdivision :=
.leaf .interval

private theorem lowRow7Cell16RootTree_certified :
    certifySubdivision 12 64 32 lowRow7Cell16RootRectangle
      CertificateObjective.endpointExpression lowRow7Cell16RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow7Cell16Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 64))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow7Cell16RootRectangle) (tree := lowRow7Cell16RootTree)
  · norm_num [lowRow7Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell16RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow7Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell16RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow7Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow7Cell16RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow7Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow7Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow7Cell16RootTree_certified

end Frankl
