import Frankl.EndpointCertificate

namespace Frankl

private def lowRow12Cell9RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((11 : ℚ) / 64) ((3 : ℚ) / 16),
    RatBall.ofBounds ((1 : ℚ) / 4) ((9 : ℚ) / 32)⟩

private def lowRow12Cell9RootTree : Subdivision :=
.horizontal ((23 : ℚ) / 128)
  (.vertical ((17 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((17 : ℚ) / 64)
  (.horizontal ((47 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))

private theorem lowRow12Cell9RootTree_certified :
    certifySubdivision 12 64 32 lowRow12Cell9RootRectangle
      CertificateObjective.endpointExpression lowRow12Cell9RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow12Cell9Root_nonneg {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow12Cell9RootRectangle) (tree := lowRow12Cell9RootTree)
  · norm_num [lowRow12Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell9RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow12Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell9RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow12Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell9RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow12Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow12Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow12Cell9RootTree_certified

private def lowRow12Cell10RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((11 : ℚ) / 64) ((3 : ℚ) / 16),
    RatBall.ofBounds ((9 : ℚ) / 32) ((5 : ℚ) / 16)⟩

private def lowRow12Cell10RootTree : Subdivision :=
.horizontal ((23 : ℚ) / 128)
  (.vertical ((19 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((19 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow12Cell10RootTree_certified :
    certifySubdivision 12 64 32 lowRow12Cell10RootRectangle
      CertificateObjective.endpointExpression lowRow12Cell10RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow12Cell10Root_nonneg {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow12Cell10RootRectangle) (tree := lowRow12Cell10RootTree)
  · norm_num [lowRow12Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell10RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow12Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell10RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow12Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell10RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow12Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow12Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow12Cell10RootTree_certified

private def lowRow12Cell11RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((11 : ℚ) / 64) ((3 : ℚ) / 16),
    RatBall.ofBounds ((5 : ℚ) / 16) ((11 : ℚ) / 32)⟩

private def lowRow12Cell11RootTree : Subdivision :=
.horizontal ((23 : ℚ) / 128)
  (.vertical ((21 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((21 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow12Cell11RootTree_certified :
    certifySubdivision 12 64 32 lowRow12Cell11RootRectangle
      CertificateObjective.endpointExpression lowRow12Cell11RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow12Cell11Root_nonneg {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow12Cell11RootRectangle) (tree := lowRow12Cell11RootTree)
  · norm_num [lowRow12Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell11RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow12Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell11RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow12Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell11RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow12Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow12Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow12Cell11RootTree_certified

private def lowRow12Cell12RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((11 : ℚ) / 64) ((3 : ℚ) / 16),
    RatBall.ofBounds ((11 : ℚ) / 32) ((3 : ℚ) / 8)⟩

private def lowRow12Cell12RootTree : Subdivision :=
.horizontal ((23 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow12Cell12RootTree_certified :
    certifySubdivision 12 64 32 lowRow12Cell12RootRectangle
      CertificateObjective.endpointExpression lowRow12Cell12RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow12Cell12Root_nonneg {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow12Cell12RootRectangle) (tree := lowRow12Cell12RootTree)
  · norm_num [lowRow12Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell12RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow12Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell12RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow12Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell12RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow12Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow12Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow12Cell12RootTree_certified

private def lowRow12Cell13RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((11 : ℚ) / 64) ((3 : ℚ) / 16),
    RatBall.ofBounds ((3 : ℚ) / 8) ((13 : ℚ) / 32)⟩

private def lowRow12Cell13RootTree : Subdivision :=
.horizontal ((23 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow12Cell13RootTree_certified :
    certifySubdivision 12 64 32 lowRow12Cell13RootRectangle
      CertificateObjective.endpointExpression lowRow12Cell13RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow12Cell13Root_nonneg {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow12Cell13RootRectangle) (tree := lowRow12Cell13RootTree)
  · norm_num [lowRow12Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell13RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow12Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell13RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow12Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell13RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow12Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow12Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow12Cell13RootTree_certified

private def lowRow12Cell14RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((11 : ℚ) / 64) ((3 : ℚ) / 16),
    RatBall.ofBounds ((13 : ℚ) / 32) ((7 : ℚ) / 16)⟩

private def lowRow12Cell14RootTree : Subdivision :=
.horizontal ((23 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow12Cell14RootTree_certified :
    certifySubdivision 12 64 32 lowRow12Cell14RootRectangle
      CertificateObjective.endpointExpression lowRow12Cell14RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow12Cell14Root_nonneg {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow12Cell14RootRectangle) (tree := lowRow12Cell14RootTree)
  · norm_num [lowRow12Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell14RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow12Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell14RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow12Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell14RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow12Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow12Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow12Cell14RootTree_certified

private def lowRow12Cell15RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((11 : ℚ) / 64) ((3 : ℚ) / 16),
    RatBall.ofBounds ((7 : ℚ) / 16) ((15 : ℚ) / 32)⟩

private def lowRow12Cell15RootTree : Subdivision :=
.horizontal ((23 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow12Cell15RootTree_certified :
    certifySubdivision 12 64 32 lowRow12Cell15RootRectangle
      CertificateObjective.endpointExpression lowRow12Cell15RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow12Cell15Root_nonneg {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow12Cell15RootRectangle) (tree := lowRow12Cell15RootTree)
  · norm_num [lowRow12Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell15RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow12Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell15RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow12Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell15RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow12Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow12Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow12Cell15RootTree_certified

private def lowRow12Cell16RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((11 : ℚ) / 64) ((3 : ℚ) / 16),
    RatBall.ofBounds ((15 : ℚ) / 32) ((1 : ℚ) / 2)⟩

private def lowRow12Cell16RootTree : Subdivision :=
.leaf .interval

private theorem lowRow12Cell16RootTree_certified :
    certifySubdivision 12 64 32 lowRow12Cell16RootRectangle
      CertificateObjective.endpointExpression lowRow12Cell16RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow12Cell16Root_nonneg {a q : ℝ}
    (haLower : ((11 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 16))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow12Cell16RootRectangle) (tree := lowRow12Cell16RootTree)
  · norm_num [lowRow12Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell16RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow12Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell16RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow12Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow12Cell16RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow12Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow12Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow12Cell16RootTree_certified

end Frankl
