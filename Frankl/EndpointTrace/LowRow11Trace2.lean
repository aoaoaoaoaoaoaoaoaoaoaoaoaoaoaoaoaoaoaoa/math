import Frankl.EndpointCertificate

namespace Frankl

private def lowRow11Cell11RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 32) ((11 : ℚ) / 64),
    RatBall.ofBounds ((5 : ℚ) / 16) ((11 : ℚ) / 32)⟩

private def lowRow11Cell11RootTree : Subdivision :=
.horizontal ((21 : ℚ) / 128)
  (.leaf .interval)
  (.vertical ((21 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow11Cell11RootTree_certified :
    certifySubdivision 12 64 32 lowRow11Cell11RootRectangle
      CertificateObjective.endpointExpression lowRow11Cell11RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow11Cell11Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow11Cell11RootRectangle) (tree := lowRow11Cell11RootTree)
  · norm_num [lowRow11Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell11RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow11Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell11RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow11Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell11RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow11Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow11Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow11Cell11RootTree_certified

private def lowRow11Cell12RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 32) ((11 : ℚ) / 64),
    RatBall.ofBounds ((11 : ℚ) / 32) ((3 : ℚ) / 8)⟩

private def lowRow11Cell12RootTree : Subdivision :=
.horizontal ((21 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow11Cell12RootTree_certified :
    certifySubdivision 12 64 32 lowRow11Cell12RootRectangle
      CertificateObjective.endpointExpression lowRow11Cell12RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow11Cell12Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow11Cell12RootRectangle) (tree := lowRow11Cell12RootTree)
  · norm_num [lowRow11Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell12RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow11Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell12RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow11Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell12RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow11Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow11Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow11Cell12RootTree_certified

private def lowRow11Cell13RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 32) ((11 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 8) ((13 : ℚ) / 32)⟩

private def lowRow11Cell13RootTree : Subdivision :=
.horizontal ((21 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow11Cell13RootTree_certified :
    certifySubdivision 12 64 32 lowRow11Cell13RootRectangle
      CertificateObjective.endpointExpression lowRow11Cell13RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow11Cell13Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow11Cell13RootRectangle) (tree := lowRow11Cell13RootTree)
  · norm_num [lowRow11Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell13RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow11Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell13RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow11Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell13RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow11Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow11Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow11Cell13RootTree_certified

private def lowRow11Cell14RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 32) ((11 : ℚ) / 64),
    RatBall.ofBounds ((13 : ℚ) / 32) ((7 : ℚ) / 16)⟩

private def lowRow11Cell14RootTree : Subdivision :=
.horizontal ((21 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow11Cell14RootTree_certified :
    certifySubdivision 12 64 32 lowRow11Cell14RootRectangle
      CertificateObjective.endpointExpression lowRow11Cell14RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow11Cell14Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow11Cell14RootRectangle) (tree := lowRow11Cell14RootTree)
  · norm_num [lowRow11Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell14RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow11Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell14RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow11Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell14RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow11Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow11Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow11Cell14RootTree_certified

private def lowRow11Cell15RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 32) ((11 : ℚ) / 64),
    RatBall.ofBounds ((7 : ℚ) / 16) ((15 : ℚ) / 32)⟩

private def lowRow11Cell15RootTree : Subdivision :=
.leaf .interval

private theorem lowRow11Cell15RootTree_certified :
    certifySubdivision 12 64 32 lowRow11Cell15RootRectangle
      CertificateObjective.endpointExpression lowRow11Cell15RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow11Cell15Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow11Cell15RootRectangle) (tree := lowRow11Cell15RootTree)
  · norm_num [lowRow11Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell15RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow11Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell15RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow11Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell15RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow11Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow11Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow11Cell15RootTree_certified

private def lowRow11Cell16RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 32) ((11 : ℚ) / 64),
    RatBall.ofBounds ((15 : ℚ) / 32) ((1 : ℚ) / 2)⟩

private def lowRow11Cell16RootTree : Subdivision :=
.leaf .interval

private theorem lowRow11Cell16RootTree_certified :
    certifySubdivision 12 64 32 lowRow11Cell16RootRectangle
      CertificateObjective.endpointExpression lowRow11Cell16RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow11Cell16Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow11Cell16RootRectangle) (tree := lowRow11Cell16RootTree)
  · norm_num [lowRow11Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell16RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow11Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell16RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow11Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell16RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow11Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow11Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow11Cell16RootTree_certified

end Frankl
