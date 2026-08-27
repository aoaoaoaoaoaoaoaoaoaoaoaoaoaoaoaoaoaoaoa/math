import Frankl.EndpointCertificate

namespace Frankl

private def lowRow16Cell13RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((15 : ℚ) / 64) ((1 : ℚ) / 4),
    RatBall.ofBounds ((3 : ℚ) / 8) ((13 : ℚ) / 32)⟩

private def lowRow16Cell13RootTree : Subdivision :=
.horizontal ((31 : ℚ) / 128)
  (.vertical ((25 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((25 : ℚ) / 64)
  (.horizontal ((63 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((63 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow16Cell13RootTree_certified :
    certifySubdivision 12 64 32 lowRow16Cell13RootRectangle
      CertificateObjective.endpointExpression lowRow16Cell13RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow16Cell13Root_nonneg {a q : ℝ}
    (haLower : ((15 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 4))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow16Cell13RootRectangle) (tree := lowRow16Cell13RootTree)
  · norm_num [lowRow16Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell13RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow16Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell13RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow16Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell13RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow16Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow16Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow16Cell13RootTree_certified

private def lowRow16Cell14RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((15 : ℚ) / 64) ((1 : ℚ) / 4),
    RatBall.ofBounds ((13 : ℚ) / 32) ((7 : ℚ) / 16)⟩

private def lowRow16Cell14RootTree : Subdivision :=
.horizontal ((31 : ℚ) / 128)
  (.vertical ((27 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((27 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow16Cell14RootTree_certified :
    certifySubdivision 12 64 32 lowRow16Cell14RootRectangle
      CertificateObjective.endpointExpression lowRow16Cell14RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow16Cell14Root_nonneg {a q : ℝ}
    (haLower : ((15 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 4))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow16Cell14RootRectangle) (tree := lowRow16Cell14RootTree)
  · norm_num [lowRow16Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell14RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow16Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell14RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow16Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell14RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow16Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow16Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow16Cell14RootTree_certified

private def lowRow16Cell15RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((15 : ℚ) / 64) ((1 : ℚ) / 4),
    RatBall.ofBounds ((7 : ℚ) / 16) ((15 : ℚ) / 32)⟩

private def lowRow16Cell15RootTree : Subdivision :=
.horizontal ((31 : ℚ) / 128)
  (.vertical ((29 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((29 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow16Cell15RootTree_certified :
    certifySubdivision 12 64 32 lowRow16Cell15RootRectangle
      CertificateObjective.endpointExpression lowRow16Cell15RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow16Cell15Root_nonneg {a q : ℝ}
    (haLower : ((15 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 4))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow16Cell15RootRectangle) (tree := lowRow16Cell15RootTree)
  · norm_num [lowRow16Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell15RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow16Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell15RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow16Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell15RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow16Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow16Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow16Cell15RootTree_certified

private def lowRow16Cell16RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((15 : ℚ) / 64) ((1 : ℚ) / 4),
    RatBall.ofBounds ((15 : ℚ) / 32) ((1 : ℚ) / 2)⟩

private def lowRow16Cell16RootTree : Subdivision :=
.horizontal ((31 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow16Cell16RootTree_certified :
    certifySubdivision 12 64 32 lowRow16Cell16RootRectangle
      CertificateObjective.endpointExpression lowRow16Cell16RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow16Cell16Root_nonneg {a q : ℝ}
    (haLower : ((15 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 4))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow16Cell16RootRectangle) (tree := lowRow16Cell16RootTree)
  · norm_num [lowRow16Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell16RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow16Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell16RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow16Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow16Cell16RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow16Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow16Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow16Cell16RootTree_certified

end Frankl
