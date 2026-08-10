import Frankl.EndpointCertificate

namespace Frankl

private def lowRow14Cell13RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((13 : ℚ) / 64) ((7 : ℚ) / 32),
    RatBall.ofBounds ((3 : ℚ) / 8) ((13 : ℚ) / 32)⟩

private def lowRow14Cell13RootTree : Subdivision :=
.horizontal ((27 : ℚ) / 128)
  (.vertical ((25 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((25 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow14Cell13RootTree_certified :
    certifySubdivision 12 64 32 lowRow14Cell13RootRectangle
      CertificateObjective.endpointExpression lowRow14Cell13RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow14Cell13Root_nonneg {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow14Cell13RootRectangle) (tree := lowRow14Cell13RootTree)
  · norm_num [lowRow14Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell13RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow14Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell13RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow14Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell13RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow14Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow14Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow14Cell13RootTree_certified

private def lowRow14Cell14RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((13 : ℚ) / 64) ((7 : ℚ) / 32),
    RatBall.ofBounds ((13 : ℚ) / 32) ((7 : ℚ) / 16)⟩

private def lowRow14Cell14RootTree : Subdivision :=
.horizontal ((27 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow14Cell14RootTree_certified :
    certifySubdivision 12 64 32 lowRow14Cell14RootRectangle
      CertificateObjective.endpointExpression lowRow14Cell14RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow14Cell14Root_nonneg {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow14Cell14RootRectangle) (tree := lowRow14Cell14RootTree)
  · norm_num [lowRow14Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell14RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow14Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell14RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow14Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell14RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow14Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow14Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow14Cell14RootTree_certified

private def lowRow14Cell15RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((13 : ℚ) / 64) ((7 : ℚ) / 32),
    RatBall.ofBounds ((7 : ℚ) / 16) ((15 : ℚ) / 32)⟩

private def lowRow14Cell15RootTree : Subdivision :=
.horizontal ((27 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow14Cell15RootTree_certified :
    certifySubdivision 12 64 32 lowRow14Cell15RootRectangle
      CertificateObjective.endpointExpression lowRow14Cell15RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow14Cell15Root_nonneg {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow14Cell15RootRectangle) (tree := lowRow14Cell15RootTree)
  · norm_num [lowRow14Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell15RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow14Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell15RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow14Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell15RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow14Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow14Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow14Cell15RootTree_certified

private def lowRow14Cell16RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((13 : ℚ) / 64) ((7 : ℚ) / 32),
    RatBall.ofBounds ((15 : ℚ) / 32) ((1 : ℚ) / 2)⟩

private def lowRow14Cell16RootTree : Subdivision :=
.horizontal ((27 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow14Cell16RootTree_certified :
    certifySubdivision 12 64 32 lowRow14Cell16RootRectangle
      CertificateObjective.endpointExpression lowRow14Cell16RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow14Cell16Root_nonneg {a q : ℝ}
    (haLower : ((13 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((7 : ℝ) / 32))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow14Cell16RootRectangle) (tree := lowRow14Cell16RootTree)
  · norm_num [lowRow14Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell16RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow14Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell16RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow14Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow14Cell16RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow14Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow14Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow14Cell16RootTree_certified

end Frankl
