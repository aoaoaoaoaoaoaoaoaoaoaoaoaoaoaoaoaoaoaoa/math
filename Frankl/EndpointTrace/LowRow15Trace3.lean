import Frankl.EndpointCertificate

namespace Frankl

private def lowRow15Cell12RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 32) ((15 : ℚ) / 64),
    RatBall.ofBounds ((11 : ℚ) / 32) ((3 : ℚ) / 8)⟩

private def lowRow15Cell12RootTree : Subdivision :=
.horizontal ((29 : ℚ) / 128)
  (.vertical ((23 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((23 : ℚ) / 64)
  (.horizontal ((59 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))

private theorem lowRow15Cell12RootTree_certified :
    certifySubdivision 12 64 32 lowRow15Cell12RootRectangle
      CertificateObjective.endpointExpression lowRow15Cell12RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow15Cell12Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow15Cell12RootRectangle) (tree := lowRow15Cell12RootTree)
  · norm_num [lowRow15Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell12RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow15Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell12RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow15Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell12RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow15Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow15Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow15Cell12RootTree_certified

private def lowRow15Cell13RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 32) ((15 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 8) ((13 : ℚ) / 32)⟩

private def lowRow15Cell13RootTree : Subdivision :=
.horizontal ((29 : ℚ) / 128)
  (.vertical ((25 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((25 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow15Cell13RootTree_certified :
    certifySubdivision 12 64 32 lowRow15Cell13RootRectangle
      CertificateObjective.endpointExpression lowRow15Cell13RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow15Cell13Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow15Cell13RootRectangle) (tree := lowRow15Cell13RootTree)
  · norm_num [lowRow15Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell13RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow15Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell13RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow15Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell13RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow15Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow15Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow15Cell13RootTree_certified

private def lowRow15Cell14RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 32) ((15 : ℚ) / 64),
    RatBall.ofBounds ((13 : ℚ) / 32) ((7 : ℚ) / 16)⟩

private def lowRow15Cell14RootTree : Subdivision :=
.horizontal ((29 : ℚ) / 128)
  (.vertical ((27 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((27 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow15Cell14RootTree_certified :
    certifySubdivision 12 64 32 lowRow15Cell14RootRectangle
      CertificateObjective.endpointExpression lowRow15Cell14RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow15Cell14Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow15Cell14RootRectangle) (tree := lowRow15Cell14RootTree)
  · norm_num [lowRow15Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell14RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow15Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell14RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow15Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell14RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow15Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow15Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow15Cell14RootTree_certified

private def lowRow15Cell15RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 32) ((15 : ℚ) / 64),
    RatBall.ofBounds ((7 : ℚ) / 16) ((15 : ℚ) / 32)⟩

private def lowRow15Cell15RootTree : Subdivision :=
.horizontal ((29 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow15Cell15RootTree_certified :
    certifySubdivision 12 64 32 lowRow15Cell15RootRectangle
      CertificateObjective.endpointExpression lowRow15Cell15RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow15Cell15Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow15Cell15RootRectangle) (tree := lowRow15Cell15RootTree)
  · norm_num [lowRow15Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell15RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow15Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell15RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow15Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell15RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow15Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow15Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow15Cell15RootTree_certified

private def lowRow15Cell16RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 32) ((15 : ℚ) / 64),
    RatBall.ofBounds ((15 : ℚ) / 32) ((1 : ℚ) / 2)⟩

private def lowRow15Cell16RootTree : Subdivision :=
.horizontal ((29 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow15Cell16RootTree_certified :
    certifySubdivision 12 64 32 lowRow15Cell16RootRectangle
      CertificateObjective.endpointExpression lowRow15Cell16RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow15Cell16Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((15 : ℝ) / 64))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow15Cell16RootRectangle) (tree := lowRow15Cell16RootTree)
  · norm_num [lowRow15Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell16RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow15Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell16RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow15Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow15Cell16RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow15Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow15Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow15Cell16RootTree_certified

end Frankl
