import Frankl.EndpointCertificate

namespace Frankl

private def lowRow11Cell6RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 32) ((11 : ℚ) / 64),
    RatBall.ofBounds ((5 : ℚ) / 32) ((3 : ℚ) / 16)⟩

private def lowRow11Cell6RootTree : Subdivision :=
.horizontal ((21 : ℚ) / 128)
  (.vertical ((11 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((11 : ℚ) / 64)
  (.horizontal ((43 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((43 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

private theorem lowRow11Cell6RootTree_certified :
    certifySubdivision 12 64 32 lowRow11Cell6RootRectangle
      CertificateObjective.endpointExpression lowRow11Cell6RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow11Cell6Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow11Cell6RootRectangle) (tree := lowRow11Cell6RootTree)
  · norm_num [lowRow11Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell6RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow11Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell6RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow11Cell6RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell6RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow11Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow11Cell6RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow11Cell6RootTree_certified

private def lowRow11Cell7RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 32) ((11 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 16) ((7 : ℚ) / 32)⟩

private def lowRow11Cell7RootTree : Subdivision :=
.horizontal ((21 : ℚ) / 128)
  (.vertical ((13 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((13 : ℚ) / 64)
  (.horizontal ((43 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))

private theorem lowRow11Cell7RootTree_certified :
    certifySubdivision 12 64 32 lowRow11Cell7RootRectangle
      CertificateObjective.endpointExpression lowRow11Cell7RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow11Cell7Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow11Cell7RootRectangle) (tree := lowRow11Cell7RootTree)
  · norm_num [lowRow11Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell7RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow11Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell7RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow11Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell7RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow11Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow11Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow11Cell7RootTree_certified

private def lowRow11Cell8RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 32) ((11 : ℚ) / 64),
    RatBall.ofBounds ((7 : ℚ) / 32) ((1 : ℚ) / 4)⟩

private def lowRow11Cell8RootTree : Subdivision :=
.horizontal ((21 : ℚ) / 128)
  (.vertical ((15 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((15 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow11Cell8RootTree_certified :
    certifySubdivision 12 64 32 lowRow11Cell8RootRectangle
      CertificateObjective.endpointExpression lowRow11Cell8RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow11Cell8Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow11Cell8RootRectangle) (tree := lowRow11Cell8RootTree)
  · norm_num [lowRow11Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell8RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow11Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell8RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow11Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell8RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow11Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow11Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow11Cell8RootTree_certified

private def lowRow11Cell9RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 32) ((11 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 4) ((9 : ℚ) / 32)⟩

private def lowRow11Cell9RootTree : Subdivision :=
.horizontal ((21 : ℚ) / 128)
  (.vertical ((17 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((17 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow11Cell9RootTree_certified :
    certifySubdivision 12 64 32 lowRow11Cell9RootRectangle
      CertificateObjective.endpointExpression lowRow11Cell9RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow11Cell9Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow11Cell9RootRectangle) (tree := lowRow11Cell9RootTree)
  · norm_num [lowRow11Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell9RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow11Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell9RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow11Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell9RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow11Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow11Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow11Cell9RootTree_certified

private def lowRow11Cell10RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 32) ((11 : ℚ) / 64),
    RatBall.ofBounds ((9 : ℚ) / 32) ((5 : ℚ) / 16)⟩

private def lowRow11Cell10RootTree : Subdivision :=
.horizontal ((21 : ℚ) / 128)
  (.vertical ((19 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((19 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow11Cell10RootTree_certified :
    certifySubdivision 12 64 32 lowRow11Cell10RootRectangle
      CertificateObjective.endpointExpression lowRow11Cell10RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow11Cell10Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 32) ≤ a)
    (haUpper : a ≤ ((11 : ℝ) / 64))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow11Cell10RootRectangle) (tree := lowRow11Cell10RootTree)
  · norm_num [lowRow11Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell10RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow11Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell10RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow11Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow11Cell10RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow11Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow11Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow11Cell10RootTree_certified

private def lowRow11Cell11RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 32) ((11 : ℚ) / 64),
    RatBall.ofBounds ((5 : ℚ) / 16) ((11 : ℚ) / 32)⟩

private def lowRow11Cell11RootTree : Subdivision :=
.horizontal ((21 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

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

end Frankl
