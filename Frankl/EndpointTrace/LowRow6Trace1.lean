import Frankl.EndpointCertificate

namespace Frankl

private def lowRow6Cell7RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 64) ((3 : ℚ) / 32),
    RatBall.ofBounds ((3 : ℚ) / 16) ((7 : ℚ) / 32)⟩

private def lowRow6Cell7RootTree : Subdivision :=
.horizontal ((11 : ℚ) / 128)
  (.leaf .interval)
  (.vertical ((13 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow6Cell7RootTree_certified :
    certifySubdivision 12 64 32 lowRow6Cell7RootRectangle
      CertificateObjective.endpointExpression lowRow6Cell7RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow6Cell7Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow6Cell7RootRectangle) (tree := lowRow6Cell7RootTree)
  · norm_num [lowRow6Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell7RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow6Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell7RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow6Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell7RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow6Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow6Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow6Cell7RootTree_certified

private def lowRow6Cell8RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 64) ((3 : ℚ) / 32),
    RatBall.ofBounds ((7 : ℚ) / 32) ((1 : ℚ) / 4)⟩

private def lowRow6Cell8RootTree : Subdivision :=
.horizontal ((11 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow6Cell8RootTree_certified :
    certifySubdivision 12 64 32 lowRow6Cell8RootRectangle
      CertificateObjective.endpointExpression lowRow6Cell8RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow6Cell8Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow6Cell8RootRectangle) (tree := lowRow6Cell8RootTree)
  · norm_num [lowRow6Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell8RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow6Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell8RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow6Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell8RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow6Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow6Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow6Cell8RootTree_certified

private def lowRow6Cell9RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 64) ((3 : ℚ) / 32),
    RatBall.ofBounds ((1 : ℚ) / 4) ((9 : ℚ) / 32)⟩

private def lowRow6Cell9RootTree : Subdivision :=
.horizontal ((11 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow6Cell9RootTree_certified :
    certifySubdivision 12 64 32 lowRow6Cell9RootRectangle
      CertificateObjective.endpointExpression lowRow6Cell9RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow6Cell9Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow6Cell9RootRectangle) (tree := lowRow6Cell9RootTree)
  · norm_num [lowRow6Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell9RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow6Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell9RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow6Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell9RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow6Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow6Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow6Cell9RootTree_certified

private def lowRow6Cell10RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 64) ((3 : ℚ) / 32),
    RatBall.ofBounds ((9 : ℚ) / 32) ((5 : ℚ) / 16)⟩

private def lowRow6Cell10RootTree : Subdivision :=
.horizontal ((11 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow6Cell10RootTree_certified :
    certifySubdivision 12 64 32 lowRow6Cell10RootRectangle
      CertificateObjective.endpointExpression lowRow6Cell10RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow6Cell10Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow6Cell10RootRectangle) (tree := lowRow6Cell10RootTree)
  · norm_num [lowRow6Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell10RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow6Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell10RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow6Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell10RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow6Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow6Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow6Cell10RootTree_certified

private def lowRow6Cell11RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 64) ((3 : ℚ) / 32),
    RatBall.ofBounds ((5 : ℚ) / 16) ((11 : ℚ) / 32)⟩

private def lowRow6Cell11RootTree : Subdivision :=
.leaf .interval

private theorem lowRow6Cell11RootTree_certified :
    certifySubdivision 12 64 32 lowRow6Cell11RootRectangle
      CertificateObjective.endpointExpression lowRow6Cell11RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow6Cell11Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow6Cell11RootRectangle) (tree := lowRow6Cell11RootTree)
  · norm_num [lowRow6Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell11RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow6Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell11RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow6Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell11RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow6Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow6Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow6Cell11RootTree_certified

private def lowRow6Cell12RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 64) ((3 : ℚ) / 32),
    RatBall.ofBounds ((11 : ℚ) / 32) ((3 : ℚ) / 8)⟩

private def lowRow6Cell12RootTree : Subdivision :=
.leaf .interval

private theorem lowRow6Cell12RootTree_certified :
    certifySubdivision 12 64 32 lowRow6Cell12RootRectangle
      CertificateObjective.endpointExpression lowRow6Cell12RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow6Cell12Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow6Cell12RootRectangle) (tree := lowRow6Cell12RootTree)
  · norm_num [lowRow6Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell12RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow6Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell12RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow6Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell12RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow6Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow6Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow6Cell12RootTree_certified

private def lowRow6Cell13RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 64) ((3 : ℚ) / 32),
    RatBall.ofBounds ((3 : ℚ) / 8) ((13 : ℚ) / 32)⟩

private def lowRow6Cell13RootTree : Subdivision :=
.leaf .interval

private theorem lowRow6Cell13RootTree_certified :
    certifySubdivision 12 64 32 lowRow6Cell13RootRectangle
      CertificateObjective.endpointExpression lowRow6Cell13RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow6Cell13Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow6Cell13RootRectangle) (tree := lowRow6Cell13RootTree)
  · norm_num [lowRow6Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell13RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow6Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell13RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow6Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell13RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow6Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow6Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow6Cell13RootTree_certified

private def lowRow6Cell14RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 64) ((3 : ℚ) / 32),
    RatBall.ofBounds ((13 : ℚ) / 32) ((7 : ℚ) / 16)⟩

private def lowRow6Cell14RootTree : Subdivision :=
.leaf .interval

private theorem lowRow6Cell14RootTree_certified :
    certifySubdivision 12 64 32 lowRow6Cell14RootRectangle
      CertificateObjective.endpointExpression lowRow6Cell14RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow6Cell14Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow6Cell14RootRectangle) (tree := lowRow6Cell14RootTree)
  · norm_num [lowRow6Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell14RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow6Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell14RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow6Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell14RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow6Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow6Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow6Cell14RootTree_certified

private def lowRow6Cell15RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 64) ((3 : ℚ) / 32),
    RatBall.ofBounds ((7 : ℚ) / 16) ((15 : ℚ) / 32)⟩

private def lowRow6Cell15RootTree : Subdivision :=
.leaf .interval

private theorem lowRow6Cell15RootTree_certified :
    certifySubdivision 12 64 32 lowRow6Cell15RootRectangle
      CertificateObjective.endpointExpression lowRow6Cell15RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow6Cell15Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow6Cell15RootRectangle) (tree := lowRow6Cell15RootTree)
  · norm_num [lowRow6Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell15RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow6Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell15RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow6Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell15RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow6Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow6Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow6Cell15RootTree_certified

private def lowRow6Cell16RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((5 : ℚ) / 64) ((3 : ℚ) / 32),
    RatBall.ofBounds ((15 : ℚ) / 32) ((1 : ℚ) / 2)⟩

private def lowRow6Cell16RootTree : Subdivision :=
.leaf .interval

private theorem lowRow6Cell16RootTree_certified :
    certifySubdivision 12 64 32 lowRow6Cell16RootRectangle
      CertificateObjective.endpointExpression lowRow6Cell16RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow6Cell16Root_nonneg {a q : ℝ}
    (haLower : ((5 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((3 : ℝ) / 32))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow6Cell16RootRectangle) (tree := lowRow6Cell16RootTree)
  · norm_num [lowRow6Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell16RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow6Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell16RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow6Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow6Cell16RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow6Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow6Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow6Cell16RootTree_certified

end Frankl
