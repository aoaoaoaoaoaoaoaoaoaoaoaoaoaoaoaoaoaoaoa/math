import Frankl.EndpointCertificate

namespace Frankl

private def lowRow8Cell7RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 64) ((1 : ℚ) / 8),
    RatBall.ofBounds ((3 : ℚ) / 16) ((7 : ℚ) / 32)⟩

private def lowRow8Cell7RootTree : Subdivision :=
.horizontal ((15 : ℚ) / 128)
  (.vertical ((13 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((13 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow8Cell7RootTree_certified :
    certifySubdivision 12 64 32 lowRow8Cell7RootRectangle
      CertificateObjective.endpointExpression lowRow8Cell7RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow8Cell7Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow8Cell7RootRectangle) (tree := lowRow8Cell7RootTree)
  · norm_num [lowRow8Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell7RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow8Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell7RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow8Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell7RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow8Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow8Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow8Cell7RootTree_certified

private def lowRow8Cell8RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 64) ((1 : ℚ) / 8),
    RatBall.ofBounds ((7 : ℚ) / 32) ((1 : ℚ) / 4)⟩

private def lowRow8Cell8RootTree : Subdivision :=
.horizontal ((15 : ℚ) / 128)
  (.vertical ((15 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((15 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow8Cell8RootTree_certified :
    certifySubdivision 12 64 32 lowRow8Cell8RootRectangle
      CertificateObjective.endpointExpression lowRow8Cell8RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow8Cell8Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow8Cell8RootRectangle) (tree := lowRow8Cell8RootTree)
  · norm_num [lowRow8Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell8RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow8Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell8RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow8Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell8RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow8Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow8Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow8Cell8RootTree_certified

private def lowRow8Cell9RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 64) ((1 : ℚ) / 8),
    RatBall.ofBounds ((1 : ℚ) / 4) ((9 : ℚ) / 32)⟩

private def lowRow8Cell9RootTree : Subdivision :=
.horizontal ((15 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow8Cell9RootTree_certified :
    certifySubdivision 12 64 32 lowRow8Cell9RootRectangle
      CertificateObjective.endpointExpression lowRow8Cell9RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow8Cell9Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow8Cell9RootRectangle) (tree := lowRow8Cell9RootTree)
  · norm_num [lowRow8Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell9RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow8Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell9RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow8Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell9RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow8Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow8Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow8Cell9RootTree_certified

private def lowRow8Cell10RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 64) ((1 : ℚ) / 8),
    RatBall.ofBounds ((9 : ℚ) / 32) ((5 : ℚ) / 16)⟩

private def lowRow8Cell10RootTree : Subdivision :=
.horizontal ((15 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow8Cell10RootTree_certified :
    certifySubdivision 12 64 32 lowRow8Cell10RootRectangle
      CertificateObjective.endpointExpression lowRow8Cell10RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow8Cell10Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow8Cell10RootRectangle) (tree := lowRow8Cell10RootTree)
  · norm_num [lowRow8Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell10RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow8Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell10RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow8Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell10RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow8Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow8Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow8Cell10RootTree_certified

private def lowRow8Cell11RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 64) ((1 : ℚ) / 8),
    RatBall.ofBounds ((5 : ℚ) / 16) ((11 : ℚ) / 32)⟩

private def lowRow8Cell11RootTree : Subdivision :=
.horizontal ((15 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow8Cell11RootTree_certified :
    certifySubdivision 12 64 32 lowRow8Cell11RootRectangle
      CertificateObjective.endpointExpression lowRow8Cell11RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow8Cell11Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow8Cell11RootRectangle) (tree := lowRow8Cell11RootTree)
  · norm_num [lowRow8Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell11RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow8Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell11RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow8Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell11RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow8Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow8Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow8Cell11RootTree_certified

private def lowRow8Cell12RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 64) ((1 : ℚ) / 8),
    RatBall.ofBounds ((11 : ℚ) / 32) ((3 : ℚ) / 8)⟩

private def lowRow8Cell12RootTree : Subdivision :=
.horizontal ((15 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow8Cell12RootTree_certified :
    certifySubdivision 12 64 32 lowRow8Cell12RootRectangle
      CertificateObjective.endpointExpression lowRow8Cell12RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow8Cell12Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow8Cell12RootRectangle) (tree := lowRow8Cell12RootTree)
  · norm_num [lowRow8Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell12RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow8Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell12RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow8Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell12RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow8Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow8Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow8Cell12RootTree_certified

private def lowRow8Cell13RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 64) ((1 : ℚ) / 8),
    RatBall.ofBounds ((3 : ℚ) / 8) ((13 : ℚ) / 32)⟩

private def lowRow8Cell13RootTree : Subdivision :=
.leaf .interval

private theorem lowRow8Cell13RootTree_certified :
    certifySubdivision 12 64 32 lowRow8Cell13RootRectangle
      CertificateObjective.endpointExpression lowRow8Cell13RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow8Cell13Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow8Cell13RootRectangle) (tree := lowRow8Cell13RootTree)
  · norm_num [lowRow8Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell13RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow8Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell13RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow8Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell13RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow8Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow8Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow8Cell13RootTree_certified

private def lowRow8Cell14RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 64) ((1 : ℚ) / 8),
    RatBall.ofBounds ((13 : ℚ) / 32) ((7 : ℚ) / 16)⟩

private def lowRow8Cell14RootTree : Subdivision :=
.leaf .interval

private theorem lowRow8Cell14RootTree_certified :
    certifySubdivision 12 64 32 lowRow8Cell14RootRectangle
      CertificateObjective.endpointExpression lowRow8Cell14RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow8Cell14Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow8Cell14RootRectangle) (tree := lowRow8Cell14RootTree)
  · norm_num [lowRow8Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell14RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow8Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell14RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow8Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell14RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow8Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow8Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow8Cell14RootTree_certified

private def lowRow8Cell15RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 64) ((1 : ℚ) / 8),
    RatBall.ofBounds ((7 : ℚ) / 16) ((15 : ℚ) / 32)⟩

private def lowRow8Cell15RootTree : Subdivision :=
.leaf .interval

private theorem lowRow8Cell15RootTree_certified :
    certifySubdivision 12 64 32 lowRow8Cell15RootRectangle
      CertificateObjective.endpointExpression lowRow8Cell15RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow8Cell15Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow8Cell15RootRectangle) (tree := lowRow8Cell15RootTree)
  · norm_num [lowRow8Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell15RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow8Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell15RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow8Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell15RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow8Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow8Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow8Cell15RootTree_certified

private def lowRow8Cell16RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((7 : ℚ) / 64) ((1 : ℚ) / 8),
    RatBall.ofBounds ((15 : ℚ) / 32) ((1 : ℚ) / 2)⟩

private def lowRow8Cell16RootTree : Subdivision :=
.leaf .interval

private theorem lowRow8Cell16RootTree_certified :
    certifySubdivision 12 64 32 lowRow8Cell16RootRectangle
      CertificateObjective.endpointExpression lowRow8Cell16RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow8Cell16Root_nonneg {a q : ℝ}
    (haLower : ((7 : ℝ) / 64) ≤ a)
    (haUpper : a ≤ ((1 : ℝ) / 8))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow8Cell16RootRectangle) (tree := lowRow8Cell16RootTree)
  · norm_num [lowRow8Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell16RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow8Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell16RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow8Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow8Cell16RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow8Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow8Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow8Cell16RootTree_certified

end Frankl
