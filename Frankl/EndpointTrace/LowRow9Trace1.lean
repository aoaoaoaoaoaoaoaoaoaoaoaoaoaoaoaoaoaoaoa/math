import Frankl.EndpointCertificate

namespace Frankl

private def lowRow9Cell7RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 8) ((9 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 16) ((7 : ℚ) / 32)⟩

private def lowRow9Cell7RootTree : Subdivision :=
.horizontal ((17 : ℚ) / 128)
  (.vertical ((13 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((13 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow9Cell7RootTree_certified :
    certifySubdivision 12 64 32 lowRow9Cell7RootRectangle
      CertificateObjective.endpointExpression lowRow9Cell7RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow9Cell7Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 8) ≤ a)
    (haUpper : a ≤ ((9 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow9Cell7RootRectangle) (tree := lowRow9Cell7RootTree)
  · norm_num [lowRow9Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell7RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow9Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell7RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow9Cell7RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell7RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow9Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow9Cell7RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow9Cell7RootTree_certified

private def lowRow9Cell8RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 8) ((9 : ℚ) / 64),
    RatBall.ofBounds ((7 : ℚ) / 32) ((1 : ℚ) / 4)⟩

private def lowRow9Cell8RootTree : Subdivision :=
.horizontal ((17 : ℚ) / 128)
  (.vertical ((15 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((15 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow9Cell8RootTree_certified :
    certifySubdivision 12 64 32 lowRow9Cell8RootRectangle
      CertificateObjective.endpointExpression lowRow9Cell8RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow9Cell8Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 8) ≤ a)
    (haUpper : a ≤ ((9 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 4)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow9Cell8RootRectangle) (tree := lowRow9Cell8RootTree)
  · norm_num [lowRow9Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell8RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow9Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell8RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow9Cell8RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell8RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow9Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow9Cell8RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow9Cell8RootTree_certified

private def lowRow9Cell9RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 8) ((9 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 4) ((9 : ℚ) / 32)⟩

private def lowRow9Cell9RootTree : Subdivision :=
.horizontal ((17 : ℚ) / 128)
  (.leaf .interval)
  (.vertical ((17 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow9Cell9RootTree_certified :
    certifySubdivision 12 64 32 lowRow9Cell9RootRectangle
      CertificateObjective.endpointExpression lowRow9Cell9RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow9Cell9Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 8) ≤ a)
    (haUpper : a ≤ ((9 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow9Cell9RootRectangle) (tree := lowRow9Cell9RootTree)
  · norm_num [lowRow9Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell9RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow9Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell9RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow9Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell9RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow9Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow9Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow9Cell9RootTree_certified

private def lowRow9Cell10RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 8) ((9 : ℚ) / 64),
    RatBall.ofBounds ((9 : ℚ) / 32) ((5 : ℚ) / 16)⟩

private def lowRow9Cell10RootTree : Subdivision :=
.horizontal ((17 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow9Cell10RootTree_certified :
    certifySubdivision 12 64 32 lowRow9Cell10RootRectangle
      CertificateObjective.endpointExpression lowRow9Cell10RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow9Cell10Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 8) ≤ a)
    (haUpper : a ≤ ((9 : ℝ) / 64))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow9Cell10RootRectangle) (tree := lowRow9Cell10RootTree)
  · norm_num [lowRow9Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell10RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow9Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell10RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow9Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell10RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow9Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow9Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow9Cell10RootTree_certified

private def lowRow9Cell11RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 8) ((9 : ℚ) / 64),
    RatBall.ofBounds ((5 : ℚ) / 16) ((11 : ℚ) / 32)⟩

private def lowRow9Cell11RootTree : Subdivision :=
.horizontal ((17 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow9Cell11RootTree_certified :
    certifySubdivision 12 64 32 lowRow9Cell11RootRectangle
      CertificateObjective.endpointExpression lowRow9Cell11RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow9Cell11Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 8) ≤ a)
    (haUpper : a ≤ ((9 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow9Cell11RootRectangle) (tree := lowRow9Cell11RootTree)
  · norm_num [lowRow9Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell11RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow9Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell11RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow9Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell11RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow9Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow9Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow9Cell11RootTree_certified

private def lowRow9Cell12RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 8) ((9 : ℚ) / 64),
    RatBall.ofBounds ((11 : ℚ) / 32) ((3 : ℚ) / 8)⟩

private def lowRow9Cell12RootTree : Subdivision :=
.horizontal ((17 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow9Cell12RootTree_certified :
    certifySubdivision 12 64 32 lowRow9Cell12RootRectangle
      CertificateObjective.endpointExpression lowRow9Cell12RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow9Cell12Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 8) ≤ a)
    (haUpper : a ≤ ((9 : ℝ) / 64))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow9Cell12RootRectangle) (tree := lowRow9Cell12RootTree)
  · norm_num [lowRow9Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell12RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow9Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell12RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow9Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell12RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow9Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow9Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow9Cell12RootTree_certified

private def lowRow9Cell13RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 8) ((9 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 8) ((13 : ℚ) / 32)⟩

private def lowRow9Cell13RootTree : Subdivision :=
.leaf .interval

private theorem lowRow9Cell13RootTree_certified :
    certifySubdivision 12 64 32 lowRow9Cell13RootRectangle
      CertificateObjective.endpointExpression lowRow9Cell13RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow9Cell13Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 8) ≤ a)
    (haUpper : a ≤ ((9 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow9Cell13RootRectangle) (tree := lowRow9Cell13RootTree)
  · norm_num [lowRow9Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell13RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow9Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell13RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow9Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell13RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow9Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow9Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow9Cell13RootTree_certified

private def lowRow9Cell14RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 8) ((9 : ℚ) / 64),
    RatBall.ofBounds ((13 : ℚ) / 32) ((7 : ℚ) / 16)⟩

private def lowRow9Cell14RootTree : Subdivision :=
.leaf .interval

private theorem lowRow9Cell14RootTree_certified :
    certifySubdivision 12 64 32 lowRow9Cell14RootRectangle
      CertificateObjective.endpointExpression lowRow9Cell14RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow9Cell14Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 8) ≤ a)
    (haUpper : a ≤ ((9 : ℝ) / 64))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow9Cell14RootRectangle) (tree := lowRow9Cell14RootTree)
  · norm_num [lowRow9Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell14RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow9Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell14RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow9Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell14RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow9Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow9Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow9Cell14RootTree_certified

private def lowRow9Cell15RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 8) ((9 : ℚ) / 64),
    RatBall.ofBounds ((7 : ℚ) / 16) ((15 : ℚ) / 32)⟩

private def lowRow9Cell15RootTree : Subdivision :=
.leaf .interval

private theorem lowRow9Cell15RootTree_certified :
    certifySubdivision 12 64 32 lowRow9Cell15RootRectangle
      CertificateObjective.endpointExpression lowRow9Cell15RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow9Cell15Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 8) ≤ a)
    (haUpper : a ≤ ((9 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow9Cell15RootRectangle) (tree := lowRow9Cell15RootTree)
  · norm_num [lowRow9Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell15RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow9Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell15RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow9Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell15RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow9Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow9Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow9Cell15RootTree_certified

private def lowRow9Cell16RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1 : ℚ) / 8) ((9 : ℚ) / 64),
    RatBall.ofBounds ((15 : ℚ) / 32) ((1 : ℚ) / 2)⟩

private def lowRow9Cell16RootTree : Subdivision :=
.leaf .interval

private theorem lowRow9Cell16RootTree_certified :
    certifySubdivision 12 64 32 lowRow9Cell16RootRectangle
      CertificateObjective.endpointExpression lowRow9Cell16RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow9Cell16Root_nonneg {a q : ℝ}
    (haLower : ((1 : ℝ) / 8) ≤ a)
    (haUpper : a ≤ ((9 : ℝ) / 64))
    (hqLower : ((15 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 2)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow9Cell16RootRectangle) (tree := lowRow9Cell16RootTree)
  · norm_num [lowRow9Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell16RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow9Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell16RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow9Cell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow9Cell16RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow9Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow9Cell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow9Cell16RootTree_certified

end Frankl
