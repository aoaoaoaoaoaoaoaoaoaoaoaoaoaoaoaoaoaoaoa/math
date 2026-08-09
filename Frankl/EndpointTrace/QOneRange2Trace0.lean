import Frankl.EndpointCertificate

namespace Frankl

private def qOneCell32RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((19249 : ℚ) / 200000) ((635017 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell32RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell32RootTree_certified :
    certifySubdivision 12 64 32 qOneCell32RootRectangle
      CertificateObjective.endpointExpression qOneCell32RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell32Root_nonneg {a q : ℝ}
    (haLower : ((19249 : ℝ) / 200000) ≤ a)
    (haUpper : a ≤ ((635017 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell32RootRectangle) (tree := qOneCell32RootTree)
  · norm_num [qOneCell32RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell32RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell32RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell32RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell32RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell32RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell32RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell32RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell32RootTree_certified

private def qOneCell33RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((635017 : ℚ) / 6400000) ((327033 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell33RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell33RootTree_certified :
    certifySubdivision 12 64 32 qOneCell33RootRectangle
      CertificateObjective.endpointExpression qOneCell33RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell33Root_nonneg {a q : ℝ}
    (haLower : ((635017 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((327033 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell33RootRectangle) (tree := qOneCell33RootTree)
  · norm_num [qOneCell33RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell33RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell33RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell33RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell33RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell33RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell33RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell33RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell33RootTree_certified

private def qOneCell34RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((327033 : ℚ) / 3200000) ((134623 : ℚ) / 1280000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell34RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell34RootTree_certified :
    certifySubdivision 12 64 32 qOneCell34RootRectangle
      CertificateObjective.endpointExpression qOneCell34RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell34Root_nonneg {a q : ℝ}
    (haLower : ((327033 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((134623 : ℝ) / 1280000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell34RootRectangle) (tree := qOneCell34RootTree)
  · norm_num [qOneCell34RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell34RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell34RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell34RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell34RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell34RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell34RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell34RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell34RootTree_certified

private def qOneCell35RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((134623 : ℚ) / 1280000) ((173041 : ℚ) / 1600000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell35RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell35RootTree_certified :
    certifySubdivision 12 64 32 qOneCell35RootRectangle
      CertificateObjective.endpointExpression qOneCell35RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell35Root_nonneg {a q : ℝ}
    (haLower : ((134623 : ℝ) / 1280000) ≤ a)
    (haUpper : a ≤ ((173041 : ℝ) / 1600000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell35RootRectangle) (tree := qOneCell35RootTree)
  · norm_num [qOneCell35RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell35RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell35RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell35RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell35RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell35RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell35RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell35RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell35RootTree_certified

private def qOneCell36RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((173041 : ℚ) / 1600000) ((711213 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell36RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell36RootTree_certified :
    certifySubdivision 12 64 32 qOneCell36RootRectangle
      CertificateObjective.endpointExpression qOneCell36RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell36Root_nonneg {a q : ℝ}
    (haLower : ((173041 : ℝ) / 1600000) ≤ a)
    (haUpper : a ≤ ((711213 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell36RootRectangle) (tree := qOneCell36RootTree)
  · norm_num [qOneCell36RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell36RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell36RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell36RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell36RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell36RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell36RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell36RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell36RootTree_certified

private def qOneCell37RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((711213 : ℚ) / 6400000) ((365131 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell37RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell37RootTree_certified :
    certifySubdivision 12 64 32 qOneCell37RootRectangle
      CertificateObjective.endpointExpression qOneCell37RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell37Root_nonneg {a q : ℝ}
    (haLower : ((711213 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((365131 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell37RootRectangle) (tree := qOneCell37RootTree)
  · norm_num [qOneCell37RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell37RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell37RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell37RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell37RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell37RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell37RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell37RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell37RootTree_certified

private def qOneCell38RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((365131 : ℚ) / 3200000) ((749311 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell38RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell38RootTree_certified :
    certifySubdivision 12 64 32 qOneCell38RootRectangle
      CertificateObjective.endpointExpression qOneCell38RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell38Root_nonneg {a q : ℝ}
    (haLower : ((365131 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((749311 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell38RootRectangle) (tree := qOneCell38RootTree)
  · norm_num [qOneCell38RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell38RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell38RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell38RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell38RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell38RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell38RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell38RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell38RootTree_certified

private def qOneCell39RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((749311 : ℚ) / 6400000) ((19209 : ℚ) / 160000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell39RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell39RootTree_certified :
    certifySubdivision 12 64 32 qOneCell39RootRectangle
      CertificateObjective.endpointExpression qOneCell39RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell39Root_nonneg {a q : ℝ}
    (haLower : ((749311 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((19209 : ℝ) / 160000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell39RootRectangle) (tree := qOneCell39RootTree)
  · norm_num [qOneCell39RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell39RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell39RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell39RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell39RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell39RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell39RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell39RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell39RootTree_certified

private def qOneCell40RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((19209 : ℚ) / 160000) ((787409 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell40RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell40RootTree_certified :
    certifySubdivision 12 64 32 qOneCell40RootRectangle
      CertificateObjective.endpointExpression qOneCell40RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell40Root_nonneg {a q : ℝ}
    (haLower : ((19209 : ℝ) / 160000) ≤ a)
    (haUpper : a ≤ ((787409 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell40RootRectangle) (tree := qOneCell40RootTree)
  · norm_num [qOneCell40RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell40RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell40RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell40RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell40RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell40RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell40RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell40RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell40RootTree_certified

private def qOneCell41RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((787409 : ℚ) / 6400000) ((403229 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell41RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell41RootTree_certified :
    certifySubdivision 12 64 32 qOneCell41RootRectangle
      CertificateObjective.endpointExpression qOneCell41RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell41Root_nonneg {a q : ℝ}
    (haLower : ((787409 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((403229 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell41RootRectangle) (tree := qOneCell41RootTree)
  · norm_num [qOneCell41RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell41RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell41RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell41RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell41RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell41RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell41RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell41RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell41RootTree_certified

private def qOneCell42RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((403229 : ℚ) / 3200000) ((825507 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell42RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell42RootTree_certified :
    certifySubdivision 12 64 32 qOneCell42RootRectangle
      CertificateObjective.endpointExpression qOneCell42RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell42Root_nonneg {a q : ℝ}
    (haLower : ((403229 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((825507 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell42RootRectangle) (tree := qOneCell42RootTree)
  · norm_num [qOneCell42RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell42RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell42RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell42RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell42RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell42RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell42RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell42RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell42RootTree_certified

private def qOneCell43RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((825507 : ℚ) / 6400000) ((211139 : ℚ) / 1600000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell43RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell43RootTree_certified :
    certifySubdivision 12 64 32 qOneCell43RootRectangle
      CertificateObjective.endpointExpression qOneCell43RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell43Root_nonneg {a q : ℝ}
    (haLower : ((825507 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((211139 : ℝ) / 1600000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell43RootRectangle) (tree := qOneCell43RootTree)
  · norm_num [qOneCell43RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell43RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell43RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell43RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell43RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell43RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell43RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell43RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell43RootTree_certified

private def qOneCell44RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((211139 : ℚ) / 1600000) ((172721 : ℚ) / 1280000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell44RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell44RootTree_certified :
    certifySubdivision 12 64 32 qOneCell44RootRectangle
      CertificateObjective.endpointExpression qOneCell44RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell44Root_nonneg {a q : ℝ}
    (haLower : ((211139 : ℝ) / 1600000) ≤ a)
    (haUpper : a ≤ ((172721 : ℝ) / 1280000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell44RootRectangle) (tree := qOneCell44RootTree)
  · norm_num [qOneCell44RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell44RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell44RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell44RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell44RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell44RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell44RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell44RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell44RootTree_certified

private def qOneCell45RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((172721 : ℚ) / 1280000) ((441327 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell45RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell45RootTree_certified :
    certifySubdivision 12 64 32 qOneCell45RootRectangle
      CertificateObjective.endpointExpression qOneCell45RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell45Root_nonneg {a q : ℝ}
    (haLower : ((172721 : ℝ) / 1280000) ≤ a)
    (haUpper : a ≤ ((441327 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell45RootRectangle) (tree := qOneCell45RootTree)
  · norm_num [qOneCell45RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell45RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell45RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell45RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell45RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell45RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell45RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell45RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell45RootTree_certified

private def qOneCell46RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((441327 : ℚ) / 3200000) ((901703 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell46RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell46RootTree_certified :
    certifySubdivision 12 64 32 qOneCell46RootRectangle
      CertificateObjective.endpointExpression qOneCell46RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell46Root_nonneg {a q : ℝ}
    (haLower : ((441327 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((901703 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell46RootRectangle) (tree := qOneCell46RootTree)
  · norm_num [qOneCell46RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell46RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell46RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell46RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell46RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell46RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell46RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell46RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell46RootTree_certified

private def qOneCell47RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((901703 : ℚ) / 6400000) ((57547 : ℚ) / 400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell47RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell47RootTree_certified :
    certifySubdivision 12 64 32 qOneCell47RootRectangle
      CertificateObjective.endpointExpression qOneCell47RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell47Root_nonneg {a q : ℝ}
    (haLower : ((901703 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((57547 : ℝ) / 400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell47RootRectangle) (tree := qOneCell47RootTree)
  · norm_num [qOneCell47RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell47RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell47RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell47RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell47RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell47RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell47RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell47RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell47RootTree_certified

end Frankl
