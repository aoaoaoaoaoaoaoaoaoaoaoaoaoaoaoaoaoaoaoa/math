import Frankl.EndpointCertificate

namespace Frankl

private def qOneCell48RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((57547 : ℚ) / 400000) ((939801 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell48RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell48RootTree_certified :
    certifySubdivision 12 64 32 qOneCell48RootRectangle
      CertificateObjective.endpointExpression qOneCell48RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell48Root_nonneg {a q : ℝ}
    (haLower : ((57547 : ℝ) / 400000) ≤ a)
    (haUpper : a ≤ ((939801 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell48RootRectangle) (tree := qOneCell48RootTree)
  · norm_num [qOneCell48RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell48RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell48RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell48RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell48RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell48RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell48RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell48RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell48RootTree_certified

private def qOneCell49RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((939801 : ℚ) / 6400000) ((19177 : ℚ) / 128000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell49RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell49RootTree_certified :
    certifySubdivision 12 64 32 qOneCell49RootRectangle
      CertificateObjective.endpointExpression qOneCell49RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell49Root_nonneg {a q : ℝ}
    (haLower : ((939801 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((19177 : ℝ) / 128000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell49RootRectangle) (tree := qOneCell49RootTree)
  · norm_num [qOneCell49RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell49RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell49RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell49RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell49RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell49RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell49RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell49RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell49RootTree_certified

private def qOneCell50RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((19177 : ℚ) / 128000) ((977899 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell50RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell50RootTree_certified :
    certifySubdivision 12 64 32 qOneCell50RootRectangle
      CertificateObjective.endpointExpression qOneCell50RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell50Root_nonneg {a q : ℝ}
    (haLower : ((19177 : ℝ) / 128000) ≤ a)
    (haUpper : a ≤ ((977899 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell50RootRectangle) (tree := qOneCell50RootTree)
  · norm_num [qOneCell50RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell50RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell50RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell50RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell50RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell50RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell50RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell50RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell50RootTree_certified

private def qOneCell51RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((977899 : ℚ) / 6400000) ((249237 : ℚ) / 1600000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell51RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell51RootTree_certified :
    certifySubdivision 12 64 32 qOneCell51RootRectangle
      CertificateObjective.endpointExpression qOneCell51RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell51Root_nonneg {a q : ℝ}
    (haLower : ((977899 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((249237 : ℝ) / 1600000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell51RootRectangle) (tree := qOneCell51RootTree)
  · norm_num [qOneCell51RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell51RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell51RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell51RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell51RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell51RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell51RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell51RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell51RootTree_certified

private def qOneCell52RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((249237 : ℚ) / 1600000) ((1015997 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell52RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell52RootTree_certified :
    certifySubdivision 12 64 32 qOneCell52RootRectangle
      CertificateObjective.endpointExpression qOneCell52RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell52Root_nonneg {a q : ℝ}
    (haLower : ((249237 : ℝ) / 1600000) ≤ a)
    (haUpper : a ≤ ((1015997 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell52RootRectangle) (tree := qOneCell52RootTree)
  · norm_num [qOneCell52RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell52RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell52RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell52RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell52RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell52RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell52RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell52RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell52RootTree_certified

private def qOneCell53RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1015997 : ℚ) / 6400000) ((517523 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell53RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell53RootTree_certified :
    certifySubdivision 12 64 32 qOneCell53RootRectangle
      CertificateObjective.endpointExpression qOneCell53RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell53Root_nonneg {a q : ℝ}
    (haLower : ((1015997 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((517523 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell53RootRectangle) (tree := qOneCell53RootTree)
  · norm_num [qOneCell53RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell53RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell53RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell53RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell53RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell53RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell53RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell53RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell53RootTree_certified

private def qOneCell54RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((517523 : ℚ) / 3200000) ((210819 : ℚ) / 1280000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell54RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell54RootTree_certified :
    certifySubdivision 12 64 32 qOneCell54RootRectangle
      CertificateObjective.endpointExpression qOneCell54RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell54Root_nonneg {a q : ℝ}
    (haLower : ((517523 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((210819 : ℝ) / 1280000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell54RootRectangle) (tree := qOneCell54RootTree)
  · norm_num [qOneCell54RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell54RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell54RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell54RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell54RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell54RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell54RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell54RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell54RootTree_certified

private def qOneCell55RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((210819 : ℚ) / 1280000) ((134143 : ℚ) / 800000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell55RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell55RootTree_certified :
    certifySubdivision 12 64 32 qOneCell55RootRectangle
      CertificateObjective.endpointExpression qOneCell55RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell55Root_nonneg {a q : ℝ}
    (haLower : ((210819 : ℝ) / 1280000) ≤ a)
    (haUpper : a ≤ ((134143 : ℝ) / 800000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell55RootRectangle) (tree := qOneCell55RootTree)
  · norm_num [qOneCell55RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell55RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell55RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell55RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell55RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell55RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell55RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell55RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell55RootTree_certified

private def qOneCell56RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((134143 : ℚ) / 800000) ((1092193 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell56RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell56RootTree_certified :
    certifySubdivision 12 64 32 qOneCell56RootRectangle
      CertificateObjective.endpointExpression qOneCell56RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell56Root_nonneg {a q : ℝ}
    (haLower : ((134143 : ℝ) / 800000) ≤ a)
    (haUpper : a ≤ ((1092193 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell56RootRectangle) (tree := qOneCell56RootTree)
  · norm_num [qOneCell56RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell56RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell56RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell56RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell56RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell56RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell56RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell56RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell56RootTree_certified

private def qOneCell57RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1092193 : ℚ) / 6400000) ((555621 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell57RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell57RootTree_certified :
    certifySubdivision 12 64 32 qOneCell57RootRectangle
      CertificateObjective.endpointExpression qOneCell57RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell57Root_nonneg {a q : ℝ}
    (haLower : ((1092193 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((555621 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell57RootRectangle) (tree := qOneCell57RootTree)
  · norm_num [qOneCell57RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell57RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell57RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell57RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell57RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell57RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell57RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell57RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell57RootTree_certified

private def qOneCell58RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((555621 : ℚ) / 3200000) ((1130291 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell58RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell58RootTree_certified :
    certifySubdivision 12 64 32 qOneCell58RootRectangle
      CertificateObjective.endpointExpression qOneCell58RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell58Root_nonneg {a q : ℝ}
    (haLower : ((555621 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((1130291 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell58RootRectangle) (tree := qOneCell58RootTree)
  · norm_num [qOneCell58RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell58RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell58RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell58RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell58RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell58RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell58RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell58RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell58RootTree_certified

private def qOneCell59RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1130291 : ℚ) / 6400000) ((57467 : ℚ) / 320000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell59RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell59RootTree_certified :
    certifySubdivision 12 64 32 qOneCell59RootRectangle
      CertificateObjective.endpointExpression qOneCell59RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell59Root_nonneg {a q : ℝ}
    (haLower : ((1130291 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((57467 : ℝ) / 320000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell59RootRectangle) (tree := qOneCell59RootTree)
  · norm_num [qOneCell59RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell59RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell59RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell59RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell59RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell59RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell59RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell59RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell59RootTree_certified

private def qOneCell60RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((57467 : ℚ) / 320000) ((1168389 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell60RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell60RootTree_certified :
    certifySubdivision 12 64 32 qOneCell60RootRectangle
      CertificateObjective.endpointExpression qOneCell60RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell60Root_nonneg {a q : ℝ}
    (haLower : ((57467 : ℝ) / 320000) ≤ a)
    (haUpper : a ≤ ((1168389 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell60RootRectangle) (tree := qOneCell60RootTree)
  · norm_num [qOneCell60RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell60RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell60RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell60RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell60RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell60RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell60RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell60RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell60RootTree_certified

private def qOneCell61RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1168389 : ℚ) / 6400000) ((593719 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell61RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell61RootTree_certified :
    certifySubdivision 12 64 32 qOneCell61RootRectangle
      CertificateObjective.endpointExpression qOneCell61RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell61Root_nonneg {a q : ℝ}
    (haLower : ((1168389 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((593719 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell61RootRectangle) (tree := qOneCell61RootTree)
  · norm_num [qOneCell61RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell61RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell61RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell61RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell61RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell61RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell61RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell61RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell61RootTree_certified

private def qOneCell62RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((593719 : ℚ) / 3200000) ((1206487 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell62RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell62RootTree_certified :
    certifySubdivision 12 64 32 qOneCell62RootRectangle
      CertificateObjective.endpointExpression qOneCell62RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell62Root_nonneg {a q : ℝ}
    (haLower : ((593719 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((1206487 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell62RootRectangle) (tree := qOneCell62RootTree)
  · norm_num [qOneCell62RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell62RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell62RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell62RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell62RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell62RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell62RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell62RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell62RootTree_certified

private def qOneCell63RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1206487 : ℚ) / 6400000) ((19149 : ℚ) / 100000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell63RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell63RootTree_certified :
    certifySubdivision 12 64 32 qOneCell63RootRectangle
      CertificateObjective.endpointExpression qOneCell63RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell63Root_nonneg {a q : ℝ}
    (haLower : ((1206487 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((19149 : ℝ) / 100000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell63RootRectangle) (tree := qOneCell63RootTree)
  · norm_num [qOneCell63RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell63RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell63RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell63RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell63RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell63RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell63RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell63RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell63RootTree_certified

end Frankl
