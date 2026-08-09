import Frankl.EndpointCertificate

namespace Frankl

private def qOneCell16RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((19449 : ℚ) / 400000) ((330233 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell16RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell16RootTree_certified :
    certifySubdivision 12 64 32 qOneCell16RootRectangle
      CertificateObjective.endpointExpression qOneCell16RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell16Root_nonneg {a q : ℝ}
    (haLower : ((19449 : ℝ) / 400000) ≤ a)
    (haUpper : a ≤ ((330233 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell16RootRectangle) (tree := qOneCell16RootTree)
  · norm_num [qOneCell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell16RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell16RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell16RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell16RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell16RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell16RootTree_certified

private def qOneCell17RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((330233 : ℚ) / 6400000) ((174641 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell17RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell17RootTree_certified :
    certifySubdivision 12 64 32 qOneCell17RootRectangle
      CertificateObjective.endpointExpression qOneCell17RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell17Root_nonneg {a q : ℝ}
    (haLower : ((330233 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((174641 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell17RootRectangle) (tree := qOneCell17RootTree)
  · norm_num [qOneCell17RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell17RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell17RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell17RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell17RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell17RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell17RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell17RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell17RootTree_certified

private def qOneCell18RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((174641 : ℚ) / 3200000) ((368331 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell18RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell18RootTree_certified :
    certifySubdivision 12 64 32 qOneCell18RootRectangle
      CertificateObjective.endpointExpression qOneCell18RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell18Root_nonneg {a q : ℝ}
    (haLower : ((174641 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((368331 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell18RootRectangle) (tree := qOneCell18RootTree)
  · norm_num [qOneCell18RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell18RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell18RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell18RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell18RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell18RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell18RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell18RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell18RootTree_certified

private def qOneCell19RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((368331 : ℚ) / 6400000) ((19369 : ℚ) / 320000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell19RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell19RootTree_certified :
    certifySubdivision 12 64 32 qOneCell19RootRectangle
      CertificateObjective.endpointExpression qOneCell19RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell19Root_nonneg {a q : ℝ}
    (haLower : ((368331 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((19369 : ℝ) / 320000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell19RootRectangle) (tree := qOneCell19RootTree)
  · norm_num [qOneCell19RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell19RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell19RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell19RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell19RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell19RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell19RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell19RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell19RootTree_certified

private def qOneCell20RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((19369 : ℚ) / 320000) ((406429 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell20RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell20RootTree_certified :
    certifySubdivision 12 64 32 qOneCell20RootRectangle
      CertificateObjective.endpointExpression qOneCell20RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell20Root_nonneg {a q : ℝ}
    (haLower : ((19369 : ℝ) / 320000) ≤ a)
    (haUpper : a ≤ ((406429 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell20RootRectangle) (tree := qOneCell20RootTree)
  · norm_num [qOneCell20RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell20RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell20RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell20RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell20RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell20RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell20RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell20RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell20RootTree_certified

private def qOneCell21RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((406429 : ℚ) / 6400000) ((212739 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell21RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell21RootTree_certified :
    certifySubdivision 12 64 32 qOneCell21RootRectangle
      CertificateObjective.endpointExpression qOneCell21RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell21Root_nonneg {a q : ℝ}
    (haLower : ((406429 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((212739 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell21RootRectangle) (tree := qOneCell21RootTree)
  · norm_num [qOneCell21RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell21RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell21RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell21RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell21RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell21RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell21RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell21RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell21RootTree_certified

private def qOneCell22RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((212739 : ℚ) / 3200000) ((444527 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell22RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell22RootTree_certified :
    certifySubdivision 12 64 32 qOneCell22RootRectangle
      CertificateObjective.endpointExpression qOneCell22RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell22Root_nonneg {a q : ℝ}
    (haLower : ((212739 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((444527 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell22RootRectangle) (tree := qOneCell22RootTree)
  · norm_num [qOneCell22RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell22RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell22RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell22RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell22RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell22RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell22RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell22RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell22RootTree_certified

private def qOneCell23RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((444527 : ℚ) / 6400000) ((57947 : ℚ) / 800000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell23RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell23RootTree_certified :
    certifySubdivision 12 64 32 qOneCell23RootRectangle
      CertificateObjective.endpointExpression qOneCell23RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell23Root_nonneg {a q : ℝ}
    (haLower : ((444527 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((57947 : ℝ) / 800000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell23RootRectangle) (tree := qOneCell23RootTree)
  · norm_num [qOneCell23RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell23RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell23RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell23RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell23RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell23RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell23RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell23RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell23RootTree_certified

private def qOneCell24RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((57947 : ℚ) / 800000) ((3861 : ℚ) / 51200),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell24RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell24RootTree_certified :
    certifySubdivision 12 64 32 qOneCell24RootRectangle
      CertificateObjective.endpointExpression qOneCell24RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell24Root_nonneg {a q : ℝ}
    (haLower : ((57947 : ℝ) / 800000) ≤ a)
    (haUpper : a ≤ ((3861 : ℝ) / 51200))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell24RootRectangle) (tree := qOneCell24RootTree)
  · norm_num [qOneCell24RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell24RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell24RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell24RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell24RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell24RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell24RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell24RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell24RootTree_certified

private def qOneCell25RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3861 : ℚ) / 51200) ((250837 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell25RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell25RootTree_certified :
    certifySubdivision 12 64 32 qOneCell25RootRectangle
      CertificateObjective.endpointExpression qOneCell25RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell25Root_nonneg {a q : ℝ}
    (haLower : ((3861 : ℝ) / 51200) ≤ a)
    (haUpper : a ≤ ((250837 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell25RootRectangle) (tree := qOneCell25RootTree)
  · norm_num [qOneCell25RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell25RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell25RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell25RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell25RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell25RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell25RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell25RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell25RootTree_certified

private def qOneCell26RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((250837 : ℚ) / 3200000) ((520723 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell26RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell26RootTree_certified :
    certifySubdivision 12 64 32 qOneCell26RootRectangle
      CertificateObjective.endpointExpression qOneCell26RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell26Root_nonneg {a q : ℝ}
    (haLower : ((250837 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((520723 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell26RootRectangle) (tree := qOneCell26RootTree)
  · norm_num [qOneCell26RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell26RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell26RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell26RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell26RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell26RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell26RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell26RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell26RootTree_certified

private def qOneCell27RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((520723 : ℚ) / 6400000) ((134943 : ℚ) / 1600000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell27RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell27RootTree_certified :
    certifySubdivision 12 64 32 qOneCell27RootRectangle
      CertificateObjective.endpointExpression qOneCell27RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell27Root_nonneg {a q : ℝ}
    (haLower : ((520723 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((134943 : ℝ) / 1600000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell27RootRectangle) (tree := qOneCell27RootTree)
  · norm_num [qOneCell27RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell27RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell27RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell27RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell27RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell27RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell27RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell27RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell27RootTree_certified

private def qOneCell28RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((134943 : ℚ) / 1600000) ((558821 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell28RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell28RootTree_certified :
    certifySubdivision 12 64 32 qOneCell28RootRectangle
      CertificateObjective.endpointExpression qOneCell28RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell28Root_nonneg {a q : ℝ}
    (haLower : ((134943 : ℝ) / 1600000) ≤ a)
    (haUpper : a ≤ ((558821 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell28RootRectangle) (tree := qOneCell28RootTree)
  · norm_num [qOneCell28RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell28RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell28RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell28RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell28RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell28RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell28RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell28RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell28RootTree_certified

private def qOneCell29RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((558821 : ℚ) / 6400000) ((57787 : ℚ) / 640000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell29RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell29RootTree_certified :
    certifySubdivision 12 64 32 qOneCell29RootRectangle
      CertificateObjective.endpointExpression qOneCell29RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell29Root_nonneg {a q : ℝ}
    (haLower : ((558821 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((57787 : ℝ) / 640000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell29RootRectangle) (tree := qOneCell29RootTree)
  · norm_num [qOneCell29RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell29RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell29RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell29RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell29RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell29RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell29RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell29RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell29RootTree_certified

private def qOneCell30RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((57787 : ℚ) / 640000) ((596919 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell30RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell30RootTree_certified :
    certifySubdivision 12 64 32 qOneCell30RootRectangle
      CertificateObjective.endpointExpression qOneCell30RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell30Root_nonneg {a q : ℝ}
    (haLower : ((57787 : ℝ) / 640000) ≤ a)
    (haUpper : a ≤ ((596919 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell30RootRectangle) (tree := qOneCell30RootTree)
  · norm_num [qOneCell30RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell30RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell30RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell30RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell30RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell30RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell30RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell30RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell30RootTree_certified

private def qOneCell31RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((596919 : ℚ) / 6400000) ((19249 : ℚ) / 200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell31RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell31RootTree_certified :
    certifySubdivision 12 64 32 qOneCell31RootRectangle
      CertificateObjective.endpointExpression qOneCell31RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell31Root_nonneg {a q : ℝ}
    (haLower : ((596919 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((19249 : ℝ) / 200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell31RootRectangle) (tree := qOneCell31RootTree)
  · norm_num [qOneCell31RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell31RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell31RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell31RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell31RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell31RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell31RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell31RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell31RootTree_certified

end Frankl
