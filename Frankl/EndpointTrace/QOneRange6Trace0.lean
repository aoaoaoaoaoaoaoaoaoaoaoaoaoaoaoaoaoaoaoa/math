import Frankl.EndpointCertificate

namespace Frankl

private def qOneCell96RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((57347 : ℚ) / 200000) ((1854153 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell96RootTree : Subdivision :=
.horizontal ((3689257 : ℚ) / 12800000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell96RootTree_certified :
    certifySubdivision 12 64 32 qOneCell96RootRectangle
      CertificateObjective.endpointExpression qOneCell96RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell96Root_nonneg {a q : ℝ}
    (haLower : ((57347 : ℝ) / 200000) ≤ a)
    (haUpper : a ≤ ((1854153 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell96RootRectangle) (tree := qOneCell96RootTree)
  · norm_num [qOneCell96RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell96RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell96RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell96RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell96RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell96RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell96RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell96RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell96RootTree_certified

private def qOneCell97RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1854153 : ℚ) / 6400000) ((936601 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell97RootTree : Subdivision :=
.horizontal ((745471 : ℚ) / 2560000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell97RootTree_certified :
    certifySubdivision 12 64 32 qOneCell97RootRectangle
      CertificateObjective.endpointExpression qOneCell97RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell97Root_nonneg {a q : ℝ}
    (haLower : ((1854153 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((936601 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell97RootRectangle) (tree := qOneCell97RootTree)
  · norm_num [qOneCell97RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell97RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell97RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell97RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell97RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell97RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell97RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell97RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell97RootTree_certified

private def qOneCell98RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((936601 : ℚ) / 3200000) ((1892251 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell98RootTree : Subdivision :=
.horizontal ((3765453 : ℚ) / 12800000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell98RootTree_certified :
    certifySubdivision 12 64 32 qOneCell98RootRectangle
      CertificateObjective.endpointExpression qOneCell98RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell98Root_nonneg {a q : ℝ}
    (haLower : ((936601 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((1892251 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell98RootRectangle) (tree := qOneCell98RootTree)
  · norm_num [qOneCell98RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell98RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell98RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell98RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell98RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell98RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell98RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell98RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell98RootTree_certified

private def qOneCell99RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1892251 : ℚ) / 6400000) ((19113 : ℚ) / 64000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell99RootTree : Subdivision :=
.horizontal ((3803551 : ℚ) / 12800000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell99RootTree_certified :
    certifySubdivision 12 64 32 qOneCell99RootRectangle
      CertificateObjective.endpointExpression qOneCell99RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell99Root_nonneg {a q : ℝ}
    (haLower : ((1892251 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((19113 : ℝ) / 64000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell99RootRectangle) (tree := qOneCell99RootTree)
  · norm_num [qOneCell99RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell99RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell99RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell99RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell99RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell99RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell99RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell99RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell99RootTree_certified

private def qOneCell100RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((19113 : ℚ) / 64000) ((1930349 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell100RootTree : Subdivision :=
.horizontal ((3841649 : ℚ) / 12800000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell100RootTree_certified :
    certifySubdivision 12 64 32 qOneCell100RootRectangle
      CertificateObjective.endpointExpression qOneCell100RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell100Root_nonneg {a q : ℝ}
    (haLower : ((19113 : ℝ) / 64000) ≤ a)
    (haUpper : a ≤ ((1930349 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell100RootRectangle) (tree := qOneCell100RootTree)
  · norm_num [qOneCell100RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell100RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell100RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell100RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell100RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell100RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell100RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell100RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell100RootTree_certified

private def qOneCell101RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1930349 : ℚ) / 6400000) ((974699 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell101RootTree : Subdivision :=
.horizontal ((3879747 : ℚ) / 12800000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell101RootTree_certified :
    certifySubdivision 12 64 32 qOneCell101RootRectangle
      CertificateObjective.endpointExpression qOneCell101RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell101Root_nonneg {a q : ℝ}
    (haLower : ((1930349 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((974699 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell101RootRectangle) (tree := qOneCell101RootTree)
  · norm_num [qOneCell101RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell101RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell101RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell101RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell101RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell101RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell101RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell101RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell101RootTree_certified

private def qOneCell102RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((974699 : ℚ) / 3200000) ((1968447 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell102RootTree : Subdivision :=
.horizontal ((783569 : ℚ) / 2560000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell102RootTree_certified :
    certifySubdivision 12 64 32 qOneCell102RootRectangle
      CertificateObjective.endpointExpression qOneCell102RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell102Root_nonneg {a q : ℝ}
    (haLower : ((974699 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((1968447 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell102RootRectangle) (tree := qOneCell102RootTree)
  · norm_num [qOneCell102RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell102RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell102RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell102RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell102RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell102RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell102RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell102RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell102RootTree_certified

private def qOneCell103RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1968447 : ℚ) / 6400000) ((248437 : ℚ) / 800000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell103RootTree : Subdivision :=
.horizontal ((3955943 : ℚ) / 12800000)
  (.leaf .interval)
  (.leaf .interval)

private theorem qOneCell103RootTree_certified :
    certifySubdivision 12 64 32 qOneCell103RootRectangle
      CertificateObjective.endpointExpression qOneCell103RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell103Root_nonneg {a q : ℝ}
    (haLower : ((1968447 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((248437 : ℝ) / 800000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell103RootRectangle) (tree := qOneCell103RootTree)
  · norm_num [qOneCell103RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell103RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell103RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell103RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell103RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell103RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell103RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell103RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell103RootTree_certified

private def qOneCell104RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((248437 : ℚ) / 800000) ((401309 : ℚ) / 1280000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell104RootTree : Subdivision :=
.horizontal ((3994041 : ℚ) / 12800000)
  (.leaf .interval)
  (.horizontal ((8007131 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))

private theorem qOneCell104RootTree_certified :
    certifySubdivision 12 64 32 qOneCell104RootRectangle
      CertificateObjective.endpointExpression qOneCell104RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell104Root_nonneg {a q : ℝ}
    (haLower : ((248437 : ℝ) / 800000) ≤ a)
    (haUpper : a ≤ ((401309 : ℝ) / 1280000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell104RootRectangle) (tree := qOneCell104RootTree)
  · norm_num [qOneCell104RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell104RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell104RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell104RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell104RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell104RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell104RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell104RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell104RootTree_certified

private def qOneCell105RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((401309 : ℚ) / 1280000) ((1012797 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell105RootTree : Subdivision :=
.horizontal ((4032139 : ℚ) / 12800000)
  (.horizontal ((8045229 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((8083327 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))

private theorem qOneCell105RootTree_certified :
    certifySubdivision 12 64 32 qOneCell105RootRectangle
      CertificateObjective.endpointExpression qOneCell105RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell105Root_nonneg {a q : ℝ}
    (haLower : ((401309 : ℝ) / 1280000) ≤ a)
    (haUpper : a ≤ ((1012797 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell105RootRectangle) (tree := qOneCell105RootTree)
  · norm_num [qOneCell105RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell105RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell105RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell105RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell105RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell105RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell105RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell105RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell105RootTree_certified

private def qOneCell106RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1012797 : ℚ) / 3200000) ((2044643 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell106RootTree : Subdivision :=
.horizontal ((4070237 : ℚ) / 12800000)
  (.horizontal ((324857 : ℚ) / 1024000)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((8159523 : ℚ) / 25600000)
  (.leaf .interval)
  (.leaf .interval))

private theorem qOneCell106RootTree_certified :
    certifySubdivision 12 64 32 qOneCell106RootRectangle
      CertificateObjective.endpointExpression qOneCell106RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell106Root_nonneg {a q : ℝ}
    (haLower : ((1012797 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((2044643 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell106RootRectangle) (tree := qOneCell106RootTree)
  · norm_num [qOneCell106RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell106RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell106RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell106RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell106RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell106RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell106RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell106RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell106RootTree_certified

end Frankl
