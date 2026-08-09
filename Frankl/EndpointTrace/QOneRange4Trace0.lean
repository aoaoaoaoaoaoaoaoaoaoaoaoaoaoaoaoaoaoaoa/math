import Frankl.EndpointCertificate

namespace Frankl

private def qOneCell64RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((19149 : ℚ) / 100000) ((248917 : ℚ) / 1280000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell64RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell64RootTree_certified :
    certifySubdivision 12 64 32 qOneCell64RootRectangle
      CertificateObjective.endpointExpression qOneCell64RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell64Root_nonneg {a q : ℝ}
    (haLower : ((19149 : ℝ) / 100000) ≤ a)
    (haUpper : a ≤ ((248917 : ℝ) / 1280000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell64RootRectangle) (tree := qOneCell64RootTree)
  · norm_num [qOneCell64RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell64RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell64RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell64RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell64RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell64RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell64RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell64RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell64RootTree_certified

private def qOneCell65RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((248917 : ℚ) / 1280000) ((631817 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell65RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell65RootTree_certified :
    certifySubdivision 12 64 32 qOneCell65RootRectangle
      CertificateObjective.endpointExpression qOneCell65RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell65Root_nonneg {a q : ℝ}
    (haLower : ((248917 : ℝ) / 1280000) ≤ a)
    (haUpper : a ≤ ((631817 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell65RootRectangle) (tree := qOneCell65RootTree)
  · norm_num [qOneCell65RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell65RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell65RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell65RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell65RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell65RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell65RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell65RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell65RootTree_certified

private def qOneCell66RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((631817 : ℚ) / 3200000) ((1282683 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell66RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell66RootTree_certified :
    certifySubdivision 12 64 32 qOneCell66RootRectangle
      CertificateObjective.endpointExpression qOneCell66RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell66Root_nonneg {a q : ℝ}
    (haLower : ((631817 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((1282683 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell66RootRectangle) (tree := qOneCell66RootTree)
  · norm_num [qOneCell66RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell66RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell66RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell66RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell66RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell66RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell66RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell66RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell66RootTree_certified

private def qOneCell67RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1282683 : ℚ) / 6400000) ((325433 : ℚ) / 1600000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell67RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell67RootTree_certified :
    certifySubdivision 12 64 32 qOneCell67RootRectangle
      CertificateObjective.endpointExpression qOneCell67RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell67Root_nonneg {a q : ℝ}
    (haLower : ((1282683 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((325433 : ℝ) / 1600000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell67RootRectangle) (tree := qOneCell67RootTree)
  · norm_num [qOneCell67RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell67RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell67RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell67RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell67RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell67RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell67RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell67RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell67RootTree_certified

private def qOneCell68RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((325433 : ℚ) / 1600000) ((1320781 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell68RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell68RootTree_certified :
    certifySubdivision 12 64 32 qOneCell68RootRectangle
      CertificateObjective.endpointExpression qOneCell68RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell68Root_nonneg {a q : ℝ}
    (haLower : ((325433 : ℝ) / 1600000) ≤ a)
    (haUpper : a ≤ ((1320781 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell68RootRectangle) (tree := qOneCell68RootTree)
  · norm_num [qOneCell68RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell68RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell68RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell68RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell68RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell68RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell68RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell68RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell68RootTree_certified

private def qOneCell69RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1320781 : ℚ) / 6400000) ((133983 : ℚ) / 640000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell69RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell69RootTree_certified :
    certifySubdivision 12 64 32 qOneCell69RootRectangle
      CertificateObjective.endpointExpression qOneCell69RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell69Root_nonneg {a q : ℝ}
    (haLower : ((1320781 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((133983 : ℝ) / 640000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell69RootRectangle) (tree := qOneCell69RootTree)
  · norm_num [qOneCell69RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell69RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell69RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell69RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell69RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell69RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell69RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell69RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell69RootTree_certified

private def qOneCell70RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((133983 : ℚ) / 640000) ((1358879 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell70RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell70RootTree_certified :
    certifySubdivision 12 64 32 qOneCell70RootRectangle
      CertificateObjective.endpointExpression qOneCell70RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell70Root_nonneg {a q : ℝ}
    (haLower : ((133983 : ℝ) / 640000) ≤ a)
    (haUpper : a ≤ ((1358879 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell70RootRectangle) (tree := qOneCell70RootTree)
  · norm_num [qOneCell70RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell70RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell70RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell70RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell70RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell70RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell70RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell70RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell70RootTree_certified

private def qOneCell71RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1358879 : ℚ) / 6400000) ((172241 : ℚ) / 800000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell71RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell71RootTree_certified :
    certifySubdivision 12 64 32 qOneCell71RootRectangle
      CertificateObjective.endpointExpression qOneCell71RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell71Root_nonneg {a q : ℝ}
    (haLower : ((1358879 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((172241 : ℝ) / 800000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell71RootRectangle) (tree := qOneCell71RootTree)
  · norm_num [qOneCell71RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell71RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell71RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell71RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell71RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell71RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell71RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell71RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell71RootTree_certified

private def qOneCell72RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((172241 : ℚ) / 800000) ((1396977 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell72RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell72RootTree_certified :
    certifySubdivision 12 64 32 qOneCell72RootRectangle
      CertificateObjective.endpointExpression qOneCell72RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell72Root_nonneg {a q : ℝ}
    (haLower : ((172241 : ℝ) / 800000) ≤ a)
    (haUpper : a ≤ ((1396977 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell72RootRectangle) (tree := qOneCell72RootTree)
  · norm_num [qOneCell72RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell72RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell72RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell72RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell72RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell72RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell72RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell72RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell72RootTree_certified

private def qOneCell73RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1396977 : ℚ) / 6400000) ((708013 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell73RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell73RootTree_certified :
    certifySubdivision 12 64 32 qOneCell73RootRectangle
      CertificateObjective.endpointExpression qOneCell73RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell73Root_nonneg {a q : ℝ}
    (haLower : ((1396977 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((708013 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell73RootRectangle) (tree := qOneCell73RootTree)
  · norm_num [qOneCell73RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell73RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell73RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell73RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell73RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell73RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell73RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell73RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell73RootTree_certified

private def qOneCell74RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((708013 : ℚ) / 3200000) ((57403 : ℚ) / 256000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell74RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell74RootTree_certified :
    certifySubdivision 12 64 32 qOneCell74RootRectangle
      CertificateObjective.endpointExpression qOneCell74RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell74Root_nonneg {a q : ℝ}
    (haLower : ((708013 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((57403 : ℝ) / 256000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell74RootRectangle) (tree := qOneCell74RootTree)
  · norm_num [qOneCell74RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell74RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell74RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell74RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell74RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell74RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell74RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell74RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell74RootTree_certified

private def qOneCell75RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((57403 : ℚ) / 256000) ((363531 : ℚ) / 1600000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell75RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell75RootTree_certified :
    certifySubdivision 12 64 32 qOneCell75RootRectangle
      CertificateObjective.endpointExpression qOneCell75RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell75Root_nonneg {a q : ℝ}
    (haLower : ((57403 : ℝ) / 256000) ≤ a)
    (haUpper : a ≤ ((363531 : ℝ) / 1600000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell75RootRectangle) (tree := qOneCell75RootTree)
  · norm_num [qOneCell75RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell75RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell75RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell75RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell75RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell75RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell75RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell75RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell75RootTree_certified

private def qOneCell76RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((363531 : ℚ) / 1600000) ((1473173 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell76RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell76RootTree_certified :
    certifySubdivision 12 64 32 qOneCell76RootRectangle
      CertificateObjective.endpointExpression qOneCell76RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell76Root_nonneg {a q : ℝ}
    (haLower : ((363531 : ℝ) / 1600000) ≤ a)
    (haUpper : a ≤ ((1473173 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell76RootRectangle) (tree := qOneCell76RootTree)
  · norm_num [qOneCell76RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell76RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell76RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell76RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell76RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell76RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell76RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell76RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell76RootTree_certified

private def qOneCell77RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1473173 : ℚ) / 6400000) ((746111 : ℚ) / 3200000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell77RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell77RootTree_certified :
    certifySubdivision 12 64 32 qOneCell77RootRectangle
      CertificateObjective.endpointExpression qOneCell77RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell77Root_nonneg {a q : ℝ}
    (haLower : ((1473173 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((746111 : ℝ) / 3200000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell77RootRectangle) (tree := qOneCell77RootTree)
  · norm_num [qOneCell77RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell77RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell77RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell77RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell77RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell77RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell77RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell77RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell77RootTree_certified

private def qOneCell78RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((746111 : ℚ) / 3200000) ((1511271 : ℚ) / 6400000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell78RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell78RootTree_certified :
    certifySubdivision 12 64 32 qOneCell78RootRectangle
      CertificateObjective.endpointExpression qOneCell78RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell78Root_nonneg {a q : ℝ}
    (haLower : ((746111 : ℝ) / 3200000) ≤ a)
    (haUpper : a ≤ ((1511271 : ℝ) / 6400000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell78RootRectangle) (tree := qOneCell78RootTree)
  · norm_num [qOneCell78RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell78RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell78RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell78RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell78RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell78RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell78RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell78RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell78RootTree_certified

private def qOneCell79RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((1511271 : ℚ) / 6400000) ((19129 : ℚ) / 80000),
    RatBall.ofBounds ((1 : ℚ) / 1) ((1 : ℚ) / 1)⟩

private def qOneCell79RootTree : Subdivision :=
.leaf .interval

private theorem qOneCell79RootTree_certified :
    certifySubdivision 12 64 32 qOneCell79RootRectangle
      CertificateObjective.endpointExpression qOneCell79RootTree =
        some () := by
  rfl

/-- One static reflected endpoint-certificate chunk. -/
theorem qOneCell79Root_nonneg {a q : ℝ}
    (haLower : ((1511271 : ℝ) / 6400000) ≤ a)
    (haUpper : a ≤ ((19129 : ℝ) / 80000))
    (hqLower : ((1 : ℝ) / 1) ≤ q)
    (hqUpper : q ≤ ((1 : ℝ) / 1)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := qOneCell79RootRectangle) (tree := qOneCell79RootTree)
  · norm_num [qOneCell79RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell79RootRectangle, RatBall.ofBounds]
  · norm_num [qOneCell79RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell79RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [qOneCell79RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [qOneCell79RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [qOneCell79RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [qOneCell79RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact qOneCell79RootTree_certified

end Frankl
