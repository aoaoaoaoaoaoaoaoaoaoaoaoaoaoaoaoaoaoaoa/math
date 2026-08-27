import Frankl.EndpointCertificate

namespace Frankl

private def lowRow13Cell9RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 16) ((13 : ℚ) / 64),
    RatBall.ofBounds ((1 : ℚ) / 4) ((9 : ℚ) / 32)⟩

private def lowRow13Cell9RootTree : Subdivision :=
.horizontal ((25 : ℚ) / 128)
  (.vertical ((17 : ℚ) / 64)
  (.horizontal ((49 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((49 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))
  (.vertical ((17 : ℚ) / 64)
  (.horizontal ((51 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.horizontal ((51 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval)))

set_option maxHeartbeats 1000000 in
-- Kernel normalization of this reflected subdivision exceeds Lean's default heartbeat budget.
private theorem lowRow13Cell9RootTree_certified :
    certifySubdivision 12 64 32 lowRow13Cell9RootRectangle
      CertificateObjective.endpointExpression lowRow13Cell9RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow13Cell9Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((1 : ℝ) / 4) ≤ q)
    (hqUpper : q ≤ ((9 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow13Cell9RootRectangle) (tree := lowRow13Cell9RootTree)
  · norm_num [lowRow13Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell9RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow13Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell9RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow13Cell9RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell9RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow13Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow13Cell9RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow13Cell9RootTree_certified

private def lowRow13Cell10RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 16) ((13 : ℚ) / 64),
    RatBall.ofBounds ((9 : ℚ) / 32) ((5 : ℚ) / 16)⟩

private def lowRow13Cell10RootTree : Subdivision :=
.horizontal ((25 : ℚ) / 128)
  (.vertical ((19 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((19 : ℚ) / 64)
  (.horizontal ((51 : ℚ) / 256)
  (.leaf .interval)
  (.leaf .interval))
  (.leaf .interval))

private theorem lowRow13Cell10RootTree_certified :
    certifySubdivision 12 64 32 lowRow13Cell10RootRectangle
      CertificateObjective.endpointExpression lowRow13Cell10RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow13Cell10Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((9 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((5 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow13Cell10RootRectangle) (tree := lowRow13Cell10RootTree)
  · norm_num [lowRow13Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell10RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow13Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell10RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow13Cell10RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell10RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow13Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow13Cell10RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow13Cell10RootTree_certified

private def lowRow13Cell11RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 16) ((13 : ℚ) / 64),
    RatBall.ofBounds ((5 : ℚ) / 16) ((11 : ℚ) / 32)⟩

private def lowRow13Cell11RootTree : Subdivision :=
.horizontal ((25 : ℚ) / 128)
  (.vertical ((21 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((21 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow13Cell11RootTree_certified :
    certifySubdivision 12 64 32 lowRow13Cell11RootRectangle
      CertificateObjective.endpointExpression lowRow13Cell11RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow13Cell11Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((5 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((11 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow13Cell11RootRectangle) (tree := lowRow13Cell11RootTree)
  · norm_num [lowRow13Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell11RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow13Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell11RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow13Cell11RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell11RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow13Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow13Cell11RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow13Cell11RootTree_certified

private def lowRow13Cell12RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 16) ((13 : ℚ) / 64),
    RatBall.ofBounds ((11 : ℚ) / 32) ((3 : ℚ) / 8)⟩

private def lowRow13Cell12RootTree : Subdivision :=
.horizontal ((25 : ℚ) / 128)
  (.vertical ((23 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))
  (.vertical ((23 : ℚ) / 64)
  (.leaf .interval)
  (.leaf .interval))

private theorem lowRow13Cell12RootTree_certified :
    certifySubdivision 12 64 32 lowRow13Cell12RootRectangle
      CertificateObjective.endpointExpression lowRow13Cell12RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow13Cell12Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((11 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((3 : ℝ) / 8)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow13Cell12RootRectangle) (tree := lowRow13Cell12RootTree)
  · norm_num [lowRow13Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell12RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow13Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell12RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow13Cell12RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell12RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow13Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow13Cell12RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow13Cell12RootTree_certified

private def lowRow13Cell13RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 16) ((13 : ℚ) / 64),
    RatBall.ofBounds ((3 : ℚ) / 8) ((13 : ℚ) / 32)⟩

private def lowRow13Cell13RootTree : Subdivision :=
.horizontal ((25 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow13Cell13RootTree_certified :
    certifySubdivision 12 64 32 lowRow13Cell13RootRectangle
      CertificateObjective.endpointExpression lowRow13Cell13RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow13Cell13Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((3 : ℝ) / 8) ≤ q)
    (hqUpper : q ≤ ((13 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow13Cell13RootRectangle) (tree := lowRow13Cell13RootTree)
  · norm_num [lowRow13Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell13RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow13Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell13RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow13Cell13RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell13RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow13Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow13Cell13RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow13Cell13RootTree_certified

private def lowRow13Cell14RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 16) ((13 : ℚ) / 64),
    RatBall.ofBounds ((13 : ℚ) / 32) ((7 : ℚ) / 16)⟩

private def lowRow13Cell14RootTree : Subdivision :=
.horizontal ((25 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow13Cell14RootTree_certified :
    certifySubdivision 12 64 32 lowRow13Cell14RootRectangle
      CertificateObjective.endpointExpression lowRow13Cell14RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow13Cell14Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((13 : ℝ) / 32) ≤ q)
    (hqUpper : q ≤ ((7 : ℝ) / 16)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow13Cell14RootRectangle) (tree := lowRow13Cell14RootTree)
  · norm_num [lowRow13Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell14RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow13Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell14RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow13Cell14RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell14RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow13Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow13Cell14RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow13Cell14RootTree_certified

private def lowRow13Cell15RootRectangle : RatRectangle :=
  ⟨RatBall.ofBounds ((3 : ℚ) / 16) ((13 : ℚ) / 64),
    RatBall.ofBounds ((7 : ℚ) / 16) ((15 : ℚ) / 32)⟩

private def lowRow13Cell15RootTree : Subdivision :=
.horizontal ((25 : ℚ) / 128)
  (.leaf .interval)
  (.leaf .interval)

private theorem lowRow13Cell15RootTree_certified :
    certifySubdivision 12 64 32 lowRow13Cell15RootRectangle
      CertificateObjective.endpointExpression lowRow13Cell15RootTree =
        some () := by
  close_endpoint_certificate

/-- One static reflected endpoint-certificate chunk. -/
theorem lowRow13Cell15Root_nonneg {a q : ℝ}
    (haLower : ((3 : ℝ) / 16) ≤ a)
    (haUpper : a ≤ ((13 : ℝ) / 64))
    (hqLower : ((7 : ℝ) / 16) ≤ q)
    (hqUpper : q ≤ ((15 : ℝ) / 32)) :
    0 ≤ endpointCertificateObjective a q := by
  apply endpointCertificateObjective_nonneg_of_subdivision
      (rectangle := lowRow13Cell15RootRectangle) (tree := lowRow13Cell15RootTree)
  · norm_num [lowRow13Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell15RootRectangle, RatBall.ofBounds]
  · norm_num [lowRow13Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell15RootRectangle, RatBall.ofBounds, RatBall.upper, abundanceTarget]
  · norm_num [lowRow13Cell15RootRectangle, RatBall.ofBounds, RatBall.lower]
  · norm_num [lowRow13Cell15RootRectangle, RatBall.ofBounds, RatBall.upper]
  · rw [lowRow13Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · rw [lowRow13Cell15RootRectangle]
    apply RatBall.ofBounds_contains <;> norm_num at * <;> linarith
  · exact lowRow13Cell15RootTree_certified

end Frankl
