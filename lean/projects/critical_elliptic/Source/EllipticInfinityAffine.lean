import EllipticQuarticAffineIso

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
universe u
namespace FourCorner.EllipticQuarticModel.Infinity
variable (K : Type u) [Field K]
abbrev ring := CriticalQuotientChart.affineRing (equation K) 2
abbrev ideal := CriticalQuotientChart.affineIdeal (equation K) 2
def coordinate (j : Fin 3) : ring K := Ideal.Quotient.mk (ideal K) (X j)

theorem dehom_conic : CriticalQuotientChart.affineEquation (equation K) 2 0 =
    (X 0 - X 1 ^ 2 : MvPolynomial (Fin 3) K) := by
  simp [CriticalQuotientChart.affineEquation, equation, conic,
    CriticalAmbientChart.dehom, CriticalAmbientChart.drop]

theorem dehom_cubic : CriticalQuotientChart.affineEquation (equation K) 2 1 =
    (X 2 ^ 2 - X 1 + X 0 * X 1 : MvPolynomial (Fin 3) K) := by
  simp [CriticalQuotientChart.affineEquation, equation, cubicClosure,
    CriticalAmbientChart.dehom, CriticalAmbientChart.drop]

theorem coordinate_conic : coordinate K 0 = coordinate K 1 ^ 2 := by
  have h : Ideal.Quotient.mk (ideal K)
      (CriticalQuotientChart.affineEquation (equation K) 2 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨0,rfl⟩)
  rw [dehom_conic, map_sub, map_pow] at h
  exact sub_eq_zero.mp h

theorem coordinate_cubic : coordinate K 2 ^ 2 = (-coordinate K 1)^3 - (-coordinate K 1) := by
  have h : Ideal.Quotient.mk (ideal K)
      (CriticalQuotientChart.affineEquation (equation K) 2 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨1,rfl⟩)
  rw [dehom_cubic, map_add, map_sub, map_mul, map_pow] at h
  change coordinate K 2 ^ 2 - coordinate K 1 + coordinate K 0 * coordinate K 1 = 0 at h
  rw [coordinate_conic] at h
  linear_combination h

def toNativePre : MvPolynomial (Fin 3) K →ₐ[K] CriticalEllipticField.ring K :=
  MvPolynomial.aeval ![CriticalEllipticField.xRing K ^ 2,
    -CriticalEllipticField.xRing K, CriticalEllipticField.yRing K]

theorem toNativePre_vanish (j : Fin 2) :
    toNativePre K (CriticalQuotientChart.affineEquation (equation K) 2 j) = 0 := by
  fin_cases j
  · change toNativePre K (CriticalQuotientChart.affineEquation (equation K) 2 0) = 0
    rw [dehom_conic]
    simp [toNativePre]
  · change toNativePre K (CriticalQuotientChart.affineEquation (equation K) 2 1) = 0
    rw [dehom_cubic]
    simp only [toNativePre,map_add,map_sub,map_pow,map_mul,MvPolynomial.aeval_X]
    change CriticalEllipticField.yRing K ^ 2 - (-CriticalEllipticField.xRing K) +
      CriticalEllipticField.xRing K ^ 2 * (-CriticalEllipticField.xRing K) = 0
    rw [CriticalEllipticField.ring_equation]
    ring

def toNative : ring K →ₐ[K] CriticalEllipticField.ring K :=
  Ideal.Quotient.liftₐ (ideal K) (toNativePre K) (by
    change ideal K ≤ RingHom.ker (toNativePre K).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact toNativePre_vanish K j)

def fromNative : CriticalEllipticField.ring K →ₐ[K] ring K :=
  AdjoinRoot.liftAlgHom ((CriticalEllipticField.curve K).toAffine.polynomial)
    (Polynomial.aeval (-coordinate K 1)) (coordinate K 2) (by
      change Polynomial.eval₂ (Polynomial.aeval (-coordinate K 1)).toRingHom (coordinate K 2)
        (Polynomial.X^2+Polynomial.C (Polynomial.C 0*Polynomial.X+Polynomial.C 0)*Polynomial.X-
          Polynomial.C (Polynomial.X^3+Polynomial.C 0*Polynomial.X^2+
            Polynomial.C (-1)*Polynomial.X+Polynomial.C 0))=0
      simp only [Polynomial.eval₂_sub,Polynomial.eval₂_add,Polynomial.eval₂_mul,
        Polynomial.eval₂_pow,Polynomial.eval₂_X,Polynomial.eval₂_C]
      simp [coordinate_cubic,sub_eq_add_neg])

@[simp] theorem toNative_coordinate (j : Fin 3) :
    toNative K (coordinate K j) =
      ![CriticalEllipticField.xRing K ^ 2,-CriticalEllipticField.xRing K,
        CriticalEllipticField.yRing K] j := by
  simp [toNative,coordinate,toNativePre]
@[simp] theorem fromNative_x :
    fromNative K (CriticalEllipticField.xRing K) = -coordinate K 1 :=
  (AdjoinRoot.liftAlgHom_of _ _ _ _ _).trans (Polynomial.aeval_X _)
@[simp] theorem fromNative_y :
    fromNative K (CriticalEllipticField.yRing K) = coordinate K 2 :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem from_to : (fromNative K).comp (toNative K) = AlgHom.id K (ring K) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  change fromNative K (toNative K (coordinate K j)) = coordinate K j
  rw [toNative_coordinate]
  fin_cases j
  · change fromNative K (CriticalEllipticField.xRing K ^ 2) = coordinate K 0
    rw [map_pow,fromNative_x,coordinate_conic]
    ring
  · change fromNative K (-CriticalEllipticField.xRing K) = coordinate K 1
    rw [map_neg,fromNative_x,neg_neg]
  · exact fromNative_y K

theorem to_from : (toNative K).comp (fromNative K) =
    AlgHom.id K (CriticalEllipticField.ring K) := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change toNative K (fromNative K (CriticalEllipticField.xRing K)) =
      CriticalEllipticField.xRing K
    rw [fromNative_x,map_neg,toNative_coordinate]
    exact neg_neg _
  · change toNative K (fromNative K (CriticalEllipticField.yRing K)) =
      CriticalEllipticField.yRing K
    rw [fromNative_y,toNative_coordinate]
    rfl

def affineEquiv : ring K ≃ₐ[K] CriticalEllipticField.ring K :=
  AlgEquiv.ofAlgHom (toNative K) (fromNative K) (to_from K) (from_to K)

end FourCorner.EllipticQuarticModel.Infinity
#print axioms FourCorner.EllipticQuarticModel.Infinity.affineEquiv
