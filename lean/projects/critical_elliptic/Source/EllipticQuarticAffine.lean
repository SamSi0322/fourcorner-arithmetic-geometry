import EllipticQuarticModel
import CriticalEllipticField

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
universe u
namespace FourCorner.EllipticQuarticModel
variable (K : Type u) [Field K]
abbrev affineRing := CriticalQuotientChart.affineRing (equation K) 0
abbrev affineIdeal := CriticalQuotientChart.affineIdeal (equation K) 0
def coordinate (j : Fin 3) : affineRing K := Ideal.Quotient.mk (affineIdeal K) (X j)

theorem dehom_conic : CriticalQuotientChart.affineEquation (equation K) 0 0 =
    (X 1 - X 0 ^ 2 : MvPolynomial (Fin 3) K) := by
  simp [CriticalQuotientChart.affineEquation, equation, conic,
    CriticalAmbientChart.dehom, CriticalAmbientChart.drop]

theorem dehom_cubic : CriticalQuotientChart.affineEquation (equation K) 0 1 =
    (X 2 ^ 2 - X 0 * X 1 + X 0 : MvPolynomial (Fin 3) K) := by
  simp [CriticalQuotientChart.affineEquation, equation, cubicClosure,
    CriticalAmbientChart.dehom, CriticalAmbientChart.drop]

theorem coordinate_conic : coordinate K 1 = coordinate K 0 ^ 2 := by
  have h : Ideal.Quotient.mk (affineIdeal K)
      (CriticalQuotientChart.affineEquation (equation K) 0 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨0,rfl⟩)
  rw [dehom_conic, map_sub, map_pow] at h
  exact sub_eq_zero.mp h

theorem coordinate_cubic : coordinate K 2 ^ 2 = coordinate K 0 ^ 3 - coordinate K 0 := by
  have h : Ideal.Quotient.mk (affineIdeal K)
      (CriticalQuotientChart.affineEquation (equation K) 0 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨1,rfl⟩)
  rw [dehom_cubic, map_add, map_sub, map_mul, map_pow] at h
  change coordinate K 2 ^ 2 - coordinate K 0 * coordinate K 1 + coordinate K 0 = 0 at h
  rw [coordinate_conic] at h
  linear_combination h

def toNativePre : MvPolynomial (Fin 3) K →ₐ[K] CriticalEllipticField.ring K :=
  MvPolynomial.aeval ![CriticalEllipticField.xRing K,
    CriticalEllipticField.xRing K ^ 2, CriticalEllipticField.yRing K]

theorem toNativePre_vanish (j : Fin 2) :
    toNativePre K (CriticalQuotientChart.affineEquation (equation K) 0 j) = 0 := by
  fin_cases j
  · change toNativePre K (CriticalQuotientChart.affineEquation (equation K) 0 0) = 0
    rw [dehom_conic]
    simp [toNativePre]
  · change toNativePre K (CriticalQuotientChart.affineEquation (equation K) 0 1) = 0
    rw [dehom_cubic]
    simp only [toNativePre,map_add,map_sub,map_pow,map_mul,MvPolynomial.aeval_X,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
    change CriticalEllipticField.yRing K ^ 2 - CriticalEllipticField.xRing K *
      CriticalEllipticField.xRing K ^ 2 + CriticalEllipticField.xRing K = 0
    rw [CriticalEllipticField.ring_equation]
    ring

def toNative : affineRing K →ₐ[K] CriticalEllipticField.ring K :=
  Ideal.Quotient.liftₐ (affineIdeal K) (toNativePre K) (by
    change affineIdeal K ≤ RingHom.ker (toNativePre K).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact toNativePre_vanish K j)

def fromNative : CriticalEllipticField.ring K →ₐ[K] affineRing K :=
  AdjoinRoot.liftAlgHom ((CriticalEllipticField.curve K).toAffine.polynomial)
    (Polynomial.aeval (coordinate K 0)) (coordinate K 2) (by
      change Polynomial.eval₂ (Polynomial.aeval (coordinate K 0)).toRingHom (coordinate K 2)
        (Polynomial.X^2+Polynomial.C (Polynomial.C 0*Polynomial.X+Polynomial.C 0)*Polynomial.X-
          Polynomial.C (Polynomial.X^3+Polynomial.C 0*Polynomial.X^2+
            Polynomial.C (-1)*Polynomial.X+Polynomial.C 0))=0
      simp only [Polynomial.eval₂_sub,Polynomial.eval₂_add,Polynomial.eval₂_mul,
        Polynomial.eval₂_pow,Polynomial.eval₂_X,Polynomial.eval₂_C]
      simp [coordinate_cubic,sub_eq_add_neg])

end FourCorner.EllipticQuarticModel
#print axioms FourCorner.EllipticQuarticModel.toNative
#print axioms FourCorner.EllipticQuarticModel.fromNative
