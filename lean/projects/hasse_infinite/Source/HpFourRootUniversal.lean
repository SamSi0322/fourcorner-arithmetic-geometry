import HpPolynomialRootAlgebra

namespace FourCorner.HpFourRootUniversal
open Polynomial FourRootLift08 Multiquadratic.CoordinateAlgebra
noncomputable section
variable (R : Type*) [CommRing R] (q : Fin 4 → R)

theorem coord_sq (i : Fin 4) : (coord R q i)^2=algebraMap R (A R q) (q i) := by
  fin_cases i
  · change (algebraMap (Stage₃ R (q 0) (q 1) (q 2)) (A R q) (coordinate₁ R (q 0) (q 1) (q 2)))^2=_
    rw [← map_pow,coordinate₁_sq,← IsScalarTower.algebraMap_apply]
    rfl
  · change (algebraMap (Stage₃ R (q 0) (q 1) (q 2)) (A R q) (coordinate₂ R (q 0) (q 1) (q 2)))^2=_
    rw [← map_pow,coordinate₂_sq,← IsScalarTower.algebraMap_apply]
    rfl
  · change (algebraMap (Stage₃ R (q 0) (q 1) (q 2)) (A R q) (coordinate₃ R (q 0) (q 1) (q 2)))^2=_
    rw [← map_pow,coordinate₃_sq,← IsScalarTower.algebraMap_apply]
    rfl
  · have h := AdjoinRoot.eval₂_root (equation R q)
    change (X^2-C (algebraMap R (Stage₃ R (q 0) (q 1) (q 2)) (q 3))).eval₂
      (AdjoinRoot.of (equation R q)) (AdjoinRoot.root (equation R q))=0 at h
    rw [eval₂_sub,eval₂_pow,eval₂_X,eval₂_C,sub_eq_zero] at h
    exact h

theorem ringHom_ext {S : Type*} [CommRing S] (f g : A R q →+* S)
    (hR : ∀x : R,f (algebraMap R (A R q) x)=g (algebraMap R (A R q) x))
    (hroot : ∀i,f (coord R q i)=g (coord R q i)) : f=g := by
  apply AdjoinRoot.ringHom_ext
  · apply Multiquadratic.CoordinateUniversal.ringHom_ext
    · exact hR
    · exact hroot 0
    · exact hroot 1
    · exact hroot 2
  · exact hroot 3

#print axioms coord_sq
#print axioms ringHom_ext
end
end FourCorner.HpFourRootUniversal
