import EllipticQuarticAffine

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
universe u
namespace FourCorner.EllipticQuarticModel
variable (K : Type u) [Field K]

@[simp] theorem toNative_coordinate (j : Fin 3) :
    toNative K (coordinate K j) =
      ![CriticalEllipticField.xRing K, CriticalEllipticField.xRing K ^ 2,
        CriticalEllipticField.yRing K] j := by
  simp [toNative,coordinate,toNativePre]

@[simp] theorem fromNative_x :
    fromNative K (CriticalEllipticField.xRing K) = coordinate K 0 :=
  (AdjoinRoot.liftAlgHom_of _ _ _ _ _).trans (Polynomial.aeval_X _)
@[simp] theorem fromNative_y :
    fromNative K (CriticalEllipticField.yRing K) = coordinate K 2 :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem from_to : (fromNative K).comp (toNative K) = AlgHom.id K (affineRing K) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  change fromNative K (toNative K (coordinate K j)) = coordinate K j
  rw [toNative_coordinate]
  fin_cases j
  · exact fromNative_x K
  · change fromNative K (CriticalEllipticField.xRing K ^ 2) = coordinate K 1
    rw [map_pow,fromNative_x,coordinate_conic]
  · exact fromNative_y K

theorem to_from : (toNative K).comp (fromNative K) =
    AlgHom.id K (CriticalEllipticField.ring K) := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change toNative K (fromNative K (CriticalEllipticField.xRing K)) =
      CriticalEllipticField.xRing K
    rw [fromNative_x,toNative_coordinate]
    rfl
  · change toNative K (fromNative K (CriticalEllipticField.yRing K)) =
      CriticalEllipticField.yRing K
    rw [fromNative_y,toNative_coordinate]
    rfl

/-- The actual V0 chart ring of the independent projective closure is the
native Mathlib affine Weierstrass coordinate ring, over the original field. -/
def affineEquiv : affineRing K ≃ₐ[K] CriticalEllipticField.ring K :=
  AlgEquiv.ofAlgHom (toNative K) (fromNative K) (to_from K) (from_to K)

end FourCorner.EllipticQuarticModel
#print axioms FourCorner.EllipticQuarticModel.affineEquiv
