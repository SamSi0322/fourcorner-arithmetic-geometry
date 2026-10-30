import ThetaCoverClassPortable.SmoothCurveAffineNormal
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory Polynomial
namespace FourCorner.KummerRegularUnits

/-- On an actual nonempty affine of the actual smooth integral curve, a
native rational function whose SQUARE is an actual regular unit is itself
an actual regular unit. Normality is proved from the native curve stalks,
not supplied as a Cartier/descent hypothesis. -/
theorem square_unit_regular {k : Type} [Field k] {X : Scheme}
    (c : X ⟶ Spec (.of k)) [IsIntegral X] [SmoothOfRelativeDimension 1 c]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (f : X.functionField) (a : Γ(X,U)ˣ)
    (ha : algebraMap Γ(X,U) X.functionField (a:Γ(X,U))=f^2) :
    ∃u : Γ(X,U)ˣ,algebraMap Γ(X,U) X.functionField (u:Γ(X,U))=f := by
  let R := Γ(X,U)
  let F := X.functionField
  letI : IsIntegrallyClosed R := SmoothCurveAffineNormal.affine_integrallyClosed c U hU
  letI : IsFractionRing R F := functionField_isFractionRing_of_isAffineOpen X U hU
  have hi2 : IsIntegral R (f^2) := by
    rw [←ha]
    exact isIntegral_algebraMap
  have hi : IsIntegral R f := hi2.of_pow (by decide : 0<2)
  obtain ⟨r,hr⟩ := (isIntegrallyClosed_iff F).mp (inferInstance : IsIntegrallyClosed R) hi
  have hr2 : r^2=(a:R) := by
    apply IsFractionRing.injective R F
    rw [map_pow,hr]
    exact ha.symm
  have hu : IsUnit r := by
    apply IsUnit.of_mul_eq_one (r*↑a⁻¹)
    rw [←mul_assoc,←pow_two,hr2]
    exact a.val_inv
  refine ⟨hu.unit,?_⟩
  rw [hu.unit_spec]
  exact hr

#print axioms square_unit_regular
end FourCorner.KummerRegularUnits
