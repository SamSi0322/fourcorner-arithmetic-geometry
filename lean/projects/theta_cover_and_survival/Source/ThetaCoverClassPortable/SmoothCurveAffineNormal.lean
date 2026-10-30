import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.AlgebraicGeometry.FunctionField

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
namespace FourCorner.SmoothCurveAffineNormal

/-- Every nonempty affine open of the actual smooth integral curve is
integrally closed. Closed affine points are genuinely closed on the curve,
by Jacobsonness; their actual stalks are the native DVRs. -/
theorem affine_integrallyClosed {k : Type} [Field k] {X : Scheme}
    (c : X ⟶ Spec (.of k)) [IsIntegral X] [SmoothOfRelativeDimension 1 c]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] : IsIntegrallyClosed Γ(X,U) := by
  letI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  letI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace c
  apply IsIntegrallyClosed.of_localization_maximal
  intro I _ _
  let p : PrimeSpectrum Γ(X,U) := ⟨I,inferInstance⟩
  have hp : IsClosed ({p} : Set (Spec Γ(X,U))) :=
    p.isClosed_singleton_iff_isMaximal.mpr inferInstance
  have hx : IsClosed ({hU.fromSpec p} : Set X) := by
    apply isClosed_singleton_of_isLocallyClosed_singleton
    simpa only [Set.image_singleton] using
      hp.isLocallyClosed.image hU.fromSpec.isOpenEmbedding.isInducing
        hU.fromSpec.isOpenEmbedding.isOpen_range.isLocallyClosed
  letI : IsDiscreteValuationRing (X.presheaf.stalk (hU.fromSpec p)) :=
    SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed c _ hx
  let e : X.presheaf.stalk (hU.fromSpec p) ≃+* Localization.AtPrime I :=
    (asIso (hU.fromSpec.stalkMap p) ≪≫ Spec.stalkIso Γ(X,U) p).commRingCatIsoToRingEquiv
  exact IsIntegrallyClosed.of_equiv e

#print axioms affine_integrallyClosed
end FourCorner.SmoothCurveAffineNormal
