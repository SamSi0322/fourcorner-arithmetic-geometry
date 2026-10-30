import ThetaCoverClassPortable.ActualCutOpenLocus
import ThetaCoverClassPortable.ActualAlgEquivZeroEulerFibre

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.RelPicard
universe u
namespace FourCorner.ActualCutOpen

theorem isOpen
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 _) c) (F : SmoothProperCurve.FiniteMapData c ε)
    {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) [LocallyOfFiniteType t]
    (L : RigidifiedLineBundle c ε t) :
    IsOpen {x : T | ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ T),
      Set.range ⇑s ⊆ {x} → IsAlgEquivZero (fibreAt c t s) (fibreModule c t s L.L)} :=
  ActualCutOpenLocus.solution R c ε F t L (fun k _ _ s V =>
    ActualAlgEquivZeroEulerIff.fibre c ε F t s V _ (L.isInvertible.pullback _))

#print axioms isOpen
end FourCorner.ActualCutOpen
