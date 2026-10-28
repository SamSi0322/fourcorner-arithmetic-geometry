import NativeCurveModelExistence
import Mathlib.AlgebraicGeometry.Morphisms.Flat

namespace FourCorner.ThetaFlatIntegralDescent
open AlgebraicGeometry CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- Reducedness descends through a genuine flat surjective morphism, via
the actual local stalk maps and faithful flatness of local flat maps. -/
theorem reduced {X Y : Scheme} (f : X ⟶ Y) [Flat f] [Surjective f] [IsReduced X] : IsReduced Y := by
  haveI (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
    obtain ⟨x,rfl⟩ := f.surjective y
    algebraize [(f.stalkMap x).hom]
    have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap f x) (f.toLRSHom.prop x)
    exact isReduced_of_injective (f.stalkMap x).hom ‹RingHom.FaithfullyFlat _›.injective
  exact isReduced_of_isReduced_stalk _

/-- Integrality descends through the SAME actual flat surjective map. -/
theorem integral {X Y : Scheme} (f : X ⟶ Y) [Flat f] [Surjective f] [IsIntegral X] : IsIntegral Y := by
  haveI := reduced f
  haveI : IrreducibleSpace Y := Function.Surjective.irreducibleSpace f.continuous f.surjective
  exact isIntegral_of_irreducibleSpace_of_isReduced _

#print axioms reduced
#print axioms integral
end
end FourCorner.ThetaFlatIntegralDescent
