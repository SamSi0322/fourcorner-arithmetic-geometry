import ThetaCoverClassPortable.Theorems.Thm_RingHom_QuasiFinite_codescendsAlong_faithfullyFlat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Descent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.PullbackCarrier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MorphismProperty AlgebraicGeometry
universe u
namespace P2MW.S_AlgebraicGeometry_LocallyQuasiFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact

/-- Exact fpqc scheme descent, obtained through the actual affine ring
property interface. No Noetherian or finite presentation assumption is added. -/
theorem solution :
    DescendsAlong (@LocallyQuasiFinite : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine HasRingHomProperty.descendsAlong @LocallyQuasiFinite (@Surjective ⊓ @Flat)
    (fun {R S} [CommRing R] [CommRing S] => @RingHom.QuasiFinite R S _ _)
    (fun {R S} [CommRing R] [CommRing S] => @RingHom.FaithfullyFlat R S _ _) ?_ ?_
    RingHom.QuasiFinite.codescendsAlong_faithfullyFlat
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  · intro _ _ f hf
    rwa [← flat_and_surjective_SpecMap_iff, and_comm]

#print axioms solution
end P2MW.S_AlgebraicGeometry_LocallyQuasiFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact
