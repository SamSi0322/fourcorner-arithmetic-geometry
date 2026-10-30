import ThetaCoverClassPortable.FiniteRelationTranslation
import Mathlib.RingTheory.RingHom.Flat

namespace FourCorner.FiniteRelationQuotient
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u
variable {A B : Type u} [CommRing A] [CommRing B]

/-- BOTH actual composable-arrow projections are flat, by genuine native
pushout stability. No C→A flatness or quotient effectiveness is used. -/
theorem composable_left_flat (s t : A →+* B) (hs : s.Flat) : (pairLeft s t).hom.Flat :=
  CommRingCat.flat.of_isPushout (IsPushout.of_hasPushout (CommRingCat.ofHom t) (CommRingCat.ofHom s)) hs

theorem composable_right_flat (s t : A →+* B) (ht : t.Flat) : (pairRight s t).hom.Flat :=
  CommRingCat.flat.of_isPushout (IsPushout.of_hasPushout (CommRingCat.ofHom t) (CommRingCat.ofHom s)).flip ht

theorem composable_source_flat (s t : A →+* B) (hs : s.Flat) :
    ((pairLeft s t).hom.comp s).Flat := hs.comp (composable_left_flat s t hs)

theorem composable_middle_flat (s t : A →+* B) (hs : s.Flat) (ht : t.Flat) :
    ((pairLeft s t).hom.comp t).Flat := ht.comp (composable_left_flat s t hs)

theorem composable_target_flat (s t : A →+* B) (ht : t.Flat) :
    ((pairRight s t).hom.comp t).Flat := ht.comp (composable_right_flat s t ht)

#print axioms composable_left_flat
#print axioms composable_right_flat
#print axioms composable_source_flat
#print axioms composable_middle_flat
#print axioms composable_target_flat
end
end FourCorner.FiniteRelationQuotient
