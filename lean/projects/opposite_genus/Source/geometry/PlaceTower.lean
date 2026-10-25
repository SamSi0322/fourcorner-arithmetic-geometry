import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Mathlib.Tactic

/-!
# Restriction and ramification in finite field towers

Both statements concern the accepted valuation-subring definition of a place.
Restriction transitivity follows from composition of the actual algebra maps.
The ramification formula follows by evaluating the order of a base uniformizer.
-/

noncomputable section

namespace FourCorner.PlaceTower

open AlgebraicCurve

variable {K F E L : Type*} [Field K] [Field F] [Field E] [Field L]
  [Algebra K F] [Algebra K E] [Algebra K L]
  [Algebra F E] [Algebra F L] [Algebra E L]
  [IsScalarTower K F E] [IsScalarTower K F L] [IsScalarTower K E L]
  [IsScalarTower F E L] [FiniteDimensional F E] [FiniteDimensional E L]
  [FiniteDimensional F L]

/-- Restriction of actual places is transitive through a finite field tower. -/
theorem restrict_restrict (w : Place K L) :
    (w.restrict E).restrict F = w.restrict F := by
  apply Place.ext
  ext a
  change algebraMap E L (algebraMap F E a) ∈ w.toValuationSubring ↔
    algebraMap F L a ∈ w.toValuationSubring
  rw [← IsScalarTower.algebraMap_apply F E L]

/-- Actual ramification indices multiply in a finite field tower. -/
theorem ramificationIndex_mul (w : Place K L) :
    w.ramificationIndex F = w.ramificationIndex E * (w.restrict E).ramificationIndex F := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    (w.restrict F).toValuationSubring
  have hπord : (w.restrict F).ord (π : F) = 1 :=
    (w.restrict F).ord_coe_irreducible hπ
  have hdirect := w.ord_restrict (F := F) (π : F)
  have htop := w.ord_restrict (F := E) (algebraMap F E (π : F))
  have hbottom := (w.restrict E).ord_restrict (F := F) (π : F)
  rw [restrict_restrict w, hπord, mul_one] at hbottom
  rw [hbottom, ← IsScalarTower.algebraMap_apply F E L] at htop
  rw [hπord, mul_one] at hdirect
  exact_mod_cast hdirect.symm.trans htop

section ThreeSteps

variable {M : Type*} [Field M]
  [Algebra K M] [Algebra F M] [Algebra E M] [Algebra L M]
  [IsScalarTower K F M] [IsScalarTower K E M] [IsScalarTower K L M]
  [IsScalarTower F L M] [IsScalarTower E L M]
  [FiniteDimensional F M] [FiniteDimensional E M] [FiniteDimensional L M]

/-- The three-step form for successive quadratic adjunctions. -/
theorem ramificationIndex_mul_three (w : Place K M) :
    w.ramificationIndex F =
      w.ramificationIndex L * (w.restrict L).ramificationIndex E *
        (w.restrict E).ramificationIndex F := by
  rw [ramificationIndex_mul (F := F) (E := L) w,
    ramificationIndex_mul (F := F) (E := E) (w.restrict L),
    restrict_restrict (F := E) (E := L) w, mul_assoc]

end ThreeSteps

end FourCorner.PlaceTower

#print axioms FourCorner.PlaceTower.restrict_restrict
#print axioms FourCorner.PlaceTower.ramificationIndex_mul
#print axioms FourCorner.PlaceTower.ramificationIndex_mul_three
