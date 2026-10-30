import ThetaCoverClassPortable.ThetaFiniteGenericDegree
import Mathlib.RingTheory.Unramified.LocalRing

namespace FourCorner.ThetaUnramifiedPlaceIndex
open AlgebraicCurve AlgebraicGeometry CategoryTheory
noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

 theorem transport_properties {A B R S : Type*} [CommRing A] [CommRing B] [CommRing R] [CommRing S]
    (f : A →+* B) (g : R →+* S) (eA : A ≃+* R) (eB : B ≃+* S)
    (he : g.comp eA.toRingHom=eB.toRingHom.comp f)
    (hf : f.FormallyUnramified) (hft : f.EssFiniteType) :
    g.FormallyUnramified ∧ g.EssFiniteType := by
  have hg : g=eB.toRingHom.comp (f.comp eA.symm.toRingHom) := by
    ext a
    have hh := RingHom.congr_fun he (eA.symm a)
    change g (eA (eA.symm a))=eB (f (eA.symm a)) at hh
    change g a=eB (f (eA.symm a))
    simpa only [RingEquiv.apply_symm_apply] using hh
  rw [hg]
  constructor
  · exact (RingHom.FormallyUnramified.of_surjective eA.symm.surjective).comp hf |>.comp
      (RingHom.FormallyUnramified.of_surjective eB.surjective)
  · exact ((RingHom.FiniteType.of_surjective _ eA.symm.surjective).essFiniteType.comp hft).comp
      (RingHom.FiniteType.of_surjective _ eB.surjective).essFiniteType

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [FiniteDimensional F E]

/-- Native formal unramifiedness of the actual valuation restriction map
forces ramification index one, by equality of the actual maximal ideals. -/
theorem index_one (w : Place K E)
    (hu : (Place.restrictInclusion F w).FormallyUnramified)
    (ht : (Place.restrictInclusion F w).EssFiniteType) : w.ramificationIndex F=1 := by
  let A := (w.restrict F).toValuationSubring
  let B := w.toValuationSubring
  letI : Algebra A B := (Place.restrictInclusion F w).toAlgebra
  letI : IsLocalHom (algebraMap A B) := Place.instIsLocalHomRestrictInclusion (F:=F) w
  letI : Algebra.FormallyUnramified A B := RingHom.formallyUnramified_algebraMap.mp hu
  letI : Algebra.EssFiniteType A B := RingHom.essFiniteType_algebraMap.mp ht
  have hm := Algebra.FormallyUnramified.map_maximalIdeal (R:=A) (S:=B)
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hma : IsLocalRing.maximalIdeal A=Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  rw [hma,Ideal.map_span,Set.image_singleton] at hm
  have hj : Irreducible (algebraMap A B π) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hm.symm
  have ho := w.ord_coe_irreducible hj
  have hr := w.ord_restrict (F:=F) (π : F)
  rw [(w.restrict F).ord_coe_irreducible hπ,mul_one] at hr
  have hx : w.ord (algebraMap F E (π : F))=1 := ho
  rw [hx] at hr
  exact_mod_cast hr.symm

#print axioms transport_properties
#print axioms index_one
end
end FourCorner.ThetaUnramifiedPlaceIndex
