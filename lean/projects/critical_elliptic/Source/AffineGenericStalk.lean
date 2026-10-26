import SmoothCurveFieldIso
import Mathlib.RingTheory.Localization.FractionRing

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
universe u
namespace FourCorner.AffineGenericStalk
variable {R : Type u} [CommRing R] [IsDomain R] {X : Scheme.{u}} [IsIntegral X]

local instance specFieldAlgebra : Algebra R (Spec (.of R)).functionField :=
  (StructureSheaf.toStalk R (genericPoint (Spec (.of R)))).hom.toAlgebra
local instance specFieldFraction : IsFractionRing R (Spec (.of R)).functionField :=
  functionField_isFractionRing_of_affine (CommRingCat.of R)

/-- The actual stalk map of an open affine chart, with the actual generic-point
identification, gives the canonical function-field ring isomorphism. -/
def stalkIso (f : Spec (.of R) ⟶ X) [IsOpenImmersion f] :
    X.functionField ≅ (Spec (.of R)).functionField :=
  X.presheaf.stalkCongr (.of_eq (genericPoint_eq_of_isOpenImmersion f).symm) ≪≫
    asIso (f.stalkMap (genericPoint (Spec (.of R))))

def ringEquiv (f : Spec (.of R) ⟶ X) [IsOpenImmersion f] :
    X.functionField ≃+* (Spec (.of R)).functionField :=
  (stalkIso f).commRingCatIsoToRingEquiv

theorem generic_diagram (f : Spec (.of R) ⟶ X) [IsOpenImmersion f] :
    Spec.map (CommRingCat.ofHom (ringEquiv f).toRingHom) ≫
      X.fromSpecStalk (genericPoint X) =
        (Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R))) ≫ f := by
  change Spec.map ((stalkIso f).hom) ≫ X.fromSpecStalk (genericPoint X) = _
  simp only [stalkIso,Iso.trans_hom,asIso_hom,Spec.map_comp,Category.assoc,
    TopCat.Presheaf.stalkCongr_hom,Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk f

variable {K : Type u} [Field K] [Algebra K R]

theorem base_compatibility (c : X ⟶ Spec (.of K))
    (f : Spec (.of R) ⟶ X) [IsOpenImmersion f]
    (hf : f ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K R))) (a : K) :
    ringEquiv f (SmoothCurveExtension.baseMap c a) =
      algebraMap R (Spec (.of R)).functionField (algebraMap K R a) := by
  have h : CommRingCat.ofHom ((ringEquiv f).toRingHom.comp (SmoothCurveExtension.baseMap c)) =
      CommRingCat.ofHom ((algebraMap R (Spec (.of R)).functionField).comp (algebraMap K R)) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp,CommRingCat.ofHom_comp,Spec.map_comp,Spec.map_comp]
    rw [←SmoothCurveExtension.generic_comp_to_base c,←Category.assoc,generic_diagram,
      Category.assoc,hf,Spec.fromSpecStalk_eq']
    rfl
  exact congrArg (fun g => g.hom a) h

def fractionEquiv (f : Spec (.of R) ⟶ X) [IsOpenImmersion f] :
    FractionRing R ≃+* X.functionField :=
  (IsFractionRing.ringEquivOfRingEquiv (RingEquiv.refl R) :
    FractionRing R ≃+* (Spec (.of R)).functionField).trans (ringEquiv f).symm

/-- A genuine over-K open affine chart supplies the canonical K-algebra
isomorphism from its fraction field to the ORIGINAL scheme's generic stalk. -/
def fieldEquiv (c : X ⟶ Spec (.of K))
    (f : Spec (.of R) ⟶ X) [IsOpenImmersion f]
    (hf : f ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K R))) :
    letI := SmoothCurveExtension.fieldAlgebra c;
    FractionRing R ≃ₐ[K] X.functionField := by
  letI := SmoothCurveExtension.fieldAlgebra c
  refine AlgEquiv.ofRingEquiv (f := fractionEquiv f) ?_
  intro a
  change fractionEquiv f (algebraMap K (FractionRing R) a) = SmoothCurveExtension.baseMap c a
  apply (ringEquiv f).injective
  change ringEquiv f ((ringEquiv f).symm
    ((IsFractionRing.ringEquivOfRingEquiv (RingEquiv.refl R) :
      FractionRing R ≃+* (Spec (.of R)).functionField) (algebraMap K (FractionRing R) a))) = _
  rw [RingEquiv.apply_symm_apply,base_compatibility c f hf]
  rw [IsScalarTower.algebraMap_apply K R (FractionRing R)]
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (RingEquiv.refl R) _

end FourCorner.AffineGenericStalk
#print axioms FourCorner.AffineGenericStalk.generic_diagram
#print axioms FourCorner.AffineGenericStalk.fieldEquiv
