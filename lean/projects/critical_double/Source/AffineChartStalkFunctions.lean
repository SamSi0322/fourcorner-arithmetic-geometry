import SmoothProperPointPlaceTransport
import AffineGenericStalk

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicCurve
universe u
namespace FourCorner.AffineChartStalkFunctions
open SchemePointStalkEvaluation SmoothProperClosedPointPlaces SmoothProperRationalPointPlaces
variable {K R : Type u} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
  {X : Scheme.{u}} [IsIntegral X]

/-- The native field embedding is the actual generic specialization of any stalk. -/
theorem functionField_stalk_diagram (x : X) :
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
      X.fromSpecStalk x=X.fromSpecStalk (genericPoint X) := by
  change Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫
    X.fromSpecStalk x=X.fromSpecStalk (genericPoint X)
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)

/-- Actual generic/stalk naturality for the given affine open immersion. -/
theorem chart_stalk_field (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (x : Spec (CommRingCat.of R)) (a : X.presheaf.stalk (j x)) :
    AffineGenericStalk.ringEquiv j (algebraMap (X.presheaf.stalk (j x)) X.functionField a)=
      algebraMap ((Spec (CommRingCat.of R)).presheaf.stalk x) (Spec (CommRingCat.of R)).functionField
        ((j.stalkMap x).hom a) := by
  let Y := Spec (CommRingCat.of R)
  have heq : CommRingCat.ofHom ((AffineGenericStalk.ringEquiv j).toRingHom.comp
      (algebraMap (X.presheaf.stalk (j x)) X.functionField))=
      CommRingCat.ofHom ((algebraMap (Y.presheaf.stalk x) Y.functionField).comp (j.stalkMap x).hom) := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk (j x))).mp
    rw [CommRingCat.ofHom_comp,CommRingCat.ofHom_comp,Spec.map_comp,Spec.map_comp]
    simp only [CommRingCat.ofHom_hom,Category.assoc]
    rw [functionField_stalk_diagram (j x),AffineGenericStalk.generic_diagram j,
      Scheme.SpecMap_stalkMap_fromSpecStalk,←Category.assoc,functionField_stalk_diagram x]
  exact congrArg (fun f : X.presheaf.stalk (j x) ⟶ Y.presheaf.stalk (genericPoint Y) => f.hom a) heq

/-- A chart ring element represented in the actual local ring of the
original curve, with no assumed affine/projective point comparison. -/
def chartLocalFunction (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (f : R →ₐ[K] K) (r : R) :
    X.presheaf.stalk ((Spec.map (CommRingCat.ofHom f.toRingHom) ≫ j) (IsLocalRing.closedPoint K)) :=
  (inv (j.stalkMap ((Spec.map (CommRingCat.ofHom f.toRingHom)) (IsLocalRing.closedPoint K)))).hom
    (StructureSheaf.toStalk R _ r)

/-- The accepted canonical affine-chart field map sends each original ring
coordinate to the image of that SAME actual local function. -/
theorem fieldEquiv_chartLocalFunction (c : X ⟶ Spec (CommRingCat.of K))
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ c=Spec.map (CommRingCat.ofHom (algebraMap K R)))
    (f : R →ₐ[K] K) (r : R) :
    letI := fieldAlgebra c
    AffineGenericStalk.fieldEquiv c j hj (algebraMap R (FractionRing R) r)=
      algebraMap (X.presheaf.stalk ((Spec.map (CommRingCat.ofHom f.toRingHom) ≫ j)
        (IsLocalRing.closedPoint K))) X.functionField (chartLocalFunction j f r) := by
  letI := fieldAlgebra c
  letI : Algebra R (Spec (CommRingCat.of R)).functionField :=
    (StructureSheaf.toStalk R (genericPoint (Spec (CommRingCat.of R)))).hom.toAlgebra
  letI : IsFractionRing R (Spec (CommRingCat.of R)).functionField :=
    functionField_isFractionRing_of_affine (CommRingCat.of R)
  let x : Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom f.toRingHom) (IsLocalRing.closedPoint K)
  let a : X.presheaf.stalk (j x) := chartLocalFunction j f r
  have hinv : (j.stalkMap x).hom a=StructureSheaf.toStalk R x r := by
    change (j.stalkMap x).hom ((inv (j.stalkMap x)).hom (StructureSheaf.toStalk R x r))=_
    have hh := congrArg (fun g : (Spec (CommRingCat.of R)).presheaf.stalk x ⟶
        (Spec (CommRingCat.of R)).presheaf.stalk x => g.hom (StructureSheaf.toStalk R x r))
      (Iso.inv_hom_id (asIso (j.stalkMap x)))
    simpa only [asIso_inv,asIso_hom,CommRingCat.hom_comp,CommRingCat.hom_id,
      RingHom.coe_comp,Function.comp_apply,RingHom.id_apply] using hh
  have hmap : AffineGenericStalk.ringEquiv j
      (AffineGenericStalk.fieldEquiv c j hj (algebraMap R (FractionRing R) r))=
        algebraMap R (Spec (CommRingCat.of R)).functionField r := by
    change AffineGenericStalk.ringEquiv j ((AffineGenericStalk.ringEquiv j).symm
      ((IsFractionRing.ringEquivOfRingEquiv (RingEquiv.refl R) :
        FractionRing R ≃+* (Spec (CommRingCat.of R)).functionField) (algebraMap R (FractionRing R) r)))=_
    rw [RingEquiv.apply_symm_apply,IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    rfl
  have hcoef : algebraMap ((Spec (CommRingCat.of R)).presheaf.stalk x)
      (Spec (CommRingCat.of R)).functionField (StructureSheaf.toStalk R x r)=
        algebraMap R (Spec (CommRingCat.of R)).functionField r := by
    exact congrArg (fun g => g.hom r)
      (StructureSheaf.toStalk_stalkSpecializes (genericPoint_specializes x))
  apply (AffineGenericStalk.ringEquiv j).injective
  change AffineGenericStalk.ringEquiv j (AffineGenericStalk.fieldEquiv c j hj (algebraMap R (FractionRing R) r))=
    AffineGenericStalk.ringEquiv j (algebraMap (X.presheaf.stalk (j x)) X.functionField a)
  calc
    _=algebraMap R (Spec (CommRingCat.of R)).functionField r := hmap
    _=algebraMap ((Spec (CommRingCat.of R)).presheaf.stalk x) (Spec (CommRingCat.of R)).functionField
        ((j.stalkMap x).hom a) := by rw [hinv];exact hcoef.symm
    _=_ := (chart_stalk_field j x a).symm

/-- The same local function evaluated at the original Scheme chart point
has exactly its original affine K-algebra value. -/
theorem chartLocalFunction_evaluate (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (f : R →ₐ[K] K) (r : R) :
    (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ j)).hom
      (chartLocalFunction j f r)=f r := by
  let x : Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom f.toRingHom) (IsLocalRing.closedPoint K)
  have hi : (j.stalkMap x).hom ((inv (j.stalkMap x)).hom (StructureSheaf.toStalk R x r))=
      StructureSheaf.toStalk R x r := by
    have hh := congrArg (fun g : (Spec (CommRingCat.of R)).presheaf.stalk x ⟶
        (Spec (CommRingCat.of R)).presheaf.stalk x => g.hom (StructureSheaf.toStalk R x r))
      (Iso.inv_hom_id (asIso (j.stalkMap x)))
    simpa only [asIso_inv,asIso_hom,CommRingCat.hom_comp,CommRingCat.hom_id,
      RingHom.coe_comp,Function.comp_apply,RingHom.id_apply] using hh
  rw [Scheme.stalkClosedPointTo_comp]
  change (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom f.toRingHom))).hom
    ((j.stalkMap x).hom ((inv (j.stalkMap x)).hom (StructureSheaf.toStalk R x r)))=f r
  rw [hi]
  have he : StructureSheaf.toStalk R x ≫ Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom f.toRingHom))=
      CommRingCat.ofHom f.toRingHom := by
    rw [Scheme.stalkClosedPointTo,←Category.assoc]
    change (StructureSheaf.toStalk R (PrimeSpectrum.comap f.toRingHom (IsLocalRing.closedPoint K)) ≫
      (Spec.sheafedSpaceMap (CommRingCat.ofHom f.toRingHom)).hom.stalkMap (IsLocalRing.closedPoint K)) ≫
        (stalkClosedPointIso (CommRingCat.of K)).hom=CommRingCat.ofHom f.toRingHom
    erw [AlgebraicGeometry.stalkMap_toStalk]
    rw [Category.assoc,← stalkClosedPointIso_inv,Iso.inv_hom_id,Category.comp_id]
  exact congrArg (fun g : CommRingCat.of R ⟶ CommRingCat.of K => g.hom r) he

#print axioms chart_stalk_field
#print axioms chartLocalFunction
#print axioms fieldEquiv_chartLocalFunction
#print axioms chartLocalFunction_evaluate
end FourCorner.AffineChartStalkFunctions
