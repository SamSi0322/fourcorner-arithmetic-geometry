import CriticalSchemeBoundary

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicCurve
universe u
namespace FourCorner.ChartSectionGeneric
variable {K R:Type u} [Field K] [CommRing R] [Algebra K R]
 {X:Scheme.{u}} [IsIntegral X] (c:X⟶Spec (.of K))
 [SmoothOfRelativeDimension 1 c] [IsProper c]
 (U:X.Opens) (e:U.toScheme≅Spec (.of R))

def chartSection (r:R):Γ(X,U) :=
 U.topIso.hom ((e.hom.app ⊤) ((Scheme.ΓSpecIso (.of R)).inv r))

def chart:Spec (.of R)⟶X:=e.inv≫U.ι
instance: IsOpenImmersion (chart U e):=by dsimp [chart];infer_instance


lemma germ_topIso {X:Scheme.{u}} (U:X.Opens) (x:U) (s:Γ(U.toScheme,⊤)) :
 X.presheaf.germ U x.val x.property (U.topIso.hom s)=
  (U.stalkIso x).hom (U.toScheme.presheaf.germ ⊤ x trivial s) := by
  have h:=congrArg (fun g:Γ(U.toScheme,⊤)⟶X.presheaf.stalk x.val=>g s)
    (U.germ_stalkIso_hom x (V:=⊤) trivial)
  simpa only [chartSection,Scheme.Opens.topIso,Functor.mapIso_hom,Iso.op_hom,
    eqToIso.inv,←ConcreteCategory.comp_apply,TopCat.Presheaf.germ_res] using h.symm

lemma chartSection_germ (f:R→ₐ[K]K) (r:R) :
 let x:=Spec.map (CommRingCat.ofHom f.toRingHom) (IsLocalRing.closedPoint K)
 let y:=e.inv x
 AffineChartStalkFunctions.chartLocalFunction (chart U e) f r=
   X.presheaf.germ U y.val y.property (chartSection U e r) := by
  dsimp only
  let x:=Spec.map (CommRingCat.ofHom f.toRingHom) (IsLocalRing.closedPoint K)
  let y:=e.inv x
  have h:=germ_topIso U y ((e.hom.app ⊤) ((Scheme.ΓSpecIso (.of R)).inv r))
  rw [chartSection,h]
  apply (ConcreteCategory.bijective_of_isIso ((chart U e).stalkMap x)).1
  have hc:((chart U e).stalkMap x) (AffineChartStalkFunctions.chartLocalFunction (chart U e) f r)=
      StructureSheaf.toStalk R x r := by
    change ((chart U e).stalkMap x) ((inv ((chart U e).stalkMap x)) (StructureSheaf.toStalk R x r))=_
    exact congrArg (fun g:(Spec (.of R)).presheaf.stalk x⟶(Spec (.of R)).presheaf.stalk x=>g.hom (StructureSheaf.toStalk R x r))
      (Iso.inv_hom_id (asIso ((chart U e).stalkMap x)))
  rw [hc]
  simp only [chart,Scheme.Hom.stalkMap_comp,CommRingCat.hom_comp,RingHom.comp_apply]
  change StructureSheaf.toStalk R x r=(e.inv.stalkMap x)
    ((U.ι.stalkMap y) ((U.stalkIso y).hom (U.toScheme.presheaf.germ ⊤ y trivial
      ((e.hom.app ⊤) ((Scheme.ΓSpecIso (.of R)).inv r)))))
  have hu (z:U.toScheme.presheaf.stalk y): (U.ι.stalkMap y) ((U.stalkIso y).hom z)=z := by
    rw [←Scheme.Opens.stalkIso_inv]
    exact congrArg (fun g:U.toScheme.presheaf.stalk y⟶U.toScheme.presheaf.stalk y=>g.hom z) (Iso.hom_inv_id (U.stalkIso y))
  rw [hu,Scheme.Hom.germ_stalkMap_apply]
  have he:(e.inv.app ⊤) ((e.hom.app ⊤) ((Scheme.ΓSpecIso (.of R)).inv r))=
     (Scheme.ΓSpecIso (.of R)).inv r := by
    have hh:=congrArg (fun q:Spec (.of R)⟶Spec (.of R)=>q.appTop) e.inv_hom_id
    simp only [Scheme.Hom.comp_appTop,Scheme.Hom.id_appTop] at hh
    exact congrArg (fun g=>g ((Scheme.ΓSpecIso (.of R)).inv r)) hh
  rw [he]
  rfl

theorem local_evaluate (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (f : R →ₐ[K] K) (r : R) :
    (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ j)).hom
      (AffineChartStalkFunctions.chartLocalFunction j f r)=f r := by
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

variable {S:Type u} [CommRing S]
lemma chartSection_trans (σ:R≃+*S) (r:S) :
 chartSection U (e≪≫Scheme.Spec.mapIso σ.symm.toCommRingCatIso.op) r=
 chartSection U e (σ.symm r) := by
  unfold chartSection
  change U.topIso.hom (((e.hom≫Spec.map (CommRingCat.ofHom σ.symm.toRingHom)).appTop)
    ((Scheme.ΓSpecIso (.of S)).inv r))=_
  rw [Scheme.Hom.comp_appTop]
  have h:=Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ.symm.toRingHom)
  have hh:=congrArg (fun g:CommRingCat.of S⟶Γ(Spec (.of R),⊤)=>g.hom r) h
  change U.topIso.hom (e.hom.appTop
    ((Spec.map (CommRingCat.ofHom σ.symm.toRingHom)).appTop ((Scheme.ΓSpecIso (.of S)).inv r)))=_
  change (Scheme.ΓSpecIso (.of R)).inv (σ.symm r)=
    (Spec.map (CommRingCat.ofHom σ.symm.toRingHom)).appTop ((Scheme.ΓSpecIso (.of S)).inv r) at hh
  rw [←hh]
  rfl

variable [Nonempty U]
def genericMap:R→+*X.functionField:=
 (X.germToFunctionField U).hom.comp
  ((U.topIso.hom.hom.comp (e.hom.app ⊤).hom).comp (Scheme.ΓSpecIso (.of R)).inv.hom)

lemma genericMap_local (f:R→ₐ[K]K) (r:R) :
 genericMap U e r=algebraMap
   (X.presheaf.stalk ((Spec.map (CommRingCat.ofHom f.toRingHom)≫chart U e) (IsLocalRing.closedPoint K)))
   X.functionField (AffineChartStalkFunctions.chartLocalFunction (chart U e) f r) := by
  rw [chartSection_germ U e f r]
  exact (X.algebraMap_germ_eq_germToFunctionField _ _).symm

variable {F:Type u} [Field F] [Algebra K F]
/-- Fixed-field evaluation at the SAME actual point, using a proved equality
with its actual affine chart function in the original generic stalk. -/
theorem fixed_chart_evaluate
 (hj:chart U e≫c=Spec.map (CommRingCat.ofHom (algebraMap K R)))
 (f:R→ₐ[K]K) (x:F) (r:R) :
 letI:=SmoothCurveExtension.fieldAlgebra c
 ∀(φ:F≃ₐ[K]X.functionField), φ x=genericMap U e r →
 let p:=AffineChartPlaceEvaluation.chartPoint c (chart U e) hj f
 let v:=SmoothProperPointPlaceTransport.pointEquivRationalPlace_of_fieldEquiv c φ p
 ∃b:v.val.toValuationSubring,(b:F)=x ∧ResiduePlaceEvaluation.evaluate v.val v.property b=f r := by
  letI:=SmoothCurveExtension.fieldAlgebra c
  intro φ hx
  let p:=AffineChartPlaceEvaluation.chartPoint c (chart U e) hj f
  let q:=SmoothProperRationalPointPlaces.pointEquivRationalPlace c p
  let v:=SmoothProperPointPlaceTransport.pointEquivRationalPlace_of_fieldEquiv c φ p
  let z:=AffineChartStalkFunctions.chartLocalFunction (chart U e) f r
  have hz:φ x=algebraMap (X.presheaf.stalk (p.val (IsLocalRing.closedPoint K))) X.functionField z :=
    hx.trans (genericMap_local U e f r)
  let d:q.val.toValuationSubring:=SmoothProperClosedPointPlaces.stalkValuationEquiv c
    (SchemePointStalkEvaluation.closedPointOfPoint c p.val p.property) z
  have hd:(d:X.functionField)=φ x:=hz.symm
  have hm:x∈v.val.toValuationSubring := by
    change φ x∈q.val.toValuationSubring
    rw [←hd]
    exact d.property
  let b:v.val.toValuationSubring:=⟨x,hm⟩
  have hv:Place.congrEquiv φ.toRingEquiv φ.commutes v.val=q.val := by
    apply Place.ext
    ext y
    change φ (φ.symm y)∈q.val.toValuationSubring ↔y∈q.val.toValuationSubring
    rw [AlgEquiv.apply_symm_apply]
  have hh:=FixedAffinePointEvaluation.evaluate_congr_of_eq φ v.val v.property q.val q.property hv b d hd
  refine ⟨b,rfl,hh.symm.trans ?_⟩
  exact (SmoothProperRationalPointPlaces.pointEquivRationalPlace_evaluate c p z).trans
    (local_evaluate (chart U e) f r)

#print axioms chartSection_germ
#print axioms fixed_chart_evaluate
end FourCorner.ChartSectionGeneric
