import NativeFunctionFieldFunctor

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
namespace FourCorner.NativeStalkFieldNaturality
open ThetaNativeFunctionFieldMap
variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y]

 theorem stalk_generic_diagram (x : X) :
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
      X.fromSpecStalk x=X.fromSpecStalk (genericPoint X) := by
  change Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫
    X.fromSpecStalk x=X.fromSpecStalk (genericPoint X)
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)

/-- Actual local pullback inside the actual generic-field map. It does NOT
need an over-K morphism, so applies to genuine semilinear base automorphisms. -/
theorem stalk_naturality (f : X ⟶ Y) [Surjective f] (x : X)
    (a : Y.presheaf.stalk (f x)) :
    fieldMap f (algebraMap (Y.presheaf.stalk (f x)) Y.functionField a)=
      algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x).hom a) := by
  have heq : CommRingCat.ofHom ((fieldMap f).comp
      (algebraMap (Y.presheaf.stalk (f x)) Y.functionField))=
      CommRingCat.ofHom ((algebraMap (X.presheaf.stalk x) X.functionField).comp (f.stalkMap x).hom) := by
    apply Spec.map_injective
    apply (cancel_mono (Y.fromSpecStalk (f x))).mp
    rw [CommRingCat.ofHom_comp,CommRingCat.ofHom_comp,Spec.map_comp,Spec.map_comp]
    simp only [CommRingCat.ofHom_hom,Category.assoc]
    rw [stalk_generic_diagram (f x),generic_diagram f,
      Scheme.SpecMap_stalkMap_fromSpecStalk,←Category.assoc,stalk_generic_diagram x]
  exact congrArg (fun h:Y.presheaf.stalk (f x) ⟶ X.presheaf.stalk (genericPoint X)=>h.hom a) heq

/-- For an actual Scheme isomorphism, target stalk range is EXACTLY the
comap of the source stalk range; surjectivity of the actual stalk map proves
the reverse inclusion. No valuation/point compatibility is assumed. -/
theorem stalk_range_comap (f : X ⟶ Y) [IsIso f] (x : X) :
    (algebraMap (Y.presheaf.stalk (f x)) Y.functionField).range=
      ((algebraMap (X.presheaf.stalk x) X.functionField).range).comap (fieldMap f) := by
  ext r
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨(f.stalkMap x).hom a,(stalk_naturality f x a).symm⟩
  · rintro ⟨b,hb⟩
    obtain ⟨a,ha⟩ := (ConcreteCategory.bijective_of_isIso (f.stalkMap x)).2 b
    refine ⟨a,(fieldMap f).injective ?_⟩
    rw [stalk_naturality,ha]
    exact hb

#print axioms stalk_naturality
#print axioms stalk_range_comap
end FourCorner.NativeStalkFieldNaturality
