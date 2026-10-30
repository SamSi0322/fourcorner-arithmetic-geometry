import ThetaCoverClassPortable.SmoothProperClosedPointPlaces

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
universe u
namespace FourCorner.SchemePointStalkEvaluation
variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- The original structural base map into the actual stalk. -/
def stalkBaseMap (c : X ⟶ Spec (CommRingCat.of K)) (x : X) : K →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x trivial).hom.comp
    (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

abbrev stalkAlgebra (c : X ⟶ Spec (CommRingCat.of K)) (x : X) :
    Algebra K (X.presheaf.stalk x) := (stalkBaseMap c x).toAlgebra

theorem stalkBaseMap_congr (c : X ⟶ Spec (CommRingCat.of K)) {x y : X} (h : x=y) (a : K) :
    (X.presheaf.stalkCongr (by rw [h];rfl)).hom (stalkBaseMap c y a)=stalkBaseMap c x a := by
  subst y
  simp [TopCat.Presheaf.stalkCongr_hom]

/-- Base compatibility on the actual Spec of each stalk. -/
theorem fromSpecStalk_comp_base (c : X ⟶ Spec (CommRingCat.of K)) (x : X) :
    X.fromSpecStalk x ≫ c=Spec.map (CommRingCat.ofHom (stalkBaseMap c x)) := by
  refine ext_of_isAffine ?_
  have h1 : (Spec.map (CommRingCat.ofHom (stalkBaseMap c x))).appTop=
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ CommRingCat.ofHom (stalkBaseMap c x) ≫
        (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
    rw [← Iso.inv_comp_eq]
    exact (Scheme.ΓSpecIso_inv_naturality _).symm
  have h2 : CommRingCat.ofHom (stalkBaseMap c x)=
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ c.appTop ≫ X.presheaf.germ ⊤ x trivial := by
    ext a
    rfl
  have h3 : (Spec (X.presheaf.stalk x)).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (X.presheaf.stalk x)).Opens)≤⊤)).op=𝟙 _ := by
    rw [show (homOfLE _).op=𝟙 (Opposite.op ⊤) from Subsingleton.elim _ _]
    exact CategoryTheory.Functor.map_id _ _
  rw [Scheme.Hom.comp_appTop,Scheme.fromSpecStalk_appTop,h3,Category.comp_id,h1,h2]
  simp only [Category.assoc,Iso.hom_inv_id_assoc]

section LocalEvaluation
variable {A : Type u} [CommRing A] [IsLocalRing A] [Algebra K A]

theorem localEval_surjective (f : A →ₐ[K] K) : Function.Surjective f := by
  intro a
  exact ⟨algebraMap K A a,f.commutes a⟩

theorem localEval_kernel (f : A →ₐ[K] K) :
    RingHom.ker f.toRingHom=IsLocalRing.maximalIdeal A :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective f.toRingHom (localEval_surjective f))

theorem localEval_unique (f g : A →ₐ[K] K) : f=g := by
  apply AlgHom.ext
  intro x
  have hx : x-algebraMap K A (f x)∈RingHom.ker f.toRingHom := by
    change f (x-algebraMap K A (f x))=0
    simp only [map_sub,AlgHom.commutes,Algebra.algebraMap_self_apply,sub_self]
  rw [localEval_kernel f,←localEval_kernel g] at hx
  change g (x-algebraMap K A (f x))=0 at hx
  simp only [map_sub,AlgHom.commutes,Algebra.algebraMap_self_apply,sub_eq_zero] at hx
  exact hx.symm

theorem localEval_isLocalHom (f : A →ₐ[K] K) : IsLocalHom f.toRingHom := by
  refine ⟨?_⟩
  intro a ha
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hmem
  rw [← localEval_kernel f] at hmem
  exact ha.ne_zero hmem
end LocalEvaluation

/-- Every actual K-section yields a K-algebra evaluation on its actual stalk. -/
def pointEvaluation (c : X ⟶ Spec (CommRingCat.of K))
    (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ c=𝟙 _) :
    letI := stalkAlgebra c (p (IsLocalRing.closedPoint K))
    X.presheaf.stalk (p (IsLocalRing.closedPoint K)) →ₐ[K] K := by
  letI := stalkAlgebra c (p (IsLocalRing.closedPoint K))
  refine {toRingHom := (Scheme.stalkClosedPointTo p).hom,commutes' := ?_}
  have he : CommRingCat.ofHom (stalkBaseMap c (p (IsLocalRing.closedPoint K))) ≫
      Scheme.stalkClosedPointTo p=𝟙 (CommRingCat.of K) := by
    apply Spec.map_injective
    rw [Spec.map_comp,Spec.map_id,← fromSpecStalk_comp_base c,
      ← Category.assoc,Scheme.Spec_stalkClosedPointTo_fromSpecStalk,hp]
  intro a
  exact congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of K => f a) he

/-- A K-algebra evaluation on an actual stalk defines an actual K-point. -/
def pointOfEvaluation (c : X ⟶ Spec (CommRingCat.of K)) (x : X)
    (f : letI := stalkAlgebra c x; X.presheaf.stalk x →ₐ[K] K) :
    Spec (CommRingCat.of K) ⟶ X := by
  letI := stalkAlgebra c x
  exact Spec.map (CommRingCat.ofHom f.toRingHom) ≫ X.fromSpecStalk x

theorem pointOfEvaluation_over (c : X ⟶ Spec (CommRingCat.of K)) (x : X)
    (f : letI := stalkAlgebra c x; X.presheaf.stalk x →ₐ[K] K) :
    pointOfEvaluation c x f ≫ c=𝟙 _ := by
  letI := stalkAlgebra c x
  rw [pointOfEvaluation,Category.assoc,fromSpecStalk_comp_base,←Spec.map_comp,←CommRingCat.ofHom_comp]
  have he : f.toRingHom.comp (stalkBaseMap c x)=RingHom.id K := by
    ext a
    exact f.commutes a
  rw [he,CommRingCat.ofHom_id,Spec.map_id]

theorem pointOfEvaluation_closedPoint (c : X ⟶ Spec (CommRingCat.of K)) (x : X)
    (f : letI := stalkAlgebra c x; X.presheaf.stalk x →ₐ[K] K) :
    pointOfEvaluation c x f (IsLocalRing.closedPoint K)=x := by
  letI := stalkAlgebra c x
  haveI := localEval_isLocalHom f
  change X.fromSpecStalk x ((Spec.map (CommRingCat.ofHom f.toRingHom)) (IsLocalRing.closedPoint K))=x
  rw [Spec_closedPoint]
  exact Scheme.fromSpecStalk_closedPoint

/-- A genuine K-section has closed image over every field. -/
def closedPointOfPoint (c : X ⟶ Spec (CommRingCat.of K))
    (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ c=𝟙 _) : closedPoints X :=
  ⟨p (IsLocalRing.closedPoint K),by
    have := isClosedImmersion_of_comp_eq_id _ _ hp
    have hh := p.isClosedEmbedding.isClosed_range
    rwa [Set.range_eq_singleton] at hh
    exact fun a => congr(p $(Subsingleton.elim _ _))⟩

/-- K-points with the same underlying point are equal over ANY field.
The uniqueness is of actual local K-algebra evaluations, not an application
of the algebraically-closed-only ext_of_apply_closedPoint_eq. -/
theorem point_ext (c : X ⟶ Spec (CommRingCat.of K))
    (p q : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ c=𝟙 _) (hq : q ≫ c=𝟙 _)
    (h : p (IsLocalRing.closedPoint K)=q (IsLocalRing.closedPoint K)) : p=q := by
  apply (SpecToEquivOfLocalRing X (CommRingCat.of K)).injective
  apply SpecToEquivOfLocalRing_eq_iff.mpr
  refine ⟨h,?_⟩
  letI := stalkAlgebra c (p (IsLocalRing.closedPoint K))
  let f := pointEvaluation c p hp
  let g : X.presheaf.stalk (p (IsLocalRing.closedPoint K)) →ₐ[K] K :=
    { toRingHom := (Scheme.stalkClosedPointTo q).hom.comp
        (X.presheaf.stalkCongr (by rw [h];rfl)).hom.hom
      commutes' := by
        intro a
        change (Scheme.stalkClosedPointTo q).hom
          ((X.presheaf.stalkCongr (by rw [h];rfl)).hom.hom
            (stalkBaseMap c (p (IsLocalRing.closedPoint K)) a))=a
        rw [stalkBaseMap_congr c h.symm]
        letI := stalkAlgebra c (q (IsLocalRing.closedPoint K))
        exact (pointEvaluation c q hq).commutes a }
  have he := localEval_unique f g
  ext a
  exact AlgHom.congr_fun he a

#print axioms closedPointOfPoint
#print axioms point_ext

#print axioms fromSpecStalk_comp_base
#print axioms localEval_unique
#print axioms pointEvaluation
#print axioms pointOfEvaluation_over
#print axioms pointOfEvaluation_closedPoint
end FourCorner.SchemePointStalkEvaluation
