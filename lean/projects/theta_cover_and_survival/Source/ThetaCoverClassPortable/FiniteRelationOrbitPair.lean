import ThetaCoverClassPortable.FiniteRelationOrbitFactor

namespace FourCorner.FiniteRelationOrbit
open CategoryTheory CategoryTheory.Limits FourCorner.FiniteRelationQuotient
noncomputable section
universe u
variable {K A B : Type u} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

abbrev orbitRelation (s t : A →ₐ[K] B) (x : A →ₐ[K] K) : CommRingCat.{u} :=
  RingMapTensorPushout.point (orbitTargetHom s t x) s.toRingHom
abbrev orbitRelationLeft (s t : A →ₐ[K] B) (x : A →ₐ[K] K) : orbit s x ⟶ orbitRelation s t x :=
  RingMapTensorPushout.left (orbitTargetHom s t x) s.toRingHom
abbrev orbitRelationArrow (s t : A →ₐ[K] B) (x : A →ₐ[K] K) : CommRingCat.of B ⟶ orbitRelation s t x :=
  RingMapTensorPushout.right (orbitTargetHom s t x) s.toRingHom
abbrev orbitPair (s : A →ₐ[K] B) (x : A →ₐ[K] K) : CommRingCat.{u} :=
  RingMapTensorPushout.point (orbitLeft s x) (orbitLeft s x)
abbrev orbitPairLeft (s : A →ₐ[K] B) (x : A →ₐ[K] K) : orbit s x ⟶ orbitPair s x :=
  RingMapTensorPushout.left (orbitLeft s x) (orbitLeft s x)
abbrev orbitPairRight (s : A →ₐ[K] B) (x : A →ₐ[K] K) : orbit s x ⟶ orbitPair s x :=
  RingMapTensorPushout.right (orbitLeft s x) (orbitLeft s x)

section
variable (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
variable (hgen : s.toRingHom.range ⊔ t.toRingHom.range=⊤)
variable (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s.toRingHom t.toRingHom (T:=T)))

theorem orbitRelation_condition :
    (orbitRelationArrow s t x).hom.comp s.toRingHom=
      (orbitRelationLeft s t x).hom.comp (orbitTargetHom s t x) :=
  (congrArg CommRingCat.Hom.hom (pushout.condition
    (f:=CommRingCat.ofHom (orbitTargetHom s t x)) (g:=CommRingCat.ofHom s.toRingHom))).symm

def orbitRelationSecond : orbit s x →+* orbitRelation s t x :=
  (orbit_target_factor_exists s t x hgen heq (orbitRelationLeft s t x).hom
    (orbitRelationArrow s t x).hom (orbitRelation_condition s t x)).choose

theorem orbitRelationSecond_target :
    (orbitRelationSecond s t x hgen heq).comp (orbitTargetHom s t x)=
      (orbitRelationArrow s t x).hom.comp t.toRingHom :=
  (orbit_target_factor_exists s t x hgen heq (orbitRelationLeft s t x).hom
    (orbitRelationArrow s t x).hom (orbitRelation_condition s t x)).choose_spec.1.1

theorem orbitRelationSecond_base :
    (orbitRelationSecond s t x hgen heq).comp (orbitLeft s x)=
      (orbitRelationLeft s t x).hom.comp (orbitLeft s x) :=
  (orbit_target_factor_exists s t x hgen heq (orbitRelationLeft s t x).hom
    (orbitRelationArrow s t x).hom (orbitRelation_condition s t x)).choose_spec.1.2

def orbitPairArrow : B →+* orbitPair s x :=
  (orbit_pair_related s t x heq (orbitPairLeft s x).hom (orbitPairRight s x).hom
    (congrArg CommRingCat.Hom.hom (pushout.condition
      (f:=CommRingCat.ofHom (orbitLeft s x)) (g:=CommRingCat.ofHom (orbitLeft s x))))).choose

theorem orbitPairArrow_source : (orbitPairArrow s t x heq).comp s.toRingHom=
    (orbitPairLeft s x).hom.comp (orbitTargetHom s t x) :=
  (orbit_pair_related s t x heq (orbitPairLeft s x).hom (orbitPairRight s x).hom
    (congrArg CommRingCat.Hom.hom (pushout.condition
      (f:=CommRingCat.ofHom (orbitLeft s x)) (g:=CommRingCat.ofHom (orbitLeft s x))))).choose_spec.1

theorem orbitPairArrow_target : (orbitPairArrow s t x heq).comp t.toRingHom=
    (orbitPairRight s x).hom.comp (orbitTargetHom s t x) :=
  (orbit_pair_related s t x heq (orbitPairLeft s x).hom (orbitPairRight s x).hom
    (congrArg CommRingCat.Hom.hom (pushout.condition
      (f:=CommRingCat.ofHom (orbitLeft s x)) (g:=CommRingCat.ofHom (orbitLeft s x))))).choose_spec.2

def orbitPairForward : orbitRelation s t x ⟶ orbitPair s x :=
  pushout.desc (orbitPairLeft s x) (CommRingCat.ofHom (orbitPairArrow s t x heq))
    (CommRingCat.hom_ext (orbitPairArrow_source s t x heq).symm)

def orbitPairBackward : orbitPair s x ⟶ orbitRelation s t x :=
  pushout.desc (orbitRelationLeft s t x) (CommRingCat.ofHom (orbitRelationSecond s t x hgen heq))
    (CommRingCat.hom_ext (orbitRelationSecond_base s t x hgen heq).symm)

theorem forward_left : orbitRelationLeft s t x ≫ orbitPairForward s t x heq=orbitPairLeft s x := by
  simp only [orbitPairForward,orbitRelationLeft,RingMapTensorPushout.left,pushout.inl_desc]
theorem forward_arrow : orbitRelationArrow s t x ≫ orbitPairForward s t x heq=
    CommRingCat.ofHom (orbitPairArrow s t x heq) := by
  simp only [orbitPairForward,orbitRelationArrow,RingMapTensorPushout.right,pushout.inr_desc]
theorem backward_left : orbitPairLeft s x ≫ orbitPairBackward s t x hgen heq=orbitRelationLeft s t x := by
  simp only [orbitPairBackward,orbitPairLeft,RingMapTensorPushout.left,pushout.inl_desc]
theorem backward_right : orbitPairRight s x ≫ orbitPairBackward s t x hgen heq=
    CommRingCat.ofHom (orbitRelationSecond s t x hgen heq) := by
  simp only [orbitPairBackward,orbitPairRight,RingMapTensorPushout.right,pushout.inr_desc]

/-- ACTUAL native ring isomorphism: the relation pulled back to the
scheme-theoretic orbit is its full pair groupoid. Both inverse maps are
constructed using the original all-ring composition and joint generation.
This is stronger than a geometric-point equivalence and retains nilpotents. -/
def orbitPairIso : orbitRelation s t x ≅ orbitPair s x where
  hom := orbitPairForward s t x heq
  inv := orbitPairBackward s t x hgen heq
  hom_inv_id := by
    apply pushout.hom_ext
    · rw [← Category.assoc,forward_left,backward_left,Category.comp_id]
    · rw [← Category.assoc,forward_arrow,Category.comp_id]
      apply CommRingCat.hom_ext
      apply joint_ext s.toRingHom t.toRingHom hgen
      · change ((orbitPairBackward s t x hgen heq).hom.comp (orbitPairArrow s t x heq)).comp s.toRingHom=_
        rw [RingHom.comp_assoc,orbitPairArrow_source,← RingHom.comp_assoc]
        rw [← CommRingCat.hom_comp,backward_left,orbitRelation_condition]
      · change ((orbitPairBackward s t x hgen heq).hom.comp (orbitPairArrow s t x heq)).comp t.toRingHom=_
        rw [RingHom.comp_assoc,orbitPairArrow_target,← RingHom.comp_assoc]
        rw [← CommRingCat.hom_comp,backward_right,CommRingCat.hom_ofHom,orbitRelationSecond_target]
  inv_hom_id := by
    apply pushout.hom_ext (f:=CommRingCat.ofHom (orbitLeft s x)) (g:=CommRingCat.ofHom (orbitLeft s x))
    · rw [← Category.assoc,backward_left,forward_left,Category.comp_id]
    · rw [← Category.assoc,backward_right,Category.comp_id]
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro d
      obtain ⟨a,rfl⟩ := orbitTarget_surjective s t x hgen d
      have hs := RingHom.congr_fun (orbitRelationSecond_target s t x hgen heq) a
      change orbitRelationSecond s t x hgen heq ((orbitTargetHom s t x) a)=(orbitRelationArrow s t x).hom (t a) at hs
      change (orbitPairForward s t x heq).hom (orbitRelationSecond s t x hgen heq ((orbitTargetHom s t x) a))=
        (orbitPairRight s x).hom ((orbitTargetHom s t x) a)
      rw [hs]
      have hf := congrArg CommRingCat.Hom.hom (forward_arrow s t x heq)
      have hh := RingHom.congr_fun hf (t a)
      exact hh.trans (RingHom.congr_fun (orbitPairArrow_target s t x heq) a)

#print axioms orbitPairIso
end
end
end FourCorner.FiniteRelationOrbit
