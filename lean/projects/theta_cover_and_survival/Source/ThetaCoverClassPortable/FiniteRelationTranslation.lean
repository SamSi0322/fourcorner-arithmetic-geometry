import ThetaCoverClassPortable.FiniteRelationComultiplication

/-! Actual groupoid translation between the two native base-change
pushouts. All target rings, including nilpotent collision rings, remain in
scope. No quotient effectiveness, freeness, or invariant-ring flatness is used. -/
namespace FourCorner.FiniteRelationQuotient
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u
variable {A B : Type u} [CommRing A] [CommRing B]

abbrev sourcePair (s : A →+* B) : CommRingCat.{u} := pushout (CommRingCat.ofHom s) (CommRingCat.ofHom s)
abbrev sourceLeft (s : A →+* B) : CommRingCat.of B ⟶ sourcePair s := pushout.inl _ _
abbrev sourceRight (s : A →+* B) : CommRingCat.of B ⟶ sourcePair s := pushout.inr _ _
abbrev pairLeft (s t : A →+* B) : CommRingCat.of B ⟶ composableObject s t := pushout.inl _ _
abbrev pairRight (s t : A →+* B) : CommRingCat.of B ⟶ composableObject s t := pushout.inr _ _

theorem jointCat_ext (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    {T : CommRingCat.{u}} (f g : CommRingCat.of B ⟶ T)
    (hs : CommRingCat.ofHom s ≫ f=CommRingCat.ofHom s ≫ g)
    (ht : CommRingCat.ofHom t ≫ f=CommRingCat.ofHom t ≫ g) : f=g := by
  apply CommRingCat.hom_ext
  exact joint_ext s t hgen f.hom g.hom (congrArg CommRingCat.Hom.hom hs) (congrArg CommRingCat.Hom.hom ht)

 theorem inverse_pair_condition (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    ((sourceLeft s).hom.comp (inverseMap s t heq)).comp t=(sourceRight s).hom.comp s := by
  rw [RingHom.comp_assoc,inverse_target]
  exact congrArg CommRingCat.Hom.hom (pushout.condition (f:=CommRingCat.ofHom s) (g:=CommRingCat.ofHom s))

 def inverseComposite (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) : CommRingCat.of B ⟶ sourcePair s :=
  CommRingCat.ofHom (compose s t hgen heq ((sourceLeft s).hom.comp (inverseMap s t heq))
    (sourceRight s).hom (inverse_pair_condition s t hgen heq))

 theorem inverseComposite_source (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    CommRingCat.ofHom s ≫ inverseComposite s t hgen heq=CommRingCat.ofHom t ≫ sourceLeft s := by
  apply CommRingCat.hom_ext
  exact (compose_source s t hgen heq _ _ (inverse_pair_condition s t hgen heq)).trans
    (by rw [RingHom.comp_assoc,inverse_source];rfl)
 theorem inverseComposite_target (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    CommRingCat.ofHom t ≫ inverseComposite s t hgen heq=CommRingCat.ofHom t ≫ sourceRight s := by
  apply CommRingCat.hom_ext
  exact compose_target s t hgen heq _ _ (inverse_pair_condition s t hgen heq)

 def translationForward (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) : sourcePair s ⟶ composableObject s t :=
  pushout.desc (pairLeft s t) (comultiplication s t hgen heq) (comultiplication_source s t hgen heq).symm
 def translationBackward (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) : composableObject s t ⟶ sourcePair s :=
  pushout.desc (sourceLeft s) (inverseComposite s t hgen heq) (inverseComposite_source s t hgen heq).symm

 theorem composition_backward (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    comultiplication s t hgen heq ≫ translationBackward s t hgen heq=sourceRight s := by
  apply jointCat_ext s t hgen
  · calc
      CommRingCat.ofHom s ≫ (comultiplication s t hgen heq ≫ translationBackward s t hgen heq)=
        (CommRingCat.ofHom s ≫ comultiplication s t hgen heq) ≫ translationBackward s t hgen heq := (Category.assoc _ _ _).symm
      _=(CommRingCat.ofHom s ≫ pairLeft s t) ≫ translationBackward s t hgen heq := by rw [comultiplication_source]
      _=CommRingCat.ofHom s ≫ sourceLeft s := by simp [translationBackward,pairLeft,pairRight,pushout.inl_desc,pushout.inr_desc,Category.assoc]
      _=CommRingCat.ofHom s ≫ sourceRight s := pushout.condition
  · calc
      CommRingCat.ofHom t ≫ (comultiplication s t hgen heq ≫ translationBackward s t hgen heq)=
        (CommRingCat.ofHom t ≫ comultiplication s t hgen heq) ≫ translationBackward s t hgen heq := (Category.assoc _ _ _).symm
      _=(CommRingCat.ofHom t ≫ pairRight s t) ≫ translationBackward s t hgen heq := by rw [comultiplication_target]
      _=CommRingCat.ofHom t ≫ inverseComposite s t hgen heq := by simp [translationBackward,pairLeft,pairRight,pushout.inl_desc,pushout.inr_desc,Category.assoc]
      _=CommRingCat.ofHom t ≫ sourceRight s := inverseComposite_target s t hgen heq

 theorem inverse_forward (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    inverseComposite s t hgen heq ≫ translationForward s t hgen heq=pairRight s t := by
  apply jointCat_ext s t hgen
  · calc
      CommRingCat.ofHom s ≫ (inverseComposite s t hgen heq ≫ translationForward s t hgen heq)=
        (CommRingCat.ofHom s ≫ inverseComposite s t hgen heq) ≫ translationForward s t hgen heq := (Category.assoc _ _ _).symm
      _=(CommRingCat.ofHom t ≫ sourceLeft s) ≫ translationForward s t hgen heq := by rw [inverseComposite_source]
      _=CommRingCat.ofHom t ≫ pairLeft s t := by simp [translationForward,sourceLeft,sourceRight,pushout.inl_desc,pushout.inr_desc,Category.assoc]
      _=CommRingCat.ofHom s ≫ pairRight s t := pushout.condition
  · calc
      CommRingCat.ofHom t ≫ (inverseComposite s t hgen heq ≫ translationForward s t hgen heq)=
        (CommRingCat.ofHom t ≫ inverseComposite s t hgen heq) ≫ translationForward s t hgen heq := (Category.assoc _ _ _).symm
      _=(CommRingCat.ofHom t ≫ sourceRight s) ≫ translationForward s t hgen heq := by rw [inverseComposite_target]
      _=CommRingCat.ofHom t ≫ comultiplication s t hgen heq := by simp [translationForward,sourceLeft,sourceRight,pushout.inl_desc,pushout.inr_desc,Category.assoc]
      _=CommRingCat.ofHom t ≫ pairRight s t := comultiplication_target s t hgen heq

 theorem forward_backward (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    translationForward s t hgen heq ≫ translationBackward s t hgen heq=𝟙 _ := by
  apply pushout.hom_ext
  · simp only [← Category.assoc,translationForward,translationBackward,sourceLeft,pairLeft,pushout.inl_desc,Category.comp_id]
  · simpa only [← Category.assoc,translationForward,pushout.inr_desc,Category.comp_id] using composition_backward s t hgen heq
 theorem backward_forward (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    translationBackward s t hgen heq ≫ translationForward s t hgen heq=𝟙 _ := by
  apply pushout.hom_ext
  · simp only [← Category.assoc,translationForward,translationBackward,sourceLeft,pairLeft,pushout.inl_desc,Category.comp_id]
  · simpa only [← Category.assoc,translationBackward,pushout.inr_desc,Category.comp_id] using inverse_forward s t hgen heq

/-- Actual over-B translation of the two source base changes, with no
field/reducedness/constant-rank/freeness hypotheses. -/
def translationIso (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) : sourcePair s ≅ composableObject s t where
  hom := translationForward s t hgen heq
  inv := translationBackward s t hgen heq
  hom_inv_id := forward_backward s t hgen heq
  inv_hom_id := backward_forward s t hgen heq

 theorem translation_over_base (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    sourceLeft s ≫ (translationIso s t hgen heq).hom=pairLeft s t := by
  simp [translationIso,translationForward,sourceLeft,pushout.inl_desc]
 theorem translation_target_coordinate (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    CommRingCat.ofHom t ≫ sourceRight s ≫ (translationIso s t hgen heq).hom=
      CommRingCat.ofHom t ≫ pairRight s t := by
  simpa only [translationIso,translationForward,← Category.assoc,pushout.inr_desc] using
    comultiplication_target s t hgen heq

#print axioms translationIso
#print axioms translation_over_base
#print axioms translation_target_coordinate
end
end FourCorner.FiniteRelationQuotient
