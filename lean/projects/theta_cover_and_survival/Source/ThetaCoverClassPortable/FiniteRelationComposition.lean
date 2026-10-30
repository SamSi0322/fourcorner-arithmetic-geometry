import ThetaCoverClassPortable.FiniteRelationStructure

namespace FourCorner.FiniteRelationQuotient
noncomputable section
universe u
variable {A B : Type u} [CommRing A] [CommRing B]
variable (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
variable (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
include hgen heq

/-- Every composable pair of ACTUAL ring maps has a unique composite,
for EVERY commutative target ring. Nilpotent test rings are retained. -/
theorem composition_exists_unique {T : Type u} [CommRing T] (f g : B →+* T)
    (hfg : f.comp t=g.comp s) :
    ∃!k : B →+* T,k.comp s=f.comp s ∧ k.comp t=g.comp t := by
  have hf : Related s t (f.comp s) (f.comp t) := ⟨f,rfl,rfl⟩
  have hg : Related s t (f.comp t) (g.comp t) := by rw [hfg];exact ⟨g,rfl,rfl⟩
  obtain ⟨k,hks,hkt⟩ := (heq T).trans hf hg
  refine ⟨k,⟨hks,hkt⟩,?_⟩
  intro l hl
  exact joint_ext s t hgen l k (hl.1.trans hks.symm) (hl.2.trans hkt.symm)

 def compose {T : Type u} [CommRing T] (f g : B →+* T) (hfg : f.comp t=g.comp s) : B →+* T :=
  (composition_exists_unique s t hgen heq f g hfg).choose
 theorem compose_source {T : Type u} [CommRing T] (f g : B →+* T) (hfg : f.comp t=g.comp s) :
    (compose s t hgen heq f g hfg).comp s=f.comp s :=
  (composition_exists_unique s t hgen heq f g hfg).choose_spec.1.1
 theorem compose_target {T : Type u} [CommRing T] (f g : B →+* T) (hfg : f.comp t=g.comp s) :
    (compose s t hgen heq f g hfg).comp t=g.comp t :=
  (composition_exists_unique s t hgen heq f g hfg).choose_spec.1.2

/-- Composition commutes with arbitrary changes of the test ring. -/
theorem compose_natural {T U : Type u} [CommRing T] [CommRing U]
    (f g : B →+* T) (hfg : f.comp t=g.comp s) (a : T →+* U) :
    a.comp (compose s t hgen heq f g hfg)=
      compose s t hgen heq (a.comp f) (a.comp g) (by rw [RingHom.comp_assoc,hfg,← RingHom.comp_assoc]) := by
  apply joint_ext s t hgen
  · rw [RingHom.comp_assoc,compose_source,compose_source,RingHom.comp_assoc]
  · rw [RingHom.comp_assoc,compose_target,compose_target,RingHom.comp_assoc]

/-- Associativity is a proved equality of actual ring maps, obtained from
joint generation and the original all-ring transitivity. -/
theorem compose_associative {T : Type u} [CommRing T] (f g h : B →+* T)
    (hfg : f.comp t=g.comp s) (hgh : g.comp t=h.comp s) :
    compose s t hgen heq (compose s t hgen heq f g hfg) h
      (by rw [compose_target,hgh])=
    compose s t hgen heq f (compose s t hgen heq g h hgh)
      (by rw [compose_source,hfg]) := by
  apply joint_ext s t hgen
  · rw [compose_source,compose_source,compose_source]
  · rw [compose_target,compose_target,compose_target]

#print axioms composition_exists_unique
#print axioms compose_natural
#print axioms compose_associative
end
end FourCorner.FiniteRelationQuotient
