import ThetaCoverClassPortable.FiniteRelationOrbit

namespace FourCorner.FiniteRelationOrbit
open CategoryTheory CategoryTheory.Limits FourCorner.FiniteRelationQuotient
noncomputable section
universe u
variable {K A B : Type u} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

/-- Every actual arrow whose source lies in the SCHEME-THEORETIC orbit
has a unique target factor through the same orbit, over the same base.
The proof uses all-ring composition, not geometric point membership. -/
theorem orbit_target_factor_exists (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (hgen : s.toRingHom.range ⊔ t.toRingHom.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s.toRingHom t.toRingHom (T:=T)))
    {T : Type u} [CommRing T] (f : orbit s x →+* T) (c : B →+* T)
    (hc : c.comp s.toRingHom=f.comp (orbitTargetHom s t x)) :
    ∃!g : orbit s x →+* T,g.comp (orbitTargetHom s t x)=c.comp t.toRingHom ∧
      g.comp (orbitLeft s x)=f.comp (orbitLeft s x) := by
  let a := f.comp (orbitArrow s x)
  have hat : a.comp t.toRingHom=c.comp s.toRingHom := hc.symm
  let k := compose s.toRingHom t.toRingHom hgen heq a c hat
  let b := f.comp (orbitLeft s x)
  have hw : CommRingCat.ofHom x.toRingHom ≫ CommRingCat.ofHom b=
      CommRingCat.ofHom s.toRingHom ≫ CommRingCat.ofHom k := by
    apply CommRingCat.hom_ext
    change b.comp x.toRingHom=k.comp s.toRingHom
    rw [compose_source]
    apply RingHom.ext
    intro v
    change f (orbitLeft s x (x v))=f (orbitArrow s x (s v))
    rw [orbit_source]
  let g : orbit s x →+* T := (pushout.desc (CommRingCat.ofHom b) (CommRingCat.ofHom k) hw).hom
  have hgB : g.comp (orbitArrow s x)=k :=
    congrArg CommRingCat.Hom.hom (pushout.inr_desc (CommRingCat.ofHom b) (CommRingCat.ofHom k) hw)
  have hgo : g.comp (orbitTargetHom s t x)=c.comp t.toRingHom := by
    change g.comp ((orbitArrow s x).comp t.toRingHom)=_
    rw [← RingHom.comp_assoc,hgB,compose_target]
  have hgK : g.comp (orbitLeft s x)=f.comp (orbitLeft s x) :=
    congrArg CommRingCat.Hom.hom (pushout.inl_desc (CommRingCat.ofHom b) (CommRingCat.ofHom k) hw)
  refine ⟨g,⟨hgo,hgK⟩,?_⟩
  intro g' hg'
  apply RingHom.ext
  intro d
  obtain ⟨v,rfl⟩ := orbitTarget_surjective s t x hgen d
  exact (RingHom.congr_fun hg'.1 v).trans (RingHom.congr_fun hgo v).symm

/-- ANY two orbit-valued points over the same base are joined by an
actual original arrow, on EVERY commutative test ring. -/
theorem orbit_pair_related (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s.toRingHom t.toRingHom (T:=T)))
    {T : Type u} [CommRing T] (f g : orbit s x →+* T)
    (hbase : f.comp (orbitLeft s x)=g.comp (orbitLeft s x)) :
    Related s.toRingHom t.toRingHom (f.comp (orbitTargetHom s t x))
      (g.comp (orbitTargetHom s t x)) := by
  have ha (f : orbit s x →+* T) : Related s.toRingHom t.toRingHom
      ((f.comp (orbitLeft s x)).comp x.toRingHom) (f.comp (orbitTargetHom s t x)) := by
    refine ⟨f.comp (orbitArrow s x),?_,rfl⟩
    apply RingHom.ext
    intro v
    change f (orbitArrow s x (s v))=f (orbitLeft s x (x v))
    rw [orbit_source]
  have hg := ha g
  rw [← hbase] at hg
  exact (heq T).trans ((heq T).symm (ha f)) hg

#print axioms orbit_target_factor_exists
#print axioms orbit_pair_related
end
end FourCorner.FiniteRelationOrbit
