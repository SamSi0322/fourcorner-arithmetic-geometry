import ThetaCoverClassPortable.FiniteRelationOrbit

namespace FourCorner.FiniteRelationOrbit
open CategoryTheory CategoryTheory.Limits FourCorner.FiniteRelationQuotient
noncomputable section
universe u
variable {K A B : Type u} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

/-- The actual SCHEME-THEORETIC orbit kernel is stable as an ideal:
s(I)B=t(I)B, proved by all-ring composition in the genuine quotient
B/s(I)B. This includes every nilpotent thickness and not just supports. -/
theorem orbit_kernel_stable (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (hgen : s.toRingHom.range ⊔ t.toRingHom.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s.toRingHom t.toRingHom (T:=T))) :
    Ideal.map s.toRingHom (RingHom.ker (orbitTargetHom s t x))=
      Ideal.map t.toRingHom (RingHom.ker (orbitTargetHom s t x)) := by
  letI := orbitAlgebra s x
  let o := (orbitTargetHom s t x)
  let I := RingHom.ker o
  let J := Ideal.map s.toRingHom I
  let q : B →+* B ⧸ J := Ideal.Quotient.mk J
  have hk : RingHom.ker o≤RingHom.ker (q.comp s.toRingHom) := by
    intro a ha
    change q (s a)=0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem s.toRingHom ha)
  let f : orbit s x →+* B ⧸ J := o.liftOfSurjective (orbitTarget_surjective s t x hgen) ⟨q.comp s.toRingHom,hk⟩
  have hfo : f.comp o=q.comp s.toRingHom := RingHom.liftOfSurjective_comp _ _ _
  let g := f.comp (orbitArrow s x)
  have hgt : g.comp t.toRingHom=q.comp s.toRingHom := hfo
  let c := compose s.toRingHom t.toRingHom hgen heq g q hgt
  let b := f.comp (orbitLeft s x)
  have hc : CommRingCat.ofHom x.toRingHom ≫ CommRingCat.ofHom b=
      CommRingCat.ofHom s.toRingHom ≫ CommRingCat.ofHom c := by
    apply CommRingCat.hom_ext
    change b.comp x.toRingHom=c.comp s.toRingHom
    rw [compose_source]
    apply RingHom.ext
    intro a
    change f (orbitLeft s x (x a))=f (orbitArrow s x (s a))
    rw [orbit_source]
  let z : orbit s x →+* B ⧸ J := (pushout.desc (CommRingCat.ofHom b) (CommRingCat.ofHom c) hc).hom
  have hzB : z.comp (orbitArrow s x)=c :=
    congrArg CommRingCat.Hom.hom (pushout.inr_desc (CommRingCat.ofHom b) (CommRingCat.ofHom c) hc)
  have hzo : z.comp o=q.comp t.toRingHom := by
    change z.comp ((orbitArrow s x).comp t.toRingHom)=_
    rw [← RingHom.comp_assoc,hzB,compose_target]
  have hts : Ideal.map t.toRingHom I≤Ideal.map s.toRingHom I := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change t a∈J
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := RingHom.congr_fun hzo a
    change z (o a)=q (t a) at h
    rw [ha,map_zero] at h
    exact h.symm
  have hst := Ideal.map_mono (f:=inverseMap s.toRingHom t.toRingHom heq) hts
  rw [Ideal.map_map,Ideal.map_map,inverse_target,inverse_source] at hst
  exact le_antisymm hst hts

#print axioms orbit_kernel_stable
end
end FourCorner.FiniteRelationOrbit
