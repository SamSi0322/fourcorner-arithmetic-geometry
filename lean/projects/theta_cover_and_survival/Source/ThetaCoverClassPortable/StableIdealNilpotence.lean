import ThetaCoverClassPortable.StableOrbitIdealLayer
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Noetherian.Basic

namespace FourCorner.StableIdealNilpotence
noncomputable section
universe u

 theorem idempotents_eq_of_span_eq {B : Type u} [CommRing B] (e f : B)
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : Ideal.span ({e} : Set B)=Ideal.span ({f} : Set B)) : e=f := by
  obtain ⟨a,ha⟩ := Ideal.mem_span_singleton'.mp (h ▸ Ideal.mem_span_singleton_self e)
  obtain ⟨b,hb⟩ := Ideal.mem_span_singleton'.mp (h.symm ▸ Ideal.mem_span_singleton_self f)
  have hef : e*f=e := by rw [← ha,mul_assoc,hf.eq]
  have hfe : f*e=f := by rw [← hb,mul_assoc,he.eq]
  exact hef.symm.trans ((mul_comm e f).trans hfe)

/-- Genuine scheme-theoretic nilpotence of ANY proper stable ideal over
scalar invariants in a finite-dimensional algebra. Stabilized ideal powers
produce an actual idempotent generator; equal extended ideals force that
idempotent invariant, and scalar invariants force it zero. No orbit support
or reduced-point substitution, and no algebraic closure, is needed. -/
theorem stable_ideal_nilpotent {K A B : Type u} [Field K] [CommRing A] [CommRing B]
    [Nontrivial A] [Algebra K A] [Algebra K B] [Module.Finite K A]
    (s t : A →ₐ[K] B)
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap K A))
    (I : Ideal A) (hproper : I≠⊤) (hstable : Ideal.map s.toRingHom I=Ideal.map t.toRingHom I) :
    IsNilpotent I := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  letI : IsNoetherianRing A := IsNoetherianRing.of_finite K A
  obtain ⟨n,hn⟩ := IsArtinian.monotone_stabilizes
    (⟨fun k : ℕ=>I^k,fun _ _ h=>Ideal.pow_le_pow_right h⟩ : ℕ →o (Ideal A)ᵒᵈ)
  let N := n+1
  let P := I^N
  have hN : n≤N := Nat.le_succ n
  have hNN : n≤N+N := hN.trans (Nat.le_add_right N N)
  have hpow : I^N=I^(N+N) := (hn N hN).symm.trans (hn (N+N) hNN)
  have hpid : IsIdempotentElem P := by
    change (I^N)*(I^N)=I^N
    rw [← pow_add,hpow.symm]
  obtain ⟨e,he,hPe⟩ := (Ideal.isIdempotentElem_iff_of_fg P P.fg_of_isNoetherianRing).mp hpid
  change P=Ideal.span ({e} : Set A) at hPe
  have hmap : Ideal.map s.toRingHom P=Ideal.map t.toRingHom P := by
    dsimp only [P]
    rw [Ideal.map_pow,Ideal.map_pow,hstable]
  rw [hPe,Ideal.map_span,Ideal.map_span,Set.image_singleton,Set.image_singleton] at hmap
  have hemap (f : A →ₐ[K] B) : IsIdempotentElem (f e) := by
    change f e*f e=f e
    rw [← map_mul,he.eq]
  have hse : s e=t e := idempotents_eq_of_span_eq (s e) (t e) (hemap s) (hemap t) hmap
  obtain ⟨c,hc⟩ := (hinv e).mp hse
  have hcId : IsIdempotentElem c := by
    apply (algebraMap K A).injective
    change algebraMap K A (c*c)=algebraMap K A c
    rw [map_mul,hc,he.eq]
  have he0 : e=0 := by
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hcId with h0|h1
    · rw [h0,map_zero] at hc
      exact hc.symm
    · exfalso
      apply hproper
      apply top_unique
      have hPI : P≤I := Ideal.pow_le_self (Nat.succ_ne_zero n)
      have hPtop : P=⊤ := by rw [hPe,← hc,h1,map_one,Ideal.span_singleton_one]
      exact hPtop ▸ hPI
  refine ⟨N,?_⟩
  change P=⊥
  rw [hPe,he0,Ideal.span_singleton_zero]

/-- The SAME original orbit kernel is therefore genuinely nilpotent.
Properness and nontriviality are derived from the actual K-point and
original diagonal, rather than supplied as new orbit hypotheses. -/
theorem orbit_kernel_nilpotent {K A B : Type u} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Module.Finite K A]
    (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (hgen : s.toRingHom.range ⊔ t.toRingHom.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (FourCorner.FiniteRelationQuotient.Related s.toRingHom t.toRingHom (T:=T)))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap K A)) :
    IsNilpotent (RingHom.ker (FourCorner.FiniteRelationOrbit.orbitTargetHom s t x)) := by
  letI : Nontrivial A := ⟨⟨1,0,by
    intro h
    have h' := congrArg x h
    exact one_ne_zero (by simpa only [map_one,map_zero] using h')⟩⟩
  have hproper : RingHom.ker (FourCorner.FiniteRelationOrbit.orbitTargetHom s t x)≠⊤ := by
    intro htop
    have hmem : (1 : A)∈RingHom.ker (FourCorner.FiniteRelationOrbit.orbitTargetHom s t x) :=
      by rw [htop];trivial
    have hzero : FourCorner.FiniteRelationOrbit.orbitTargetHom s t x 1=0 := hmem
    have h' := congrArg (FourCorner.FiniteRelationOrbit.orbitAugmentation s t x heq) hzero
    exact one_ne_zero (by simpa only [map_one,map_zero] using h')
  exact stable_ideal_nilpotent s t hinv _ hproper
    (FourCorner.FiniteRelationOrbit.orbit_kernel_stable s t x hgen heq)

/-- The last actual nonzero ideal power is selected from a genuine
nilpotence bound, with its annihilation equation proved. -/
theorem exists_last_nonzero_power {A : Type u} [CommRing A] [Nontrivial A]
    (I : Ideal A) (hI : I≠⊥) (hnil : IsNilpotent I) :
    ∃k : ℕ,0<k ∧ I^k≠⊥ ∧ I^(k+1)=⊥ := by
  let k := nilpotencyClass I-1
  have hp : 0<nilpotencyClass I := pos_nilpotencyClass_iff.mpr hnil
  have hn1 : nilpotencyClass I≠1 := fun h=>hI (eq_zero_of_nilpotencyClass_eq_one h)
  have hk : 0<k := by dsimp only [k];omega
  refine ⟨k,hk,pow_pred_nilpotencyClass hnil,?_⟩
  have hs : k+1=nilpotencyClass I := by dsimp only [k];omega
  rw [hs]
  exact pow_nilpotencyClass hnil

/-- Any original ring-invariant element in a PROPER actual ideal is
zero, because the exact invariants are the field scalars. This lemma does
not substitute mod-I invariance for original s(j)=t(j). -/
theorem invariant_in_proper_ideal_eq_zero {K A B : Type u} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (s t : A →ₐ[K] B)
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap K A))
    (I : Ideal A) (hproper : I≠⊤) (j : A) (hj : j∈I) (hjt : s j=t j) : j=0 := by
  obtain ⟨c,hc⟩ := (hinv j).mp hjt
  by_cases h0 : c=0
  · simpa only [h0,map_zero] using hc.symm
  · have hu : IsUnit j := hc ▸ (isUnit_iff_ne_zero.mpr h0).map (algebraMap K A)
    exact (hproper (Ideal.eq_top_of_isUnit_mem I hj hu)).elim

#print axioms exists_last_nonzero_power
#print axioms invariant_in_proper_ideal_eq_zero

#print axioms orbit_kernel_nilpotent

#print axioms idempotents_eq_of_span_eq
#print axioms stable_ideal_nilpotent
end
end FourCorner.StableIdealNilpotence
