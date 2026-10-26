import ThetaPairInvariants
import ThetaPairRank
noncomputable section
namespace FourCorner.ThetaPairInvariantEquiv
open Algebra AlgebraicGeometry
universe u
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (P : ThetaPairPresentation.Data R S)
lemma base_injective (ell : R) (h : P.a+ell*P.b=1) (h2 : IsUnit (2:R)) :
    Function.Injective (algebraMap R S) := by
  have hf:=ThetaPairDescent.finite_etale P ell h h2
  letI : Module.Finite R S := RingHom.finite_algebraMap.mp hf.1
  letI : Algebra.Etale R S := RingHom.etale_algebraMap.mp hf.2
  apply PrimeSpectrum.comap_surjective_iff_injective_of_finite.mp
  apply PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective.mp
  intro p
  rw [ThetaPairRank.rankAtStalk P ell h p]
  norm_num

def fixed : Subalgebra R S := AlgHom.equalizer (ThetaPairInvariants.negate P) (AlgHom.id R S)
def constants : R →ₐ[R] fixed P where
  toFun r:=⟨algebraMap R S r,(ThetaPairInvariants.negate P).commutes r⟩
  map_one':=Subtype.ext (map_one _)
  map_zero':=Subtype.ext (map_zero _)
  map_mul' r s:=Subtype.ext (map_mul _ r s)
  map_add' r s:=Subtype.ext (map_add _ r s)
  commutes' r:=Subtype.ext rfl
/-- Exact original-base/invariant-algebra comparison, with both injectivity and surjectivity proved. -/
def equiv (ell : R) (h : P.a+ell*P.b=1) (h2 : IsUnit (2:R)) : R ≃ₐ[R] fixed P :=
  AlgEquiv.ofBijective (constants P) ⟨fun r s hrs=>base_injective P ell h h2 (congrArg Subtype.val hrs),by
    intro x
    obtain ⟨r,hr⟩:=(ThetaPairInvariants.fixed_iff P h2 x).mp x.2
    exact ⟨r,Subtype.ext hr⟩⟩

/-- The categorical fixed-ring universal property, for arbitrary ring maps. -/
theorem universal (ell : R) (h : P.a+ell*P.b=1) (h2 : IsUnit (2:R))
    {T : Type u} [CommRing T] (f : T →+* S)
    (hf : (ThetaPairInvariants.negate P).toRingHom.comp f=f) :
    ∃! g : T →+* R,(algebraMap R S).comp g=f := by
  let ff : T →+* fixed P :=
    {toFun:=fun t=>⟨f t,RingHom.congr_fun hf t⟩
     map_one':=Subtype.ext (map_one f)
     map_zero':=Subtype.ext (map_zero f)
     map_add':=fun x y=>Subtype.ext (map_add f x y)
     map_mul':=fun x y=>Subtype.ext (map_mul f x y)}
  let e:=equiv P ell h h2
  let g:=e.symm.toRingHom.comp ff
  have hg : (algebraMap R S).comp g=f := by
    apply RingHom.ext
    intro t
    have he:=congrArg (fun x : fixed P=>(x:S)) (e.apply_symm_apply (ff t))
    change algebraMap R S (e.symm (ff t))=f t at he
    exact he
  refine ⟨g,hg,?_⟩
  intro g' hg'
  apply RingHom.ext
  intro t
  apply base_injective P ell h h2
  exact (RingHom.congr_fun hg' t).trans (RingHom.congr_fun hg t).symm
end FourCorner.ThetaPairInvariantEquiv
#print axioms FourCorner.ThetaPairInvariantEquiv.equiv

#print axioms FourCorner.ThetaPairInvariantEquiv.universal
