import ThetaCoverClassPortable.ThetaPairPresentation
noncomputable section
namespace FourCorner.ThetaPairInvariants
open Algebra AlgebraicGeometry
universe u
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (P : ThetaPairPresentation.Data R S)
lemma adjoin_eq_top : Algebra.adjoin R ({P.u,P.v} : Set S)=⊤ := by
  let A:=Algebra.adjoin R ({P.u,P.v} : Set S)
  let x : A:=⟨P.u,Algebra.subset_adjoin (by simp)⟩
  let y : A:=⟨P.v,Algebra.subset_adjoin (by simp)⟩
  have hx : x^2=algebraMap R A P.a := Subtype.ext P.u_sq
  have hy : y^2=algebraMap R A P.b := Subtype.ext P.v_sq
  have hc : x*y=algebraMap R A P.c := Subtype.ext P.uv
  let f:=P.lift x y hx hy hc
  have he : A.val.comp f=AlgHom.id R S := by
    apply P.hom_ext
    · change (f P.u:S)=P.u
      rw [P.lift_u]
    · change (f P.v:S)=P.v
      rw [P.lift_v]
  apply _root_.eq_top_iff.mpr
  intro s _
  have hs : (f s:S)=s := DFunLike.congr_fun he s
  rw [←hs]
  exact (f s).2

def normalForms : Subalgebra R S where
  carrier:={x | ∃ a b c : R,x=algebraMap R S a+algebraMap R S b*P.u+algebraMap R S c*P.v}
  zero_mem':=⟨0,0,0,by simp⟩
  one_mem':=⟨1,0,0,by simp⟩
  add_mem':=by
    rintro x y ⟨a,b,c,hx⟩ ⟨d,e,f,hy⟩
    refine ⟨a+d,b+e,c+f,?_⟩
    rw [hx,hy]
    simp only [map_add]
    ring
  mul_mem':=by
    rintro x y ⟨a,b,c,hx⟩ ⟨d,e,f,hy⟩
    refine ⟨a*d+b*e*P.a+c*f*P.b+(b*f+c*e)*P.c,a*e+b*d,a*f+c*d,?_⟩
    rw [hx,hy]
    simp only [map_add,map_mul]
    linear_combination (algebraMap R S b*algebraMap R S e)*P.u_sq+
      (algebraMap R S c*algebraMap R S f)*P.v_sq+
      (algebraMap R S b*algebraMap R S f+algebraMap R S c*algebraMap R S e)*P.uv
  algebraMap_mem':=fun a=>⟨a,0,0,by simp⟩
lemma normal_form (x : S) : ∃ a b c : R,
    x=algebraMap R S a+algebraMap R S b*P.u+algebraMap R S c*P.v := by
  have hn : Algebra.adjoin R ({P.u,P.v} : Set S)≤normalForms P := by
    apply Algebra.adjoin_le
    intro s hs
    rcases hs with hs|hs
    · subst s
      exact ⟨0,1,0,by simp⟩
    · have he : s=P.v := Set.mem_singleton_iff.mp hs
      subst s
      exact ⟨0,0,1,by simp⟩
  apply hn
  rw [adjoin_eq_top]
  trivial

def negate : S →ₐ[R] S :=
  P.lift (-P.u) (-P.v) (by simpa only [neg_sq] using P.u_sq)
    (by simpa only [neg_sq] using P.v_sq) (by simpa only [neg_mul_neg] using P.uv)
@[simp] lemma negate_u : negate P P.u= -P.u := P.lift_u _ _ _ _ _
@[simp] lemma negate_v : negate P P.v= -P.v := P.lift_v _ _ _ _ _
lemma negate_sq : (negate P).comp (negate P)=AlgHom.id R S := by
  apply P.hom_ext <;> simp
/-- The full invariant ring is exactly the original base ring's image. -/
theorem fixed_iff (h2 : IsUnit (2:R)) (x : S) :
    negate P x=x ↔ ∃ r : R,algebraMap R S r=x := by
  constructor
  · intro h
    obtain ⟨a,b,c,hx⟩:=normal_form P x
    have hn : negate P x=algebraMap R S a-algebraMap R S b*P.u-algebraMap R S c*P.v := by
      rw [hx,map_add,map_add,map_mul,map_mul,negate_u,negate_v]
      simp only [AlgHom.commutes]
      ring
    rw [h] at hn
    have he : (2:S)*x=(2:S)*algebraMap R S a := by linear_combination hx+hn
    have hu : IsUnit (2:S) := by simpa only [map_ofNat] using h2.map (algebraMap R S)
    exact ⟨a,(hu.mul_left_cancel he).symm⟩
  · rintro ⟨r,rfl⟩
    exact (negate P).commutes r
end FourCorner.ThetaPairInvariants
#print axioms FourCorner.ThetaPairInvariants.normal_form
#print axioms FourCorner.ThetaPairInvariants.fixed_iff
