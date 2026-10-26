import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module

noncomputable section
set_option autoImplicit false
namespace FourCorner.ProjectiveThreePoint
variable {K:Type*} [Field K]
abbrev V (K:Type*) [Field K]:=Fin 2→K
abbrev Line (K:Type*) [Field K]:=Projectivization K (V K)
def e0:V K:=![1,0]
def e1:V K:=![0,1]
lemma e0_ne_zero:(e0:V K)≠0:=by intro h;have:=congrFun h 0;simpa [e0] using this
lemma e1_ne_zero:(e1:V K)≠0:=by intro h;have:=congrFun h 1;simpa [e1] using this
lemma sum_ne_zero:(e0+e1:V K)≠0:=by intro h;have:=congrFun h 0;simpa [e0,e1] using this
def infinity:Line K:=Projectivization.mk K e0 e0_ne_zero
def zero:Line K:=Projectivization.mk K e1 e1_ne_zero
def one:Line K:=Projectivization.mk K (e0+e1) sum_ne_zero

def action (g:V K≃ₗ[K]V K):Line K→Line K:=Projectivization.map g.toLinearMap g.injective
lemma action_injective (g:V K≃ₗ[K]V K):Function.Injective (action g):=
 Projectivization.map_injective g.toLinearMap g.injective

lemma decompose (v:V K):v=v 0 •e0+v 1 •e1:=by
 funext j;fin_cases j <;>simp [e0,e1]

/-- Actual linear automorphisms with the same three projective images differ
by a scalar on every vector. No finite-automorphism assertion is assumed. -/
theorem scalar_of_three (g h:V K≃ₗ[K]V K)
 (h0:action g infinity=action h infinity)
 (h1:action g zero=action h zero)
 (hs:action g one=action h one):∃c:K,∀v:V K,g v=c •h v := by
  change Projectivization.mk K (g e0) _=Projectivization.mk K (h e0) _ at h0
  change Projectivization.mk K (g e1) _=Projectivization.mk K (h e1) _ at h1
  change Projectivization.mk K (g (e0+e1)) _=Projectivization.mk K (h (e0+e1)) _ at hs
  obtain ⟨a,ha⟩:=(Projectivization.mk_eq_mk_iff' K _ _ _ _).mp h0
  obtain ⟨b,hb⟩:=(Projectivization.mk_eq_mk_iff' K _ _ _ _).mp h1
  obtain ⟨c,hc⟩:=(Projectivization.mk_eq_mk_iff' K _ _ _ _).mp hs
  have hv:a •h e0+b •h e1=c •h (e0+e1) :=by rw [ha,hb,←map_add,hc]
  have hh:=congrArg h.symm hv
  simp only [map_add,map_smul,h.symm_apply_apply] at hh
  have hac:a=c:=by have hh0:=congrFun hh 0;simpa [e0,e1] using hh0
  have hbc:b=c:=by have hh1:=congrFun hh 1;simpa [e0,e1] using hh1
  refine ⟨c,?_⟩
  intro v
  conv_lhs=>rw [decompose v]
  rw [map_add,map_smul,map_smul,←ha,←hb,hac,hbc]
  conv_rhs=>rw [decompose v]
  rw [map_add,map_smul,map_smul]
  module

/-- The scalar comparing the two invertible linear maps is genuinely a unit. -/
theorem scalar_unit_of_three (g h:V K≃ₗ[K]V K)
 (h0:action g infinity=action h infinity)
 (h1:action g zero=action h zero)
 (hs:action g one=action h one):∃c:Kˣ,∀v:V K,g v=c •h v := by
  obtain ⟨c,hc⟩:=scalar_of_three g h h0 h1 hs
  have hc0:c≠0:=by
    intro he
    have hh:=hc e0
    rw [he,zero_smul] at hh
    exact e0_ne_zero (g.injective (hh.trans g.map_zero.symm))
  exact ⟨Units.mk0 c hc0,hc⟩

/-- The GL2-induced projective action is determined by its images of the
three genuine native projective points infinity, zero and one. -/
theorem action_ext (g h:V K≃ₗ[K]V K)
 (h0:action g infinity=action h infinity)
 (h1:action g zero=action h zero)
 (hs:action g one=action h one):action g=action h := by
  obtain ⟨c,hc⟩:=scalar_of_three g h h0 h1 hs
  funext p
  induction p using Projectivization.ind with
  | h v hv =>
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    exact ⟨c,(hc v).symm⟩

#print axioms scalar_of_three
#print axioms scalar_unit_of_three
#print axioms action_ext
end FourCorner.ProjectiveThreePoint
