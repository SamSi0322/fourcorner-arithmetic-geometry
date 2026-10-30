import ThetaCoverClassPortable.ThetaPairBaseChange
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.RingHom.Finite
noncomputable section
namespace FourCorner.ThetaPairDescent
open Algebra AlgebraicGeometry
open scoped TensorProduct
universe u
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (P : ThetaPairPresentation.Data R S)
def swap : ThetaPairPresentation.Data R S where
  a:=P.b
  b:=P.a
  c:=P.c
  u:=P.v
  v:=P.u
  base_conic:=by simpa only [mul_comm] using P.base_conic
  u_sq:=P.v_sq
  v_sq:=P.u_sq
  uv:=by simpa only [mul_comm] using P.uv
  lift:=fun x y hx hy hc=>P.lift y x hy hx (by simpa only [mul_comm] using hc)
  lift_u:=fun x y hx hy hc=>P.lift_v y x hy hx _
  lift_v:=fun x y hx hy hc=>P.lift_u y x hy hx _
  hom_ext:=fun hu hv=>P.hom_ext hv hu
lemma cover_span (ell : R) (h : P.a+ell*P.b=1) : Ideal.span ({P.a,P.b} : Set R)=⊤ := by
  rw [Ideal.eq_top_iff_one]
  rw [←h]
  exact Ideal.add_mem _ (Ideal.subset_span (by simp)) (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

attribute [local instance] Algebra.TensorProduct.rightAlgebra
lemma local_property (r : R) (h2 : IsUnit (2:R))
    (hb : IsUnit (algebraMap R (Localization.Away r) P.b)) :
    ∃ (Rr Sr : Type u) (_ : CommRing Rr) (_ : CommRing Sr)
      (_ : Algebra R Rr) (_ : Algebra S Sr) (_ : IsLocalization.Away r Rr)
      (_ : IsLocalization.Away (algebraMap R S r) Sr) (f : Rr →+* Sr)
      (_ : f.comp (algebraMap R Rr)=(algebraMap S Sr).comp (algebraMap R S)),
      f.Finite ∧ f.Etale := by
  let W:=Localization.Away r
  let T:=W ⊗[R] S
  let D:=ThetaPairBaseChange.data (W:=W) P
  haveI hfin : Module.Finite W T := ThetaPairPresentation.finite D hb
  haveI het : Algebra.Etale W T := ThetaPairPresentation.algebra_etale D hb (by
    simpa only [map_ofNat] using h2.map (algebraMap R W))
  refine ⟨W,T,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
    algebraMap W T,?_,?_,?_⟩
  · apply RingHom.ext
    intro x
    change algebraMap W T (algebraMap R W x)=algebraMap S T (algebraMap R S x)
    rw [←IsScalarTower.algebraMap_apply R W T,←IsScalarTower.algebraMap_apply R S T]
  · exact RingHom.finite_algebraMap.mpr hfin
  · exact RingHom.etale_algebraMap.mpr het

theorem finite_etale (ell : R) (h : P.a+ell*P.b=1) (h2 : IsUnit (2:R)) :
    (algebraMap R S).Finite ∧ (algebraMap R S).Etale := by
  have hP : RingHom.OfLocalizationSpan (fun f=>f.Finite ∧ f.Etale) :=
    RingHom.finite_ofLocalizationSpan.and RingHom.Etale.ofLocalizationSpan
  have hPi : RingHom.RespectsIso (fun f=>f.Finite ∧ f.Etale) :=
    RingHom.finite_respectsIso.and RingHom.Etale.respectsIso
  apply hP.ofIsLocalization hPi (algebraMap R S) ({P.a,P.b} : Set R) (cover_span P ell h)
  intro r
  rcases r.2 with hr|hr
  · have he : r.val=P.a := hr
    have hu : IsUnit (algebraMap R (Localization.Away r.val) P.a) := by
      have hv : IsUnit (algebraMap R (Localization.Away r.val) r.val) := IsLocalization.Away.algebraMap_isUnit r.val
      exact (congrArg (fun x : R=>IsUnit (algebraMap R (Localization.Away r.val) x)) he).mp hv
    exact local_property (swap P) r.val h2 hu
  · have he : r.val=P.b := Set.mem_singleton_iff.mp hr
    have hu : IsUnit (algebraMap R (Localization.Away r.val) P.b) := by
      have hv : IsUnit (algebraMap R (Localization.Away r.val) r.val) := IsLocalization.Away.algebraMap_isUnit r.val
      exact (congrArg (fun x : R=>IsUnit (algebraMap R (Localization.Away r.val) x)) he).mp hv
    exact local_property P r.val h2 hu
end FourCorner.ThetaPairDescent
#print axioms FourCorner.ThetaPairDescent.finite_etale
