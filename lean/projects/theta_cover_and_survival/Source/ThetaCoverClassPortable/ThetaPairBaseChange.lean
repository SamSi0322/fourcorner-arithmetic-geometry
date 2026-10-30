import ThetaCoverClassPortable.ThetaPairPresentation
import Mathlib.RingTheory.TensorProduct.Basic
noncomputable section
namespace FourCorner.ThetaPairBaseChange
open Algebra AlgebraicGeometry
open scoped TensorProduct
universe u
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S W : Type u} [CommRing R] [CommRing S] [CommRing W]
  [Algebra R S] [Algebra R W]
variable (P : ThetaPairPresentation.Data R S)
abbrev T := W ⊗[R] S

def lift {V : Type u} [CommRing V] [Algebra W V] (x y : V)
    (hx : x^2=algebraMap W V (algebraMap R W P.a))
    (hy : y^2=algebraMap W V (algebraMap R W P.b))
    (hc : x*y=algebraMap W V (algebraMap R W P.c)) : T (R:=R) (S:=S) (W:=W) →ₐ[W] V := by
  letI : Algebra R V := ((algebraMap W V).comp (algebraMap R W)).toAlgebra
  letI : IsScalarTower R W V := IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  let g : S →ₐ[R] V := P.lift x y hx hy hc
  let f : W ⊗[R] S →ₐ[R] V := Algebra.TensorProduct.lift
    ((Algebra.ofId W V).restrictScalars R) g (fun _ _=>Commute.all _ _)
  refine { f.toRingHom with commutes' := ?_ }
  intro w
  change f (w ⊗ₜ[R] (1:S))=algebraMap W V w
  simp [f,Algebra.TensorProduct.lift_tmul]
lemma lift_u {V : Type u} [CommRing V] [Algebra W V] (x y : V) (hx) (hy) (hc) :
    lift (W:=W) P x y hx hy hc ((1:W) ⊗ₜ[R] P.u)=x := by
  simp only [lift]
  simp [Algebra.TensorProduct.lift_tmul,P.lift_u]
lemma lift_v {V : Type u} [CommRing V] [Algebra W V] (x y : V) (hx) (hy) (hc) :
    lift (W:=W) P x y hx hy hc ((1:W) ⊗ₜ[R] P.v)=y := by
  simp only [lift]
  simp [Algebra.TensorProduct.lift_tmul,P.lift_v]
lemma hom_ext {V : Type u} [CommRing V] [Algebra W V]
    {f g : T (R:=R) (S:=S) (W:=W) →ₐ[W] V}
    (hu : f ((1:W) ⊗ₜ[R] P.u)=g ((1:W) ⊗ₜ[R] P.u))
    (hv : f ((1:W) ⊗ₜ[R] P.v)=g ((1:W) ⊗ₜ[R] P.v)) : f=g := by
  letI : Algebra R V := ((algebraMap W V).comp (algebraMap R W)).toAlgebra
  letI : IsScalarTower R W V := IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  let fr : S →ₐ[R] V := (f.restrictScalars R).comp Algebra.TensorProduct.includeRight
  let gr : S →ₐ[R] V := (g.restrictScalars R).comp Algebra.TensorProduct.includeRight
  have he : fr=gr := P.hom_ext hu hv
  have hs (s : S) : f (1 ⊗ₜ[R] s)=g (1 ⊗ₜ[R] s) := DFunLike.congr_fun he s
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add] using congrArg₂ (·+·) hz hw
  | tmul w s =>
    have ht : w ⊗ₜ[R] s=algebraMap W (W ⊗[R] S) w*(1 ⊗ₜ[R] s) := by
      simp [Algebra.TensorProduct.algebraMap_apply,Algebra.TensorProduct.tmul_mul_tmul]
    rw [ht,map_mul,map_mul,f.commutes,g.commutes,hs]

/-- The same presentation after actual tensor-product base change. -/
def data : ThetaPairPresentation.Data W (W ⊗[R] S) where
  a:=algebraMap R W P.a
  b:=algebraMap R W P.b
  c:=algebraMap R W P.c
  u:=1 ⊗ₜ[R] P.u
  v:=1 ⊗ₜ[R] P.v
  base_conic:=by simpa only [map_mul,map_pow] using congrArg (algebraMap R W) P.base_conic
  u_sq:=by
    have h:=congrArg (Algebra.TensorProduct.includeRight : S →ₐ[R] W ⊗[R] S) P.u_sq
    change (Algebra.TensorProduct.includeRight (R:=R) (A:=W) P.u)^2=algebraMap R (W ⊗[R] S) P.a
    simpa only [map_pow,AlgHom.commutes] using h
  v_sq:=by
    have h:=congrArg (Algebra.TensorProduct.includeRight : S →ₐ[R] W ⊗[R] S) P.v_sq
    change (Algebra.TensorProduct.includeRight (R:=R) (A:=W) P.v)^2=algebraMap R (W ⊗[R] S) P.b
    simpa only [map_pow,AlgHom.commutes] using h
  uv:=by
    have h:=congrArg (Algebra.TensorProduct.includeRight : S →ₐ[R] W ⊗[R] S) P.uv
    change Algebra.TensorProduct.includeRight (R:=R) (A:=W) P.u*
      Algebra.TensorProduct.includeRight (R:=R) (A:=W) P.v=algebraMap R (W ⊗[R] S) P.c
    simpa only [map_mul,AlgHom.commutes] using h
  lift:=lift P
  lift_u:=lift_u P
  lift_v:=lift_v P
  hom_ext:=hom_ext P
end FourCorner.ThetaPairBaseChange
#print axioms FourCorner.ThetaPairBaseChange.data
