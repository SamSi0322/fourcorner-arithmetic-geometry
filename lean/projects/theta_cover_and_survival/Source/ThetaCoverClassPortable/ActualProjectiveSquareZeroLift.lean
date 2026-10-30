import ThetaCoverClassPortable.ActualSquareZeroLinearEquiv
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.LinearAlgebra.TensorProduct.Pi
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 8000000
open TensorProduct
universe u
namespace FourCorner.SquareZeroLifts
variable {R:Type u}[CommRing R](I:Ideal R)
variable (W:Type u)[AddCommGroup W][Module R W]
lemma end_baseChange_surjective [Module.Projective R W] :
    Function.Surjective (Module.End.baseChangeHom R (R⧸I) W) := by
  intro e
  obtain ⟨f,hf⟩ := Module.projective_lifting_property (reduction I W)
    ((e.restrictScalars R).comp (reduction I W)) (reduction_surjective I W)
  refine ⟨f,?_⟩
  apply TensorProduct.AlgebraTensorModule.ext
  intro r x
  have hh := congrArg (fun f:W→ₗ[R]_=>f x) hf
  change (1:R⧸I)⊗ₜ[R]f x=e ((1:R⧸I)⊗ₜ[R]x) at hh
  change r⊗ₜ[R]f x=e (r⊗ₜ[R]x)
  calc r⊗ₜ[R]f x = r • e ((1:R⧸I)⊗ₜ[R]x) := by simpa only [smul_tmul',smul_eq_mul,mul_one] using congrArg (fun z=>r•z) hh
    _ = e (r⊗ₜ[R]x) := by rw [←e.map_smul];simp only [smul_tmul',smul_eq_mul,mul_one]
lemma end_baseChange_ker_nilpotent (hI:I^2=⊥)
    (f:Module.End R W)(hf:f∈RingHom.ker (Module.End.baseChangeHom R (R⧸I) W).toRingHom):
    IsNilpotent f := by
  have hh : ∀x,f x∈I • (⊤:Submodule R W) := by
    intro x
    apply (reduction_eq_zero I W _).mp
    have hf0 : f.baseChange (R⧸I)=0 := hf
    have h0 := congrArg (fun h:Module.End (R⧸I) ((R⧸I)⊗[R]W)=>h ((1:R⧸I)⊗ₜ[R]x)) hf0
    change (1:R⧸I)⊗ₜ[R]f x=0
    simpa only [LinearMap.baseChange_tmul,LinearMap.zero_apply] using h0
  refine ⟨2,?_⟩
  ext x
  exact end_square_zero I W hI f hh x
end FourCorner.SquareZeroLifts

namespace Module.Projective
/-- Every finite projective module lifts across an actual square-zero quotient.
The lift is the range of a genuinely lifted idempotent on a finite free module. -/
theorem exists_baseChange_quotient_iso_of_squareZero
    {R:Type u}[CommRing R](I:Ideal R)(hI:I^2=⊥)
    (P:Type u)[AddCommGroup P][Module (R⧸I) P]
    [Module.Projective (R⧸I) P][Module.Finite (R⧸I) P] :
    ∃(P':Type u)(_ : AddCommGroup P')(_ : Module R P'),
      Module.Projective R P' ∧ Module.Finite R P' ∧ Nonempty ((R⧸I)⊗[R]P' ≃ₗ[R⧸I] P) := by
  classical
  obtain ⟨n,q,hq⟩ := Module.Finite.exists_fin' (R⧸I) P
  let W := Fin n → R
  let t := TensorProduct.piScalarRight R (R⧸I) (R⧸I) (Fin n)
  let s : (R⧸I)⊗[R]W →ₗ[R⧸I]P := q.comp t.toLinearMap
  have hs : Function.Surjective s := hq.comp t.surjective
  obtain ⟨i,hi⟩ := Module.projective_lifting_property s (LinearMap.id:P→ₗ[R⧸I]P) hs
  let e : Module.End (R⧸I) ((R⧸I)⊗[R]W) := i.comp s
  have he : IsIdempotentElem e := by
    apply LinearMap.ext
    intro x
    change i (s (i (s x)))=i (s x)
    rw [show s (i (s x))=s x from congrArg (fun h=>h (s x)) hi]
  let f := (Module.End.baseChangeHom R (R⧸I) W).toRingHom
  obtain ⟨p,hp,hpe⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent f
    (FourCorner.SquareZeroLifts.end_baseChange_ker_nilpotent I W hI) e
    (FourCorner.SquareZeroLifts.end_baseChange_surjective I W e) he
  let j : p.range →ₗ[R] W := p.range.subtype
  let r : W→ₗ[R]p.range := p.rangeRestrict
  have hrj : r.comp j=LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    obtain ⟨y,hy⟩ := x.property
    change p x.val=x.val
    rw [←hy]
    exact congrArg (fun p:Module.End R W=>p y) hp
  have hjr : j.comp r=p := by ext x;rfl
  letI : Module.Projective R p.range := Module.Projective.of_split j r hrj
  letI : Module.Finite R p.range := Module.Finite.range p
  let j' := j.baseChange (R⧸I)
  let r' := r.baseChange (R⧸I)
  have hrj' : r'.comp j'=LinearMap.id := by
    rw [←LinearMap.baseChange_comp,hrj,LinearMap.baseChange_id]
  have hjr' : j'.comp r'=e := by
    rw [←LinearMap.baseChange_comp,hjr]
    exact hpe
  let a := s.comp j'
  let b := r'.comp i
  have hab : a.comp b=LinearMap.id := by
    change (s.comp j').comp (r'.comp i)=LinearMap.id
    calc (s.comp j').comp (r'.comp i) = s.comp ((j'.comp r').comp i) := by simp only [LinearMap.comp_assoc]
      _ = s.comp ((i.comp s).comp i) := by rw [hjr']
      _ = LinearMap.id := by simp only [LinearMap.comp_assoc,hi,LinearMap.comp_id]
  have hba : b.comp a=LinearMap.id := by
    have he' : e.comp j'=j' := by rw [←hjr',LinearMap.comp_assoc,hrj',LinearMap.comp_id]
    change (r'.comp i).comp (s.comp j')=LinearMap.id
    calc (r'.comp i).comp (s.comp j') = r'.comp (e.comp j') := by rfl
      _ = LinearMap.id := by rw [he',hrj']
  exact ⟨p.range,inferInstance,inferInstance,inferInstance,inferInstance,⟨LinearEquiv.ofLinear a b hab hba⟩⟩
#print axioms exists_baseChange_quotient_iso_of_squareZero
end Module.Projective
