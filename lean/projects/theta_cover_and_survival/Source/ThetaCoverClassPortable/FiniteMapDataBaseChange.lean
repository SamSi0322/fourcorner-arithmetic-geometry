import ThetaCoverClassPortable.FiniteMapBaseChangeGeometry
import ThetaCoverClassPortable.FiniteMapBaseChangeAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open scoped TensorProduct
namespace FourCorner.FiniteMapBaseChange
open AlgebraicGeometry.SmoothProperCurve
variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  (c : C ⟶ Spec (.of R)) (T : Type u) [CommRing T] [Algebra R T]

/-- Finiteness of the actual pulled-back section, with both structural algebras fixed. -/
theorem finite_pullSection (W : C.Opens) (hW : IsAffineOpen W) (a : Γ(C, W))
    (ha : letI := Scheme.TwoAffineOpenCover.algebraOfHom c W
      (Polynomial.aeval a : Polynomial R →ₐ[R] Γ(C, W)).toRingHom.Finite) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (snd c T) ((fst c T) ⁻¹ᵁ W)
    (Polynomial.aeval (((fst c T).app W).hom a) : Polynomial T →ₐ[T]
      Γ(pullback c (specMap R T), (fst c T) ⁻¹ᵁ W)).toRingHom.Finite := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c W
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (snd c T) ((fst c T) ⁻¹ᵁ W)
  let e := AffineSections.algEquiv c T W hW
  have hfin := (RingHom.Finite.of_surjective e.toRingHom e.surjective).comp
    (Algebra.finite_aeval_baseChange (T := T) a ha)
  have he := congrArg AlgHom.toRingHom
    (Polynomial.aeval_algHom e.toAlgHom ((1 : T) ⊗ₜ[R] a))
  have eone : e ((1 : T) ⊗ₜ[R] a) = ((fst c T).app W).hom a :=
    AffineSections.algEquiv_one_tmul c T W hW a
  have hresult : (Polynomial.aeval (e ((1 : T) ⊗ₜ[R] a)) : Polynomial T →ₐ[T]
      Γ(pullback c (specMap R T), (fst c T) ⁻¹ᵁ W)).toRingHom.Finite := by
    exact (congrArg (fun k : Polynomial T →+*
      Γ(pullback c (specMap R T), (fst c T) ⁻¹ᵁ W) => k.Finite) he).mpr hfin
  rwa [eone] at hresult

end FourCorner.FiniteMapBaseChange

namespace AlgebraicGeometry.SmoothProperCurve.FiniteMapData
open FourCorner.FiniteMapBaseChange
variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (.of R)} {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
  (𝔉 : FiniteMapData c ε) (T : Type u) [CommRing T] [Algebra R T]

/-- Genuine arbitrary commutative base change of the original finite-map data. -/
def baseChange : FiniteMapData (SmoothProperCurve.baseChange R c T) (sectionBaseChange T ε) where
  U := FourCorner.FiniteMapBaseChange.U c T ε 𝔉
  V := FourCorner.FiniteMapBaseChange.V c T ε 𝔉
  f := FourCorner.FiniteMapBaseChange.f c T ε 𝔉
  g := FourCorner.FiniteMapBaseChange.g c T ε 𝔉
  m := 𝔉.m
  isAffineOpen_U := FourCorner.FiniteMapBaseChange.isAffineOpen_U c T ε 𝔉
  isAffineOpen_V := FourCorner.FiniteMapBaseChange.isAffineOpen_V c T ε 𝔉
  sup_eq_top := FourCorner.FiniteMapBaseChange.sup_eq_top c T ε 𝔉
  mem_U_iff := FourCorner.FiniteMapBaseChange.mem_U_iff c T ε 𝔉
  inf_eq_basicOpen := FourCorner.FiniteMapBaseChange.inf_eq_basicOpen c T ε 𝔉
  inf_eq_basicOpen_g := FourCorner.FiniteMapBaseChange.inf_eq_basicOpen_g c T ε 𝔉
  res_f_mul_res_g := FourCorner.FiniteMapBaseChange.res_f_mul_res_g c T ε 𝔉
  finite_f := finite_pullSection c T 𝔉.U 𝔉.isAffineOpen_U 𝔉.f 𝔉.finite_f
  finite_g := finite_pullSection c T 𝔉.V 𝔉.isAffineOpen_V 𝔉.g 𝔉.finite_g
  levelSet_free := by
    intro S _ _ _ s
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (FourCorner.FiniteMapBaseChange.snd c T)
      ((FourCorner.FiniteMapBaseChange.fst c T) ⁻¹ᵁ 𝔉.U)
    letI : Algebra R S := ((algebraMap T S).comp (algebraMap R T)).toAlgebra
    haveI : IsScalarTower R T S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    exact FourCorner.FiniteMapBaseChange.Algebra.levelSet_free
      (FourCorner.FiniteMapBaseChange.AffineSections.algEquiv c T 𝔉.U 𝔉.isAffineOpen_U)
      𝔉.f (FourCorner.FiniteMapBaseChange.f c T ε 𝔉)
      (FourCorner.FiniteMapBaseChange.AffineSections.algEquiv_one_tmul c T 𝔉.U 𝔉.isAffineOpen_U 𝔉.f)
      𝔉.m 𝔉.levelSet_free s

@[simp] theorem baseChange_m : (𝔉.baseChange T).m = 𝔉.m := rfl
@[simp] theorem baseChange_U : (𝔉.baseChange T).U =
    (pullback.fst c (specMap R T)) ⁻¹ᵁ 𝔉.U := rfl
@[simp] theorem baseChange_V : (𝔉.baseChange T).V =
    (pullback.fst c (specMap R T)) ⁻¹ᵁ 𝔉.V := rfl
@[simp] theorem baseChange_f : (𝔉.baseChange T).f =
    ((pullback.fst c (specMap R T)).app 𝔉.U).hom 𝔉.f := rfl
@[simp] theorem baseChange_g : (𝔉.baseChange T).g =
    ((pullback.fst c (specMap R T)).app 𝔉.V).hom 𝔉.g := rfl

theorem exists_baseChange :
    ∃ 𝔊 : FiniteMapData (SmoothProperCurve.baseChange R c T) (sectionBaseChange T ε),
      𝔊.m = 𝔉.m := ⟨𝔉.baseChange T, rfl⟩

end AlgebraicGeometry.SmoothProperCurve.FiniteMapData
