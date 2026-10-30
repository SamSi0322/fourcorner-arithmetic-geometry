import ThetaCoverClassPortable.FiniteMapCechTransport

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory NeronModelInfra
universe u
namespace FourCorner.FiniteMapCohomology

 theorem cyclesMap_bijective_of_bijective
    {R A B D E : Type u} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup D] [Module R D] [AddCommGroup E] [Module R E]
    (f : A →ₗ[R] B) (g : D →ₗ[R] E) (p : A →ₗ[R] D) (q : B →ₗ[R] E)
    (h : g.comp p=q.comp f) (hp : Function.Bijective p) (hq : Function.Injective q) :
    Function.Bijective (FourCorner.TwoTermFiniteness.cyclesMap f g p q h) := by
  constructor
  · intro x y he
    apply Subtype.ext
    apply hp.1
    exact congrArg Subtype.val he
  · intro y
    obtain ⟨x,hx⟩ := hp.2 y.val
    have hz : f x=0 := by
      apply hq
      rw [map_zero]
      have hh := LinearMap.congr_fun h x
      simp only [LinearMap.comp_apply] at hh
      rw [hx,y.property] at hh
      exact hh.symm
    exact ⟨⟨x,hz⟩,Subtype.ext hx⟩

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}

 theorem nativeCochain0_bijective (F : SmoothProperCurve.FiniteMapData c ε) (M : C.Modules) :
    Function.Bijective (nativeCochain0 F M) := by
  constructor
  · intro x y h
    exact h
  · intro y
    exact ⟨y,rfl⟩

/-- The SAME actual native H0, via its actual cycle map under the overlap
open equality and the identity on the two actual chart-section modules. -/
def nativeH0Equiv (F : SmoothProperCurve.FiniteMapData c ε) (M : C.Modules) :
    (finiteMapLaurentSections F M).H0 ≃ₗ[R] (F.twoAffineOpenCover.sectionsOf c M).H0 :=
  LinearEquiv.ofBijective
    (FourCorner.TwoTermFiniteness.cyclesMap (finiteMapLaurentSections F M).cechDiff
      (F.twoAffineOpenCover.sectionsOf c M).cechDiff (nativeCochain0 F M)
      (nativeOverlapEquiv F M).toLinearMap (nativeCochain_comm F M))
    (cyclesMap_bijective_of_bijective _ _ _ _ _ (nativeCochain0_bijective F M) (nativeOverlapEquiv F M).injective)
end FourCorner.FiniteMapCohomology
