import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import ThetaCoverClassPortable.Definitions.Def_JacJ1Iface
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_AffineLimit
import ThetaCoverClassPortable.ActualCutSurjectivity
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_AffineLimit_locallyOfFiniteType_of_forall_exists_fg_factor
import ThetaCoverClassPortable.P2M.Util
namespace FourCorner.ActualPicardLocallyFiniteType

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry FourCorner.ActualPicardLocallyFiniteType.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.AffineLimit FourCorner.ActualPicardLocallyFiniteType.AlgebraicGeometry.AffineLimit Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper GeometricallyIntegral LocallyOfFiniteType Spec Spec.map Scheme geometrically SmoothProperCurve.FiniteMapData"
namespace AffineLimit
p2m_export "AlgebraicGeometry.AffineLimit" "specOver specOverOfSubalgebra IsLFPSurj HomIsLFP locallyOfFiniteType_of_forall_exists_fg_factor"
p2m_open "AlgebraicGeometry.AffineLimit AlgebraicGeometry"

theorem exists_fg_factor_of_representableBy {R : Type u} [CommRing R] {X : Scheme.{u}} (ξ : X ⟶ Spec (CommRingCat.of R))
    (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type (u + 1)) (e : G.RepresentableBy (Over.mk ξ)) (hG : IsLFPSurj G)
    (A : Type u) [CommRing A] [Algebra R A] (φ : Spec (CommRingCat.of A) ⟶ X)
    (hφ : φ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    ∃ (A₀ : Subalgebra R A) (_ : A₀.FG) (φ₀ : Spec (CommRingCat.of ↥A₀) ⟶ X),
      φ₀ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R ↥A₀)) ∧
      Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ≫ φ₀ = φ := by
  let g : specOver R A ⟶ Over.mk ξ := Over.homMk φ hφ
  obtain ⟨A₀, hA₀, x₀, hx₀⟩ := hG A (e.homEquiv g)
  let g₀ : specOver R ↥A₀ ⟶ Over.mk ξ := e.homEquiv.symm x₀
  refine ⟨A₀, hA₀, g₀.left, Over.w g₀, ?_⟩
  have hg : specOverOfSubalgebra R A₀ ≫ g₀ = g :=
    e.homEquiv.injective (by rw [e.homEquiv_comp, Equiv.apply_symm_apply, hx₀])
  exact congrArg (fun k => k.left) hg

end AlgebraicGeometry.AffineLimit

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (F : SmoothProperCurve.FiniteMapData c ε)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) :
    LocallyOfFiniteType D.toBase :=
  locallyOfFiniteType_of_forall_exists_fg_factor D.toBase fun A _ _ φ hφ =>
    exists_fg_factor_of_representableBy D.toBase _ h.representableBy
      (FourCorner.ActualCutSurjectivity.solution R c ε F) A φ hφ
