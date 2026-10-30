import ThetaCoverClassPortable.LaurentH0Finite
import ThetaCoverClassPortable.NativeCechKernelTransport

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory NeronModelInfra
universe u
namespace AlgebraicGeometry.SmoothProperCurve.FiniteMapData
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}

/-- Finiteness of both actual native two-chart Cech cohomology modules of
any locally trivial invertible module. The proof derives polynomial chart
finiteness and localization from the actual finite-map datum, constructs
two genuine standard-twist presentations, and uses the actual connecting
map and its proved exactness. No cohomology finiteness is a premise. -/
theorem finite_H0_H1_sectionsOf (F : SmoothProperCurve.FiniteMapData c ε) (M : C.Modules)
    (htriv : ∀ x : C, ∃ (V : C.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    Module.Finite R (F.twoAffineOpenCover.sectionsOf c M).H0 ∧
      Module.Finite R (F.twoAffineOpenCover.sectionsOf c M).H1 := by
  haveI := FourCorner.FiniteMapCohomology.finiteMapLaurentSections_finite_negative F M htriv
  haveI := FourCorner.FiniteMapCohomology.finiteMapLaurentSections_finite_positive F M htriv
  haveI := FourCorner.FiniteMapCohomology.laurent_H0_finite
    (FourCorner.FiniteMapCohomology.finiteMapLaurentSections F M)
    (FourCorner.FiniteMapCohomology.finiteMap_negative_localizes F M htriv)
    (FourCorner.FiniteMapCohomology.finiteMap_positive_localizes F M htriv)
  exact ⟨Module.Finite.equiv (FourCorner.FiniteMapCohomology.nativeH0Equiv F M),
    FourCorner.FiniteMapCohomology.finiteMap_H1_finite F M htriv⟩
end AlgebraicGeometry.SmoothProperCurve.FiniteMapData
