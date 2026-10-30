import ThetaCoverClassPortable.AnyCoverFiniteMapCohomology
import ThetaCoverClassPortable.CanonicalFiniteMapKernelBaseChange
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_flat_sections_of_locallyTrivial
import ThetaCoverClassPortable.Theorems.Thm_TwoChartCech_isLocallyConstant_fibreEulerChar

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open scoped TensorProduct
universe u
namespace FourCorner.ActualFiniteMapEulerLocus

theorem isLocallyConstant
    {R : Type u} [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (.of R)} [IsSeparated c] [Flat c]
    {ε : SchemeHomOver (𝟙 _) c} (F : SmoothProperCurve.FiniteMapData c ε)
    (M : C.Modules) (hM : Scheme.Modules.IsInvertible M) (V : C.TwoAffineOpenCover) :
    IsLocallyConstant (fun p : PrimeSpectrum R =>
      (Module.finrank p.asIdeal.ResidueField
        (LinearMap.ker ((V.sectionsOf c M).cechDiff.baseChange p.asIdeal.ResidueField)) : ℤ) -
      Module.finrank p.asIdeal.ResidueField
        ((p.asIdeal.ResidueField ⊗[R] (V.sectionsOf c M).M01) ⧸
          LinearMap.range ((V.sectionsOf c M).cechDiff.baseChange p.asIdeal.ResidueField))) := by
  have flatOf : ∀ (U : C.Opens) (hU : IsAffineOpen U),
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M U
      Module.Flat R Γ(M,U) := by
    intro U hU
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M U
    letI := Scheme.TwoAffineOpenCover.isScalarTower_sections c M U
    haveI : Module.Flat R Γ(C,U) := ActualCohomologyChartInputs.BCH0.flat_sections c U hU
    haveI : Module.Flat Γ(C,U) Γ(M,U) :=
      Scheme.Modules.flat_sections_of_locallyTrivial M hM.exists_trivialization ⟨U,hU⟩
    exact Module.Flat.trans R Γ(C,U) Γ(M,U)
  haveI : Module.Flat R (V.sectionsOf c M).M0 := flatOf V.U0 V.isAffineOpen_U0
  haveI : Module.Flat R (V.sectionsOf c M).M1 := flatOf V.U1 V.isAffineOpen_U1
  haveI : Module.Flat R (V.sectionsOf c M).M01 := flatOf _ V.isAffineOpen_inf
  haveI : Module.Flat R ((V.sectionsOf c M).M0 × (V.sectionsOf c M).M1) :=
    ActualCohomologyChartInputs.BCH0.flat_prod R _ _
  obtain ⟨hf0,hf1⟩ := ActualCohomologyChartInputs.finiteMap_H0_H1_anyCover F M hM.exists_trivialization V
  haveI : Module.Finite R (V.sectionsOf c M).H0 := hf0
  haveI : Module.Finite R (V.sectionsOf c M).H1 := hf1
  exact TwoChartCech.isLocallyConstant_fibreEulerChar (V.sectionsOf c M).cechDiff

#print axioms isLocallyConstant
end FourCorner.ActualFiniteMapEulerLocus
