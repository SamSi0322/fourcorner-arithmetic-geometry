import geometry.AdjacentCoordinateAlgebra
import geometry.SchemeModelGeometricIntegral
import geometry.GeometricFractionField
import geometry.SchemeModelTwoAffineCover
import ModelGenusBridge.KaehlerSheafGenus
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_algEquiv

noncomputable section
namespace FourCorner.Slot03Adjacent
open AlgebraicGeometry AlgebraicCurve
open scoped TensorProduct
universe u
variable {K : Type u} [Field K] [CharZero K]

abbrev adjacentField (c : K) := AdjacentGenus.field c

def model (c : K) : CurveModel K (adjacentField c) :=
  SchemeModelFiniteExtension.model K (adjacentField c)

theorem model_integral (c : K) : IsIntegral (model c).C := inferInstance
theorem model_proper (c : K) : IsProper (model c).toBase := inferInstance
theorem model_smooth (c : K) : SmoothOfRelativeDimension 1 (model c).toBase := inferInstance

def functionFieldEquiv (c : K) :
    letI := (model c).functionFieldAlgebra
    adjacentField c ≃ₐ[K] (model c).C.functionField := (model c).ffAlgEquiv

theorem model_genus [IsAlgClosed K] (c : K) (h : AdjacentPolynomials.Admissible c) :
    letI := (model c).functionFieldAlgebra
    genusFF K (model c).C.functionField = 5 := by
  letI := (model c).functionFieldAlgebra
  exact (genusFF_eq_of_algEquiv (functionFieldEquiv c)).symm.trans
    (AdjacentGenus.genusFF_eq_five h)

theorem globalDifferentials_five [IsAlgClosed K] (c : K)
    (h : AdjacentPolynomials.Admissible c) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
      (model c).toBase (model c).toBase.kaehler ⊤
    Module.Finite K Γ((model c).toBase.kaehler, ⊤) ∧
      Module.finrank K Γ((model c).toBase.kaehler, ⊤) = 5 := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
    (model c).toBase (model c).toBase.kaehler ⊤
  obtain ⟨hfin, hrk⟩ := @KaehlerSheafBridge.finite_and_finrank_globalDifferentials_eq_genusFF K _ _ (model c).C
    (SchemeModelFiniteExtension.twoAffineOpenCover K (adjacentField c))
    (model c).toBase (model_integral c) (model_proper c) (model_smooth c)
  exact ⟨hfin, hrk.trans (model_genus c h)⟩

theorem rational_geometric_globalDifferentials_five (c : ℚ) (hc : 0 < c) (h1 : c ≠ 1) :
    let M := model (algebraMap ℚ (AlgebraicClosure ℚ) c)
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom M.toBase M.toBase.kaehler ⊤
    Module.Finite (AlgebraicClosure ℚ) Γ(M.toBase.kaehler, ⊤) ∧
      Module.finrank (AlgebraicClosure ℚ) Γ(M.toBase.kaehler, ⊤) = 5 :=
  globalDifferentials_five _ (AdjacentPolynomials.rational_admissible c hc h1)

#print axioms rational_geometric_globalDifferentials_five
#print axioms model
#print axioms model_genus
#print axioms globalDifferentials_five
end FourCorner.Slot03Adjacent
