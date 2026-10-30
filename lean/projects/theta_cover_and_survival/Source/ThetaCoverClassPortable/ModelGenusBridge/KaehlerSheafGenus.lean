import ThetaCoverClassPortable.ModelGenusBridge.KaehlerSheafBridge
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_finite_and_finrank_kaehlerSections_H0_eq_genusFF_of_isAlgClosed

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u

namespace FourCorner.KaehlerSheafBridge

theorem finite_and_finrank_globalDifferentials_eq_genusFF
    {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}}
    (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c] :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler ⊤
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    Module.Finite K Γ(c.kaehler, ⊤) ∧
      Module.finrank K Γ(c.kaehler, ⊤) = AlgebraicCurve.genusFF K C.functionField := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler ⊤
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  obtain ⟨e⟩ := exists_globalSectionsEquivChartH0 c 𝒱
  obtain ⟨hfin, hrk⟩ :=
    AlgebraicCurve.finite_and_finrank_kaehlerSections_H0_eq_genusFF_of_isAlgClosed 𝒱 c
  letI := hfin
  exact ⟨Module.Finite.equiv e.symm, e.finrank_eq.trans hrk⟩

end FourCorner.KaehlerSheafBridge

