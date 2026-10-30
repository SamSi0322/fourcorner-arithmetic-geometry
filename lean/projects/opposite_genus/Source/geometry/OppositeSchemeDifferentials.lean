import geometry.OppositeSchemeGenus
import geometry.SchemeModelTwoAffineCover
import ModelGenusBridge.KaehlerSheafGenus

noncomputable section
namespace FourCorner.OppositeSchemeModel
open AlgebraicGeometry AlgebraicCurve OppositePolynomials OppositeCoordinateAlgebra
universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Global sections of the actual relative Kähler sheaf on the constructed
smooth proper scheme form a five-dimensional vector space. -/
theorem model_globalDifferentials_finrank_five {mu nu : K}
    (hmu : mu ≠ 0) (hnu : nu ≠ 0) (hA : A mu nu ≠ 0)
    (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
      (model mu nu).toBase (model mu nu).toBase.kaehler ⊤
    Module.Finite K Γ((model mu nu).toBase.kaehler, ⊤) ∧
      Module.finrank K Γ((model mu nu).toBase.kaehler, ⊤) = 5 := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
    (model mu nu).toBase (model mu nu).toBase.kaehler ⊤
  have : IsIntegral (model mu nu).C := model_integral mu nu
  have : IsProper (model mu nu).toBase := model_proper mu nu
  have : SmoothOfRelativeDimension 1 (model mu nu).toBase := model_smooth mu nu
  obtain ⟨hfin, hrk⟩ := @KaehlerSheafBridge.finite_and_finrank_globalDifferentials_eq_genusFF K _ _ (model mu nu).C
    (SchemeModelFiniteExtension.twoAffineOpenCover K (functionField mu nu))
    (model mu nu).toBase (model_integral mu nu) (model_proper mu nu) (model_smooth mu nu)
  exact ⟨hfin, hrk.trans (model_functionField_genus_five hmu hnu hA hB hS)⟩

/-- The paper's rational parameter range gives actual geometric global
differential dimension five, without a supplied model or comparison map. -/
theorem rational_geometric_model_globalDifferentials_five (mu nu : ℚ) (hnu : nu ≠ 0)
    (hpos : 0 < mu / nu) (hlt : mu / nu < 2) :
    let M := model (algebraMap ℚ (AlgebraicClosure ℚ) mu)
      (algebraMap ℚ (AlgebraicClosure ℚ) nu)
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom M.toBase M.toBase.kaehler ⊤
    Module.Finite (AlgebraicClosure ℚ) Γ(M.toBase.kaehler, ⊤) ∧
      Module.finrank (AlgebraicClosure ℚ) Γ(M.toBase.kaehler, ⊤) = 5 := by
  let M := model (algebraMap ℚ (AlgebraicClosure ℚ) mu)
    (algebraMap ℚ (AlgebraicClosure ℚ) nu)
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom M.toBase M.toBase.kaehler ⊤
  have : IsIntegral M.C := model_integral _ _
  have : IsProper M.toBase := model_proper _ _
  have : SmoothOfRelativeDimension 1 M.toBase := model_smooth _ _
  obtain ⟨hfin, hrk⟩ := @KaehlerSheafBridge.finite_and_finrank_globalDifferentials_eq_genusFF (AlgebraicClosure ℚ) _ _ M.C
    (SchemeModelFiniteExtension.twoAffineOpenCover (AlgebraicClosure ℚ)
      (functionField (algebraMap ℚ (AlgebraicClosure ℚ) mu)
        (algebraMap ℚ (AlgebraicClosure ℚ) nu))) M.toBase
      (model_integral _ _) (model_proper _ _) (model_smooth _ _)
  exact ⟨hfin, hrk.trans (rational_geometric_model_genus_five mu nu hnu hpos hlt)⟩

#print axioms model_globalDifferentials_finrank_five
#print axioms rational_geometric_model_globalDifferentials_five
end FourCorner.OppositeSchemeModel
