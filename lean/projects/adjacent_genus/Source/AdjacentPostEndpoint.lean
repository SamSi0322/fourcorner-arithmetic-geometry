import AdjacentPostSourceMap
import MonicBoundaryRegular

noncomputable section
namespace FourCorner.AdjacentPostEndpoint
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open Slot03Adjacent Slot03HighAdjacent AdjacentPostModelSource AdjacentPostSourceMap
open Slot03HighAdjacentProjective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- One endpoint on the actual normalized-chart Scheme, the original literal source,
and the genuine geometric base change. It contains no assumed model comparison. -/
theorem rational_model_source_and_geometric_genus (c : ℚ) (hc : 0 < c) (h1 : c ≠ 1) :
    IsIntegral (canonicalScheme c) ∧ IsProper (modelToBase c) ∧
    SmoothOfRelativeDimension 1 (modelToBase c) ∧
    GeometricallyIntegral (modelToBase c) ∧ GeometricallyConnected (modelToBase c) ∧
    (∃ m : Spec (.of (literalR c)) ⟶ canonicalScheme c,
      m ≫ modelToBase c = Spec.map (CommRingCat.ofHom (algebraMap ℚ (literalR c))) ∧
      (let h := AdjacentPolynomials.rational_admissible_self c hc h1
       letI := AdjacentCoordinateAlgebra.coordinateRing_isDomain c h
       (Spec (.of (literalR c))).fromSpecStalk (genericPoint (Spec (.of (literalR c)))) ≫ m =
         literalGenericMap c h)) ∧
    (letI := geometricIntegral c hc h1
     letI := (baseToFunctionField (geometricToBase c)).toAlgebra
     genusFF (AlgebraicClosure ℚ) (geometricScheme c).functionField = 5) ∧
    (letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
       (geometricToBase c) (geometricToBase c).kaehler ⊤
     Module.Finite (AlgebraicClosure ℚ) Γ((geometricToBase c).kaehler, ⊤) ∧
       Module.finrank (AlgebraicClosure ℚ) Γ((geometricToBase c).kaehler, ⊤) = 5) := by
  refine ⟨?_,?_,?_,model_geometricallyIntegral c hc h1,model_geometricallyConnected c hc h1,
    ⟨sourceToModel c hc h1,sourceToModel_over c hc h1,generic_sourceToModel c hc h1⟩,
    geometric_genus_five c hc h1,geometric_globalDifferentials_five c hc h1⟩
  · exact model_integral c
  · exact model_proper c
  · exact model_smooth c

#print axioms rational_model_source_and_geometric_genus
end FourCorner.AdjacentPostEndpoint
