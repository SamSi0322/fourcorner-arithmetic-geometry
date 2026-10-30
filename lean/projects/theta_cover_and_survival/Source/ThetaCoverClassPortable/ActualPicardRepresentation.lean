import ThetaCoverClassPortable.ActualPicardAtlas
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelSubPicGlue

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.RelPicard
universe u
namespace FourCorner.ActualPicardRepresentation

/-- The actual all-test atlas is glued to its native represented Picard
zero-cut. Properness, smoothness, AF and QQ descent are separate theorems. -/
theorem exists_represented
    (R : Type u) [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R]
    {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 _) c)
    (hF : ∀m0:ℕ,∃F:SmoothProperCurve.FiniteMapData c ε,m0≤F.m)
    (n g r : ℕ) (hgr : 2*g<r)
    (γ : Fin n → Fin (r-g) → SchemeHomOver (𝟙 _) c) (hγ : HasChartSections c γ)
    (hUniv : ∀d:ℕ,∃(Y:Scheme.{u})(y:Y⟶Spec (.of R))(D:RelEffCartierDiv c d y),D.IsUniversal)
    (hSheaf : Presieve.IsSheaf (Scheme.zariskiTopology.over (Spec (.of R)))
      (relSubPicPresheaf c ε (algEquivZeroCut c ε))) :
    ∃ D : GoodReductionJacobian.RelativePic0Designation R c,
      Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) := by
  obtain ⟨X,f,hf,hsurj⟩ := ActualPicardAtlas.solution R c ε hF n g r hgr γ hγ hUniv hSheaf
  haveI := hsurj
  exact ⟨gluedDesignation hSheaf f hf,RepresentsRelSubPic.nonempty_gluedDesignation hSheaf f hf⟩

#print axioms exists_represented
end FourCorner.ActualPicardRepresentation
