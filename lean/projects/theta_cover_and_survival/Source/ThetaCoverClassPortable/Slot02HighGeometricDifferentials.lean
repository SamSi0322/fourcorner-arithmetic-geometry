import ThetaCoverClassPortable.Slot02HighGeometricGenus
import ThetaCoverClassPortable.geometry.OppositeSchemeDifferentials

noncomputable section
namespace FourCorner.OppositeProjective.HighGenus
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open OppositeSchemeModel

theorem geometricProper (mu nu : ℚ) : IsProper (geometricToBase mu nu) := by
  haveI := model_proper mu nu
  unfold geometricToBase modelToBase
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem geometricSmooth (mu nu : ℚ) : SmoothOfRelativeDimension 1 (geometricToBase mu nu) := by
  haveI := model_smooth mu nu
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  change SmoothOfRelativeDimension 1 (pullback.snd (modelToBase mu nu) (Scheme.TwoAffineOpenCover.specMap ℚ (AlgebraicClosure ℚ)))
  exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance

/-- Actual geometric genus via global sections of the Kähler sheaf on the categorical Qbar pullback. -/
theorem geometric_globalDifferentials_five (mu nu : ℚ) (hn : nu ≠ 0)
    (hp : 0 < mu / nu) (hl : mu / nu < 2) :
    let c := geometricToBase mu nu
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler ⊤
    Module.Finite (AlgebraicClosure ℚ) Γ(c.kaehler, ⊤) ∧
      Module.finrank (AlgebraicClosure ℚ) Γ(c.kaehler, ⊤) = 5 := by
  let c := geometricToBase mu nu
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler ⊤
  letI := geometricIntegral mu nu hn hp hl
  letI := geometricProper mu nu
  letI := geometricSmooth mu nu
  let V := (modelCover mu nu).pullback (modelToBase mu nu) (AlgebraicClosure ℚ)
  obtain ⟨hfin, hrk⟩ := KaehlerSheafBridge.finite_and_finrank_globalDifferentials_eq_genusFF V c
  exact ⟨hfin, hrk.trans (geometric_genus_five mu nu hn hp hl)⟩

#print axioms geometricProper
#print axioms geometricSmooth
#print axioms geometric_globalDifferentials_five
end FourCorner.OppositeProjective.HighGenus
