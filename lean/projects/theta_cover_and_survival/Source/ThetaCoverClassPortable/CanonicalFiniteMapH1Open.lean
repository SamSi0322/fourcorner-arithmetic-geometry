import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial
import ThetaCoverClassPortable.FiniteMapCohomology
import ThetaCoverClassPortable.FibreSurjectivityOpen

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra
open scoped TensorProduct
universe u
namespace FourCorner.ActualCohomologyChartInputs
variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}

/-- For the actual native finite-map cover, actual residue-fibre H1
vanishing is surjectivity of the base change of its actual differential.
The comparison is the genuine natural section base-change comparison. -/
theorem canonical_finiteMap_H1_fibre_iff_surjective
    (F : SmoothProperCurve.FiniteMapData c ε) (M : C.Modules)
    (htriv : ∀ x : C, ∃ (V : C.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (p : PrimeSpectrum R) :
    Subsingleton (((F.twoAffineOpenCover.pullback c p.asIdeal.ResidueField).sectionsOf
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R p.asIdeal.ResidueField))
      ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R p.asIdeal.ResidueField))).obj M)).H1) ↔
      Function.Surjective ((F.twoAffineOpenCover.sectionsOf c M).cechDiff.baseChange p.asIdeal.ResidueField) := by
  obtain ⟨⟨e⟩, -, -⟩ := Scheme.TwoAffineOpenCover.exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial
    F.twoAffineOpenCover c M htriv p.asIdeal.ResidueField
  exact e.toEquiv.subsingleton_congr.trans
    (FourCorner.FibreSurjectivity.surjective_baseChange_iff _ _).symm

/-- Genuine openness for the actual canonical FMD cover. No target H1
finiteness, general proper-coherence theorem, or flatness is a premise.
This explicitly retains the canonical-cover scope. -/
theorem canonical_finiteMap_isOpen_H1_fibre
    (F : SmoothProperCurve.FiniteMapData c ε) (M : C.Modules)
    (htriv : ∀ x : C, ∃ (V : C.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    IsOpen {p : PrimeSpectrum R | Subsingleton
      (((F.twoAffineOpenCover.pullback c p.asIdeal.ResidueField).sectionsOf
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R p.asIdeal.ResidueField))
        ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R p.asIdeal.ResidueField))).obj M)).H1)} := by
  haveI := FourCorner.FiniteMapCohomology.finiteMap_H1_finite F M htriv
  have heq : {p : PrimeSpectrum R | Subsingleton
      (((F.twoAffineOpenCover.pullback c p.asIdeal.ResidueField).sectionsOf
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R p.asIdeal.ResidueField))
        ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R p.asIdeal.ResidueField))).obj M)).H1)} =
      {p : PrimeSpectrum R | Function.Surjective ((F.twoAffineOpenCover.sectionsOf c M).cechDiff.baseChange p.asIdeal.ResidueField)} := by
    ext p
    exact canonical_finiteMap_H1_fibre_iff_surjective F M htriv p
  rw [heq]
  exact LinearMap.isOpen_setOf_surjective_baseChange_residueField _
end FourCorner.ActualCohomologyChartInputs
