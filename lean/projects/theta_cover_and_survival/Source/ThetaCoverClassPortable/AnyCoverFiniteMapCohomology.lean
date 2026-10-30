import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_linearEquiv_H1_sectionsOf_of_isSeparated
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import ThetaCoverClassPortable.CanonicalFiniteMapH1Open

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra
universe u
namespace FourCorner.ActualCohomologyChartInputs
variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} [IsSeparated c]

theorem finiteMap_H1_anyCover (F : SmoothProperCurve.FiniteMapData c ε) (M : C.Modules)
    (htriv : ∀ x : C, ∃ (V : C.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (V : C.TwoAffineOpenCover) : Module.Finite R (V.sectionsOf c M).H1 := by
  haveI := FourCorner.FiniteMapCohomology.finiteMap_H1_finite F M htriv
  obtain ⟨e⟩ := Scheme.TwoAffineOpenCover.nonempty_linearEquiv_H1_sectionsOf_of_isSeparated
    c M htriv F.twoAffineOpenCover V
  exact Module.Finite.equiv e

theorem finiteMap_H0_H1_anyCover [IsNoetherianRing R]
    (F : SmoothProperCurve.FiniteMapData c ε) (M : C.Modules)
    (htriv : ∀ x : C, ∃ (V : C.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (V : C.TwoAffineOpenCover) :
    Module.Finite R (V.sectionsOf c M).H0 ∧ Module.Finite R (V.sectionsOf c M).H1 := by
  haveI := (F.finite_H0_H1_sectionsOf M htriv).1
  obtain ⟨e0, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 F.twoAffineOpenCover c M
  obtain ⟨e1, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 V c M
  exact ⟨Module.Finite.equiv (e0.symm.trans e1),finiteMap_H1_anyCover F M htriv V⟩

/-- Actual residue-fibre vanishing for EVERY two-affine cover is equivalent
to vanishing for the canonical finite-map cover. All comparison maps and
restriction signs are inherited from the proved actual cover equivalence. -/
theorem allCover_H1_fibre_iff_canonical
    (F : SmoothProperCurve.FiniteMapData c ε) (M : C.Modules)
    (htriv : ∀ x : C, ∃ (V : C.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (p : PrimeSpectrum R) :
    (∀ V : (pullback c (Scheme.TwoAffineOpenCover.specMap R p.asIdeal.ResidueField)).TwoAffineOpenCover,
      Subsingleton (V.sectionsOf
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R p.asIdeal.ResidueField))
        ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R p.asIdeal.ResidueField))).obj M)).H1) ↔
      Subsingleton (((F.twoAffineOpenCover.pullback c p.asIdeal.ResidueField).sectionsOf
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R p.asIdeal.ResidueField))
        ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R p.asIdeal.ResidueField))).obj M)).H1) := by
  constructor
  · intro h
    exact h (F.twoAffineOpenCover.pullback c p.asIdeal.ResidueField)
  · intro h V
    have hM : Scheme.Modules.IsInvertible M := ⟨htriv⟩
    have hMK := hM.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R p.asIdeal.ResidueField))
    obtain ⟨e⟩ := Scheme.TwoAffineOpenCover.nonempty_linearEquiv_H1_sectionsOf_of_isSeparated
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R p.asIdeal.ResidueField))
      ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R p.asIdeal.ResidueField))).obj M)
      hMK.1 (F.twoAffineOpenCover.pullback c p.asIdeal.ResidueField) V
    haveI := h
    exact e.symm.toEquiv.subsingleton

/-- The full EVERY-cover residue-fibre H1 vanishing locus is genuinely open
for the actual finite-map curve. No general proper-coherence result is used. -/
theorem finiteMap_isOpen_allCover_H1_fibre
    (F : SmoothProperCurve.FiniteMapData c ε) (M : C.Modules)
    (htriv : ∀ x : C, ∃ (V : C.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    IsOpen {p : PrimeSpectrum R | ∀ V :
      (pullback c (Scheme.TwoAffineOpenCover.specMap R p.asIdeal.ResidueField)).TwoAffineOpenCover,
      Subsingleton (V.sectionsOf
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R p.asIdeal.ResidueField))
        ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R p.asIdeal.ResidueField))).obj M)).H1} := by
  have heq : {p : PrimeSpectrum R | ∀ V :
      (pullback c (Scheme.TwoAffineOpenCover.specMap R p.asIdeal.ResidueField)).TwoAffineOpenCover,
      Subsingleton (V.sectionsOf
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R p.asIdeal.ResidueField))
        ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R p.asIdeal.ResidueField))).obj M)).H1} =
      {p : PrimeSpectrum R | Subsingleton (((F.twoAffineOpenCover.pullback c p.asIdeal.ResidueField).sectionsOf
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R p.asIdeal.ResidueField))
        ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R p.asIdeal.ResidueField))).obj M)).H1)} := by
    ext p
    exact allCover_H1_fibre_iff_canonical F M htriv p
  rw [heq]
  exact canonical_finiteMap_isOpen_H1_fibre F M htriv
end FourCorner.ActualCohomologyChartInputs
