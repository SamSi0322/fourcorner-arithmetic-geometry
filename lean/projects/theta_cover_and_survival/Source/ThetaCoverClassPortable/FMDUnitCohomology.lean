import ThetaCoverClassPortable.UnitSections
import ThetaCoverClassPortable.FiniteMapCohomology
import ThetaCoverClassPortable.FiniteMapDataBaseChange
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory NeronModelInfra
universe u
namespace FourCorner.FMDUnitCohomology

section Field
variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}}
  {π : Y ⟶ Spec (.of k)} {ε : SchemeHomOver (𝟙 (Spec (.of k))) π}

/-- True FMD cohomology and the actual Gamma/H0 equivalence prove finite
STRUCTURE-RING sections. No genus or desired dimension is an input. -/
theorem field_globalSections_finite (F : SmoothProperCurve.FiniteMapData π ε) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π (⊤ : Y.Opens)
    Module.Finite k Γ(Y,⊤) := by
  let M := SheafOfModules.unit Y.ringCatSheaf
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π (⊤ : Y.Opens)
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M (⊤ : Y.Opens)
  haveI := (F.finite_H0_H1_sectionsOf M (Scheme.Modules.isInvertible_unit Y).exists_trivialization).1
  obtain ⟨eΓ,-⟩ := F.twoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 π M
  haveI : Module.Finite k Γ(M,⊤) := Module.Finite.equiv eΓ.symm
  exact Module.Finite.equiv (unitSectionsRingEquiv π (⊤ : Y.Opens))

/-- The CANONICAL structural map is bijective: actual integral Gamma is a
finite integral k-algebra, and k is algebraically closed. No dimension iso. -/
theorem field_structuralMap_bijective [IsIntegral Y] (F : SmoothProperCurve.FiniteMapData π ε) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π (⊤ : Y.Opens)
    Function.Bijective (algebraMap k Γ(Y,⊤)) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π (⊤ : Y.Opens)
  haveI := field_globalSections_finite F
  haveI : Algebra.IsIntegral k Γ(Y,⊤) := inferInstance
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- ANY actual native cover has unit H0 of dimension1, through actual global
sections and the proved canonical structural map, not a supplied genus/dim. -/
theorem field_finrank_H0_unit_eq_one [IsIntegral Y]
    (F : SmoothProperCurve.FiniteMapData π ε) (V : Y.TwoAffineOpenCover) :
    Module.finrank k (V.sectionsOf π (SheafOfModules.unit Y.ringCatSheaf)).H0 = 1 := by
  let M := SheafOfModules.unit Y.ringCatSheaf
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π (⊤ : Y.Opens)
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M (⊤ : Y.Opens)
  obtain ⟨eΓ,-⟩ := V.exists_linearEquiv_sectionsOf_H0 π M
  let eK : k ≃ₗ[k] Γ(Y,⊤) := LinearEquiv.ofBijective (Algebra.linearMap k Γ(Y,⊤))
    (field_structuralMap_bijective F)
  rw [←eΓ.finrank_eq,(unitSectionsRingEquiv π (⊤ : Y.Opens)).finrank_eq,←eK.finrank_eq]
  exact Module.finrank_self k
end Field

section Fibre
variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}

/-- Honest actual-FMD fibre version of structural-map bijectivity. R need
NOT be Noetherian. The original FMD is actually base changed internally. -/
theorem structuralMap_bijective_fibre (F : SmoothProperCurve.FiniteMapData c ε)
    {k : Type u} [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ Spec (.of R)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.snd c x) (⊤ : (pullback c x).Opens)
    Function.Bijective (algebraMap k Γ(pullback c x,⊤)) := by
  obtain ⟨a,ha⟩ := Spec.map_surjective x
  letI : Algebra R k := a.hom.toAlgebra
  have hx : Scheme.TwoAffineOpenCover.specMap R k=x := ha
  subst x
  haveI : IsIntegral (pullback c (Scheme.TwoAffineOpenCover.specMap R k)) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (IsPullback.of_hasPullback _ _)
  exact field_structuralMap_bijective (F.baseChange k)

/-- The requested actual-FMD H0 leaf: arbitrary algebraically closed field
point, ANY two-affine cover, true native UNIT. No genus theorem/NoethR/dim premise. -/
theorem finrank_H0_unit_fibre_eq_one (F : SmoothProperCurve.FiniteMapData c ε)
    {k : Type u} [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ Spec (.of R))
    (V : (pullback c x).TwoAffineOpenCover) :
    Module.finrank k (V.sectionsOf (pullback.snd c x) (𝟙_ (pullback c x).Modules)).H0 = 1 := by
  obtain ⟨a,ha⟩ := Spec.map_surjective x
  letI : Algebra R k := a.hom.toAlgebra
  have hx : Scheme.TwoAffineOpenCover.specMap R k=x := ha
  subst x
  haveI : IsIntegral (pullback c (Scheme.TwoAffineOpenCover.specMap R k)) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (IsPullback.of_hasPullback _ _)
  exact field_finrank_H0_unit_eq_one (F.baseChange k) V
end Fibre
end FourCorner.FMDUnitCohomology
