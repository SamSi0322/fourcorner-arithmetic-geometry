import ThetaCoverClassPortable.FiniteMapLaurentLocalizations
import ThetaCoverClassPortable.LaurentH1Finite

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory NeronModelInfra
universe u
namespace FourCorner.FiniteMapCohomology
variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}

/-- Transport along equality of actual opens, retaining the actual structural
R-action. It is not a chosen equivalence of cohomology modules. -/
def sectionsCongr (c : C ⟶ Spec (.of R)) (M : C.Modules) (U V : C.Opens) (h : U=V) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M U
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M V
    Γ(M,U) ≃ₗ[R] Γ(M,V) := by
  subst V
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M U
  exact LinearEquiv.refl R _

 theorem sectionsCongr_restrict (c : C ⟶ Spec (.of R)) (M : C.Modules)
    (W U V : C.Opens) (hU : U≤W) (hV : V≤W) (h : U=V) (x : Γ(M,W)) :
    sectionsCongr c M U V h (Scheme.TwoAffineOpenCover.restrictSections c M hU x) =
      Scheme.TwoAffineOpenCover.restrictSections c M hV x := by
  subst V
  rfl

 def nativeOverlapEquiv (F : SmoothProperCurve.FiniteMapData c ε) (M : C.Modules) :
    (finiteMapLaurentSections F M).M01 ≃ₗ[R] (F.twoAffineOpenCover.sectionsOf c M).M01 :=
  sectionsCongr c M (F.U ⊓ F.V) (F.V ⊓ F.U) (inf_comm F.U F.V)

 theorem nativeOverlap_positive (F : SmoothProperCurve.FiniteMapData c ε) (M : C.Modules) (x : Γ(M,F.U)) :
    nativeOverlapEquiv F M ((finiteMapLaurentSections F M).r1 x) =
      (F.twoAffineOpenCover.sectionsOf c M).r1 x :=
  sectionsCongr_restrict c M F.U (F.U ⊓ F.V) (F.V ⊓ F.U) inf_le_left inf_le_right (inf_comm F.U F.V) x

 theorem nativeOverlap_negative (F : SmoothProperCurve.FiniteMapData c ε) (M : C.Modules) (x : Γ(M,F.V)) :
    nativeOverlapEquiv F M ((finiteMapLaurentSections F M).r0 x) =
      (F.twoAffineOpenCover.sectionsOf c M).r0 x :=
  sectionsCongr_restrict c M F.V (F.U ⊓ F.V) (F.V ⊓ F.U) inf_le_right inf_le_left (inf_comm F.U F.V) x

 def nativeCochain0 (F : SmoothProperCurve.FiniteMapData c ε) (M : C.Modules) :
    ((finiteMapLaurentSections F M).M0 × (finiteMapLaurentSections F M).M1) →ₗ[R]
      ((F.twoAffineOpenCover.sectionsOf c M).M0 × (F.twoAffineOpenCover.sectionsOf c M).M1) :=
  LinearMap.id

 theorem nativeCochain_comm (F : SmoothProperCurve.FiniteMapData c ε) (M : C.Modules) :
    (F.twoAffineOpenCover.sectionsOf c M).cechDiff.comp (nativeCochain0 F M) =
      (nativeOverlapEquiv F M).toLinearMap.comp (finiteMapLaurentSections F M).cechDiff := by
  apply LinearMap.ext
  intro z
  change (F.twoAffineOpenCover.sectionsOf c M).cechDiff z =
    nativeOverlapEquiv F M ((finiteMapLaurentSections F M).cechDiff z)
  rw [TwoChartCech.Sections.cechDiff_apply,TwoChartCech.Sections.cechDiff_apply,map_sub,
    nativeOverlap_positive,nativeOverlap_negative]

/-- This is already finiteness of the ACTUAL original FMD Cech H1, with all
localization, scalar and native-cover transport inputs proved internally. -/
theorem finiteMap_H1_finite (F : SmoothProperCurve.FiniteMapData c ε) (M : C.Modules)
    (htriv : ∀ x : C, ∃ (V : C.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    Module.Finite R (F.twoAffineOpenCover.sectionsOf c M).H1 := by
  haveI := finiteMapLaurentSections_finite_negative F M htriv
  haveI := finiteMapLaurentSections_finite_positive F M htriv
  haveI := laurent_H1_finite (finiteMapLaurentSections F M)
    (finiteMap_negative_localizes F M htriv) (finiteMap_positive_localizes F M htriv)
  exact FourCorner.TwoTermFiniteness.finite_H1 (finiteMapLaurentSections F M).cechDiff
    (F.twoAffineOpenCover.sectionsOf c M).cechDiff (nativeCochain0 F M)
    (nativeOverlapEquiv F M).toLinearMap (nativeCochain_comm F M) (nativeOverlapEquiv F M).surjective
end FourCorner.FiniteMapCohomology
