import ThetaCoverClassPortable.FiniteMapOverlapSections
import ThetaCoverClassPortable.LaurentGluingCover

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory NeronModelInfra Polynomial
universe u
namespace FourCorner.FiniteMapCohomology
variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}

/-- Restrict the actual FMD Cech modules to the literal polynomial/Laurent
scalar rings. Underlying modules and maps are SAME actual sections/restrictions;
only their explicitly supplied scalar actions are restricted. -/
def finiteMapLaurentSections (F : SmoothProperCurve.FiniteMapData c ε) (M : C.Modules) :
    TwoChartCech.Sections (laurentCover R) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c F.U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c F.V
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c (F.U ⊓ F.V)
  letI : Module R Γ(M,F.U) := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M F.U
  letI : Module R Γ(M,F.V) := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M F.V
  letI : Module R Γ(M,F.U ⊓ F.V) := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M (F.U ⊓ F.V)
  letI : Module R[X] Γ(M,F.U) := Module.compHom Γ(M,F.U) (Polynomial.aeval F.f : R[X] →ₐ[R] Γ(C,F.U)).toRingHom
  letI : Module R[X] Γ(M,F.V) := Module.compHom Γ(M,F.V) (Polynomial.aeval F.g : R[X] →ₐ[R] Γ(C,F.V)).toRingHom
  haveI : IsScalarTower R R[X] Γ(M,F.U) := IsScalarTower.of_algebraMap_smul fun a m => by
    change (Polynomial.aeval F.f : R[X] →ₐ[R] Γ(C,F.U)) (algebraMap R R[X] a) • m = _
    rw [AlgHom.commutes]
    rfl
  haveI : IsScalarTower R R[X] Γ(M,F.V) := IsScalarTower.of_algebraMap_smul fun a m => by
    change (Polynomial.aeval F.g : R[X] →ₐ[R] Γ(C,F.V)) (algebraMap R R[X] a) • m = _
    rw [AlgHom.commutes]
    rfl
  letI : Module (LaurentPolynomial R) Γ(M,F.U ⊓ F.V) :=
    Module.compHom Γ(M,F.U ⊓ F.V) (laurentEvaluation (R := R) (overlapUnit F)).toRingHom
  haveI : IsScalarTower R (LaurentPolynomial R) Γ(M,F.U ⊓ F.V) :=
    IsScalarTower.of_algebraMap_smul fun a m => by
      change laurentEvaluation (R := R) (overlapUnit F) (algebraMap R (LaurentPolynomial R) a) • m = _
      rw [AlgHom.commutes]
      rfl
  refine {
    M0 := Γ(M,F.V)
    M1 := Γ(M,F.U)
    M01 := Γ(M,F.U ⊓ F.V)
    M0_moduleA := inferInstanceAs (Module R[X] Γ(M,F.V))
    M1_moduleA := inferInstanceAs (Module R[X] Γ(M,F.U))
    M01_moduleA := inferInstanceAs (Module (LaurentPolynomial R) Γ(M,F.U ⊓ F.V))
    r0 := restrictNegative F M
    r1 := restrictPositive F M
    r0_smul := ?_
    r1_smul := ?_ }
  · intro p x
    change M.presheaf.map (homOfLE (inf_le_right : F.U ⊓ F.V ≤ F.V)).op
      ((Polynomial.aeval F.g : R[X] →ₐ[R] Γ(C,F.V)) p • x) =
        laurentEvaluation (R := R) (overlapUnit F) (LaurentPolynomial.invert (Polynomial.toLaurent p)) •
          M.presheaf.map (homOfLE (inf_le_right : F.U ⊓ F.V ≤ F.V)).op x
    rw [Scheme.Modules.map_smul,laurentEvaluation_minus]
    congr 1
    exact (Polynomial.aeval_algHom_apply
      (Scheme.TwoAffineOpenCover.restrictAlgHom c (inf_le_right : F.U ⊓ F.V ≤ F.V)) F.g p).symm
  · intro p x
    change M.presheaf.map (homOfLE (inf_le_left : F.U ⊓ F.V ≤ F.U)).op
      ((Polynomial.aeval F.f : R[X] →ₐ[R] Γ(C,F.U)) p • x) =
        laurentEvaluation (R := R) (overlapUnit F) (Polynomial.toLaurent p) •
          M.presheaf.map (homOfLE (inf_le_left : F.U ⊓ F.V ≤ F.U)).op x
    rw [Scheme.Modules.map_smul,laurentEvaluation_plus]
    congr 1
    exact (Polynomial.aeval_algHom_apply
      (Scheme.TwoAffineOpenCover.restrictAlgHom c (inf_le_left : F.U ⊓ F.V ≤ F.U)) F.f p).symm

 theorem finiteMapLaurentSections_finite_negative
    (F : SmoothProperCurve.FiniteMapData c ε) (M : C.Modules)
    (htriv : ∀ x : C, ∃ (V : C.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    Module.Finite R[X] (finiteMapLaurentSections F M).M0 :=
  finiteMap_sections_V_polynomial F M htriv

 theorem finiteMapLaurentSections_finite_positive
    (F : SmoothProperCurve.FiniteMapData c ε) (M : C.Modules)
    (htriv : ∀ x : C, ∃ (V : C.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    Module.Finite R[X] (finiteMapLaurentSections F M).M1 :=
  finiteMap_sections_U_polynomial F M htriv
end FourCorner.FiniteMapCohomology
