import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_finite_sections_of_locallyTrivial

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory NeronModelInfra
universe u
namespace FourCorner.FiniteMapCohomology

/-- Actual sections of a locally trivial invertible module on an affine chart
finite over R[T] are genuinely finite as polynomial modules. No global H0/H1
finiteness or polynomial freeness is a premise. -/
theorem finite_affine_sections_over_polynomial
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
    (M : C.Modules)
    (htriv : ∀ x : C, ∃ (V : C.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : C.Opens) (hU : IsAffineOpen U) (f : Γ(C,U))
    (hfin : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
      (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C,U)).toRingHom.Finite) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI : Algebra (Polynomial R) Γ(C,U) := (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C,U)).toRingHom.toAlgebra
    letI : Module (Polynomial R) Γ(M,U) := Module.compHom Γ(M,U) (algebraMap (Polynomial R) Γ(C,U))
    Module.Finite (Polynomial R) Γ(M,U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI : Algebra (Polynomial R) Γ(C,U) := (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C,U)).toRingHom.toAlgebra
  letI : Module (Polynomial R) Γ(M,U) := Module.compHom Γ(M,U) (algebraMap (Polynomial R) Γ(C,U))
  haveI : IsScalarTower (Polynomial R) Γ(C,U) Γ(M,U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite (Polynomial R) Γ(C,U) := hfin
  haveI : Module.Finite Γ(C,U) Γ(M,U) :=
    Scheme.Modules.finite_sections_of_locallyTrivial M htriv ⟨U,hU⟩
  exact Module.Finite.trans Γ(C,U) Γ(M,U)

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}

theorem finiteMap_sections_U_polynomial (F : SmoothProperCurve.FiniteMapData c ε)
    (M : C.Modules)
    (htriv : ∀ x : C, ∃ (V : C.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c F.U
    letI : Algebra (Polynomial R) Γ(C,F.U) := (Polynomial.aeval F.f : Polynomial R →ₐ[R] Γ(C,F.U)).toRingHom.toAlgebra
    letI : Module (Polynomial R) Γ(M,F.U) := Module.compHom Γ(M,F.U) (algebraMap (Polynomial R) Γ(C,F.U))
    Module.Finite (Polynomial R) Γ(M,F.U) :=
  finite_affine_sections_over_polynomial c M htriv F.U F.isAffineOpen_U F.f F.finite_f

theorem finiteMap_sections_V_polynomial (F : SmoothProperCurve.FiniteMapData c ε)
    (M : C.Modules)
    (htriv : ∀ x : C, ∃ (V : C.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c F.V
    letI : Algebra (Polynomial R) Γ(C,F.V) := (Polynomial.aeval F.g : Polynomial R →ₐ[R] Γ(C,F.V)).toRingHom.toAlgebra
    letI : Module (Polynomial R) Γ(M,F.V) := Module.compHom Γ(M,F.V) (algebraMap (Polynomial R) Γ(C,F.V))
    Module.Finite (Polynomial R) Γ(M,F.V) :=
  finite_affine_sections_over_polynomial c M htriv F.V F.isAffineOpen_V F.g F.finite_g
end FourCorner.FiniteMapCohomology
