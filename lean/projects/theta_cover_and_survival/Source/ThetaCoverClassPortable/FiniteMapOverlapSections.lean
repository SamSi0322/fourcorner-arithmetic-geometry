import ThetaCoverClassPortable.FiniteMapChartSections
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory NeronModelInfra Opposite
universe u
namespace FourCorner.FiniteMapCohomology
variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
  (F : SmoothProperCurve.FiniteMapData c ε) (M : C.Modules)
/-- The actual reciprocal function unit on the literal FMD overlap. -/
def overlapUnit : Γ(C,F.U ⊓ F.V)ˣ where
  val := C.presheaf.map (homOfLE inf_le_left).op F.f
  inv := C.presheaf.map (homOfLE inf_le_right).op F.g
  val_inv := F.res_f_mul_res_g
  inv_val := by rw [mul_comm];exact F.res_f_mul_res_g

def restrictPositive :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M F.U
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M (F.U ⊓ F.V)
    Γ(M,F.U) →ₗ[R] Γ(M,F.U ⊓ F.V) := Scheme.TwoAffineOpenCover.restrictSections c M inf_le_left
def restrictNegative :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M F.V
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M (F.U ⊓ F.V)
    Γ(M,F.V) →ₗ[R] Γ(M,F.U ⊓ F.V) := Scheme.TwoAffineOpenCover.restrictSections c M inf_le_right

/-- Genuine local-module localization on the positive FMD chart, retaining
both denominator clearing and the annihilation of restriction-kernel sections. -/
theorem positive_overlap_localization
    (htriv : ∀ x : C, ∃ (V : C.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    (∀ z : Γ(M,F.U ⊓ F.V), ∃ (n : ℕ) (x : Γ(M,F.U)),
      restrictPositive F M x = (overlapUnit F ^ n : Γ(C,F.U ⊓ F.V)ˣ) • z) ∧
    (∀ x : Γ(M,F.U), restrictPositive F M x=0 → ∃ n : ℕ, F.f^n • x=0) := by
  have h := Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial M htriv ⟨F.U,F.isAffineOpen_U⟩ F.f
  change (∀ z : Γ(M,F.U ⊓ F.V), ∃ n x,
    M.presheaf.map (homOfLE (inf_le_left : F.U ⊓ F.V ≤ F.U)).op x =
      (C.presheaf.map (homOfLE (inf_le_left : F.U ⊓ F.V ≤ F.U)).op F.f)^n • z) ∧ _
  have aux (W : C.Opens) (hW : W ≤ F.U) (he : W=C.basicOpen F.f) :
      (∀ z : Γ(M,W), ∃ (n : ℕ) (x : Γ(M,F.U)),
        M.presheaf.map (homOfLE hW).op x = (C.presheaf.map (homOfLE hW).op F.f)^n • z) ∧
      (∀ x : Γ(M,F.U), M.presheaf.map (homOfLE hW).op x=0 → ∃ n : ℕ, F.f^n • x=0) := by
    subst W
    simpa only [map_pow] using h
  simpa only [restrictPositive,Scheme.TwoAffineOpenCover.restrictSections_apply] using
    aux (F.U ⊓ F.V) inf_le_left F.inf_eq_basicOpen

/-- The symmetric actual negative-chart localization; the reciprocal
function is exactly the inverse of the same overlap unit. -/
theorem negative_overlap_localization
    (htriv : ∀ x : C, ∃ (V : C.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    (∀ z : Γ(M,F.U ⊓ F.V), ∃ (n : ℕ) (y : Γ(M,F.V)),
      restrictNegative F M y = ((overlapUnit F)⁻¹ ^ n : Γ(C,F.U ⊓ F.V)ˣ) • z) ∧
    (∀ y : Γ(M,F.V), restrictNegative F M y=0 → ∃ n : ℕ, F.g^n • y=0) := by
  have h := Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial M htriv ⟨F.V,F.isAffineOpen_V⟩ F.g
  change (∀ z : Γ(M,F.U ⊓ F.V), ∃ n y,
    M.presheaf.map (homOfLE (inf_le_right : F.U ⊓ F.V ≤ F.V)).op y =
      (C.presheaf.map (homOfLE (inf_le_right : F.U ⊓ F.V ≤ F.V)).op F.g)^n • z) ∧ _
  have aux (W : C.Opens) (hW : W ≤ F.V) (he : W=C.basicOpen F.g) :
      (∀ z : Γ(M,W), ∃ (n : ℕ) (y : Γ(M,F.V)),
        M.presheaf.map (homOfLE hW).op y = (C.presheaf.map (homOfLE hW).op F.g)^n • z) ∧
      (∀ y : Γ(M,F.V), M.presheaf.map (homOfLE hW).op y=0 → ∃ n : ℕ, F.g^n • y=0) := by
    subst W
    simpa only [map_pow] using h
  simpa only [restrictNegative,Scheme.TwoAffineOpenCover.restrictSections_apply] using
    aux (F.U ⊓ F.V) inf_le_right F.inf_eq_basicOpen_g

/-- Polynomial-power compatibility is the TRUE module restriction formula. -/
theorem positive_restrict_power (n : ℕ) (x : Γ(M,F.U)) :
    restrictPositive F M (F.f^n • x) = (overlapUnit F ^ n : Γ(C,F.U ⊓ F.V)ˣ) • restrictPositive F M x := by
  change M.presheaf.map (homOfLE (inf_le_left : F.U ⊓ F.V ≤ F.U)).op (F.f^n • x) =
    (C.presheaf.map (homOfLE (inf_le_left : F.U ⊓ F.V ≤ F.U)).op F.f)^n • _
  rw [Scheme.Modules.map_smul,map_pow]
  rfl

theorem negative_restrict_power (n : ℕ) (y : Γ(M,F.V)) :
    restrictNegative F M (F.g^n • y) = ((overlapUnit F)⁻¹ ^ n : Γ(C,F.U ⊓ F.V)ˣ) • restrictNegative F M y := by
  change M.presheaf.map (homOfLE (inf_le_right : F.U ⊓ F.V ≤ F.V)).op (F.g^n • y) =
    (C.presheaf.map (homOfLE (inf_le_right : F.U ⊓ F.V ≤ F.V)).op F.g)^n • _
  rw [Scheme.Modules.map_smul,map_pow]
  rfl

end FourCorner.FiniteMapCohomology
