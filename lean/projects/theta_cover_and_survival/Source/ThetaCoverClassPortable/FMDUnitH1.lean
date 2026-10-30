import ThetaCoverClassPortable.UnitStructureCohomology
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_finite_H0_H1_structureSheaf_of_smoothProperCurve
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_eq_genusFF_of_forall_ell_sub_ell_eq
import ThetaCoverClassPortable.ThetaIsoFunctionField
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_genusFF_eq_of_algEquiv

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry CategoryTheory AlgebraicCurve NeronModelInfra
universe u
namespace FourCorner.FMDUnitH1
variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}}
  {π : Y ⟶ Spec (.of k)} {ε : SchemeHomOver (𝟙 (Spec (.of k))) π}
  [IsIntegral Y] [IsProper π] [SmoothOfRelativeDimension 1 π]

/-- Actual native unit H1 equals the SAME curve's adelic function-field genus.
The genusReached input is derived from the true function field, not from H1. -/
theorem field_H1_eq_genusFF (F : SmoothProperCurve.FiniteMapData π ε)
    (V : Y.TwoAffineOpenCover) :
    letI := (baseToFunctionField π).toAlgebra
    Module.finrank k (V.sectionsOf π (𝟙_ Y.Modules)).H1 = genusFF k Y.functionField := by
  letI := (baseToFunctionField π).toAlgebra
  haveI : IsCurveOver k Y.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one π (RingEquiv.refl _) (fun _ => rfl)
  haveI : Algebra.EssFiniteType k Y.functionField := essFiniteType_functionField π
  obtain ⟨t,ht,hfd,hsep⟩ := IsCurveOver.exists_separating_transcendental (K:=k) (F:=Y.functionField)
  letI := hfd
  have hc := constantsAreBase_of_isAlgClosed_of_transcendental t ht
  obtain ⟨-,hL0,γ,D₀,hγ⟩ := stichtenothGenusExists_of_isCurveOver hc
  have h := finite_H0_H1_structureSheaf_of_smoothProperCurve V π inferInstance hL0 ⟨γ,D₀,hγ⟩
  obtain ⟨-,⟨e1⟩⟩ := unit_equiv V π
  exact e1.finrank_eq.trans h.2.2.2

/-- A genuine model and all-divisor RR equation determine the integer g;
no H1 dimension premise is used. -/
theorem field_H1_eq_of_model_RR (F : SmoothProperCurve.FiniteMapData π ε)
    {L : Type u} [Field L] [Algebra k L] (M : CurveModel k L)
    (e : M.C ≅ Y) (he : e.hom ≫ π=M.toBase)
    (Kc : Divisor k L) (g : ℕ)
    (hRR : ∀ D : Divisor k L, (ell D:ℤ)-ell (Kc-D)=Divisor.degree D+1-g)
    (V : Y.TwoAffineOpenCover) :
    Module.finrank k (V.sectionsOf π (𝟙_ Y.Modules)).H1=g := by
  letI := M.isIntegral
  letI := M.isProper
  letI := M.smooth
  letI := M.functionFieldAlgebra
  letI := (baseToFunctionField π).toAlgebra
  let φ := ThetaIsoFunctionField.algEquiv M.toBase π e he
  haveI : IsCurveOver k L := isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
    M.toBase M.ffEquiv M.ffEquiv_algebraMap
  haveI : Algebra.EssFiniteType k M.C.functionField := essFiniteType_functionField M.toBase
  haveI : Algebra.EssFiniteType k L :=
    Algebra.EssFiniteType.of_surjective M.ffAlgEquiv.symm.toAlgHom M.ffAlgEquiv.symm.surjective
  obtain ⟨t,ht,hfd,_⟩ := IsCurveOver.exists_separating_transcendental (K:=k) (F:=L)
  letI := hfd
  have hc := constantsAreBase_of_isAlgClosed_of_transcendental t ht
  have hg : g=genusFF k Y.functionField :=
    (eq_genusFF_of_forall_ell_sub_ell_eq hc hRR).trans
      ((genusFF_eq_of_algEquiv M.ffAlgEquiv).trans (genusFF_eq_of_algEquiv φ.symm))
  exact (field_H1_eq_genusFF F V).trans hg.symm

/-- Actual unit Euler characteristic, using canonical structural-map H0=1. -/
theorem field_unit_euler_eq (F : SmoothProperCurve.FiniteMapData π ε)
    (V : Y.TwoAffineOpenCover) :
    letI := (baseToFunctionField π).toAlgebra
    (Module.finrank k (V.sectionsOf π (𝟙_ Y.Modules)).H0:ℤ)-
      Module.finrank k (V.sectionsOf π (𝟙_ Y.Modules)).H1=1-genusFF k Y.functionField := by
  have h0 : Module.finrank k (V.sectionsOf π (𝟙_ Y.Modules)).H0=1 :=
    FMDUnitCohomology.field_finrank_H0_unit_eq_one F V
  rw [h0,field_H1_eq_genusFF F V]
  rfl
end FourCorner.FMDUnitH1
