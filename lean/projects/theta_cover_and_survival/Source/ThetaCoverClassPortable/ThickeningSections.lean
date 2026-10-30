import ThetaCoverClassPortable.FiniteThickeningRank
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_epi_unit_app_tensor_invModule_pow_and_exists_shortExact
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
universe u
namespace AlgebraicGeometry

/-- Actual section-power thickening: its restricted line bundle has exactly n
sections over the field, and the actual adjunction unit is injective on global
sections precisely when the lower twist has no global sections. -/
theorem finrank_sections_pushforward_thickening_and_injective_unit_app_iff
    {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] [SmoothOfRelativeDimension 1 x]
    (σ : Spec (CommRingCat.of k) ⟶ X) (hσ : σ ≫ x = 𝟙 _)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (r n d : ℕ) (hd : d + n = r) :
    (letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x
      ((Scheme.Modules.pushforward (σ.ker ^ n).subschemeι).obj
        ((Scheme.Modules.pullback (σ.ker ^ n).subschemeι).obj (L ⊗ (σ.ker ^ r).invModule))) ⊤
     Module.Finite k Γ((Scheme.Modules.pushforward (σ.ker ^ n).subschemeι).obj
        ((Scheme.Modules.pullback (σ.ker ^ n).subschemeι).obj (L ⊗ (σ.ker ^ r).invModule)), ⊤) ∧
     Module.finrank k Γ((Scheme.Modules.pushforward (σ.ker ^ n).subschemeι).obj
        ((Scheme.Modules.pullback (σ.ker ^ n).subschemeι).obj (L ⊗ (σ.ker ^ r).invModule)), ⊤) = n) ∧
    (Function.Injective (((Scheme.Modules.pullbackPushforwardAdjunction (σ.ker ^ n).subschemeι).unit.app
      (L ⊗ (σ.ker ^ r).invModule)).app ⊤) ↔ Subsingleton Γ(L ⊗ (σ.ker ^ d).invModule, ⊤)) := by
  have hI : σ.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := x) σ hσ
  have hG : Scheme.Modules.IsInvertible (L ⊗ (σ.ker ^ r).invModule) :=
    hL.tensor (hI.pow r).isInvertible_invModule
  obtain ⟨hfin, hrank, -, -⟩ :=
    Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id σ hσ n
  have hN := hG.pullback (σ.ker ^ n).subschemeι
  obtain ⟨hfinite, hr⟩ := FourCorner.ThetaThickeningSections.finite_rank_global_sections x
    (σ.ker ^ n).subschemeι hfin _ hN
  refine ⟨⟨hfinite, (hr (IsLocalRing.closedPoint k)).trans (hrank _)⟩, ?_⟩
  obtain ⟨-, ι, w, hS⟩ := Scheme.IdealSheafData.IsInvertible.epi_unit_app_tensor_invModule_pow_and_exists_shortExact σ.ker hI L hL r n d hd
  let S : ShortComplex X.Modules := ShortComplex.mk ι _ w
  have hS' : S.ShortExact := hS
  haveI : Mono ι := hS'.mono_f
  have hf := FourCorner.FieldZeroDivisor.Euler.Ws31ChiA.injective_app_of_mono ι (⊤ : X.Opens)
  have he := FourCorner.FieldZeroDivisor.Euler.Ws31ChiA.exact_app S hS'.exact (⊤ : X.Opens)
  constructor
  · intro hg
    refine ⟨fun a b => hf (hg ?_)⟩
    exact ((he (ι.app ⊤ a)).mpr ⟨a, rfl⟩).trans ((he (ι.app ⊤ b)).mpr ⟨b, rfl⟩).symm
  · intro hs
    haveI := hs
    intro a b hab
    have hz : S.g.app ⊤ (a - b) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hab
    obtain ⟨v, hv⟩ := (he (a - b)).mp hz
    have hv0 : ι.app ⊤ v = 0 := by rw [Subsingleton.elim v 0, map_zero]
    exact sub_eq_zero.mp (hv.symm.trans hv0)

#print axioms finrank_sections_pushforward_thickening_and_injective_unit_app_iff
end AlgebraicGeometry
