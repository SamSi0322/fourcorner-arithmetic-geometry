import ThetaCoverClassPortable.P2M.Sol.S_Algebra_exists_polynomial_isUnit_aeval_imp_etale_levelSet
import ThetaCoverClassPortable.Theorems.Thm_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits NeronModelInfra
open scoped TensorProduct
namespace AlgebraicGeometry.SmoothProperCurve.FiniteMapData
variable {F : Type u} [Field F] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of F)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of F))) c}
  (𝔉 : FiniteMapData c ε)

theorem levelSetsGenericallyEtale_of_nonempty [IsIntegral C] [Nonempty 𝔉.U]
    (hunit : IsUnit (𝔉.m : F)) : 𝔉.LevelSetsGenericallyEtale := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
  let A := Γ(C, 𝔉.U)
  letI : Algebra (Polynomial F) A := (Polynomial.aeval 𝔉.f).toRingHom.toAlgebra
  haveI : IsScalarTower F (Polynomial F) A :=
    IsScalarTower.of_algebraMap_eq (fun x => (Polynomial.aeval 𝔉.f).commutes x |>.symm)
  haveI : Module.Finite (Polynomial F) A := 𝔉.finite_f
  haveI : Algebra.FiniteType (Polynomial F) A := inferInstance
  haveI : Algebra.FiniteType F A := Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType F (Polynomial F)) inferInstance
  haveI : Algebra.FinitePresentation F A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let e : F ≃ₐ[F] IsLocalRing.ResidueField F :=
    AlgEquiv.ofBijective (Algebra.ofId F (IsLocalRing.ResidueField F))
      ⟨(algebraMap F (IsLocalRing.ResidueField F)).injective, IsLocalRing.residue_surjective⟩
  let E : IsLocalRing.ResidueField F ⊗[F] A ≃ₐ[F] A :=
    (Algebra.TensorProduct.congr e.symm (AlgEquiv.refl : A ≃ₐ[F] A)).trans
      (Algebra.TensorProduct.lid F A)
  haveI : IsDomain A := inferInstance
  haveI : IsDomain (IsLocalRing.ResidueField F ⊗[F] A) := MulEquiv.isDomain A E.toMulEquiv
  exact P2MW.S_Algebra_exists_polynomial_isUnit_aeval_imp_etale_levelSet.solution
    F A 𝔉.f 𝔉.m hunit 𝔉.levelSet_free

noncomputable abbrev LevelSet (s : F) : Type u :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
  F ⊗[F] Γ(C, 𝔉.U) ⧸ Ideal.span {(1 : F) ⊗ₜ[F] 𝔉.f - s ⊗ₜ[F] (1 : Γ(C, 𝔉.U))}

theorem nonempty_U_of_isUnit (hunit : IsUnit (𝔉.m : F)) : Nonempty 𝔉.U := by
  classical
  by_contra h
  have hU : 𝔉.U = ⊥ := by
    ext x
    constructor
    · intro hx; exact False.elim (h ⟨⟨x, hx⟩⟩)
    · intro hx; exact False.elim hx
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
  haveI : Subsingleton Γ(C, 𝔉.U) := by rw [hU]; infer_instance
  haveI : Subsingleton (𝔉.LevelSet 0) := inferInstance
  have hzero : Module.finrank F (𝔉.LevelSet 0) = 0 := Module.finrank_zero_of_subsingleton
  have hrank : Module.finrank F (𝔉.LevelSet 0) = 𝔉.m := 𝔉.levelSet_finrank_eq F 0
  have hm : 𝔉.m = 0 := hrank.symm.trans hzero
  rw [hm, Nat.cast_zero] at hunit
  exact not_isUnit_zero hunit

theorem levelSetsGenericallyEtale_of_isUnit [IsIntegral C]
    (hunit : IsUnit (𝔉.m : F)) : 𝔉.LevelSetsGenericallyEtale := by
  haveI : Nonempty 𝔉.U := 𝔉.nonempty_U_of_isUnit hunit
  exact 𝔉.levelSetsGenericallyEtale_of_nonempty hunit

theorem exists_finiteEtale_splitLevelSet [Infinite F] [IsIntegral C]
    (hunit : IsUnit (𝔉.m : F)) :
    ∃ s : F, Module.Finite F (𝔉.LevelSet s) ∧ Module.Free F (𝔉.LevelSet s) ∧
      Module.finrank F (𝔉.LevelSet s) = 𝔉.m ∧ Algebra.Etale F (𝔉.LevelSet s) ∧
      ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra F R') (_ : Module.Finite F R')
        (_ : Algebra.Etale F R') (_ : Module.FaithfullyFlat F R') (_ : IsNoetherianRing R')
        (_ : _root_.IsReduced R'),
        Nonempty ((R' ⊗[F] 𝔉.LevelSet s) ≃ₐ[R'] (Fin 𝔉.m → R')) := by
  classical
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
  obtain ⟨D, ⟨i, hi⟩, hD⟩ := 𝔉.levelSetsGenericallyEtale_of_isUnit hunit
  have hDne : D ≠ 0 := by
    intro h
    rw [h, Polynomial.coeff_zero] at hi
    exact not_isUnit_zero hi
  obtain ⟨s, hs⟩ : ∃ s : F, D.eval s ≠ 0 := by
    by_contra h
    push Not at h
    exact hDne (Polynomial.zero_of_eval_zero D h)
  have hunitD : IsUnit (Polynomial.aeval s D) := by
    simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using isUnit_iff_ne_zero.mpr hs
  obtain ⟨hfinite, hfree, hrank⟩ := 𝔉.levelSet_free F s
  change Module.finrank F (𝔉.LevelSet s) = 𝔉.m at hrank
  have het := hD F s hunitD
  haveI : Module.Finite F (𝔉.LevelSet s) := hfinite
  haveI : Algebra.Etale F (𝔉.LevelSet s) := het
  obtain ⟨R', _, _, _, _, _, _, ⟨e⟩⟩ :=
    Algebra.Etale.exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi F (𝔉.LevelSet s)
  haveI : Algebra.EssFiniteType F R' := Algebra.EssFiniteType.of_finiteType F R'
  haveI : _root_.IsReduced R' := Algebra.FormallyUnramified.isReduced_of_field F R'
  refine ⟨s, hfinite, hfree, hrank, het, R', inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [hrank] at e
  exact ⟨e⟩

end AlgebraicGeometry.SmoothProperCurve.FiniteMapData
