import ThetaCoverClassPortable.FieldZeroEuler
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace FourCorner.ThetaThickeningSections
open P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite.C3Aux
/-- Global form of the accepted finite zero-scheme section calculation, with the actual pushforward scalar action. -/
theorem finite_rank_global_sections
    {k : Type u} [Field k] {Z X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (i : Z ⟶ X) (hZ : IsFinite (i ≫ x))
    (N : Z.Modules) (hN : Scheme.Modules.IsInvertible N) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x ((Scheme.Modules.pushforward i).obj N) ⊤
    Module.Finite k Γ((Scheme.Modules.pushforward i).obj N, ⊤) ∧
      ∀ t : Spec (CommRingCat.of k),
        Module.finrank k Γ((Scheme.Modules.pushforward i).obj N, ⊤) = (i ≫ x).finrank t := by
  classical
  haveI := hZ
  obtain ⟨hZaff, hfinTop⟩ := (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp hZ
  haveI : IsAffine Z := hZaff

  let φ : CommRingCat.of k ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ x).appTop
  have hφfin : φ.hom.Finite :=
    RingHom.Finite.comp hfinTop
      (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).surjective)
  have hφflat : φ.hom.Flat := by
    letI := φ.hom.toAlgebra
    exact (inferInstance : Module.Flat k Γ(Z, ⊤))
  obtain ⟨hZfin, hZdisc⟩ := finite_and_discrete_of_finite φ.hom hφfin

  let P : X.Modules := (Scheme.Modules.pushforward i).obj N

  have hdeg : ∀ t : Spec (CommRingCat.of k),
      (i ≫ x).finrank t = (letI := φ.hom.toAlgebra; Module.finrank k Γ(Z, ⊤)) := by
    intro t
    have hfac : i ≫ x = Z.isoSpec.hom ≫ Spec.map φ := by
      rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, Scheme.isoSpec_hom_naturality_assoc,
        Iso.hom_inv_id, Category.comp_id]
    haveI : IsFinite (Spec.map φ) := (IsFinite.SpecMap_iff φ).2 hφfin
    haveI : Flat (Spec.map φ) := Flat.SpecMap_iff.2 hφflat
    rw [hfac, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_eq_finrank hφfin hφflat]
    letI := φ.hom.toAlgebra
    simp only [RingHom.finrank, Module.rankAtStalk_eq_finrank_of_free]
    rfl

  let ψ₀ : k →+* Γ(Z, ⊤) := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom x ⊤
    exact (i.app ⊤).hom.comp (algebraMap k Γ(X, ⊤))
  have hψ₀ : ψ₀ = φ.hom := by
    refine RingHom.ext fun r => ?_
    change (i.app ⊤).hom ((x.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of k)).inv.hom r)) =
      ((i ≫ x).appTop).hom ((Scheme.ΓSpecIso (.of k)).inv.hom r)
    have h1 : x.appLE ⊤ ⊤ le_top = x.appTop := (Scheme.Hom.app_eq_appLE x).symm
    rw [h1, Scheme.Hom.comp_appTop]
    rfl

  haveI : Fintype Z := Fintype.ofFinite Z
  choose V hzV eV using hN.exists_trivialization
  let pt : Z → Z.Opens := fun z => ⟨{z}, isOpen_discrete _⟩
  let Wz : ∀ z : Z, (V z).toScheme.Opens := fun z => (V z).ι ⁻¹ᵁ (pt z)
  let U : Z → Z.Opens := fun z => (V z).ι ''ᵁ (Wz z)
  have hU : ∀ z, (U z : Set Z) = {z} := by
    intro z
    have h := (V z).ι.image_preimage_eq_opensRange_inf (pt z)
    rw [Scheme.Opens.opensRange_ι] at h
    have h' := congrArg (fun W : Z.Opens => (W : Set Z)) h
    simp only [TopologicalSpace.Opens.coe_inf] at h'
    refine h'.trans ?_
    exact Set.inter_eq_right.2 (Set.singleton_subset_iff.2 (hzV z))
  have hzU : ∀ z, z ∈ U z := fun z => by
    show z ∈ (U z : Set Z)
    rw [hU]
    exact Set.mem_singleton z
  have hcov : (⊤ : Z.Opens) ≤ iSup U := fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hzU z⟩
  have hdisj : ∀ a b, a ≠ b → U a ⊓ U b = ⊥ := by
    intro a b hab
    apply TopologicalSpace.Opens.ext
    simp only [TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_bot, hU]
    exact Set.singleton_inter_eq_empty.2 (by simpa using hab)

  let O : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  letI instN : Module k Γ(N, ⊤) := modK N ⊤ ψ₀
  letI instO : Module k Γ(O, ⊤) := modK O ⊤ ψ₀
  letI instNz : ∀ z, Module k Γ(N, U z) := fun z => modK N (U z) (resHom ψ₀ (U z))
  letI instOz : ∀ z, Module k Γ(O, U z) := fun z => modK O (U z) (resHom ψ₀ (U z))
  let eN := piEquiv N ψ₀ U hcov hdisj
  let eO := piEquiv O ψ₀ U hcov hdisj

  have eτ : ∀ z, Nonempty (Γ(N, U z) ≃ₗ[k] Γ(O, U z)) := by
    intro z
    obtain ⟨τ, hτ⟩ := exists_addEquiv_of_trivial N (V z) (eV z).some (Wz z)
    exact ⟨τ.toLinearEquiv fun r m => hτ (resHom ψ₀ (U z) r) m⟩

  letI : Algebra k Γ(Z, ⊤) := φ.hom.toAlgebra
  haveI : Module.Finite k Γ(Z, ⊤) := hφfin
  let ι₀ : Γ(O, ⊤) ≃ₗ[k] Γ(Z, ⊤) :=
    { toFun := fun s => show Γ(Z, ⊤) from s
      invFun := fun s => show Γ(O, ⊤) from s
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r s => by
        show ψ₀ r * (show Γ(Z, ⊤) from s) = φ.hom r * (show Γ(Z, ⊤) from s)
        rw [hψ₀] }
  haveI : Module.Finite k Γ(O, ⊤) := Module.Finite.equiv ι₀.symm
  haveI hOz : ∀ z, Module.Finite k Γ(O, U z) := fun z =>
    Module.Finite.of_surjective
      ((LinearMap.proj z : (∀ a, Γ(O, U a)) →ₗ[k] Γ(O, U z)).comp eO.toLinearMap)
      ((Function.surjective_eval z).comp eO.surjective)
  haveI hNz : ∀ z, Module.Finite k Γ(N, U z) := fun z => Module.Finite.equiv (eτ z).some.symm
  haveI hNfin : Module.Finite k Γ(N, ⊤) := Module.Finite.equiv eN.symm
  have hrank : Module.finrank k Γ(N, ⊤) = Module.finrank k Γ(Z, ⊤) := by
    rw [eN.finrank_eq, ← ι₀.finrank_eq, eO.finrank_eq, Module.finrank_pi_fintype,
      Module.finrank_pi_fintype]
    exact Finset.sum_congr rfl fun z _ => (eτ z).some.finrank_eq

  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x P ⊤
  haveI hfinP : Module.Finite k Γ(P, ⊤) := hNfin
  exact ⟨hfinP, fun t => hrank.trans (hdeg t).symm⟩

end FourCorner.ThetaThickeningSections
