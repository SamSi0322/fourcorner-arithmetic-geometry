import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Affine

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TensorProduct
open AlgebraicGeometry.Scheme.TwoAffineOpenCover
namespace FourCorner.AffineSectionsModel
open P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf.AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable (R : Type u) [CommRing R] {X : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of R)) (A : Type u) [CommRing A] [Algebra R A]

abbrev XA := pullback c (specMap R A)
abbrev p : XA R c A ⟶ X := pullback.fst c (specMap R A)
abbrev q : XA R c A ⟶ Spec (CommRingCat.of A) := pullback.snd c (specMap R A)

def forward (U : X.Opens) (hU : IsAffineOpen U) :
    letI := algebraOfHom c U
    letI := algebraOfHom (p R c A ≫ c) ((p R c A) ⁻¹ᵁ U)
    Γ(X,U) ⊗[R] A ≃ₐ[R] Γ(XA R c A, (p R c A) ⁻¹ᵁ U) := by
  letI := algebraOfHom c U
  letI := algebraOfHom (p R c A ≫ c) ((p R c A) ⁻¹ᵁ U)
  refine AlgEquiv.ofRingEquiv (f := AffineBaseChange.sigma c A U hU) (fun r => ?_)
  change AffineBaseChange.sigma c A U hU ((algebraMap R Γ(X,U) r) ⊗ₜ[R] (1 : A)) = _
  rw [AffineBaseChange.sigma_tmul_one]
  simp only [algebraMap_algebraOfHom]
  change ((p R c A).app U).hom (((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ U le_top).hom r) =
    ((Scheme.ΓSpecIso (.of R)).inv ≫ (p R c A ≫ c).appLE ⊤ ((p R c A) ⁻¹ᵁ U) le_top).hom r
  rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE]

end FourCorner.AffineSectionsModel

open FourCorner.AffineSectionsModel
namespace AlgebraicGeometry

theorem exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen
    (R : Type u) [CommRing R] {X : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of R)) (A : Type u) [CommRing A] [Algebra R A] :
    letI instK : ∀ U : X.Opens, Algebra R Γ(X,U) := fun U => algebraOfHom c U
    letI instKA : ∀ W : (XA R c A).Opens, Algebra R Γ(XA R c A,W) :=
      fun W => algebraOfHom (p R c A ≫ c) W
    ∃ (ε : ∀ (U : X.Opens) (_ : IsAffineOpen U),
        Γ(XA R c A, (p R c A) ⁻¹ᵁ U) ≃ₐ[R] Γ(X,U) ⊗[R] A),
      (∀ (U : X.Opens) (_ : IsAffineOpen U), IsAffineOpen ((p R c A) ⁻¹ᵁ U)) ∧
      (∀ (U : X.Opens) (hU : IsAffineOpen U) (s : Γ(X,U)),
        ε U hU (((p R c A).app U).hom s) = s ⊗ₜ[R] (1 : A)) ∧
      (∀ (U : X.Opens) (hU : IsAffineOpen U) (a : A),
        ε U hU (((q R c A).appLE ⊤ ((p R c A) ⁻¹ᵁ U) le_top).hom
          ((Scheme.ΓSpecIso (.of A)).inv.hom a)) = (1 : Γ(X,U)) ⊗ₜ[R] a) ∧
      (∀ (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U)
          (s : Γ(XA R c A, (p R c A) ⁻¹ᵁ U)),
        Algebra.TensorProduct.map (restrictAlgHom c hVU) (AlgHom.id R A) (ε U hU s) =
          ε V hV (((XA R c A).presheaf.map
            (homOfLE ((p R c A).preimage_mono hVU)).op).hom s)) := by
  letI instK : ∀ U : X.Opens, Algebra R Γ(X,U) := fun U => algebraOfHom c U
  letI instKA : ∀ W : (XA R c A).Opens, Algebra R Γ(XA R c A,W) :=
    fun W => algebraOfHom (p R c A ≫ c) W
  refine ⟨fun U hU => (forward R c A U hU).symm, ?_, ?_, ?_, ?_⟩
  · intro U hU
    haveI : IsAffineHom (specMap R A) := isAffineHom_of_isAffine _
    haveI : IsAffineHom (p R c A) :=
      MorphismProperty.pullback_fst (P := @IsAffineHom) c (specMap R A) inferInstance
    exact hU.preimage (p R c A)
  · intro U hU s
    apply (forward R c A U hU).injective
    rw [AlgEquiv.apply_symm_apply]
    exact (P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.sigma_tmul_one c A U hU s).symm
  · intro U hU a
    apply (forward R c A U hU).injective
    rw [AlgEquiv.apply_symm_apply]
    change _ = P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.sigma c A U hU (1 ⊗ₜ[R] a)
    rw [P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.sigma_one_tmul]
    rfl
  · intro U V hU hV hVU s
    obtain ⟨x,rfl⟩ := (forward R c A U hU).surjective s
    apply (forward R c A V hV).injective
    rw [AlgEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b =>
      have hsplit : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : A)) * ((1 : Γ(X,U)) ⊗ₜ[R] b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hsplit, map_mul, map_mul, map_mul, map_mul]
      congr 1
      · change _ = _
        simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
        change forward R c A V hV ((restrictAlgHom c hVU a) ⊗ₜ[R] 1) =
          (((XA R c A).presheaf.map (homOfLE ((p R c A).preimage_mono hVU)).op).hom
            (forward R c A U hU (a ⊗ₜ[R] 1)))
        simp only [forward, AlgEquiv.ofRingEquiv_apply]
        rw [P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.sigma_tmul_one,
          P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.sigma_tmul_one]
        exact ConcreteCategory.congr_hom ((p R c A).naturality (homOfLE hVU).op) a
      · simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
        simp only [forward, AlgEquiv.ofRingEquiv_apply]
        rw [P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.sigma_one_tmul,
          P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.sigma_one_tmul]
        change ((XA R c A).presheaf.map _).hom _ =
          ((XA R c A).presheaf.map _).hom (((XA R c A).presheaf.map _).hom _)
        conv_rhs => rw [← CommRingCat.comp_apply, ← Functor.map_comp]
        rfl

end AlgebraicGeometry
