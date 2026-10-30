import ThetaCoverClassPortable.AffineBaseChangeSections
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
namespace FourCorner.FiniteMapBaseChange
open AlgebraicGeometry.SmoothProperCurve
variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  (c : C ⟶ Spec (.of R)) (T : Type u) [CommRing T] [Algebra R T]

abbrev fst : pullback c (specMap R T) ⟶ C := pullback.fst c (specMap R T)
abbrev snd : pullback c (specMap R T) ⟶ Spec (.of T) := pullback.snd c (specMap R T)

variable (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)

theorem section_isPullback :
    IsPullback (specMap R T) (sectionBaseChange T ε).1 ε.1 (fst c T) := by
  have houter : IsPullback (specMap R T) ((sectionBaseChange T ε).1 ≫ snd c T)
      (ε.1 ≫ c) (specMap R T) := by
    rw [(sectionBaseChange T ε).2, ε.2]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  exact houter.of_bot (sectionBaseChange_coe_fst T ε).symm
    (IsPullback.of_hasPullback c (specMap R T))

theorem section_range : Set.range (sectionBaseChange T ε).1 =
    (fst c T) ⁻¹' Set.range ε.1 := by
  let h := section_isPullback c T ε
  have he : Function.Surjective h.isoPullback.hom := by
    intro x
    refine ⟨h.isoPullback.inv x, ?_⟩
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  rw [← h.isoPullback_hom_snd]
  change Set.range ((pullback.snd ε.1 (fst c T) : _ → _) ∘ (h.isoPullback.hom : _ → _)) = _
  rw [Set.range_comp, Set.range_eq_univ.mpr he, Set.image_univ,
    Scheme.Pullback.range_snd]

variable (𝔉 : SmoothProperCurve.FiniteMapData c ε)

def U := (fst c T) ⁻¹ᵁ 𝔉.U
def V := (fst c T) ⁻¹ᵁ 𝔉.V
def f : Γ(pullback c (specMap R T), U c T ε 𝔉) := ((fst c T).app 𝔉.U).hom 𝔉.f
def g : Γ(pullback c (specMap R T), V c T ε 𝔉) := ((fst c T).app 𝔉.V).hom 𝔉.g

theorem isAffineOpen_U : IsAffineOpen (U c T ε 𝔉) := by
  haveI := Scheme.TwoAffineOpenCover.isAffineHom_fst c T
  exact 𝔉.isAffineOpen_U.preimage _
theorem isAffineOpen_V : IsAffineOpen (V c T ε 𝔉) := by
  haveI := Scheme.TwoAffineOpenCover.isAffineHom_fst c T
  exact 𝔉.isAffineOpen_V.preimage _
theorem sup_eq_top : U c T ε 𝔉 ⊔ V c T ε 𝔉 = ⊤ := by
  rw [U, V, ← Scheme.Hom.preimage_sup, 𝔉.sup_eq_top]
  rfl

theorem mem_U_iff (x : ↑(pullback c (specMap R T))) :
    x ∈ U c T ε 𝔉 ↔ x ∉ Set.range (sectionBaseChange T ε).1 := by
  rw [section_range]
  exact 𝔉.mem_U_iff _

theorem inf_eq_basicOpen : U c T ε 𝔉 ⊓ V c T ε 𝔉 =
    (pullback c (specMap R T)).basicOpen (f c T ε 𝔉) := by
  change (fst c T) ⁻¹ᵁ 𝔉.U ⊓ (fst c T) ⁻¹ᵁ 𝔉.V = _
  rw [← Scheme.Hom.preimage_inf, 𝔉.inf_eq_basicOpen,
    Scheme.preimage_basicOpen]
  rfl

theorem inf_eq_basicOpen_g : U c T ε 𝔉 ⊓ V c T ε 𝔉 =
    (pullback c (specMap R T)).basicOpen (g c T ε 𝔉) := by
  change (fst c T) ⁻¹ᵁ 𝔉.U ⊓ (fst c T) ⁻¹ᵁ 𝔉.V = _
  rw [← Scheme.Hom.preimage_inf, 𝔉.inf_eq_basicOpen_g,
    Scheme.preimage_basicOpen]
  rfl

theorem res_f_mul_res_g :
    ((pullback c (specMap R T)).presheaf.map (homOfLE (inf_le_left : U c T ε 𝔉 ⊓ V c T ε 𝔉 ≤ U c T ε 𝔉)).op).hom (f c T ε 𝔉) *
    ((pullback c (specMap R T)).presheaf.map (homOfLE (inf_le_right : U c T ε 𝔉 ⊓ V c T ε 𝔉 ≤ V c T ε 𝔉)).op).hom (g c T ε 𝔉) = 1 := by
  have h := congrArg (((fst c T).app (𝔉.U ⊓ 𝔉.V)).hom) 𝔉.res_f_mul_res_g
  rw [map_mul, map_one] at h
  have hleft := (fst c T).naturality (homOfLE (inf_le_left : 𝔉.U ⊓ 𝔉.V ≤ 𝔉.U)).op
  have hright := (fst c T).naturality (homOfLE (inf_le_right : 𝔉.U ⊓ 𝔉.V ≤ 𝔉.V)).op
  have hl := congrArg (fun k => k.hom 𝔉.f) hleft
  have hr := congrArg (fun k => k.hom 𝔉.g) hright
  simp only [CommRingCat.comp_apply] at hl hr
  rw [hl, hr] at h
  exact h
end FourCorner.FiniteMapBaseChange
