import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_surjective_app_of_shortExact_of_locallyTrivial
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_surjective_app_sup_of_shortExact_of_locallyTrivial

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_surjective_app_sup_of_shortExact_of_locallyTrivial.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.Modules.pullback Scheme IsAffineOpen Scheme.Modules Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero Scheme.Modules.surjective_app_of_shortExact_of_locallyTrivial"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules.pullback Hom Γ Hom.naturality Modules Opens PresheafOfModules Modules.exists_app_eq_of_exact_of_app_eq_zero Modules.surjective_app_of_shortExact_of_locallyTrivial"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback presheaf Hom isSheaf exists_app_eq_of_exact_of_app_eq_zero surjective_app_of_shortExact_of_locallyTrivial"
namespace SupSurj
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

theorem app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : U ⟶ V) (m : Γ(M, V)) :
    N.presheaf.map i.op (φ.app V m) = φ.app U (M.presheaf.map i.op m) := by
  have h := PresheafOfModules.Hom.naturality φ.val i.op
  have h' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) m
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h'
  exact h'.symm

theorem comp_app_apply {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) (U : X.Opens) (m : Γ(M, U)) :
    (φ ≫ ψ).app U m = ψ.app U (φ.app U m) := rfl

theorem zero_app_apply {M N : X.Modules} (U : X.Opens) (m : Γ(M, U)) : (0 : M ⟶ N).app U m = 0 := rfl

theorem fg_app_apply (S : ShortComplex X.Modules) (U : X.Opens) (m : Γ(S.X₁, U)) :
    S.g.app U (S.f.app U m) = 0 := by
  rw [← comp_app_apply, S.zero, zero_app_apply]

noncomputable abbrev rM (M : X.Modules) {V W : X.Opens} (h : V ≤ W) : Γ(M, W) → Γ(M, V) :=
  fun y => M.presheaf.map (homOfLE h).op y

theorem rM_rM (M : X.Modules) {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (y : Γ(M, V₁)) :
    rM M h₃₂ (rM M h₂₁ y) = rM M (h₃₂.trans h₂₁) y := by
  show (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) y = _
  rw [← Functor.map_comp]; rfl

theorem map_eq_rM (M : X.Modules) {V W : X.Opens} (i : V ⟶ W) (y : Γ(M, W)) :
    M.presheaf.map i.op y = rM M (leOfHom i) y := by
  rw [Subsingleton.elim i (homOfLE (leOfHom i))]

theorem rM_app {M N : X.Modules} (φ : M ⟶ N) {V W : X.Opens} (h : V ≤ W) (m : Γ(M, W)) :
    rM N h (φ.app W m) = φ.app V (rM M h m) :=
  app_naturality φ (homOfLE h) m

theorem rM_sub (M : X.Modules) {V W : X.Opens} (h : V ≤ W) (y z : Γ(M, W)) :
    rM M h (y - z) = rM M h y - rM M h z := map_sub _ _ _

noncomputable def F (M : X.Modules) : TopCat.Sheaf Ab X.carrier := ⟨M.presheaf, M.isSheaf⟩

def U2 (W₀ W₁ : X.Opens) : Bool → X.Opens := fun b => cond b W₁ W₀

theorem iSup_U2 (W₀ W₁ : X.Opens) : iSup (U2 W₀ W₁) = W₀ ⊔ W₁ := by
  apply le_antisymm
  · exact iSup_le fun b => by cases b <;> simp [U2]
  · exact sup_le (le_iSup (U2 W₀ W₁) false) (le_iSup (U2 W₀ W₁) true)

theorem exists_glue (M : X.Modules) (W₀ W₁ : X.Opens) (p0 : Γ(M, W₀)) (p1 : Γ(M, W₁))
    (hp : rM M (inf_le_left : W₀ ⊓ W₁ ≤ W₀) p0 = rM M (inf_le_right : W₀ ⊓ W₁ ≤ W₁) p1) :
    ∃ s : Γ(M, W₀ ⊔ W₁), rM M (le_sup_left : W₀ ≤ W₀ ⊔ W₁) s = p0 ∧ rM M (le_sup_right : W₁ ≤ W₀ ⊔ W₁) s = p1 := by
  let sf : ∀ b : Bool, (F M).1.obj (op (U2 W₀ W₁ b)) := fun b => match b with
    | false => p0
    | true => p1
  have hcomp : TopCat.Presheaf.IsCompatible (F M).1 (U2 W₀ W₁) sf := by
    intro i j
    show M.presheaf.map _ (sf i) = M.presheaf.map _ (sf j)
    rw [map_eq_rM, map_eq_rM]
    cases i <;> cases j
    · rfl
    · exact hp
    · show rM M (inf_le_left : W₁ ⊓ W₀ ≤ W₁) p1 = rM M (inf_le_right : W₁ ⊓ W₀ ≤ W₀) p0
      have h10 : W₁ ⊓ W₀ ≤ W₀ ⊓ W₁ := le_of_eq (inf_comm _ _)
      rw [← rM_rM M inf_le_right h10, ← rM_rM M inf_le_left h10, hp]
    · rfl
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F M) (U2 W₀ W₁) (W₀ ⊔ W₁)
    (fun b => homOfLE (by cases b <;> simp [U2])) (iSup_U2 W₀ W₁).ge sf hcomp
  exact ⟨s, hs false, hs true⟩

theorem eq_of_rM_eq (M : X.Modules) (W₀ W₁ : X.Opens) (s t : Γ(M, W₀ ⊔ W₁))
    (h0 : rM M (le_sup_left : W₀ ≤ W₀ ⊔ W₁) s = rM M (le_sup_left : W₀ ≤ W₀ ⊔ W₁) t)
    (h1 : rM M (le_sup_right : W₁ ≤ W₀ ⊔ W₁) s = rM M (le_sup_right : W₁ ≤ W₀ ⊔ W₁) t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq₂ (F M) (homOfLE (le_sup_left : W₀ ≤ W₀ ⊔ W₁))
    (homOfLE (le_sup_right : W₁ ≤ W₀ ⊔ W₁)) le_rfl s t h0 h1

theorem surjective_app_sup (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (htriv : ∀ p : X, ∃ W : X.Opens, p ∈ W ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj S.X₁ ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))
    (W₀ W₁ : X.Opens) (h₀ : IsAffineOpen W₀) (h₁ : IsAffineOpen W₁)
    (hH1 : ∀ δ : Γ(S.X₁, W₀ ⊓ W₁), ∃ (a : Γ(S.X₁, W₀)) (b : Γ(S.X₁, W₁)),
      δ = S.X₁.presheaf.map (homOfLE inf_le_left).op a - S.X₁.presheaf.map (homOfLE inf_le_right).op b) :
    Function.Surjective (S.g.app (W₀ ⊔ W₁)) := by
  haveI := hS.mono_f
  intro s

  obtain ⟨m₀, hm₀⟩ := Scheme.Modules.surjective_app_of_shortExact_of_locallyTrivial S hS htriv W₀ h₀
    (rM S.X₃ le_sup_left s)
  obtain ⟨m₁, hm₁⟩ := Scheme.Modules.surjective_app_of_shortExact_of_locallyTrivial S hS htriv W₁ h₁
    (rM S.X₃ le_sup_right s)

  have hd : S.g.app (W₀ ⊓ W₁)
      (rM S.X₂ (inf_le_left : W₀ ⊓ W₁ ≤ W₀) m₀ - rM S.X₂ (inf_le_right : W₀ ⊓ W₁ ≤ W₁) m₁) = 0 := by
    rw [map_sub, ← rM_app, ← rM_app, hm₀, hm₁, rM_rM, rM_rM, sub_self]
  obtain ⟨δ, hδ⟩ := Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero S hS.exact (W₀ ⊓ W₁) _ hd
  obtain ⟨a, b, hab⟩ := hH1 δ
  change δ = rM S.X₁ inf_le_left a - rM S.X₁ inf_le_right b at hab

  have hagree : rM S.X₂ (inf_le_left : W₀ ⊓ W₁ ≤ W₀) (m₀ - S.f.app W₀ a)
      = rM S.X₂ (inf_le_right : W₀ ⊓ W₁ ≤ W₁) (m₁ - S.f.app W₁ b) := by
    rw [rM_sub, rM_sub, rM_app, rM_app]
    have key : S.f.app (W₀ ⊓ W₁) (rM S.X₁ inf_le_left a) - S.f.app (W₀ ⊓ W₁) (rM S.X₁ inf_le_right b)
        = rM S.X₂ inf_le_left m₀ - rM S.X₂ inf_le_right m₁ := by
      rw [← map_sub, ← hab, hδ]
    rw [sub_eq_sub_iff_sub_eq_sub, ← key]
  obtain ⟨m, hm0, hm1⟩ := exists_glue S.X₂ W₀ W₁ _ _ hagree
  refine ⟨m, eq_of_rM_eq S.X₃ W₀ W₁ _ _ ?_ ?_⟩
  · rw [rM_app, hm0, map_sub, hm₀, fg_app_apply, sub_zero]
  · rw [rM_app, hm1, map_sub, hm₁, fg_app_apply, sub_zero]

end AlgebraicGeometry.Scheme.Modules.SupSurj

theorem solution
    {X : Scheme.{u}} (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (htriv : ∀ p : X, ∃ W : X.Opens, p ∈ W ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj S.X₁ ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))
    (W₀ W₁ : X.Opens) (h₀ : IsAffineOpen W₀) (h₁ : IsAffineOpen W₁)
    (hH1 : ∀ δ : Γ(S.X₁, W₀ ⊓ W₁), ∃ (a : Γ(S.X₁, W₀)) (b : Γ(S.X₁, W₁)),
      δ = S.X₁.presheaf.map (homOfLE inf_le_left).op a - S.X₁.presheaf.map (homOfLE inf_le_right).op b) :
    Function.Surjective (S.g.app (W₀ ⊔ W₁)) :=
  AlgebraicGeometry.Scheme.Modules.SupSurj.surjective_app_sup S hS htriv W₀ W₁ h₀ h₁ hH1
