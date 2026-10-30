import ThetaCoverClassPortable.RigidifiedFFIsoFrame
import ThetaCoverClassPortable.DescentDataPrimeIsoLifting
import ThetaCoverClassPortable.DescentFunctorCoherence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
open CategoryTheory.Pseudofunctor
universe u v
namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry"
noncomputable section
namespace AlgebraicGeometry.RelPicard.DescentAux
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"
open NeronModelInfra
variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
section bridge
variable {c ε}
variable {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
  {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
  (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t)
scoped instance isIso_rawHom (L : (Limits.pullback c t).Modules) : IsIso (rawHom c ψ₁ ψ₂ L) := by
  exact Eq.mp (congrArg (fun f => IsIso f) (transHom₂_eq_rawHom (c := c) ψ₁ ψ₂ L))
    (isIso_transHom₂ (baseChangeSnd c ψ₁) (baseChangeSnd c ψ₂) (chosenPullback c ψ₁ ψ₂) L)

lemma chosenPullback_p_eq : (chosenPullback c ψ₁ ψ₂).p =
    baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂)) := rfl

lemma rigNatIso_eq_sqIso {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) :
    RigData.rigNatIso (c := c) (ε := ε) ψ =
      Scheme.Modules.sqIso (rigSection_baseChangeSnd c ε ψ) := rfl

def legIso {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t)
    (ρ : SchemeHomOver (strMap₁₂ ψ₁ ψ₂) t') (G : ρ.1 ≫ ψ.1 = (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1) (L : (Limits.pullback c t).Modules) :
    (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).obj
        ((Scheme.Modules.pullback (baseChangeSnd c ρ)).obj ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj L)) ≅
      (Scheme.Modules.pullback (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1).obj ((Scheme.Modules.pullback (rigSection c t ε)).obj L) :=
  (RigData.rigNatIso (c := c) (ε := ε) ρ).app ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj L) ≪≫
    (Scheme.Modules.pullback ρ.1).mapIso ((RigData.rigNatIso (c := c) (ε := ε) ψ).app L) ≪≫
      (Scheme.Modules.τ ρ.1 ψ.1 (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1 G).app ((Scheme.Modules.pullback (rigSection c t ε)).obj L)

lemma map_map_eq_legIso_conj {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t)
    (ρ : SchemeHomOver (strMap₁₂ ψ₁ ψ₂) t') (G : ρ.1 ≫ ψ.1 = (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1)
    (A₁ A₂ : RigData c ε t)
    (φ : (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj A₁.L ⟶ (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj A₂.L)
    (hφ : RigData.Compat (A₁.pb ψ) (A₂.pb ψ) φ) :
    (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).map
        ((Scheme.Modules.pullback (baseChangeSnd c ρ)).map φ) =
      (legIso ψ₁ ψ₂ ψ ρ G A₁.L).hom ≫ (Scheme.Modules.pullback (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1).map (A₁.α.hom ≫ A₂.α.inv) ≫
        (legIso ψ₁ ψ₂ ψ ρ G A₂.L).inv := by

  apply FourCorner.DescentFunctorCoherence.map_map_conjugation
    (Scheme.Modules.pullback (baseChangeSnd c ψ))
    (Scheme.Modules.pullback (baseChangeSnd c ρ))
    (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε))
    (Scheme.Modules.pullback (rigSection c t' ε))
    (Scheme.Modules.pullback (rigSection c t ε))
    (Scheme.Modules.pullback ψ.1) (Scheme.Modules.pullback ρ.1)
    (Scheme.Modules.pullback (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1)
    (RigData.rigNatIso (c := c) (ε := ε) ρ)
    (RigData.rigNatIso (c := c) (ε := ε) ψ)
    (Scheme.Modules.τ ρ.1 ψ.1 (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1 G)
    A₁.α A₂.α _ φ
  exact (Iso.eq_comp_inv _).mpr hφ


lemma legIso_eq_sqIso {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (ρ : SchemeHomOver (strMap₁₂ ψ₁ ψ₂) t')
    (G : ρ.1 ≫ ψ.1 = (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1) (L : (Limits.pullback c t).Modules) :
    legIso ψ₁ ψ₂ ψ ρ G L =
      (Scheme.Modules.sqIso (rigSection_baseChangeSnd c ε ρ)).app
        ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj L) ≪≫
      (Scheme.Modules.pullback ρ.1).mapIso
        ((Scheme.Modules.sqIso (rigSection_baseChangeSnd c ε ψ)).app L) ≪≫
      (Scheme.Modules.τ ρ.1 ψ.1 (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1 G).app
        ((Scheme.Modules.pullback (rigSection c t ε)).obj L) := by
  unfold legIso
  rw [rigNatIso_eq_sqIso,rigNatIso_eq_sqIso]
