import ThetaCoverClassPortable.RigidifiedFFIsoFrame
import ThetaCoverClassPortable.DescentDataPrimeIsoLifting
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor Opposite AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux
universe u v
namespace FourCorner.RigidifiedFFIsoNativeLift

/-- The native module types are fixed before the actual family is substituted.
This is the same module pseudofunctor and its same canonical descent datum. -/
theorem solution {S : Scheme.{u}} {ι : Type v} {X : ι → Scheme.{u}}
    (g : ∀i,X i ⟶ S) (sq : ∀i j,ChosenPullback (g i) (g j))
    (sq₃ : ∀i j k,ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (L₁ L₂ : S.Modules)
    (e : ∀i,(Scheme.Modules.pullback (g i)).obj L₁ ≅
      (Scheme.Modules.pullback (g i)).obj L₂)
    (comm : ∀i j,
      (Scheme.Modules.pullback (sq i j).p₁).map (e i).hom ≫
          transHom₂ (g i) (g j) (sq i j) L₂ =
        transHom₂ (g i) (g j) (sq i j) L₁ ≫
          (Scheme.Modules.pullback (sq i j).p₂).map (e j).hom)
    (h₁₂ : Function.Surjective ((MOD.toDescentData g).map (X := L₁) (Y := L₂)))
    (h₂₁ : Function.Surjective ((MOD.toDescentData g).map (X := L₂) (Y := L₁)))
    (h₁₁ : Function.Injective ((MOD.toDescentData g).map (X := L₁) (Y := L₁)))
    (h₂₂ : Function.Injective ((MOD.toDescentData g).map (X := L₂) (Y := L₂))) :
    Nonempty (L₁ ≅ L₂) := by
  apply FourCorner.DescentDataPrimeIsoLifting.nonempty_iso_of_components
    MOD g sq sq₃ L₁ L₂ e ?_ h₁₂ h₂₁ h₁₁ h₂₂
  intro i j
  rw [fromDescentData_toDescentData_hom,fromDescentData_toDescentData_hom]
  exact comm i j

/-- Actual affine faithfully flat descent, with full faithfulness supplied
internally before computed family schemes are substituted. -/
theorem affine {S S' : Scheme.{u}} (q : S' ⟶ S)
    [IsAffineHom q] [Flat q] [Surjective q]
    (sq : ∀i j : Unit,ChosenPullback q q)
    (sq₃ : ∀i j k : Unit,ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (L₁ L₂ : S.Modules) (h₁ : Scheme.Modules.IsInvertible L₁)
    (h₂ : Scheme.Modules.IsInvertible L₂)
    (e : ∀i : Unit,(Scheme.Modules.pullback q).obj L₁ ≅ (Scheme.Modules.pullback q).obj L₂)
    (comm : ∀i j,
      (Scheme.Modules.pullback (sq i j).p₁).map (e i).hom ≫
          transHom₂ q q (sq i j) L₂ =
        transHom₂ q q (sq i j) L₁ ≫
          (Scheme.Modules.pullback (sq i j).p₂).map (e j).hom) :
    Nonempty (L₁ ≅ L₂) := by
  have hbij := fun (M N : S.Modules) (hM : Scheme.Modules.IsInvertible M)
      (hN : Scheme.Modules.IsInvertible N) =>
    AlgebraicGeometry.Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
      q M N hM hN
  exact solution (fun _ : Unit => q) sq sq₃ L₁ L₂ e comm
    (hbij L₁ L₂ h₁ h₂).2 (hbij L₂ L₁ h₂ h₁).2
    (hbij L₁ L₁ h₁ h₁).1 (hbij L₂ L₂ h₂ h₂).1

end FourCorner.RigidifiedFFIsoNativeLift
