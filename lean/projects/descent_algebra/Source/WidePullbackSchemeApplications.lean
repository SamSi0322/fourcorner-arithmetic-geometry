import Theorems.Thm_CategoryTheory_MorphismProperty_widePullback_base
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Affine

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FourCorner.FiniteWidePullback

/-- The exact native scheme fibre-power map used by the divisor callers. -/
theorem scheme_fibre_power (P : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) (hf : P f) :
    P (WidePullback.base (fun _ : Fin n => f)) :=
  MorphismProperty.widePullback_base (P:=P) (fun _ : Fin n => X)
    (fun _ => f) (fun _ => hf)

theorem proper_scheme_fibre_power {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] (n : ℕ) : IsProper (WidePullback.base (fun _ : Fin n => f)) :=
  scheme_fibre_power (@IsProper) f n inferInstance

theorem affine_scheme_fibre_power {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffineHom f] (n : ℕ) : IsAffineHom (WidePullback.base (fun _ : Fin n => f)) :=
  scheme_fibre_power (@IsAffineHom) f n inferInstance

#print axioms scheme_fibre_power
#print axioms proper_scheme_fibre_power
#print axioms affine_scheme_fibre_power
end FourCorner.FiniteWidePullback
