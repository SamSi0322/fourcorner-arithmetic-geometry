import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_exists_sumMap
import ThetaCoverClassPortable.Theorems.Thm_CategoryTheory_MorphismProperty_widePullback_base
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_IsSeparated_of_comp_of_universallyClosed_of_surjective
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_LocallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_isProper

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f] [SmoothOfRelativeDimension 1 f]
    [IsLocallyNoetherian S] {r : ℕ} {Y : Scheme.{u}} {y : Y ⟶ S}
    {Duniv : RelEffCartierDiv f r y} (hU : Duniv.IsUniversal) : IsProper y := by
  obtain ⟨σ, hσ, -, hfin, hflat, -, hsurj, -⟩ := hU.exists_sumMap
  have hp : IsProper (fibrePowOver.toBase f r) :=
    MorphismProperty.widePullback_base (P := @IsProper) (fun _ : Fin r ↦ 𝒞) (fun _ ↦ f)
      fun _ ↦ inferInstance
  have : IsProper (σ ≫ y) := by rw [hσ]; exact hp
  exact @IsProper.mk _ _ y (IsSeparated.of_comp_of_universallyClosed_of_surjective σ y)
    (UniversallyClosed.of_comp_surjective σ y)
    (LocallyOfFiniteType.of_comp_of_isFinite_of_flat_of_surjective σ y)
