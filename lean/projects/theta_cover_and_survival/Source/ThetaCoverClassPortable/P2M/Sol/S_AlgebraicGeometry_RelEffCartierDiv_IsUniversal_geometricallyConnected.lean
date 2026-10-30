import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_exists_sumMap
import ThetaCoverClassPortable.Theorems.Thm_CategoryTheory_MorphismProperty_widePullback_base
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_GeometricallyConnected_of_comp_of_surjective
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_geometricallyConnected

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_geometricallyConnected.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension.smooth SmoothOfRelativeDimension geometrically_iff_of_isClosedUnderIsomorphisms GeometricallyConnected.comp Scheme Smooth UniversallyOpen IsSeparated GeometricallyConnected geometrically RelEffCartierDiv.IsUniversal RelEffCartierDiv fibrePowOver fibrePowOver.toBase RelEffCartierDiv.IsUniversal.exists_sumMap GeometricallyConnected.of_comp_of_surjective"
p2m_open "AlgebraicGeometry"

namespace GeometricallyConnected p2m_export "AlgebraicGeometry.GeometricallyConnected" "comp of_comp_of_surjective" end GeometricallyConnected
p2m_open_scoped "AlgebraicGeometry.GeometricallyConnected" in

theorem GeometricallyConnected.id (X : Scheme.{u}) : GeometricallyConnected (𝟙 X) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ k ↦ ?_⟩
  rw [(pullback.snd (𝟙 X) k).homeomorph.connectedSpace_iff]
  infer_instance

theorem isMultiplicative_geometricallyConnected_inf_universallyOpen :
    (@GeometricallyConnected ⊓ @UniversallyOpen : MorphismProperty Scheme.{u}).IsMultiplicative where
  id_mem X := ⟨GeometricallyConnected.id X, inferInstance⟩
  comp_mem f g hf hg := by
    obtain ⟨hf₁, hf₂⟩ := hf
    obtain ⟨hg₁, hg₂⟩ := hg
    exact ⟨GeometricallyConnected.comp f g, inferInstance⟩

end AlgebraicGeometry

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    [GeometricallyConnected f] {r : ℕ} {Y : Scheme.{u}} {y : Y ⟶ S}
    {Duniv : RelEffCartierDiv f r y} (hU : Duniv.IsUniversal) : GeometricallyConnected y := by
  obtain ⟨σ, hσ, -, -, -, -, hsurj, -⟩ := hU.exists_sumMap
  have : Smooth f := SmoothOfRelativeDimension.smooth (n := 1) (f := f)
  have : UniversallyOpen f := inferInstance
  have := isMultiplicative_geometricallyConnected_inf_universallyOpen.{u}
  have hGC : (@GeometricallyConnected ⊓ @UniversallyOpen : MorphismProperty Scheme.{u})
      (fibrePowOver.toBase f r) :=
    MorphismProperty.widePullback_base (P := @GeometricallyConnected ⊓ @UniversallyOpen)
      (fun _ : Fin r ↦ 𝒞) (fun _ ↦ f) fun _ ↦ ⟨‹_›, ‹_›⟩
  have : GeometricallyConnected (σ ≫ y) := by rw [hσ]; exact hGC.1
  exact GeometricallyConnected.of_comp_of_surjective σ y
