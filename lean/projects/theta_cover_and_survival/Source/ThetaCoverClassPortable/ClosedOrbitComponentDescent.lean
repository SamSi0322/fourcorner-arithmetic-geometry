import ThetaCoverClassPortable.NoetherianConnectedComponents

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set TopologicalSpace
namespace FourCorner.ThetaLocalSurvival.ComponentDescent

/-- Effective descent of the ACTUAL connected component through a closed
surjective projection with orbit fibres. Invariance alone is not used as
a descent assertion: saturation and a descended clopen subset are proved. -/
theorem closed_orbit_component_descent
    {Z Y Γ : Type} [TopologicalSpace Z] [TopologicalSpace Y] [NoetherianSpace Z]
    (π : Z → Y) (hclosed : IsClosedMap π) (hsurj : Function.Surjective π)
    (ρ : Γ → Z ≃ₜ Z) (z0 : Z) (hfix : ∀g,ρ g z0=z0)
    (horbit : ∀z w,π z=π w → ∃g,ρ g z=w) :
    ∃U : Set Y,IsClopen U ∧ π ⁻¹' U=connectedComponent z0 ∧ π z0∈U := by
  let C := connectedComponent z0
  let U := π '' C
  have hC : IsClopen C := noetherian_connectedComponent_isClopen z0
  have hstable (g : Γ) : ρ g '' C⊆C := by
    have h := (ρ g).continuous.image_connectedComponent_subset z0
    rwa [hfix g] at h
  have hpre : π ⁻¹' U=C := by
    ext z
    constructor
    · rintro ⟨w,hw,heq⟩
      obtain ⟨g,hg⟩ := horbit w z heq
      exact hstable g ⟨w,hw,hg⟩
    · intro hz
      exact ⟨z,hz,rfl⟩
  have hcomp : π '' Cᶜ=Uᶜ := by
    ext y
    constructor
    · rintro ⟨z,hz,heq⟩ hy
      have h : z∈π ⁻¹' U := by change π z∈U;rw [heq];exact hy
      rw [hpre] at h
      exact hz h
    · intro hy
      obtain ⟨z,hz⟩ := hsurj y
      refine ⟨z,?_,hz⟩
      intro hc
      apply hy
      exact ⟨z,hc,hz⟩
  have hcU : IsClosed U := hclosed C hC.isClosed
  have hcComp : IsClosed Uᶜ := by
    rw [←hcomp]
    exact hclosed Cᶜ hC.isOpen.isClosed_compl
  exact ⟨U,⟨hcU,isClosed_compl_iff.mp hcComp⟩,hpre,⟨z0,mem_connectedComponent,rfl⟩⟩

end FourCorner.ThetaLocalSurvival.ComponentDescent
