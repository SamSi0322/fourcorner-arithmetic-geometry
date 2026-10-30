import ThetaCoverClassPortable.P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_of_forall_finset

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.RelEffCartierDiv
theorem exists_supportedIn_of_forall_finset
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    (hcov : ∀ (V : S.affineOpens) (F : Finset 𝒞), (∀ x ∈ F, f x ∈ (V : S.Opens)) →
      ∃ U : 𝒞.Opens, IsAffineOpen U ∧ U ≤ f ⁻¹ᵁ (V : S.Opens) ∧ ∀ x ∈ F, x ∈ U)
    (r : ℕ) {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) (t : T) :
    ∃ (W : T.Opens) (_ : t ∈ W) (V : S.affineOpens) (U : 𝒞.affineOpens)
      (_ : (U : 𝒞.Opens) ≤ f ⁻¹ᵁ (V : S.Opens)),
      (D.pullbackAlong W.ι rfl).SupportedIn U :=
  P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_of_forall_finset.solution f hcov r D t
end AlgebraicGeometry.RelEffCartierDiv
