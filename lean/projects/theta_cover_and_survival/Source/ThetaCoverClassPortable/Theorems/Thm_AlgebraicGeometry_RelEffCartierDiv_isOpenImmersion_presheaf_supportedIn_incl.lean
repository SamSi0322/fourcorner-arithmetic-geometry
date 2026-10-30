import ThetaCoverClassPortable.P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_isOpenImmersion_presheaf_supportedIn_incl

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.RelEffCartierDiv
theorem isOpenImmersion_presheaf_supportedIn_incl {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ) (U : 𝒞.Opens) :
    IsOpenImmersion.presheaf (RelEffCartierDiv.supportedIn f r U).ι :=
  P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isOpenImmersion_presheaf_supportedIn_incl.solution f r U
end AlgebraicGeometry.RelEffCartierDiv
