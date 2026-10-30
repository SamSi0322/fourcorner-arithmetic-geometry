import ThetaCoverClassPortable.P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_isUniversal_empty

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.RelEffCartierDiv
theorem isUniversal_empty {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) :
    (RelEffCartierDiv.empty f (𝟙 S)).IsUniversal :=
  P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isUniversal_empty.solution f
end AlgebraicGeometry.RelEffCartierDiv
