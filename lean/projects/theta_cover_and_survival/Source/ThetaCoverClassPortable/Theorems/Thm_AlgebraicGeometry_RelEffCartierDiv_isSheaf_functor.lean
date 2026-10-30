import ThetaCoverClassPortable.P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_isSheaf_functor

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.RelEffCartierDiv
theorem isSheaf_functor {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ) :
    Presieve.IsSheaf Scheme.zariskiTopology (RelEffCartierDiv.functor f r) :=
  P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isSheaf_functor.solution f r
end AlgebraicGeometry.RelEffCartierDiv
