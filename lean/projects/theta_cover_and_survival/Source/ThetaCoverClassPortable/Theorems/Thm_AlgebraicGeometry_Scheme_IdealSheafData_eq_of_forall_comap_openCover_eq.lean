import ThetaCoverClassPortable.P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.IdealSheafData
theorem eq_of_forall_comap_openCover_eq
    {X : Scheme.{u}} (𝒰 : X.OpenCover) {I J : X.IdealSheafData}
    (h : ∀ i, I.comap (𝒰.f i) = J.comap (𝒰.f i)) : I = J :=
  P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq.solution 𝒰 h
end AlgebraicGeometry.Scheme.IdealSheafData
