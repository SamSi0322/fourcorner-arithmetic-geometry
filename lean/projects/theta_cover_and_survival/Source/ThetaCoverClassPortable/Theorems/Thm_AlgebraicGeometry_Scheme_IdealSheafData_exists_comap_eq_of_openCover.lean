import ThetaCoverClassPortable.P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.IdealSheafData
theorem exists_comap_eq_of_openCover
    {X : Scheme.{u}} (𝒰 : X.OpenCover) (I : ∀ i, (𝒰.X i).IdealSheafData)
    (hI : ∀ ⦃i j : 𝒰.I₀⦄ ⦃V : Scheme.{u}⦄ (a : V ⟶ 𝒰.X i) (b : V ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (I i).comap a = (I j).comap b) :
    ∃ I₀ : X.IdealSheafData, ∀ i, I₀.comap (𝒰.f i) = I i :=
  P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.solution 𝒰 I hI
end AlgebraicGeometry.Scheme.IdealSheafData
