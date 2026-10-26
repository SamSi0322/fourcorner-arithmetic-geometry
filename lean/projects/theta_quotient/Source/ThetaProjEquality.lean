import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
noncomputable section
namespace FourCorner.ThetaProjEquality
open AlgebraicGeometry CategoryTheory HomogeneousIdeal
universe u
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {G : ℕ → σ} [GradedRing G]
theorem map_eq_id (f : G →+*ᵍ G) (h : f=GradedRingHom.id G)
    (hf : G₊ ≤ G₊.map f) :
    Proj.map f hf=𝟙 (Proj G) := by
  subst f
  exact Proj.map_id
end FourCorner.ThetaProjEquality
