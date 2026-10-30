import ThetaCoverClassPortable.EtaleSchemePointLocalHomeomorph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
open scoped Topology
namespace FourCorner.ThetaLocalSurvival.StrongTopology

variable (R K : Type*) [CommRing R] [CommRing K] [Algebra R K]
  [TopologicalSpace K] [IsTopologicalRing K] (ι : Type*)

/-- The canonical strong topology on free affine-space points is the usual product topology. -/
def freePolynomialPointsHomeomorph : (MvPolynomial ι R →ₐ[R] K) ≃ₜ (ι→K) where
  toFun f := fun i => f (X i)
  invFun x := aeval x
  left_inv := by intro f; ext i; simp
  right_inv := by intro x; funext i; simp
  continuous_toFun := continuous_pi (fun i => continuous_evaluation R _ K (X i))
  continuous_invFun := by
    apply (continuous_affine_iff R _ K _).2
    intro p
    have h := (continuous_eval₂_point R R K p).comp
      (continuous_const.prodMk continuous_id : Continuous
        (fun x : ι→K => ((Algebra.ofId R K : R →ₐ[R] K),x)))
    exact h

/-- Actual affine-line points have the ordinary topology of K itself. -/
def affineLinePointsHomeomorph : (MvPolynomial (Fin 1) R →ₐ[R] K) ≃ₜ K :=
  (freePolynomialPointsHomeomorph R K (Fin 1)).trans (Homeomorph.piUnique fun _ : Fin 1 => K)

end FourCorner.ThetaLocalSurvival.StrongTopology
