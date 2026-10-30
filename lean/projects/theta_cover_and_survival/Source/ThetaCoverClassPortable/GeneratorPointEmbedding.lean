import ThetaCoverClassPortable.PolynomialPointTopology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
open scoped Topology
namespace FourCorner.ThetaLocalSurvival.StrongTopology

variable (R A K : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing K] [Algebra R K] [TopologicalSpace K] [IsTopologicalRing K]
  {ι : Type*} (P : Algebra.Generators R A ι)

def generatorCoordinates (f : A →ₐ[R] K) : ι→K := fun i => f (P.val i)

theorem continuous_generatorCoordinates : Continuous (generatorCoordinates R A K P) :=
  continuous_pi (fun i => continuous_evaluation R A K (P.val i))

def generatorReconstruct (x : ι→K) : A→K :=
  fun a => eval₂ (algebraMap R K) x (P.σ a)

theorem generatorReconstruct_coordinates (f : A →ₐ[R] K) :
    generatorReconstruct R A K P (generatorCoordinates R A K P f)=(f : A→K) := by
  funext a
  have h := congrArg f (P.aeval_val_σ a)
  rw [aeval_def] at h
  change f.toRingHom (eval₂ (algebraMap R A) P.val (P.σ a))=f a at h
  rw [eval₂_comp_left] at h
  have hc : f.toRingHom.comp (algebraMap R A)=algebraMap R K := f.comp_algebraMap
  rw [hc] at h
  exact h

theorem continuous_generatorReconstruct : Continuous (generatorReconstruct R A K P) := by
  apply continuous_pi
  intro a
  have h := (continuous_eval₂_point R R K (P.σ a)).comp
    (continuous_const.prodMk continuous_id : Continuous
      (fun x : ι→K => ((Algebra.ofId R K : R →ₐ[R] K),x)))
  exact h

/-- Evaluation at any actual family of algebra generators determines exactly the strong topology. -/
theorem isEmbedding_generatorCoordinates :
    Topology.IsEmbedding (generatorCoordinates R A K P) := by
  apply Topology.IsEmbedding.of_comp (continuous_generatorCoordinates R A K P)
    (continuous_generatorReconstruct R A K P)
  have h : generatorReconstruct R A K P ∘ generatorCoordinates R A K P =
      (fun f : A →ₐ[R] K => (f : A→K)) := funext (generatorReconstruct_coordinates R A K P)
  rw [h]
  exact affinePoint_isEmbedding R A K

end FourCorner.ThetaLocalSurvival.StrongTopology
