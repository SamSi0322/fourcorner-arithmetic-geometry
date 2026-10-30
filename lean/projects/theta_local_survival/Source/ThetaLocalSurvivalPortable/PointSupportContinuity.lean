import ThetaLocalSurvivalPortable.SchemePointTopology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
open scoped Topology
namespace FourCorner.ThetaLocalSurvival.StrongTopology
open Multiplication Infinitesimal

variable (K : Type) [Field K] [Algebra ℚ K] [TopologicalSpace K] [T1Space K]

/-- The actual image of the unique point of Spec K. Its target has the Zariski topology. -/
def pointSupport {X : Over base} (P : KPoints K X) : X.left :=
  P.left (IsLocalRing.closedPoint K)

theorem affinePointSupport_mem_basicOpen (A : Type) [CommRing A] [Algebra ℚ A]
    (p : A →ₐ[ℚ] K) (a : A) :
    pointSupport K (pointChange p) ∈ PrimeSpectrum.basicOpen a ↔ p a ≠ 0 := by
  change a ∉ (PrimeSpectrum.comap p.toRingHom (IsLocalRing.closedPoint K)).asIdeal ↔ _
  simp [IsLocalRing.closedPoint, IsLocalRing.maximalIdeal_eq_bot]

theorem continuous_affinePointSupport (A : Type) [CommRing A] [Algebra ℚ A] :
    Continuous (fun p : A →ₐ[ℚ] K => pointSupport K (pointChange p)) := by
  apply PrimeSpectrum.isTopologicalBasis_basic_opens.continuous_iff.mpr
  rintro U ⟨a, rfl⟩
  have h : (fun p : A →ₐ[ℚ] K => pointSupport K (pointChange p)) ⁻¹'
      (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) = {p | p a ≠ 0} := by
    ext p
    exact affinePointSupport_mem_basicOpen K A p a
  rw [h]
  exact isClosed_singleton.isOpen_compl.preimage (continuous_evaluation ℚ A K a)

/-- Strong-topology points map continuously to the underlying Zariski space. -/
theorem continuous_pointSupport (X : Over base) : Continuous (pointSupport K (X:=X)) := by
  apply (continuous_schemePoints_iff K _).2
  intro A j
  have h : (fun p : A →ₐ[ℚ] K => pointSupport K (affineTest K A j p)) =
      (fun p => j.left (pointSupport K (pointChange p))) := rfl
  rw [h]
  exact j.left.continuous.comp (continuous_affinePointSupport K A)

theorem isOpen_pointSupport_preimage {X : Over base} (U : X.left.Opens) :
    IsOpen ((pointSupport K (X:=X)) ⁻¹' (U : Set X.left)) :=
  U.isOpen.preimage (continuous_pointSupport K X)

end FourCorner.ThetaLocalSurvival.StrongTopology
