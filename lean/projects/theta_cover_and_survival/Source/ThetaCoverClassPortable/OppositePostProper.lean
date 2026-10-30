import ThetaCoverClassPortable.Slot02HighRatios
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace FourCorner.OppositeProjective.PostProper
universe u
variable {K : Type u} [Field K] [CharZero K]

instance ambientFiniteType : Algebra.FiniteType (grading K 0) (OppositeHomogeneousQuadrics.Ambient K) := by
  classical
  refine ⟨⟨Finset.univ.image MvPolynomial.X, eq_top_iff.mpr fun p _ => ?_⟩⟩
  induction p using MvPolynomial.induction_on with
  | C r => exact Subalgebra.algebraMap_mem _ (⟨C r,isHomogeneous_C _ r⟩ : grading K 0)
  | add p q hp hq => exact Subalgebra.add_mem _ (hp trivial) (hq trivial)
  | mul_X p j hp =>
    exact Subalgebra.mul_mem _ (hp trivial)
      (Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ j))))

theorem spaceToBase_isProper : IsProper (OppositeProjective.spaceToBase (K := K)) := by
  have hc : OppositeProjective.constants (K := K) =
      (Slot02HighProjSpace.grad0Equiv K 4).toRingHom := rfl
  unfold OppositeProjective.spaceToBase
  rw [hc]
  haveI : IsIso (CommRingCat.ofHom (Slot02HighProjSpace.grad0Equiv K 4).toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (Slot02HighProjSpace.grad0Equiv K 4).bijective
  infer_instance

/-- Properness belongs to the actual literal three-quadric projective scheme and its original base map. -/
theorem toBase_isProper (mu nu : K) : IsProper (OppositeProjective.toBase mu nu) := by
  haveI := embedding_isClosedImmersion mu nu
  haveI := spaceToBase_isProper (K := K)
  unfold OppositeProjective.toBase
  infer_instance

end FourCorner.OppositeProjective.PostProper
#print axioms FourCorner.OppositeProjective.PostProper.toBase_isProper
