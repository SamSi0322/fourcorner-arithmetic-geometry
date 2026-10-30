import HpModelFieldPoint
import Mathlib.RingTheory.Flat.Basic

namespace FourCorner.HpPolynomialRootAlgebra
open Polynomial HpLiteralField HpFieldGeometry
open scoped TensorProduct
noncomputable section
variable (K : Type*) [Field K] [NeZero (2 : K)]
local instance constantAlgebra (p : K) : Algebra K (field K p) := HpFieldGeometry.constantAlgebra K p
local instance constantModule (p : K) : Module K (field K p) := Algebra.toModule
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false

abbrev A (p : K) := FourRootLift08.A K[X] (poly K p)

def evaluation (p : K) : A K p →ₐ[K[X]] field K p where
  __ := FourRootLift08.lift K[X] (algebraMap K[X] (field K p)) (poly K p) (root K p)
    (fun i => by rw [root_sq];rfl)
  commutes' := FourRootLift08.lift_algebraMap K[X] (algebraMap K[X] (field K p)) _ _ _

def tensorEvaluation (p : K) : (RatFunc K) ⊗[K[X]] (A K p) →ₐ[RatFunc K] field K p :=
  Algebra.TensorProduct.lift (Algebra.ofId (RatFunc K) (field K p)) (evaluation K p)
    (fun _ _=>Commute.all _ _)

theorem tensorEvaluation_surjective (p : K) : Function.Surjective (tensorEvaluation K p) := by
  have hrange : (tensorEvaluation K p).range=⊤ := by
    apply top_unique
    rw [← root_generates K p]
    apply Algebra.adjoin_le
    rintro _ ⟨i,rfl⟩
    refine ⟨1 ⊗ₜ[K[X]] FourRootLift08.coord K[X] (poly K p) i,?_⟩
    change tensorEvaluation K p (1 ⊗ₜ[K[X]] FourRootLift08.coord K[X] (poly K p) i)=root K p i
    rw [tensorEvaluation,Algebra.TensorProduct.lift_tmul]
    simp only [map_one,one_mul]
    change FourRootLift08.lift K[X] (algebraMap K[X] (field K p)) (poly K p) (root K p) (fun k=>by rw [root_sq];rfl)
      (FourRootLift08.coord K[X] (poly K p) i)=root K p i
    exact FourRootLift08.lift_coord K[X] (algebraMap K[X] (field K p)) (poly K p) (root K p)
      (fun k=>by rw [root_sq];rfl) i
  intro x
  have hx : x∈(tensorEvaluation K p).range := by rw [hrange];trivial
  exact hx

def tensorEquiv (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    (RatFunc K) ⊗[K[X]] (A K p) ≃ₐ[RatFunc K] field K p := by
  letI := finite_over_line K p
  have hd : Module.finrank (RatFunc K) ((RatFunc K) ⊗[K[X]] (A K p))=
      Module.finrank (RatFunc K) (field K p) := by
    rw [Module.finrank_baseChange,FourRootLift08.finrank,field_degree_sixteen K p hp ha hb]
  have hi := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd
    (f:=(tensorEvaluation K p).toLinearMap)).mpr (tensorEvaluation_surjective K p)
  exact AlgEquiv.ofBijective (tensorEvaluation K p) ⟨hi,tensorEvaluation_surjective K p⟩

/-- The original four monic linear-radicand equations over K[rho] form
an actual integral ring; no fraction-field or irreducibility premise is assumed. -/
theorem isDomain (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) : IsDomain (A K p) := by
  let e := tensorEquiv K p hp ha hb
  letI : IsDomain ((RatFunc K) ⊗[K[X]] (A K p)) := Function.Injective.isDomain e e.injective
  have hi := Algebra.TensorProduct.includeRight_injective (R:=K[X]) (A:=RatFunc K) (B:=A K p)
    (RatFunc.algebraMap_injective (K:=K))
  exact Function.Injective.isDomain (Algebra.TensorProduct.includeRight : A K p →ₐ[K[X]] _ ) hi

#print axioms tensorEquiv
#print axioms isDomain
end
end FourCorner.HpPolynomialRootAlgebra
