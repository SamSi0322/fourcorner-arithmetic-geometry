import HpFourRootUniversal

namespace FourCorner.HpPolynomialFractionField
open Polynomial HpLiteralField HpPolynomialRootAlgebra
noncomputable section
variable (K : Type*) [Field K] [NeZero (2 : K)]
local instance constantAlgebra (p : K) : Algebra K (field K p) := HpFieldGeometry.constantAlgebra K p
local instance constantModule (p : K) : Module K (field K p) := Algebra.toModule

theorem evaluation_injective (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    Function.Injective (evaluation K p) := by
  have hi := Algebra.TensorProduct.includeRight_injective (R:=K[X]) (A:=RatFunc K) (B:=A K p)
    (RatFunc.algebraMap_injective (K:=K))
  intro x y h
  apply hi
  apply (tensorEquiv K p hp ha hb).injective
  change tensorEvaluation K p (1 ⊗ₜ[K[X]] x)=tensorEvaluation K p (1 ⊗ₜ[K[X]] y)
  simp only [tensorEvaluation,Algebra.TensorProduct.lift_tmul,map_one,one_mul]
  exact h

local instance coordinateAlgebra (p : K) : Algebra (A K p) (field K p) :=
  (evaluation K p).toRingHom.toAlgebra
local instance coordinateTower (p : K) : IsScalarTower K[X] (A K p) (field K p) :=
  IsScalarTower.of_algebraMap_eq fun x=>(evaluation K p).commutes x |>.symm

/-- The actual field of the four-root function field is the fraction field
of the integral monic coordinate ring, via its original coordinate map. -/
theorem isFractionRing (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    IsFractionRing (A K p) (field K p) := by
  letI : FaithfulSMul (A K p) (field K p) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (evaluation_injective K p hp ha hb)
  apply Multiquadratic.GeneratedFractionField.of_adjoin_eq_top K[X] (RatFunc K) (A K p)
    (field K p) (Set.range (root K p)) (HpFieldGeometry.root_generates K p)
  rintro _ ⟨i,rfl⟩
  refine ⟨FourRootLift08.coord K[X] (poly K p) i,?_⟩
  change FourRootLift08.lift K[X] (algebraMap K[X] (field K p)) (poly K p) (root K p)
    (fun k=>by rw [root_sq];rfl) (FourRootLift08.coord K[X] (poly K p) i)=root K p i
  exact FourRootLift08.lift_coord _ _ _ _ _ i

#print axioms evaluation_injective
#print axioms isFractionRing
end
end FourCorner.HpPolynomialFractionField
