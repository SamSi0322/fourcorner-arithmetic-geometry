import HpAffineEquiv

namespace FourCorner.HpAffineFractionField
open Polynomial HpLiteralField HpAffineUniversal HpAffineEquiv
noncomputable section
variable (K : Type*) [Field K] [CharZero K]
local instance constantAlgebra (p : K) : Algebra K (field K p) := HpFieldGeometry.constantAlgebra K p
local instance constantModule (p : K) : Module K (field K p) := Algebra.toModule
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false

def evaluation (p : K) : B K p →+* field K p :=
  (HpPolynomialRootAlgebra.evaluation K p).toRingHom.comp (toUniversal K p)
local instance affineAlgebra (p : K) : Algebra (B K p) (field K p) := (evaluation K p).toAlgebra

 theorem evaluation_constant (p c : K) : evaluation K p (algebraMap K (B K p) c)=algebraMap K (field K p) c := by
  rw [evaluation,RingHom.comp_apply,toUniversal_C]
  change HpPolynomialRootAlgebra.evaluation K p (algebraMap K[X] (A K p) (Polynomial.C c))=_
  rw [AlgHom.commutes]
  rfl

local instance affineTower (p : K) : IsScalarTower K (B K p) (field K p) :=
  IsScalarTower.of_algebraMap_eq fun c=>(evaluation_constant K p c).symm

theorem isFractionRing (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    IsFractionRing (B K p) (field K p) := by
  letI : Algebra (A K p) (field K p) := HpPolynomialFractionField.coordinateAlgebra K p
  letI := HpPolynomialFractionField.isFractionRing K p hp ha hb
  apply IsFractionRing.of_ringEquiv_left (ringEquiv K p hp)
  intro b
  rfl

/-- Exact function field of the literal Z=1 coordinate ring, preserving
its original K-structure and the original ordered radical coordinates. -/
def fieldEquiv (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    letI := affine_isDomain K p hp ha hb
    FractionRing (B K p) ≃ₐ[K] field K p := by
  letI := affine_isDomain K p hp ha hb
  letI := isFractionRing K p hp ha hb
  exact IsFractionRing.algEquivOfAlgEquiv (AlgEquiv.refl : B K p ≃ₐ[K] B K p)

#print axioms isFractionRing
#print axioms fieldEquiv
end
end FourCorner.HpAffineFractionField
