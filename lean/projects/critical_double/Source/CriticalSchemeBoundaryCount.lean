import CriticalPointNaturality
import CriticalLiteralCount

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
open AlgebraicGeometry CategoryTheory AlgebraicCurve
universe u
namespace FourCorner.CriticalSchemeBoundaryCount
variable {k:Type u} [Field k]
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants i).toModule
local instance coverConstants (i:k) : Algebra k (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.targetConstants k i
local instance coverModule (i:k) : Module k (CriticalLiteralDouble.field k i) := (coverConstants i).toModule
local instance relative (i:k) : Algebra (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.relativeAlgebra k i
local instance relativeModule (i:k) : Module (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := (relative i).toModule
local instance tower (i:k) : IsScalarTower k (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.constants_base_tower k i

/-- ACTUAL cover Scheme points whose image under the FIXED original cover
map lies on the literal b=V1²-V0² boundary. -/
abbrev BoundaryPoints (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :=
 {P:CriticalSchemePointPlaces.CoverPoints (k:=k) //
 (CriticalPointNaturality.imagePoint i hi h2 P).val ⁻¹ᵁ CriticalHomogeneousEvaluation.shiftOpen i=⊥}

def boundaryEquiv (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
 BoundaryPoints i hi h2 ≃ CriticalActualBoundaryCount.Boundary i := by
 let e:=CriticalSchemePointPlaces.coverEquiv i hi h2
 let B: {w:Place k (CriticalLiteralDouble.field k i)//w.IsRational}→Prop :=
   fun w=>0<(w.val.restrict (CriticalLiteralDouble.base k i)).ord (CriticalBoundaryResidues.shift i)
 have hp:∀P, (CriticalPointNaturality.imagePoint i hi h2 P).val ⁻¹ᵁ CriticalHomogeneousEvaluation.shiftOpen i=⊥ ↔ B (e P) := by
   intro P
   rw [CriticalSchemeBoundary.boundary_iff_place i hi h2,
     CriticalPointNaturality.image_place i hi h2]
 let e1:=e.subtypeEquiv hp
 let e2:{w:{w:Place k (CriticalLiteralDouble.field k i)//w.IsRational}//B w} ≃
   CriticalActualBoundaryCount.Boundary i :=
   {toFun:=fun w=>⟨w.val.val,w.val.property,w.property⟩
    invFun:=fun w=>⟨⟨w.val,w.property.1⟩,w.property.2⟩
    left_inv:=by intro w;cases w;rfl
    right_inv:=by intro w;cases w;rfl}
 exact e1.trans e2

theorem boundary_count (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
 Nat.card (BoundaryPoints i hi h2)=if IsSquare i then 16 else 8 := by
 rw [Nat.card_congr (boundaryEquiv i hi h2)]
 exact CriticalActualBoundaryCount.boundary_count i hi h2

theorem boundary_count_mod_eight {p:ℕ} [Fact p.Prime] (hmod:p%4=1)
 (i:ZMod p) (hi:i^2= -1) (h2:(2:ZMod p)≠0) :
 Nat.card (BoundaryPoints i hi h2)=if p%8=1 then 16 else 8 := by
 rw [Nat.card_congr (boundaryEquiv i hi h2)]
 exact CriticalActualBoundaryCount.boundary_count_mod_eight hmod i hi

variable [Fintype k] [DecidableEq k]
/-- Exact original Scheme count with Bp itself counting ACTUAL Scheme
points above the ORIGINAL boundary under this SAME map. -/
theorem count (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
 Nat.card (CriticalLiteralCount.PositivePoints i hi h2)=
 (Nat.card (CriticalSchemePointPlaces.CoverPoints (k:=k))-Nat.card (BoundaryPoints i hi h2))/2 := by
 rw [Nat.card_congr (boundaryEquiv i hi h2)]
 exact CriticalLiteralCount.count i hi h2

end FourCorner.CriticalSchemeBoundaryCount
#print axioms FourCorner.CriticalSchemeBoundaryCount.boundaryEquiv
#print axioms FourCorner.CriticalSchemeBoundaryCount.boundary_count
#print axioms FourCorner.CriticalSchemeBoundaryCount.boundary_count_mod_eight
#print axioms FourCorner.CriticalSchemeBoundaryCount.count
