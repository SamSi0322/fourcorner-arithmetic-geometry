import CriticalBoundaryFibre
import CriticalBoundaryEight
import CriticalRationalFibres

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 40000
attribute [local instance] Classical.propDecidable
namespace FourCorner.CriticalActualBoundaryCount
open AlgebraicCurve CriticalRadicalField CriticalBoundaryResidues CriticalBoundaryRootCounts
variable {k:Type*} [Field k]
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants i).toModule
local instance coverConstants (i:k) : Algebra k (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.targetConstants k i
local instance coverModule (i:k) : Module k (CriticalLiteralDouble.field k i) := (coverConstants i).toModule
local instance relative (i:k) : Algebra (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.relativeAlgebra k i
local instance relativeModule (i:k) : Module (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := (relative i).toModule
local instance tower (i:k) : IsScalarTower k (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.constants_base_tower k i

abbrev Boundary (i:k) := {w:Place k (CriticalLiteralDouble.field k i) //
  w.IsRational ∧ 0<(w.restrict (field k i)).ord (shift i)}

/-- Actual rational places on the SAME specified cover above the ORIGINAL
boundary, not formal sign tuples, are in bijection with its normalized roots. -/
def boundaryEquiv (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    Boundary i ≃ (Σ e:Fin 3→Bool,{z:k //z^2=residue i e}) := by
  letI:=CriticalLiteralDouble.separable k i h2
  let first:=CriticalRationalFibres.sigmaOverEquiv (K:=k) (F:=field k i) (E:=CriticalLiteralDouble.field k i)
    (fun v=>0<v.ord (shift i))
  refine first.trans (Equiv.sigmaCongr (CriticalBoundaryEight.boundaryEquiv i hi h2) fun v=>?_)
  have he:=CriticalBoundaryEight.boundaryEquiv_evaluations i hi h2 v
  exact CriticalBoundaryFibre.boundaryFibreEquiv i hi h2 v.val v.property.1 v.property.2
    (CriticalBoundaryEight.boundaryEquiv i hi h2 v) he.1 he.2.1 he.2.2

/-- The Bp value on ACTUAL rational cover points. No fibre count is assumed. -/
theorem boundary_count (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    Nat.card (Boundary i)=if IsSquare i then 16 else 8 := by
  rw [Nat.card_congr (boundaryEquiv i hi h2)]
  exact local_boundary_count i hi h2

theorem boundary_count_mod_eight {p:ℕ} [Fact p.Prime] (hmod:p%4=1)
    (i:ZMod p) (hi:i^2 = -1) :
    Nat.card (Boundary i)=if p%8=1 then 16 else 8 := by
  have hp2:p≠2 := by omega
  have h2:(2:ZMod p)≠0 := Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp2)
  rw [boundary_count i hi h2]
  simp only [CriticalBoundaryCharacter.square_i_iff_mod_eight hmod i hi]

end FourCorner.CriticalActualBoundaryCount
#print axioms FourCorner.CriticalActualBoundaryCount.boundaryEquiv
#print axioms FourCorner.CriticalActualBoundaryCount.boundary_count
#print axioms FourCorner.CriticalActualBoundaryCount.boundary_count_mod_eight
