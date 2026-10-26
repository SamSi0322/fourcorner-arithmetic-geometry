import CriticalSchemeCount
import CriticalSchemeBoundary
import CriticalLiteralSchemeCharacter

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
open AlgebraicGeometry CategoryTheory AlgebraicCurve
universe u
namespace FourCorner.CriticalLiteralCount
variable {k:Type u} [Field k] [Fintype k] [DecidableEq k]
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants i).toModule

/-- Literal original b-nonzero locus on actual over-k Scheme points. -/
abbrev PositivePoints (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :=
 {P:CriticalSchemePointPlaces.BasePoints i //
 P.val ⁻¹ᵁ CriticalHomogeneousEvaluation.shiftOpen i≠⊥ ∧ CriticalSchemeCount.character i hi h2 P=1}

theorem boundary_iff_vector (i:k) (hi:i^2= -1) (h2:(2:k)≠0)
 (P:CriticalSchemePointPlaces.BasePoints i) :
 P.val ⁻¹ᵁ CriticalHomogeneousEvaluation.shiftOpen i=⊥ ↔
 CriticalElliptic23.Shift (CriticalSchemeCount.residueVector i hi h2 P)=0 := by
 rw [CriticalSchemeBoundary.boundary_iff_place i hi h2 P]
 exact (CriticalProjectiveBoundary.vector_boundary_iff i hi h2
   (CriticalSchemePointPlaces.baseEquiv i hi h2 P).val
   (CriticalSchemePointPlaces.baseEquiv i hi h2 P).property).symm

def positiveEquiv (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
 PositivePoints i hi h2 ≃ CriticalSchemeCount.SquarePoints i hi h2 :=
 Equiv.subtypeEquivRight (fun P=>and_congr (not_congr (boundary_iff_vector i hi h2 P)) Iff.rfl)

theorem count (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
 Nat.card (PositivePoints i hi h2)=
 (Nat.card (CriticalSchemePointPlaces.CoverPoints (k:=k))-
 Nat.card (CriticalActualBoundaryCount.Boundary i))/2 := by
 rw [Nat.card_congr (positiveEquiv i hi h2)]
 exact CriticalSchemeCount.count i hi h2

theorem count_mod_eight {p:ℕ} [Fact p.Prime] (hmod:p%4=1)
 (i:ZMod p) (hi:i^2= -1) (h2:(2:ZMod p)≠0) :
 Nat.card (PositivePoints i hi h2)=
 (Nat.card (CriticalSchemePointPlaces.CoverPoints (k:=ZMod p))-
 (if p%8=1 then 16 else 8))/2 := by
 rw [Nat.card_congr (positiveEquiv i hi h2)]
 exact CriticalSchemeCount.count_mod_eight hmod i hi h2

end FourCorner.CriticalLiteralCount
#print axioms FourCorner.CriticalLiteralCount.boundary_iff_vector
#print axioms FourCorner.CriticalLiteralCount.positiveEquiv
#print axioms FourCorner.CriticalLiteralCount.count
#print axioms FourCorner.CriticalLiteralCount.count_mod_eight
