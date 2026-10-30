import CriticalGlobalFibreCount
import CriticalSchemePointPlaces

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
open AlgebraicGeometry CategoryTheory AlgebraicCurve
universe u
namespace FourCorner.CriticalSchemeCount
variable {k:Type u} [Field k] [Fintype k] [DecidableEq k]
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants i).toModule
local instance coverConstants (i:k) : Algebra k (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.targetConstants k i
local instance coverModule (i:k) : Module k (CriticalLiteralDouble.field k i) := (coverConstants i).toModule

def residueVector (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) (p:CriticalSchemePointPlaces.BasePoints i) : Fin 4→k :=
  let v:=CriticalSchemePointPlaces.baseEquiv i hi h2 p
  CriticalProjectiveResidues.vector i hi h2 v.val v.property

def character (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) (p:CriticalSchemePointPlaces.BasePoints i) : ℤ :=
  quadraticChar k (2*CriticalProjectiveCharacter.product (residueVector i hi h2 p))

abbrev SquarePoints (i:k) (hi:i^2 = -1) (h2:(2:k)≠0):=
  {p:CriticalSchemePointPlaces.BasePoints i //
    CriticalElliptic23.Shift (residueVector i hi h2 p)≠0 ∧character i hi h2 p=1}

/-- Source-specific projective coordinates are taken from the SAME genuine
Scheme point's original a,b,c functions via its fixed generic-stalk map. -/
theorem residueVector_critical (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (p:CriticalSchemePointPlaces.BasePoints i) :
    CriticalElliptic23.CriticalCoordinates i (residueVector i hi h2 p) ∧residueVector i hi h2 p≠0 := by
  let v:=CriticalSchemePointPlaces.baseEquiv i hi h2 p
  exact ⟨CriticalProjectiveResidues.vector_critical i hi h2 v.val v.property,
    CriticalProjectiveResidues.vector_nonzero i hi h2 v.val v.property⟩

def squarePointsEquiv (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    SquarePoints i hi h2 ≃ CriticalGlobalFibreCount.GoodBase i hi h2 := by
  refine (CriticalSchemePointPlaces.baseEquiv i hi h2).subtypeEquiv ?_
  intro p
  let v:=CriticalSchemePointPlaces.baseEquiv i hi h2 p
  have hb:=CriticalProjectiveBoundary.vector_boundary_iff i hi h2 v.val v.property
  exact and_congr (not_congr hb) Iff.rfl

/-- The exact original b-nonzero, positive-character count on genuine
Scheme K-points, with E the SAME independent accepted y²=x³−x model. -/
theorem count (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    Nat.card (SquarePoints i hi h2)=
      (Nat.card (CriticalSchemePointPlaces.CoverPoints (k:=k))-
        Nat.card (CriticalActualBoundaryCount.Boundary i))/2 := by
  rw [Nat.card_congr (squarePointsEquiv i hi h2)]
  rw [CriticalGlobalFibreCount.good_count i hi h2]
  rw [CriticalSchemePointPlaces.cover_card i hi h2]

theorem count_mod_eight {p:ℕ} [Fact p.Prime] (hmod:p%4=1)
    (i:ZMod p) (hi:i^2 = -1) (h2:(2:ZMod p)≠0) :
    Nat.card (SquarePoints i hi h2)=
      (Nat.card (CriticalSchemePointPlaces.CoverPoints (k:=ZMod p))-
        (if p%8=1 then 16 else 8))/2 := by
  rw [count i hi h2,CriticalActualBoundaryCount.boundary_count_mod_eight hmod i hi]

/-- The actual finite-field quadratic character is unchanged by every
nonzero rescaling of these original projective coordinate values. -/
theorem character_rescale (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (p:CriticalSchemePointPlaces.BasePoints i) (a:k) (ha:a≠0) :
    quadraticChar k (2*CriticalProjectiveCharacter.product (fun j=>a*residueVector i hi h2 p j))=
      character i hi h2 p :=
  CriticalProjectiveCharacter.rescale (residueVector i hi h2 p) a ha

end FourCorner.CriticalSchemeCount
#print axioms FourCorner.CriticalSchemeCount.residueVector_critical
#print axioms FourCorner.CriticalSchemeCount.squarePointsEquiv
#print axioms FourCorner.CriticalSchemeCount.count
#print axioms FourCorner.CriticalSchemeCount.count_mod_eight
#print axioms FourCorner.CriticalSchemeCount.character_rescale
