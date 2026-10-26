import CriticalBoundaryUnits
import CriticalDoublePointCount
import QuadraticRationalPlaceFibre

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 40000
namespace FourCorner.CriticalBoundaryFibre
open AlgebraicCurve CriticalRadicalField ResiduePlaceEvaluation CriticalBoundaryResidues
open CriticalElliptic23 CriticalBoundaryRootCounts
variable {k:Type*} [Field k]
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants i).toModule
local instance coverConstants (i:k) : Algebra k (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.targetConstants k i
local instance coverModule (i:k) : Module k (CriticalLiteralDouble.field k i) := (coverConstants i).toModule
local instance relative (i:k) : Algebra (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.relativeAlgebra k i
local instance relativeModule (i:k) : Module (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := (relative i).toModule
local instance tower (i:k) : IsScalarTower k (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.constants_base_tower k i

/-- Genuine actual normalized-cover rational places above the SAME original
boundary place, bijective with the roots of its original signed residue. -/
def boundaryFibreEquiv (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (v:Place k (field k i)) (hv:v.IsRational) (hp:0<v.ord (shift i))
    (e:Fin 3→Bool)
    (ha:evaluate v hv (A i hi h2 v hp)=sign (e 0))
    (hb:evaluate v hv (B i hi h2 v hp)=sign (e 1))
    (hc:evaluate v hv (C i hi h2 v hp)=sign (e 2)) :
    {w:Place k (CriticalLiteralDouble.field k i) //w.restrict (field k i)=v ∧ w.IsRational} ≃
      {z:k //z^2=residue i e} := by
  letI:=CriticalLiteralDouble.separable k i h2
  let data:=CriticalBoundaryUnits.normalized_unit i hi h2 v hv hp e ha hb hc
  let u:=Classical.choose data
  have hu:IsUnit u := (Classical.choose_spec data).1
  let rootData:=(Classical.choose_spec data).2
  let r:=Classical.choose rootData
  have hr: r^2=algebraMap (field k i) (CriticalLiteralDouble.field k i) (u:field k i) :=
    (Classical.choose_spec rootData).1
  have hgen:Algebra.adjoin (field k i) {r}=⊤ := (Classical.choose_spec rootData).2.1
  have hres:evaluate v hv u=residue i e := (Classical.choose_spec rootData).2.2
  have eqv:=QuadraticRationalPlaceFibre.rationalFibreRootEquiv v hv u r hr hgen
    (CriticalDoublePointCount.degree_two k i hi h2) hu h2
  simpa only [hres] using eqv

theorem boundary_fibre_card (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (v:Place k (field k i)) (hv:v.IsRational) (hp:0<v.ord (shift i))
    (e:Fin 3→Bool)
    (ha:evaluate v hv (A i hi h2 v hp)=sign (e 0))
    (hb:evaluate v hv (B i hi h2 v hp)=sign (e 1))
    (hc:evaluate v hv (C i hi h2 v hp)=sign (e 2)) :
    Nat.card {w:Place k (CriticalLiteralDouble.field k i) //w.restrict (field k i)=v ∧ w.IsRational}=
      Nat.card {z:k //z^2=residue i e} :=
  Nat.card_congr (boundaryFibreEquiv i hi h2 v hv hp e ha hb hc)

end FourCorner.CriticalBoundaryFibre
#print axioms FourCorner.CriticalBoundaryFibre.boundaryFibreEquiv
#print axioms FourCorner.CriticalBoundaryFibre.boundary_fibre_card
