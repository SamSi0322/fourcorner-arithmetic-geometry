import CriticalOffBoundaryUnit
import CriticalBoundaryFibre
import CriticalProjectiveBoundary

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 40000
namespace FourCorner.CriticalOffBoundaryFibre
open AlgebraicCurve CriticalRadicalField ResiduePlaceEvaluation CriticalProjectiveResidues
variable {k:Type*} [Field k]
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants i).toModule
local instance coverConstants (i:k) : Algebra k (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.targetConstants k i
local instance coverModule (i:k) : Module k (CriticalLiteralDouble.field k i) := (coverConstants i).toModule
local instance relative (i:k) : Algebra (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.relativeAlgebra k i
local instance relativeModule (i:k) : Module (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := (relative i).toModule
local instance tower (i:k) : IsScalarTower k (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.constants_base_tower k i

def fibreEquiv (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (v:Place k (field k i)) (hv:v.IsRational)
    (hb:¬0<v.ord (CriticalBoundaryResidues.shift i)) :
    {w:Place k (CriticalLiteralDouble.field k i) //w.restrict (field k i)=v ∧w.IsRational} ≃
      {z:k //z^2=2*CriticalProjectiveCharacter.product (vector i hi h2 v hv)} := by
  letI:=CriticalLiteralDouble.separable k i h2
  let data:=CriticalOffBoundaryUnit.off_boundary_unit i hi h2 v hv hb
  let u:=Classical.choose data
  have hu:IsUnit u := (Classical.choose_spec data).1
  let rootData:=(Classical.choose_spec data).2
  let r:=Classical.choose rootData
  have hr:r^2=algebraMap (field k i) (CriticalLiteralDouble.field k i) (u:field k i) := (Classical.choose_spec rootData).1
  have hgen:Algebra.adjoin (field k i) {r}=⊤ := (Classical.choose_spec rootData).2.1
  have hres:evaluate v hv u=2*CriticalProjectiveCharacter.product (vector i hi h2 v hv) := (Classical.choose_spec rootData).2.2
  have eqv:=QuadraticRationalPlaceFibre.rationalFibreRootEquiv v hv u r hr hgen
    (CriticalDoublePointCount.degree_two k i hi h2) hu h2
  simpa only [hres] using eqv

theorem product_nonzero (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (v:Place k (field k i)) (hv:v.IsRational)
    (hb:¬0<v.ord (CriticalBoundaryResidues.shift i)) :
    2*CriticalProjectiveCharacter.product (vector i hi h2 v hv)≠0 := by
  obtain ⟨u,hu,r,hr,hgen,hres⟩:=CriticalOffBoundaryUnit.off_boundary_unit i hi h2 v hv hb
  have hz: evaluate v hv u≠0 := (ResidueValuationFacts.evaluate_nonzero_iff_unit v hv u).mpr hu
  rwa [hres] at hz

section Character
variable [Fintype k] [DecidableEq k]
def character (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (v:Place k (field k i)) (hv:v.IsRational) : ℤ :=
  quadraticChar k (2*CriticalProjectiveCharacter.product (vector i hi h2 v hv))

/-- EVERY nonboundary actual rational fibre has exactly two points for the
original projective character+1, and zero otherwise, with poles included. -/
theorem fibre_card (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (v:Place k (field k i)) (hv:v.IsRational)
    (hb:¬0<v.ord (CriticalBoundaryResidues.shift i)) :
    Nat.card {w:Place k (CriticalLiteralDouble.field k i) //w.restrict (field k i)=v ∧w.IsRational}=
      if character i hi h2 v hv=1 then 2 else 0 := by
  rw [Nat.card_congr (fibreEquiv i hi h2 v hv hb)]
  have hn:=product_nonzero i hi h2 v hv hb
  have he:character i hi h2 v hv=1 ↔ IsSquare (2*CriticalProjectiveCharacter.product (vector i hi h2 v hv)) :=
    quadraticChar_one_iff_isSquare hn
  split_ifs with hc
  · exact CriticalBoundaryRootCounts.card_square_roots _ hn h2 (he.mp hc)
  · exact CriticalBoundaryRootCounts.card_nonsquare_roots _ (fun h=>hc (he.mpr h))
end Character

end FourCorner.CriticalOffBoundaryFibre
#print axioms FourCorner.CriticalOffBoundaryFibre.fibreEquiv
#print axioms FourCorner.CriticalOffBoundaryFibre.product_nonzero
#print axioms FourCorner.CriticalOffBoundaryFibre.fibre_card
