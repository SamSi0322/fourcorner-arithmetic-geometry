import CriticalActualBoundaryCount
import CriticalOffBoundaryFibre
import CriticalFiniteRationalPlaces
import FiniteFibreCounting

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 40000
attribute [local instance] Classical.propDecidable
namespace FourCorner.CriticalGlobalFibreCount
open AlgebraicCurve CriticalRadicalField
variable {k:Type*} [Field k] [Fintype k] [DecidableEq k]
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants i).toModule
local instance coverConstants (i:k) : Algebra k (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.targetConstants k i
local instance coverModule (i:k) : Module k (CriticalLiteralDouble.field k i) := (coverConstants i).toModule
local instance relative (i:k) : Algebra (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.relativeAlgebra k i
local instance relativeModule (i:k) : Module (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := (relative i).toModule
local instance tower (i:k) : IsScalarTower k (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.constants_base_tower k i

abbrev RationalBase (i:k):={v:Place k (field k i) //v.IsRational}
abbrev RationalCover (i:k):={w:Place k (CriticalLiteralDouble.field k i) //w.IsRational}
def isBoundary (i:k) (v:RationalBase i):Prop:=0<v.val.ord (CriticalBoundaryResidues.shift i)
def positiveCharacter (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) (v:RationalBase i):Prop:=
  CriticalOffBoundaryFibre.character i hi h2 v.val v.property=1
abbrev GoodBase (i:k) (hi:i^2 = -1) (h2:(2:k)≠0):=
  {v:RationalBase i //¬isBoundary i v ∧positiveCharacter i hi h2 v}

/-- Exact total count using EVERY actual rational place, with boundary and
nonboundary fibres decomposed by actual restriction to the original field. -/
theorem total_count (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    Nat.card (RationalCover i)=Nat.card (CriticalActualBoundaryCount.Boundary i)+
      2*Nat.card (GoodBase i hi h2) := by
  classical
  letI:=CriticalLiteralDouble.separable k i h2
  letI:=CriticalFiniteRationalPlaces.base_finite i hi h2
  letI:Fintype (RationalBase i):=Fintype.ofFinite _
  let β:=fun v:RationalBase i=>
    {w:Place k (CriticalLiteralDouble.field k i) //w.restrict (field k i)=v.val ∧w.IsRational}
  letI(v:RationalBase i):Finite (β v):=CriticalFiniteRationalPlaces.fibre_finite v.val
  have h0:=FiniteFibreCounting.boundary_and_two β (isBoundary i) (positiveCharacter i hi h2)
    (by
      intro v hv
      have hf:=CriticalOffBoundaryFibre.fibre_card i hi h2 v.val v.property hv
      by_cases hc:positiveCharacter i hi h2 v
      · rw [if_pos hc]
        have he:CriticalOffBoundaryFibre.character i hi h2 v.val v.property=1:=hc
        simpa only [β,if_pos he] using hf
      · rw [if_neg hc]
        have he:¬CriticalOffBoundaryFibre.character i hi h2 v.val v.property=1:=hc
        simpa only [β,if_neg he] using hf)
  have htotal:Nat.card (RationalCover i)=Nat.card (Σv:RationalBase i,β v) :=
    Nat.card_congr (CriticalRationalFibres.sigmaEquiv (K:=k) (F:=field k i) (E:=CriticalLiteralDouble.field k i))
  let eb:{v:RationalBase i //isBoundary i v} ≃ CriticalBoundaryClassification.Boundary i :=
    {toFun:=fun v=>⟨v.val.val,v.val.property,v.property⟩
     invFun:=fun v=>⟨⟨v.val,v.property.1⟩,v.property.2⟩
     left_inv:=by intro v;cases v;rfl
     right_inv:=by intro v;cases v;rfl}
  let es:(Σv:{v:RationalBase i //isBoundary i v},β v.val) ≃
      Σv:CriticalBoundaryClassification.Boundary i,
        {w:Place k (CriticalLiteralDouble.field k i) //w.restrict (field k i)=v.val ∧w.IsRational}:=
    Equiv.sigmaCongr eb (fun _=>Equiv.refl _)
  have hb:Nat.card (Σv:{v:RationalBase i //isBoundary i v},β v.val)=
      Nat.card (CriticalActualBoundaryCount.Boundary i) := by
    rw [Nat.card_congr es]
    exact (Nat.card_congr (CriticalRationalFibres.sigmaOverEquiv (K:=k) (F:=field k i)
      (E:=CriticalLiteralDouble.field k i) (fun v=>0<v.ord (CriticalBoundaryResidues.shift i)))).symm
  exact htotal.trans (h0.trans (congrArg (fun n=>n+2*Nat.card (GoodBase i hi h2)) hb))

theorem good_count (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    Nat.card (GoodBase i hi h2)=
      (Nat.card (RationalCover i)-Nat.card (CriticalActualBoundaryCount.Boundary i))/2 := by
  have h:=total_count i hi h2
  omega

end FourCorner.CriticalGlobalFibreCount
#print axioms FourCorner.CriticalGlobalFibreCount.total_count
#print axioms FourCorner.CriticalGlobalFibreCount.good_count
