import CriticalRationalFibres
import CriticalDoublePointCount
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
namespace FourCorner.CriticalFiniteRationalPlaces
open AlgebraicCurve

/-- Every actual rational subfibre is a subtype of the genuine finite
place fibre, independently of whether any of its points are rational. -/
theorem fibre_finite {K F E:Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] (v:Place K F) :
    Finite {w:Place K E //w.restrict F=v ∧w.IsRational} := by
  classical
  let f:{w:Place K E //w.restrict F=v ∧w.IsRational}→↥(v.fiberOver E):=fun w=>⟨w.val,by
    have h:=Place.restrict_mem_fiberOver (F:=F) w.val
    rwa [w.property.1] at h⟩
  apply Finite.of_injective f
  intro w z he
  have hh:=congrArg (fun x:↥(v.fiberOver E)=>(x:Place K E)) he
  exact Subtype.ext hh

variable {k:Type*} [Field k]
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants i).toModule
local instance coverConstants (i:k) : Algebra k (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.targetConstants k i
local instance coverModule (i:k) : Module k (CriticalLiteralDouble.field k i) := (coverConstants i).toModule
local instance relative (i:k) : Algebra (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.relativeAlgebra k i
local instance relativeModule (i:k) : Module (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := (relative i).toModule
local instance tower (i:k) : IsScalarTower k (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.constants_base_tower k i

theorem base_finite [Finite k] (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    Finite {v:Place k (CriticalLiteralDouble.base k i) //v.IsRational} := by
  have he:{v:Place k (CriticalLiteralDouble.base k i) //v.IsRational} ≃
      {v:Place k (CriticalLiteralDouble.base k i) //v.deg=1} :=
    Equiv.subtypeEquivRight (fun v=>v.isRational_iff_deg_eq_one)
  letI:Finite {v:Place k (CriticalLiteralDouble.base k i) //v.deg=1}:=
    (CriticalFiniteGenus.hasse_bound k i hi h2).1.to_subtype
  exact Finite.of_equiv _ he.symm

theorem cover_finite [Finite k] (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    Finite {w:Place k (CriticalLiteralDouble.field k i) //w.IsRational} := by
  letI:=CriticalLiteralDouble.separable k i h2
  letI:=base_finite i hi h2
  letI (v:{v:Place k (CriticalLiteralDouble.base k i) //v.IsRational}):
      Finite {w:Place k (CriticalLiteralDouble.field k i) //w.restrict (CriticalLiteralDouble.base k i)=v.val ∧w.IsRational} :=
    fibre_finite v.val
  exact Finite.of_equiv _ (CriticalRationalFibres.sigmaEquiv (K:=k)
    (F:=CriticalLiteralDouble.base k i) (E:=CriticalLiteralDouble.field k i)).symm

end FourCorner.CriticalFiniteRationalPlaces
#print axioms FourCorner.CriticalFiniteRationalPlaces.fibre_finite
#print axioms FourCorner.CriticalFiniteRationalPlaces.base_finite
#print axioms FourCorner.CriticalFiniteRationalPlaces.cover_finite
