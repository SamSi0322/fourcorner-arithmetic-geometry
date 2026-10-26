import CriticalDoubleFieldIso
import CriticalFiniteGenus
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_algEquiv

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
namespace FourCorner.CriticalDoublePointCount
open AlgebraicCurve
variable (k:Type*) [Field k]
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants k i).toModule
local instance coverConstants (i:k) : Algebra k (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.targetConstants k i
local instance coverModule (i:k) : Module k (CriticalLiteralDouble.field k i) := (coverConstants k i).toModule
local instance relative (i:k) : Algebra (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.relativeAlgebra k i
local instance relativeModule (i:k) : Module (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := (relative k i).toModule

/-- The original specified cover has exactly the actual degree-one places of
native E. This is a proved field/place equivalence, not isogeny-count input. -/
def degreeOneEquiv (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    {w:Place k (CriticalLiteralDouble.field k i) //w.deg=1} ≃
      {v:Place k (CriticalEllipticField.field k) //v.deg=1} :=
  (Place.congrEquiv (CriticalDoubleFieldIso.equiv k i hi h2).toRingEquiv
    (CriticalDoubleFieldIso.equiv k i hi h2).commutes).subtypeEquiv
    (fun w=>by rw [Place.congrEquiv_apply,Place.deg_congrRingEquiv])

theorem point_count_eq (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    Nat.card {w:Place k (CriticalLiteralDouble.field k i) //w.deg=1}=
      Nat.card {v:Place k (CriticalEllipticField.field k) //v.deg=1} :=
  Nat.card_congr (degreeOneEquiv k i hi h2)

/-- Degree two holds over every original constant field, with no closure
hypothesis, by the actual arbitrary-base nonsquareness proof. -/
theorem degree_two (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    Module.finrank (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i)=2 :=
  Multiquadratic.Tower.finrank_first (CriticalLiteralDouble.base k i)
    (CriticalLiteralDouble.radicand k i) (CriticalDoubleNonsquare.original_product_nonsquare k i hi h2)

/-- Finite-base genus one follows from the same actual E/literal-Ci
isomorphisms and the accepted unconditional finite-base genus theorem. -/
theorem genus_one_finite [Finite k] (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    genusFF k (CriticalLiteralDouble.field k i)=1 := by
  have h1:=genusFF_eq_of_algEquiv (CriticalDoubleFieldIso.equiv k i hi h2)
  have h2g:=genusFF_eq_of_algEquiv (CriticalOriginalFieldEquiv.equiv k i hi h2)
  exact h1.trans (h2g.trans (CriticalFiniteGenus.genus_one k i hi h2))

end FourCorner.CriticalDoublePointCount
#print axioms FourCorner.CriticalDoublePointCount.degreeOneEquiv
#print axioms FourCorner.CriticalDoublePointCount.point_count_eq
#print axioms FourCorner.CriticalDoublePointCount.degree_two
#print axioms FourCorner.CriticalDoublePointCount.genus_one_finite
