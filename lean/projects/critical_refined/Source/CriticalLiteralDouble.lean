import CriticalProductNonsquare
import CriticalProductOrders
import CriticalGeometricGenus
import CriticalFieldConstants

noncomputable section
namespace FourCorner.CriticalLiteralDouble
open AlgebraicCurve Polynomial
variable (k:Type*) [Field k]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 40000

abbrev base (i:k) := CriticalRadicalField.field k i
def radicand (i:k) : base k i := 2*CriticalProductValuation.f i
abbrev field (i:k) := Multiquadratic.Tower.first (base k i) (radicand k i)
def root (i:k) : field k i := Multiquadratic.Tower.stepRoot₁ (base k i) (radicand k i)

local instance baseConstants (i:k) : Algebra k (base k i) :=
  CriticalFieldConstants.constantAlgebra k i
local instance baseModule (i:k) : Module k (base k i) := (baseConstants k i).toModule
local instance basePolynomials (i:k) : Algebra k[X] (base k i) :=
  ((algebraMap (RatFunc k) (base k i)).comp (algebraMap k[X] (RatFunc k))).toAlgebra
local instance targetConstants (i:k) : Algebra k (field k i) :=
  ((algebraMap (base k i) (field k i)).comp (algebraMap k (base k i))).toAlgebra
local instance targetModule (i:k) : Module k (field k i) := (targetConstants k i).toModule
local instance targetLine (i:k) : Algebra (RatFunc k) (field k i) :=
  ((algebraMap (base k i) (field k i)).comp (algebraMap (RatFunc k) (base k i))).toAlgebra
local instance targetLineModule (i:k) : Module (RatFunc k) (field k i) := (targetLine k i).toModule
local instance relativeAlgebra (i:k) : Algebra (base k i) (field k i) :=
  (field k i).toSubalgebra.algebra
local instance relativeModule (i:k) : Module (base k i) (field k i) := (relativeAlgebra k i).toModule
local instance constants_base_tower (i:k) : IsScalarTower k (base k i) (field k i) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
local instance line_base_tower (i:k) : IsScalarTower (RatFunc k) (base k i) (field k i) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
local instance constants_line_tower (i:k) : IsScalarTower k (RatFunc k) (field k i) := by
  apply IsScalarTower.of_algebraMap_eq'
  ext x
  rfl

theorem root_square (i:k) : root k i^2=algebraMap (base k i) (field k i) (radicand k i) :=
  Multiquadratic.Tower.stepRoot₁_sq (base k i) (radicand k i)

theorem root_generates (i:k) : Algebra.adjoin (base k i) {root k i}=⊤ :=
  Multiquadratic.Tower.stepRoot₁_generates (base k i) (radicand k i)

theorem radicand_ne_zero (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) : radicand k i≠0 := by
  have h2F : (2:base k i)≠0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap k (base k i))).mpr h2
  exact mul_ne_zero h2F (CriticalProductValuation.nonzero i hi h2).1

theorem finite_over_line (i:k) : FiniteDimensional (RatFunc k) (field k i) :=
  FiniteDimensional.trans (RatFunc k) (base k i) (field k i)

theorem isCurveOver [PerfectField k] (i:k) : IsCurveOver k (field k i) := by
  letI := finite_over_line k i
  exact RatFuncFiniteExtension.isCurveOver_of_perfectField k (field k i)

theorem separable (i:k) (h2:(2:k)≠0) : Algebra.IsSeparable (base k i) (field k i) := by
  have h2F : (2:base k i)≠0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap k (base k i))).mpr h2
  exact RadicalSeparable.primitive (root_square k i) (root_generates k i) h2F

local instance separated [NeZero (2:k)] (i:k) : Algebra.IsSeparable (base k i) (field k i) := separable k i (NeZero.ne (2:k))

/-- All actual places of the literal root extension, including projective boundary
places, have unit different and ramification index one. -/
theorem unramified [NeZero (2:k)] (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) (w:Place k (field k i)) :
    differentIdeal (w.restrict (base k i)).toValuationSubring
      (Place.integralClosureAt (field k i) (w.restrict (base k i)))=⊤ ∧
    w.ramificationIndex (base k i)=1 := by
  letI : NeZero (2:k) := ⟨h2⟩
  letI := separable k i h2
  exact OddQuadraticParity.even_order w (root_square k i) (root_generates k i)
    (radicand_ne_zero k i hi h2) (CriticalProductOrders.all_places_even i hi h2 _)

theorem degree_two [IsAlgClosed k] (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    Module.finrank (base k i) (field k i)=2 :=
  Multiquadratic.Tower.finrank_first (base k i) (radicand k i)
    (CriticalProductNonsquare.literal_product_nonsquare i hi h2)

/-- Genuine RH on the specified root extension, over every algebraically closed
constant field of characteristic different from two. -/
theorem genus_one [IsAlgClosed k] (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    genusFF k (field k i)=1 := by
  classical
  letI : NeZero (2:k):=⟨h2⟩
  letI : PerfectField k:=IsAlgClosed.perfectField k
  letI := separable k i h2
  letI := finite_over_line k i
  letI := CriticalRadicalField.isCurveOver k i
  letI := isCurveOver k i
  have he (w:Place k (field k i)) : w.ramificationIndex (base k i)=1 :=
    (unramified k i hi h2 w).2
  have htame (w:Place k (field k i)) : ((w.ramificationIndex (base k i):ℕ):k)≠0 := by
    rw [he]
    simpa only [Nat.cast_one] using (one_ne_zero : (1:k)≠0)
  have hsum : (∑ᶠ w:Place k (field k i), ((w.ramificationIndex (base k i):ℤ)-1))=0 := by
    simp only [he,Nat.cast_one,sub_self,finsum_zero]
  have hrh := two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame
    (RatFuncFiniteExtension.oneVariable k (base k i)) htame
  rw [degree_two k i hi h2,CriticalGeometricGenus.genus_one i hi h2,hsum] at hrh
  omega

#print axioms root_square
#print axioms root_generates
#print axioms finite_over_line
#print axioms unramified
#print axioms degree_two
#print axioms genus_one
end FourCorner.CriticalLiteralDouble
