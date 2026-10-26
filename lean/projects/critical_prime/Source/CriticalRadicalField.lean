import CriticalAffineBaseChange
import geometry.RatFuncFiniteExtension

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open Polynomial
namespace FourCorner.CriticalRadicalField
variable (k : Type*) [Field k]

abbrev radicandB (i : k) : RatFunc k :=
  algebraMap k[X] (RatFunc k) (CriticalSquareclasses.qB i)
abbrev radicandC (i : k) : RatFunc k :=
  algebraMap k[X] (RatFunc k) (CriticalSquareclasses.qC i)
abbrev field (i : k) := Biquadratic.field (RatFunc k) (radicandB k i) (radicandC k i)
abbrev tower (i : k) := CriticalAffineTower.tower i

instance constants_line_tower (i : k) : IsScalarTower k (RatFunc k) (field k i) := by
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  rfl

theorem finite_over_line (i : k) : FiniteDimensional (RatFunc k) (field k i) := inferInstance

theorem degree_four (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) :
    Module.finrank (RatFunc k) (field k i) = 4 := by
  have h2F : (2:RatFunc k)≠0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap k (RatFunc k))).mpr h2
  exact Biquadratic.finrank_field (RatFunc k) _ _ h2F
    (CriticalSquareclasses.independent i hi h2)

def a (i : k) : field k i := algebraMap (RatFunc k) (field k i) RatFunc.X
def b (i : k) : field k i := Biquadratic.root₁ (RatFunc k) (radicandB k i) (radicandC k i)
def c (i : k) : field k i := Biquadratic.root₂ (RatFunc k) (radicandB k i) (radicandC k i)

theorem polynomial_constants (i z : k) :
    algebraMap (RatFunc k) (field k i) (algebraMap k[X] (RatFunc k) (C z)) =
      algebraMap k (field k i) z := by
  change algebraMap (RatFunc k) (field k i)
    (algebraMap k[X] (RatFunc k) (algebraMap k k[X] z)) = _
  rw [←IsScalarTower.algebraMap_apply k k[X] (RatFunc k),
    ←IsScalarTower.algebraMap_apply k (RatFunc k) (field k i)]

def polynomialValue (i : k) : k[X] →+* field k i :=
  (algebraMap (RatFunc k) (field k i)).comp (algebraMap k[X] (RatFunc k))

@[simp] theorem polynomialValue_C (i z : k) :
    polynomialValue k i (C z) = algebraMap k (field k i) z :=
  polynomial_constants k i z
@[simp] theorem polynomialValue_X (i : k) : polynomialValue k i X = a k i := rfl

theorem b_squared (i : k) : b k i ^ 2 =
    algebraMap k (field k i) i * a k i ^ 2 + algebraMap k (field k i) (1-i) := by
  rw [b,Biquadratic.root₁_sq]
  change polynomialValue k i (CriticalSquareclasses.qB i) = _
  simp only [CriticalSquareclasses.qB,CriticalSquareclasses.quadratic,
    map_add,map_mul,map_pow,polynomialValue_C,polynomialValue_X]

theorem c_squared (i : k) : c k i ^ 2 =
    algebraMap k (field k i) (1+i) * a k i ^ 2 - algebraMap k (field k i) i := by
  rw [c,Biquadratic.root₂_sq]
  change polynomialValue k i (CriticalSquareclasses.qC i) = _
  simp only [CriticalSquareclasses.qC,CriticalSquareclasses.quadratic,
    map_add,map_mul,map_pow,polynomialValue_C,polynomialValue_X,map_neg,sub_eq_add_neg]

theorem actual_critical_equations (i : k) :
    b k i ^ 2 - 1 = algebraMap k (field k i) i * (a k i ^ 2 - 1) ∧
    c k i ^ 2 - 1 = algebraMap k (field k i) (1+i) * (a k i ^ 2 - 1) := by
  rw [b_squared,c_squared]
  simp only [map_sub,map_one,map_add]
  constructor <;> ring

theorem a_transcendental (i : k) : Transcendental k (a k i) :=
  RatFuncFiniteExtension.transcendental_X k (field k i)

theorem isCurveOver [PerfectField k] (i : k) : AlgebraicCurve.IsCurveOver k (field k i) :=
  RatFuncFiniteExtension.isCurveOver_of_perfectField k (field k i)

theorem essFiniteType (i : k) : Algebra.EssFiniteType k (field k i) :=
  RatFuncFiniteExtension.essFiniteType k (field k i)

end FourCorner.CriticalRadicalField
#print axioms FourCorner.CriticalRadicalField.degree_four
#print axioms FourCorner.CriticalRadicalField.actual_critical_equations
#print axioms FourCorner.CriticalRadicalField.a_transcendental
#print axioms FourCorner.CriticalRadicalField.isCurveOver
#print axioms FourCorner.CriticalRadicalField.essFiniteType
