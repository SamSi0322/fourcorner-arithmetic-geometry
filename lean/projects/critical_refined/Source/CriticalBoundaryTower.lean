import RationalLineEvaluation
import CriticalBoundaryResidues
import CriticalActualRamification

noncomputable section
namespace FourCorner.CriticalBoundaryTower
open AlgebraicCurve FourCorner.Multiquadratic CriticalRadicalField
variable {k : Type*} [Field k]
abbrev Line := RatFunc k
abbrev First (i : k) := Tower.first (RatFunc k) (radicandB k i)
abbrev Full (i : k) := CriticalRadicalField.field k i

instance relativeAlgebra (i : k) : Algebra (First i) (Full i) :=
  Tower.algebra₁₂ (RatFunc k) (radicandB k i) (radicandC k i)
instance relativeModule (i : k) : Module (First i) (Full i) := (relativeAlgebra i).toModule

def firstRoot (i : k) : First i := Tower.stepRoot₁ (RatFunc k) (radicandB k i)

instance constants_first_full (i : k) : IsScalarTower k (First i) (Full i) :=
  IsScalarTower.to₁₃₄ k (RatFunc k) (First i) (Full i)

theorem first_square (i : k) : firstRoot i^2=algebraMap (RatFunc k) (First i) (radicandB k i) :=
  Tower.stepRoot₁_sq _ _
theorem first_generates (i : k) : Algebra.adjoin (RatFunc k) {firstRoot i}=⊤ :=
  Tower.stepRoot₁_generates _ _
theorem second_generates (i : k) : Algebra.adjoin (First i) {c k i}=⊤ :=
  Tower.stepRoot₂_generates _ _ _
theorem second_square (i : k) : c k i^2=algebraMap (First i) (Full i)
    (algebraMap (RatFunc k) (First i) (radicandC k i)) := Tower.stepRoot₂_sq _ _ _

theorem first_degree (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) :
    Module.finrank (RatFunc k) (First i)=2 :=
  Tower.finrank_first _ _ (CriticalSquareclasses.independent i hi h2).first

theorem second_degree (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) :
    Module.finrank (First i) (Full i)=2 := by
  apply Biquadratic.finrank_step₂
  · simpa only [map_ofNat] using (map_ne_zero (algebraMap k (RatFunc k))).mpr h2
  · exact CriticalSquareclasses.independent i hi h2

theorem first_separable (i : k) (h2 : (2:k)≠0) : Algebra.IsSeparable (RatFunc k) (First i) := by
  apply RadicalSeparable.primitive (first_square i) (first_generates i)
  simpa only [map_ofNat] using (map_ne_zero (algebraMap k (RatFunc k))).mpr h2

theorem second_separable (i : k) (h2 : (2:k)≠0) : Algebra.IsSeparable (First i) (Full i) := by
  apply RadicalSeparable.primitive (second_square i) (second_generates i)
  simpa only [map_ofNat] using (map_ne_zero (algebraMap k (First i))).mpr h2

#print axioms first_degree
#print axioms second_degree
#print axioms second_separable
end FourCorner.CriticalBoundaryTower
