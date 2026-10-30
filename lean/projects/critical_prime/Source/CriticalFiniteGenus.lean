import CriticalConstantFieldComparison
import CriticalGeometricGenus
import GeometricFrobeniusTransport
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed
import SharpPointBound

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicCurve
open scoped TensorProduct
namespace FourCorner.CriticalFiniteGenus
open CriticalRadicalField
variable (k : Type*) [Field k] [Finite k]
local instance constantAlgebra (i : k) : Algebra k (field k i) :=
  CriticalFieldConstants.constantAlgebra k i
local instance constantModule (i : k) : Module k (field k i) :=
  CriticalFieldConstants.constantModule k i

/-- The actual finite-base genus is obtained by transporting the genuine
constant tensor and its Frobenius to the literal algebraically closed model.
No finite-base genus or Frobenius datum is assumed. -/
theorem genus_one (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) :
    genusFF k (field k i) = 1 := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  let L := AlgebraicClosure k
  let F0 := field k i
  let F := field L (algebraMap k L i)
  letI : PerfectField k := PerfectField.ofFinite
  letI : PerfectField L := IsAlgClosed.perfectField L
  letI : Algebra L F := CriticalFieldConstants.constantAlgebra L (algebraMap k L i)
  letI : Module L F := CriticalFieldConstants.constantModule L (algebraMap k L i)
  letI : IsDomain (L ⊗[k] F0) := CriticalFieldConstants.field_tensor_domain k i hi h2 L
  let e : FractionRing (L ⊗[k] F0) ≃ₐ[L] F :=
    CriticalConstantFieldComparison.fractionFieldEquiv k L i hi h2
  letI : Algebra F0 F := GeometricTensorFrobenius.imageAlgebra k L F0 F e
  letI : IsCurveOver k F0 := CriticalRadicalField.isCurveOver k i
  letI : IsCurveOver L F := CriticalRadicalField.isCurveOver L (algebraMap k L i)
  have hfg : ∃ s : Finset F0, IntermediateField.adjoin k (s:Set F0) = ⊤ := by
    exact IntermediateField.fg_top_iff.mpr (CriticalRadicalField.essFiniteType k i)
  have hdesc := genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed
    k L F0 F hfg (GeometricTensorFrobenius.image_algebra_generates k L F0 F e)
    (GeometricTensorFrobenius.transportedFrobenius k L F0 F e)
    (GeometricTensorFrobenius.transportedFrobenius_algebraMap k L F0 F e)
    (CriticalFieldConstants.constantsAreBase k i hi h2)
  have hL := CriticalConstantFieldComparison.mapped_hypotheses k L i hi h2
  have hg : genusFF L F = 1 := CriticalGeometricGenus.genus_one (K:=L) _ hL.1 hL.2
  exact hdesc.symm.trans hg

/-- Hasse--Weil now applies to the actual degree-one places of the original
finite-constant field. Its full constants and genus have both been proved. -/
theorem hasse_bound (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) :
    {w : Place k (field k i) | w.deg = 1}.Finite ∧
    |(Nat.card {w : Place k (field k i) | w.deg = 1}:ℝ) - ((Nat.card k:ℝ)+1)| ≤
      2 * Real.sqrt (Nat.card k:ℝ) := by
  letI : PerfectField k := PerfectField.ofFinite
  letI : IsCurveOver k (field k i) := CriticalRadicalField.isCurveOver k i
  letI : Algebra.EssFiniteType k (field k i) := CriticalRadicalField.essFiniteType k i
  have h := finite_degree_one_places_and_hasseWeil_bound k (field k i)
    (CriticalFieldConstants.constantsAreBase k i hi h2)
  simpa only [genus_one k i hi h2,Nat.cast_one,mul_one] using h

end FourCorner.CriticalFiniteGenus
#print axioms FourCorner.CriticalFiniteGenus.genus_one
#print axioms FourCorner.CriticalFiniteGenus.hasse_bound
