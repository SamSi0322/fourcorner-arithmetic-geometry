import TensorAlgebraicConstants
import FunctionFieldIntegralConstants
import ResidueGeometricField

noncomputable section
open AlgebraicCurve
open scoped TensorProduct
namespace FourCorner.ResidueFullConstants
variable (K : Type*) [Field K] [PerfectField K] [NeZero (2 : K)]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

/-- The actual residue radical field has exactly the given constants,
derived independently of any rational-place existence or Hasse--Weil bound. -/
theorem constantsAreBase {t κ : K} (h0 : t ≠ 0) (h1 : t ≠ 1)
    (hm : t ≠ -1) (hκ : κ ≠ 0) :
    ConstantsAreBase K (CommonGenus17Field.field K t κ) := by
  let F := CommonGenus17Field.field K t κ
  letI := ResidueRadicalField.finite_over_line K t κ
  letI := ResidueGeometricField.all_constants_domain K (AlgebraicClosure K) h0 h1 hm hκ
  change LSpace (0 : Divisor K F) = LinearMap.range (Algebra.linearMap K F)
  apply le_antisymm
  · intro x hx
    obtain ⟨c,hc⟩ := TensorAlgebraicConstants.integral_is_base
      (FunctionFieldIntegralConstants.lSpace_zero_integral K F hx)
    exact ⟨c,hc⟩
  · rintro x ⟨c,rfl⟩
    exact algebraMap_mem_lSpace_zero c

end FourCorner.ResidueFullConstants
#print axioms FourCorner.ResidueFullConstants.constantsAreBase
