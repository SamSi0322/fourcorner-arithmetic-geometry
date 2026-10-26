import CriticalDoubleFieldIso
import CriticalConstantFieldComparison
import CriticalGeometricGenus
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_algEquiv

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 40000
open scoped TensorProduct
namespace FourCorner.CriticalDoubleGeometricGenus
open AlgebraicCurve
variable (k:Type*) [Field k]
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants k i).toModule
local instance coverConstants (i:k) : Algebra k (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.targetConstants k i
local instance coverModule (i:k) : Module k (CriticalLiteralDouble.field k i) := (coverConstants k i).toModule

/-- Absolute constant-field isomorphism, with both curves still retaining
their already proved distinct original degree-two relative base embedding. -/
def absoluteEquiv (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    CriticalLiteralDouble.field k i ≃ₐ[k] CriticalLiteralDouble.base k i :=
  (CriticalDoubleFieldIso.equiv k i hi h2).trans (CriticalOriginalFieldEquiv.equiv k i hi h2)

variable (L:Type*) [Field L] [Algebra k L]

def tensorEquiv (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    (L⊗[k]CriticalLiteralDouble.field k i) ≃ₐ[L] (L⊗[k]CriticalLiteralDouble.base k i) := by
  let e:=Algebra.TensorProduct.congr (AlgEquiv.refl : L≃ₐ[k]L) (absoluteEquiv k i hi h2)
  apply AlgEquiv.ofRingEquiv (f:=e.toRingEquiv)
  intro l
  change e (l⊗ₜ[k](1:CriticalLiteralDouble.field k i))=l⊗ₜ[k](1:CriticalLiteralDouble.base k i)
  simp [e,Algebra.TensorProduct.congr]

theorem tensor_domain (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    IsDomain (L⊗[k]CriticalLiteralDouble.field k i) := by
  letI:=CriticalFieldConstants.field_tensor_domain k i hi h2 L
  exact Function.Injective.isDomain (tensorEquiv k L i hi h2).toRingHom (tensorEquiv k L i hi h2).injective

/-- The ACTUAL field-constant tensor of the specified original cover has
geometric genus one, over every original constant field and every algebraically
closed extension. No finite, perfect, or characteristic-zero premise occurs. -/
theorem geometric_genus_one [IsAlgClosed L] (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    letI:=tensor_domain k L i hi h2
    genusFF L (FractionRing (L⊗[k]CriticalLiteralDouble.field k i))=1 := by
  letI:=tensor_domain k L i hi h2
  letI:=CriticalFieldConstants.field_tensor_domain k i hi h2 L
  let e1:FractionRing (L⊗[k]CriticalLiteralDouble.field k i) ≃ₐ[L]
      FractionRing (L⊗[k]CriticalLiteralDouble.base k i):=
    IsFractionRing.algEquivOfAlgEquiv (tensorEquiv k L i hi h2)
  let e2:=CriticalConstantFieldComparison.fractionFieldEquiv k L i hi h2
  have hg:=CriticalConstantFieldComparison.mapped_hypotheses k L i hi h2
  exact (genusFF_eq_of_algEquiv (e1.trans e2)).trans
    (CriticalGeometricGenus.genus_one (K:=L) (algebraMap k L i) hg.1 hg.2)

end FourCorner.CriticalDoubleGeometricGenus
#print axioms FourCorner.CriticalDoubleGeometricGenus.absoluteEquiv
#print axioms FourCorner.CriticalDoubleGeometricGenus.tensorEquiv
#print axioms FourCorner.CriticalDoubleGeometricGenus.tensor_domain
#print axioms FourCorner.CriticalDoubleGeometricGenus.geometric_genus_one
