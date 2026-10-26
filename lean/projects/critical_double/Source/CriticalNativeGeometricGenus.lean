import CriticalDoubleGeometricGenus
import CriticalDoubleOriginalMap

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory AlgebraicCurve
universe u v
namespace FourCorner.CriticalNativeGeometricGenus

section Tensor
variable {k F G L:Type*} [Field k] [Field F] [Field G] [Field L]
  [Algebra k F] [Algebra k G] [Algebra k L]
def tensorIso (e:F≃ₐ[k]G) : L⊗[k]F≃ₐ[L]L⊗[k]G :=
  Algebra.TensorProduct.congr (AlgEquiv.refl:L≃ₐ[L]L) e

theorem domain_of_equiv (e:F≃ₐ[k]G) [IsDomain (L⊗[k]G)] : IsDomain (L⊗[k]F) :=
  Function.Injective.isDomain (tensorIso (L:=L) e).toRingHom (tensorIso (L:=L) e).injective

theorem genus_congr (e:F≃ₐ[k]G) [IsDomain (L⊗[k]F)] [IsDomain (L⊗[k]G)] :
    genusFF L (FractionRing (L⊗[k]F))=genusFF L (FractionRing (L⊗[k]G)) :=
  genusFF_eq_of_algEquiv (IsFractionRing.algEquivOfAlgEquiv (tensorIso (L:=L) e))
end Tensor

variable {k:Type u} [Field k] (L:Type v) [Field L] [Algebra k L]
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants i).toModule
local instance coverConstants (i:k) : Algebra k (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.targetConstants k i
local instance coverModule (i:k) : Module k (CriticalLiteralDouble.field k i) := (coverConstants i).toModule

theorem cover_domain (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    letI:=EllipticQuarticModel.integral k
    letI:=SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
    IsDomain (L⊗[k](EllipticQuarticModel.curve k).functionField) := by
  letI:=EllipticQuarticModel.integral k
  letI:=SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
  letI:=CriticalDoubleGeometricGenus.tensor_domain k L i hi h2
  exact domain_of_equiv (L:=L) (CriticalDoubleModel.fieldEquiv i hi h2).symm

theorem cover_genus_one [IsAlgClosed L] (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    letI:=EllipticQuarticModel.integral k
    letI:=SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
    letI:=cover_domain L i hi h2
    genusFF L (FractionRing (L⊗[k](EllipticQuarticModel.curve k).functionField))=1 := by
  letI:=EllipticQuarticModel.integral k
  letI:=SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
  letI:=cover_domain L i hi h2
  letI:=CriticalDoubleGeometricGenus.tensor_domain k L i hi h2
  exact (genus_congr (L:=L) (CriticalDoubleModel.fieldEquiv i hi h2).symm).trans
    (CriticalDoubleGeometricGenus.geometric_genus_one k L i hi h2)

theorem base_domain (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    letI:=CriticalAffineDomain.ring_isDomain i hi h2
    letI:=CriticalProjectiveIntegral.projective_integral i hi h2
    letI:=SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
    IsDomain (L⊗[k](CriticalProj23.criticalCurve i).functionField) := by
  letI:=CriticalAffineDomain.ring_isDomain i hi h2
  letI:=CriticalProjectiveIntegral.projective_integral i hi h2
  letI:=SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
  letI:=CriticalFieldConstants.field_tensor_domain k i hi h2 L
  exact domain_of_equiv (L:=L) (CriticalDoubleOriginalMap.baseFieldEquiv i hi h2).symm

theorem base_genus_one [IsAlgClosed L] (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    letI:=CriticalAffineDomain.ring_isDomain i hi h2
    letI:=CriticalProjectiveIntegral.projective_integral i hi h2
    letI:=SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
    letI:=base_domain L i hi h2
    genusFF L (FractionRing (L⊗[k](CriticalProj23.criticalCurve i).functionField))=1 := by
  letI:=CriticalAffineDomain.ring_isDomain i hi h2
  letI:=CriticalProjectiveIntegral.projective_integral i hi h2
  letI:=SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
  letI:=base_domain L i hi h2
  letI:=CriticalFieldConstants.field_tensor_domain k i hi h2 L
  have he:=genus_congr (L:=L) (CriticalDoubleOriginalMap.baseFieldEquiv i hi h2).symm
  have hg:=genusFF_eq_of_algEquiv (CriticalConstantFieldComparison.fractionFieldEquiv k L i hi h2)
  have hp:=CriticalConstantFieldComparison.mapped_hypotheses k L i hi h2
  exact he.trans (hg.trans (CriticalGeometricGenus.genus_one (K:=L) (algebraMap k L i) hp.1 hp.2))

end FourCorner.CriticalNativeGeometricGenus
#print axioms FourCorner.CriticalNativeGeometricGenus.cover_genus_one
#print axioms FourCorner.CriticalNativeGeometricGenus.base_genus_one
