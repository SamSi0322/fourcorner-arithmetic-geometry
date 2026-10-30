import ThetaCoverClassPortable.ThetaCoverNormalization
import ThetaCoverClassPortable.ThetaCoverQuadraticCoefficientData
import ThetaCoverClassPortable.ThetaCoverAllOrders

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits
namespace FourCorner.ThetaCoverGeometryClassAssembly
open ThetaDGeometricModel ThetaCoverFunctions ThetaCoverBoundaryPoints ThetaCoverDivisor
open ThetaCoverClass ThetaCoverContacts ThetaCoverPic0 ThetaCoverGaloisDescentData
open ThetaCoverRationalData ThetaCoverAllOrders ThetaDCanonicalInfinityDivisor
open ThetaGaloisSchemeField ThetaGaloisFieldAction DivisorPicClassification
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
attribute [local instance] Classical.propDecidable

/-- Native divisor-Pic0 class data for the SAME literal cover, whose full
actual normalization data is proved separately in ThetaCoverNormalization. QQ points/functions and absolute-Galois invariance are
proved data. A represented Jac(D)(QQ) identification and effective Cartier/
line-bundle descent are deliberately NOT asserted by this theorem. -/
theorem actual_geometric_class_data :
    h=(ellPlus/ellMinus)*squareMultiplier^2 ∧
    principalDivisor h h_ne_zero=2 • boundarySum-2 • infinitySum ∧
    (∀w : Place K field,w.ord h=if ∃e,place e=w then 2 else if w∈infinityPlaces then -2 else 0) ∧
    delta∈Pic0.torsion K field 2 ∧ delta≠0 ∧
    delta=Pic0.mk contactZeroDegreeDivisor ∧
    (∀σ : Gal,absoluteAction σ • delta=delta) ∧
    ell Bplus=1 ∧ ell Bminus=1 ∧ Bplus≠Bminus ∧
    (∀e : Signs,(point e).val ≫ pullback.fst (ThetaLiteralModels.dToBase ℚ) qb=qb ≫ rationalPoint e) ∧
    rationalPoint (true,true)=ThetaActualPoints.originD (k:=ℚ) :=
  ⟨exact_cover_identity,actual_divisor_h,all_orders_h,delta_mem_native_torsion,delta_ne_zero,
    delta_eq_actual_contacts,delta_fixed,plus_ell_one,minus_ell_one,contact_divisors_distinct,
    rationalPoint_basechange,rational_origin_preserved⟩

#print axioms actual_geometric_class_data
end FourCorner.ThetaCoverGeometryClassAssembly
