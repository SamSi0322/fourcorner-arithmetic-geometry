import ThetaCoverClassPortable.ThetaCoverRationalData
import ThetaCoverClassPortable.ThetaCoverClass

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits
namespace FourCorner.ThetaCoverGaloisDescentData
open ThetaDGeometricModel ThetaLiteralModels ThetaCoverBoundaryPoints ThetaCoverRationalData
open ThetaGaloisSchemeField ThetaGaloisFieldAction ThetaGaloisPointPlace ThetaGaloisCanonicalPlane
open ThetaCoverDivisor ThetaCoverClass ThetaDCanonicalInfinityDivisor
open ThetaDActualDifferential SemilinearDifferentialOrder SemilinearPicAndEll DivisorPicClassification
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
local instance : ∀w : Place K field,w.DCoordGenerates := dCoordGenerates_of_isCurveOver

/-- Fixedness follows from the TRUE rational point descent diagram. -/
theorem boundary_point_fixed (σ : Gal) (e : Signs) : pointMap σ (point e)=point e := by
  apply Subtype.ext
  apply pullback.hom_ext
  · change (baseScheme σ ≫ (point e).val ≫ schemeMap σ⁻¹) ≫ pullback.fst (dToBase ℚ) qb=_
    simp only [Category.assoc,schemeMap_fst]
    rw [rationalPoint_basechange]
    rw [←Category.assoc,←base_square,Category.comp_id]
  · change (pointMap σ (point e)).val ≫ toBase=(point e).val ≫ toBase
    rw [(pointMap σ (point e)).property,(point e).property]

 theorem boundary_place_fixed (σ : Gal) (e : Signs) : absoluteAction σ • place e=place e := by
  have hh:=(pointPlace_galois σ (point e)).symm
  rw [boundary_point_fixed] at hh
  exact hh

 theorem boundary_divisor_fixed (σ : Gal) : absoluteAction σ • boundarySum=boundarySum := by
  simp only [boundarySum,Finset.smul_sum,SemilinearAut.smul_single,boundary_place_fixed]

 theorem infinity_divisor_fixed (σ : Gal) : absoluteAction σ • infinitySum=infinitySum := by
  have hh:=canonicalDivisor_transport (absoluteAction σ) omega_ne_zero
  have he : canonicalDivisorOf (omegaMap_ne_zero (absoluteAction σ) omega_ne_zero)=
      canonicalDivisorOf omega_ne_zero := by
    ext w
    rw [canonicalDivisorOf_apply,canonicalDivisorOf_apply,omega_fixed]
  rw [he,canonical_divisor_exact] at hh
  exact hh.symm

/-- Genuine invariance in native divisor Pic, accompanied by rational
function and point descent data. This is NOT claimed to be line-bundle
Galois descent or a represented Jacobian(QQ)-point identification. -/
theorem geometric_class_galois_fixed (σ : Gal) : picMap σ geometricClass=geometricClass := by
  unfold geometricClass
  rw [picMap_class,smul_sub,boundary_divisor_fixed,infinity_divisor_fixed]

#print axioms boundary_point_fixed
#print axioms geometric_class_galois_fixed
end FourCorner.ThetaCoverGaloisDescentData
