import ThetaCoverClassPortable.ThetaGaloisPointPlace
import ThetaCoverClassPortable.SemilinearDifferentialOrder
import ThetaCoverClassPortable.ThetaOddThetaCanonicalLines

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve KaehlerDifferential CategoryTheory
namespace FourCorner.ThetaGaloisCanonicalPlane
open ThetaDGeometricModel ThetaGaloisSchemeField ThetaGaloisFieldAction
open SemilinearPicAndEll SemilinearDifferentialOrder DivisorPicClassification
open ThetaOddThetaCanonicalLines ThetaGaloisPointPlace
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : PerfectField K := IsAlgClosed.perfectField K
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
local instance : ∀v : Place K field,v.DCoordGenerates := dCoordGenerates_of_isCurveOver

 def picMap (σ : Gal) (c : Pic K field) : Pic K field := absoluteAction σ • c

 theorem picMap_one (c : Pic K field) : picMap (1:Gal) c=c := by simp [picMap]
 theorem picMap_mul (σ ρ : Gal) (c : Pic K field) :
    picMap (σ*ρ) c=picMap σ (picMap ρ c) := by simp only [picMap,map_mul,mul_smul]
 theorem picMap_class (σ : Gal) (B : Divisor K field) :
    picMap σ (divisorClass B)=divisorClass (absoluteAction σ • B) := rfl
 theorem picMap_degree (σ : Gal) (c : Pic K field) : picDegree (picMap σ c)=picDegree c :=
    picDegree_smul _ _
 theorem picMap_ell (σ : Gal) (c : Pic K field) : picEll (picMap σ c)=picEll c := picEll_smul _ _
 theorem picMap_canonical (σ : Gal) : picMap σ (canonicalClass K field)=canonicalClass K field :=
    canonicalClass_fixed _
 theorem picMap_odd (σ : Gal) {c : Pic K field} (hc : IsOddThetaClass c) :
    IsOddThetaClass (picMap σ c) := oddTheta_smul _ hc

/-- Fixed because Fy is the actual rational-coefficient polynomial in the
actual fixed rational functions x,y; no differential basis action is assumed. -/
theorem fieldAut_Fy (σ : Gal) :
    fieldAut σ (ThetaDifferentialChartIdentity.Fy ThetaDFieldCoordinates.x ThetaDFieldCoordinates.y)=
      ThetaDifferentialChartIdentity.Fy ThetaDFieldCoordinates.x ThetaDFieldCoordinates.y := by
  simp only [ThetaDifferentialChartIdentity.Fy,map_mul,map_sub,map_add,map_pow,map_ofNat,
    fieldAut_x,fieldAut_y]

/-- The genuine universal Kähler map FIXES the actual dx/Fy differential,
derived from its definition and actual stalk-induced x,y invariance. -/
theorem omega_fixed (σ : Gal) :
    omegaMap (absoluteAction σ) ThetaDActualDifferential.omega=ThetaDActualDifferential.omega := by
  unfold ThetaDActualDifferential.omega
  rw [omegaMap_smul_F,omegaMap_D]
  change fieldAut σ (ThetaDifferentialChartIdentity.Fy ThetaDFieldCoordinates.x ThetaDFieldCoordinates.y)⁻¹ •
      D K field (fieldAut σ ThetaDFieldCoordinates.x)=_
  rw [map_inv₀,fieldAut_Fy,fieldAut_x]

 def coefficientMap (σ : Gal) (a : Fin 3→K) : Fin 3→K := fun i=>σ (a i)
 theorem coefficientMap_zero (σ : Gal) : coefficientMap σ 0=0 := by ext i;exact map_zero σ
 theorem coefficientMap_injective (σ : Gal) : Function.Injective (coefficientMap σ) := by
  intro a b h
  funext i
  exact σ.injective (congrFun h i)
 theorem coefficientMap_ne_zero (σ : Gal) {a : Fin 3→K} (ha : a≠0) : coefficientMap σ a≠0 := by
  intro hh
  exact ha (coefficientMap_injective σ (hh.trans (coefficientMap_zero σ).symm))

 theorem fieldAut_line_coefficient (σ : Gal) (a : Fin 3→K) :
    fieldAut σ (algebraMap K field (a 2)+algebraMap K field (a 0)*ThetaDFieldCoordinates.x+
      algebraMap K field (a 1)*ThetaDFieldCoordinates.y)=
      algebraMap K field (σ (a 2))+algebraMap K field (σ (a 0))*ThetaDFieldCoordinates.x+
        algebraMap K field (σ (a 1))*ThetaDFieldCoordinates.y := by
  rw [map_add,map_add,map_mul,map_mul,fieldAut_constants,fieldAut_constants,
    fieldAut_constants,fieldAut_x,fieldAut_y]

/-- Natural original canonical-plane forms commute with ACTUAL geometric
Galois pullback, not an arbitrary semilinear map chosen from a basis. -/
theorem omegaMap_plane (σ : Gal) (a : Fin 3→K) :
    omegaMap (absoluteAction σ) (planeToField a)=planeToField (coefficientMap σ a) := by
  rw [planeToField_formula,omegaMap_smul_F,omega_fixed,planeToField_formula]
  change fieldAut σ (algebraMap K field (a 2)+algebraMap K field (a 0)*ThetaDFieldCoordinates.x+
      algebraMap K field (a 1)*ThetaDFieldCoordinates.y) • ThetaDActualDifferential.omega=_
  rw [fieldAut_line_coefficient]
  rfl

 theorem canonical_plane_divisor_transport (σ : Gal) {a : Fin 3→K} (ha : a≠0) :
    canonicalDivisorOf (planeToField_ne_zero (coefficientMap_ne_zero σ ha))=
      absoluteAction σ • canonicalDivisorOf (planeToField_ne_zero ha) := by
  have hh:=canonicalDivisor_transport (absoluteAction σ) (planeToField_ne_zero ha)
  ext w
  rw [canonicalDivisorOf_apply]
  have hw:=congrArg (fun B:Divisor K field=>B w) hh
  rw [canonicalDivisorOf_apply,omegaMap_plane] at hw
  exact hw

 theorem point_divisor_transport (σ : Gal) (p : SmoothProperRationalPointPlaces.RationalPoint toBase) :
    absoluteAction σ • Finsupp.single (pointPlace p) (1:ℤ)=
      Finsupp.single (pointPlace (pointMap σ p)) (1:ℤ) := by
  rw [SemilinearAut.smul_single,pointPlace_galois]

#print axioms picMap_odd
#print axioms omega_fixed
#print axioms omegaMap_plane
#print axioms canonical_plane_divisor_transport
end FourCorner.ThetaGaloisCanonicalPlane
