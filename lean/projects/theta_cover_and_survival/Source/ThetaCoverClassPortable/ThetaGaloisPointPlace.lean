import ThetaCoverClassPortable.ThetaGaloisFieldAction
import ThetaCoverClassPortable.NativeStalkFieldNaturality

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open scoped Pointwise
namespace FourCorner.ThetaGaloisPointPlace
open ThetaDGeometricModel ThetaGaloisSchemeField ThetaGaloisFieldAction
open ThetaNativeFunctionFieldMap NativeStalkFieldNaturality SmoothProperRationalPointPlaces
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra

abbrev pointPlace (p : RationalPoint toBase) : Place K field :=
  (pointEquivRationalPlace toBase p).val

 theorem pointPlace_range (p : RationalPoint toBase) :
    (algebraMap (geometricD.presheaf.stalk (p.val (IsLocalRing.closedPoint K))) field).range=
      (pointPlace p).toValuationSubring.toSubring :=
  pointEquivRationalPlace_range toBase p

 theorem pointMap_center (σ : Gal) (p : RationalPoint toBase) :
    (pointMap σ p).val (IsLocalRing.closedPoint K)=
      schemeMap σ⁻¹ (p.val (IsLocalRing.closedPoint K)) := by
  change (baseScheme σ ≫ p.val ≫ schemeMap σ⁻¹) (IsLocalRing.closedPoint K)=_
  simp only [Scheme.Hom.comp_apply]
  congr 2
  exact Subsingleton.elim _ _

 theorem fieldMap_inverse_action (σ : Gal) (r : field) :
    fieldMap (schemeMap σ⁻¹) r=(absoluteAction σ)⁻¹ • r := by
  have hh:=congrArg (fun q:SemilinearAut K field=>SemilinearAut.toRingAut q r)
    (map_inv absoluteAction σ)
  exact hh

/-- The TRUE point action maps the TRUE native point Place by valuation-ring
IMAGE under tau_sigma. Both inclusions come from actual stalk isomorphisms;
no point/Place equivariance or over-K property of delta_sigma is assumed. -/
theorem pointPlace_galois (σ : Gal) (p : RationalPoint toBase) :
    pointPlace (pointMap σ p)=(absoluteAction σ) • pointPlace p := by
  let x := p.val (IsLocalRing.closedPoint K)
  have hnew : (algebraMap (geometricD.presheaf.stalk (schemeMap σ⁻¹ x)) field).range=
      (pointPlace (pointMap σ p)).toValuationSubring.toSubring := by
    have hh:=pointPlace_range (pointMap σ p)
    change (algebraMap (geometricD.presheaf.stalk ((pointMap σ p).val (IsLocalRing.closedPoint K))) field).range=
      (pointPlace (pointMap σ p)).toValuationSubring.toSubring at hh
    rw [pointMap_center] at hh
    exact hh
  have hr := stalk_range_comap (schemeMap σ⁻¹) x
  have hold : (algebraMap (geometricD.presheaf.stalk x) field).range=
      (pointPlace p).toValuationSubring.toSubring := pointPlace_range p
  apply Place.ext
  apply SetLike.ext
  intro r
  change r∈(pointPlace (pointMap σ p)).toValuationSubring.toSubring ↔
    r∈((absoluteAction σ) • pointPlace p).toValuationSubring
  rw [←hnew,hr,hold]
  change (fieldMap (schemeMap σ⁻¹) r∈(pointPlace p).toValuationSubring) ↔
    r∈(absoluteAction σ) • (pointPlace p).toValuationSubring
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,fieldMap_inverse_action]

#print axioms pointMap_center
#print axioms pointPlace_galois
end FourCorner.ThetaGaloisPointPlace
