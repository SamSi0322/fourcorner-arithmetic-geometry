import ThetaCoverClassPortable.ThetaGaloisCanonicalCorrespondence
import ThetaCoverClassPortable.ThetaLinesDualLines

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve KaehlerDifferential
namespace FourCorner.ThetaNativeDualCanonicalLines
open ThetaDGeometricModel ThetaGaloisSchemeField ThetaGaloisFieldAction ThetaGaloisCanonicalPlane
open ThetaOddThetaCanonicalLines ThetaActualOddThetaClasses DivisorPicClassification
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : PerfectField K := IsAlgClosed.perfectField K
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
local instance : ∀v : Place K field,v.DCoordGenerates := dCoordGenerates_of_isCurveOver

abbrev NativeDual := Projectivization K (Module.Dual K (Fin 3→K))

def dualOf (a : Fin 3→K) (ha : a≠0) : NativeDual :=
  Projectivization.mk K (dotProductEquiv K (Fin 3) a) (by
    intro h
    exact ha ((dotProductEquiv K (Fin 3)).injective (h.trans (map_zero _).symm)))

 theorem dual_eq_of_scalar {a b : Fin 3→K} (ha : a≠0) (hb : b≠0)
    (u : K) (h : u • b=a) : dualOf a ha=dualOf b hb := by
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨u,?_⟩
  rw [←map_smul,h]

 theorem canonical_divisor_eq_of_dual_eq {a b : Fin 3→K} (ha : a≠0) (hb : b≠0)
    (h : dualOf a ha=dualOf b hb) :
    canonicalDivisorOf (planeToField_ne_zero ha)=canonicalDivisorOf (planeToField_ne_zero hb) := by
  obtain ⟨u,hu⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp h
  have hvec : u • b=a := (dotProductEquiv K (Fin 3)).injective (by rw [map_smul];exact hu)
  have hu0 : u≠0 := by
    intro hz
    rw [hz,zero_smul] at hvec
    exact ha hvec.symm
  have hform : planeToField a=(algebraMap K field u) • planeToField b := by
    rw [←hvec,map_smul,algebraMap_smul]
  ext v
  rw [canonicalDivisorOf_apply,canonicalDivisorOf_apply,hform,
    Place.ordDifferential_smul _ ((map_ne_zero (algebraMap K field)).mpr hu0)
      (coeff_ne_zero (planeToField_ne_zero hb) v),ord_base_constant v hu0,zero_add]

 theorem double_divisor_injective {B E : ActualDivisor} (h : (2:ℕ) • B=(2:ℕ) • E) : B=E := by
  ext v
  have hh:=congrArg (fun D:ActualDivisor=>D v) h
  simp only [two_nsmul,Finsupp.add_apply] at hh
  omega

/-- EXACT comparison with the already frozen pure-LINE native dual action.
It is used only after deriving the actual geometric coefficient action. -/
theorem pure_dualAction_dualOf (σ : Gal) (a : Fin 3→K) (ha : a≠0) :
    ThetaLinesDualLines.dualAction σ (dualOf a ha)=
      dualOf (coefficientMap σ a) (coefficientMap_ne_zero σ ha) := by
  let e := ThetaLinesDualLines.projectiveEquiv (dotProductEquiv K (Fin 3))
  have he : e (Projectivization.mk K a ha)=dualOf a ha := rfl
  change e (ThetaLinesAbsoluteGalois.projectiveAction σ (e.symm (dualOf a ha)))=_
  rw [←he,Equiv.symm_apply_apply]
  change e (Projectivization.map (ThetaLinesAbsoluteGalois.coordinateMap σ)
    (ThetaLinesAbsoluteGalois.coordinateMap_injective σ) (Projectivization.mk K a ha))=_
  rw [Projectivization.map_mk]
  rfl

#print axioms canonical_divisor_eq_of_dual_eq
#print axioms pure_dualAction_dualOf
end FourCorner.ThetaNativeDualCanonicalLines
