import CriticalCoverNativeProperties
import AllPointFlat
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Noetherian

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry AlgebraicCurve
universe u
namespace FourCorner.CriticalCoverNativeProperties
variable {k : Type u} [Field k]

/-- The original critical double map is native flat at ALL its scheme points,
by injectivity into the actual function fields over smooth valuation stalks. -/
theorem actual_flat (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
    Flat (CriticalDoubleOriginalMap.map i hi h2) := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  letI := CriticalProjectiveIntegral.projective_integral i hi h2
  letI := EllipticQuarticModel.integral k
  letI := CriticalProjectiveSmooth.projective_smooth i hi h2
  letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
  letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
  letI := CriticalCoverGenericField.relativeAlgebra i hi h2
  exact AllPointFlat.flat_of_generic_diagram (CriticalProj23.criticalToSpec i)
    (CriticalDoubleOriginalMap.map i hi h2) (CriticalDoubleOriginalMap.map_generic i hi h2)

/-- Native finite etaleness of the exact original critical double map over
arbitrary k with i^2=-1 and 2 nonzero, including generic and nonrational points. -/
theorem actual_finite_etale (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
    IsFinite (CriticalDoubleOriginalMap.map i hi h2) ∧
      Etale (CriticalDoubleOriginalMap.map i hi h2) := by
  obtain ⟨hfin,hun,hft⟩ := actual_finite_unramified i hi h2
  letI := hfin
  letI := hun
  letI := hft
  letI := actual_flat i hi h2
  letI := CriticalProj23.criticalToSpec_isProper i
  letI : IsLocallyNoetherian (CriticalProj23.criticalCurve i) :=
    LocallyOfFiniteType.isLocallyNoetherian (CriticalProj23.criticalToSpec i)
  exact ⟨hfin,Etale.of_formallyUnramified_of_flat _⟩

#print axioms actual_flat
#print axioms actual_finite_etale
end FourCorner.CriticalCoverNativeProperties
