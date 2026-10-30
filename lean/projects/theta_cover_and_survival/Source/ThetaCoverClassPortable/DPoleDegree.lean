import ThetaCoverClassPortable.PoleFieldDegree
import ThetaCoverClassPortable.DSinglePoleModel

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
namespace FourCorner.DRationalInputs
open AlgebraicGeometry AlgebraicCurve
open ThetaLiteralModels
local instance instIsIntegralCurve_dPoleDegree : IsIntegral curve := integral
local instance instSmoothOfRelativeDimensionOfNatNatToBase_dPoleDegree : SmoothOfRelativeDimension 1 toBase := smooth
local instance instIsProperToBase_dPoleDegree : IsProper toBase := proper
local instance instAlgebraRatField_dPoleDegree : Algebra ℚ field := constants

/-- Actual field degree equals the EXACT single-OD pole order in the SAME
original native C/Q function field. No map-degree or rank premise is added. -/
theorem actual_field_degree_eq_pole (f : field) (r : ℕ)
    (ht : Transcendental ℚ f)
    [FiniteDimensional (IntermediateField.adjoin ℚ ({f} : Set field)) field]
    (hord : originPlace.ord f=-(r:ℤ))
    (haway : ∀ v : Place ℚ field,v≠originPlace → 0≤v.ord f) :
    Module.finrank (IntermediateField.adjoin ℚ ({f} : Set field)) field=r := by
  classical
  letI := field_isCurveOver
  letI : FiniteDimensional ℚ (LSpace (0 : Divisor ℚ field)) :=
    stichtenothGenusExists.2.1
  let D : Divisor ℚ field := Finsupp.single originPlace (r:ℤ)
  have hD : ∀ v : Place ℚ field,D v=max 0 (-v.ord f) := by
    intro v
    by_cases hv : v=originPlace
    · subst v
      simp [D,hord]
    · have h := haway v hv
      simp only [D,Finsupp.single_eq_of_ne hv]
      omega
  have hd : Divisor.degree D=(r:ℤ) := by
    simp [D,Divisor.degree_single,originPlace_degree_one]
  have he := PoleFieldDegree.degree_eq_finrank_adjoin f ht D hD
  rw [hd] at he
  exact_mod_cast he.symm

/-- The exact single-origin pole construction gives UNBOUNDED genuine finite
field degrees over Q(f), for the actual ORIGINAL D/Q field. -/
theorem unbounded_actual_field_degree (m0 : ℕ) :
    ∃ f : field,
      Transcendental ℚ f ∧
      FiniteDimensional (IntermediateField.adjoin ℚ ({f} : Set field)) field ∧
      m0<Module.finrank (IntermediateField.adjoin ℚ ({f} : Set field)) field := by
  obtain ⟨f,r,hf,hr,hord,haway,ht,hfd⟩ := single_origin_poles m0
  letI := hfd
  refine ⟨f,ht,hfd,?_⟩
  rw [actual_field_degree_eq_pole f r ht hord haway]
  exact hr

#print axioms actual_field_degree_eq_pole
#print axioms unbounded_actual_field_degree
end FourCorner.DRationalInputs
