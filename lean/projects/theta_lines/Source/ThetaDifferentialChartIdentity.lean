import ThetaDNativeSections

namespace FourCorner.ThetaDifferentialChartIdentity
open AlgebraicCurve
noncomputable section
variable {K E : Type*} [Field K] [Field E] [Algebra K E]
attribute [local instance] Classical.propDecidable

def Fx (x y : E) : E := x*(39204*x^2+39196*y^2-79184)
def Fy (x y : E) : E := y*(39196*x^2+39204*y^2-79184)
def Gu (u v : E) : E := u*(39196+39204*u^2-79184*v^2)

theorem partial_chart_identity (x y : E) (hx : x ≠ 0) : Gu (y/x) x⁻¹=x⁻¹^3*Fy x y := by
  unfold Gu Fy
  field_simp

/-- Exact differential transition in the literal X=1 chart. In particular
the minus sign and the SINGLE factor v are independently verified. -/
theorem omega_transition (x y : E) (hx : x ≠ 0) (hy : Fy x y ≠ 0) :
    (Fy x y)⁻¹ • KaehlerDifferential.D K E x=
      (-(x⁻¹)/(Gu (y/x) x⁻¹)) • KaehlerDifferential.D K E (x⁻¹) := by
  rw [Derivation.leibniz_inv,smul_smul,partial_chart_identity x y hx]
  congr 1
  field_simp

theorem xomega_transition (x y : E) (hx : x ≠ 0) (hy : Fy x y ≠ 0) :
    x • ((Fy x y)⁻¹ • KaehlerDifferential.D K E x)=
      (-1/Gu (y/x) x⁻¹) • KaehlerDifferential.D K E (x⁻¹) := by
  rw [omega_transition x y hx hy,smul_smul]
  congr 1
  field_simp

theorem yomega_transition (x y : E) (hx : x ≠ 0) (hy : Fy x y ≠ 0) :
    y • ((Fy x y)⁻¹ • KaehlerDifferential.D K E x)=
      (-(y/x)/Gu (y/x) x⁻¹) • KaehlerDifferential.D K E (x⁻¹) := by
  rw [omega_transition x y hx hy,smul_smul]
  congr 1
  field_simp

#print axioms partial_chart_identity
#print axioms omega_transition
#print axioms xomega_transition
#print axioms yomega_transition
end
end FourCorner.ThetaDifferentialChartIdentity
