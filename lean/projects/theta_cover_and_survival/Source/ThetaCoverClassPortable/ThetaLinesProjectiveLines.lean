import ThetaCoverClassPortable.FourCorner.ThetaBitangentProjectiveChartsWave36
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Matrix.Dual

namespace FourCorner.ThetaLinesProjectiveLines
open Matrix
noncomputable section
variable {K : Type*} [Field K]
attribute [local instance] Classical.propDecidable

def coefficients : ThetaLine K → Fin 3 → K
  | .affine α β => ![-α,-β,1]
  | .vertical t => ![1,-t,0]
  | .yzero => ![0,1,0]

theorem coefficients_ne_zero (L : ThetaLine K) : coefficients L ≠ 0 := by
  cases L with
  | affine α β => intro h;have hh:=congrFun h 2;simpa [coefficients] using hh
  | vertical t => intro h;have hh:=congrFun h 0;simpa [coefficients] using hh
  | yzero => intro h;have hh:=congrFun h 1;simpa [coefficients] using hh

/-- The actual nonzero homogeneous linear form of a normalized line. -/
def linearForm (L : ThetaLine K) : Module.Dual K (Fin 3 → K) := dotProductEquiv K (Fin 3) (coefficients L)

theorem linearForm_apply (L : ThetaLine K) (x y z : K) :
    linearForm L ![x,y,z]=L.equation x y z := by
  cases L <;> simp [linearForm,dotProductEquiv,coefficients,dotProduct,Fin.sum_univ_three,ThetaLine.equation] <;> ring

def geometricLine (L : ThetaLine K) : Projectivization K (Fin 3 → K) :=
  Projectivization.mk K (coefficients L) (coefficients_ne_zero L)

/-- Native dual projective point of the actual linear form, with its actual
vector-space equivalence to the coefficient model made explicit. -/
def dualLine (L : ThetaLine K) : Projectivization K (Module.Dual K (Fin 3 → K)) :=
  Projectivization.mk K (linearForm L) (by
    intro h
    apply coefficients_ne_zero L
    exact (dotProductEquiv K (Fin 3)).injective (h.trans (map_zero _).symm))

theorem geometricLine_injective : Function.Injective (geometricLine (K:=K)) := by
  intro L M h
  obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp h
  have hn : c ≠ 0 := by intro hz;apply coefficients_ne_zero L;simpa [hz] using hc.symm
  apply theta_projective_line_chart_unique L M c hn
  intro x y z
  have he := congrArg (fun v : Fin 3 → K => (dotProductEquiv K (Fin 3) v) ![x,y,z]) hc
  rw [map_smul,LinearMap.smul_apply] at he
  change c • linearForm M ![x,y,z]=linearForm L ![x,y,z] at he
  simpa only [linearForm_apply,smul_eq_mul] using he.symm

theorem geometricLine_surjective : Function.Surjective (geometricLine (K:=K)) := by
  intro p
  induction p using Projectivization.ind with
  | h v hv =>
    have hn : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 := by
      by_contra h
      push Not at h
      apply hv
      ext i
      fin_cases i <;> tauto
    obtain ⟨L,c,hc,he⟩ := theta_projective_line_chart_cover (v 0) (v 1) (v 2) hn
    refine ⟨L,?_⟩
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨c⁻¹,?_⟩
    have hvv : v=c • coefficients L := by
      have h0:=he 1 0 0
      have h1:=he 0 1 0
      have h2:=he 0 0 1
      cases L <;> ext i <;> fin_cases i <;>
        simp_all [coefficients,ThetaLine.equation,Pi.smul_apply,smul_eq_mul]
    rw [hvv,smul_smul,inv_mul_cancel₀ hc,one_smul]

/-- Normalized charts are a proved parametrization of ALL actual plane lines. -/
def lineEquiv : ThetaLine K ≃ Projectivization K (Fin 3 → K) :=
  Equiv.ofBijective geometricLine ⟨geometricLine_injective,geometricLine_surjective⟩

#print axioms linearForm_apply
#print axioms geometricLine_injective
#print axioms geometricLine_surjective
#print axioms lineEquiv
end
end FourCorner.ThetaLinesProjectiveLines
