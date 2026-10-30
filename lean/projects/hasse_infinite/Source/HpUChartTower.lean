import HpAffineFractionField
import MonicBoundaryRegular

namespace FourCorner.HpUChartTower
open Polynomial Multiquadratic.CoordinateAlgebra
noncomputable section
variable (K : Type*) [Field K] [CharZero K]

def q (p : K) : Fin 3 → K[X]
  | 0 => C (2*(p-1)/p)*(1-C p*X^2)
  | 1 => C (2*(p+1)/p)*(1+C p*X^2)
  | 2 => C ((p-1)/p)+C (p+1)*X^2

def qTimes (p : K) : Fin 3 → K[X]
  | 0 => C (2*(p-1))*(1-C p*X^2)
  | 1 => C (2*(p+1))*(1+C p*X^2)
  | 2 => C (p-1)+C (p*(p+1))*X^2

/-- Literal source equations in the U=1 chart, with the original unit
coefficient p cleared inside the polynomial ring. -/
theorem q_times_p (p : K) (hp : p ≠ 0) (i : Fin 3) : C p*q K p i=qTimes K p i := by
  apply Polynomial.funext
  intro z
  fin_cases i <;> simp only [q,qTimes,eval_mul,eval_add,eval_sub,eval_C,eval_one,eval_pow,eval_X]
  all_goals field_simp [hp]
  all_goals ring

abbrev Tower (p : K) := Stage₃ K[X] (q K p 0) (q K p 1) (q K p 2)
def coeff (p : K) : K →+* Tower K p := (algebraMap K[X] (Tower K p)).comp C
def z (p : K) : Tower K p := algebraMap K[X] (Tower K p) X
def roots (p : K) : Fin 3 → Tower K p :=
  ![coordinate₁ K[X] (q K p 0) (q K p 1) (q K p 2),
    coordinate₂ K[X] (q K p 0) (q K p 1) (q K p 2),
    coordinate₃ K[X] (q K p 0) (q K p 1) (q K p 2)]

theorem roots_sq (p : K) (i : Fin 3) : (roots K p i)^2=algebraMap K[X] (Tower K p) (q K p i) := by
  fin_cases i
  · exact coordinate₁_sq _ _ _ _
  · exact coordinate₂_sq _ _ _ _
  · exact coordinate₃_sq _ _ _ _

/-- The original boundary coordinate stays regular in the full monic
U-chart tower, preserving possible components and nilpotents before localization. -/
theorem z_regular (p : K) : IsRegular (z K p) :=
  MonicBoundaryRegular.algebraMap_isRegular (isRegular_of_ne_zero Polynomial.X_ne_zero)

#print axioms q_times_p
#print axioms roots_sq
#print axioms z_regular
end
end FourCorner.HpUChartTower
