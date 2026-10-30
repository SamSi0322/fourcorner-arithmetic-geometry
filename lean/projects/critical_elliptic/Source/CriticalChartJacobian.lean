import CriticalStandardCharts
import CriticalScalarGeometry
import FiniteJacobianSmooth

noncomputable section
namespace FourCorner.CriticalChartJacobian
open Algebra AlgebraicGeometry MvPolynomial CriticalStandardCharts CriticalAmbientChart CriticalScalarGeometry
universe u
variable {k : Type u} [Field k]
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false

def columns : Fin 3 → Fin 2 → Fin 3
  | 0 => ![0,1]
  | 1 => ![0,2]
  | 2 => ![1,2]
lemma columns_injective (a : Fin 3) : Function.Injective (columns a) := by fin_cases a <;> decide

def pres (i : k) (j : Fin 4) (a : Fin 3) :
    PreSubmersivePresentation k (affineRing i j) (Fin 3) (Fin 2) :=
  .naive (v:=affineEquation i j) (columns a) (columns_injective a)

def ax (i : k) (j : Fin 4) (a : Fin 3) : affineRing i j := Ideal.Quotient.mk _ (X a)

lemma pres_jacobi (i : k) (j : Fin 4) (a : Fin 3) :
    (pres i j a).jacobiMatrix=fun r c=>pderiv (columns a r) (affineEquation i j c) := by
  apply Matrix.ext
  intro r c
  exact PreSubmersivePresentation.jacobiMatrix_apply (pres i j a) r c
lemma pres_map (i : k) (j : Fin 4) (a : Fin 3) (p : MvPolynomial (Fin 3) k) :
    algebraMap (pres i j a).Ring (affineRing i j) p=Ideal.Quotient.mk (affineIdeal i j) p := rfl

theorem jacobian_formula (i : k) (j : Fin 4) (a : Fin 3) :
    (pres i j a).jacobian=4*algebraMap k (affineRing i j)
      (minor i (insert j (columns a 0)) (insert j (columns a 1)))*
      ax i j (columns a 0)*ax i j (columns a 1) := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,pres_map,pres_jacobi,Matrix.det_fin_two]
  have hc (j : Fin 4) (c : k) : Ideal.Quotient.mk (affineIdeal i j) (C c)=algebraMap k (affineRing i j) c := rfl
  have hn (j : Fin 4) (n : ℕ) : Ideal.Quotient.mk (affineIdeal i j) (n : MvPolynomial (Fin 3) k)=n := map_natCast _ n
  fin_cases j <;> fin_cases a
  all_goals simp [affineEquation,CriticalQuotientChart.affineEquation,CriticalAmbientChart.dehom,
    CriticalProj23.equation,CriticalProj23.F0,CriticalProj23.F1,drop,CriticalAmbientChart.insert,columns,
    minor,coefficient0,coefficient1,ax,hc,hn,map_ofNat,map_natCast,pderiv_pow]
  all_goals ring

end FourCorner.CriticalChartJacobian
#print axioms FourCorner.CriticalChartJacobian.jacobian_formula
