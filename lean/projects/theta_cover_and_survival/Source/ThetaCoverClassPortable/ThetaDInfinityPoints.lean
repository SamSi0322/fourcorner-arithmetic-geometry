import ThetaCoverClassPortable.ThetaDGeometricChartPoints
import Mathlib.FieldTheory.Separable

namespace FourCorner.ThetaDInfinityPoints
open Polynomial AlgebraicGeometry CategoryTheory MvPolynomial
open ThetaDGeometricModel ThetaDGeometricChartPoints ThetaLiteralModels
noncomputable section
attribute [local instance] Classical.propDecidable
local instance : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective

def polynomial : Polynomial K := Polynomial.C 9801*(1+Polynomial.X^4)+Polynomial.C 19598*Polynomial.X^2

theorem derivative_formula : polynomial.derivative=Polynomial.C 39204*Polynomial.X^3+Polynomial.C 39196*Polynomial.X := by
  apply Polynomial.funext
  intro u
  simp [polynomial,Polynomial.derivative_add,Polynomial.derivative_mul,Polynomial.derivative_pow]
  ring

def bezoutA : Polynomial K := Polynomial.C (1/9801)-Polynomial.C (9799/39200)*Polynomial.X^2
def bezoutB : Polynomial K := Polynomial.C (95981201/1536796800)*Polynomial.X+Polynomial.C (9799/156800)*Polynomial.X^3

theorem bezout : bezoutA*polynomial+bezoutB*polynomial.derivative=1 := by
  apply Polynomial.funext
  intro u
  simp [bezoutA,bezoutB,polynomial,derivative_formula]
  ring

theorem separable : polynomial.Separable := (Polynomial.separable_def' _).mpr ⟨bezoutA,bezoutB,bezout⟩
theorem degree_four : polynomial.natDegree=4 := by
  unfold polynomial
  compute_degree!

theorem nonzero : polynomial ≠ 0 := by
  intro h
  have hh:=degree_four
  rw [h] at hh
  norm_num at hh

def parameters : Finset K := polynomial.roots.toFinset

theorem parameters_card : parameters.card=4 := by
  rw [parameters,Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots separable)]
  rw [← (IsAlgClosed.splits polynomial).natDegree_eq_card_roots,degree_four]

theorem parameter_isRoot (u : K) (hu : u∈parameters) : polynomial.eval u=0 :=
  (Polynomial.mem_roots nonzero).mp (Multiset.mem_toFinset.mp hu)

/-- All four roots at infinity are SIMPLE: the original X=1 chart's
partial F_u is nonzero at every one, proved by an exact Bezout identity. -/
theorem partial_u_nonzero (u : K) (hu : polynomial.eval u=0) : u*(39196+39204*u^2) ≠ 0 := by
  have hd : polynomial.derivative.eval u ≠ 0 := by
    intro h
    have he:=congrArg (Polynomial.eval u) bezout
    simp only [Polynomial.eval_add,Polynomial.eval_mul,hu,h,mul_zero,add_zero,Polynomial.eval_one] at he
    exact zero_ne_one he
  have hform : polynomial.derivative.eval u=u*(39196+39204*u^2) := by
    rw [derivative_formula]
    simp
    ring
  rw [←hform]
  exact hd

theorem relations (u : K) (hu : polynomial.eval u=0) :
    ∀a : Fin 1,MvPolynomial.aeval ![u,0] (equation 0 a)=0 := by
  intro a;fin_cases a
  simpa [equation,ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,targetEquation,targetPolynomial,
    ThetaActualPoints.target_drop,polynomial,map_ofNat] using hu

/-- These are ACTUAL points of the SAME native categorical D_Qbar. -/
def point (u : K) (hu : polynomial.eval u=0) : Spec (.of K) ⟶ geometricD :=
  ThetaDGeometricChartPoints.point 0 ![u,0] (relations u hu)

theorem point_over (u : K) (hu) : point u hu ≫ toBase=𝟙 _ := ThetaDGeometricChartPoints.point_over _ _ _
theorem point_injective (u v : K) (hu hv) (h : point u hu=point v hv) : u=v :=
  congrFun (ThetaDGeometricChartPoints.point_injective 0 _ _ _ _ h) 0

def parametrizedPoint (u : {u : K // u∈parameters}) : Spec (.of K) ⟶ geometricD :=
  point u.val (parameter_isRoot u.val u.property)

theorem parametrizedPoint_injective : Function.Injective parametrizedPoint := by
  intro u v h
  apply Subtype.ext
  exact point_injective _ _ _ _ h

/-- Exactly four DISTINCT ACTUAL original-geometric-curve scheme points
are displayed on Z=0, with their simple-root certificates. -/
theorem actual_four_points : Nat.card (Set.range parametrizedPoint)=4 := by
  rw [←Nat.card_congr (Equiv.ofInjective parametrizedPoint parametrizedPoint_injective)]
  simp [parameters_card]

#print axioms bezout
#print axioms parameters_card
#print axioms partial_u_nonzero
#print axioms point_over
#print axioms parametrizedPoint_injective
#print axioms actual_four_points
end
end FourCorner.ThetaDInfinityPoints
