import HpCanonicalIsomorphism
import Mathlib.LinearAlgebra.Matrix.Dual

namespace FourCorner.HpCanonicalActionFormula
open AlgebraicCurve HpLiteralField HpFieldGeometry HpCanonicalForms HpCanonicalBasis HpCanonicalIsomorphism
noncomputable section
attribute [local instance] Classical.propDecidable

variable (K : Type*) [Field K]
def transposeEquiv (A : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K)) : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K) :=
  ((dotProductEquiv K (Fin 5)).trans A.dualMap).trans (dotProductEquiv K (Fin 5)).symm

theorem transposeEquiv_apply (A : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K)) (x : Fin 5 → K) (i : Fin 5) :
    transposeEquiv K A x i=∑j,x j*A (Pi.single i 1) j := rfl

variable [IsAlgClosed K] [CharZero K]
local instance perfect : PerfectField K := IsAlgClosed.perfectField K
local instance finite (p : K) : FiniteDimensional (RatFunc K) (field K p) := finite_over_line K p
local instance curve (p : K) : IsCurveOver K (field K p) := isCurveOver K p
local instance finiteType (p : K) : Algebra.EssFiniteType K (field K p) := RatFuncFiniteExtension.essFiniteType K (field K p)
local instance constantModule (p : K) : Module K (field K p) := Algebra.toModule

variable {p q : K} (e : field K p ≃ₐ[K] field K q)
  (hp : p ≠ 0) (hpa : p-1 ≠ 0) (hpb : p+1 ≠ 0)
  (hq : q ≠ 0) (hqa : q-1 ≠ 0) (hqb : q+1 ≠ 0)

def matrix : Fin 5 → Fin 5 → K := fun j i =>
  coordinateAction K e hp hpa hpb hq hqa hqb (Pi.single i 1) j

theorem matrix_eq_repr (i j : Fin 5) : matrix K e hp hpa hpb hq hqa hqb j i=
    (HpCanonicalBasis.basis K q hq hqa hqb).repr
      (regularMap K e (HpCanonicalBasis.basis K p hp hpa hpb i)) j := by
  have hs : (HpCanonicalBasis.basis K p hp hpa hpb).equivFun.symm (Pi.single i 1)=
      HpCanonicalBasis.basis K p hp hpa hpb i := by
    apply (HpCanonicalBasis.basis K p hp hpa hpb).equivFun.injective
    ext j
    simp [Module.Basis.equivFun_self,Pi.single_apply,eq_comm]
  simp only [matrix,coordinateAction,LinearEquiv.trans_apply,hs,Module.Basis.equivFun_apply]
  rfl

theorem pullback_differential (i : Fin 5) :
    pullbackDiff e.toAlgHom (differential K p i)=
      ∑j,matrix K e hp hpa hpb hq hqa hqb j i • differential K q j := by
  have h := congrArg (fun z : regularDifferentials K (field K q) => (z : Ω[field K q⁄K]))
    ((HpCanonicalBasis.basis K q hq hqa hqb).sum_repr
      (regularMap K e (HpCanonicalBasis.basis K p hp hpa hpb i))).symm
  simpa only [matrix_eq_repr,Submodule.coe_sum,Submodule.coe_smul,HpCanonicalBasis.basis_coe,
    regularMap,LinearMap.codRestrict_apply,LinearMap.comp_apply,Submodule.subtype_apply] using h

def linearCoordinate (i : Fin 5) : field K q :=
  ∑j,algebraMap K (field K q) (matrix K e hp hpa hpb hq hqa hqb j i)*coordinate K q j

theorem pullback_coefficient (i : Fin 5) :
    pullbackDiff e.toAlgHom (differential K p i)=
      linearCoordinate K e hp hpa hpb hq hqa hqb i • form K q Finset.univ := by
  rw [pullback_differential,linearCoordinate,Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [differential_eq_coordinate_smul K q hq hqa hqb,mul_smul,IsScalarTower.algebraMap_smul]

theorem coordinate_scaling (i : Fin 5) :
    e (coordinate K p i)*linearCoordinate K e hp hpa hpb hq hqa hqb 4=
      linearCoordinate K e hp hpa hpb hq hqa hqb i := by
  have hd4 : differential K p 4=form K p Finset.univ := by simp [differential,denominatorSupport]
  have hh : (e (coordinate K p i)*linearCoordinate K e hp hpa hpb hq hqa hqb 4) • form K q Finset.univ=
      linearCoordinate K e hp hpa hpb hq hqa hqb i • form K q Finset.univ := by
    rw [mul_smul,← pullback_coefficient K e hp hpa hpb hq hqa hqb 4,hd4,
      ← HpDifferentialTransport.pullback_smul,← differential_eq_coordinate_smul K p hp hpa hpb,
      pullback_coefficient]
  have hz : (e (coordinate K p i)*linearCoordinate K e hp hpa hpb hq hqa hqb 4-
      linearCoordinate K e hp hpa hpb hq hqa hqb i) • form K q Finset.univ=0 := by rw [sub_smul,hh,sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right (form_ne_zero K q hq hqa hqb _))

#print axioms transposeEquiv
#print axioms matrix_eq_repr
#print axioms pullback_differential
#print axioms coordinate_scaling
end
end FourCorner.HpCanonicalActionFormula
